using Accessors: @capture, foldtree, postwalk, need_dynamic_optic, replace_underscore, lower_index, DynamicIndexLens
import Accessors: parse_obj_optics


# https://github.com/JuliaObjects/Accessors.jl/pull/103
tree_contains(ex, parts::Tuple) = foldtree((yes, x) -> yes || x ∈ parts, false, ex)
tree_contains(ex, part) = tree_contains(ex, (part,))

struct IgnoreChildren
    value
end

foldtree_pre(op, init, x) = op(init, x)
function foldtree_pre(op, init, ex::Expr)
    curval = op(init, ex)
    curval isa IgnoreChildren && return curval.value
    return foldl((acc, x) -> foldtree_pre(op, acc, x), ex.args; init=curval)
end

# todo: remove this when Accessors is released
_secondarg(_, x) = x
_esc_and_dot_name_to_broadcasted(f) = esc(f)
_esc_and_dot_name_to_broadcasted(f::Symbol) =
    if f == :.
    # eg, in @set a[:] .= 1
        # the returned function will be called as func(a, 1)
        :(Base.BroadcastFunction($_secondarg))
    elseif startswith(string(f), '.')
        # eg, in @set a[:] .+= 1 or @optic _ .+ 1
        :(Base.BroadcastFunction($(esc(Symbol(string(f)[2:end])))))
    else
        esc(f)
    end

# changes from upstream:
# https://github.com/JuliaObjects/Accessors.jl/pull/103
# creating:
# - FixArgs
# – PropertyFunction
# - splat
# - ⩓, ⩔, _ < _ < _ support
function parse_obj_optics(ex::Expr)
    @debug "Parsing optic" ex
    dollar_exprs = foldtree([], ex) do exs, x
        x isa Expr && x.head == :$ ?
            push!(exs, only(x.args)) :
            exs
    end
    if !isempty(dollar_exprs)
        @debug "Has dollar expressions" dollar_exprs
        length(dollar_exprs) == 1 || error("Only a single dollar-expression is supported")
        # obj is the only dollar-expression:
        obj = esc(only(dollar_exprs))
        # parse expr with an underscore instead of the dollar-expression:
        _, optics = parse_obj_optics(postwalk(x -> x isa Expr && x.head == :$ ? :_ : x, ex))
        return obj, optics
    end

    if @capture(ex, (front_ |> back_))
        @debug "Captured front_ |> back_" front back
        obj, frontoptic = parse_obj_optics(front)
        backoptic = try
            # allow e.g. obj |> first |> _.a.b
            obj_back, backoptic = parse_obj_optics(back)
            if obj_back == esc(:_)
                backoptic
            else
                (esc(back),)
            end
        catch ArgumentError
            backoptic = (esc(back),)
        end
        return obj, tuple(frontoptic..., backoptic...)
    elseif @capture(ex, (left_ && right_)) || @capture(ex, (left_ || right_))
        @debug "Captured left_ && right_ or left_ || right_" left right
        objl, leftoptic = parse_obj_optic(left)
        objr, rightoptic = parse_obj_optic(right)
        @assert objl == objr
        obj = objl
        operator = Dict(:&& => ⩓, :|| => ⩔)[ex.head]
        return obj, (:($operator($leftoptic, $rightoptic)),)
    elseif Base.isexpr(ex, :comparison) && length(ex.args) == 5 && !tree_contains(ex.args[1], :_) && !tree_contains(ex.args[5], :_)
        @debug "Captured comparison"
        obj1, optic1 = parse_obj_optic(:($(ex.args[2])($(ex.args[1]), $(ex.args[3]))))
        obj2, optic2 = parse_obj_optic(:($(ex.args[4])($(ex.args[3]), $(ex.args[5]))))
        @assert obj1 == obj2
        obj = obj1
        return obj, (:($⩓($optic1, $optic2)),)
    elseif @capture(ex, front_[indices__])
        @debug "Captured front_[indices__]" front indices
        if !tree_contains(front, :_) && any(ind -> tree_contains(ind, :_), indices)
            ind = only(indices)
            @assert tree_contains(ind, :_)
            obj, frontoptic = parse_obj_optics(ind)
            optic = :(Base.Fix1(getindex, $(esc(front))))
        else
            obj, frontoptic = parse_obj_optics(front)
            if any(need_dynamic_optic, indices)
                @gensym collection
                indices = replace_underscore.(indices, collection)
                dims = length(indices) == 1 ? nothing : 1:length(indices)
                lindices = esc.(lower_index.(collection, indices, dims))
                optic = :($DynamicIndexLens($(esc(collection)) -> ($(lindices...),)))
            else
                index = esc(Expr(:tuple, indices...))
                optic = :($IndexLens($index))
            end
        end
    elseif @capture(ex, front_.property_)
        @debug "Captured front_.property_" front property
        property isa Union{Int,Symbol,String} || throw(ArgumentError(
            string("Error while parsing :($ex). Second argument to `getproperty` can only be",
                   "an `Int`, `Symbol` or `String` literal, received `$property` instead.")
        ))
        obj, frontoptic = parse_obj_optics(front)
        optic = :($PropertyLens{$(QuoteNode(property))}())
    elseif @capture(ex, f_(args__))
        @debug "Captured f_(args__)" f args
        args_contain_under = map(arg -> tree_contains(arg, :_), args)
        f_contains_under = tree_contains(f, :_)
        f_contains_under && any(args_contain_under) && error("Either the function or the arguments can contain an underscore, not both")
        if f_contains_under
            obj, frontoptic = parse_obj_optics(f)
            optic = :($funcvallens($(esc.(args)...),))
        elseif length(args) == 1
            arg = only(args)
            if Base.isexpr(arg, :(...))
                obj, frontoptic = parse_obj_optics(only(arg.args))
                optic = :(splat($(esc(f))))
            else
                # regular function optic
                # broadcasted operators like .- also fall here
                obj, frontoptic = parse_obj_optics(arg)
                optic = _esc_and_dot_name_to_broadcasted(f)
            end
        elseif any(args_contain_under)
            if count(args_contain_under) == 1
                # single function argument is optic target - create Fix1, Fix2, or FixArgs optic
                # multi-arg broadcasts also fall here, no matter if regular function or operator
                f = _esc_and_dot_name_to_broadcasted(f)
                if length(args) == 2 && !any(a -> Base.isexpr(a, :kw) || Base.isexpr(a, :parameters), args)
                    # Base.Fix1 or Fix2 is enough
                    if args_contain_under[1]
                        obj, frontoptic = parse_obj_optics(args[1])
                        optic = :(Base.Fix2($f, $(esc(args[2]))))
                    elseif args_contain_under[2]
                        obj, frontoptic = parse_obj_optics(args[2])
                        optic = :(Base.Fix1($f, $(esc(args[1]))))
                    end
                else
                    # need FixArgs
                    i_under = findfirst(args_contain_under)
                    obj, frontoptic = parse_obj_optics(args[i_under])
                    @reset args[i_under] = Placeholder()
                    optic = Expr(:call, fixargs, f, esc.(args)...)
                end
            else
                # multiple function arguments are "targets" - do nothing here, will create propertyfunction below
            end
        else
            # do nothing, see extra processing below
        end
    elseif @capture(ex, f_.(front_))
        @debug "Captured f_.(front_)" f front
        # broadcasted function call (not operator)
        obj, frontoptic = parse_obj_optics(front)
        optic = :(Base.BroadcastFunction($(esc(f))))
    end

    if !@isdefined optic
        @debug "No full optic captured, going with PropertyFunction"
        if tree_contains(ex, :_)
            # placeholder in ex, but doesn't match any of the known forms
            # try creating a propertyfunction if possible
            props = foldtree_pre(Any[], ex) do acc, ex
                # XXX: catches all "_.prop" code, even within other macros
                
                # can this be done for arbitrary nesting?
                if @capture(ex, front_.p1_.p2_.p3_.p4_) && front == :_
                    push!(acc, (p1,p2,p3,p4))
                    return IgnoreChildren(acc)
                elseif @capture(ex, front_.p1_.p2_.p3_) && front == :_
                    push!(acc, (p1,p2,p3))
                    return IgnoreChildren(acc)
                elseif @capture(ex, front_.p1_.p2_) && front == :_
                    push!(acc, (p1,p2))
                    return IgnoreChildren(acc)
                elseif @capture(ex, front_.p1_) && front == :_
                    push!(acc, (p1,))
                    return IgnoreChildren(acc)
                elseif ex == :_
                    push!(acc, ())
                else
                    acc
                end
            end |> unique
            props_nt = aggregate_props(props)

            obj = esc(:_)
            frontoptic = ()
            arg = gensym(:_)
            funcbody = :($(esc(arg)) -> $(esc(replace_underscore(ex, arg))))
            optic = if props_nt == Placeholder()
                funcbody
            else
                :($PropertyFunction($props_nt, $funcbody))
            end
        else
            # no placeholder in ex
            obj = esc(ex)
            return obj, ()
        end
    end

    return (obj, tuple(frontoptic..., optic))
end

function aggregate_props(props)
    if any(isempty, props)
        return Placeholder()
    end
    byfirst = Dict{Symbol, Vector{Any}}()
    for ps in props
        push!(get!(byfirst, first(ps), []), Base.tail(ps))
    end
    byfirst_nested = modify(byfirst, Elements() ∘ values) do rests
        aggregate_props(rests)
    end
    (; byfirst_nested...)
end
