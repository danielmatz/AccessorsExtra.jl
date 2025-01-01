@inline modify(f, A::Tuple, ::Elements, Bs::Tuple...) = map(f, A, Bs...)
@inline modify(f, A::NTuple{N,Any}, ::Elements, Bs::Vararg{Union{Tuple,AbstractVector,NamedTuple,CartesianIndex}}) where {N} = ntuple(i -> f(A[i], map(B -> B[i], Bs)...), Val(N))
@inline modify(f, A::NamedTuple, ::Elements, Bs...) = @modify(t -> modify(f, t, ∗, Bs...), Tuple(A))
@inline modify(f, A::Vector, ::Elements, Bs...) = map(f, A, Bs...)

@inline modify(f, A::NamedTuple{KS}, ::Properties, B::NamedTuple, Bs::Vararg{NamedTuple}) where {KS} = map(f, A, B[KS], map(B -> B[KS], Bs)...)
@inline modify(f, A::NTuple{N,Any}, ::Properties, B::NTuple{N,Any}) where {N} = map(f, A, B)
@inline modify(f, A::Tuple, ::Properties, B::Tuple) = error("modify not supported for different lengths: $(length(A)) vs $(length(B))")
@inline modify(f, A, ::Properties, Bs...) = setproperties(A, modify(f, getproperties(A), Properties(), getproperties.(Bs)...))

# when transferring these to Accessors, can remove separate "B" argument
modify(f, A, o::ComposedFunction, B, Bs...) =
    modify(A, o.inner, B, Bs...) do a, b, bs...
        modify(f, a, o.outer, b, bs...)
    end

@inline modify(f, A, o, B, Bs...) =
    modify(A, o) do a
        f(a, o(B), map(o, Bs)...)
    end

# functionality is useful: "take elements according to their indices, not iteration order"
# but it shouldn't be keyed(∗) because it means different things for a single argument
# @inline modify(f, A::Tuple, ::Keyed{Elements}, B::Tuple) = map(f, A, B)
# @inline modify(f, A::NTuple{N,Any}, ::Keyed{Elements}, B::Vector) where {N} = ntuple(i -> f(A[i], B[i]), Val(N))
# @inline modify(f, A::Vector, ::Keyed{Elements}, B::Union{Tuple,Vector}) = map(f, A, B)
# @inline modify(f, A::NamedTuple{KS}, ::Keyed{Elements}, B) where {KS} =
#     NamedTuple{KS}(map(KS) do k
#         f(A[k], B[k])
#     end)
