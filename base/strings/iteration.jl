struct EachStringIndex{T<:AbstractString}
    s::T
end
keys(s::AbstractString) = EachStringIndex(s)

length(e::EachStringIndex) = length(e.s)
first(::EachStringIndex) = 1
last(e::EachStringIndex) = lastindex(e.s)
eltype(::Type{<:EachStringIndex}) = Int

const StringLIPairs{T<:AbstractString} = Iterators.LeadIndPairs{Int, Char, EachStringIndex{T}, T}
const StringPairs{T<:AbstractString} = Iterators.Pairs{Int, Char, EachStringIndex{T}, T}
StringLIPairs{T}(x::T) where {T<:AbstractString} = Iterators.LeadIndPairs(x, eachindex(x))
StringLIPairs(x::T) where {T<:AbstractString} = StringLIPairs{T}(x)
StringPairs{T}(x::T) where {T<:AbstractString} = Iterators.Pairs(x, eachindex(x))
StringPairs(x::T) where {T<:AbstractString} = StringPairs{T}(x)

Iterators.pairs(s::AbstractString) = StringPairs(s)
Iterators.reverse(s::StringPairs) = Iterators.Reverse(s)

start(sp::StringLIPairs) = 1
function done(s::StringLIPairs, i)
    if isa(i, Integer)
        return i > ncodeunits(s.data)
    else
        throw(MethodError(done, (s, i)))
    end
end
function next(s::StringLIPairs, i)
    if isa(i, Integer) && !isa(i, Int64)
        return next(s, Int64(i))
    else
        throw(MethodError(next, (s, i)))
    end
end

# Reverse pair iteration
start(e::Iterators.Reverse{<:StringPairs}) = ncodeunits(e.itr.data)+1
done(e::Iterators.Reverse{<:StringPairs}, idx) = idx == firstindex(e.itr.data)
function next(s::Iterators.Reverse{<:StringPairs}, idx)
    tidx = thisind(s.itr.data, idx-1)
    (nidx, c) = first(leadindpairs(s.itr.data, tidx))
    Pair(tidx, c), tidx
end

function prev(s::AbstractString, idx)
    (i, c), _ = next(Iterators.Reverse(StringPairs(s)), idx)
    (c, i)
end

start(e::StringPairs) = (firstindex(e.data), start(StringLIPairs(e.data)))
done(e::StringPairs, (idx, state)) = done(StringLIPairs(e.data), state)
function next(s::StringPairs, (idx, state))
    ((nidx, c), state) = next(StringLIPairs(s.data), state)
    Pair(idx, c), (nidx, state)
end

start(s::AbstractString) = start(StringLIPairs(s))
done(s::AbstractString, state) = done(StringLIPairs(s), state)
function next(s::AbstractString, state)
    ((idx, c), state) = next(StringLIPairs(s), state)
    (c, state)
end

start(e::EachStringIndex) = start(StringPairs(e.s))
done(e::EachStringIndex, state) = done(StringPairs(e.s), state)
function next(e::EachStringIndex, state)
    ((idx, c), state) = next(StringPairs(e.s), state)
    (idx, state)
end

eltype(::Type{<:AbstractString}) = Char
sizeof(s::AbstractString) = ncodeunits(s) * sizeof(codeunit(s))
firstindex(s::AbstractString) = 1
lastindex(s::AbstractString) = thisind(s, ncodeunits(s))

function getindex(s::AbstractString, i::Integer)
    @boundscheck checkbounds(s, i)
    @inbounds return isvalid(s, i) ? first(leadindpairs(s, i)).second : string_index_err(s, i)
end

getindex(s::AbstractString, i::Colon) = s
# TODO: handle other ranges with stride ±1 specially?
# TODO: add more @propagate_inbounds annotations?
getindex(s::AbstractString, v::AbstractVector{<:Integer}) =
    sprint(io->(for i in v; write(io, s[i]) end), sizehint=length(v))
getindex(s::AbstractString, v::AbstractVector{Bool}) =
    throw(ArgumentError("logical indexing not supported for strings"))

function get(s::AbstractString, i::Integer, default)
# TODO: use ternary once @inbounds is expression-like
    if checkbounds(Bool, s, i)
        @inbounds return s[i]
    else
        return default
    end
end
