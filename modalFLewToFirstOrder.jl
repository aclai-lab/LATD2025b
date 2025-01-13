using SoleLogics
using SoleLogics: AbstractAlgebra
using SoleLogics.ManyValuedLogics
using SoleLogics.ManyValuedLogics: FiniteIndexFLewAlgebra, FiniteIndexTruth
using UUIDs

struct Point
    value::String
end

struct Interval
    x::Point
    y::Point
end

"""
    translate(
        φ::F,
        α::FiniteIndexTruth,
        algebra::FiniteIndexFLewAlgebra{N};
        solver::String="z3"
    ) where {
     F<:Formula,
     N
    }

Translate the α-satisfiability problem for modal FLew-algebra formulae into two-sorted
first-order using smt-lib syntax and calling an smt-solver.
"""
function translate(φ::F,
    α::FiniteIndexTruth,
    algebra::FiniteIndexFLewAlgebra{N};
    solver::String="z3"
) where {
    F<:Formula,
    N
}
    # algebra
    smtfile = "(declare-sort A)\n"
    for i ∈ 1:N
        smtfile *= "(declare-const a$i A)\n"
    end
    smtfile *= "(assert (distinct"
    for i ∈ 1:N
        smtfile *= " a$i"
    end
    smtfile *= "))\n(declare-fun join (A A) A)\n(declare-fun meet (A A) A)\n"
    smtfile *= "(declare-fun monoid (A A) A)\n(declare-fun implication (A A) A)\n"
    for i ∈ 1:N
        for j ∈ 1:N
            smtfile *= "(assert (= (join a$i a$j) "
            smtfile *= "a$(algebra.join(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (meet a$i a$j) "
            smtfile *= "a$(algebra.meet(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (monoid a$i a$j) "
            smtfile *= "a$(algebra.monoid(UInt8(i), UInt8(j)).index)))\n"
            smtfile *= "(assert (= (implication a$i a$j) "
            smtfile *= "a$(algebra.implication(UInt8(i), UInt8(j)).index)))\n"
        end
    end
    smtfile *= "(define-fun precedeq ((x A) (y A)) Bool (= (meet x y) x))\n"
    # order
    smtfile *= "(declare-sort W)\n"
    smtfile *= "(declare-fun mveq (W W) A)\n"
    smtfile *= "(declare-fun mvlt (W W) A)\n"
    # =(x,y) = 1 iff x = y
    smtfile *= "(assert (forall ((x W) (y W)) (= (= (mveq x y) a1) (= x y))))\n"
    # =(x,y) = =(y,x)    
    smtfile *= "(assert (forall ((x W) (y W)) (= (mveq x y) (mveq y x))))\n" 
    # <(x,x) = 0       
    smtfile *= "(assert (forall ((x W)) (= (mvlt x x) a2)))\n"      
    # <(x,z) ⪰ <(x,y) ⋅ <(y,z)                
    smtfile *= "(assert (forall ((x W) (y W) (z W)) "
    smtfile *= "(precedeq (monoid (mvlt x y) (mvlt y z)) (mvlt x z))))\n"   
    # if <(x,y) ≻ 0 and <(y,z) ≻ 0 then <(x,z) ≻ 0        
    smtfile *= "(assert (forall ((x W) (y W) (z W)) "
    smtfile *= "(=> (and (distinct (mvlt x y) a2) "
    smtfile *= "(distinct (mvlt y z) a2)) (distinct (mvlt x z) a2))))\n"
    # if <(x,y) = 0 and <(y,x) = 0 then =(x,y) = 1          
    smtfile *= "(assert (forall ((x W) (y W)) "
    smtfile *= "(=> (and (= (mvlt x y) a2) (= (mvlt y x) a2)) (= (mveq x y) a1))))\n"
    # if =(x,y) ≻ 0 then <(x,y) ≺ 1                       
    smtfile *= "(assert (forall ((x W) (y W)) "
    smtfile *= "(=> (distinct (mveq x y) a2) (distinct (mvlt x y) a1))))\n"                                          

    w = Interval(Point("x"),Point("y"))
    atoms = Vector{Atom}()
    translation = translate(φ, w, α, algebra, atoms)
    for p ∈ atoms
        smtfile *= "(declare-fun P (W W A) Bool)\n"
    end
    smtfile *= "(assert (exists ((x W) (y W)) $(translation)))\n"

    smtfile *= "(check-sat)"
    b = IOBuffer()
    uuid = UUIDs.uuid4()
    touch("$(tempdir())/temp$uuid.smt2")
    open("$(tempdir())/temp$uuid.smt2", "w") do file
        write(file, smtfile)
    end
    if solver == "z3"
        run(pipeline(`z3 $(tempdir())/temp$uuid.smt2`, stdout = b))
        rm("$(tempdir())/temp$uuid.smt2")
        return take!(b) == UInt8[0x73, 0x61, 0x74, 0x0a]
    else
        rm("$(tempdir())/temp$uuid.smt2")
        error("Please specify a supported solver. At the moment, only z3 is supported.")
    end
end

"""
    translate(
        φ::F,
        α::T,
        algebra::A;
        solver::String="z3"
    ) where {
        T<:Truth,
        F<:Formula,
        A<:AbstractAlgebra
    }

Translate the α-satisfiability problem for modal FLew-algebra formulae into two-sorted
first-order using smt-lib syntax and calling an smt-solver.
"""
function translate(
    φ::F,
    α::T,
    a::A;
    solver::String="z3"
) where {
    T<:Truth,
    F<:Formula,
    A<:AbstractAlgebra
}
    if !isa(α, FiniteIndexTruth) α = convert(FiniteIndexTruth, α) end
    if !isa(a, FiniteIndexFLewAlgebra) a = convert(FiniteIndexFLewAlgebra, a) end
    translate(φ, α, a; solver)
end

function translate(
    p::Atom,
    w::Interval,
    _::FiniteIndexTruth,
    _::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom}
) where {
    N
}
    if p ∉ atoms push!(atoms, p) end
    smtfile = "(or"
    for value in 1:N
        smtfile *= " (P $(w.x.value) $(w.y.value) a$value)"
    end
    smtfile *= ")"
    return smtfile
end

function translate(
    β::T,
    _::Interval,
    α::FiniteIndexTruth,
    _::FiniteIndexFLewAlgebra,
    atoms::Vector{Atom}
) where {
    T<:Truth
}
    if !isa(β, FiniteIndexTruth) β = convert(FiniteIndexTruth, β) end
    return "(precedeq a$(α.index) a$(β.index))"
end

function alphasat(
    α::T,
    φ::F,
    algebra::A;
    solver::String="z3"
) where {
    T<:Truth,
    F<:Formula,
    A<:AbstractAlgebra
}
    return translate(φ, α, algebra; solver)
end

function sat(φ::F, algebra::A; solver::String="z3") where {F<:Formula, A<:AbstractAlgebra}
    alphasat(⊤, φ, algebra; solver)
end