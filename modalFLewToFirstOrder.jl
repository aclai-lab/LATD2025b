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
function translate(
    φ::F,
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
    translation = translategeq(φ, w, α, algebra, atoms)
    for p ∈ atoms
        smtfile *= "(declare-fun $(p.value) (W W) A)\n"
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

"""
    translategeq(
        p::Atom,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        N
    }

||p||_x ⪰ α = P(x) ⪰ α

For each atom p, there is a P(x) that returns a value from the algebra corresponing to the
value of p at the world x.
"""
function translategeq(
    p::Atom,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom};
    solver::String="z3"
) where {
    N
}
    if p ∉ atoms push!(atoms, p) end
    if isa(α, FiniteIndexTruth)
        return "(precedeq a$(α.index) ($(p.value) $(w.x.value) $(w.y.value)))"
    elseif isa(α, FiniteTruth)
        return "(precedeq $(α.label) ($(p.value) $(w.x.value) $(w.y.value)))"
    else
        error("Something went wrong")
    end
end

"""
    translateleq(
        p::Atom,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        N
    }

||p||_x ⪯ α = P(x) ⪯ α

For each atom p, there is a P(x) that returns a value from the algebra corresponing to the
value of p at the world x.
"""
function translateleq(
    p::Atom,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom};
    solver::String="z3"
) where {
    N
}
    if p ∉ atoms push!(atoms, p) end
    if isa(α, FiniteIndexTruth)
        return "(precedeq ($(p.value) $(w.x.value) $(w.y.value)) a$(α.index))"
    elseif isa(α, FiniteTruth)
        return "(precedeq ($(p.value) $(w.x.value) $(w.y.value)) $(α.label))"
    else
        error("Something went wrong")
    end
end

"""
    translategeq(
        β::T,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        T<:Truth,
        N
    }

||β||_x ⪰ α = β ⪰ α
"""
function translategeq(
    β::T,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom};
    solver::String="z3"
) where {
    T<:Truth,
    N
}
    if !isa(β, FiniteIndexTruth) β = convert(FiniteIndexTruth, β) end
    if isa(α, FiniteIndexTruth)
        return "(precedeq a$(α.index) a$(β.index))"
    elseif isa(α, FiniteTruth)
        return "(precedeq $(α.label) a$(β.index))"
    else
        error("Something went wrong")
    end
end

"""
    translateleq(
        β::T,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        a::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        T<:Truth,
        N
    }

||β||_x ⪯ α = β ⪯ α
"""
function translateleq(
    β::T,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    a::FiniteIndexFLewAlgebra,
    atoms::Vector{Atom};
    solver::String="z3"
) where {
    T<:Truth
}
    if !isa(β, FiniteIndexTruth) β = convert(FiniteIndexTruth, β) end
    if isa(α, FiniteIndexTruth)
        return "(precedeq a$(β.index) a$(α.index))"
    elseif isa(α, FiniteTruth)
        return "(precedeq a$(β.index) $(α.label))"
    else
        error("Something went wrong")
    end
end

"""
    function translategeq(
        φ::SyntaxBranch,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        algebra::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        N
    }

||φ∧ψ|| ⪰ α = ∃a,b(A(a)∧A(b)∧(||φ||_x⪰a)∧(||φ||_x⪰b)∧(a⋅b⪰α))
||φ∨ψ|| ⪰ α = ∃a,b(A(a)∧A(b)∧(||φ||_x⪰a)∧(||φ||_x⪰b)∧(a+b⪰α))
||φ→ψ|| ⪰ α = ∃a,b(A(a)∧A(b)∧(||φ||_x⪯a)∧(||φ||_x⪰b)∧(a↪b⪰α))
"""
function translategeq(
    φ::SyntaxBranch,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    algebra::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom};
    solver::String="z3"
) where {
    N
}
    if isa(φ.token, typeof(∧)) || isa(φ.token, typeof(∨)) || isa(φ.token, typeof(→))
        (ψ, ε) = φ.children
        (a, b) = FiniteTruth.(["a", "b"])
        smtfile = "(exists ((a A) (b A)) (and "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= a a$i)")
        end
        smtfile *= ") (or"
        for i ∈ 1:N
            smtfile *= (" (= b a$i)")
        end
        smtfile *= ") "
        if isa(φ.token, typeof(∧))
            smtfile *= "$(translategeq(ψ, w, a, algebra, atoms; solver)) "
            smtfile *= "$(translategeq(ε, w, b, algebra, atoms; solver)) "
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq a$(α.index) (monoid a b))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq $(α.label) (monoid a b))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(∨))
            smtfile *= "$(translategeq(ψ, w, a, algebra, atoms; solver)) "
            smtfile *= "$(translategeq(ε, w, b, algebra, atoms; solver)) "
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq a$(α.index) (join a b))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq $(α.label) (join a b))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(→))
            smtfile *= "$(translateleq(ψ, w, a, algebra, atoms; solver)) "
            smtfile *= "$(translategeq(ε, w, b, algebra, atoms; solver)) "
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq a$(α.index) (implication a b))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq $(α.label) (implication a b))))"
            else
                error("Something went wrong")
            end
        else
            error("Something went wrong")
        end
    else
        error("Something went wrong")
    end    
end

"""
    function translateleq(
        φ::SyntaxBranch,
        w::Interval,
        α::Union{FiniteIndexTruth, FiniteTruth},
        algebra::FiniteIndexFLewAlgebra{N},
        atoms::Vector{Atom};
        solver::String="z3"
    ) where {
        N
    }

||φ∧ψ|| ⪯ α = ∃a,b(A(a)∧A(b)∧(||φ||_x⪯a)∧(||φ||_x⪯b)∧(a⋅b⪯α))
||φ∨ψ|| ⪯ α = ∃a,b(A(a)∧A(b)∧(||φ||_x⪯a)∧(||φ||_x⪯b)∧(a+b⪯α))
||φ→ψ|| ⪯ α = ∃a,b(A(a)∧A(b)∧(||φ||_x⪰a)∧(||φ||_x⪯b)∧(a↪b⪯α))
"""
function translateleq(
    φ::SyntaxBranch,
    w::Interval,
    α::Union{FiniteIndexTruth, FiniteTruth},
    algebra::FiniteIndexFLewAlgebra{N},
    atoms::Vector{Atom};
    solver::String="z3"
) where {
    N
}
    if isa(φ.token, typeof(∧)) || isa(φ.token, typeof(∨)) || isa(φ.token, typeof(→))
        (ψ, ε) = φ.children
        (a, b) = FiniteTruth.(["a", "b"])
        smtfile = "(exists ((a A) (b A)) (and "
        smtfile *= "(or"
        for i ∈ 1:N
            smtfile *= (" (= a a$i)")
        end
        smtfile *= ") (or"
        for i ∈ 1:N
            smtfile *= (" (= b a$i)")
        end
        smtfile *= ") "
        if isa(φ.token, typeof(∧))
            smtfile *= "$(translateleq(ψ, w, a, algebra, atoms; solver)) "
            smtfile *= "$(translateleq(ε, w, b, algebra, atoms; solver)) "
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq (monoid a b) a$(α.index))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq (monoid a b) $(α.label))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(∨))
            smtfile *= "$(translateleq(ψ, w, a, algebra, atoms; solver)) "
            smtfile *= "$(translateleq(ε, w, b, algebra, atoms; solver)) "
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq (join a b) a$(α.index))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq (join a b) $(α.label))))"
            else
                error("Something went wrong")
            end
        elseif isa(φ.token, typeof(→))
            smtfile *= "$(translategeq(ψ, w, a, algebra, atoms; solver)) "
            smtfile *= "$(translateleq(ε, w, b, algebra, atoms; solver)) "
            if isa(α, FiniteIndexTruth)
                smtfile *= "(precedeq (implication a b) a$(α.index))))"
            elseif isa(α, FiniteTruth)
                smtfile *= "(precedeq (implication a b) $(α.label))))"
            else
                error("Something went wrong")
            end
        else
            error("Something went wrong")
        end
    else
        error("Something went wrong")
    end    
end

"""
    alphasat(
        α::T,
        φ::F,
        algebra::A;
        solver::String="z3"
    ) where {
        T<:Truth,
        F<:Formula,
        A<:AbstractAlgebra
    }

Check α-satisfiability of the formula `φ` for a given value `α` from an algebra `algebra`
using an smt solver (default=`z3`).
"""
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

"""
    sat(φ::F, algebra::A; solver::String="z3")

Check 1-satisfiability of the formula `φ` using an smt solver (default=`z3`).
"""
function sat(φ::F, algebra::A; solver::String="z3") where {F<:Formula, A<:AbstractAlgebra}
    alphasat(⊤, φ, algebra; solver)
end