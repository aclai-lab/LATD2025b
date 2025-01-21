using Random
using SoleLogics
using SoleLogics.ManyValuedLogics
using SoleReasoners
using StatsBase
import SoleBase: initrng
import SoleLogics: sample

diamondA = diamond(IA_A)
diamondL = diamond(IA_L)
diamondB = diamond(IA_B)
diamondE = diamond(IA_E)
diamondD = diamond(IA_D)
diamondO = diamond(IA_O)
diamondAi = diamond(IA_Ai)
diamondLi = diamond(IA_Li)
diamondBi = diamond(IA_Bi)
diamondEi = diamond(IA_Ei)
diamondDi = diamond(IA_Di)
diamondOi = diamond(IA_Oi)
boxA = box(IA_A)
boxL = box(IA_L)
boxB = box(IA_B)
boxE = box(IA_E)
boxD = box(IA_D)
boxO = box(IA_O)
boxAi = box(IA_Ai)
boxLi = box(IA_Li)
boxBi = box(IA_Bi)
boxEi = box(IA_Ei)
boxDi = box(IA_Di)
boxOi = box(IA_Oi)

BASE_MANY_VALUED_MODAL_CONNECTIVES = [
    ∨,
    ∧,
    →,
    diamondA,
    diamondL,
    diamondB,
    diamondE,
    diamondD,
    diamondO,
    diamondAi,
    diamondLi,
    diamondBi,
    diamondEi,
    diamondDi,
    diamondOi,
    boxA,
    boxL,
    boxB,
    boxE,
    boxD,
    boxO,
    boxAi,
    boxLi,
    boxBi,
    boxEi,
    boxDi,
    boxOi
]
BaseManyValuedConnectives = Union{typeof.(BASE_MANY_VALUED_MODAL_CONNECTIVES)...}

myalphabet = Atom.(["p", "q", "r"])

min_height = 1
max_height = 5
max_it = 2000
max_avg = 50
max_timeout = 30 # seconds

using SoleLogics.ManyValuedLogics: booleanalgebra
myoperators2 = []
append!(myoperators2, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators2, getdomain(booleanalgebra))
opweights2 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G3, Ł3
myoperators3 = []
append!(myoperators3, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators3, getdomain(G3))
opweights3 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G4, Ł4, H4
myoperators4 = []
append!(myoperators4, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators4, getdomain(G4))
opweights4 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G5
myoperators5 = []
append!(myoperators5, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators5, getdomain(G5))
opweights5 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

using SoleLogics.ManyValuedLogics: G6, H6_1, H6_2, H6_3, H6
myoperators6 = []
append!(myoperators6, BASE_MANY_VALUED_MODAL_CONNECTIVES)
append!(myoperators6, getdomain(G6))
opweights6 = [8, 8, 8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

algebras = [
    ("BA",   booleanalgebra, myoperators2, opweights2),
    ("G3",   G3,             myoperators3, opweights3),
    ("Ł3",   Ł3,             myoperators3, opweights3),
    ("G4",   G4,             myoperators4, opweights4),
    ("Ł4",   Ł4,             myoperators4, opweights4),
    ("H4",   H4,             myoperators4, opweights4),
    ("G5",   G5,             myoperators5, opweights5),
    ("G6",   G6,             myoperators6, opweights6),
    ("H6_1", H6_1,           myoperators6, opweights6),
    ("H6_2", H6_2,           myoperators6, opweights6),
    ("H6_3", H6_3,           myoperators6, opweights6),
    ("H6",   H6,             myoperators6, opweights6)
]

for a in algebras
    # Formula generation
    rng = initrng(Random.GLOBAL_RNG)
    aot = vcat(myalphabet,getdomain(a[2])) # atoms or truths
    aotweights = StatsBase.uweights(length(myalphabet)+length(getdomain(a[2])))
    aotpicker = (rng)->StatsBase.sample(rng, aot, aotweights)
    atomweights = StatsBase.uweights(length(myalphabet))
    truthweights = StatsBase.uweights(length(getdomain(a[2])))
    leafpicker1 = (rng)->SyntaxTree(
        →,
        (StatsBase.sample(rng, myalphabet, atomweights)),
        (StatsBase.sample(rng, getdomain(a[2]), truthweights))
    )
    leafpicker2 = (rng)->SyntaxTree(
        →,
        (StatsBase.sample(rng, getdomain(a[2]), truthweights)),
        (StatsBase.sample(rng, myalphabet, atomweights))
    )
    leafpickers = [leafpicker1, leafpicker2]
    lpweights = StatsBase.uweights(length(leafpickers))
    leafpicker = (rng)->(StatsBase.sample(rng, leafpickers, lpweights))(rng)

    # Confronting results with SoleReasoners tableau system
    for height in min_height:max_height
        j = 0
        for i in 1:max_it
            t = rand(MersenneTwister(i), getdomain(a[2]))
            f = randformula(
                MersenneTwister(i),
                height-1,   # height,
                myalphabet,
                BASE_MANY_VALUED_CONNECTIVES,
                opweights=StatsBase.uweights(length(BASE_MANY_VALUED_CONNECTIVES)),
                basecase=leafpicker,    # basecase=aotpicker
                balanced=true
            )
            if !isbot(t) && SoleLogics.height(f) == height
                j += 1
                brng = MersenneTwister(i)
                r = mvhsalphasat(
                    t,
                    f,
                    a[2],
                    rng=brng,
                    timeout=max_timeout,
                    verbose=false
                )
                r_translation = ModalFLewToFirstOrder.alphasat(
                    t,
                    f,
                    a[2]
                )
                if !isnothing(r) && !isnothing(r_translation) 
                    @test r == r_translation
                end
                if j == max_avg
                    break
                end
            end
            if i == max_it
                @warn "Warning: maximum iterations reached"
            end
        end
    end
end