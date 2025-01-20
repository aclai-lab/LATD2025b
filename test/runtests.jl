using Test
using Random

include("../src/modalFLewToFirstOrder.jl")

function run_tests(list)
    println("\n" * ("#"^50))
    for test in list
        println("TEST: $test")
        @time include(test)
    end
end

println("Julia version: ", VERSION)

test_suites = [
    ("ModalFLewToFirstOrder", ["modalFLewToFirstOrder.jl",]),
]

@testset "LATD2025B.jl" begin
    for ts in eachindex(test_suites)
        name = test_suites[ts][1]
        list = test_suites[ts][2]
        let
            @testset "$name" begin
                run_tests(list)
            end
        end
    end
    println()
end
