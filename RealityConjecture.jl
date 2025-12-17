include("LineIncidenceVarieties.jl")
using HomotopyContinuation, LinearAlgebra, Random, StatsBase;
using JSON;

# function for making a totally positive matrix of external data
# 
function totally_positive_data(n::Int, m::Int)
raw = JSON.parsefile("/Users/hollerin/LineConfigurationVarieties/LineIncidenceVarieties/matrices.json");
matrices = [transpose(Matrix{Float64}(hcat(s...))) for s in raw[1]]
Zs=matrices[1:m];
return Zs
end


# 
function schubert_slice(n::Int, E::Vector{Vector{Int64}}, u::Vector{Int64}, Z)


    # ideal which we will make for Iu
    Iu = affine_incidence_ideal(E)

    # keep track of which column of Z we are on
    k = 1
    # for each internal line we add u[i] schubert conditions
    for i in 1:n
        # for each schubert condition we make it by choosing adjacent columns of Z
        cur_internal_line = transpose(reduce(hcat, affine_pl_matrix(i)))
        for j in 1:u[i]
            if k == sum(u)
                cur_external_line = transpose(Z[:,[k, 1]])
            else
                cur_external_line = transpose(Z[:,[k, k+1]])
            end
            
            line_eqn = det(vcat(cur_internal_line, cur_external_line))
            push!(Iu, line_eqn)
            k = k+1;
        end
    end

    return Iu
end


# 
function test_reality_conjecture(n::Int, E::Vector{Vector{Int64}}, u::Vector{Int64}, Zs::Vector, return_dict = false)

    results = []

    for Z in Zs

        Iu = schubert_slice(n::Int, E, u, Z)
        W = solve(Iu)
        all_sols = length(solutions(W))
        real_sols = length(real_solutions(W))
        push!(results, [all_sols == real_sols, all_sols, real_sols])
    end

    if return_dict
        return results
    else
        return all(map(i -> i[1] == 1, results))
    end
end


# 
function test_reality_conjecture(n::Int, E::Vector{Vector{Int64}}, trials::Int, return_dict = false)

    # generate data and 
    Zs = totally_positive_data(n, trials)
    println("Data generation complete")

    # Dictionary to store our results for each multidegree
    results = Dict()

    # get the multidegree in dictionary format
    mld = parse_multidegree(n, E)

    
    # for each u coming from the exponent vectors in the multidegree
    # check that our LS degree many solutions are all real if our external lines are positive
    # and cyclically ordered
    for u in keys(mld)

        # get the LS degree
        LS_deg = mld[u]
        # test conjecture for this specific u
        u_result = test_reality_conjecture(n, E, u, Zs, true)

        # check that we actually get LS degree many solutions each trial
        found_LS_deg_sols = all(i -> i[2] == LS_deg, u_result)

        # check reality for each trial
        results[u] = [all(i -> i[1] == 1, u_result), found_LS_deg_sols]

        println("Finished: "*string(u))
    end

    
    if return_dict
        return results
    else
        return all(i -> i[1] == 1, values(results))
    end
end