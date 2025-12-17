using HomotopyContinuation, LinearAlgebra, IterTools, Base.Threads
using Graphs
import Graphs.Experimental.has_isomorph
import Base.Iterators.drop


# plucker matrix
function pl_matrix(v)

    s = vars[v]
    P = [[0, s[3, 4], -s[2, 4], s[2,3]], [0, 0, s[1, 4], -s[1, 3]], [0, 0, 0, s[1, 2]], [0, 0, 0, 0]]
    P = transpose(reduce(hcat, P))
    return P - transpose(P)
end


# dual plucker matrix
function pl_dual_matrix(v)

    s = vars[v]
    P = [[0, s[1, 2], s[1, 3], s[1,4]], [0, 0, s[2, 3], s[2, 4]], [0, 0, 0, s[3, 4]], [0, 0, 0, 0]]
    P = transpose(reduce(hcat, P))
    return P - transpose(P)
end


# plucker matrix
function pl_param_matrix(i,j)

    s = 
    P = [[0, m[i,j,3,4], -m[i,j,2,4], m[i,j,2,3]], [0, 0, m[i,j,1,4], -m[i,j,1,3]], [0, 0, 0, m[i,j,1,2]], [0, 0, 0, 0]]
    P = transpose(reduce(hcat, P))
    return P - transpose(P)
end


# inner product of two plucker vectors
function pl_inner_product(v, w)

    P = pl_matrix(v)
    Q = pl_dual_matrix(w)
    PQ = P*Q

    return sum([PQ[i,i] for i in 1:4])
end


# make the line config ideal
function line_incidence_ideal(V, E)

    if length(E) == 0
        return [pl_inner_product(v, v) for v in V]
    end

    return vcat([pl_inner_product(v, v) for v in V], map(e -> pl_inner_product(e[1], e[2]), E))
end


# make a dictionary of equations corresponding to edges
function edge_equations(n::Int)

    edge_eqns = Dict()
    all_edges = [[i, j] for i in 1:n for j in (i+1):n]
    for e in all_edges
        (i, j) = e
        v = a[i, :] - a[j, :]
        w = b[i, :] - b[j, :]
        edge_eqns[e] = transpose(v)*v - transpose(w)*w
    end

    return edge_eqns
end


# make the line incidence ideal in the Elekes-Sharir framework
function elekes_sharir_ideal(E::Vector{Vector{Int64}})

    edge_eqns = edge_equations(n)

    return [edge_eqns[e] for e in E]
end


# check if a polynomial evaluates to zero on all points in a witness set
# a polynomial "evaluates to zero" on a point if |f(p)| < tol 
function is_zero_on_witness_set(f::Expression, W::WitnessSet, tol::Float64 = 1e-10)

    sols = solutions(W)
    all_vars = vcat(reduce(vcat, a), reduce(vcat, b))
    evalsf = map(p -> abs(evaluate(f, all_vars => p)), sols)
    
    return maximum(evalsf) < tol
end


# compute the max of each edge equation on a witness set
function score_edges(E::Vector{Vector{Int64}}, W::WitnessSet)

    sols = solutions(W)
    all_vars = vcat(reduce(vcat, a), reduce(vcat, b))
    all_edges = [[i, j] for i in 1:n for j in (i+1):n]
    edge_eqns = edge_equations(n)
    
    
    return [[e, maximum(map(p -> abs(evaluate(edge_eqns[e], all_vars => p)), sols))] for e in E]
end


# find all edge polynomials which evaluate to zero on W
function find_zero_edges(W::WitnessSet, tol::Float64 = 1e-10)

    all_vars = vcat(reduce(vcat, a), reduce(vcat, b))
    all_edges = [[i, j] for i in 1:n for j in (i+1):n]
    edge_eqns = edge_equations(n)

    return [e for e in all_edges if is_zero_on_witness_set(edge_eqns[e], W, tol)]
end


# find the set of edges which are not in E but evaluate to zero on a given witness set
function find_implied_edges(E::Vector{Vector{Int64}}, W::WitnessSet, tol::Float64 = 1e-10)

    all_edges = [[i, j] for i in 1:n for j in (i+1):n]
    all_zero_edges = find_zero_edges(W, tol)
    return [e for e in all_zero_edges if !(e in E)]
end


# find the set of extra edges which vanish on each component
function components_via_zero_edges(E::Vector{Vector{Int64}}, decomp::NumericalIrreducibleDecomposition, tol::Float64 = 1e-10)

    wits = witness_sets(decomp)
    comps = Dict()
    
    for comp_dim in keys(wits)
        
        cur_comps = []

        for W in wits[comp_dim]
            implied_edges = find_implied_edges(E, W, tol)
            push!(cur_comps, [HomotopyContinuation.degree(W), length(implied_edges), implied_edges])
        end

        comps[comp_dim] = cur_comps
    end

    return comps
end


# find all components such that the only edge polynomials which evaluate to zero are the edges in E
function main_component(E::Vector{Vector{Int64}}, decomp::NumericalIrreducibleDecomposition, tol::Float64 = 1e-10)

    wits = witness_sets(decomp)
    main_comps = WitnessSet[]

    for comp_dim in keys(wits)
        for W in wits[comp_dim]
            implied_edges = find_implied_edges(E, W, tol)
            if length(implied_edges) == 0
                push!(main_comps, W)
            end
        end
    end
    
    return main_comps
end


# test if there is a main component
function is_graph_realizable(E::Vector{Vector{Int64}}, decomp::NumericalIrreducibleDecomposition, tol::Float64 = 1e-10)

    main_comps = main_component(E, decomp, tol)

    return length(main_comps) > 0
end


# compute the rank of a graph in the rigidity matroid
function rigidity_rank(n::Int, E::Vector{Vector{Int64}}, trials = 100)

    images = Expression[]

    for e in E
        (i, j) = e
        v = a[i, :] - a[j, :]
        push!(images, transpose(v)*v)
    end

    F = System(images)
    jac = jacobian(F)
    nvars = length(variables(F))

    return maximum([rank(evaluate(jac, variables(F) => rand(-1000:1000, nvars))) for i in 1:trials])
end


# compute the rank of a graph in the rigidity matroid
function rigidity_rank(G::SimpleGraph{Int64})

    n = length(vertices(G))
    E = [[src(e), dst(e)] for e in edges(G)]
    
    return rigidity_rank(n, E)
end


#
function graph_from_edges(n, E)

    G = Graph(n);
    map(e -> add_edge!(G, e[1], e[2]), E)
    return G
end 





# determine if an incidence variety with nid W is a complete intersection
function is_CI(n::Int, E::Vector{Vector{Int64}}, W::NumericalIrreducibleDecomposition)

    dims = collect(keys(degrees(W)))
    return 4*n - length(E) == maximum(dims)
end




# make the 2x4 matrix of a line in our chosen affine chart
function affine_pl_matrix(i::Int)

    return [[1, 0, a[i,1,1], a[i,1,2]], [0, 1, a[i,2,1], a[i,2,2]]]
end


# make the edge equation A_iA_j
function affine_pl_inner_product(i::Int, j::Int)

    A = affine_pl_matrix(i)
    B = affine_pl_matrix(j)
    AB = reduce(vcat, [A, B])
    AB = transpose(reduce(hcat, AB))

    return det(AB)
end


# make the line incidence ideal in affine coordinates
function affine_incidence_ideal(E::Vector{Vector{Int64}})

    edge_eqns = [affine_pl_inner_product(e[1], e[2]) for e in E]

    return edge_eqns
end


# check if a graph is K_4 free
function is_k4_free(n::Int, E::Vector{Vector{Int64}})


    G = graph_from_edges(n, E)

    for S in subsets(V)

        if length(S) < 6
            continue
        end

        (g, vmap) = induced_subgraph(G, S)

        if length(edges(g)) < 8
            continue
        end

        if has_isomorph(g, K24)
            return false
        end
    end

    return true
end


# check if a graph contains H as an induced subgraph
function contians_subgraph(n::Int, E::Vector{Vector{Int64}}, H)


    G = graph_from_edges(n, E)

    for S in subsets(V)

        if length(S) < nv(H)
            continue
        end

        (g, vmap) = induced_subgraph(G, S)

        if length(edges(g)) < ne(H)
            continue
        end

        if has_isomorph(g, H)
            return true
        end
    end

    return false
end


# nicely print which additional edge equations vanish on each component of an NID
function print_comps_via_zero_edges(E::Vector{Vector{Int64}}, decomp::NumericalIrreducibleDecomposition, tol::Float64 = 1e-10, PrintOutput = true)

    comps = components_via_zero_edges(E, decomp, tol)

    out = []

    for comp_dim in keys(comps)
        push!(out, [prepend!(val, comp_dim) for val in comps[comp_dim]])
    end

    out = reduce(vcat, out)
    
    if !(PrintOutput)
        return out
    end

    imp_edge_lengths = unique([length(x[4]) for x in out])

    out_str = []

    for comp in out
        str_comp = [string(i) for i in comp]
        print("Dim: "*str_comp[1]*", ")
        print("Degree: "*str_comp[2]*", ")
        #print("Number of Implied Edges: "*str_comp[3]*", ")
        if comp[3] > 0
            print("Implied Edges: "*str_comp[4]*"")
        else
            print("Implied Edges: []")
        end
        print("\n")
    end
end


# count how many components have a certain set of implied edges
function count_comps_via_zero_edges(E::Vector{Vector{Int64}}, decomp::NumericalIrreducibleDecomposition, tol::Float64 = 1e-10, ReturnString = false)

    comps = components_via_zero_edges(E, decomp, tol)

    out = []

    for comp_dim in keys(comps)
        push!(out, [prepend!(val, comp_dim) for val in comps[comp_dim]])
    end

    out = reduce(vcat, out)

    implied_edge_sets = unique(map(x -> x[4], out))

    comp_count = []

    for imp_E in implied_edge_sets

        comps_by_edges = [comp for comp in out if imp_E in comp]
        dims = [i[1] for i in comps_by_edges]
        degs = [i[2] for i in comps_by_edges]

        if length(unique(dims)) != 1 || length(unique(degs)) != 1
            print("Something weird happened with implied edge set:"*string(imp_E))
        end

        push!(comp_count, [length(comps_by_edges), imp_E])
    end

    return comp_count
end


# create a string to be used in the creation of our associated data files
# this string encodes which extra edge equations vanish on each component of a NID
function write_comps_via_zero_edges(E::Vector{Vector{Int64}}, decomp::NumericalIrreducibleDecomposition, tol::Float64 = 1e-10)

    comps = components_via_zero_edges(E, decomp, tol)

    out = []

    for comp_dim in keys(comps)
        push!(out, [prepend!(val, comp_dim) for val in comps[comp_dim]])
    end

    out = reduce(vcat, out)

    out_strs = []

    for comp in out
        cur_dim = comp[1]
        cur_deg = comp[2]
        if comp[3] > 0
            imp_edges = string(comp[4])
        else
            imp_edges = "\$\\emptyset\$"
        end
        cur_str = "\\item Component (Dim: $cur_dim, Deg: $cur_deg): "*imp_edges
        push!(out_strs, cur_str*"\n")
    end

    return join(out_strs)
end


# Verify that every CI witness set has the expected number of points
function verify_CI_witness_set(n::Int, E::Vector{Vector{Int64}}, W::NumericalIrreducibleDecomposition)

    degs = reduce(vcat, collect(values(degrees(W))))
    total_deg = sum(degs)

    return 2^(length(E)) == total_deg
end


# compute the total degree of a numerical irreducible decomposition
function total_deg(W::NumericalIrreducibleDecomposition)

    degs = degrees(W)
    return sum(reduce(vcat, collect(values(degs))))
end


# compute the number of missing solutions of a complete intersection
# if the graph is not a complete intersection, try to compute the degree again with more sensitive tracker options
function missing_solutions(n::Int, E::Vector{Vector{Int64}}, W::NumericalIrreducibleDecomposition)

    deg = total_deg(W)

    if is_CI(n, E, W)
        
        return 2^(length(E)) - deg
    end


    I = ideals[E]
    F = System(I)
    tracker_opts = TrackerOptions(automatic_differentiation = 1000, max_steps = 50000, max_step_size = .01, terminate_cond = 1e20, parameters = CONSERVATIVE_TRACKER_PARAMETERS)
    endgame_opts = EndgameOptions(max_endgame_steps = 10000, only_nonsingular = false, singular_min_accuracy = 1e-20, val_at_infinity_tol = 1e-10, sing_cond = 1e20, sing_accuracy = 1e-6, refine_steps = 10)
    newW = regeneration(F, tracker_options = tracker_opts, endgame_options = endgame_opts)
    new_deg = sum([HomotopyContinuation.degree(wit) for wit in newW])

    return new_deg - deg
end


# compute the multidegree of a CI incidence variety
function multidegree(n, E)

    @var t[1:n]

    mld = 2^n*prod([t[i] for i in 1:n])*prod([t[e[1]] + t[e[2]] for e in E])
    return mld
end


#
function parse_multidegree(n, E)

    @var t[1:n]
    mld = multidegree(n, E)
    (M, c) = exponents_coefficients(mld, t)

    result = Dict()

    for i in 1:size(M, 2)

        u = [5 for i in 1:n] - M[:, i]
        result[u] = c[i]
    end

    return result
end