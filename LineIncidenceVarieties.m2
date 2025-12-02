needsPackage "Graphs"
needsPackage "NumericalAlgebraicGeometry"


------------------------------------------------------------------
-- Pluecker coordinates for line incidence ideals
------------------------------------------------------------------

-- make the ring with n sets of variables a_(i,j), b_(i, j), ...
plProductRing = {GradeRing => true, CoefficientRing => QQ} >> opts -> n -> (

    syms := take(a..z, n);
    KK := opts.CoefficientRing;
    R := KK[flatten apply(syms, s -> flatten for i from 1 to 4 list for j from i+1 to 4 list s_(i, j))];

    if opts.GradeRing then(
        Id := entries map(ZZ^n);
        degs := flatten apply(n, i -> toList(6:Id_i));
        return newRing(R, Degrees => degs);
    );

    return R
)

-- make a hashtable which we can use to easily access our ring elements
plHashTable = (i, R) -> (

    n := sub(numgens(R) / 6, ZZ);
    syms := take(a..z, n);
    s := syms_(i-1);
    
    return hashTable flatten for i from 1 to 4 list for j from i+1 to 4 list {(i, j), (s_(i, j))_R}
)

-- make the matrix whose pfaffian is the plucker relation
plMatrix = (i, R) -> (

    n := sub(numgens(R) / 6, ZZ);
    syms := take(a..z, n);
    s := syms_(i-1);

    P := matrix {{0, s_(3, 4)_R, -s_(2, 4)_R, s_(2,3)_R}, {0, 0, s_(1, 4)_R, -s_(1, 3)_R}, {0, 0, 0, s_(1, 2)_R}, {0, 0, 0, 0}};
    
    return P - transpose(P);
)

-- make the dual of the plucker matrix under Hodge-star duality
plDualMatrix = (i, R) -> (

    n := sub(numgens(R) / 6, ZZ);
    syms := take(a..z, n);
    s := syms_(i-1);

    P := matrix {{0, s_(1, 2)_R, s_(1, 3)_R, s_(1, 4)_R}, {0, 0, s_(2, 3)_R, s_(2, 4)_R}, {0, 0, 0, s_(3, 4)_R}, {0, 0, 0, 0}};
    
    return P - transpose(P);
)

-- inner product of two plucker vectors
plInnerProduct = (i, j, R) -> (

    A := plHashTable(i, R);
    B := plHashTable(j, R);

    return A#(1,2)*B#(3,4)-A#(1,3)*B#(2,4)+A#(1,4)*B#(2,3)+A#(2,3)*B#(1,4)-A#(2,4)*B#(1,3)+A#(3,4)*B#(1,2);
)

-- plucker ideal
plIdeal = (n, R) -> (

    return ideal apply(toList(1..n), x -> (1/2)*plInnerProduct(x, x, R))
)

-- make the vanishing ideal of the concurrent lines variety with indices L in the ring R
concurrentLinesIdeal = (L, R) -> (

    n := #L;
    quads := ideal flatten for i from 0 to n-1 list for j from i to n-1 list trace(plMatrix(L_i, R)*plDualMatrix(L_j, R));
    vecs := map(ZZ^4) | transpose matrix flatten for i from 1 to 4 list for j from i+1 to 4 list apply(toList(1..4), k -> if member(k, {i, j}) then 1 else 0);
    cubics := sum for i from 0 to 9 list minors(3, matrix(apply(L, j -> plMatrix(j, R)*vecs_i)));
    return quads + cubics
)

-- make the vanishing ideal of the coplanar lines variety with indices L in the ring R
coplanarLinesIdeal = (L, R) -> (

    n := #L;
    quads := ideal flatten for i from 0 to n-1 list for j from i to n-1 list trace(plMatrix(L_i, R)*plDualMatrix(L_j, R));
    vecs := map(ZZ^4) | transpose matrix flatten for i from 1 to 4 list for j from i+1 to 4 list apply(toList(1..4), k -> if member(k, {i, j}) then 1 else 0);
    cubics := sum for i from 0 to 9 list minors(3, matrix(apply(L, j -> plDualMatrix(j, R)*vecs_i)));
    return quads + cubics
)


-- make the ideal of the line configuration for any graph
lineIncidenceIdeal = G -> (
    
    n := #vertices(G);
    R := plProductRing(n);
    I := plIdeal(n, R);
    return I + ideal apply(edges(G)/toList, e -> plInnerProduct(e_0, e_1, R))
)


------------------------------------------------------------------
-- Useful graph functions and rigidity
------------------------------------------------------------------

-- make a graph whose vertices correspond to triangles in T 
-- and whose edges correspond to pairs of triangles which intersect in a line
triangleGraph = T -> (

    E := for S in subsets(#T, 2) list if #intersect(set T_(S_0), set T_(S_1)) == 2 then S else continue;
    return graph(toList(0..#T-1), E)
)

-- find all the triangles in G
triangles = G -> (
    
    n := #vertices(G);
    return select(subsets(toList(1..n), 3), L -> #edges(inducedSubgraph(G, L)) == 3)
);



-- check if a graph is (k, l)-sparse
-- note this method is not optimal and just brute-force checks every induced subgraph
isSparse = (k, l, G) -> (

    V := vertices(G);

    for A in subsets(V) do(

        if #A <= 2 then continue;

        n' := #A;
        G' := inducedSubgraph(G, A);
        if #edges(G') <= k*n' - l then continue else return false;
    );

    return true;
)

-- find the indices of the edge set of a graph in the set of all possible edges
graphToInd = E -> (

    allSubs := subsets(toList(1..n), 2);
    inds := E / (e -> position(allSubs, i -> i == e));
    return sort(inds)
)

-- check if a graph contains a K4
containsK4 = (n, E) -> (

    G := graph(toList(1..n), E);
    for A in subsets(toList(1..n), 4) do if #edges(inducedSubgraph(G, A)) == 6 then return true;

    return false
)


-- compute the jacobian of the map \delta_G in Section 5 which parametrizes the Cayler-Menger variety
-- this is the matrix which yields a representation of the rigidity matroid
rigidityJacobian = n -> (

    S := QQ[x_1..x_n, y_1..y_n];
    images = matrix {for e in subsets(toList(1..n), 2) list(

        (i, j) := toSequence e;
        
        (x_i - x_j)^2 + (y_i - y_j)^2
    )};

    return jacobian images
)

-- compute the rigidity rank by evaluating the jacobian at many points over a finite field
rigidityRank = method(Options => {SpecializeJacobian => true, Trials => 100, Coefficients => ZZ/32003});
rigidityRank (Number, List) := Number => opts -> (n, E) -> (

    J := rigidityJacobian(n);
    allSubs := subsets(toList(1..n), 2);
    inds := E / (e -> position(allSubs, i -> i == sort e));
    JG = J_inds;

    if not opts.SpecializeJacobian then return rank JG;

    ranks = apply(opts.Trials, t -> rank sub(JG, apply(gens ring JG, x -> x => random(opts.Coefficients))));
    return max ranks
)

rigidityRank Graph := Number => opts -> G -> rigidityRank(#vertices(G), apply(edges(G), toList), SpecializeJacobian => opts.SpecializeJacobian, Trials => opts.Trials, Coefficients => opts.Coefficients)


------------------------------------------------------------------
-- Functions for decomposition and primality testing
------------------------------------------------------------------

-- compute the minimal primes of a triangulation of an n-gon as described in Theorem 4.10
triangleDecomposition = (G, I) -> (

    triangles := select(subsets(toList(1..n), 3), L -> #edges(inducedSubgraph(G, L)) == 3);
    T := triangleGraph(triangles);

    -- make a hashtable which will store our components
    idealHash := new MutableHashTable;

    -- loop through every coloring of our triangle graph to build our components
    for A in subsets(vertices(T)) list(
        B := select(vertices(T), i -> not member(i, A));
        H := deleteEdges(T, flatten for a in A list for b in B list {a, b});
        connComps := apply(connectedComponents(H), i -> unique flatten triangles_i);
        labelComps := apply(connectedComponents(H), connComps, (i, j) -> {if member(i_0, A) then 0 else 1, j});
        idealHash#labelComps = sum(apply(labelComps, i -> if i_0 == 0 then concurrentLinesIdeal(i_1, R) else coplanarLinesIdeal(i_1, R))) + I;
    );

    filter out keys using some plabic graph rules
    goodKeys := for key in keys(idealHash) list(

        maxLength := max apply(key, i -> #i_1);
        
        if maxLength == n and #key > 1 then continue else key
    );

    return idealHash;

    return hashTable apply(goodKeys, i -> {i, idealHash#i})
)


-- check if the polynomial g is a zero divisor modulo I
isZeroDivisor = (g, I) -> (

    R := ring I;
    S := R / I;
    M := sub(matrix({{g}}), S);
    return ker(M) != 0
)


-- check if an ideal is prime using Proposition 23 of https://arxiv.org/pdf/math/0301255
-- this involves elimination but is often faster than the default isPrime in M2
primeDescent = J -> (

    R := ring J;
    idealList := {J};
    witnesses := {};
    elimVars := gens R;

    for x in gens(R) do(

        I := idealList_(-1);

        if not (isSubset({x}, support I)) then continue;

        foundf = false;

        for f in (flatten entries gens I) do(

            suppf := support f;

            if not isSubset({x}, suppf) then continue;

            g = f // x;
            h = f % x;
            if f != x*g + h then error 0;
            f' = f;
            --print(f);

            if member(x, support h) or member(x, support g) then continue;

            if isZeroDivisor(g, I) then continue else(

                foundf = true;
                witnesses = append(witnesses, {f', x, g, h});
                break;
            );

        );

        if foundf then idealList = append(idealList, eliminate(x, I));
    );

    return isPrime last idealList; 
);


------------------------------------------------------------------
-- Affine coordinates for line incidence ideals
------------------------------------------------------------------

-- make the ring of affine coordinates which correspond to setting p_(1,2) = 1
affineIncidenceRing = n -> QQ[a_(1,1,1)..a_(n, 2, 2)]


-- make the 2x4 matrix which encodes a line in our affine coordinate system
affineLineMatrix = i -> matrix{{1, 0, a_(i, 1, 1), a_(i, 1, 2)}, {0, 1, a_(i, 2, 1), a_(i, 2, 2)}}


-- make the equation corresponding to the edge ij in affine coordinates
edgeEqn = (i, j) -> det(plMatrix(i)||plMatrix(j))


-- make the line incidence ideal in affine coordinates
affineEdgeIdeal = E -> ideal apply(E, i -> edgeEqn(i_0, i_1))





