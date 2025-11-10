using Infiltrator

@doc raw"""
    det_ff(A::AbstractAlgebra.Generic.MatSpaceElem{FqPolyRingElem}) -> FqPolyRingElem

Returns the rank of A using interpolation. 
"""
function det_ff(A::AbstractAlgebra.Generic.MatSpaceElem{FqPolyRingElem})
    start = time_ns()
    #println("Start!")
    Fx = parent(A[1,1])
    F = base_ring(Fx)
    n = nrows(A)
    maxdeg = maximum(degree(A[i,j]) for i in 1:n, j in 1:n)
    det_deg = maxdeg*n
    #t1 = time_ns()
    #println("Abschnitt 1: ", (t1 - start) / 1e6, " ms")
    # determine the smallest natural number m, such that det_deg+1 <= p^m
    m = ceil(Int, log(order(F), ZZ(det_deg+1)))
    Fq = GF(order(F), m)
    Fqy, y = polynomial_ring(Fq, :y)
    input = Vector{FqFieldElem}(undef, det_deg+1)
    dets = Vector{FqFieldElem}(undef, det_deg+1)
    a = zero(Fq)
    A_lifted = matrix(Fqy, zeros(Fqy,n,n))
    for i = 1:n
        for j = 1:n
            A_lifted[i,j] = lift_polynomial(A[i,j], Fqy)
        end
    end
    #t2 = time_ns()
    #println("Abschnitt 2: ", (t2 - start) / 1e6, " ms")
    A_eval = matrix(Fq, zeros(Fqy,n,n))
    for i = 1:det_deg+1
        A_eval = map_entries(p -> evaluate(p, a), A_lifted)
        #for j = 1:n
        #    for k = 1:n 
        #        A_eval[j,k] = evaluate(A_lifted[j,k], a)
        #    end
        #end
        input[i] = a
        dets[i] = det(A_eval)
        #push!(input, a)
        #push!(dets, det(A_i))
        #push!(dets, one(Fq))
        a = next_element(a)
    end
    A0 = matrix(Fq,zeros(Fq,det_deg+1,det_deg+1))
    #t3 = time_ns()
    #println("Abschnitt 3: ", (t3 - start) / 1e6, " ms")
    for i = 0:det_deg
        for j = 0:det_deg
            #if (counter > det_deg)
            #    break
            #end
            A0[i+1,j+1] = input[j+1]^(i)
            #counter += 1
        end
    end
    #println("Lösen des LGS...")
    coeffs = solve(A0, dets)
    #println("fertig!")
    g = Fqy(coeffs)
    return lift_polynomial(g, Fx)
end

function next_element(x::FqFieldElem)
    Fq = parent(x)
    a = gen(Fq)
    deg = degree(Fq)
    for i = 0:deg-1
        x += one(Fq)*a^i
        if (coeff(x, i) != 0)
            break
        end
    end
    return x
end

function lift_polynomial(f::FqPolyRingElem, Fx::FqPolyRing)
    deg = degree(f)
    g = zero(Fx)
    x = gen(Fx)
    for i = 0:deg
        g += Fx(lift(ZZ, coeff(f, i)))*x^i
    end
    return g
end

function lift_polynomial(f::MPolyRingElem, Fx::MPolyRing, l::Nemo.FinFieldMorphism{FqField, FqField})
    #g = zero(Fx)
    #x = gens(Fx)
    #for i = 0:degree(f)
    #    g += l(coeff(f, i))*x^i
    #end
    #return g

    degs = degrees(f)
    g = zero(Fx)
    x = gens(Fx)
    for tup in Iterators.product((0:ni for ni in degs)...)
        monom = l(coeff(f, collect(tup)))
        for i = 1:number_of_variables(Fx)
            monom *= x[i]^tup[i]
        end
        g += monom
    end
    return g
end

function lift_polynomial(f::PolyRingElem, Fx::MPolyRing)
    g = zero(Fx)
    x = gens(Fx)[1]
    for i = 0:degree(f)
        g += coeff(f, i)*x^i
    end
    return g
end

function lift_polynomial(f::FqMPolyRingElem, Fqx::FqMPolyRing)
    degs = degrees(f)
    g = zero(Fqx)
    x = gens(Fqx)
    for tup in Iterators.product((0:ni for ni in degs)...)
        monom = Fqx(lift(ZZ, coeff(f, collect(tup))))
        for i = 1:number_of_variables(Fqx)
            monom *= x[i]^tup[i]
        end
        g += monom
    end
    return g
end


function random_ff_matrix(Qx::QQPolyRing, n::Int, m::Int, range::Int, d::Int)
    x = gen(Qx)
    S = matrix_space(QQ, n, m)
    M = zero(Qx)
    for i = 0:d
        r = rand(S, -range:range)
        M += r*x^i
    end
    return M
end

function random_ff_matrix(Kx::T,
                             n::Int, m::Int, range::Int, d_nom::Int, d_denom::Int) where T <: AbstractAlgebra.Generic.RationalFunctionField
    x = gen(Kx)
    S = matrix_space(base_ring(Kx), n, m)
    M_num = zero_matrix(Kx, n, m)
    M_denom = zero_matrix(Kx, n, m)
    for i = 0:d_nom
        r = rand(S, -range:range)
        M_num += r*x^i
    end
    for i = 0:d_denom
        r = rand(S, -range:range)
        M_denom += r*x^i
    end
    #println(typeof(M_num))
    for i = 1:n
        for j = 1:m
            if (M_denom[i,j] == zero(Kx))
                M_denom[i,j] = one(Kx)
            end
            M_num[i,j] = M_num[i,j]//M_denom[i,j]
            #denominator(M_nom[i,j]) 
            #denominator(M_nom[i,j]) = numerator(M_denom[i,j])
        end
    end
    return M_num
end

function random_ff_matrix(Fx::FqMPolyRing, n::Int, m::Int, range::Int, d::Int)
    x = gens(Fx)
    num_vars = number_of_variables(Fx)
    S = matrix_space(base_ring(Fx), n, m)
    M = zero(Fx)
    #for tup in Iterators.product((0:d for ni in 1:num_vars)...)
    for tup in Oscar.Hecke.cartesian_product_iterator(0:d, num_vars)
        r = rand(S, -range:range)
        #monom = Fqx(lift(ZZ, coeff(f, collect(tup))))
        for i = 1:num_vars
            r *= x[i]^tup[i]
        end
        M += r
    end
    return M
end

function det_ff(A::AbstractAlgebra.Generic.MatSpaceElem{QQPolyRingElem})

    Qx = parent(A[1,1])
    n = nrows(A)
    maxdeg = maximum(degree(A[i,j]) for i in 1:n, j in 1:n)
    det_deg = maxdeg*n

    dets = Vector{QQFieldElem}(undef, det_deg+1)
    input = Vector{QQFieldElem}(undef, det_deg+1)

    A_eval = zero_matrix(QQ,n,n)
    if (det_deg % 2 == 0)
        b2 = QQ(det_deg)/2
    else
        b2 = QQ(det_deg+1)/2
    end

    for i = 1:det_deg+1
        a = QQ(i)-b2
        A_eval = map_entries(p -> evaluate(p, a), A)
        dets[i] = det(A_eval)
        input[i] = a
        #println(A_eval)
    end

    return interpolate(Qx, input, dets)

    #A0 = matrix(QQ,zeros(QQ,det_deg+1,det_deg+1))
    #for j = 1:det_deg+1
    #    a = one(QQ)
    #    e = QQ(j)-b2
    #    for i = 1:det_deg+1
    #        A0[i,j] = a
    #        a *= e
    #    end
    #end
    #coeffs = solve(A0, dets)
    #return Qx(coeffs)
end

function det_ff(A::AbstractAlgebra.Generic.MatSpaceElem{AbstractAlgebra.Generic.RationalFunctionFieldElem{QQFieldElem, QQPolyRingElem}})
    M = A
    Qx, _ = polynomial_ring(QQ, :x)
    denom = one(parent(A[1,1]))
    for i = 1:nrows(A)
        for j = 1:ncols(A)
            M = multiply_row(M, denominator(M[i,j]), i)
            denom *= denominator(M[i,j])
        end
    end
    return 1//denom * det_ff(matrix(Qx,M))
end

function det_fff(A::AbstractAlgebra.Generic.MatSpaceElem{QQPolyRingElem})
    Qx = parent(A[1,1])
    n = nrows(A)
    for i = 1:nrows(A)
        for j = 1:ncols(A)
            M = multiply_row(M, denominator(M[i,j]), i)
            denom *= denominator(M[i,j])
        end
    end
end
function rank_ff(A::AbstractAlgebra.Generic.MatSpaceElem{AbstractAlgebra.Generic.RationalFunctionFieldElem{QQFieldElem, QQPolyRingElem}})
    M = deepcopy(A)
    Qx, _ = polynomial_ring(QQ, :x)
    for i = 1:nrows(A)
        for j = 1:ncols(A)
            if (denominator(M[i,j]) != one(Qx))
                if nrows(A) < ncols(A)
                    multiply_column!(M, denominator(M[i,j]), j)
                else
                    multiply_row!(M, denominator(M[i,j]), i)
                end
            end
        end
    end
    return rank_ff(matrix(Qx,M))
end

@doc raw"""
    rank_ff(A::AbstractAlgebra.Generic.MatSpaceElem{QQPolyRingElem}) -> Int

Returns the rank of A. 
"""
function rank_ff(A::AbstractAlgebra.Generic.MatSpaceElem{QQPolyRingElem})

    #Qx = parent(A[1,1])
    n = nrows(A)
    m = ncols(A)
    min_ = min(n,m)
    maxdeg = maximum(degree(A[i,j]) for i in 1:n, j in 1:m)
    det_deg = maxdeg*min_
    maxrank = 0
    #ranks = Vector{QQFieldElem}(undef, det_deg+1)
    #input = Vector{QQFieldElem}(undef, det_deg+1)

    A_eval = matrix(QQ, zeros(QQ,n,m))
    b2 = ceil(Int, det_deg/2)
    #if (det_deg % 2 == 0)
    #    b2 = QQ(det_deg)/2
    #else
    #    b2 = QQ(det_deg+1)/2
    #end

    a = -QQ(b2)
    for i = 1:det_deg+1
        A_eval = map_entries(p -> evaluate(p, a), A)
        maxrank = max(rank(A_eval), maxrank)
        if (maxrank == min_)
            break
        end
        a += 1
    end

    return maxrank
end



function rank_ff(A::AbstractAlgebra.Generic.MatSpaceElem{FqPolyRingElem})

    Fx = parent(A[1,1])
    F = base_ring(Fx)
    n = nrows(A)
    m = ncols(A)
    min_ = min(n,m)
    maxdeg = maximum(degree(A[i,j]) for i in 1:n, j in 1:m)
    det_deg = maxdeg*min_
    maxrank = 0

    
    if(size(F) == characteristic(F)) 

        expo = ceil(Int, log(characteristic(F), ZZ(det_deg+1)))
        Fq = GF(characteristic(F), expo)
        Fqy, y = polynomial_ring(Fq, :y)
        a = zero(Fq)
        A_lifted = matrix(Fqy, zeros(Fqy,n,m))
        for i = 1:n
            for j = 1:m
                A_lifted[i,j] = lift_polynomial(A[i,j], Fqy)
            end
        end
        #t2 = time_ns()
        #println("Abschnitt 2: ", (t2 - start) / 1e6, " ms")
        A_eval = matrix(Fq, zeros(Fqy,n,m))
        for i = 1:det_deg+1
            A_eval = map_entries(p -> evaluate(p, a), A_lifted)
            maxrank = max(rank(A_eval), maxrank)
            if (maxrank == min_)
                #break
            end
            a = next_element(a)
        end
    
    else

        A_representation = absolute_representation_matrix(A)
        r = Int(rank_ff(A_representation)/degree(F))
        return r

        min_poly = minimal_polynomial(gen(F))
        _, ϕ = residue_field(parent(min_poly), min_poly)
    end
    return maxrank
end

function rank_ff(A::AbstractAlgebra.Generic.MatSpaceElem{FqMPolyRingElem})
    
    Fx = parent(A[1,1])
    F = base_ring(Fx)
    num_vars = number_of_variables(Fx)
    
    n = nrows(A)
    m = ncols(A)
    min_ = min(n,m)
    maxdegs = Vector{Int}(undef, num_vars)

    for k = 1:num_vars
        maxdegs[k] = maximum(degree(A[i,j], k) for i in 1:n, j in 1:m)
    end
    det_degs = maxdegs*min_
    num_evals = prod(det_degs[i]+1 for i in 1:num_vars)
    height = maximum(det_degs[i] for i in 1:num_vars)
    maxrank = 0
    #println("det_degs: " * string(det_degs) * ", height: " * string(height) * ", num_vars: " * string(num_vars))
    
    if(size(F) == characteristic(F)) 

        expo = ceil(Int, log(characteristic(F), ZZ(height+1)))
        Fq = GF(characteristic(F), expo)
        Fqy, y = polynomial_ring(Fq, num_vars, :y)
        #a = zero(Fq)
        A_lifted = matrix(Fqy, zeros(Fqy,n,m))
        for i = 1:n
            for j = 1:m
                A_lifted[i,j] = lift_polynomial(A[i,j], Fqy)
            end
        end

        eval_set = get_eval_set(height+1, Fq)
        #println(A_lifted)
        a = FqFieldElem[]
        return rank_ff_helper(det_degs, a, A_lifted, min_, eval_set)
        #t2 = time_ns()
        #println("Abschnitt 2: ", (t2 - start) / 1e6, " ms")
        #A_eval = matrix(Fq, zeros(Fqy,n,m))

        #for tup in Iterators.product((1:ni for ni in det_degs)...)
            
        #    A_eval = map_entries(p -> evaluate(p, a), A_lifted)
        #    maxrank = max(rank(A_eval), maxrank)
        #    if (maxrank == min_)
                #break
        #    end
        #    a = next_element(a)
        #end
        return maxrank
    else

        #min_poly = minimal_polynomial(gen(F))
        #_, ϕ = residue_field(parent(min_poly), min_poly)
        return -1
    end
    
end

function get_eval_set(n::Int, Fq::FqField)
    set = Vector{FqFieldElem}(undef, n)
    a = zero(Fq)
    set[1] = a
    for i = 2:n
        a = next_element(a)
        set[i] = a
    end
    return set
end

function preimage_eval(a::FqPolyRingElem, Fy::FqMPolyRing)

    Fqx = parent(a)
    Fq = base_ring(Fqx)
    dx = degree(a)
    d = degree(Fq)
    f = zero(Fy)
    y = gens(Fy)
    for i = 0:dx
        for j = 0:d-1
            f += Fy(lift(ZZ,coeff(coeff(a, i), j)))* y[1]^i* y[2]^j
        end
    end
    return f
end

function preimage_eval(A::AbstractAlgebra.Generic.MatSpaceElem{FqPolyRingElem}, Fy::FqMPolyRing)
    n = nrows(A)
    m = ncols(A)
    A_new = matrix(Fy, zeros(Fy,n,m))
    for i = 1:n
        for j = 1:m
            A_new[i,j] = preimage_eval(A[i,j], Fy)
        end
    end
    return A_new
end

function rank_ff_helper(det_degs::Vector{Int}, a::Vector{FqFieldElem}, A_lifted::AbstractAlgebra.Generic.MatSpaceElem{FqMPolyRingElem}, 
                        min_::Int, eval_set::Vector{FqFieldElem})
    i = length(a) + 1
    if i > length(det_degs)
        A_eval = map_entries(p -> evaluate(p, a), A_lifted)
        #println(A_eval)
        return rank(A_eval)
        #maxrank = max(rank(A_eval), maxrank)
        #    if (maxrank == min_)
        #       break
        #    end
    else
        maxrank = 0
        for idx in 1:det_degs[i]+1
            push!(a, eval_set[idx])
            maxrank = max(maxrank, rank_ff_helper(det_degs, a, A_lifted, min_, eval_set))
            pop!(a)
            if (maxrank == min_)
                break
            end
        end
        return maxrank
    end
end

function absolute_representation_matrix(A::AbstractAlgebra.Generic.MatSpaceElem{FqPolyRingElem})
    
    Fqx = parent(A[1,1])
    Fq = base_ring(Fqx)
    F = prime_field(Fq)
    Fy, y = polynomial_ring(F, :y)

    d = degree(Fq)
    n = nrows(A)
    m = ncols(A)
    A_new = matrix(Fy, zeros(Fy,d*n,d*m))
    for i = 0:n-1
        for j = 0:m-1
            M = absolute_representation_matrix(A[i+1,j+1], Fy, d)
            for k = 1:d 
                for l = 1:d
                    A_new[i*d+k, j*d+l] = M[k,l]
                end
            end
        end
    end
    return A_new
end

function absolute_representation_matrix(f::FqPolyRingElem, Fx::FqPolyRing, d::Int)
    dx = degree(f)
    x = gen(Fx)
    A = matrix(Fx, zeros(Fx, d,d))
    for i = 0:dx
        A += x^i * absolute_representation_matrix(coeff(f,i))
    end
    return A
end

function solve_ff(A::AbstractAlgebra.Generic.MatSpaceElem{AbstractAlgebra.Generic.RationalFunctionFieldElem{QQFieldElem, QQPolyRingElem}}, 
                    b::AbstractAlgebra.Generic.MatSpaceElem{AbstractAlgebra.Generic.RationalFunctionFieldElem{QQFieldElem, QQPolyRingElem}})
    n = nrows(A)
    m = ncols(A)
    Qx = parent(A[1,1])
    if nrows(b) != 1
        error("Second argument must be a row vector")
    end
    if ncols(b) != ncols(A)
        error("Number of rows of matrix does not eqaul to the length of row vector")
    end

    M = matrix(Qx, zeros(Qx, n+1,m))
    for i = 1:n
        for j = 1:m
            M[i,j] = A[i,j]
        end
    end
    for j = 1:m
        M[n+1,j] = b[1,j]
    end
    K = kernel(M)
    #println(typeof(K))
    #println(parent(K[1,n]))
    #println(parent(zero(Qx)))
    for i = 1:nrows(K)
        if K[i,n+1] != zero(Qx)
            return -1//K[i,n+1] * K[i:i,1:n]
        end
    end
    error("Linear system has no solution")
end

function kernel_ff(A::AbstractAlgebra.Generic.MatSpaceElem{QQPolyRingElem},flag::Bool)

    Qx = parent(A[1,1])
    Qy, y = rational_function_field(QQ, var(Qx))
    K = kernel_ff(matrix(Qy,A), flag)
    for i = 1:nrows(K)
        for j = 1:ncols(K)
            K = multiply_row!(K, denominator(K[i,j]), i)
        end
    end
    return matrix(Qx,K)
end
    
function kernel_ff(A::AbstractAlgebra.Generic.MatSpaceElem{AbstractAlgebra.Generic.RationalFunctionFieldElem{QQFieldElem, QQPolyRingElem}}, flag::Bool)
    M = deepcopy(A)
    Qx = parent(A[1,1])
    r = rank_ff(A)
    n = nrows(A)
    m = ncols(A)
    rows = Int[]
    rows_to_swap = Int[]
    cols = Int[]
    cols_to_swap = Int[]

    if (r == n)
        return zero_matrix(Qx, 0, ncols(A))
    end

    #swap columns such that the first r columns are linearly independent
    for j = 1:m
        if(rank_ff(M[:,vcat(cols, [j])]) == length(cols)+1)
            if (j > r) 
                push!(cols, pop!(cols_to_swap))
                M = swap_cols!(M, j, last(cols))
            else 
                push!(cols, j)
            end
            if(length(cols) == r)
                break
            end
        else
            if(j <= r)
                push!(cols_to_swap,j)
            end
        end
    end

    #swap rows such that the first r rows are linearly independent - since swapping rows leads to swapping entries of kernel K, 
    #we save our swaps in rows_to_swap and use it later to swap back
    for i = 1:n
        if(rank_ff(M[vcat(rows, [i]),:]) == length(rows)+1)
            if (i > r) 
                push!(rows, popfirst!(rows_to_swap))
                M = swap_rows!(M, i, last(rows))
                push!(rows_to_swap, i)
            else 
                push!(rows, i)
            end
            if(length(rows) == r)
                break
            end
        else
            if(i <= r)
                push!(rows_to_swap,i)
            end
        end
    end
    #Qy, y = rational_function_field(QQ, var(Qx))
    #det_rr = det(M[1:r,1:r])
    #M_inv = inv_ff(map_entries(t -> evaluate(t,y), M[1:r,1:r]))*evaluate(det_rr, y)
    
    K = zero_matrix(Qx, n-r,n)
    if flag
        #1. Variante - mit Matrix invertieren
        M_inv = inv(M[1:r,1:r])
        for i = 1:(n-r)
            #z_i = map_entries(t -> evaluate(t,y), M[i+r:i+r,1:r])*M_inv
            z_i = M[i+r:i+r,1:r]*M_inv
            for j = 1:r
                K[i,j] = z_i[j]
            end
        end
    else
        #2. Variante - mit solve GLS
        for i = 1:n-r
            z_i = solve(M[1:r,1:r], M[i+r:i+r,1:r])
            for j = 1:r
                K[i,j] = z_i[j]
            end
        end
    end


    for i = 1:(n-r)
        K[i,r+i] = -1
    end
    #for i = 1:(n-r)
    #    K[i,r+i] = -det_rr
    #end

    #swap back to get the true kernel matrix
    for i = 1:length(rows_to_swap)
        K = swap_cols!(K, rows[length(rows)+1-i], rows_to_swap[length(rows_to_swap)+1-i])
    end
    return K
end

function inv_ff(A::AbstractAlgebra.Generic.MatSpaceElem{AbstractAlgebra.Generic.RationalFunctionFieldElem{QQFieldElem, QQPolyRingElem}})

    n = nrows(A)
    Qx = parent(A[1,1])
    d = det(A)
    if (d == Qx(0) || n != ncols(A))
        error("Matrix is not invertible")
    end
    D = zero_matrix(Qx, n,n)
    for i= 1:n
        for j = 1:n
            M = A[vcat(1:(i-1), (i+1):n), vcat(1:(j-1), (j+1):n)]
            D[j,i] = det(M)*(-1)^(i+j)
        end
    end
    D = D* (1//d)
    return D
end

























#TESTSPACE
function rank_ff_abstract(M::MatrixElem{T}) where {T <: NumFieldElem}
    return rank_nf(M)
end

function rank_ff_abstract(M::MatrixElem{T}) where {T <: FieldElem}
    return rank(M)
end

function rank_ff_abstract(M::MatrixElem{T}) where {T <: PolyRingElem}
    Kx = parent(M[1,1])
    K = base_ring(Kx)
    n = nrows(M)
    m = ncols(M)

    if (!(typeof(K) <: Field))
        error("base ring is not a field!")
    end

    #The maximum degree of det(M') is calculated where M' is an arbitrary quadratic submatrix of M.
    min_ = min(n,m)
    maxdeg = maximum(degree(M[i,j]) for i in 1:n, j in 1:m)
    det_deg = maxdeg*min_
    r = 0

    eval_set, flag = get_eval_set(K, det_deg+1)
    if flag
        #rank(M) is calculated by computing the rank of det_deg+1 matrices, evaluated in an element of eval_set, respectively.
        for elem in eval_set
            M_eval = map_entries(p -> evaluate(p,elem), M)
            r = max(rank_ff_abstract(M_eval), r)
            if (r == min_)
                break
            end
        end
        return r
    else
        #function get_eval_set throws an error if and only if K is a finite field and order(K) < det_deg+1 holds. 
        #In this case a field extension L of K such that order(L) >= det_deg+1 is constructed.
        #d is the smallest natural number such that order(K)^d >= det_deg+1.
        d = ceil(Int, log(order(K), ZZ(det_deg+1)))
        L, l = Oscar.Nemo._extension(K, d)
        Lx, _ = polynomial_ring(L, var(Kx)) 

        #The given matrix M is embedded into the space of matrices over Lx
        A = matrix(Lx,n,m, [lift_polynomial(M[i,j], Lx, l) for i in 1:n, j in 1:m])
        return rank_ff_abstract(A)
    end

end

function rank_ff_abstract(M::MatrixElem{T}) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    Kx = parent(M[1,1])
    K = base_ring(Kx)
    n = nrows(M)
    m = ncols(M)

    if (!(typeof(K) <: Field))
        error("base ring is not a field!")
    end
    #In this case all rows/columns of M are multiplied with polynomials such that all entries of M have denominator 1.
    #Then M can be considered as a matrix over some polynomial ring. 
    A = deepcopy(M)
    one_ = one(Kx)
    Ky = parent(numerator(one_))
    for i = 1:n
        for j = 1:m
            if (denominator(A[i,j]) != one_)
                if n < m
                    multiply_column!(A, denominator(M[i,j]), j)
                else
                    multiply_row!(A, denominator(M[i,j]), i)
                end
            end
        end
    end
    return rank_ff_abstract(matrix(Ky,n,m,[numerator(A[i,j]) for i in 1:n, j in 1:m]))
end

function rank_ff_abstract(M::MatrixElem{T}) where {T <: MPolyRingElem}
    Kx = parent(M[1,1])
    K = base_ring(Kx)
    n = nrows(M)
    m = ncols(M)
    num_vars = number_of_variables(Kx)

    if (!(typeof(K) <: Field))
        error("base ring is not a field!")
    end

    #The maximum degree of det(M') is calculated where M' is an arbitrary quadratic submatrix of M.
    min_ = min(n,m)
    maxdeg = [maximum(degree(M[i,j], k) for i in 1:n, j in 1:m) for k in 1:num_vars]
    det_deg = maxdeg*min_
    r = 0
    flag = true
    eval_set = Vector{Vector{elem_type(K)}}(undef, num_vars)

    for i = 1:num_vars
        eval_set[i], fl = get_eval_set(K, det_deg[i]+1)
        flag &= fl
    end

    if flag
        #rank(M) is calculated by computing the rank of (det_deg+1)^number_of_variables(Kx) matrices, evaluated in elements of eval_set.
        for tup in Oscar.Hecke.cartesian_product_iterator(eval_set)
            M_eval = map_entries(p -> evaluate(p,tup), M)
            r = max(rank_ff_abstract(M_eval), r)
            if (r == min_)
                break
            end
        end
        return r
    else
        #function get_eval_set returns false if and only if K is a finite field and order(K) < det_deg+1 holds. 
        #In this case a field extension L of K such that order(L) >= det_deg+1 is constructed.
        #d is the smallest natural number such that order(K)^d >= det_deg+1.
        d = ceil(Int, log(order(K), ZZ(det_deg+1)))
        L, l = Oscar.Nemo._extension(K, d)
        Lx, _ = polynomial_ring(L, symbols(Kx)) 

        #The given matrix M is embedded into the space of matrices over Lx
        A = matrix(Lx,n,m, [lift_polynomial(M[i,j], Lx, l) for i in 1:n, j in 1:m])
        return rank_ff_abstract(A)
    end
end

function kernel_ff_abstract(M::MatrixElem{T}) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    A = deepcopy(M)
    Kx = parent(A[1,1])
    n = nrows(A)
    m = ncols(A)
    rows = Int[]
    rows_to_swap = Int[]
    cols = Int[]
    cols_to_swap = Int[]



    for i = 1:n
        for j = 1:m
            if (denominator(A[i,j]) != one(Kx))
                if n < m
                    multiply_column!(A, denominator(A[i,j]), j)
                else
                    multiply_row!(A, denominator(A[i,j]), i)
                end
            end
        end
    end

    r = rank_ff_abstract(A)

    if (r == n)
        return zero_matrix(Kx, 0, ncols(A))
    end
    #swap columns such that the first r columns are linearly independent
    for j = 1:m
        if(rank_ff_abstract(A[:,vcat(cols, [j])]) == length(cols)+1)
            push!(cols, j) 
            if(length(cols) == r)
                break
            end
        else
            if(j <= r)
                push!(cols_to_swap,j)
            end
        end
    end

    #swap rows such that the first r rows are linearly independent - since swapping rows leads to swapping entries of kernel K, 
    #we save our swaps in rows_to_swap and use it later to swap back
    for i = 1:n
        if(rank_ff_abstract(A[vcat(rows, [i]),:]) == length(rows)+1)
            push!(rows, i)
            if(length(rows) == r)
                break
            end
        else
            if(i <= r)
                push!(rows_to_swap,i)
            end
        end
    end

    A = deepcopy(M)

    for j = 0:length(cols_to_swap)-1
        #swap_cols!(M, cols_to_swap[j], cols[r-j])
        swap_cols!(A, cols[length(cols)-j], cols_to_swap[length(cols_to_swap)-j])
    end
    for i = 0:length(rows_to_swap)-1
        #swap_rows!(M, rows_to_swap[i], rows[r-i])
        swap_rows!(A, rows[length(rows)-i], rows_to_swap[length(rows_to_swap)-i])
    end
    


    #Qy, y = rational_function_field(QQ, var(Qx))
    #det_rr = det(M[1:r,1:r])
    #M_inv = inv_ff(map_entries(t -> evaluate(t,y), M[1:r,1:r]))*evaluate(det_rr, y)
    
    K = zero_matrix(Kx, n-r,n)
    #1. Variante - mit Matrix invertieren
    A_inv = inv(A[1:r,1:r])
    for i = 1:(n-r)
        #z_i = map_entries(t -> evaluate(t,y), M[i+r:i+r,1:r])*M_inv
        z_i = A[i+r:i+r,1:r]*A_inv
        for j = 1:r
            K[i,j] = z_i[j]
        end
    end

    #2. Variante - mit solve GLS
    #for i = 1:n-r
    #    z_i = solve(M[1:r,1:r], M[i+r:i+r,1:r])
    #    for j = 1:r
    #        K[i,j] = z_i[j]
    #    end
    #end



    for i = 1:(n-r)
        K[i,r+i] = -1
    end
    #for i = 1:(n-r)
    #    K[i,r+i] = -det_rr
    #end

    #swap back to get the true kernel matrix
    for i = 1:length(rows_to_swap)
        swap_cols!(K, rows[length(rows)+1-i], rows_to_swap[length(rows_to_swap)+1-i])
    end
    return K
end

#function swap_rows_cols(M::MatrixElem{T}, swaps::Tuple{Vector{Int}, Vector{Int}}, rank::Int) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
#    for j = 1:m
#        if(rank_ff_abstract(M[:,vcat(cols, [j])]) == length(cols)+1)
#            if (j > r) 
#                push!(cols, pop!(cols_to_swap))
#                M = swap_cols!(M, j, last(cols))
#            else 
#                push!(cols, j)
#            end
#            if(length(cols) == r)
#                break
#            end
#        else
#            if(j <= r)
#                push!(cols_to_swap,j)
#            end
#        end
#    end
#end

function get_eval_set(K::Field, n::Int)

    if (n <= 0)
        error("n must be positive!")
    end
    set = Vector{elem_type(K)}(undef, n)

    if (typeof(K) == FqField)
        if (size(K) < n)
            return (set,false)
        end
        set[1] = zero(K)
        for i = 2:n
            set[i] = next_element(set[i-1])
        end
    elseif (typeof(K) <: AbstractAlgebra.Generic.RationalFunctionField)
        F = base_ring(K)
        set, flag = get_eval_set(F, n)
        if flag
            return (set, true)
        else
            set = elem_type(K)[]
            base_set, flag = get_eval_set(F, Int(size(F)))
            d = ceil(Int, log(size(F), ZZ(n)))
            while (length(set) < n)
                for coeffs in Oscar.Hecke.cartesian_product_iterator(base_set, d)
                #for coeffs in Iterators.product(ntuple(_ -> base_set, d)...)
                    push!(set, sum(coeffs[j] * gen(K)^(j- 1) for j in 1:d))
                    if length(set) == n
                        break
                    end
                end

            end
        end
    else
        set[1] = K(div(-n,2))
        for i = 2:n
            set[i] = set[i-1] + 1
        end
    end

    return (set,true)
end

function get_eval_set(K::Field, n::Int, f::PolyRingElem)
    d = degree(f)
    if (n <= 0)
        error("n must be positive!")
    end
    set = elem_type(K)[]

    if (typeof(K) == FqField)
        if (size(K) < n+d)
            return (set,false)
        end
        elem = zero(K)
        while (length(set) < n)
            if (f(elem) != 0)
                push!(set, elem)
            end
            elem = next_element(elem)
        end
    elseif (typeof(K) <: AbstractAlgebra.Generic.RationalFunctionField)
        F = base_ring(K)
        set, flag = get_eval_set(F, n)
        if flag
            return (set, true)
        else
            set = elem_type(K)[]
            base_set, flag = get_eval_set(F, Int(size(F)))
            m = ceil(Int, log(size(F), ZZ(n+d)))
            while (length(set) < n)
                for coeffs in Oscar.Hecke.cartesian_product_iterator(base_set, m)
                #for coeffs in Iterators.product(ntuple(_ -> base_set, m)...)
                    elem = sum(coeffs[j] * gen(K)^(j- 1) for j in 1:m)
                    if (f(elem) != 0)
                        push!(set, elem)
                    end
                    if length(set) == n
                        break
                    end
                end

            end
        end
    else
        elem = K(div(-n-d,2))
        while (length(set) < n)
            if (f(elem) != 0)
                push!(set, elem)
            end
            elem += 1
        end
    end

    return (set,true)
end

function inv_ff_abstract(M::MatrixElem{T}) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    n = nrows(M)
    K = base_ring(parent(M[1,1]))
    Kx = parent(numerator(M[1,1]))
    lcm_ = lcm([denominator(M[i,j]) for i in 1:n, j in 1:n])
    #d = degree(lcm_)
    maxdeg_nums = maximum(degree(numerator(M[i,j])) for i in 1:n, j in 1:n)
    maxdeg_denoms = maximum(degree(denominator(M[i,j])) for i in 1:n, j in 1:n)
    e_len = (2n-1)*maxdeg_denoms+n*maxdeg_nums+n*(n-1)*maxdeg_denoms+ (n-1)*maxdeg_nums+(n-1)*(n-2)*maxdeg_denoms
    eval_set, _ = get_eval_set(K, e_len, lcm_)
    #@infiltrate
    e_len = length(eval_set)
    S = matrix_space(K, n, n)
    images = Vector{elem_type(S)}(undef, e_len)
    for i = 1:e_len
        S1 = map_entries(p -> p(eval_set[i]), M)
        S2 = inv(S1)
        #@infiltrate
        images[i] = S2 
        #images[i] = matrix(K, inv(map_entries(p -> p(eval_set[i]), M)))
    end
    b = prod(gen(Kx) - p for p in eval_set)
    A = zero_matrix(parent(M[1,1]), n,n)
    for i = 1:n
        for j = 1:n
            a = interpolate(Kx, eval_set, [images[k][i,j] for k in 1:e_len])
            @infiltrate
            _, f, g = rational_reconstruction(a,b)
            @infiltrate
            A[i,j] = f//g
        end
    end
    return A
end


function inv_ff_abstract_v2(M::MatrixElem{T}, mode::Int) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    #time = 0
    n = nrows(M)
    K = base_ring(parent(M[1,1]))
    Kx = parent(numerator(M[1,1]))
    x = gen(Kx)
    lcm_ = lcm([denominator(M[i,j]) for i in 1:n, j in 1:n])
    prod_ = prod(denominator(M[i,j]) for i in 1:n, j in 1:n)
    d = det(M)
    denom = numerator(d)*(prod_//denominator(d))
    #denom = lcm_
    maxdeg_nums = maximum(degree(numerator(M[i,j])) for i in 1:n, j in 1:n)
    maxdeg_denoms = maximum(degree(denominator(M[i,j])) for i in 1:n, j in 1:n)
    e_len = (2n-1)*maxdeg_denoms + (n-1)*maxdeg_nums+(n-1)*(n-2)*maxdeg_denoms + maxdeg_denoms+maxdeg_nums
    eval_set, _ = get_eval_set(K, e_len, lcm_)
    #@infiltrate

    S = matrix_space(K, n, n)
    images = elem_type(S)[]
    denoms = elem_type(K)[]
    eval_set_new = elem_type(K)[]
    for i = 1:e_len
        #time -= time_ns()
        S = map_entries(p -> p(eval_set[i]), M)
        #time += time_ns()
        if (rank(S) == n)
            #@infiltrate
            push!(images, inv(S))
            push!(denoms, denom(eval_set[i]))
            push!(eval_set_new, eval_set[i])
        end
    end
    e_len_new = length(eval_set_new)
    A = zero_matrix(parent(M[1,1]), n,n)
    #time = time_ns()
    if mode == 1
        for i = 1:n
            for j = 1:n

                num = interpolate(Kx, eval_set_new, [images[k][i,j]*denoms[k] for k in 1:e_len_new])
                #@infiltrate
                A[i,j] = num//denom
            end
        end
    elseif mode == 2
        c = crt_env([x-e for e in eval_set_new])
        for i = 1:n
            for j = 1:n
                num = crt([Kx(images[k][i,j]*denoms[k]) for k in 1:e_len_new], c)
                #@infiltrate
                A[i,j] = num//denom
            end
        end
    end
    #println("Interpolation: ", (time_ns() - time) / 1e6, " ms")
    return A
end



function inv_ff_abstract_v3(M::MatrixElem{T}, mode::Int) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    #time = 0
    n = nrows(M)
    K = base_ring(parent(M[1,1]))
    Kx = parent(numerator(M[1,1]))
    x = gen(Kx)
    lcm_ = lcm([denominator(M[i,j]) for i in 1:n, j in 1:n])
    #prod_ = prod(denominator(M[i,j]) for i in 1:n, j in 1:n)
    lcms = [lcm([denominator(M[i,j]) for i in 1:n]) for j in 1:n]
    M_new = deepcopy(M)
    for i = 1:n
        multiply_column!(M_new, lcms[i], i)
    end
    d = numerator(det(M_new))
    maxdeg = maximum(degree(numerator(M_new[i,j])) for i in 1:n, j in 1:n)

    e_len = maxdeg *(n-1) +1 + maxdeg
    eval_set, _ = get_eval_set(K, e_len, lcm_)
    #@infiltrate

    S = matrix_space(K, n, n)
    images = elem_type(S)[]
    denoms = elem_type(K)[]
    eval_set_new = elem_type(K)[]
    lcmss_ = Vector{elem_type(K)}[]
    for i = 1:e_len
        #time -= time_ns()
        S = map_entries(p -> p(eval_set[i]), M_new)
        #time += time_ns()
        if (rank(S) == n)
            #@infiltrate
            push!(images, inv(S))
            push!(denoms, d(eval_set[i]))
            push!(eval_set_new, eval_set[i])
            #v = Vector{elem_type(K)}(undef, n)
            for j = 1:n
                #v[j] = lcms[j](eval_set[i])
            end
            #push!(lcmss_,v)
        end
    end
    e_len_new = length(eval_set_new)
    A = zero_matrix(parent(M[1,1]), n,n)
    #time = time_ns()
    if mode == 1
        for i = 1:n
            for j = 1:n
                num = interpolate(Kx, eval_set_new, [images[k][i,j]*denoms[k] for k in 1:e_len_new])
                #num = interpolate(Kx, eval_set_new, [images[k][i,j]*denoms[k]/(lcmss_[k][i]) for k in 1:e_len_new])
                #@infiltrate
                A[i,j] = num*lcms[i]//d
            end
            #multiply_row!(A, lcms[i], i)
            #@infiltrate
        end
    elseif mode == 2
        c = crt_env([x-e for e in eval_set_new])
        for i = 1:n
            for j = 1:n
                num = crt([Kx(images[k][i,j]*denoms[k]) for k in 1:e_len_new], c)
                #@infiltrate
                A[i,j] = num*lcms[i]//d
            end
            #multiply_row!(A, lcms[i], i)
        end
    end
    #println("Interpolation: ", (time_ns() - time) / 1e6, " ms")
    return A
end