using Infiltrator



@doc raw"""
    rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64) where {T <: PolyRingElem} -> Int

Returns the rank of $A$ with error probability < $ϵ$.
"""
function rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64) where {T <: PolyRingElem}
    return rank_monte_carlo(M, ϵ, 10)
end

@doc raw"""
    rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: PolyRingElem} -> Int

Returns the rank of $A$ with error probability < $ϵ$. $s$ is some internal parameter.
"""
function rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: PolyRingElem}
    Kx = parent(M[1,1])
    K = base_ring(Kx)
    n = nrows(M)
    m = ncols(M)
    min_ = min(n,m)

    maxdeg = maximum(degree(M[i,j]) for i in 1:n, j in 1:n)
    det_deg = maxdeg*min_
    S = get_eval_set(K, s*det_deg)
    #k is the minimum amount of evaluations of M needed to compute the correct rank of M with error probability < ϵ
    k = ceil(log(s, 1/ϵ))
    maxrank = 0
    if !is_empty(S)
        #rank(M) is calculated by computing the rank of k matrices, evaluated in elements of eval_set, and taking the maximum
        for _ = 1:k
            a = rand(S)
            M_eval = map_entries(p -> evaluate(p,a), M)
            maxrank = max(rank(M_eval), maxrank)
            if maxrank == min_
                return maxrank
            end
        end
    else
        #function get_eval_set returns an empty set if and only if K is a finite field and order(K) < det_deg+1 holds. 
        #In this case a field extension L of K such that order(L) >= det_deg+1 is constructed.
        #d is the smallest natural number such that order(K)^d >= det_deg+1.
        d = ceil(Int, log(order(K), ZZ(det_deg*s)))
        L, l = Oscar.Nemo._extension(K, d)
        Lx, _ = polynomial_ring(L, var(Kx)) 

        #The given matrix M is embedded into the space of matrices over Lx
        A = matrix(Lx,n,m, [lift_polynomial(M[i,j], Lx, l) for i in 1:n, j in 1:m])
        return rank_monte_carlo(A, ϵ, s)
    end
    return maxrank
end

@doc raw"""
    rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem} -> Int

Returns the rank of $A$ with error probability < $ϵ$.
"""
function rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    return rank_monte_carlo(M, ϵ, 10)
end 

@doc raw"""
    rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem} -> Int

Returns the rank of $A$ with error probability < $ϵ$. $s$ is some internal parameter.
"""
function rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    #Kx = parent(M[1,1])
    n = nrows(M)
    m = ncols(M)

    #In this case all rows/columns of M are multiplied with polynomials such that all entries of M have denominator 1.
    #Then M can be considered as a matrix over some polynomial ring. 
    A = deepcopy(M)
    Ky = parent(numerator(M[1,1]))
    for i = 1:n
        for j = 1:m
            if is_one(denominator(A[i,j]))
                if n < m
                    multiply_column!(A, denominator(M[i,j]), j)
                else
                    multiply_row!(A, denominator(M[i,j]), i)
                end
            end
        end
    end
    return rank_monte_carlo(matrix(Ky,n,m,[numerator(A[i,j]) for i in 1:n, j in 1:m]), ϵ, s)
end

@doc raw"""
    rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64) where {T <: MPolyRingElem} -> Int

Returns the rank of $A$ with error probability < $ϵ$.
"""
function rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64) where {T <: MPolyRingElem}
    return rank_monte_carlo(M, ϵ, 10)
end 

@doc raw"""
    rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: MPolyRingElem} -> Int

Returns the rank of $A$ with error probability < $ϵ$. $s$ is some internal parameter.
"""
function rank_monte_carlo(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: MPolyRingElem}
    Kx = parent(M[1,1])
    K = base_ring(Kx)
    n = nrows(M)
    m = ncols(M)
    min_ = min(n,m)
    num_vars = number_of_variables(Kx)

    maxdeg = maximum(degree(M[i,j], k) for i in 1:n, j in 1:m, k in 1:num_vars)
    det_deg = maxdeg*min_
    S = get_eval_set(K, s*det_deg)
    #k is the minimum amount of evaluations of M needed to compute the correct rank of M with error probability < ϵ
    k = ceil(log(s, 1/ϵ))
    maxrank = 0

    if !is_empty(S)
        #rank(M) is calculated by computing the rank of k matrices, evaluated in elements of eval_set, and taking the maximum
        for _ = 1:k
            a = Vector{elem_type(K)}(undef, num_vars)
            for i = 1:num_vars
                a[i] = rand(S)
            end
            M_eval = map_entries(p -> evaluate(p,a), M)
            maxrank = max(rank(M_eval), maxrank)
            if maxrank == min_
                return maxrank
            end
        end
        return maxrank
    else
        #function get_eval_set returns an empty set if and only if K is a finite field and order(K) < det_deg*s holds. 
        #In this case a field extension L of K is constructed such that order(L) >= det_deg*s.
        #d is the smallest natural number such that order(K)^d >= det_deg*s.
        d = ceil(Int, log(order(K), ZZ(det_deg*s)))
        L, l = Oscar.Nemo._extension(K, d)
        Lx, _ = polynomial_ring(L, symbols(Kx)) 

        #The given matrix M is embedded into the space of matrices over Lx
        A = matrix(Lx,n,m, [lift_polynomial(M[i,j], Lx, l) for i in 1:n, j in 1:m])
        return rank_monte_carlo(A, ϵ, s)
    end
end



















# SPACE FOR UNUSED CODE

function has_nonzero_determinant(M::MatrixElem{T}, ϵ::Float64) where {T <: PolyRingElem}
    return has_nonzero_determinant(M, ϵ, 2)
end

function has_nonzero_determinant(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: PolyRingElem}
    n = nrows(M)

    if n != ncols(M)
        error("Given matrix is not a square matrix!")
    end

    Kx = parent(M[1,1])
    K = base_ring(Kx)
    maxdeg = maximum(degree(M[i,j]) for i in 1:n, j in 1:n)
    det_deg = maxdeg*n
    S, flag = get_eval_set(K, s*det_deg)
    
    k = ceil(log(s, 1/ϵ))
    for _ = 1:k
        a = rand(S)
        M_eval = map_entries(p -> evaluate(p,a), M)
        if det(M_eval) != 0
            return true
        end
    end
    return false
end


#was only a function to test, if the error probability bound is correct for has_nonzero_determinant. Has no use at this moment

#=
function how_many_trues(M::MatrixElem{T}, ϵ::Float64) where {T <: PolyRingElem}
    counter = 1
    while has_nonzero_determinant(M, ϵ)
        counter += 1
        if (counter == 100000)
            break
        end
    end
    return counter
end
=#



# I tested v2 but it is slower that the original one, so it has no use at this moment

#=
function rank_monte_carlo_v2(M::MatrixElem{T}, ϵ::Float64, s::Int) where {T <: AbstractAlgebra.Generic.RationalFunctionFieldElem}
    Kx = parent(numerator(M[1,1]))
    K = base_ring(Kx)
    n = nrows(M)
    m = ncols(M)
    num_vars = number_of_variables(Kx)

    #The maximum degree of det(M') is calculated where M' is an arbitrary quadratic submatrix of M.
    min_ = min(n,m)
    maxdeg_nums = maximum(total_degree(numerator(M[i,j])) for i in 1:n, j in 1:m)
    maxdeg_denoms = maximum(total_degree(denominator(M[i,j])) for i in 1:n, j in 1:m)
    det_deg = maxdeg_nums + maxdeg_denoms*(min_-1)
    r = 0
    S, flag = get_eval_set(K, s*det_deg)
    k = ceil(log(s, 1/ϵ))
    maxrank = 0
    one_ = one(K)
    if flag
        #rank(M) is calculated by computing the rank of (det_deg+1)^number_of_variables(Kx) matrices, evaluated in elements of eval_set.

        #@infiltrate
        for _ = 1:k
            a = Vector{elem_type(K)}(undef, num_vars)
            for i = 1:num_vars
                a[i] = rand(S)
            end
            #@infiltrate
            M_eval = zero_matrix(K, n, m)
            for i = 1:n
                row_denoms = Vector{elem_type(K)}(undef, m)
                for j = 1:m
                    row_denoms[j] = evaluate(denominator(M[i,j]), a)
                end
                for j = 1:m
                    e = one_
                    for l = 1:m
                        if l == j
                            e *= evaluate(numerator(M[i,l]), a)
                        else
                            e *= row_denoms[l]
                        end
                    end
                    M_eval[i,j] = e
                end
            end
            maxrank = max(rank(M_eval), maxrank)
            if maxrank == min_
                return maxrank
            end
        end
        return maxrank
    else
        #function get_eval_set returns false if and only if K is a finite field and order(K) < det_deg*s holds. 
        #In this case a field extension L of K such that order(L) >= det_deg*s is constructed.
        #d is the smallest natural number such that order(K)^d >= det_deg*s.
        d = ceil(Int, log(order(K), ZZ(det_deg*s)))
        L, l = Oscar.Nemo._extension(K, d)
        Lx, _ = rational_function_field(L, symbols(Kx)) 

        #The given matrix M is embedded into the space of matrices over Lx
        A = matrix(Lx,n,m, [lift_polynomial(numerator(M[i,j]), Lx, l)/lift_polynomial(denominator(M[i,j]), Lx, l) for i in 1:n, j in 1:m])
        return rank_monte_carlo_v2(A, ϵ, s)
    end
end
=#