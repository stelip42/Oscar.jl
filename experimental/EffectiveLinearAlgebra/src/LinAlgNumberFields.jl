


@doc raw"""
    rank_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}) -> Int

Returns the rank of $A$. 
"""
function rank_nf(A::MatrixElem{T}) where T <: NumFieldElem
    
    #reduce the problem to compute the rank r of the representation matrix of A over QQ. Then r divided by degree(Qa) equals to rank(A) 
    A_rational = matrix(QQ, representation_matrix(A))
    d = degree(parent(A[1,1]))
    return divexact(rank(A_rational),d)
end


@doc raw"""
    representation_matrix(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}) -> QQMatrix

Returns a matrix with rational entries representing multiplication with $A$ with respect to the power basis of the generator of the parent of $a$. 
The output matrix is of type QQMatrix.
"""
function representation_matrix(A::MatrixElem{T}) where T <: NumFieldElem
    Qa = parent(A[1,1])
    n = nrows(A)
    m = ncols(A)
    d = degree(Qa)
    A_new = zero_matrix(QQ, d*n, d*m)

    #compute for each entry A[i,j] its representation matrix and save all entries in A_new
    for i = 0:(n-1)
        for j = 0:(m-1)
            M = representation_matrix(A[i+1,j+1])
            for k = 1:d
                for l = 1:d
                    A_new[i*d+k, j*d+l] = M[k,l]
                end
            end
        end
    end
    return A_new
end
















#maybe useful function: absolute_representation_matrix - is only for finite fields!

#SPACE FOR UNUSED CODE


@doc raw"""
    random_nf_matrix(Qa::AbsSimpleNumField, n::Int, m::Int, range::Int) -> AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}

Returns a random $n$x$m$ matrix over $Qa$ as a sum of random matrices M_i over a_i*QQ, where a_i is the i-th basis element of $Qa$. 
All nominators and denominators of rational coefficients are in [-$range$:$range$]
"""
function random_nf_matrix(Qa::AbsSimpleNumField, n::Int, m::Int, range::Int)
    a = gen(Qa,1)
    d = degree(Qa)
    S = matrix_space(QQ, n, m)
    M = zero(Qa)
    for i = 1:d
        r = rand(S, -range:range)
        M += r*a^i
    end
    return M
end

@doc raw"""
    nf_matrix(Qa::AbsSimpleNumField, A::QQMatrix) -> AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}

If $A$ is a representation matrix of some matrix $M$ over $Qa$, then this method returns $M$.
"""
function nf_matrix(Qa::AbsSimpleNumField, A::QQMatrix)
    B = basis(Qa)
    d = degree(Qa)
    n = Int(number_of_rows(A)/d)
    m = Int(number_of_columns(A)/d)
    A_new = zero_matrix(Qa,n,m)

    #read out the first row of each (d x d)-block of A to reconstruct the respective entry in Qa 
    for i = 1:n
        for j = 1:m
            for k = 1:d  
               A_new[i,j] += B[k]* A[1+d*(i-1), k+d*(j-1)]
            end
        end
    end
    return A_new
end

@doc raw"""
    solve_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}, 
    b::Union{Vector{AbsSimpleNumFieldElem}, AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}}) -> 

Solves the linear system xA = b and returns x
""" 
function solve_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}, 
        b::Union{Vector{AbsSimpleNumFieldElem}, AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}})
    
    #reduce the problem to solving a linear system over QQ, solve it and translate the solution back with nf_matrix
    Qa = parent(A[1,1])
    A_rational = matrix(QQ, representation_matrix(A))
    b_rational = matrix(QQ, representation_matrix(b))
    X = solve(A_rational, b_rational)
    return nf_matrix(Qa, X)
end

@doc raw"""
    kernel_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}) -> AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}

Returns a matrix $K$ whose rows generate the left kernel of $A$, that is, $KA$ is the zero matrix.
""" 
function kernel_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem})
    
    #reduce the problem to compute the kernal of the representation matrix of A over QQ and translate the result back with nf_matrix
    Qa = parent(A[1,1])
    A_rational = matrix(QQ, representation_matrix(A))
    K = kernel(A_rational)

    #B = basis(Qa)
    #d = degree(Qa)
    #n = Int(nrows(X)/d)
    #m = Int(ncols(X)/d)

    return nf_matrix(Qa,K)
    #K = zero_matrix(Qa, n, m)
    #for i = 0:n-1 
    #    for j = 0:m-1
    #        for k = 1:d
    #            K[i+1,j+1] += B[k]*X[i*d+1,j*d+k]
    #        end
    #    end
    #end
    #return K
end



@doc raw"""
    det_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}) -> AbsSimpleNumFieldElem

Returns the determinant of $A$. 
"""
function det_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem})
    
    #construct a matrix M with entries of type QQPolyRingElem, compute det(M) and evulate det(M) at gen(parent([1,1])).
    #start = time_ns()
    A_x = preimage_eval(A)
    #t1 = time_ns()
    #println("Abschnitt 1: ", (t1 - start) / 1e6, " ms")
    d = det(A_x)
    #t2 = time_ns()
    #println("Abschnitt 2: ", (t2 - start) / 1e6, " ms")
    return evaluate(d, gen(parent(A[1,1]),1))
end

@doc raw"""
    inv_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}) -> AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem}
    
Returns the inverse of A. 
"""
function inv_nf(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem})

    #reduce the problem to compute the inverse of the representation matrix of A over QQ and translate the result back with nf_matrix
    A_rational = matrix(QQ, representation_matrix(A))
    A_rational_inv = matrix(QQ, inv(A_rational))
    return nf_matrix(parent(A[1,1]), A_rational_inv)
end

#Returns a matrix M with entries of type QQPolyRingElem such that evaluate(M[i,j], gen(parent(a))) equals A[i,j]
function preimage_eval(a::AbsSimpleNumFieldElem)
    d = degree(a)
    Qx, x = polynomial_ring(QQ)
    f = zero(Qx)
    for i = 0:d
        f += coeff(a, i)*x^i
    end
    return f
end

#Returns an univariate polynomial t over QQ such that evaluate(t, gen(parent(a))) equals a
function preimage_eval(A::AbstractAlgebra.Generic.MatSpaceElem{AbsSimpleNumFieldElem})
    
    n = nrows(A)
    m = ncols(A)
    Qx, x = polynomial_ring(QQ)
    A_new = matrix(Qx, zeros(Qx,n,m))
    for i = 1:n
        for j = 1:m
            A_new[i,j] = preimage_eval(A[i,j])
        end
    end
    return A_new
end