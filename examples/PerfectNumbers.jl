@doc raw"""
    first_perfect_number() -> Int64

Return the smallest perfect number.
"""
function first_perfect_number()
    return 6
end

function second_perfect_number()
    return 28
end

@doc raw"""
    perfect_numbers(n::Int) -> Vector{Int}

Return the first n perfect numbers by calculating number by number their divisors.
"""
function perfect_numbers_naive(n::Int)
    start_time = time()
    v = zeros(Int, n)
    idx = 1
    #print(time())
    for i = 1:2^(62)
        #print(time())
        if is_perfect_number(i)
            v[idx] = i
            idx+= 1
            if idx > n 
                return v
            end
        end
        if (time() - start_time > 60)
            break
        end
    end
    println("Time is up (one minute), n was chosen too large!")
end


@doc raw"""
    perfect_numbers(n::Int) -> Vector{Int}

Return the first n even perfect numbers (for n < 42) by using the fact, that 2^(p-1)(2^p-1) yields all even perfect numbers.
"""
function perfect_numbers(n::Int)
    v = zeros(Int, n)
    idx = 1
    p = 2
    if n >= 42
        println("n must be smaller than 42!")
        return v
    end
    for i = 1:2^n
        if is_prime(2^p-1)
            v[idx] = 2^(p-1)*(2^p-1)
            idx+= 1
            if idx > n 
                return v
            end
        end
        
        println("i = $i")
        println("p = $p")
        p = next_prime(p)
    end
    println("Time is up, n was chosen too large!")
end

#is_perfect_number(n::Int8) -> Bool
#Returns true, if n is a perfect number

function is_perfect_number(n::Integer)
    d = divisors(n)
    return (2n == sum(d))
end