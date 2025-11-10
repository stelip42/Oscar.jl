

function sieve_of_erosthates(n::Int)
    #list = collect(2:n)
    #list = Int[]
    primes = trues(n)
    upper_bound = isqrt(n)
    for i = 2:upper_bound
        if primes[i]
            #push!(list, i)    
            for j = i^2:i:n
                primes[j] = false
            end
        end
    end
    return findall(primes)
end
