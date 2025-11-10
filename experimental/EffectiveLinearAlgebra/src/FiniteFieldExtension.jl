
@doc raw"""
    GF_prime_power(p::Int, n::Int) -> FqField

Returns the finite field of characteristic p and degree p^n.
"""
function GF_p_power(p::Int, n::Int)
    F = GF(p)
    Fx, x = polynomial_ring(F, :x)
    f = irred_polynomial_of_deg_p_to_the_power_of_n(p,n,Fx)
    return residue_field(Fx, f)
end

@doc raw"""
    irred_polynomial_of_deg_p_to_the_power_of_n(p::Int, n::Int, Fx::FqPolyRing) -> FqPolyRingElem

Returns an irreducible polynomial of the given FqPolyRing Fx of degree p^n.
"""
function irred_polynomial_of_deg_p_to_the_power_of_n(p::Int, n::Int, Fx::FqPolyRing)
    x = gen(Fx)
    ϕ = x^p-x+1
    if(n <= 1)
        return ϕ
    end
    d_prev = irred_polynomial_of_deg_p_to_the_power_of_n(p, n-1, Fx)
    pow_ϕ = one(Fx)
    dn = one(Fx)
    for i = 1:p^(n-1) 
        pow_ϕ *= ϕ
        dn += coeff(d_prev, p^(n-1)-i)*pow_ϕ
        #println(dn)
    end
    return dn
end

function field_extension(Fq::FqField, n::Int, t::Symbol)
    if (characteristic(Fq) == order(Fq))
        return GF(characteristic(Fq), n)
    else
        #K = GF(characteristic(Fq), n)
        Fqx, x = polynomial_ring(Fq, :x)
        #f = lift_polynomial(defining_polynomial(K), Fqx)
        #for i = 1:order(Fq)
        #    if (is_irreducible(f))
        #        return finite_field(f, t)
        #    end
        #    println(f)

        #    f += next_element(coeff(f,0)) - coeff(f,0)
        #end
        a = one(Fq)
        for i = 1:order(Fq)-1
            b = one(Fq)
            for j = 1:order(Fq)-1
                f = x^n + a*x + b
                if (is_irreducible(f))
                    return finite_field(f, t)
                end
                println(f)
                b = next_element(b)
            end
            a = next_element(a)
        end        
        error("Field extension not possible")
    end
end

function lift_polynomial_(f::FqPolyRingElem, Fx::FqPolyRing)
    deg = degree(f)
    g = zero(Fx)
    x = gen(Fx)
    for i = 0:deg
        g += Fx(lift(ZZ, coeff(f, i)))*x^i
    end
    return g
end