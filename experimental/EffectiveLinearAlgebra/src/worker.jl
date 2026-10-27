n, m, coeff, maxdeg, d, e, r = parse.(Int, ARGS[1:7])
budget = parse(Float64, ARGS[8])


Kx, _ = polynomial_ring(QQ, :x)
pattern = Tuple{Int,Int}[(d, e) for _ in 1:r]
A, _, _ = example_matrix(Kx, n, m, pattern, coeff, maxdeg)

t1 = mean_runtime(hnf, A; budget)
println("t1=", t1); flush(stdout)     # Teilergebnis sofort sichern
GC.gc(true)
t2 = mean_runtime(hnf_lip_full_rank, A; budget)
println("t2=", t2); flush(stdout)