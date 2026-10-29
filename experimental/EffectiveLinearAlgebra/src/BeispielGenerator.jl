
# ---------- Hilfsfunktionen ----------

# zufälliges normiertes irreduzibles Polynom vom Grad deg, nicht in `avoid`
function random_irreducible(Kx::PolyRing, deg::Int, rng::Int, avoid::Vector{T}) where {T <: PolyRingElem}
    x = gen(Kx)
    tries = 0
    while tries < 1000
        tries += 1
        f = x^deg + rand(Kx, deg-1, -rng:rng)
        if is_irreducible(f) && !(f in avoid)
            return f
        end
    end
    error("could not find any irreducible polynomial, please check input parameters.")
end

# unimodulare m×m-Matrix (det = 1) als Produkt L*U
function random_unimodular(Kx::PolyRing, m::Int, rng::Int, maxdeg::Int)
    L = identity_matrix(Kx, m)
    U = identity_matrix(Kx, m)
    for i in 1:m, j in 1:m
        i > j && (L[i, j] = rand(Kx, -1:maxdeg, -rng:rng))
        i < j && (U[i, j] = rand(Kx, -1:maxdeg, -rng:rng))
    end
    return L * U
end

# ---------- Minor mit vorgegebener Determinante ----------

# pattern: Vector{Tuple{Int,Int}} mit (Grad, Potenz) je irreduziblem Faktor
function matrix_with_det_pattern(Kx::PolyRing, m::Int, pattern::Vector{Tuple{Int,Int}}, rng::Int, maxdeg::Int)
    primes = elem_type(Kx)[]
    for (d, _) in pattern
        push!(primes, random_irreducible(Kx, d, rng, primes))
    end
    diag = [one(Kx) for _ in 1:m]
    for (p, (_, e)) in zip(primes, pattern)
        diag[rand(1:m)] *= p^e
    end
    D = diagonal_matrix(diag)
    M = random_unimodular(Kx, m, rng, maxdeg) * D *
        random_unimodular(Kx, m, rng, maxdeg)
    return M, prod(p^e for (p, (_, e)) in zip(primes, pattern); init = one(Kx))
end

# ---------- n×m-Matrix mit vollem Spaltenrang ----------

function example_matrix(Kx::PolyRing, n::Int, m::Int, pattern::Vector{Tuple{Int,Int}}, rng::Int, maxdeg::Int)
    @assert n >= m >= 1
    M, f = matrix_with_det_pattern(Kx, m, pattern, rng, maxdeg)
    sigma = rand(symmetric_group(n))
    indices = sort!([sigma(i) for i in 1:m])            # Positionen der Minor-Zeilen
    A = zero_matrix(Kx, n, m)
    k = 0                                               # Anzahl bisher gesetzter Minor-Zeilen
    for i in 1:n
        if k < m && i == indices[k+1]
            k += 1
            for j in 1:m
                A[i, j] = M[k, j]
            end
        elseif k >= 1
            # abhängige Zeile: Polynomkombination der bisherigen Minor-Zeilen
            scalars = [rand(Kx, -1:0, -rng:rng) for _ in 1:k]
            for j in 1:m
                A[i, j] = sum(scalars[c] * M[c, j] for c in 1:k)
            end
        end                                             # sonst: Nullzeile
    end
    return A, f, indices
end

# ---------- dein Greedy-Verfahren zur Kontrolle ----------

function greedy_minor_rows(A)
    n, m = nrows(A), ncols(A)
    rows = Int[]
    for i in 1:n
        length(rows) == m && break
        r = A[i:i, :]
        iszero(r) && continue
        cand = vcat([A[j:j, :] for j in rows]..., r)
        rank(cand) == length(rows) + 1 && push!(rows, i)
    end
    return rows
end

function check_example(A, f, pattern)
    m = ncols(A)
    rows = greedy_minor_rows(A)
    length(rows) == m || return false
    rank(A) == m || return false
    d = det(A[rows, :])
    d == f || return false
    fac = factor(d)
    found = sort([(degree(p), e) for (p, e) in fac])
    return found == sort(collect(pattern))
end

# ---------- Generator für diverse Beispiele ----------

function generate_examples(N::Int; seed = 1, nrange = 20:30, mrange = 10:20,
                           max_factors = 4, max_deg = 8, max_pow = 4,
                           max_total_degree = 20, rng = 2)
    #rng = Random.MersenneTwister(seed)
    Qx, _ = polynomial_ring(QQ, :x)
    examples = NamedTuple[]
    seen = Set{Any}()
    attempts = 0
    while length(examples) < N && attempts < 100N
        attempts += 1
        m = rand(mrange)
        n = rand(max(m, first(nrange)):max(m, last(nrange)))
        k = rand(0:max_factors)
        pattern = [(rand(1:max_deg), rand(1:max_pow)) for _ in 1:k]
        sum(d * e for (d, e) in pattern; init = 0) > max_total_degree && continue
        sig = (n, m, sort(pattern))
        sig in seen && continue
        push!(seen, sig)

        A, f, sel = example_matrix(Qx, n, m, pattern, rng, max_deg)
        check_example(A, f, pattern) ||
            (@warn "Verifikation fehlgeschlagen" sig; continue)
        push!(examples, (A = A, n = n, m = m, det = f,
                         det_degree = degree(f),
                         n_factors = k,
                         factor_degrees = [d for (d, _) in sort(pattern)],
                         factor_powers = [e for (_, e) in sort(pattern)],
                         minor_rows = sel))
    end
    return examples
end

# Binärformat (little endian), ein Datensatz pro Beispiel, 52 Bytes:
#   7 × Int32  : n, m, coeff, maxdeg, d, e, r
#   3 × Float64: ratio (= t1/t2), t1, t2   (mittlere Zeiten in Sekunden)
const RECORD_FIELDS_INT   = (:n, :m, :coeff, :maxdeg, :d, :e, :r)
const RECORD_FIELDS_FLOAT = (:ratio, :t1, :t2)

# Mittlere Laufzeit von f(A): wiederholt ausführen, bis `budget` Sekunden vorbei sind
function mean_runtime(f, A, budget::Float64)
    times = Float64[]
    t_start = time_ns()
    while (time_ns() - t_start) / 1e9 < budget || isempty(times)
        t0 = time_ns()
        f(A)
        push!(times, (time_ns() - t0) / 1e9)
    end
    return sum(times) / length(times)
end

#Analyse der Laufzeit von zwei Funktionen im Vergleich
function method_analysis(n_range::Vector{Int}, m_range::Vector{Int},
                         coeff_range::Vector{Int}, maxdeg_range::Vector{Int},
                         d_range::Vector{Int}, e_range::Vector{Int},
                         r_range::Vector{Int};
                         budget::Float64 = 1.0, seed = nothing)

    filepath = expanduser("~/OSCAR_Testdateien/hnf_full_rank_meins_vs_OSCAR.bin")   # <-- manuell anpassen

    seed === nothing || Random.seed!(seed)
    Kx, _ = polynomial_ring(QQ, :x)
    
    A, _, _ = example_matrix(Kx, 2, 2, [(1,1)], 1, 1)
    hnf(A);                                      # Warm-up (Kompilierung), nicht gemessen
    hnf_lip_full_rank(A);     
    
    io = open(filepath, "a")                     # "w" zu "a" ändern, damit angehangen wird, d.h. bestehende Daten erhalten bleiben
    try
        for n in n_range, m in m_range
            n < m && continue                    # voller Spaltenrang braucht n >= m
            for coeff in coeff_range, maxdeg in maxdeg_range,
                r in r_range, d in d_range, e in e_range

                # Bei r == 0 spielen d und e keine Rolle -> nur einmal ausführen
                if r == 0 && (d != first(d_range) || e != first(e_range))
                    continue
                end

                pattern = Tuple{Int,Int}[(d, e) for _ in 1:r]
                local A
                try
                    A, _, _ = example_matrix(Kx, n, m, pattern, coeff, maxdeg)
                catch err
                    @warn "Beispielgenerierung fehlgeschlagen" n m coeff maxdeg d e r err
                    continue
                end

                local t1, t2
                try
                    t1 = mean_runtime(hnf, A, budget)
                    GC.gc(true)
                    t2 = mean_runtime(hnf_lip_full_rank, A, budget)
                    GC.gc(true)
                catch err
                    @warn "Methode abgebrochen" A n m coeff maxdeg d e r err
                    flush(io)                       # nichts verlieren bei Abbruch
                    close(io)
                    return filepath
                end
                # status, t1, t2 = run_case(n, m, coeff, maxdeg, d, e, r, budget)
                # if status != :ok
                #     println("method_analysis: n=$n m=$m coeff=$coeff maxdeg=$maxdeg d=$d e=$e r=$r status=$status t1=$t1")
                #     open("skipped.log", "a") do f
                #         println(f, "n=$n m=$m coeff=$coeff maxdeg=$maxdeg d=$d e=$e r=$r status=$status t1=$t1")
                #     end
                #     continue
                # end

                for v in (n, m, coeff, maxdeg, d, e, r)
                    write(io, Int32(v))
                end
                write(io, Float64(t1 / t2), Float64(t1), Float64(t2))
                flush(io)                        # nichts verlieren bei Abbruch
                println("n=$n m=$m coeff=$coeff maxdeg=$maxdeg d=$d e=$e r=$r  ratio=$(round(t1 / t2; sigdigits = 4))")
            end
        end
    finally
        close(io)
    end
    return filepath
end

const MEM_LIMIT_KB = 6 * 1024^2    # 6 GiB, deutlich unter dem OOM-Limit deiner Maschine
const HARD_TIMEOUT = 300.0         # Sekunden pro Fall (inkl. Start/Kompilierung)

function rss_kb(pid)
    try
        for l in eachline("/proc/$pid/status")
            startswith(l, "VmRSS:") && return parse(Int, split(l)[2])
        end
    catch
    end
    return 0
end

function run_case(n, m, coeff, maxdeg, d, e, r, budget)
    out = tempname()
    #cmd = `$(Base.julia_cmd()) --project=$project worker.jl
    #       $n $m $coeff $maxdeg $d $e $r $budget`
    project = normpath(joinpath(homedir(), "Oscar.jl"))
    worker = joinpath(@__DIR__, "worker.jl")
    cmd = `$(Base.julia_cmd()) --project=$project $worker $n $m $coeff $maxdeg $d $e $r $budget`
    proc = run(pipeline(cmd; stdout = out, stderr = stderr); wait = false)
    pid = getpid(proc)
    println("run-case n=$n m=$m coeff=$coeff maxdeg=$maxdeg d=$d e=$e r=$r")
    t0 = time()
    status = :ok
    while process_running(proc)
        if rss_kb(pid) > MEM_LIMIT_KB
            status = :oom;     kill(proc, Base.SIGKILL); break
        elseif time() - t0 > HARD_TIMEOUT
            status = :timeout; kill(proc, Base.SIGKILL); break
        end
        sleep(0.2)
    end
    wait(proc)
    #Main.@infiltrate
    t1 = t2 = NaN
    for l in eachline(out)
        startswith(l, "t1=") && (t1 = parse(Float64, l[4:end]))
        startswith(l, "t2=") && (t2 = parse(Float64, l[4:end]))
    end
    rm(out; force = true)
    if status == :ok && !(isfinite(t1) && isfinite(t2))
        status = :failed        # Worker ist mit Fehler beendet (z. B. Exception)
    end
    return status, t1, t2
end

# ---------- Visualisierung der Daten als Tabelle - HTML ----------

# Zum späteren Einlesen (Format siehe oben):
function read_analysis(filepath::String)
    nint, nfloat = length(RECORD_FIELDS_INT), length(RECORD_FIELDS_FLOAT)
    rows = NamedTuple[]
    open(filepath, "r") do io
        while !eof(io)
            ints   = [Int(read(io, Int32)) for _ in 1:nint]
            floats = [read(io, Float64) for _ in 1:nfloat]
            push!(rows, NamedTuple{(RECORD_FIELDS_INT..., RECORD_FIELDS_FLOAT...)}((ints..., floats...)))
        end
    end
    return rows
end

# benötigt read_analysis aus method_analysis
function visualize_analysis(filepath::String;
                            outfile::String = joinpath(tempdir(), "method_analysis.html"),
                            open_browser::Bool = true)
    rows = read_analysis(filepath)
    isempty(rows) && error("Keine Daten in $filepath")

    # Daten als JSON-Array von Arrays: [n,m,coeff,maxdeg,d,e,r,ratio,t1,t2]
    num(x) = isfinite(x) ? string(x) : "null"
    recs = [string("[", join((string(getfield(r, f)) for f in RECORD_FIELDS_INT), ","), ",",
                   join((num(getfield(r, f)) for f in RECORD_FIELDS_FLOAT), ","), "]")
            for r in rows]
    json = string("[", join(recs, ","), "]")

    write(outfile, replace(HTML_TEMPLATE, "__DATA__" => json))
    println("Interface geschrieben: ", outfile)

    if open_browser
        try
            # if Sys.iswindows()
            #     run(`cmd /c start "" $outfile`)
            # elseif Sys.isapple()
            #     run(`open $outfile`)
            # else
            #     run(`xdg-open $outfile`)
            # end
            if Sys.iswindows()
                run(`cmd /c start "" $outfile`)
            elseif Sys.isapple()
                run(`open $outfile`)
            elseif Sys.islinux() &&
                isfile("/proc/sys/kernel/osrelease") &&
                occursin("microsoft",
                            lowercase(read("/proc/sys/kernel/osrelease", String)))

                # WSL: Linux-Pfad in einen Windows-Pfad umwandeln
                winpath = strip(read(`wslpath -w $outfile`, String))
                # Windows-Standardbrowser öffnen
                run(`cmd.exe /c start "" $winpath`)
            else
                run(`xdg-open $outfile`)
            end
        catch
            @warn "Browser konnte nicht automatisch geöffnet werden, bitte Datei manuell öffnen." outfile
        end
    end
    return outfile
end

const HTML_TEMPLATE = raw"""
<!DOCTYPE html>
<html lang="de"><head><meta charset="utf-8">
<title>method_analysis</title>
<style>
 body{font-family:sans-serif;margin:20px}
 #ctrl{display:flex;flex-wrap:wrap;gap:14px;align-items:flex-end;margin-bottom:12px}
 #ctrl label{display:flex;flex-direction:column;font-size:12px;color:#444}
 #ctrl select,#ctrl button{font-size:14px;padding:3px 6px}
 fieldset{border:1px solid #bbb;border-radius:6px;display:flex;gap:14px;flex-wrap:wrap}
 table{border-collapse:collapse}
 th,td{border:1px solid #ccc;padding:5px 9px;text-align:right;font-variant-numeric:tabular-nums}
 th{background:#f0f0f0}
 td.empty{color:#aaa;text-align:center}
 #info{margin-top:10px;font-size:12px;color:#555}
</style></head><body>
<div id="ctrl"></div>
<div id="tab"></div>
<div id="info"></div>
<script>
const DATA = __DATA__;
const P = ["n","m","coeff","maxdeg","d","e","r"];
const METRICS = [[7,"Ratio t1/t2"],[8,"t1 [s] (method1)"],[9,"t2 [s] (method2)"]];
const vals = P.map((_,i)=>[...new Set(DATA.map(x=>x[i]))].sort((a,b)=>a-b));
const state = {row:0, col:1, metric:7, fixed:{}};
P.forEach((_,i)=>{ state.fixed[i] = vals[i][0]; });

function mk(label, options, current, cb){
  const l = document.createElement("label");
  l.append(label);
  const s = document.createElement("select");
  for (const [v,t] of options){
    const o = document.createElement("option");
    o.value = v; o.textContent = t;
    if (String(v) === String(current)) o.selected = true;
    s.append(o);
  }
  s.onchange = () => cb(s.value);
  l.append(s);
  return l;
}

function color(ratio){          // log-Skala, blau: method1 schneller, orange: method2 schneller
  const t = Math.max(-1, Math.min(1, Math.log2(ratio)/3));
  const hue = t > 0 ? 28 : 210;
  return "hsl(" + hue + ",85%," + (100 - 45*Math.abs(t)) + "%)";
}

function render(){
  const ctrl = document.getElementById("ctrl");
  ctrl.innerHTML = "";
  const pOpts = P.map((p,i)=>[i,p]);
  ctrl.append(mk("Zeilen", pOpts, state.row, v=>{
    v = +v; if (v === state.col) state.col = state.row; state.row = v; render(); }));
  ctrl.append(mk("Spalten", pOpts, state.col, v=>{
    v = +v; if (v === state.row) state.row = state.col; state.col = v; render(); }));
  const sw = document.createElement("button");
  sw.textContent = "Zeilen/Spalten tauschen";
  sw.onclick = () => { [state.row, state.col] = [state.col, state.row]; render(); };
  ctrl.append(sw);
  ctrl.append(mk("Tabelleneintrag", METRICS, state.metric, v=>{ state.metric = +v; render(); }));

  const fs = document.createElement("fieldset");
  const lg = document.createElement("legend"); lg.textContent = "Fixierte Parameter"; fs.append(lg);
  P.forEach((p,i)=>{
    if (i === state.row || i === state.col) return;
    fs.append(mk(p, vals[i].map(v=>[v,v]), state.fixed[i], v=>{ state.fixed[i] = +v; render(); }));
  });
  ctrl.append(fs);

  // Daten filtern und in Zellen gruppieren
  const cells = new Map();
  let used = 0;
  for (const x of DATA){
    let ok = true;
    for (let i = 0; i < P.length; i++){
      if (i !== state.row && i !== state.col && x[i] !== state.fixed[i]) { ok = false; break; }
    }
    const v = x[state.metric];
    if (!ok || v === null) continue;
    used++;
    const key = x[state.row] + "|" + x[state.col];
    if (!cells.has(key)) cells.set(key, []);
    cells.get(key).push(v);
  }
  const rv = vals[state.row], cv = vals[state.col];
  const agg = a => state.metric === 7
      ? Math.exp(a.reduce((s,v)=>s+Math.log(v),0)/a.length)   // geometrisches Mittel für Ratios
      : a.reduce((s,v)=>s+v,0)/a.length;
  const fmt = v => v >= 1000 || v < 0.001 ? v.toExponential(2) : v.toPrecision(3);

  let h = "<table><tr><th>" + P[state.row] + " \\ " + P[state.col] + "</th>";
  for (const c of cv) h += "<th>" + c + "</th>";
  h += "</tr>";
  for (const r of rv){
    h += "<tr><th>" + r + "</th>";
    for (const c of cv){
      const a = cells.get(r + "|" + c);
      if (!a) { h += "<td class='empty'>–</td>"; continue; }
      const v = agg(a);
      const style = state.metric === 7 ? " style='background:" + color(v) + "'" : "";
      h += "<td" + style + " title='" + a.length + " Messung(en)'>" + fmt(v) + "</td>";
    }
    h += "</tr>";
  }
  h += "</table>";
  document.getElementById("tab").innerHTML = h;
  document.getElementById("info").textContent =
    "Datensätze gesamt: " + DATA.length + ", in dieser Tabelle: " + used +
    (state.metric === 7 ? ". Ratio > 1 (orange): method2 schneller, Ratio < 1 (blau): method1 schneller." : ".");
}
render();
</script></body></html>
"""