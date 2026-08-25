# Route P wild-saddle minimal trace depth (2026-08-25)

Formalized new sharp bridge in `formal/GaloisForLFunctions/RHTower/RoutePWildSaddleMinimalTraceClassDepth.lean`, wired into `formal/GaloisForLFunctions/RHTower.lean`. Card: `docs/drafts/pipeline/3-formalized/route-p-wild-saddle-minimal-trace-class-depth.md`.

Mathematical result: for Lambert-W/RVM saddle `u + log u = L`, first truncation `u1=L-log L` has reciprocal defect eventually >= `1/(256 p_n)`, hence is not summable. The signed one-step source is Schatten-2 but its difference from signed RVM is not Schatten-1; actual reciprocal Xi minus one-step source is also not Schatten-1. Existing second truncation `u2=L-log u1` is Schatten-1 close to both RVM and actual reciprocal Xi. Thus depth two is necessary and sufficient for trace-class relocation.

Key lower bound: `u-u1=log(L/u) >= log u/L >= 1/(4L)`. Uniform `log u>=1/4` follows from `u>=4/3`, forced by `L>=2` and `log u<=u-1`. Ordered-prime PNT gives `NL<=8p_n`, yielding prime-harmonic divergence.

Verification: direct `lake env lean GaloisForLFunctions/RHTower/RoutePWildSaddleMinimalTraceClassDepth.lean` passed. Every new theorem axiom-audited; only `[propext, Classical.choice, Quot.sound]`. `git diff --check` passed. Temporary scratch, axiom file, and temporary dependency/new `.olean` files removed; no stale Lean process. No lake/umbrella build or global lint run. Frontier map untouched.

Primary-source novelty audit: Corless et al. Lambert W asymptotics, Franca-LeClair smooth RVM inversion, Bertola RH/Fredholm tau functions, Hartmann-Lesch regularized determinants. No matching fixed-log-truncation Schatten threshold found. Claim kept `[BRIDGE]`, not RH.

Next exact frontier: signed pairing should kill degree-one trace anomaly, but trace-class proximity alone does not identify det2 because multiplicative cross-trace/higher trace coordinates remain. Need source-side determination of trace-class correction or relative determinant anomaly, not more foundations.