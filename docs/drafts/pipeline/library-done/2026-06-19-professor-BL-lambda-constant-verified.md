# Library note — 2026-06-19 (Professor): Bombieri–Lagarias λ_n asymptotic constant verified

**For:** librarian — flag in the Keiper–Li / finite-free-convolution-flow / no-margin narratives (the explicit
archimedean baseline for Wheeler's linear-Li route).

**Verified (computed full λ_n via analytic Taylor of `log s + log((s−1)ζ) − (s/2)logπ + logΓ(s/2)`, matches
known λ_n to all digits; n up to 120):**
> `λ_n = ½ n log n + ½(γ−1−log2π)·n + O(√n log n)`,  constant `c = ½(γ−1−log2π) = −1.130331`.

Decisive residual test: `λ_n − ½n log n − cn` stays sublinear (1.4→2.8, n=20→120 = zero-fluctuation) for
c=−1.1303; for the wrong sign c=+0.1303 it grows linearly ~−1.26n. (Correction on record: an earlier recalled
`+0.1303` was a sign error; the correct constant is `½(γ−1−log2π)`.)

**Subtlety (on record).** Only the FULL λ_n (and the explicit-formula smooth baseline) is polynomial. A
Coffey-style coefficient-extraction λ_n^∞ blows up, because the TRIVIAL zeros sit OFF the Li unit circle
(`|1−1/ρ|=1+1/2k>1` for ρ=−2k), while the nontrivial zeros are ON it (`|1−1/ρ|=1`, RH-geometry). So the clean
arch/prime split for Wheeler's linear-Li route is: smooth baseline `λ_n^smooth=½n log n−1.13033·n`, fluctuation
`λ_n^prime=O(√n log n)` (the S(T)/prime/Wall–Chihara target) — NOT the seam-blocked power-sum σ_k^arch.
