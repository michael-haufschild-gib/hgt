# Phase-1 primitive audit (2026-09-05): primitives not based on |ζ| on the line, not random models

Directive: start at phase 1 with a primitive that is not a functional of `|ζ|` on the critical
line and not a random-model comparison. Each candidate below was examined against the corpus
(search first) and the literature; the verdict names the exact receiver step.

| primitive | pre-divisor object | why it is a receiver | corpus status |
|---|---|---|---|
| Speiser critical points | `−ζ' = ∑ (log n) n^{-s}` (nonnegative coefficients); zeros of `ζ'` | Speiser 1934 / Levinson–Montgomery 1974: `RH ⟺ ζ'` zero-free on `0<σ<1/2`; the mechanism is the FE sign law `2Re(ζ'/ζ)(1/2+it) = log π − Re ψ(1/4+it/2) < 0` plus the argument principle; the sign law is unconditional (now Lean, `SpeiserCriticalLineSignLaw`), the equivalence is a count identity `N⁻_{ζ'} = N⁻_ζ + O(log T)` | sign law present (`re_logDeriv_riemannZeta_criticalLine`); Speiser equivalence absent; not a producer |
| Redheffer matrix `R_n` (divisibility + counting column) | integer matrix, `det R_n = M(n)`; nontrivial eigenvalues are roots of `z^{K+1} = ∑_k C_k(n) z^{K−k}` (chain counts); `λ ∈ Spec∖{1} ⟺ ∑_{m≤n}[(ζ−1)/(λ−ζ)](m) = λ − 1` | `coker(R_n) ≅ ℤ/M(n)ℤ` (unipotent × rank-one), so the integral structure is exactly `M(n)`; the small eigenvalues encode partial sums of `(ζ−1)/(λ−ζ)`, i.e. `a`-points; RH ⟺ product of small eigenvalues `≪ n^{-1/2+ε}` (Littlewood) | absent; Redheffer 1977, Barrett–Forcade–Pollington 1988, Vaughan 1993/96 |
| Hurwitz–Lerch deformation `L(α,a,s)` | additive twist `e(nα)` and shift `n+a` | zeros leave the line for every `a ∉ {1/2,1}` (Davenport–Heilbronn, Cassels) and every irrational `α`; the RH locus is the multiplicative (Euler-product) locus; deformation measures the loss of multiplicativity, no rigidity across it | Lerch/Hurwitz present; standard twists present (Selberg-class modules) |
| Landau-lemma series | Dirichlet series with nonnegative coefficients and poles at zeros of `ζ` | any `∑ a_n n^{-s} = F/ζ` with `a ≥ 0` forces `F = Aζ`; every nonnegative candidate (`−ζ'/ζ`, character combinations) has its first real singularity at `s = 1`, so Landau yields only the trivial region | — |
| Farey / closed horocycle | rationals of height `≤ N`; horocycle at height `1/N²` | Franel–Landau and Zagier–Sarnak: rate `y^{3/4−ε}` ⟺ RH; only the Eisenstein constant term `ξ(2s−1)/ξ(2s)` contributes; cusp forms drop out | `FareySet`, Eisenstein residual `_iff_riemannHypothesis` present |
| Bagchi recurrence | vertical shifts `ζ(·+iτ)` on the strip | `RH ⟺ ζ` recurrent in the compact-open topology; `B²`-almost periodicity gives recurrence only on average over base points; upgrading needs sup control near zeros | `PrimeEulerProductAperture` (Bohr) present |
| Knauf Farey spin chain | ferromagnetic chain with `Z = ζ(s−1)/ζ(s)` | Lee–Yang constrains field zeros, RH is a temperature (Fisher) statement | prime–Ising already closed (F87/F88) |
| Large-order / resurgence at `s = 1` | Taylor coefficients of `1/ζ` or `ζ^z` at `s=1` (Möbius log-moments `∑ μ(n)(log n)^k/n`) | growth rate `|1−ρ|^{-k}` is Cauchy–Hadamard, dominated by the first zero; the full duality is Li's criterion (closed, `LiSignOscillation`) | Li closed |
| Hardy oscillator / Prüfer phase | `(θ'Z, Z')` with `|ζ'(1/2+it)|² = Z'² + θ'²Z²` | monotone winding ⟺ `Z'² − ZZ'' ≥ 0` ⟺ Laguerre inequality of `Ξ` (CANNOT-185) | Laguerre closed |
| lattice-point / divisor problems | `Δ(x) ≪ x^{1/4+ε}` (no zeros) | same square-root barrier with known spectrum; size problems (Lindelöf-type), not zero problems | — |

Conclusion of phase 1: no primitive outside the excluded classes survives as a producer; every
one is a functional whose RH content is an argument-principle or Jensen statement about a divisor.
Positive residue certified: the unconditional Speiser sign law and its corollary that critical
points of `ζ` on the critical line above height `20` are multiple zeros
(`RHTower/SpeiserCriticalLineSignLaw`). Recorded so that these nine primitives are not re-opened.
