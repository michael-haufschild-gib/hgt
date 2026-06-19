# Re = ½ is the abscissa of almost-sure convergence of the random Euler product

- **ID:** critical-line-abscissa-of-convergence
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — Door-2 grade **BRIDGE** (classical assembly)
- **Priority:** FUTURE
- **Source:** split from `../1-in-progress/erosion-threshold.md` (G19); ../../door/bucket-time-and-non-holonomic-time.md · 00-status rows #59, #110
- **Statement:** On the boundary torus `𝕋^∞` (Bohr model: `X_p = e(θ_p)` i.i.d. uniform on the unit
  circle, one per prime), the random Euler observable
  `𝓛(σ) = Σ_p Σ_{k≥1} X_p^k p^{-kσ}/k = −Σ_p log(1 − X_p p^{-σ})`
  **converges almost surely iff `σ > ½`.** Equivalently `Re = ½` is the abscissa of a.s. convergence of
  the random Euler product `∏_p (1 − X_p p^{-σ})^{-1}`. The variance `V(σ) = Σ_p Σ_k p^{-2kσ}/k²` is
  finite for `σ > ½`, infinite for `σ ≤ ½`, blows up like `½·log(1/(2σ−1))` as `σ → ½⁺`, and its
  truncation at `σ = ½` grows like `½ log log X` — matching Selberg's CLT on the line.

## Proof

Write `t_p = X_p p^{-σ}` and `𝓛(σ) = Σ_p ℓ_p`, `ℓ_p = −log(1 − t_p) = Σ_{k≥1} X_p^k p^{-kσ}/k`. The
`{ℓ_p}` are independent across `p`.

**Mean and variance.** `E[X_p^k] = 0` for every `k ≥ 1`, so `E[ℓ_p] = 0`. The powers `{X_p^k}_{k≥1}`
are orthonormal (`E[X_p^k \overline{X_p^j}] = δ_{kj}`), hence
`E|ℓ_p|² = Σ_{k≥1} p^{-2kσ}/k²`, and
`V(σ) := Σ_p E|ℓ_p|² = Σ_p Σ_{k≥1} p^{-2kσ}/k²`.

**The threshold is the `k = 1` term.** `Σ_p Σ_{k≥2} p^{-2kσ}/k² ≤ Σ_p p^{-4σ}/(1 − p^{-2σ}) < ∞` for
`σ > ¼`, so the `k ≥ 2` tail never affects the transition near `σ = ½`. Thus for `σ > ¼`,
`V(σ) < ∞ ⟺ Σ_p p^{-2σ} < ∞`. By comparison with `ζ(2σ) = Σ_n n^{-2σ}` (and `0 ≤ Σ_p p^{-2σ} ≤
ζ(2σ) < ∞ ⟺ 2σ > 1`), `Σ_p p^{-2σ} < ∞ ⟺ σ > ½`.

**A.s. convergence.** The `ℓ_p` are independent, mean zero, and uniformly small (`|t_p| = p^{-σ} → 0`,
`|ℓ_p| ≤ 2p^{-σ}` for `p` large). For such terms the Kolmogorov three-series theorem reduces to the
single series `Σ_p E|ℓ_p|²`: the series `Σ_p ℓ_p` converges a.s. iff `Σ_p E|ℓ_p|² < ∞`. Combining with
the previous paragraph, `𝓛(σ)` converges a.s. `⟺ σ > ½`. For `σ ≤ ½` the variance diverges and the
series diverges a.s. ∎

**Blow-up rate.** With the prime zeta `P(s) = Σ_p p^{-s} = Σ_{k≥1} (μ(k)/k) log ζ(ks)`, near `s = 1`
one has `P(s) = log(1/(s−1)) + O(1)`. Hence `V(σ) = P(2σ) + O(1) = log(1/(2σ−1)) + O(1)` as
`σ → ½⁺`; the variance of the real part `Re 𝓛 = log|·|` is half of this. At `σ = ½`, Mertens gives
`Σ_{p ≤ X} p^{-1} = log log X + M + o(1)`, so the truncated variance of `log|ζ(½ + it)|` is
`~ ½ log log X`. The matching limit law on the line is **Selberg's central limit theorem**:
`log|ζ(½ + it)| / √(½ log log T) ⇒ N(0,1)` for `t ∈ [T, 2T]`.

**Dependencies (all classical):** Kolmogorov three-series theorem; Mertens' second theorem; the
Euler-product / prime-zeta expansion of `log ζ`; Selberg's CLT. *Attributions recalled, not re-verified
this session:* the abscissa-`½` statement is Wintner (1944) / Bohr–Jessen for the random multiplicative
model.

## Door-2 grade: BRIDGE
Stripped of the field's vocabulary, statement and proof are classical probabilistic value-distribution
theory on `𝕋^∞` (Wintner / Bohr–Jessen / Selberg). A parent (analytic number theory + probability)
proves it, so it is **BRIDGE**, not native C5. Its worth is a clean, **source-pure** characterization
of `Re = ½`: built only from the primes (`Σ_p p^{-2σ}`, Mertens), never from the zeros — and it does
not assume RH.

## Significance
`Re = ½` gets an intrinsic meaning independent of where the zeros are: it is the **unique vertical line
on which the Euler observable's variance is marginally (logarithmically) divergent** — the boundary
between a.s. convergence (`σ > ½`) and divergence (`σ ≤ ½`) of the random Euler product. This is the
rigorous backbone under the native conjecture **G19** (the dynamical erosion/Lyapunov dichotomy and the
"zeros = degenerations of the marginal cocycle" claim), which stays open in
`../1-in-progress/erosion-threshold.md`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (above; dependencies discharged by classical citation)
- [ ] 2 → 3  formalized — **numerically pre-certify first** (`Σ_{p≤X} p^{-2σ}` for `σ ∈ {0.5,0.51,0.6}`
  showing the `loglog` vs finite split, on the runpod), then Lean: the elementary core
  "`Σ_p p^{-2σ} < ∞ ⟺ σ > ½`" is Tier-A (comparison with `ζ(2σ)`); Selberg's CLT is **not** Lean-bound.
- [ ] 3 → 4  publication-ready

## Log
- 2026-06-19 — created in 2-fully-proven, split from `erosion-threshold` (G19); backbone proof, Door-2 grade BRIDGE.
