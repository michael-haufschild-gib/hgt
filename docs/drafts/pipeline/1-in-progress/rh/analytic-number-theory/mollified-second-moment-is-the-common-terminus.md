# The sharp mollified second moment is the common terminus of three RH programmes

- **ID:** mollified-second-moment-common-terminus
- **Stage:** 1-in-progress
- **Type:** ROUTE AUDIT
- **Statement:** Three independent programmes in the tree — the completed-logarithmic-derivative
  criterion, the grid density device, and Levinson's proportion method — all terminate at a sharp
  asymptotic for `∫_{T}^{2T} ‖(ζ + λζ′)·Ψ(σ₀+it)‖² dt`.  Nothing else in any of the three is open.

## The three termini

### 1. Criterion positivity (`xi-hadamard-pair-sign-law`)

`riemannHypothesis_iff_re_logDeriv_xi_nonneg` reduces RH to `0 ≤ Re (ξ'/ξ)(s)` on `Re s > 1/2`, and
`re_logDeriv_xi_nonneg_of_disk_bound` reduces that to the disk condition
`(Re ρ − ½)² < (Re s − ½)² + (Im s − Im ρ)²` for every zero.  The unconditional part is a low-height
box and any zero-free region; the open part is unbounded height.  Five mechanisms were tried and
each closed with a proved obstruction (see that card).

### 2. Grid density (`selberg-superlinear-xi-density-programme`, Route 1)

`no_modulus_only_cell_bound` (this session) shows **no** estimate of the cell cancellation that
factors through `|Z·W|` can give a positive surplus — subsuming Cauchy–Schwarz, Hölder at every
exponent, the affine mean value theorem, and any sharpening of Graham's constants.  What is needed
is an estimate using where `Z·W` changes sign, i.e. Selberg's mollified machinery.

### 3. Levinson proportion (`levinson-critical-proportion-programme`)

`RHTower.exists_le_xiOddFiberCount_of_mollified_meanSquare` is unconditional and takes the mean
square only as the scalar hypothesis

```text
∫_{T₁}^{T₂} ‖levinsonMollifiedDetector λ b (σ₀+it)‖² ≤ Msq ,
```

returning `n ≤ xiOddFiberCount T₂` whenever

```text
(n+2)π + π + (T₂−T₁)(6/T₁²) + cw(log T₁ + log T₂)
  + [ (T₂−T₁)/2 · log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb) ] / (1/2 − σ₀)
    ≤ θ(T₂) − θ(T₁) .
```

Read off the Lean statement: `Msq` enters **only** through `log(Msq/(T₂−T₁))` divided by
`(1/2 − σ₀)`.  So a crude bound `Msq ≪ T` is not enough — the loss term is
`(T/2)·log(Msq/T)/(1/2−σ₀)`, which is of the same order `T log T` as the gain `θ(2T)−θ(T)` once
`σ₀` is pushed towards `1/2` (as it must be, since at fixed `σ₀ < 1/2` the functional equation makes
`∫|ζ(σ₀+it)|² ≍ T^{2−2σ₀}` and no short mollifier can remove that growth).  **The constant in the
asymptotic is what decides the proportion.**

## The common target

```text
∫_{T}^{2T} ‖(ζ + λζ′)·Ψ(σ₀+it)‖² dt   with   σ₀ = 1/2 − R/log T ,  Ψ of length X = T^θ, θ < 1/2 ,
```

to leading order with its constant — the Conrey / Balasubramanian–Conrey–Heath-Brown computation.
The tree owns every surrounding piece: Montgomery–Vaughan in affine form
(`Sieve/DirichletPolyAffineMeanSquare.lean`, and the infinite version), Graham's mean square
(`Sieve/GrahamMeanSquare.lean`), the harmonic-weighted variant (`HarmonicWeightedGrahamMeanSquare`),
the smooth AFE with truncation at every exponent (`SmoothAFEDirectTruncationRpow`, this session),
Barban–Vehov weights, and Levinson's entire consumer half.

## Why this is the corpus's highest-value single target

It is the *only* open input of three otherwise-complete programmes, it is a named classical theorem
rather than an open problem, and every ingredient around it is already Lean-certified.  No other
open item in the audited routes has that property.

## Caveat on the Levinson reading

The structural statement — that `Msq` enters only as `log(Msq/(T₂−T₁))/(1/2−σ₀)` — is read directly
from the Lean statement and is solid.  The consequence that a crude `≪ T` bound is insufficient is
an order-of-magnitude argument, not a Lean result; it should be checked against the tree's own
`levinsonMollifiedDetector` normalisation before being relied on.

## Log
- 2026-09-24 — created; consolidates the termini of three programmes after tracing each to its
  open input.

## The precise missing brick: the signed off-diagonal (2026-09-24)

Inspecting the tree's mean-value chain shows exactly where sharpness is lost.

**What is owned.**

* `Sieve/DirichletMVT.lean`, `dirichlet_meanValue_theorem` — two-sided, but with the crude error
  `4N(1+log N)·∑‖a_m‖²`.
* `Sieve/DirichletPolyAffineMeanSquare.lean`, `integral_Icc_normSq_dirPoly_le_affine` — the affine
  error `∑(m+1)‖a_m‖²`, but **upper bound only**, and with the main-term constant `5π/2` rather
  than `2`, so it cannot support an asymptotic.
* `Sieve/DirichletIntegralMeanValue.lean`, `norm_integral_normSq_dirPoly_sub_diag_le` — the exact
  reduction of the error to the off-diagonal.
* `Sieve/OffDiagonalBound.lean`, `offDiagonal_le`.

**Where sharpness is lost.**  `norm_integral_normSq_dirPoly_sub_diag_le` reduces the error to

```text
∑_{m ≠ n} ‖a_m‖ ‖a_n‖ · 2/|log m − log n| ,
```

i.e. it passes to **absolute values** before estimating.  That is fatal for the affine form: with
nonnegative coefficients there is no cancellation, and the displayed double sum really is of order
`N log N · ∑‖a_m‖²` (take `a_m ≡ 1`: the terms with `|m−n| = d` contribute `≍ n/d`, summing to
`≍ N² log N` against `∑‖a‖² = N`).  So `offDiagonal_le` is **sharp for what it estimates**, and no
work on it can produce the affine bound.

**The missing brick.**  Montgomery–Vaughan's theorem needs the *signed* bilinear form

```text
∑_{m ≠ n} a_m conj(a_n) · 2 sin(T log(m/n)) / log(m/n)
```

estimated by Hilbert's inequality with the spacings `δ_n = min_{m≠n}|log m − log n| ≍ 1/n`, giving
`≤ C ∑_n n ‖a_n‖²` — the affine error with the **correct** main constant `2T`.  The tree has a
Hilbert inequality (`Sieve/HilbertBilinear.lean`, `hilbert_bilinear_bound`) but in a discrete
root-of-unity form, not yet in the shape needed for the logarithmic spacings.

So the next brick is: a variant of `norm_integral_normSq_dirPoly_sub_diag_le` that **keeps the
signs**, plus the Hilbert inequality at logarithmic spacings.  Everything after that — the sharp
mollified second moment, and hence Levinson's proportion — is assembly against pieces already owned.

## Brick 1 of the missing step: logarithmic spacing (2026-09-24)

`formal/GaloisForLFunctions/HTGeometry/LogarithmicSpacing.lean`

- `sub_div_le_log_sub_log`, `log_sub_log_le_sub_div` — the two-sided linear comparison
  `(m−n)/m ≤ log m − log n ≤ (m−n)/n` for positive reals, both from
  `Real.log_le_sub_one_of_pos`.
- `abs_sub_div_max_le_abs_log_sub_log` — `|m−n|/max(m,n) ≤ |log m − log n|`.
- `inv_max_le_abs_log_sub_log_nat` — for distinct positive integers, `1/max(m,n) ≤ |log m − log n|`:
  the `δ_n ≍ 1/n` input of Montgomery–Vaughan.
- `inv_le_abs_log_sub_log_nat_of_le` — the uniform form `1/N` below `N`.

Axiom-clean.  This is the elementary input shared by both routes to the affine error — the
Hilbert-inequality route and the Fejér-minorant route below.

## Two routes to the affine error, and what each costs

**Route H (Hilbert).**  Keep the signed off-diagonal and apply Montgomery–Vaughan's inequality
`|∑_{r≠s} a_r conj(a_s)/(λ_r−λ_s)| ≤ π ∑_r |a_r|²/δ_r` at `λ_n = log n`, `δ_n ≥ 1/n` (brick 1).
This gives the affine error **with the correct main constant `2T`**, hence supports an asymptotic.
Cost: Montgomery–Vaughan's inequality itself, which the tree does not have at logarithmic spacings
(`Sieve/HilbertBilinear.lean` is a discrete root-of-unity form).

**Route F (Fejér minorant).**  Use `K(t) = (1−|t|/T)_+ ≤ 1_{[−T,T]}` with `K̂ ≥ 0` (Fejér), giving
`∫_{−T}^{T}|D|² ≥ ∑_{m,n} a_m conj(a_n) K̂(log(m/n))`, then `K̂(ξ) ≤ 4/(Tξ²)` together with brick 1
bounds the off-diagonal by `C ∑_n n‖a_n‖²` once `N ≲ T`.  Cost: elementary, no Hilbert inequality.
**But** `∫K = T`, not `2T`, so the main constant is off by a factor two and the result is a
two-sided affine bound, not an asymptotic.  Recovering `2T` is the Beurling–Selberg extremal
problem.

So Route F is reachable and would give the tree its first affine *lower* bound; Route H is what the
terminus actually needs.  Brick 1 serves both.

## Correction: the mean value theorem is not the missing piece (2026-09-24)

The preceding two sections argued that the affine mean value theorem is what stands between the
tree and the sharp mollified moment.  Re-doing the error budget shows that is **wrong**.

The tree's crude two-sided theorem (`Sieve/DirichletMVT.lean`, `dirichlet_meanValue_theorem`) gives

```text
| ∫_0^T ‖dirPoly N a‖² − T ∑‖a_m‖² |  ≤  4 N (1 + log N) ∑‖a_m‖² .
```

With `N ≍ T^{1/2+θ}` this error is `≍ T^{1/2+θ} log T · ∑‖a_m‖²`, and `T^{1/2+θ} log T ≪ T` for every
`θ < 1/2` — the programme's own threshold.  **So the crude form is already sufficient**, the affine
form is a convenience rather than a requirement, and Montgomery–Vaughan's inequality is not needed
at all.  (`SmoothAFEDirectTruncationRpow` and `LogarithmicSpacing` remain correct and reusable, but
they are not on the critical path.)

What the sharp moment actually needs is the **main term**, `T · ∑_m ‖a_m‖²`, evaluated
asymptotically.  For the mollified AFE coefficients that sum is the Barban–Vehov coefficient mean
square, and Graham's theorem is exactly its asymptotic:

```text
∑_{k ≤ N} ( ∑_{m ∣ k, m ≤ X} μ(m) log(X/m) )²  =  N log X + O(N)          (Graham 1978).
```

Bricks 46–47 prove the **upper half only**, and with the constant `4A²` (`A = 6 + |γ|`) rather than
`1`:

```text
sum_sq_barbanVehovCoeff_le :  ∑_{k ≤ N} b_X(k)²  ≤  4A² N (1 + log X) + X² log²X .
```

### The actual missing brick

**Graham's lower bound, with the sharp constant**: `∑_{k ≤ N} b_X(k)² ≥ N log X − O(N)`.  It runs
through the same Selberg diagonalisation as the upper half (bricks 21–23), but needs a lower bound
on the totient-weighted diagonal `∑_{e ≤ X} φ(e)·(inner_e)²` in place of brick 46's upper bound,
and the sharp evaluation of `inner_e = (μ(e)/e)·T_e(X/e)` rather than the majorant `|T_e| ≤ A·e/φ(e)`
of bricks 42–43.

This is strictly inside the sieve computation the tree already owns half of, and is far more
tractable than Montgomery–Vaughan.  It is the single brick that converts the tree's `≪` statements
into the asymptotic all three programmes need.

**Verified vs inferred.**  The statements quoted are read directly from the Lean source.  The
budget comparison `T^{1/2+θ} log T ≪ T` is elementary.  The claim that Graham's asymptotic is
exactly the main term needed is inferred from the structure of the chain (AFE → Dirichlet
polynomial → mean value theorem → coefficient sum) and should be confirmed against
`Sieve/MollifierShortRange.lean` and bricks 16–19 before a build is started on it.

## The flagged inference was wrong (2026-09-24)

The previous section inferred that Graham's asymptotic supplies the main term of the mollified
mean square, and flagged it for checking against `Sieve/MollifierShortRange.lean`.  The check
**refutes** it.

`sum_moebius_filter_mul_const_eq_zero` says the mollified coefficient **vanishes** for `1 < k ≤ X`,
and `sum_moebius_filter_one` says only `m = 1` survives at `k = 1`.  Hence

```text
∑_k ‖c_k‖²  =  ‖c_1‖²  +  ∑_{k > X} ‖c_k‖²  =  1  +  (tail) ,
```

so Graham's estimate bounds the **tail**, and the main term of the coefficient sum is simply `1`.
Graham is not the main term.

Where the main term really comes from: at `σ₀ < 1/2` the direct edge is not the whole of `ζ`.
Brick 12 splits critical-line zeta into two edges, and the dual edge carries the factor `χ(σ₀+it)`
with `|χ| ≍ t^{1/2−σ₀}`.  So

```text
Msq  ≍  T^{1 + 2(1/2 − σ₀)} ,      log(Msq/(T₂−T₁))  ≈  2(1/2 − σ₀) log T ,
```

and the Levinson loss term `(T/2)·log(Msq/T)/(1/2 − σ₀)` is `≈ T log T` — **exactly the order of the
gain** `θ(2T) − θ(T)`.  That is Levinson's balance, and it is why the recorded margin is `0.009`:
the proportion is decided by the *constant* in front of `T log T`, after the `(ζ + λζ′)` combination
is chosen to cancel the leading dual-edge contribution.

So the terminus is the genuine Conrey computation — the leading constant of

```text
∫_T^{2T} ‖(ζ + λζ′)·Ψ(σ₀+it)‖² dt
```

including the dual edge and the cross terms — not any single sieve estimate.  Graham (tail), the
mean value theorem (error), the AFE and the truncation are all supporting parts that the tree
already owns; what is missing is the two-edge main-term evaluation with its constant.

**Record of corrections in this card.**  Three successive diagnoses were wrong and are superseded:
"needs the affine mean value theorem" (the crude form suffices), "needs Montgomery–Vaughan" (not
needed at all), "Graham supplies the main term" (Graham bounds the tail).  The surviving statement
is the one above.

## Asset inventory for the two-edge main term (2026-09-24)

Searched before building; every supporting fact for the dual edge is already owned, so the gap is
the *evaluation*, not any ingredient.

| fact | module |
|---|---|
| `‖χ(s)‖ = π^{σ−1/2}‖Γ((1−s)/2)‖/‖Γ(s/2)‖` | `RouteBOfflineDomination`, `norm_zetaChi_eq` |
| `‖χ‖ = 1` on the critical line | `ZetaChiCriticalModulus`, `norm_zetaChi_critical`; also `HardyCarrier`, `norm_zetaChi_line` |
| `‖χ(σ+it)‖ ≤ C‖t‖^{1/2−σ}` left of `Re s = 1/2` | `ZetaChiLineSharp`, `exists_norm_zetaChi_line_le` |
| matching lower bound, displaced right | `SmoothAFEZetaRightReflectedPrimalMass`, `exists_norm_zetaChi_rightDisplaced_ge_rpow` |
| two-sided vertical Gamma ratio | `GammaVerticalRatioUniform`, `exists_twoSided_gamma_vertical_ratio` |
| Stirling for digamma, `ψ(z) = log z − 1/(2z) + O(‖z‖⁻²)` | `HTGeometry/GammaDigammaStirlingBound`, `norm_digammaStirlingDefect_le` |
| two-edge split of critical-line zeta | brick 12 of the Selberg card |
| smooth AFE, truncation at every exponent | `SmoothAFEDirectTruncationRpow` |
| mean value theorem (crude, two-sided — sufficient) | `Sieve/DirichletMVT`, `dirichlet_meanValue_theorem` |
| coefficient tail bound | `Sieve/GrahamMeanSquare`, `sum_sq_barbanVehovCoeff_le` |
| short range vanishes, `c_1 = 1` | `Sieve/MollifierShortRange` |

So nothing in the supporting layer is missing.  What is missing is a single object: the leading
constant of `∫_T^{2T}‖(ζ + λζ′)·Ψ(σ₀+it)‖² dt`, assembled from the direct edge, the dual edge and
the cross term, with `λ` chosen to cancel the leading dual-edge contribution.  That is Conrey's
computation and it is genuinely new mathematics to formalise, not an assembly of owned pieces.

## Brick: the logarithmic derivative of the chi factor (2026-09-24)

`formal/GaloisForLFunctions/RHTower/ZetaChiLogDeriv.lean`

- `logDeriv_zetaChi` — since `χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s)`, the reflection in the numerator contributes
  with a minus sign and the two archimedean logarithmic derivatives **add**:
  ```
  (χ'/χ)(s)  =  − (Γ_ℝ'/Γ_ℝ)(1−s)  −  (Γ_ℝ'/Γ_ℝ)(s) .
  ```

Axiom-clean.  This is the algebraic core of Levinson's cancellation, and it is exact — no Stirling
is used.  Stirling enters only afterwards: on a vertical line both arguments have modulus `≍ |t|/2`,
so `norm_digammaStirlingDefect_le` turns the right-hand side into `−log(|t|/2π) + O(1/|t|)`.

Why this is the right next brick.  The dual edge of `ζ + λζ′` carries the factor
`1 + λ·(χ'/χ)(s)`, and Levinson's choice `λ ≍ 1/log(|t|/2π)` is exactly what makes that factor
vanish to leading order.  The two-edge main term is therefore controlled by this identity together
with the Stirling asymptotic, both now available; what remains is the evaluation of the resulting
direct, dual and cross contributions.

The tree already had *bounds* on `logDeriv zetaChi`
(`SmoothAFEZetaChiShiftVariationBound`, `norm_logDeriv_zetaChi_shift_sub_line_le`, and the
displaced-line bound), but not the identity.
