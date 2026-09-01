# Levinson / PRZZ critical-line proportion: the Lean programme

- **ID:** `levinson-critical-proportion-programme`
- **Stage:** 1-in-progress
- **Type:** PROGRAMME (formalization of `[LITERATURE]` results; `not_new_scientific_knowledge`)
- **Opened:** 2026-08-20
- **Reason it exists:** `horizontal-singleton-zero-fibers` (2-fully-proven) is complete except for
  two *cited* analytic inputs.  This card owns those inputs.

## What is needed and why

`horizontal-singleton-zero-fibers` proves, unconditionally and in Lean,

```text
H₁(T) ≥ N₀,s(T) − (N(T) − N₀(T))/2,          liminf H₁/N ≥ κ_* − (1−κ)/2,
```

where `κ = liminf N₀/N` and `κ_* = liminf N₀,s/N`.  The bound is non-vacuous exactly when
`κ_* > (1−κ)/2`; with `κ = κ_*` that is `κ > 1/3`.  So the card cannot be closed with any
proportion at or below Levinson's threshold — a genuinely `> 1/3` unconditional proportion is
required.  The card's advertised decimal `0.116158438` uses the Pratt–Robles–Zaharescu–Zeindler
constants `κ ≥ 0.417293962`, `κ_* ≥ 0.407511457`.

**No hypothesis wrapper is acceptable.**  A Lean theorem with `κ ≥ 0.417…` as a premise does not
close the card; the constants must be theorems.

## Dependency tree

| # | Brick | State |
|---|---|---|
| 1 | Littlewood's lemma on a rectangle, branch-free | **OWNED**: `RHTower/WeightedLittlewoodRectangle.lean`, `weighted_littlewood_from_rectIntegral` |
| 2 | log-mean → mean-square (Jensen step) | **DONE 2026-08-20**: `RHTower/LevinsonLogMeanStep.lean`, `two_mul_integral_log_norm_le` |
| 3 | Riemann–von Mangoldt `N(T) ~ (T/2π)log T` | **DONE 2026-08-20** — `RHTower/RiemannVonMangoldt.lean`, `exists_xiZeroCount_close` |
| 4 | Levinson's lemma | **DERIVED ON PAPER 2026-08-20** — full derivation below; formalization open |
| 5 | Twisted second moment of `ζ` on `Re s = 1/2 − R/log T` against a Dirichlet-polynomial mollifier of length `T^θ`, `θ < 1/2` | **MISSING** — the analytic heart. Balasubramanian–Conrey–Heath-Brown. Corpus owns the smooth AFE (`SmoothAFEZeta*`), the fourth-moment polylog bound, the Ingham mollifier second-moment stack, and Montgomery–Vaughan mean values (`RHTower/SecondMoment.lean`, `RHTower/Mollifier.lean`) |
| 6 | Mollified second moment `(1/T)∫_T^{2T}\|Vψ\|² → c(Q,θ,R)` and its optimization | **MISSING** — depends on (5) |
| 7 | `κ ≥ 1/3 + δ` (Levinson 1974) | depends on 1–6 |
| 8 | `κ_* ≥ κ` for the same mollifier (Heath-Brown / Selberg simple-zero variant) | **MISSING** |
| 9 | `θ = 4/7` (Conrey) — Deshouillers–Iwaniec / Watt spectral input for Kloosterman sums | **MISSING**, only needed for the PRZZ constants |
| 10 | PRZZ two-piece mollifier optimization to `0.417293962` / `0.407511457` | **MISSING**, depends on 9 |

Bricks 7–8 already make the singleton-fiber density non-vacuous (with a constant smaller than the
card's displayed one).  Bricks 9–10 are needed only for the exact displayed decimal.

## Corrected survey of brick 3 (2026-08-20, second pass)

The first survey was wrong: the corpus already carries almost the whole Riemann–von Mangoldt
computation.  The chain that exists:

* `RHTower/XiLogDerivFactorization.lean` — `logDeriv_xi_fourFactor`: `ξ'/ξ = 1/s + 1/(s−1)
  − ½log π + ½ψ(s/2) + ζ'/ζ`;
* `RHTower/XiVerticalPhaseTwo.lean` — `re_logDeriv_xi_two_add`, `integral_re_logDeriv_xi_two`,
  `abs_integral_rational_head_le` (`≤ π`), `abs_integral_re_logDeriv_zeta_two_le` (`≤ π`, via the
  principal logarithm on the half-plane `Re ζ(2+iy) > 0`);
* `RHTower/GammaVerticalPhaseAsymptotic.lean` — `gammaVerticalPhase`,
  `tendsto_gammaVerticalPhase_ratio`;
* `RHTower/XiVerticalRatioLimit.lean` — **`tendsto_vertical_ratio`**:
  `(∫₀^T Re(ξ'/ξ)(2+iy)dy)/(T log T) → 1/2`;
* `RHTower/XiHorizontalBound.lean` — `exists_horizontal_xi_bound`: the horizontal side is
  `O(log T)`, resting on `RHTower/ZetaRealTraceSignChanges.lean`'s `exists_horizontal_zeta_bound`
  (`S(T) = O(log T)`, Backlund via Jensen on the real trace);
* `RHTower/XiRectangleFold.lean` — `two_pi_mul_regionOrderSum_eq`, the quarter-path formula
  `Im ∮ = 4∫₀^T Re(ξ'/ξ)(a+iy)dy − 4∫_{1/2}^a Im(ξ'/ξ)(x+iT)dx`;
* `RHTower/XiSymmetricMassBounds.lean` — `xiSymmetricMass`, `two_pi_mul_xiSymmetricMass`,
  `exists_xiSymmetricMass_two_sided` (crude two-sided `T log T` bounds);
* `RHTower/XiAdmissibleHeights.lean` — `exists_admissible_height` (heights with no `ξ`-zero
  ordinate are dense), `exists_annular_mass_lower`;
* `RHTower/XiOrdinateBandCopies.lean` — `xiSymmetricMass_eq_support_sum`,
  `xiSymmetricMass_diff_eq_card` (monotonicity in usable form);
* `RHTower/XiZeroCountingFunction.lean` — `xiZeroCount`, `xiCriticalZeroCount` (`ℤ`-valued box
  masses), `xiZeroCount_mono`, `exists_xi_zero_im_mem_Ioc_of_lt`;
* `RHTower/RiemannXiRealAxisNonvanishing.lean` — `xi_ne_zero_of_ofReal`;
* `RHTower/BornTemperatureFactorType.lean` — `xi_zero_re_mem_open_unit`.

What is still missing for brick 3:

1. ~~the **sharp** ratio at admissible heights~~ — **DONE 2026-08-20**,
   `RHTower/XiSymmetricMassSharp.lean`:
   `exists_xiSymmetricMass_admissible_close (ε) (hε : 0 < ε) : ∃ T₀ ≥ 4, ∀ T ≥ T₀ admissible,
   |xiSymmetricMass T − (1/π)·T log T| ≤ ε·T log T`, together with `xiSymmetricMass_mono`;
2. ~~transfer to **arbitrary** heights~~ — **DONE 2026-08-20**,
   `RHTower/XiMassHeightTransfer.lean`: `mul_log_mono`, `neg_two_mul_le_log_one_sub`,
   `succ_mul_log_le`, `pred_mul_log_ge`, and
   `exists_xiSymmetricMass_close (ε) (hε : 0 < ε) : ∃ T₀ ≥ 4, ∀ T ≥ T₀,
   |xiSymmetricMass T − (1/π)·T log T| ≤ ε·T log T`;
3. ~~`xiSymmetricMass T = 2 · xiZeroCount T`~~ — **DONE 2026-08-20**,
   `RHTower/RiemannVonMangoldt.lean`: `xiSupportsPos`, `xiSupport_im_ne_zero`, `xiSupportConj`,
   `xiSupportMultiplicity_conj`, `xiSymmetricMass_eq_two_mul_pos`, `xiZeroCount_eq_pos_sum`,
   `xiSymmetricMass_eq_two_mul_xiZeroCount`;
4. ~~hence the asymptotic for `xiZeroCount`~~ — **DONE 2026-08-20**:
   `exists_xiZeroCount_close (ε) (hε : 0 < ε) : ∃ T₀ ≥ 4, ∀ T ≥ T₀,
   |N(T) − (1/2π)·T log T| ≤ ε·T log T`.  Brick 3 is closed.

## Brick 4 derived in full (2026-08-20)

The literature calls this step "well known" and cites Levinson (1974) or Conrey (1989); it is not
proved in the modern short treatments.  Here it is, dependency-closed, in the normalization the
Lean corpus uses.  (Transcribed from the Hecke-family form in J. Cantillo, *Critical zeros of Hecke
L-functions*, Rutgers thesis 2014, §3.1, to the zeta case; the numerical endgame follows M. P.
Young, *A short proof of Levinson's theorem*, arXiv:1002.4403.)

Write `γ(s) = π^{-s/2}Γ(s/2)`, so the completed zeta is `Λ = γ·ζ` with `Λ(s) = Λ(1−s)`.  Fix
`L = log T`, a parameter `r > 0`, and set `λ = −1/(rL)`,

```text
G(s) := ζ(s) + λ ζ'(s).
```

**(4a) A functional equation for `G`.**  From `γ(s)G(s) = Λ(s)(1 + λ(ζ'/ζ)(s))` and the same at
`1−s`, adding and using `0 = (Λ'/Λ)(s) + (Λ'/Λ)(1−s)`:

```text
Y(s)·Λ(s) = γ(s)G(s) + γ(1−s)G(1−s),      Y(s) := 2 − λ(γ'/γ)(s) − λ(γ'/γ)(1−s).
```

**(4b) The real detector.**  On `s = 1/2+it` one has `1−s = s̄`, and `γ`, `G` have real Taylor
coefficients, so `γ(1−s)G(1−s) = conj(γ(s)G(s))` and

```text
Y(1/2+it)·Λ(1/2+it) = 2·Re[γ(1/2+it)G(1/2+it)].
```

Since `Re(γ'/γ)(1/2+it) = ½log(t/2π) + O(1/t)` (the corpus owns this as
`re_digamma_vertical_bound_uncond`), `Y(1/2+it) = 2 + 1/r + o(1)`, which is nonzero for every
`r > 0`.  Hence **for `t` large, `Re[γ(1/2+it)G(1/2+it)] = 0` if and only if `ζ(1/2+it) = 0`.**
With `λ = 0` this degenerates to Hardy's `Z`; `λ ≠ 0` is Levinson's deformation.

**(4c) Argument variation.**  Let `N_G(T)` count the zeros of `G` with `1/2 < β < 4`, `0 < γ ≤ T`.
The argument principle on `[1/2, 4] × [0, T]`, with small right-hand dents around the zeros of `G`
on the critical segment, gives

```text
N_G(T) = −(1/2π)·Δ_Γ arg G(s) + O(T),
```

the right edge `Re s = 4` contributing `O(T)` by absolute convergence and the horizontal edges
`O(log T)`.

**(4d) The lower bound.**  Every `π`-variation of `arg[γG]` along the critical segment is a sign
change of `Re[γG]`, hence by (4b) a zero of `ζ` on the line, so

```text
N₀(T) ≥ (1/π)·Δ_Γ arg γ(s) + (1/π)·Δ_Γ arg G(s) = N(T) − N_G(T) + O(T),
```

because `(1/π)Δ_Γ arg γ = 2θ(T)/π = N(T)(1+o(1))` (the corpus owns `gammaHardyTheta` and now
`exists_xiZeroCount_close`).

**(4e) Mollify and apply Littlewood.**  Zeros of `G` are zeros of `GM` for any Dirichlet polynomial
`M`, so `N_G(T) ≤ N_{GM}(T)`.  Littlewood's lemma on `[σ₀, 4] × [0, T]` with `σ₀ = 1/2 − R/L`, plus
`β − σ₀ > R/L` for each zero with `β > 1/2`, plus the Jensen step `∫log|f| ≤ (T/2)log((1/T)∫|f|²)`,
gives

```text
N_G(T) ≤ (L/2πR)·(T/2)·log c + o(TL),      c := lim (1/T)∫_1^T |GM(σ₀+it)|² dt.
```

With `N(T) ~ (T/2π)L` this is `N_G(T)/N(T) ≤ (1/2R)log c`, whence **`κ ≥ 1 − (1/R)·log c`** once the
count is doubled by the functional equation (`N − N₀ = 2N⁻`).

**(4f) The constant.**  For the general operator `V(s) = Q(−L⁻¹ d/ds)ζ(s)` (Conrey's generalization
of `G`), mollifier `ψ(s) = Σ_{h≤M} μ(h)h^{-(s+1/2-σ₀)}P(log(M/h)/log M)`, `M = T^θ`, `P(0)=0`,
`P(1)=1`, Young's Theorem 1 gives

```text
(1/T)∫_1^T |Vψ(σ₀+it)|² dt = c(P,Q,R,θ) + o(1),
c(P,Q,R,θ) = 1 + (1/θ)∫_0^1∫_0^1 e^{2Rv} ( d/dx [ e^{Rx}P(x+u)Q(v+x) ]|_{x=0} )² du dv.
```

`P(x)=x`, `Q(x)=1−x`, `R=1.3`, `θ=1/2` give `c = 2.35…` and `κ ≥ 0.34…`.

**Formalization-hostile steps flagged.**
* (4c) the right-edge `O(T)` and the horizontal `O(log T)` are stated in the literature by analogy;
  the corpus owns the ξ-versions (`exists_horizontal_xi_bound`, `XiVerticalPhaseTwo`) and they must
  be redone for `G`, which is *not* an Euler product — the `ζ'/ζ` bound on `Re s = 4` is fine, but
  the horizontal bound needs a Jensen count for `Re[γG]`, mirroring `ZetaRealTraceSignChanges`.
* (4d) "every `π`-variation is a sign change" needs the dented contour and a limiting argument at
  the zeros of `G` on the line; this is the one genuinely fiddly piece.
* (5)/(6) Young's Lemma 5 uses repeated integration by parts with `|log(hm/kn)| ≫ (hkmn)^{-1/2}`,
  and his Lemma 7 replaces a sum by an integral "which requires some thought" — both must be made
  explicit.
* The final numerical step is an explicit definite integral of a polynomial times `e^{2Rv}`; it is
  exactly evaluable in closed form and must be, since the project forbids numerics.

## The consumer side is now closed (2026-08-20)

`horizontal-singleton-zero-fibers` no longer needs two proportions.  A new charging law
(`RHTower/HorizontalOddFiberCharging.lean`) plus the fibre-parity law
(`RHTower/HorizontalFibreParity.lean`) plus the sign-change bridge
(`RHTower/HardySignFlipOddOrder.lean`) reduce that card to the single statement

```text
liminf O(T)/N(T) > 1/3,        O(T) = # ordinates in (0,T] with odd critical multiplicity,
```

and `O(T)` is bounded below by the number of sign changes of Hardy's `Z`.  So bricks 7 and 8 of this
programme collapse to **brick 7 alone**: Levinson's method delivers sign changes of the real detector
`Re[γ(s)G(s)]` natively, and Heath-Brown's simple-zero refinement (brick 8) is no longer required.

| Brick | New state |
|---|---|
| 8 | **DROPPED** — the odd-fibre charging law removes it from the dependency list |

## Landed toward bricks 4 and 5 (2026-08-20)

* `RHTower/LevinsonDetectorFE.lean` — **step (4a) is Lean.**  `levinsonG lam s = ζ(s) + λζ'(s)`,
  `levinsonY lam s = 2 − λ·logDeriv Γ_ℝ(s) − λ·logDeriv Γ_ℝ(1−s)`,
  `completedRiemannZeta_eq_Gammaℝ_mul`, `deriv_completedRiemannZeta_one_sub` (`Λ'` is odd under the
  functional equation), `hasDerivAt_completedRiemannZeta_of_strip`, and
  **`levinsonY_mul_completedRiemannZeta`**: `Y(s)Λ(s) = Γ_ℝ(s)G(s) + Γ_ℝ(1−s)G(1−s)` on the open
  strip.  Axiom-clean.
* `RHTower/Sieve/DirichletMVTWindow.lean` — `dirichlet_meanValue_window` and
  `dirichlet_meanValue_dyadic`: the corpus's mean value theorem transported from the anchored
  interval `[0,T]` to an arbitrary window, error `8N(1+log N)∑|a|²`.  Every moment computation on
  `[T,2T]` needs this form.  Axiom-clean.

* `RHTower/LevinsonDetectorLine.lean` — **step (4b) is Lean, and unconditional.**
  `levinsonG_conj` (Schwarz symmetry of `G` for real `λ`, from the corpus's `riemannZeta_conj` and
  `deriv_riemannZeta_conj`), **`levinsonY_mul_completed_line`**:
  `Y(½+iτ)·Λ(½+iτ) = 2·Re[Γ_ℝ(½+iτ)·G(½+iτ)]`; `levinsonY_line_eq`, the explicit real form
  `Y(½+iτ) = 2 − λ·(Re ψ(¼+iτ/2) − log π)`; `log_pi_lt_re_digamma_quarter` (`Re ψ(¼+iτ/2) > log π`
  for `τ ≥ 20`, from `re_digamma_vertical_bound_uncond`); `levinsonY_line_ne_zero`; and the
  detection lemma

  ```text
  re_Gammaℝ_mul_levinsonG_eq_zero_iff_of_nonpos :
    λ ≤ 0 real, τ ≥ 20  →  ( Re[Γ_ℝ(½+iτ)·(ζ + λζ')(½+iτ)] = 0  ↔  ζ(½+iτ) = 0 ).
  ```

  Axiom-clean.  **Brick 4 steps (4a) and (4b) are complete**; what remains of brick 4 is the
  argument-principle bookkeeping (4c)–(4e).

### The detector adds nothing on the line — and that is exactly why the odd-fibre route works

`re_Gammaℝ_mul_levinsonG_eq_half_Y_mul_completed`:

```text
Re[Γ_ℝ(½+iτ)·G(½+iτ)] = (Y(½+iτ)/2)·Λ(½+iτ),        Y(½+iτ) ≠ 0.
```

So on the critical line the detector is the completed zeta times a nonvanishing real factor: same
zeros, same orders.  The whole gain of `λ ≠ 0` is *off* the line, where `G` has fewer zeros than `ζ`
and Littlewood's lemma can see it.

The consequence for `horizontal-singleton-zero-fibers` is decisive: **what Levinson's method counts
is sign changes of a function proportional to `Ξ`, hence critical zeros of odd order.**  That is
exactly `O(T)`, the quantity the odd-fibre charging law consumes.  So the chain

```text
Levinson  ⟹  liminf O/N ≥ 1 − (1/R)log c = 0.3474…  >  1/3  ⟹  liminf H₁/N ≥ (3/2)(0.3474) − 1/2 > 0
```

closes the card with **only** Levinson's constant — no Heath-Brown, no PRZZ.  The displayed decimal
`0.116158438` still needs PRZZ, but non-vacuity does not.

### Landed: the counting step of (4d), in its clean form (2026-08-20)

`HTGeometry/PhaseSignChain.lean` — **a phase advance of `nπ` forces `n` sign changes**, with no
complex numbers and no monotonicity assumption:

```text
firstHit φ a b c = sInf (Icc a b ∩ φ ⁻¹' Ici c)
firstHit_mem, firstHit_phase (φ(firstHit) = c), firstHit_mono
exists_sign_chain_of_phase_increase :
  φ continuous on [a,b], ρ > 0, φ a ≤ m₀π, (m₀+n)π ≤ φ b
  →  ∃ g, strictly increasing on 0..n, in [a,b], with
     (ρ·cos φ)(g i)·(ρ·cos φ)(g (i+1)) < 0 for every i < n.
```

The chain is the sequence of first hitting times of the levels `(m₀+i)π`: distinct phase values make
them strictly increasing, and `cos` alternates in sign between consecutive integer multiples of `π`
while never vanishing there.  Axiom-clean.

This is exactly the shape `RHTower/HardySignChainCount.lean` consumes, so once the polar phase of
`Γ_ℝ(½+iτ)·G(½+iτ)` is produced with a lower bound for its advance, the whole chain

```text
phase advance  ⟹  sign chain  ⟹  odd-order ordinates  ⟹  H₁ ≥ (3/2)n − N/2
```

is closed in Lean.

### Landed: the polar form (2026-08-20)

`HTGeometry/SegmentPolarForm.lean` — the missing link between an argument-variation bound and a
sign-change count:

```text
exists_continuousOn_log_of_hasDerivAt :
  f differentiable, f'/f continuous, f ≠ 0 on [a,b]
  →  ∃ L continuous on [a,b] with f = exp L
exists_continuousOn_polar :
  same hypotheses  →  ∃ r ψ, ψ continuous, r > 0, (f τ).re = r τ · cos (ψ τ)  on [a,b]
```

The logarithm is `log (f a) + ∫_a^τ f'/f`; the check is that `f·exp(−L)` has vanishing derivative
and equals `1` at the left endpoint.  Axiom-clean.

**The downstream half of the card is therefore closed as a single chain:**

```text
Δψ ≥ nπ  →[SegmentPolarForm + PhaseSignChain]→  n sign changes
        →[HardySignFlipOddOrder]→  n odd-order ordinates
        →[HorizontalFibreParity + HorizontalOddFiberCharging]→  H₁ ≥ (3/2)n − N/2
```

Every arrow is unconditional Lean.  Note that the corpus already supplies the polar phase of the
archimedean factor on the line: `gammaHardyPhase τ = conj(Γ_ℝ(½+iτ))/‖Γ_ℝ(½+iτ)‖ = exp(−iθ(τ))`,
so `Γ_ℝ(½+iτ) = ‖Γ_ℝ(½+iτ)‖·exp(iθ(τ))` with `θ = gammaHardyTheta` continuous and explicitly
asymptotic.

### Landed: the interface and the polar identity (2026-08-20)

* `RHTower/PhaseAdvanceToSingletonFibre.lean` — **the single interface every Levinson-type argument
  has to hit**:

  ```text
  le_xiOddFiberCount_of_phase_advance,  xiSingletonFiberCount_ge_of_phase_advance :
    on [T₁,T₂] ⊆ (0,∞),  Z = ρ·cos ψ  with ρ > 0, ψ continuous, ψ(T₂) − ψ(T₁) ≥ nπ
    ⟹  O(T₂) ≥ n  and  H₁(T₂) ≥ (3/2)n − N(T₂)/2.
  ```

* `RHTower/CompletedLinePolar.lean` — `Gammaℝ_line_eq_norm_mul_exp_theta`
  (`Γ_ℝ(½+iτ) = ‖Γ_ℝ(½+iτ)‖·exp(iθ(τ))`, from the corpus's `gammaHardyPhase_eq_exp_neg_theta`) and
  **`completedRiemannZeta_line_eq_norm_mul_hardyZ`**: `Λ(½+iτ) = ‖Γ_ℝ(½+iτ)‖·Z(τ)`.  This is what
  turns the detector identity `Y·Λ = 2·Re[Γ_ℝ·G]` into a polar representation of `Z` with phase
  `θ + ψ_G` and amplitude `2 r_G /(Y‖Γ_ℝ‖) > 0`.

* `HTGeometry/SegmentPolarForm.lean` was generalized to segment hypotheses
  (`HasDerivAt` and continuity of `f'/f` only on `[a,b]`), via a clamped extension of the
  logarithmic derivative, so it applies to `Γ_ℝ·G` on a `G`-zero-free window.

### Landed: the polar representation of `Z` from the detector (2026-08-20)

`RHTower/LevinsonDetectorPolar.lean`:

* **`levinsonY_line_mul_hardyZ`** — the archimedean modulus cancels out of the detector identity:

  ```text
  Y(½+iτ)·Z(τ) = 2·Re[ exp(iθ(τ))·G(½+iτ) ].
  ```

* `analyticAt_riemannZeta_of_ne_one`, `analyticAt_levinsonG`, `linePt_ne_one'`,
  `hasDerivAt_detectorPhase`, `continuous_linePt'` — the regularity of
  `τ ↦ exp(iθ(τ))·G(½+iτ)` (`ζ` and `ζ'` are analytic away from `s = 1`, and the critical line
  misses it).

* **`exists_polar_hardyZ_of_levinsonG_ne_zero`** — for real `λ ≤ 0`, on a window `[T₁,T₂]` with
  `T₁ ≥ 20` on which `G(½+iτ) ≠ 0`:

  ```text
  ∃ ρ ψ,  ψ continuous,  ρ > 0,  Z τ = ρ τ · cos (ψ τ)   on [T₁,T₂],
  ```

  with `ρ = 2r/Y` (positive because `Y ≥ 2` there) and `ψ` the phase of `exp(iθ)·G`.

Axiom-clean.  **This is precisely the hypothesis of
`xiSingletonFiberCount_ge_of_phase_advance`**, so the chain from Levinson's detector to the
singleton-fibre density is now closed except for one inequality.

### The single remaining inequality

A lower bound for the advance `ψ(T₂) − ψ(T₁)` of that phase.  Since `ψ = θ + ψ_G`, and
`θ(T₂) − θ(T₁)` is `≈ π·N(T₂,T₁)` by the corpus's `gammaHardyTheta` asymptotics, what is needed is
an upper bound for `|ψ_G(T₂) − ψ_G(T₁)|` — the argument variation of `G` along the critical
segment.  That is the argument principle on `[½,4]×[T,2T]` (a window avoiding `ζ`'s pole at `s=1`)
followed by Littlewood's lemma and the mollified second moment.  The corpus's
`RHTower/ArgumentVariation.lean` (Borel–Carathéodory, winding-phase caps, lattice rigidity) is the
toolkit.

## Order of work

3 → 4 → 5 → 6 → 7, then 9 → 10 (only if the exact PRZZ decimal is wanted).

## Log

- 2026-08-20 — Card opened while closing `hardy-critical-line-moment-anchor`.  Brick 2 formalized
  as `RHTower/LevinsonLogMeanStep.lean` (`two_mul_integral_log_norm_le`); the corpus's
  `RHTower/MeanValueBridge.lean` already carried the same fact in probability-average form
  (`jensen_avg_log_sq`), the new module is the interval-integral spelling Littlewood's lemma
  consumes.  Brick 1 found already owned.
- 2026-08-20 (fourth pass) — **Brick 3 CLOSED.**  `RHTower/RiemannVonMangoldt.lean` proves the
  Riemann–von Mangoldt asymptotic unconditionally, by halving the symmetric divisor mass along the
  fixed-point-free conjugation involution (`ξ` has no real zero) and combining with
  `exists_xiSymmetricMass_close`.  Axiom-clean.
- 2026-08-20 (third pass) — Brick 3 items 1 and 2 landed:
  `RHTower/XiSymmetricMassSharp.lean` (`xiSymmetricMass_mono`,
  `exists_xiSymmetricMass_admissible_close`) and `RHTower/XiMassHeightTransfer.lean`
  (`exists_xiSymmetricMass_close`).  Both axiom-clean.  What remains of brick 3 is only the
  combinatorial halving `xiSymmetricMass T = 2·xiZeroCount T`.
- 2026-08-20 (second pass) — A first draft of the right-edge asymptotic
  (`XiRightEdgeAsymptotic.lean`) was written and then **deleted**: `RHTower/XiVerticalPhaseTwo.lean`
  and `RHTower/XiVerticalRatioLimit.lean` already prove it, in a sharper form.  The corrected survey
  above replaces the original brick-3 entry.

## Brick 4 — the argument-variation package (2026-08-20, fifth pass)

The single remaining inequality of the previous pass has been decomposed into an exact identity plus
three edge estimates, and the identity and two of the estimates are now Lean-proved.

### 4a. The phase advance is an integral

`HTGeometry/SegmentPolarForm.lean` (strengthened): `exists_continuousOn_log_of_hasDerivAt` now also
returns `HasDerivAt L (f'/f)`, `exists_continuousOn_polar` returns `HasDerivAt ψ (Im (f'/f))`, and

* **`exists_continuousOn_polar_advance`** — `ψ b − ψ a = ∫_a^b Im(f'/f)`.

`RHTower/LevinsonPhaseAdvance.lean`:

* `integral_gammaHardyPhaseRate` — `∫_a^b θ' = θ(b) − θ(a)`.
* `detector_logDeriv_eq`, `im_detector_logDeriv_eq` — the logarithmic derivative of `e^{iθ}·G(½+i·)`
  is `i·(θ' + (G'/G)(½+i·))`, so its imaginary part is `θ' + Re (G'/G)`.
* **`exists_polar_hardyZ_advance_of_levinsonG_ne_zero`** —

  ```text
  ψ(T₂) − ψ(T₁) = (θ(T₂) − θ(T₁)) + ∫_{T₁}^{T₂} Re (G'/G)(½+it) dt.
  ```

### 4b. The entire detector and the rectangle argument principle

`RHTower/LevinsonEntireDetector.lean` defines

```text
G♯(s) = (s−1)·zetaEntire(s) + λ·((s−1)·zetaEntire′(s) − zetaEntire(s)),
```

proves it entire (`differentiable_levinsonGEntire`), equal to `(s−1)²G(s)` off the pole
(`levinsonGEntire_eq`), with the same zeros there (`levinsonGEntire_eq_zero_iff`), value `−λ` at the
pole (`levinsonGEntire_one`, hence not identically zero), and

* **`logDeriv_levinsonGEntire`** — `logDeriv G♯ = 2/(s−1) + logDeriv G`.

`RHTower/EntireArgumentVariationRectangle.lean` takes the imaginary part of the unweighted rectangle
argument principle (`rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd` with weight `1`, then
`two_pi_mul_weighted_re_sum_eq_edges`) and obtains, for entire `f` nonvanishing on the boundary:

* **`exists_entire_argument_variation_rectangle`** —

  ```text
  ∫_{T₁}^{T₂} Re (f'/f)(c+it) dt
    = ∫_{T₁}^{T₂} Re (f'/f)(d+it) dt
      + ∫_c^d Im (f'/f)(x+iT₁) dx − ∫_c^d Im (f'/f)(x+iT₂) dx
      − 2π·#{zeros in [c,d]×[T₁,T₂]}.
  ```

`RHTower/LevinsonEntirePhaseAdvance.lean` transports 4a to `G♯`: on the critical line
`Re[2/(−½+iτ)] = −(¼+τ²)^{-1} ≤ 0`, so the correction only helps —

* **`exists_polar_hardyZ_advance_entire_le`** —

  ```text
  (θ(T₂) − θ(T₁)) + ∫_{T₁}^{T₂} Re (G♯'/G♯)(½+it) dt  ≤  ψ(T₂) − ψ(T₁).
  ```

`RHTower/LevinsonWindowAdvance.lean` composes the two into the **window inequality**
`exists_levinson_window_advance`, and `RHTower/PhaseAdvanceIncrementCount.lean`
(`le_xiOddFiberCount_of_increment`, `xiSingletonFiberCount_ge_of_increment`) converts a raw
increment `(n+1)π` into `n` odd fibres by anchoring at `m₀ = ⌈ψ(T₁)/π⌉`.

### 4c. The right edge — one half-turn

`RHTower/ZetaFarRightDecay.lean` proves the geometric tail decay
`‖ζ(s) − 1‖ ≤ (3/4)·2^{−m}` for `Re s ≥ 2 + m` (`norm_riemannZeta_sub_one_le_scaled`), hence
`≤ 3/8` at `Re s ≥ 3` and `≤ 3/16` at `Re s ≥ 4`; Cauchy's estimate on the unit disc applied to
`ζ − 1` then gives `‖ζ'(s)‖ ≤ 3/8` for `Re s ≥ 4`.

`RHTower/LevinsonRightEdge.lean`: for `‖λ‖ ≤ 1`, `‖G(s) − 1‖ ≤ 9/16` and therefore
`Re G(s) ≥ 7/16 > 0` on `Re s ≥ 4`.  A function with positive real part has argument variation at
most `π`, so

* **`abs_integral_re_logDeriv_levinsonG_right_le`** — `|∫_{T₁}^{T₂} Re (G'/G)(4+it) dt| ≤ π`.

Positivity also supplies the nonvanishing hypotheses of the rectangle theorem on the right edge.

### 4d. The horizontal edges — `O(log T)`

`HTGeometry/SegmentArgumentBound.lean` combines the continuous logarithm along a segment with
Backlund's sign-change step:

* **`abs_integral_im_logDeriv_le_of_finite_re_zeros`** —
  `|∫_a^b Im(f'/f)| ≤ (#Z + 1)·π` whenever `Z` contains every zero of `Re f` in `(a,b)`.

`RHTower/LevinsonStripBound.lean` transfers the crude polynomial bound for `ζ` on a strip to `ζ'`
(Cauchy on the unit disc) and hence to `G`.

`RHTower/LevinsonRealTrace.lean` introduces the analytic real trace
`(G(z+iT) + G(z−iT))/2`, which is `Re G(σ+iT)` on the real axis by `levinsonG_conj`, is analytic on
`|Im z| < 5` for `T ≥ 6`, is at least `7/16` in modulus at the centre `z = 4`, and obeys the
polynomial bound on the sphere of radius `4`.  Jensen's inequality
(`HTGeometry/UniformZeroCountBound.sum_divisor_le_of_bounds`) then gives

* **`exists_levinsonGTrace_count_bound`** — the trace has `O(log T)` zeros in the disc of radius
  `7/2` about `4`, uniformly in `|λ| ≤ 1`.

`RHTower/LevinsonHorizontalEdge.lean` combines the two:

* **`exists_horizontal_levinsonG_bound`** —
  `|∫_{1/2}^{4} Im (G'/G)(x+iT) dx| ≤ c·log T` for every `T ≥ 6` at which `G` does not vanish on the
  segment.

### What is left of brick 4

Only the assembly and the density of admissible heights for `G` (the finiteness of `G`-zeros in a
compact box gives them exactly as `exists_admissible_height` does for `ξ`).  After that the window
inequality reads

```text
ψ(T₂) − ψ(T₁) ≥ (θ(T₂) − θ(T₁)) − 2π·N_{G♯}([½,4]×[T₁,T₂]) − O(log T),
```

with `θ(T₂) − θ(T₁) ≈ π·(N(T₂) − N(T₁))`, so the whole Levinson programme has been reduced to the
single quantity `N_{G♯}([½,4]×[T₁,T₂])` — brick 5, the mollified second moment.

### 4f. The one structural hypothesis still carried

`exists_polar_hardyZ_of_levinsonG_ne_zero` and everything above it assume `G(½+iτ) ≠ 0` on the
window.  This is not automatic: a zero of `G` on the critical line is exactly a point where
`Re[e^{iθ}G] = ½Y·Z` vanishes, i.e. a critical-line zero of `ζ` at which the detector also vanishes.

The removal is a finite induction, not a new idea.  The zeros of `G` on the segment are the zeros of
the entire `G♯` on the left edge of a compact rectangle, hence finitely many, say
`τ_1 < … < τ_k` with multiplicities `m_i`.  On each closed subinterval avoiding them the polar form
applies, and across `τ_i` the factor `(s − ½ − iτ_i)^{m_i}` restricted to the line is
`(i(τ − τ_i))^{m_i}`, whose argument *increases* by `m_i π`.  So the total advance is the sum of the
subinterval advances plus `π Σ m_i`, i.e. dropping the hypothesis can only increase the bound.  The
Lean work is the bookkeeping of the finite chain, not new mathematics.

## Brick 5 — corpus assets already owned (survey, 2026-08-20)

The mollified second moment is the last analytic input.  The corpus already owns most of its
non-twisted infrastructure:

* `RHTower/SecondMoment.lean` — `secondMoment_meanValue`: `∫‖F‖² = U·∑ a_n² + ` explicit
  off-diagonal double sum, for a general Dirichlet polynomial; and `secondMoment_meanValue_sqrt` for
  the AFE carrier `∑_{n≤N} n^{-1/2-it}`.
* `RHTower/Mollifier.lean` — `mollifier_secondMoment`: the Montgomery–Vaughan mean value of the
  Möbius mollifier with squarefree-supported diagonal and explicit off-diagonal.
* `RHTower/MFreeLadder.lean` — the same for the square-dilated Möbius mollifier.
* `RHTower/Sieve/DirichletMVT.lean`, `RHTower/Sieve/DirichletMVTWindow.lean` — the Dirichlet
  mean-value theorem on a window and on a dyadic block.
* `RHTower/SmoothAFEZetaExact.lean` — the exact Gaussian smooth approximate functional equation,
  `ζ(½+iτ) = ∑ cutoff-weighted n^{-1/2-iτ} − dual − residue`, with the dual edge already expanded as
  a Dirichlet series (`SmoothAFEZetaDualExpansion`).
* `RHTower/Sieve/InghamMollifierSecondMoment.lean` — the actual critical-line mollifier second
  moment with explicit constants.

What is missing is the **twist**: every mean value above is untwisted, and Levinson's evaluation
needs `∫_0^T ζ(½+α+it)ζ(½+β−it)(h/k)^{-it} dt` for `h,k ≤ T^θ`, `θ < 1/2`, with a power-saving
error.  With the smooth AFE in hand this is a diagonal `mh = nk` computation plus an off-diagonal
sum controlled by `∑ 1/|log(mh/nk)|`; the corpus's off-diagonal machinery in `SecondMoment.lean` is
the right shape but is written for the untwisted diagonal `m = n`.

### 4f, corrected: removing the hypothesis is free

The earlier sketch was pessimistic.  The exact accounting is this.

Let `τ_1 < … < τ_k` be the ordinates in `[T₁,T₂]` at which `G(½+iτ) = 0`, with multiplicities
`m_i`, and put `M = Σ m_i`.  Two observations make the hypothesis removable at no cost.

1. **The integrand does not blow up.**  Near a line zero `s₀ = ½+iτ_0` of order `m`,
   `logDeriv G♯(s) = m/(s−s₀) + h(s)` with `h` analytic, and on the critical line
   `s − s₀ = i(τ−τ_0)`, so the singular part is `−i m/(τ−τ_0)`, which is *purely imaginary*.
   Hence `Re (G♯'/G♯)(½+iτ)` extends continuously across every line zero, and
   `∫_{T₁}^{T₂} Re (G♯'/G♯)(½+it) dt` is an ordinary integral.

2. **Indentation costs exactly `π` per unit of multiplicity.**  Indenting the left edge to the
   right around each line zero excludes it from the rectangle and contributes `−π m_i` (half of the
   full `−2π m_i`).  So

   ```text
   ∫_{T₁}^{T₂} Re (G♯'/G♯)(½+it) dt = (three edges) − 2π·N_int − π·M,
   ```

   where `N_int` counts the zeros in the *open* rectangle, and `N_total = N_int + M`.

Splitting `[T₁,T₂]` at the `k` line zeros, the phase is defined on each closed subinterval and the
anchored counting lemma loses at most one half-turn per subinterval, i.e. `k+1` in total.  Summing,

```text
n ≥ Δθ/π − 2N_int − M − (k+1) ≥ Δθ/π − 2N_int − 2M − 1 = Δθ/π − 2·N_total − 1,
```

using `k ≤ M`.  **This is exactly the bound of the zero-free case**, with the closed-rectangle zero
count in place of the open one.  So hypothesis 4f can be removed without weakening the constant;
what it costs is the Lean work of (i) the continuous extension of `Re (G♯'/G♯)` across a line zero,
(ii) the indented rectangle argument principle, and (iii) the finite subdivision bookkeeping.

## Verification log

- 2026-08-20 — **Brick 4 closed and machine-checked.**  `lake build` green for, in dependency
  order: `HTGeometry/SegmentPolarForm` (strengthened), `HTGeometry/SegmentArgumentBound`,
  `RHTower/LevinsonPhaseAdvance`, `RHTower/EntireArgumentVariationRectangle`,
  `RHTower/LevinsonEntireDetector`, `RHTower/LevinsonEntirePhaseAdvance`,
  `RHTower/PhaseAdvanceIncrementCount`, `RHTower/LevinsonWindowAdvance`,
  `RHTower/ZetaFarRightDecay`, `RHTower/LevinsonStripBound`, `RHTower/LevinsonRightEdge`,
  `RHTower/LevinsonAdmissibleHeight`, `RHTower/LevinsonRealTrace`,
  `RHTower/LevinsonHorizontalEdge`, `RHTower/LevinsonWindowBound`.  All are wired into their
  area umbrellas.  The capstone is `exists_levinson_window_edge_bound`.
- 2026-08-20 — Brick 5 groundwork landed: `HTGeometry/ExponentialWindowIntegral` (`expInt`,
  `expInt_zero`, `expInt_eq`, `norm_expInt_le`, `norm_expInt_le_length`),
  `HTGeometry/TwistedDirichletMeanValue` (`cdterm`, `cdpoly`, `twisted_meanValue`) and
  `HTGeometry/TwistedDiagonal` (`sub_div_le_log_sub_log`, `inv_le_abs_log_sub_log`,
  `twistedFreq_eq`, `expInt_twisted_diag`, `norm_expInt_twisted_offdiag`) all build.

## Brick 5a — the twisted mean value of a Dirichlet polynomial (2026-08-20)

Landed and machine-checked:

* `HTGeometry/ExponentialWindowIntegral.lean` — `expInt L T U = ∫_T^{T+U} e^{iLt}dt`, with
  `expInt 0 T U = U`, the closed form, `‖expInt‖ ≤ 2/|L|` and `‖expInt‖ ≤ U`.
* `HTGeometry/TwistedDirichletMeanValue.lean` — `cdterm`, `cdpoly`, and the **exact** identity

  ```text
  ∫_T^{T+U} A(σ+it)·conj B(σ+it)·e^{iL₀t} dt
      = ∑_{m,n} a_m conj(b_n) (mn)^{-σ} · expInt(log n − log m + L₀).
  ```

* `HTGeometry/TwistedDiagonal.lean` — for a twist by `(h/k)^{-it}` the frequency is
  `log(nk) − log(mh)`; `expInt` is `U` on the diagonal `nk = mh` and `O(max(nk,mh))` off it.
* `HTGeometry/TwistedMeanValueSplit.lean` — the exact diagonal/off-diagonal split
  `U·(diagonal) + (off-diagonal)`, and the termwise off-diagonal bound.
* `HTGeometry/VerticalLogDerivRegular.lean` — `Re (f'/f)` along a vertical line through a zero of
  order `m` equals `Re` of the cofactor's logarithmic derivative, because the singular part
  `m/(iτ)` is purely imaginary.  (This is ingredient (i) of brick 4f.)
* `RHTower/Sieve/DistinctReciprocalSum.lean` — a finite set of positive integers has reciprocal sum
  at most the harmonic number of its cardinality (`sum_inv_le_sum_Icc`), hence
  `∑ 1/|v i| ≤ 2(1 + log #s)` for any family of **distinct nonzero integers**
  (`sum_inv_abs_le_of_injOn`).  This is the combinatorial engine of every off-diagonal estimate.

Next: `RHTower/Sieve/TwistedOffDiagonalSum.lean` (`|log A − log B| ≥ |A−B|/max(A,B)`, and the row
sum `∑_n 1/|nk − mh| ≤ 2(1 + log #s)` from the distinct-integer lemma), then the twisted mean value
theorem in error form, then the approximate functional equation step.

### Brick 5a closed (2026-08-20)

`RHTower/Sieve/TwistedOffDiagonalSum.lean` (`abs_sub_div_max_le_abs_log_sub_log`,
`two_div_abs_log_twisted_le`, `sum_inv_abs_twisted_row_le`) and
`RHTower/Sieve/TwistedMeanValueError.lean` build, giving

* **`twisted_meanValue_error`** — for Dirichlet polynomials supported on `s`, a twist by
  `(h/k)^{-it}`, any bound `B` on `nk` and `mh`, and any uniform coefficient bound `C`:

  ```text
  ‖ ∫_T^{T+U} A·conj B·(h/k)^{-it} − U · ∑_{nk = mh} a_m conj(b_n) (mn)^{-σ} ‖
      ≤ 4 · #s · C · B · (1 + log #s).
  ```

Axiom audit: all 23 capstones of bricks 4 and 5a depend only on
`propext, Classical.choice, Quot.sound`.

## Brick 5b — the shifted approximate functional equation (scoped 2026-08-20)

`RHTower/Sieve/TwistedDiagonalReindex.lean` closes the diagonal:

* **`twisted_diagonal_reindex`** — for coprime `h,k`, the pairs with `nk = mh` are exactly
  `(kd, hd)`, so the twisted diagonal is the single sum `∑_d f(kd, hd)`.
  (`twisted_diagonal_decomp` isolates the arithmetic: `k ∣ mh` and `(h,k)=1` force `k ∣ m`.)

With the twisted mean value and its diagonal in hand, the remaining input is a Dirichlet-polynomial
representation of `ζ` at the Levinson abscissa `σ₀ = ½ − R/log T`.

**Plain truncation is provably insufficient.**  The corpus's exact Euler–Maclaurin identity
`riemannZeta_eq_sum_add_tail` gives
`ζ(w) = ∑_{k ≤ N} k^{-w} + O(N^{1-σ}/|w−1|) + O(|w| N^{-σ}/σ)`.  At `σ ≈ ½` the second error is
`≍ T·N^{-1/2}`, so a useful error needs `N ≫ T²` — and then the mean-value error term
`4·N·y·(1+log N)` swamps the main term `U ≍ T`.  The approximate functional equation, with its
length `≍ √T`, is therefore not a convenience but a necessity.

**What has to be generalized.**  The corpus owns a complete *exact* Gaussian smooth AFE, but every
statement in the chain is written at `linePt τ`:

* `SmoothAFEZetaExact.riemannZeta_line_eq_tsum_smoothAFECutoff_sub_dual_sub_residue`,
* `SmoothAFEZetaStripBound.smoothAFEZetaMellin_infinite_contour_shift_line`,
* `SmoothAFEZetaInfiniteContour.smoothAFEZetaMellin_infinite_contour_shift_line_of_horizontal_tendsto`
  and its two horizontal-decay inputs.

The Dirichlet expansion `smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff` is *already general in `s`*
(it needs only `1 < Re s + c`).  So brick 5b is exactly: replace `linePt τ` by a general `s` with
`|Re s − ½| ≤ ½` in the contour-shift chain, checking that the Gaussian horizontal decay estimates
are uniform in that strip.  Since Levinson's abscissa satisfies `|σ₀ − ½| = R/log T → 0`, uniformity
on any fixed strip around the critical line suffices.

## Brick 5b CLOSED — the smooth AFE at a general point (2026-08-20)

The Gaussian smooth approximate functional equation now holds at **every** `s` in the open strip
`0 < Re s < 2` with `s ≠ 1`, not just on the critical line.  Five new modules, each scratch-checked
clean:

* `RHTower/ZetaVerticalLineGrowth.lean` — **`exists_bound_norm_riemannZeta_vertical`**: for any
  abscissa `σ ≠ 1`, `‖ζ(σ+it)‖ ≤ C(1+|t|)^N` for *every* `t`.  (The corpus's strip bound covers only
  `|t| ≥ 1`; below it the segment is compact and `ζ` continuous.)
* `RHTower/GaussianShiftedMoment.lean` — **`integrable_shifted_pow_mul_exp_neg_sq`**:
  `(a+|v|)^N e^{-v²}` is integrable, by binomial expansion into the corpus's monomial moments.
* `RHTower/SmoothAFEZetaGeneralHorizontal.lean` — the horizontal Gaussian edges vanish at a general
  base point (`tendsto_smoothAFEZetaMellinIntegrand_horizontal_general`), with the explicit
  majorant `C·max(x,x⁻¹)·e · (|Im s|+|v|)^N e^{-v²}` and the limit lemma
  `tendsto_shifted_pow_mul_exp_neg_sq`.
* `RHTower/SmoothAFEZetaGeneralVertical.lean` — **both** vertical edges are integrable at a general
  base point (`smoothAFEZetaMellinIntegrand_verticalIntegrable_general`), the only hypotheses being
  `c ≠ 0` (avoid the kernel's pole) and `Re s + c ≠ 1` (avoid zeta's).  This removes the corpus's
  `1 < Re s + c` restriction and its critical-line-only left-edge argument.
* `RHTower/SmoothAFEZetaGeneral.lean` — the assembly:
  `smoothAFEZetaMellin_finite_contour_shift_general`,
  `smoothAFEZetaMellin_infinite_contour_shift_general`, and the two exact forms
  **`riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general`** and
  **`riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general`**:

  ```text
  ζ(s) = ∑_{n≥1} n^{-s} W(n/x) − (reflected Mellin integral) − x^{1-s}e^{(1-s)²}/(1-s).
  ```

The rectangle identity `rectIntegral_smoothAFEZetaMellinIntegrand_horizontal_box` and the Dirichlet
expansion `smoothAFEZetaMellinAt_eq_tsum_smoothAFECutoff` were already general in `s`; what was
missing — and is now supplied — is the edge analysis.

Axiom audit (2026-08-20): all nine brick-5b capstones plus `twisted_diagonal_reindex` depend only
on `propext, Classical.choice, Quot.sound`.

## Brick 5c — the AFE as a finite Dirichlet polynomial (2026-08-20)

`RHTower/SmoothAFETruncation.lean` (builds clean, no warnings):

* `norm_smoothAFE_term_le` — `‖n^{-s}·W(n/x)‖ ≤ K·x^A·n^{-(Re s + A)}` from the Gaussian cutoff's
  arbitrary-power decay `exists_norm_smoothAFECutoff_le_neg_rpow`.
* `exists_smoothAFE_direct_tail_le` — the tail of the direct edge beyond `L` is at most
  `C·x^A·L^{1-Re s-A}/(Re s + A − 1)`, using the corpus's integral-test tail
  `Sieve.tsum_tail_rpow_neg_le`.
* `summable_smoothAFE_direct` — the direct edge converges at *any* abscissa (the cutoff, not the
  exponent, supplies convergence).
* **`exists_riemannZeta_sub_smoothAFE_head_le`** —

  ```text
  ‖ ζ(s) − ( ∑_{n ≤ L} n^{-s}W(n/x) − (reflected edge) − (pole term) ) ‖
      ≤ C · x^A · L^{1-Re s-A}/(Re s + A − 1),
  ```

  for every `s` with `0 < Re s < 2`, `s ≠ 1`, every `x > 0`, every `A > 0` with `Re s + A > 1`.

Choosing `A` large and `L` a small power above `x` makes the error negligible, so at the Levinson
abscissa `σ₀ = ½ − R/log T` the zeta function *is* a finite Dirichlet polynomial of length `≍ √T`
up to the reflected edge, the pole term, and a power saving.  This is exactly the input
`twisted_meanValue_error` consumes, and it is why `θ < 1/2` is the right mollifier constraint: the
mean-value error `4·#s·C·B·(1+log #s)` is then `≍ T^{1/2+θ+ε} = o(T)`.

**Remaining in brick 5:** the reflected edge's own Dirichlet expansion (the corpus's
`smoothAFEZetaDualCutoff` at a general point), then the assembly of `∫|G♯M|²` and the arithmetic
main term.

## Brick 5d — the movable left edge (2026-08-20)

`RHTower/SmoothAFEZetaGeneralEdge.lean` (scratch-clean on first try) repeats the general-point
contour analysis with the reflected edge at `Re w = -c` instead of `-1`:

* `smoothAFEZetaDualMellinEdge`, `tendsto_smoothAFEZetaMellinIntegrand_horizontal_edge`,
  `smoothAFEZetaMellin_finite_contour_shift_edge`,
  `smoothAFEZetaMellin_infinite_contour_shift_edge`, and
  **`riemannZeta_eq_smoothAFEZetaMellin_sub_dualEdge_sub_residue`**, valid for `0 < c ≤ 1`,
  `s ≠ 1`, `0 < Re s < 1 + c`.

**Why the edge has to move.**  Expanding the reflected edge into a dual Dirichlet series needs two
things at once:

* `Re(1 − s − w) = 1 − Re s + c > 1`, i.e. `c > Re s`, for the dual series to converge;
* `Re(s + w) = Re s − c ∈ [−1/2, 1/2]`, the strip on which the corpus controls the
  functional-equation factor (`norm_zetaChi_le_half_strip`), i.e. `c ≤ Re s + 1/2`.

At the fixed edge `c = 1` and Levinson's abscissa `σ₀ = ½ − R/log T` the second condition fails
(`σ₀ − 1 < −1/2`).  Choosing `c = Re s + 1/4` satisfies both, and `c ≤ 1` holds for `Re s ≤ 3/4`.

**Next:** the dual expansion itself — `ζ(s+w) = χ(s+w)·ζ(1−s−w)`, termwise, with Fubini justified
by the χ bound times the Gaussian.  That is the last structural piece of the AFE side; after it the
mollified second moment is an assembly of `twisted_meanValue_error` over the two edges.

### The χ input for the dual expansion (2026-08-20)

`RHTower/ZetaChiVerticalGrowth.lean` (scratch-clean):

* `vertical_ne_neg_two_mul`, `one_sub_vertical_ne_neg_two_mul` — on the strip `-1 ≤ σ ≤ 1/2` with
  `σ ≠ 0`, neither `s` nor `1-s` meets the pole ladder of `Γ_ℝ`;
* `Gammaℝ_vertical_ne_zero`, `Gammaℝ_one_sub_vertical_ne_zero`, `continuousAt_Gammaℝ_of_ne_poles`,
  `continuousAt_zetaChi_vertical`;
* **`exists_bound_norm_zetaChi_vertical`** — `‖χ(σ+it)‖ ≤ C(1+|t|)²` for *every* `t`, on
  `-1 ≤ σ ≤ 1/2`, `σ ≠ 0`.

The corpus already owned the two strip bounds above ordinate `2`
(`norm_zetaChi_le_negative_one_strip` on `[-1,-1/2]` and `norm_zetaChi_le_half_strip` on
`[-1/2,1/2]`); what was missing is the compact part, exactly as for `ζ`.  Note this also shows the
fixed edge `Re w = -1` is already usable at the Levinson abscissa: `Re(s+w) = σ₀ - 1 ∈ (-1,0)` lies
in the covered range and `Re(1-s-w) = 2 - σ₀ > 1` converges, so the movable edge of
`SmoothAFEZetaGeneralEdge` is a convenience rather than a necessity.

## Brick 4f CLOSED — the critical-edge hypothesis is removed at no cost (2026-08-20)

`exists_levinson_window_advance` and everything above it assumed `G(½+iτ) ≠ 0` on the window.  That
hypothesis is now gone, and the constant is unchanged: the zero-free bound `(n+1)π` becomes
`(n+2)π`, one extra half-turn independent of the window.

**Capstone.**  `RHTower/LevinsonWindowUnconditional.lean`:

```text
le_xiOddFiberCount_of_levinson_window_unconditional :
  λ < 0,  ½ < d,  20 ≤ T₁ < T₂,  G♯ ≠ 0 on the bottom, top and right edges only,
  and  (n+2)π ≤ Δθ + I_right + I_bot − I_top − 2π·Σ_{Z} ord   for the zero set Z of G♯ in the
       closed box
  ⟹  n ≤ O(T₂),
xiSingletonFiberCount_ge_of_levinson_window_unconditional :  … ⟹ H₁(T₂) ≥ (3/2)n − N(T₂)/2.
```

Axiom audit: all ten new capstones depend only on `propext, Classical.choice, Quot.sound`.

### Why nothing is lost — the exact accounting

First, a simplification the earlier passes missed.  On the critical line the detector identity gives
`Y·Z = 2 Re[e^{iθ}G]` with `Y ≠ 0`, so `G(½+iτ) = 0` forces `ζ(½+iτ) = 0`, and then
`λ ζ'(½+iτ) = 0` with `λ ≠ 0` forces `ζ'(½+iτ) = 0`.  **`G` vanishes on the critical line exactly at
the multiple zeros of `ζ`**, and there `ord G = ord ζ − 1`.

Write `G♯ = Q·H` with `Q(s) = ∏_j (s − ½ − iτ_j)^{m_j}` the node polynomial of those zeros in the
window and `H` entire, nonvanishing on the whole segment.  Three exact facts:

1. **The left edge does not see `Q`.**  `Re (Q'/Q)(½+iτ) = Σ_j m_j Re(1/(i(τ−τ_j))) = 0`, so
   `∫_{T₁}^{T₂} Re (G♯'/G♯)(½+it) dt = ∫_{T₁}^{T₂} Re (H'/H)(½+it) dt`.
2. **Each node costs exactly `π` on the other three edges.**  With `a = d−½`, `p = τ_j−T₁`,
   `q = T₂−τ_j`, the three integrals are `arctan(q/a)+arctan(p/a)`, `arctan(a/p)` and `−arctan(a/q)`,
   and `arctan u + arctan u⁻¹ = π/2` collapses their combination to `π`
   (`HTGeometry/RectangleBoundaryPole.lean`, `HTGeometry/RectangleNodeProductVariation.lean`).
3. **Removing the nodes lowers the box count by exactly `M = Σ m_j`.**

Hence, with `N_closed` the zero count of `G♯` in the *closed* box,

```text
∫_{T₁}^{T₂} Re (G♯'/G♯)(½+it) dt = (three edges of G♯) − 2π·N_closed + π·M,
```

which is the indented-contour identity of the earlier pass, obtained without any indentation or
limiting argument.

The surplus `π·M` is exactly what the counting step needs.  On the line
`Q(½+iτ) = i^M ∏_j (τ−τ_j)^{m_j}`, so

```text
Z(τ) = P(τ)·ρ(τ)·cos φ(τ),      P(τ) = ∏_j (τ−τ_j)^{m_j},  ρ > 0,  φ continuous,
```

and each sign change of `P` can spoil at most one step of the sign chain — *provided the chain's
nodes avoid the `τ_j`*.  They can: the chain is built from first hitting times of the levels
`c₀ + iπ`, and `φ(g_i) = c₀ + iπ` exactly, so a node lands on a prescribed point only for finitely
many base levels `c₀`; one extra half-turn of phase buys a base level avoiding all of them
(`HTGeometry/PhaseSignChainAvoid.lean`).  The loss is therefore `#{τ_j} ≤ M`, paid for by the `π·M`
surplus.

### New modules

| Module | Content |
|---|---|
| `HTGeometry/PhaseSignChainAvoid.lean` | sign chains at an arbitrary base level `c₀` with `cos c₀ ≠ 0`; `exists_avoiding_level`; `exists_sign_chain_avoiding` (nodes off a prescribed finite set) |
| `HTGeometry/RectangleBoundaryPole.lean` | `simplePole_three_edge_variation`: a simple pole on the open left edge contributes exactly `π` to `(right)+(bottom)−(top)` |
| `HTGeometry/RectangleNodeProductVariation.lean` | `logDeriv_nodeProduct`; `nodeProduct_three_edge_variation` = `π·Σ m_j` |
| `HTGeometry/EntireMultiplicityFactor.lean` | `exists_entire_factor_of_analyticOrderAt_eq`, `exists_entire_multiplicity_factor` (exact prescribed multiplicities, cofactor nonvanishing at every node), plus the order-transfer helpers |
| `RHTower/HardySignSubchainCount.lean` | `le_xiOddFiberCount_of_sign_subchain` (a subfamily of steps suffices); `le_xiOddFiberCount_add_card_of_factored_advance` (the `Z = P·ρ·cos φ` counting interface) |
| `RHTower/LevinsonLineZeroFactorization.lean` | `exists_levinson_line_factorization`: finitely many line zeros, node polynomial divided out, cofactor nonvanishing on the segment |
| `RHTower/LevinsonFactoredPolar.lean` | `exists_factored_polar_hardyZ_advance`: `Z = P·ρ·cos φ` with `Δφ ≥ Δθ + ∫ Re (H'/H)(½+it) dt` |
| `RHTower/LevinsonWindowUnconditional.lean` | the assembly |

The reflected quadratic factor `conj(s−1)²` is what replaces the pole term `(s−1)^{-2}` inside the
polar carrier: its phase velocity is `(¼+τ²)^{-1} > 0`, so the correction again only helps, and the
carrier stays a product of entire objects with no quotient.

### What brick 4 still owes

Nothing structural.  The chain

```text
(three edges of G♯) + Δθ − 2π·N_closed  ⟹  odd fibres  ⟹  H₁
```

is unconditional Lean, with the edge bounds already owned
(`exists_levinson_window_edge_bound`).  The only remaining quantity is `N_closed` — brick 5, the
mollified second moment.

## Brick 4 fully discharged — the whole counting apparatus is now hypothesis-free (2026-08-20)

Two further modules remove the last standing hypotheses.

* `RHTower/LevinsonWindowEdgeUnconditional.lean` —
  **`exists_levinson_window_edge_bound_unconditional`**: the `LevinsonWindowBound` capstone with
  `hleft` deleted and `(n+1)π` replaced by `(n+2)π`.  The `G♯`-versions of the horizontal-edge
  hypotheses are derived from the `G`-versions through `levinsonGEntire_eq_zero_iff`, so only two
  hypotheses survive: `G ≠ 0` on `[½,4]×{T₁}` and on `[½,4]×{T₂}`.

* `RHTower/LevinsonAdmissibleWindow.lean` —
  **`exists_levinson_admissible_window`** and **`exists_levinson_admissible_window_singleton`**:
  those two heights are chosen by `exists_levinsonG_admissible_height'` inside any prescribed pair
  of intervals, so nothing at all is assumed:

  ```text
  ∃ c > 0, ∀ λ < 0 with |λ| ≤ 1, ∀ 20 ≤ a₁ < b₁ ≤ a₂ < b₂,
    ∃ T₁ ∈ (a₁,b₁), ∃ T₂ ∈ (a₂,b₂), ∀ n,
      (n+2)π + π + (T₂−T₁)(6/T₁²) + c log T₁ + c log T₂ + 2π·N_{G♯}([½,4]×[T₁,T₂])
        ≤ θ(T₂) − θ(T₁)
      ⟹  n ≤ O(T₂)   and   H₁(T₂) ≥ (3/2)n − N(T₂)/2.
  ```

Axiom-clean.  `θ(T₂) − θ(T₁)` is the archimedean main term, asymptotically `π·(N(T₂) − N(T₁))`.

**Levinson's method is therefore reduced, in Lean and unconditionally, to a single analytic
quantity: `N_{G♯}([½,4]×[T₁,T₂])`.**  That is brick 5 — Littlewood's lemma applied to `G♯·M` at the
abscissa `σ₀ = ½ − R/log T`, hence the mollified second moment.  Bricks 6 and 7 are the optimization
of the resulting constant.

## Brick 5c--5d structural AFE closure (2026-08-24)

Three axiom-clean modules now close both infinite-series and both finite-tail steps at every point
of the open critical strip, hence at every Levinson abscissa:

* `RHTower/SmoothAFEZetaGeneralDualExpansion.lean` proves
  `riemannZeta_eq_two_tsum_smoothAFE_general`.  The fixed reflected edge `Re w = -1` is expanded
  term by term for every `0 < Re s < 1`; its coefficients decay as
  `(n+1)^(-(2-Re s))` after a polynomial-times-Gaussian domination of the exact shifted `χ` factor.
* `RHTower/SmoothAFEZetaGeneralDualTruncation.lean` proves
  `exists_smoothAFEZetaDualMellinGeneral_sub_head_le`, with explicit reflected remainder
  `K L^(Re s-1)/(1-Re s)`.
* `RHTower/SmoothAFEZetaGeneralTwoHeadTruncation.lean` proves
  `exists_riemannZeta_sub_two_smoothAFE_heads_le`, replacing both contour edges by finite
  Dirichlet polynomials and retaining the direct arbitrary-power tail and reflected `p`-series tail
  separately.

Exact leaf builds pass; `#print axioms` for all new capstones reports only
`propext, Classical.choice, Quot.sound`.

This closes the pointwise structural AFE.  It does **not** yet close brick 5: the constants and
exact dual coefficients still vary with height.  Remaining analytic work is a uniform dyadic
height/conductor estimate for the two finite heads, the corresponding derivative expansion for
`G = ζ + λζ'`, multiplication by the mollifier, and arithmetic main-term evaluation strong enough
to give a proportion strictly above `1/3` (then the sharper PRZZ constants).

## Brick 5e displaced-contour conductor localization (2026-08-24)

Four further axiom-clean modules specialize and localize the structural AFE at Levinson's moving
abscissa `σ₀ = 1/2 - R/log T`:

* `RHTower/LevinsonAbscissaSmoothAFE.lean` proves the exact two-head truncation at every
  `1/2-R/log T+iτ` with `R>0` and `exp(2R)<T`.
* `RHTower/SmoothAFEZetaChiShiftGeneralPowerBound.lean` reflects the denominator of the shifted
  `χ`-ratio and proves the full conductor gain
  `‖χ(s+d+η-iv)/χ(s)‖ ≤ K(1+|v|)^η/max(1,|τ|)^(d+η)`.
* `RHTower/SmoothAFEZetaDisplacedDualContour.lean` proves the finite residue rectangle on
  `Re w ∈ [-(d+η),1]`.
* `RHTower/SmoothAFEZetaDisplacedDualContourLimit.lean` proves integrability of both vertical
  edges, Gaussian extinction of both horizontal edges, the exact infinite residue identity, and
  the conductor-localized capstone
  `‖W_{d,τ}(Y)-1‖ ≤ C(d,η)Y^(d+η)/max(1,|τ|)^(d+η)`.

Each leaf passes direct `lake env lean`, exact-module `lake build`, and a declaration-local axiom
audit reporting only `propext, Classical.choice, Quot.sound`.

This removes the previously missing conductor factor from the displaced dual weight.  Brick 5 is
still open: its final dyadic argument needs control of `C(d,η)` uniform as
`d = R/log T → 0`, the differentiated two-head formula for `ζ'`, mollifier multiplication, and
the arithmetic mean-square evaluation yielding a strict proportion above `1/3`.

## Brick 5f moving-abscissa uniformity (2026-08-24)

`RHTower/SmoothAFEZetaChiUniformMovingRightLine.lean` removes the `d → 0` qualification above.
Compactness controls `χ` uniformly on the bounded-height rectangle
`0 ≤ d ≤ d₀, |t| ≤ 256`; the explicit digamma estimate controls its complement.  The resulting
three capstones give, with constants independent of `d`:

```text
|χ(1/2+d+it)| ≤ K / max(1,|t|)^d,
|χ(s+d+η-iv)/χ(s)| ≤ K′(1+|v|)^η / max(1,|τ|)^(d+η),
|W_{d,τ}(Y)-1| ≤ C Y^(d+η) / max(1,|τ|)^(d+η)
```

simultaneously for every `0<d≤d₀<1/2`.  Direct check, exact leaf build, and declaration-local
axiom audit pass; axioms are only `propext, Classical.choice, Quot.sound`.

Remaining brick-5 work is now the differentiated finite-head formula for `ζ'`, mollifier
multiplication, and arithmetic mean-square evaluation/optimization above `1/3`.

## Brick 5g classical reflected head and derivative inputs (2026-08-24)

Six axiom-clean leaves now replace the exact displaced reflected weight by its classical
Dirichlet head, uniformly across a compact family of moving Levinson lines:

* `RHTower/SmoothAFEZetaChiShiftDisplacedDerivative.lean` proves the exact derivative and
  logarithmic-derivative laws for the displaced shifted `χ`-ratio.
* `RHTower/SmoothAFEZetaDisplacedDualReflection.lean` identifies every general reflected
  coefficient as `-χ(s)n^(s-1)W_{d,τ}(nx)` and isolates its difference from the classical
  coefficient.
* `RHTower/SmoothAFEZetaDisplacedTwoHeadTruncation.lean` gives explicit finite direct and exact
  displaced-weight heads.
* `RHTower/SmoothAFEZetaChiUniformMovingLeftLine.lean` proves
  `|χ(1/2-d+it)| ≤ K max(1,|t|)^d` with one `K` for every `0≤d≤d₀`.
* `RHTower/SmoothAFEZetaDisplacedDualHeadMainApproximation.lean` combines left-line growth with
  conductor localization.  Pointwise errors have exponent `n^(-1/2+η)`, and their first `L`
  terms satisfy the explicit uniform bound
  `C x^(d+η) max(1,|τ|)^(-η) (1 + L^(1/2+η)/(1/2+η))`.
* `RHTower/SmoothAFEZetaDisplacedClassicalTwoHeadTruncation.lean` inserts that estimate into the
  finite AFE, yielding direct and classical reflected Dirichlet heads plus three explicit errors.

Every leaf passes direct `lake env lean`, exact-module `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.

Remaining brick-5 core: differentiate the finite classical two-head identity to obtain a usable
`ζ'` polynomial with controlled remainder, multiply by the mollifier, and prove/evaluate the
arithmetic mean square strongly enough to force a critical-zero proportion strictly above `1/3`.

## Brick 5h differentiated classical AFE closure (2026-08-25)

The differentiated finite-head step is now closed by four axiom-clean leaves:

* `RHTower/SmoothAFEZetaDisplacedDualCoefficientDerivative.lean` differentiates one exact
  reflected coefficient under the fixed left contour, proves its
  `(n+1)^(-(3/2+d))(1+log(n+1))(1+|tau|)^3` envelope, absolute summability, termwise
  differentiation of the full coefficient series, and the exact derivative of
  `smoothAFEZetaDualMellinGeneral`.
* `RHTower/SmoothAFEZetaDisplacedFullDerivativeIdentity.lean` identifies the contour derivative
  with the negative derivative of the conductor-oriented weighted coefficient, differentiates the
  full weighted reflected series, and proves the exact unconditional identity
  `d/dtau zeta(1/2-d+i tau) = direct' + reflected' - residue'` for `0<d<=1/4`.
* `RHTower/SmoothAFEZetaDisplacedReflectedDerivativeTruncation.lean` absorbs the logarithm into
  half of the `d` margin and gives the explicit reflected derivative tail
  `K(1+|tau|)^3 L^(-(1/2+d/2))/(1/2+d/2)`.
* `RHTower/SmoothAFEZetaDisplacedClassicalDerivativeTruncation.lean` combines that tail with the
  direct derivative tail and the finite weighted-to-classical correction.  Its capstone
  `exists_norm_deriv_riemannZeta_mul_I_displaced_sub_finiteClassical_le` is the analytic `zeta'`
  statement, with every direct, reflected, pole, and conductor error retained explicitly.

All four leaves pass direct `lake env lean`, exact-module `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.  They are wired
into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core is now strictly the mollifier product and the twisted arithmetic
mean-square evaluation/optimization yielding a proportion above `1/3`.  No derivative-AFE
structural hypothesis remains.

## Brick 5i deep-edge differentiated AFE (2026-08-25)

The coarse reflected derivative tail has been replaced by an exact fixed-exponent expansion.
Eight axiom-clean leaves close the contour and differentiation chain:

* `RHTower/SmoothAFEZetaArbitraryNegativeEdge.lean` moves the reflected contour to every
  admissible negative depth and proves exact equality with the original `Re w=-1` edge.
* `RHTower/SmoothAFEZetaDisplacedDeepDualExpansion.lean` couples the depth to `4-d`, fixing
  `s+w=-7/2+i(tau+v)` and the reflected coefficient power at `(n+1)^(-9/2)`.
* `RHTower/SmoothAFEZetaDisplacedDeepDualCoefficientDerivative.lean` differentiates each deep
  coefficient in `d`; fixed `s+w` removes both `chi'` and `log(n+1)` from the derivative.
* `RHTower/SmoothAFEZetaDisplacedDeepDualTsumDerivative.lean` proves absolute derivative
  summability, differentiates the deep series termwise, and transfers the derivative back to the
  exact original dual edge.
* `RHTower/SmoothAFEZetaDisplacedDirectDisplacementDerivative.lean` supplies the matching
  logarithmic derivative series for the direct edge with uniform normal convergence.
* `RHTower/SmoothAFEZetaDisplacedPoleResidueDisplacementDerivative.lean` differentiates the
  elementary pole residue and identifies displacement differentiation with `I` times height
  differentiation.
* `RHTower/SmoothAFEZetaDisplacedDeepFullDerivativeIdentity.lean` assembles the exact AFE and
  proves the closed identity
  `deepDisplacementDerivativeSourceField(d,x,tau) = -zeta'(1/2-d+i tau)`.
* `RHTower/SmoothAFEZetaDisplacedDeepDerivativeTruncation.lean` gives a polynomial-height
  coefficient envelope, the explicit reflected derivative tail `O((1+|tau|)^N L^(-7/2))`, and a
  finite `zeta'` approximation whose only other infinite-series error is the direct
  `O(L^(-3/4))` tail.

Each leaf passes direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.  All leaves are
wired into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core: mollifier product, twisted arithmetic mean-square evaluation, and explicit
parameter optimization yielding a critical-zero proportion strictly above `1/3`.

## Brick 5j deep-edge coefficient and height transfer (2026-08-25)

Two further axiom-clean leaves remove the last contour-identification and derivative-orientation
ambiguities:

* `RHTower/SmoothAFEZetaDisplacedDeepCoefficientIdentification.lean` proves coefficientwise
  contour invariance from the coupled deep edge back to the original general reflected
  coefficient.  It supplies the required reciprocal-zeta and closed-strip `chi` bounds,
  differentiability, horizontal decay, and exact coefficient identity.
* `RHTower/SmoothAFEZetaDisplacedDeepHeightDerivative.lean` differentiates the deep contour in
  height, proves a compatible Cauchy-derived polynomial bound for `chi'`, integrates the
  frequency derivative using `HTGeometry/IntegralDerivativeZero.lean`, and establishes the exact
  quarter-turn laws
  `deepDisplacementDerivative = I * deepHeightDerivative` and
  `deepDisplacementDerivative = -I * weightedReflectedHeightDerivative`, coefficientwise and for
  every finite reflected head.

Both leaves pass direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.  They are wired
into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core is strictly mollifier multiplication, twisted arithmetic mean-square
evaluation, and explicit parameter optimization yielding a critical-zero proportion above `1/3`.

## Brick 5k finite detector and mollifier normal form (2026-08-25)

Two axiom-clean leaves now connect the differentiated AFE to the existing Dirichlet mean-value
machinery:

* `RHTower/SmoothAFEZetaDisplacedFiniteDetectorDirichlet.lean` defines the finite approximation to
  `zeta + lambda zeta'`, splits complex powers into amplitude and frequency, and proves its exact
  normal form: one direct Dirichlet polynomial at frequency `-tau`, two reflected Dirichlet
  polynomials at `+tau` with the exact `chi` and `chi'` multipliers, and both pole terms.  After
  multiplication by an arbitrary finite mollifier, the direct same-frequency product is the
  existing Dirichlet convolution, while both opposite-frequency products remain explicit for the
  twisted mean-value theorem.
* `RHTower/SmoothAFEZetaDisplacedFiniteDetectorApproximation.lean` combines the classical value
  AFE and differentiated AFE into a quantitative bound for the actual Levinson detector.  All five
  source constants and every direct, reflected, conductor-localization, logarithmic, and pole
  contribution are retained.

Both leaves pass direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.  They are wired
into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core: strengthen the value truncation to height-uniform constants, apply the
twisted mean-value theorem to the two opposite-frequency products, evaluate the arithmetic main
term, and optimize parameters above `1/3`.

## Brick 5l height-uniform detector truncation (2026-08-25)

Three axiom-clean leaves remove the height-dependent value-tail constants:

* `RHTower/SmoothAFEZetaDisplacedDeepValueTruncation.lean` proves a polynomial-height
  `(n+1)^(-9/2)` envelope for deep reflected value coefficients and the resulting explicit
  `L^(-7/2)` tail.
* `RHTower/SmoothAFEZetaDisplacedUniformValueTruncation.lean` adds the direct `L^-1` tail, proves
  the exact deep-edge value AFE, and transfers its finite truncation to the classical reflected
  head with the conductor-localization error retained.
* `RHTower/SmoothAFEZetaDisplacedUniformFiniteDetectorApproximation.lean` combines that value
  estimate with the differentiated AFE.  Its constants are selected before `lambda`, height, and
  cutoff; the capstone bounds the actual `zeta + lambda zeta'` detector by the exact finite
  Dirichlet normal form uniformly for every height at least `4`.

All three leaves pass direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.  They are wired
into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core is now the twisted mean-square application, arithmetic main-term
evaluation, and explicit optimization above `1/3`.

## Brick 5m mollified twisted mean-value and reduced diagonal (2026-08-25)

Ten axiom-clean leaves now connect the finite AFE detector coefficients to the exact arithmetic
diagonal consumed by the classical mollified-moment calculation:

* `RHTower/SmoothAFEZetaDisplacedDirichletMeanValueBridge.lean` identifies zero-based
  `Sieve.dirPoly` values exactly with positive-natural `HTGeometry.cdpoly` values at `sigma = 0`,
  with the correct height reflection.
* `RHTower/Sieve/MollifiedTwistedMeanValueError.lean` expands two finite mollifier factors into the
  integer-ratio twists, identifies the resulting weighted family with a literal four-polynomial
  correlation, and proves its distance from the exact diagonal `n*k = m*h` is at most
  `4*#s*C*B*(1+log #s)*||u||_1*||v||_1`.
* `RHTower/Sieve/TwistedDiagonalGCDReindex.lean` removes the former coprimality restriction:
  arbitrary positive `h,k` reduce along `g = gcd h k`, and their diagonal is one scale sum on the
  coprime direction `(k/g,h/g)`.
* `RHTower/Sieve/MollifiedTwistedDiagonalIcc.lean` specializes that scale sum to AFE support
  `Icc 1 L`; its exact range is `Icc 1 (L / max(k/g,h/g))`.
* `RHTower/Sieve/MollifiedTwistedMeanValueIcc.lean` packages the AFE-ready capstone: source
  cardinality `L`, geometric product bound `L*M`, exact gcd-reduced main term, and accumulated
  mollifier error in one theorem.
* `RHTower/Sieve/LevinsonLinearMollifier.lean` defines the literal linear mollifier
  `mu(n)n^(-1/2)log(M/n)/log M` in the same positive-natural convention, proves its exact
  Barban--Vehov coefficient identity, and gives the reusable `ell^1 <= 2 sqrt M` bound.
* `RHTower/Sieve/LevinsonLinearMollifiedMeanValue.lean` instantiates the full finite correlation
  theorem with that mollifier and eliminates both coefficient masses from the error term.
* `RHTower/SmoothAFEZetaDisplacedLinearMollifier.lean` reindexes that positive-natural mollifier
  into the detector's zero-based convolution convention and gives the exact mollified detector:
  one direct `dirConv` polynomial, two reflected products, and both pole terms.
* `RHTower/Sieve/DirichletMVTNegativeWindow.lean` transfers the arbitrary-window mean-value
  theorem to the direct head's negative-frequency convention by coefficient conjugation.
* `RHTower/SmoothAFEZetaDisplacedDirectMollifiedMeanSquare.lean` defines the direct convolution
  coefficient and proves its exact window mean square with the coefficient energy and explicit
  Montgomery--Vaughan error retained.

Each leaf passes direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. All leaves are
wired into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core is evaluation of this explicit gcd-reduced arithmetic main term for the
chosen Möbius-polynomial mollifier, control of the chi-weighted cross heads and truncation error in
the dyadic integral, then exact parameter optimization above `1/3`.

## Brick 5n divisor coefficient and critical Barban--Vehov bridge (2026-08-25)

Three further axiom-clean leaves expose the exact arithmetic coefficient consumed by the main-term
calculation:

* `RHTower/Sieve/DirichletConvolutionDivisorReindex.lean` rewrites every zero-based finite
  `Sieve.dirConv` fibre as the standard positive-natural divisor convolution, with both finite
  supports retained exactly.
* `RHTower/SmoothAFEZetaDisplacedDirectMollifiedDivisorCoefficient.lean` specializes that theorem
  to the displaced direct detector and literal linear Levinson mollifier.  It gives both the exact
  supported divisor sum and its fully expanded Möbius--logarithmic form.
* `RHTower/Sieve/LevinsonLinearMollifiedCriticalCoefficient.lean` proves the complementary-divisor
  square-root cancellation, identifies the unsmoothed critical product coefficient exactly as
  `b_M(k)/(log M sqrt k)`, converts its finite square energy to the harmonic Barban--Vehov mean
  square, and applies the existing harmonic Graham bound.

Each leaf passes direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.  All three are
wired into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core is the sharp asymptotic, rather than only the current unconditional upper
bound, for the displaced/log-differentiated and Gaussian-cutoff coefficient energy; the
chi-weighted reflected cross heads and truncation error; and exact parameter optimization above
`1/3`.

## Brick 5o differentiated coefficient and cutoff-transfer algebra (2026-08-25)

Five further axiom-clean leaves isolate the differentiated Barban--Vehov carrier and remove the
Gaussian cutoff through an exact finite convolution estimate:

* `RHTower/Sieve/LevinsonLinearMollifiedCriticalDetectorCoefficient.lean` defines the literal
  critical `zeta + lambda zeta'` product coefficient and proves its exact decomposition into the
  Barban--Vehov term plus the complementary divisor-log moment.
* `RHTower/Sieve/LevinsonLinearMollifiedCriticalDetectorDirConv.lean` identifies every short-head
  finite convolution fibre with that differentiated divisor coefficient.
* `RHTower/SmoothAFEZetaCriticalDetectorArithmeticBridge.lean` proves the exact zero-displacement
  Gaussian-cutoff factorization and a uniform power-rate coefficient error.
* `RHTower/Sieve/DirichletConvolutionLinear.lean` supplies both-sided add, subtract, and scalar
  bilinearity for the finite Dirichlet convolution.
* `RHTower/SmoothAFEZetaCriticalDetectorMollifiedCutoffError.lean` proves that the full mollified
  cutoff error is exactly the convolution of the head error with the linear mollifier, converts
  its finite `ell^1` mass to the positive-natural `Icc` form, and obtains the explicit
  `2 * sqrt M` amplification bound and uniform power-rate consequence.

Each leaf passes direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. All leaves are
wired into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core is the sharp differentiated Barban--Vehov asymptotic (the current Graham
bounds are insufficient), control of the chi-weighted reflected cross heads and truncation error
in the dyadic integral, and the exact PRZZ parameter optimization above `1/3`.

## Brick 5p differentiated short-range energy decomposition (2026-08-25)

Six axiom-clean leaves now expose and bound every elementary arithmetic moment in the literal
linear-mollifier detector coefficient:

* `RHTower/Sieve/LevinsonLinearMollifiedCriticalDetectorEnergy.lean` proves the exact finite
  squared norm in both Barban--Vehov and divisor-log-moment forms;
* `RHTower/Sieve/LevinsonLinearMollifiedCriticalDetectorShortRange.lean` uses the existing exact
  Möbius divisor identities to identify the unit coefficient and every non-unit coefficient as
  `((1-lambda log M)Lambda(k)-lambda(Lambda*Lambda)(k))/(log M sqrt k)`;
* `RHTower/Sieve/LevinsonLinearMollifiedCriticalDetectorEnergyExpansion.lean` expands that square
  into the `Lambda²`, cross, and `(Lambda*Lambda)²` harmonic moments;
* `RHTower/Sieve/VonMangoldtHarmonicSquareAsymptotic.lean` proves the explicit sharp estimate
  `|sum Lambda(k)²/k-(log N)²/2| <= 39 log N+25`;
* `RHTower/Sieve/VonMangoldtSelfConvCrossHarmonicBound.lean` proves the cross moment is supported
  on proper prime powers and is at most `24 log N(1+log N)`;
* `RHTower/Sieve/VonMangoldtSelfConvLogBound.lean` proves the unconditional pointwise bounds
  `(Lambda*Lambda)(n) <= 2(log n)²` and `(Lambda*Lambda)(n)² <= 4(log n)^4`, hence an explicit
  finite `4(log N)^4(1+log N)` envelope for the last moment.

Every leaf passes direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. They are wired
into `RHTower.lean`; no umbrella build was run.

Remaining arithmetic core is the sharp leading asymptotic for
`sum_(k<=N) (Lambda*Lambda)(k)²/k`; the coarse finite envelope is not substituted for that result.
After it, reflected-head cancellation, full PRZZ long-mollifier moment, and exact published
parameter optimization remain.

## Brick 5q sharp self-convolution and short detector energy (2026-08-25)

The remaining short-range arithmetic moment is now closed unconditionally and with its sharp
constant:

* `RHTower/Sieve/VonMangoldtSquareProperPrimePowerCorrection.lean` proves that the difference
  between `(Lambda*Lambda)(k)^2` and twice the square-weight convolution vanishes at primes, is
  supported only on proper prime powers, and has a cutoff-uniform summable bound.
* `QuadraticIncrementConvolution.lean`, `VonMangoldtSquareDyadicProfile.lean`,
  `VonMangoldtSquareDyadicHyperbola.lean`, and
  `VonMangoldtSquareDyadicHyperbolaAsymptotic.lean` prove the exact dyadic hyperbola squeeze and
  the coefficient `1/24`.
* `VonMangoldtSquareHyperbolaAsymptotic.lean` removes the dyadic restriction;
  `VonMangoldtSelfConvHarmonicSquareAsymptotic.lean` absorbs the bounded proper-prime-power
  correction and proves
  `sum_(k<=N) (Lambda*Lambda)(k)^2/k / log(N)^4 -> 1/12`.
* `VonMangoldtMomentRatioAsymptotics.lean` packages all three normalized moment limits, including
  `sum Lambda(k)^2/k / log(N)^2 -> 1/2` and the cross moment divided by `log(N)^3 -> 0`.
* `LevinsonLinearMollifiedCriticalDetectorEnergyAsymptotic.lean` substitutes those limits into the
  exact differentiated Barban--Vehov quadratic form. For `lambda_N=r/log N`, the non-unit energy
  tends to `(1-r)^2/2+r^2/12`, and the full short-range energy tends exactly to
  `1+(1-r)^2/2+r^2/12`.

Every leaf passes direct `lake env lean`, exact-module `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. All leaves are
wired into `RHTower.lean`; no umbrella build was run.

Remaining brick-5 core is no longer arithmetic short-range evaluation. It is the dyadic integral
assembly with the chi-weighted reflected and cross heads, transfer of the finite-cutoff error, then
the explicit Levinson/PRZZ parameter optimization above `1/3`.

## Brick 5r reflected differentiated-head mean value (2026-08-25)

Two axiom-clean leaves now place the actual reflected AFE detector heads into the exact mollified
twisted mean-value substrate without discarding their coefficient structure:

* `RHTower/SmoothAFEZetaDisplacedReflectedMollifiedMeanSquare.lean` proves unit/logarithmic
  envelopes for the literal reflected base and detector coefficients and specializes the existing
  mollified twisted theorem to each head. Both complex correlations are identified with literal
  squared `Sieve.dirPoly`--linear-mollifier norms. Main terms remain the exact gcd-reduced
  diagonals.
* `RHTower/SmoothAFEZetaDisplacedReflectedCombinedMeanSquare.lean` merges the two differentiated
  reflected heads exactly through the frozen complex value of `logDeriv zetaChi`, including an
  exact normal form for the full finite mollified detector. It adds the arbitrary-complex
  conjugate-coefficient bridge needed for positive frequencies, proves the actual displaced-line
  logarithmic coefficient envelope, and establishes the corresponding exact gcd-reduced
  mollified mean square.

Both leaves pass scratch `lake env lean`, exact-module `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. They are wired into
`RHTower.lean`; no umbrella build was run.

Remaining dyadic work is now sharply scoped: control variation of the actual moving
`logDeriv zetaChi` coefficient against this frozen combined carrier, price the direct/reflected
cross term without losing its oscillation, transfer the Gaussian and pole remainders, and evaluate
the full long-range gcd-reduced diagonal before parameter optimization above `1/3`.

## Brick 5s moving reflected-coefficient freezing (2026-08-25)

Two axiom-clean leaves now control the actual height dependence of the differentiated reflected
coefficient and transfer that control to its mollified mean square:

* `RHTower/SmoothAFEZetaChiDisplacedHeightVariationBound.lean` proves an unconditional Lipschitz
  estimate for `logDeriv zetaChi` on the displaced critical line from the existing digamma
  derivative bounds. Its dyadic form is
  `norm (q(t)-q(u)) <= (8+4*pi)(1+H)/T` whenever `u >= T`, `T >= 4`, and
  `abs (t-u) <= H <= T/2`.
* `RHTower/SmoothAFEZetaDisplacedReflectedCombinedFreezingMeanSquare.lean` identifies the moving
  combined reflected head minus its coefficient frozen at `u` exactly as
  `lambda*(q(t)-q(u))` times the reflected base head and mollifier. It proves continuity, converts
  the exact complex base-head mean theorem into a positive real energy bound, and integrates the
  dyadic freezing error against the same exact gcd-reduced diagonal plus its explicit mean-value
  error.

Both leaves pass exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. They are wired into `RHTower.lean`; no umbrella build
was run.

Remaining dyadic work is the direct/reflected cross term with its oscillatory chi factor, the
variation and magnitude of the chi weight itself, Gaussian and pole remainder transfer, and the
full long-range gcd-reduced diagonal and parameter optimization above `1/3`.

## Brick 5t actual chi-weighted moving reflected energy (2026-08-25)

Three axiom-clean leaves now close the same-head mean-square assembly for the literal reflected
part of the differentiated smooth AFE:

* `RHTower/SmoothAFEZetaDisplacedReflectedCombinedEnergyUpper.lean` converts the exact frozen
  complex mean theorem into a positive real energy upper bound, retaining the full gcd-reduced
  combined diagonal and explicit error.
* `RHTower/SmoothAFEZetaDisplacedReflectedChiWeightedMeanSquare.lean` reuses the existing uniform
  moving-left-line chi theorem to prove one existential dyadic conductor-growth constant for every
  `0 < d <= d0`, then transfers the frozen combined energy through the literal chi factor.
* `RHTower/SmoothAFEZetaDisplacedReflectedMovingMeanSquare.lean` proves the exact moving carrier
  decomposition into the frozen `logDeriv zetaChi` carrier plus its freezing error. It integrates
  the literal chi-weighted moving head on a short dyadic subwindow against the sum of the exact
  frozen combined diagonal and the exact reflected-base diagonal pricing the freezing error.

Every leaf passes exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. They are wired into `RHTower.lean`; no umbrella build
was run.

Same-head reflected energy is no longer an open analytic interface. Remaining dyadic gates are the
oscillatory direct/reflected cross term, Gaussian and pole remainder transfer, and evaluation of the
full long-range gcd-reduced diagonal followed by parameter optimization above `1/3`.

## Brick 5u Gaussian pole-remainder transfer (2026-08-25)

Two axiom-clean leaves now remove both elementary pole terms from the differentiated finite AFE
frontier:

* `RHTower/SmoothAFEZetaDisplacedPoleDecay.lean` proves the missing displaced-line Gaussian bound
  for `smoothAFEZetaShiftedPoleResidue`, the pointwise `2*sqrt M` envelope for the literal linear
  mollifier, and a single exact package for the shifted residue plus height-derivative residue. Its
  norm is bounded by an explicit coefficient times `exp(-t^2)`.
* `RHTower/SmoothAFEZetaDisplacedPoleRemainderMeanSquare.lean` proves continuity of the displaced
  residue, its closed-form height derivative, and the combined mollified remainder. It integrates
  the literal remainder over every positive interval above `T`, obtaining the interval length times
  the square of the explicit `exp(-T^2)` envelope.

Both leaves pass exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. They are wired into `RHTower.lean`; no umbrella build
was run.

Pole and Gaussian remainders are no longer open. Remaining differentiated-AFE analytic gate is the
phase-faithful direct/reflected cross term. Arithmetic gates remain the full long-range gcd-reduced
diagonal and published parameter optimization above `1/3`.

## Brick 5v exact full-detector energy assembly (2026-08-25)

`RHTower/SmoothAFEZetaDisplacedDetectorEnergyDecomposition.lean` now gives the exact global
bookkeeping layer for the finite mollified differentiated AFE:

* `smoothAFEZetaDisplacedMollifiedDirectHead` is the literal convolution polynomial from the
  direct detector and linear mollifier;
* `smoothAFEZetaDisplacedMollifiedPrincipalHead` is direct plus the actual moving chi-weighted
  reflected head;
* `smoothAFEZetaDisplacedFiniteClassicalDetector_mul_mollifier_eq_principal_add_pole` identifies the
  full finite detector exactly with that principal part plus the already bounded Gaussian pole
  remainder;
* pointwise and integrated squared-energy identities preserve the direct/reflected mixed term as
  the literal integral of
  `re (conj direct * reflected)`. No triangle inequality or phase erasure is applied to it.

The leaf passes exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. It is wired into `RHTower.lean`; no umbrella build was
run.

This removes all assembly ambiguity. The differentiated-AFE analytic frontier is exactly the
stationary direct/reflected cross integral. Arithmetic frontier remains evaluation of the full
long-range gcd-reduced diagonal and parameter optimization above `1/3`.

## Brick 5w exact zero-twist product-fibre energy (2026-08-25)

`RHTower/Sieve/MollifiedTwistedDiagonalProductEnergy.lean` identifies the full zero-twist
four-index mollified diagonal with its exact multiplicative product-fibre Gram energy. The proof
first matches the twisted diagonal to the literal product-collision sum, then partitions the
Cartesian coefficient support by the product map. In the self-paired case it proves the exact
initial-range identity

`mollifiedTwistedDiagonalIcc a a u u L M 0 = sum_r ofReal (normSq c_r)`,

where `c_r` is the complete head/mollifier convolution coefficient on product fibre `r`. Thus the
long-range arithmetic main term is now a manifest finite square energy, with no lost cross terms
and no asymptotic replacement.

The leaf passes exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. It is wired into `RHTower.lean`; no umbrella build was
run.

Remaining arithmetic task is a sharp short/tail analysis of these exact product-fibre coefficients
for the Levinson detector and linear mollifier. Analytic frontier remains the stationary
direct/reflected cross integral, followed by optimization above `1/3`.

## Brick 5x full finite-convolution diagonal and exact long tail (2026-08-25)

Three axiom-clean leaves now put the entire zero-twist arithmetic diagonal into the coefficient
space used by the Levinson programme:

* `RHTower/Sieve/MollifiedTwistedDiagonalDirConvEnergy.lean` proves that each positive-natural
  product-fibre coefficient is exactly the corresponding zero-based `dirConv` coefficient and that
  the whole Icc diagonal is the sum of its squared moduli over `Fin (L*M)`;
* `RHTower/SmoothAFEZetaCriticalDetectorDiagonalEnergy.lean` specializes this identity to the
  literal finite critical detector and linear Levinson mollifier;
* `RHTower/SmoothAFEZetaCriticalDetectorLongRangeSplit.lean` splits the full product energy exactly
  at index `L`. The short summand is definitionally the already-evaluated Barban--Vehov detector
  energy, while `levinsonCriticalDetectorLongEnergy` is the explicit sum of squared finite
  convolution coefficients for `L < r+1`; it is proved nonnegative.

Every leaf passes exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. They are wired into `RHTower.lean`; no umbrella build
was run.

There is no longer any ambiguity between the gcd-reduced four-index diagonal, multiplicative
product fibres, finite Dirichlet convolution, and the short arithmetic model. Remaining arithmetic
gate is now exactly a sharp asymptotic or upper bound for `levinsonCriticalDetectorLongEnergy` in
the AFE scaling regime. Analytic gate remains the stationary direct/reflected cross integral.

## Brick 5y critical-line stationary mixed cross (2026-08-25)

Three axiom-clean leaves now close the phase bookkeeping and exact finite-polynomial reduction at
zero displacement:

* `RHTower/ZetaChiCriticalLineOscillatoryIntegral.lean` identifies the critical-line chi factor
  with the Hardy-theta phase and applies the proved negative-curvature van der Corput estimate to
  every linear twist, including stationary frequencies;
* `RHTower/ZetaChiCriticalDirichletCross.lean` expands an arbitrary finite chi-twisted
  positive/negative Dirichlet cross and proves an explicit coefficient-`ell^1` integral bound;
* `RHTower/SmoothAFEZetaCriticalFrozenCross.lean` specializes that bound exactly to the conjugated
  direct mollified smooth-AFE head times the frozen reflected critical head, identifies its literal
  convolution coefficient, and factors its `ell^1` mass through both head arrays and the linear
  mollifier.

Every leaf passes exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. They are wired into `RHTower.lean`; no umbrella build
was run.

Remaining cross-term gate is displaced-line transfer together with coefficient summation sharp
enough for the Levinson scaling; the current `ell^1` bound deliberately does not claim that
asymptotic. Arithmetic gate remains the sharp long-tail estimate for
`levinsonCriticalDetectorLongEnergy`, followed by published parameter optimization above `1/3`.

## Brick 5z displaced stationary cross transfer (2026-08-25)

Four axiom-clean leaves now carry stationary cancellation from the critical line to every moving
Levinson displacement `0 < d <= d₀ <= 1/4`:

* `RHTower/OscillatoryIntegralComplexAmplitude.lean` proves complex Abel summation against any
  bounded anchored oscillatory primitive;
* `RHTower/ZetaChiDisplacedCriticalRatioOscillatoryIntegral.lean` differentiates the exact ratio
  `chi(1/2-d+it)/chi(1/2+it)`, proves horizontal logarithmic-slope variation `O(1/t)` from the
  existing digamma bounds, and derives a uniform dyadic stationary-frequency estimate of size
  `T^(d+1/2)`;
* `RHTower/ZetaChiDisplacedDirichletCross.lean` sums all finite positive/negative Dirichlet
  frequencies without a nonstationary-frequency assumption;
* `RHTower/SmoothAFEZetaDisplacedFrozenCross.lean` identifies the literal conjugated displaced
  direct mollified head times the frozen chi-weighted reflected head with that finite cross and
  proves its explicit factorized `ell^1` bound.

Every leaf passes exact-module `lake build` and declaration-local `#print axioms`; dependencies are
only `propext, Classical.choice, Quot.sound`. They are wired into `RHTower.lean`; no umbrella build
was run.

Stationary phase and displaced-line transfer are no longer open interfaces. Remaining cross-term
task is coefficient summation sharp enough for Levinson scaling; the proved `ell^1` estimate is an
exact unconditional carrier but is not claimed to be asymptotically sharp. Arithmetic gate remains
the long-tail estimate for `levinsonCriticalDetectorLongEnergy`, followed by published parameter
optimization above `1/3`.

## Brick 5aa actual moving cross on short windows (2026-08-25)

Five axiom-clean leaves now transfer the frozen displaced cross estimate to the literal moving
`logDeriv zetaChi` reflected head on every short dyadic subwindow:

* `RHTower/ZetaChiDisplacedSubintervalOscillatoryIntegral.lean` proves the displaced stationary
  primitive estimate on arbitrary subintervals `[a,b]` of `[T,2T]` with the same
  `T^(d+1/2)` scale;
* `RHTower/ZetaChiDisplacedDirichletCrossSubinterval.lean` expands the finite positive/negative
  cross on such subintervals and retains the exact factorized coefficient mass;
* `RHTower/SmoothAFEZetaDisplacedFrozenCrossSubinterval.lean` specializes that estimate to the
  literal differentiated direct head and frozen chi-weighted reflected head;
* `RHTower/SmoothAFEZetaDisplacedDirectMollifiedEnergyUpper.lean` converts the exact direct
  mean-value identity into the positive energy upper bound needed by Cauchy--Schwarz;
* `RHTower/SmoothAFEZetaDisplacedMovingCrossFreezing.lean` proves the exact pointwise and
  integrated moving-equals-frozen-plus-error identities, bounds the chi-weighted freezing-error
  energy from the existing dyadic chi envelope and freezing mean square, and concludes that the
  actual moving cross is at most the phase-faithful frozen cross plus an explicit short-window
  square-root error.

All five leaves pass direct `lake env lean`, exact leaf `lake build`, and one batched
declaration-local `#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`.
They are wired into `RHTower.lean`; no umbrella build was run.

Moving-coefficient variation and short-window transfer are no longer open interfaces. Remaining
cross-term gate is a coefficient summation estimate sharp enough for Levinson scaling; the exact
factorized `ell^1` carrier is not silently substituted for it. Arithmetic gate remains the sharp
upper/asymptotic estimate for `levinsonCriticalDetectorLongEnergy`, followed by published
parameter optimization above `1/3` and, for the card's exact decimal, the full PRZZ inputs.

## Brick 5ab exact long-tail decomposition and unconditional coarse caps (2026-08-25)

Four axiom-clean leaves now expose the arithmetic long range without hiding cancellation behind a
divisor estimate:

* `RHTower/SmoothAFEZetaCriticalDetectorLongEnergyDivisorBound.lean` gives an unconditional
  arbitrarily-small-power divisor-fibre cap and explicit logarithmic factor energies;
* `RHTower/SmoothAFEZetaCriticalDetectorLongCoefficientDecomposition.lean` proves that every
  finite product coefficient is the full differentiated Barban--Vehov coefficient minus the exact
  omitted-head divisor tail. It reindexes both long energies onto `(L,L*M]`, gives the full tail's
  literal arithmetic quadratic form, and reduces the exact detector tail to twice the full energy
  plus twice the omitted-boundary energy;
* `RHTower/Sieve/DirichletYoung.lean` proves finite multiplicative Young
  `ell^2 convolved with ell^1 to ell^2` for the corpus's product-index convolution, with no divisor
  factor;
* `RHTower/SmoothAFEZetaCriticalDetectorLongEnergyYoungBound.lean` specializes Young to the exact
  detector and proves the complementary explicit bound `longEnergy <= 4*M*headEnergy`.

All four leaves pass scratch/direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. They are wired into
`RHTower.lean`; no umbrella build was run.

These bounds are unconditional but deliberately coarse: neither the small-power divisor cap nor
the polynomial Young cap is the sharp `o(1)` long-tail evaluation required in Levinson scaling.
The exact remaining arithmetic cores are now the displayed full differentiated Barban--Vehov
quadratic form and the omitted-head boundary energy. Cross-term coefficient summation and published
parameter optimization remain open as before.

## Brick 5ac exact long-moment carrier and linear optimization certificate (2026-08-25)

Two axiom-clean leaves now close the remaining algebraic and scalar layers around the analytic
mean-value input:

* `RHTower/SmoothAFEZetaCriticalDetectorFullLongMomentExpansion.lean` names the base, mixed, and
  differentiated harmonic Barban--Vehov moments on the exact range `(L,L*M]` and proves that the
  full differentiated long energy is their literal quadratic polynomial in the detector parameter;
* `RHTower/LevinsonLinearOptimization.lean` evaluates Young's linear choice
  `P(x)=x`, `Q(x)=1-x`, `R=13/10`, `theta=1/2` by exact antiderivatives and rational Taylor bounds,
  proving unconditionally
  `1 - log(levinsonLinearOptimizationConstant)/(13/10) > 1/3`.

Both leaves pass direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. They are wired into
`RHTower.lean`; no umbrella build was run.

Parameter optimization is therefore no longer an open scalar task for the cheaper odd-fibre
closure. The remaining classical Levinson gate is analytic: prove the mollified mean-value
asymptotic matching this constant, including sharp full/omitted long-tail evaluation and sharp
mixed-cross coefficient summation. The card's exact decimal still additionally requires the full
PRZZ proportion inputs.

## Brick 5ad admissible interior parameter and logarithmic Möbius normalization (2026-08-25)

Seven axiom-clean leaves now close the endpoint-continuity and fixed-modulus arithmetic layers:

* `RHTower/LevinsonLinearOptimizationInterior.lean` transfers the exact endpoint computation to
  some strict `0 < theta < 1/2` while preserving proportion `> 1/3`;
* `RHTower/LevinsonLinearAdmissibleParameter.lean` selects a fixed unconditional admissible
  parameter and exports its proportion certificate;
* `RHTower/Sieve/MoebiusHarmonicTailIdentity.lean`,
  `HTGeometry/ReciprocalLogPowerTail.lean`, and
  `RHTower/Sieve/MoebiusHarmonicLogRate.lean` provide the Abel identity and logarithmic decay needed
  at the zeta pole;
* `RHTower/Sieve/MoebiusLogarithmicNormalization.lean` proves
  `sum_{d <= N} mu(d)/d log(N/d) -> 1` by identifying the boundary derivative of reciprocal zeta;
* `RHTower/Sieve/CoprimeLogMoebiusOneLimit.lean` and
  `RHTower/Sieve/CoprimeLogMoebiusLimit.lean` transfer this to real cutoffs, prove a generic
  divided-argument contraction theorem, and establish for every fixed squarefree modulus `e`
  that `T_e(Y) -> e/phi(e)`.

Every leaf passes direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. Leaves are wired
into their umbrellas; no umbrella build was run.

The admissible strict-theta scalar and fixed-modulus Graham normalization are therefore closed.
This does not yet give the modulus-uniform Barban--Vehov quadratic asymptotic when the modulus grows
with the mollifier length. Sharp full/omitted long-tail evaluation and mixed-cross coefficient
summation remain the analytic Levinson gate; the exact card decimal still additionally requires
both PRZZ proportion providers.

## Brick 5ae squarefree--totient mean and sharp Selberg lower half (2026-08-26)

Four axiom-clean leaves close the arithmetic residue and lower-variational side of Graham's
quadratic form:

* `RHTower/SummableDivisorHarmonicMean.lean` proves a reusable dominated divisor-harmonic mean
  from plain absolute summability of the reciprocal residue;
* `RHTower/Sieve/SquarefreeTotientResidueKernel.lean` constructs the Möbius inverse of
  `n*mu(n)^2/phi(n)`, proves its prime-square support, absolute summability after reciprocal
  weighting, and exact Euler mass `1`;
* `RHTower/Sieve/SquarefreeTotientLogMean.lean` deduces the unconditional asymptotic
  `sum_{n<=N} mu(n)^2/phi(n) / log N -> 1`;
* `RHTower/Sieve/SelbergDiagonalLowerAsymptotic.lean` proves the finite Möbius inversion constraint,
  the weighted-Cauchy bound
  `log(X)^2 / sum_{e<=X} mu(e)^2/phi(e) <= D_X`, and hence the sharp epsilon-form lower law
  `D_X/log X >= 1-epsilon` eventually.

Each leaf passes direct `lake env lean`, exact leaf `lake build`, and declaration-local
`#print axioms`; dependencies are only `propext, Classical.choice, Quot.sound`. Leaves are wired
into `RHTower.lean`; no umbrella build was run.

Graham's lower half and its leading constant are no longer open. Remaining arithmetic core is the
matching sharp upper law for the specific linear Barban--Vehov weight, uniformly across growing
moduli; existing `GrahamMeanSquare` and `HarmonicWeightedGrahamMeanSquare` give unconditional but
coarse upper bounds. Full/omitted differentiated long-tail evaluation, mixed-cross summation, and
published PRZZ providers remain open.

## Brick 5af — general-order Selberg log-monomials CLOSED, and a structural correction to the
## direct/dual/cross route (2026-08-29)

### What landed

Three axiom-clean leaves replace the whole ad-hoc order-by-order ladder of this lane:

* `RHTower/Sieve/HarmonicLogWindowGeneralMoment.lean` — the Abel weight `(log t)^m / t` is antitone
  beyond `4^m` (`antitoneOn_logPowDivId_pow_four`, using only `log 4 > 1`), hence
  **`exists_abs_harmonicLogWindowMoment_zero_sub_primitive_le`**
  (`|∑_{d≤N}(log d)^m/d − (log(N+1))^{m+1}/(m+1)| ≤ C_m` for `N ≥ 4^m`) and
  **`tendsto_harmonicLogWindowMoment_natDiv_div_log_pow`**
  (`M_m(N/c)/(log N)^{m+1} → 1/(m+1)`) at **every** order `m`.  This supersedes the separate
  `m = 0,1,2,3` files (`HarmonicLogWindowLowerMoments`, `HarmonicLogWindowMoments`,
  `HarmonicLogWindowThirdMoment`, `HarmonicLogMomentAsymptotics`).
* `RHTower/Sieve/SelbergLogPowerHarmonicGeneral.lean` — the alternating binomial identity
  `∑_{s≤m}(−1)^s C(m,s)/(s+1) = 1/(m+1)` (`sum_choose_alternating_div_succ`), the one-shift
  harmonic power sum `selbergShiftedLogPowerHarmonic` with
  **`tendsto_selbergShiftedLogPowerHarmonic`** (`→ 1/(m+1)`), and the capstone
  **`tendsto_selbergLogPowerHarmonicMain_div_log_pow`**:
  `selbergLogPowerHarmonicMain q r a b N / (log N)^{q+r+1} → (q+1)(r+1)/(q+r+1)` for every `(q,r)`
  and every pair of dilations.
* `RHTower/Sieve/SelbergLogPowerGeneralAsymptotic.lean` —
  `tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow`,
  `tendsto_selbergCorrectionScaledLogPowerTerm`,
  `tendsto_tsum_selbergCorrectionScaledLogPowerTerm`, and the capstone

  ```text
  tendsto_selbergOriginalLogMonomial_div_log_pow (0 < i) (0 < j) :
     selbergOriginalLogMonomial i j N / (log N)^{i+j-1}  →  i·j/(i+j-1).
  ```

  **Graham's Selberg diagonal at every pair of positive logarithmic powers.**  The previously
  available instances were only `(1,1)`, `(1,2)`, `(2,2)`, `(1,4)`, `(2,3)`.

All three pass `lake env lean` and exact leaf `lake build` with **no warnings**.

### The structural correction: the min-log family is a detour, and the direct/dual/cross split is divergent

While scoping the min-log family `selbergOriginalMinLogMonomial i j k`
(`∑ c(m,n) A^i B^j min(A,B)^k`, `A = log(N/m)`) that the included/omitted long-energy boundary
needs, the following came out — and it invalidates the assumption that the long tail is a small
correction.

**(1) The min-log monomials are one order larger than the pure-log ones.**  Write
`G(Y) := ∑_{q,r ≤ Y} μ(q)μ(r)(q,r)/(qr)`.  Selberg's diagonalization
`(q,r) = ∑_{d | (q,r)} φ(d)` gives `G(Y) = ∑_{d ≤ Y} φ(d)·(∑_{q ≤ Y, d | q} μ(q)/q)² ≥ 0`, and the
single dyadic block `d ∈ (Y/2, Y]` already contributes `∑ μ²(d)φ(d)/d² ≍ 1`.  So

```text
G(Y) ≍ 1        (bounded away from 0, not o(1)).
```

Layer-caking `min(A,B) = ∫_0^∞ 1_{t<A} 1_{t<B} dt` and writing `Y = M e^{-t}`, `A = t + log(Y/q)`:

```text
S(1,1,1) = ∫_0^ℓ [ t²·G(Me^{-t}) + 2t·H(Me^{-t}) + I(Me^{-t}) ] dt,   ℓ = log M,
```

with `I(Y) ~ log Y` (Graham) and `|H| ≤ √(G·I) ≪ √(log Y)` by Cauchy–Schwarz.  Hence
**`S(1,1,1) ≍ ℓ³`**, whereas every pure-log monomial of the same total degree is `≍ ℓ²`.
The general shape is `S(i,j,κ) ≍ ℓ^{i+j+κ}` for `κ ≥ 1`, one power **above** the pure-log law
`S(i,j,0) ~ (ij/(i+j−1))ℓ^{i+j−1}`, and the leading constant is an arithmetic integral of Möbius
partial sums (`∫_0^∞ M(e^u)² du`-type), not a rational number.

**(2) Consequence: the corpus's long energy dominates its short energy.**  With the linear
mollifier `w(q) = μ(q)log(M/q)/ℓ`, the included base boundary is
`ℓ·S(1,1,0) − S(2,1,0) − S(1,2,0) + S(1,1,1)`, so after the `ℓ²` normalization

```text
short energy  ≍ 1,        long energy  ≍ ℓ  →  ∞.
```

So `levinsonCriticalDetectorLongEnergy` is **not** a small correction; it is the dominant term of
the direct-head diagonal.

**(3) Why that is not a contradiction — and what it forces.**  For the classical twisted second
moment (Balasubramanian–Conrey–Heath-Brown)

```text
∫_0^T ζ(½+it)ζ(½−it)(h/k)^{-it} dt = T·((h,k)/√(hk))·( log(T(h,k)²/(2πhk)) + 2γ − 1 ) + …,
```

the per-pair weight is `log T − log[h,k] + log(h,k)`.  The **direct** AFE head alone gives, for the
same pair, the weight `log x − log[h,k] + log min(h,k)`, and the reflected head gives
`log y − log[h,k] + log min(h,k)`.  Therefore

```text
(direct) + (dual) − (full)  =  2·log min(h,k) − log(hk)  =  −log( max(h,k)/min(h,k) ),
```

i.e. **the direct/reflected cross term carries the exact weight `+log(max/min) = |A − B|`**, and
`|A−B| = A + B − 2·min(A,B)`.  The divergent `min(A,B)` mass of the direct and reflected diagonals
is cancelled, exactly, by the cross term.

**This is a no-go for the current sub-route.**  Bricks 5y, 5z, 5aa produce `ℓ¹`-coefficient
*upper bounds* for the cross integral.  An upper bound can never cancel a divergence: the cross
must be evaluated with its leading term and its sign, to the same order `ℓ` as the long energy.
Any amount of further sharpening of `levinsonCriticalDetectorLongEnergy` alone is wasted, because
the quantity it belongs to is not convergent on its own.

### Corrected arithmetic plan for brick 5

Evaluate the *combination*, not the three pieces.  Concretely, prove the twisted second moment with
its classical main term and feed the result into the Selberg diagonal.  The arithmetic layer that
this needs is exactly two families, both of *normal* order:

| family | statement | state |
|---|---|---|
| pure-log | `∑_{m,n≤N} c(m,n)·log(N/m)^i log(N/n)^j  ~  (ij/(i+j−1))·(log N)^{i+j−1}` | **CLOSED 2026-08-29** (`tendsto_selbergOriginalLogMonomial_div_log_pow`) |
| gcd-log | `∑_{m,n≤N} c(m,n)·log(N/m)^i log(N/n)^j·log(m,n)  ~  (ij/((i+j−1)(i+j)))·(log N)^{i+j}` | **OPEN — next target** |

The gcd-log constant is derived by peeling one prime from the gcd,
`log(m,n) = ∑_{p|m, p|n} log p`, rescaling to `N/p`, and using Mertens
`∑_{p≤x} log p / p ~ log x`; the inner Selberg form contributes
`ij·(log(N/p))^{i+j−1}/(i+j−1)`, and `∫_0^L ij(L−u)^{i+j−1}/(i+j−1) du = ij·L^{i+j}/((i+j−1)(i+j))`.

**Verification against Young's theorem.**  With `P(x)=x`, `Q=1`, `R=0` the full weight
`log T − 2ℓ + A + B + 2log(m,n) + 2γ − 1` gives

```text
(log T − 2ℓ)/ℓ + (S(2,1,0)+S(1,2,0))/ℓ² + 2·(ℓ²/2)/ℓ² = (1/θ − 2) + 2 + 1 = 1 + 1/θ,
```

which is exactly `c(P,Q,R,θ) = 1 + (1/θ)∫₀¹∫₀¹ (d/dx[e^{Rx}P(x+u)Q(v+x)]|₀)² du dv` at those
parameters.  The two families above therefore suffice for the whole mollified main term.

### What this means for the min-log modules already in the tree

`SelbergMinLog*`, `DifferentiatedBarbanVehov*Included*`/`*Omitted*` and
`SmoothAFEZetaCriticalDetectorLong*` remain correct theorems; they are simply not on the shortest
path any more, and their target (a sharp evaluation of `levinsonCriticalDetectorLongEnergy` alone)
cannot close brick 5 by itself.  They stay as corpus assets.

## Brick 5ag — the gcd-logarithmic Selberg family: dilations, diagonal weight, harmonic main
## (2026-08-29)

Four further axiom-clean leaves build the corrected route's second family.  Everything below passes
direct `lake env lean`, exact leaf `lake build` with **no warnings**, and a declaration-local
`#print axioms` reporting only `propext, Classical.choice, Quot.sound`; all are wired into
`RHTower.lean` (no umbrella build was run).

* `RHTower/Sieve/SelbergDilatedLogMonomial.lean`
  - **`exists_abs_selbergPrincipalScaledLogPowerModel_le`** — one envelope
    `|P(q+1,r+1,a,b,N)| ≤ M·(log N)^{q+r+1}` valid at **every** pair of dilations (extracted from
    the inline estimate that `SelbergLogPowerCorrectionAsymptotics` previously used only for the
    correction indices);
  - `selbergOriginalDilatedLogMonomial i j a b N` =
    `∑_{m ≤ N/a, n ≤ N/b} c(m,n)·log(N/(am))^i·log(N/(bn))^j`, with
    **`selbergOriginalDilatedLogMonomial_eq_correction_scaled`**, the exact Euler-correction
    decomposition `∑_{d,e} corr(d,e)·P(i,j,ad,be,N)`.

* `RHTower/Sieve/SelbergDilatedLogMonomialAsymptotic.lean`
  - **`tendsto_selbergOriginalDilatedLogMonomial_div_log_pow`** — every fixed pair of dilations has
    the *undilated* leading coefficient `(q+1)(r+1)/(q+r+1)`;
  - **`exists_abs_selbergOriginalDilatedLogMonomial_le`** — one envelope for the whole dilated
    family, uniform in `(a,b)`.  (This is what any prime-peeling comparison needs.)

* `RHTower/Sieve/SelbergGcdLogHarmonicMain.lean`
  - `selbergGcdLogHarmonicMain q r a b N` = `∑_{d ≤ N/max(a,b)} (q+1)(r+1)·log d·A_d^q·B_d^r / d`;
  - **`tendsto_selbergGcdLogHarmonicMain_div_log_pow`** —

    ```text
    selbergGcdLogHarmonicMain q r a b N / (log N)^{q+r+2}  →  (q+1)(r+1)/((q+r+1)(q+r+2)),
    ```

    i.e. with `i = q+1`, `j = r+1` exactly the predicted `i·j/((i+j−1)(i+j))`.  The proof is the
    identity `log d = (log N − log a) − log(N/(a d))`, which turns the model into the two ordinary
    harmonic mains of brick 5af at consecutive degrees.

* `RHTower/Sieve/SelbergGcdLogPrincipalCollapse.lean`
  - `selbergDiagonalLogReciprocalCoeff` (`log d / d` on the diagonal — the `s`-derivative at `s = 1`
    of the diagonal Euler factor `1/(1 − p^{s−1}XY/p)`), its double-sum collapse, the gcd-log
    principal coefficient `𝒫^{log} = diag(log d/d) ∗ (μ/·)⊗(μ/·)`, and
  - **`selbergGcdLogPrincipalCoeff_weighted_logPower_eq_scaledModel`** — the exact rectangular
    collapse `∑_{r,s} 𝒫^{log}(r,s)·W = ∑_{d ≤ N/max(a,b)} (log d/d)·K_i(N/(ad))·K_j(N/(bd))`,
    mirroring the ordinary principal collapse.

### What the gcd-log family still owes

The Leibniz identity for the two-parameter family `c_s(m,n) = μ(m)μ(n)(m,n)^s/(mn)` is

```text
c·log(m,n)  =  corr ∗ 𝒫^{log}  +  corr^{log} ∗ 𝒫,      corr^{log} := ∂_s corr_s |_{s=1},
```

with `corr_s = c_s ∗ mp^{-1} ∗ diag_s^{-1}` and `diag_s^{-1}(m,n) = μ(m)m^{s-2}·[m = n]`, so
`corr^{log}` is a concrete bivariate function.  Its local factor is

```text
(log p / p²)·XY(X + Y − 2XY)/((1−X/p)(1−Y/p)),
```

so `‖corr^{log}‖₁ ≪ ∑_p log p / p² < ∞`.  Only the **summability** is needed (not the mass): the
second term is then `O((log N)^{i+j−1}) = o((log N)^{i+j})` by the dilated envelope above.  That
summability proof is the analogue of the existing `SelbergEulerCorrectionCoefficient*` chain and is
the next target, together with the harmonic replacement for `𝒫^{log}`.

**Why the prime-peel alternative was rejected.**  Peeling `log(m,n) = ∑_{d|(m,n)} Λ(d)` needs the
`p`-coprime Selberg form uniformly in `p`.  The two-dimensional recursion
`Ŝ^{(p)}(a,b) = Ŝ(a,b) + (1/p)[Ŝ^{(p)}(ap,b) + Ŝ^{(p)}(a,bp) − Ŝ^{(p)}(ap,bp)]` contracts only for
`p > 3`, and no weighted sup-norm fixes `p = 2` (the operator's triangle bound is `3/p`, and the
true `ℓ¹` norm of the local inverse needs the analyticity of `1/(1 − (X+Y−XY)/p)` on the closed
polydisc — true, but not elementary).  The one-dimensional kernel recursion
`K^{(p)}_{q+1}(Y) = K_{q+1}(Y) + (1/p)K^{(p)}_{q+1}(Y/p)` *does* contract for every `p ≥ 2`, which
is why the `diag(log d/d)` route is the right one: it keeps the whole `p`-dependence inside a
one-dimensional kernel.

## Brick 5ah — gcd-logarithmic harmonic replacement closed (2026-08-29)

`RHTower/Sieve/SelbergGcdLogHarmonicReplacement.lean` (axiom-clean, no warnings, wired):

* **`exists_kernelProduct_close`** — the reusable pointwise input, isolated for the first time:
  for every `δ > 0` there is `K ≥ 2` such that for all cutoffs `Y, Z ≥ K`

  ```text
  |K_{q+1}(Y)·K_{r+1}(Z) − (q+1)(r+1)·(log Y)^q (log Z)^r| ≤ δ·(log Y)^q (log Z)^r,
  ```

  a **relative** bound, so it applies to any weight.  (The corresponding estimate was previously
  inlined inside `SelbergLogPowerPrincipalAsymptotics` and unusable elsewhere.)
* `selbergGcdLogPrincipalScaledLogPowerModel_sub_harmonicMain` — single-sum form of the error;
* **`tendsto_selbergGcdLogPrincipalScaledLogPowerModel_sub_harmonic_div_log_pow_zero`** —
  the harmonic replacement, error `o((log N)^{q+r+2})`;
* **`tendsto_selbergGcdLogPrincipalScaledLogPowerModel_div_log_pow`** —

  ```text
  ∑_{d ≤ N/max(a,b)} (log d/d)·K_{q+1}(N/(ad))·K_{r+1}(N/(bd)) / (log N)^{q+r+2}
      →  (q+1)(r+1)/((q+r+1)(q+r+2)).
  ```

So the **whole principal side of the gcd-logarithmic family is closed**, at every pair of
logarithmic powers and every pair of dilations.

### The single remaining step of the gcd-log family

`‖corr^{log}‖₁ < ∞`, where

```text
corr^{log} = c^{log} ∗ mp⁻¹ ∗ diag⁻¹ + c ∗ mp⁻¹ ∗ diagInvLog,
  mp⁻¹(r,s) = 1/(rs),   diag⁻¹(d,d) = μ(d)/d,   diagInvLog(d,d) = μ(d)·log d/d.
```

Only summability is needed, not the mass: with it, the Leibniz identity
`c·log(m,n) = corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫` plus the dilated envelope
`exists_abs_selbergOriginalDilatedLogMonomial_le` makes the second term `O((log N)^{i+j−1})`,
and dominated convergence over `corr` turns the first into
`i·j/((i+j−1)(i+j))·(log N)^{i+j}`.

The summability is the exact analogue of `summable_selbergEulerCorrectionCoeff` and should reuse
`summableFiberPushforward` from `SelbergEulerCorrectionCoefficientMass.lean`; the local factor to
parameterize is

```text
(log p / p²)·XY(X + Y − 2XY)/((1 − X/p)(1 − Y/p)).
```

## Session summary (2026-08-29)

Nine axiom-clean leaves landed, all wired into `RHTower.lean`, all passing exact leaf `lake build`
with no warnings and `#print axioms` with only `propext, Classical.choice, Quot.sound`:

| # | module | capstone |
|---|---|---|
| 1 | `Sieve/HarmonicLogWindowGeneralMoment` | `tendsto_harmonicLogWindowMoment_natDiv_div_log_pow` (all orders) |
| 2 | `Sieve/SelbergLogPowerHarmonicGeneral` | `tendsto_selbergLogPowerHarmonicMain_div_log_pow` |
| 3 | `Sieve/SelbergLogPowerGeneralAsymptotic` | `tendsto_selbergOriginalLogMonomial_div_log_pow` (**Graham at every `(i,j)`**) |
| 4 | `Sieve/SelbergDilatedLogMonomial` | `exists_abs_selbergPrincipalScaledLogPowerModel_le`, dilated decomposition |
| 5 | `Sieve/SelbergDilatedLogMonomialAsymptotic` | `tendsto_selbergOriginalDilatedLogMonomial_div_log_pow`, dilated envelope |
| 6 | `Sieve/SelbergGcdLogHarmonicMain` | `tendsto_selbergGcdLogHarmonicMain_div_log_pow` |
| 7 | `Sieve/SelbergGcdLogPrincipalCollapse` | `selbergGcdLogPrincipalCoeff_weighted_logPower_eq_scaledModel` |
| 8 | `Sieve/SelbergGcdLogHarmonicReplacement` | `tendsto_selbergGcdLogPrincipalScaledLogPowerModel_div_log_pow` |

plus the structural correction of brick 5af (the direct/reflected cross must be evaluated, not
bounded).

## The explicit shape of `corr^{log}` (worked out 2026-08-29, for the next session)

`corr^{log}` is the derivation of the bivariate-multiplicative correction: for coprime pairs

```text
corr^{log}(ac, bd) = corr^{log}(a,b)·corr(c,d) + corr(a,b)·corr^{log}(c,d),
```

so `corr^{log}(m,n) = ∑_p corr^{log}(p^{a_p}, p^{b_p})·∏_{q≠p} corr(q^{a_q}, q^{b_q})`, i.e.
`corr^{log} = ∑_p L_p ⊗ corr^{(p)}` with `corr^{(p)}` the correction with the `p`-fibre deleted.
In the corpus's `(r,u,v)`-pushforward parameterization (`selbergCorrectionWeight`), `corr^{(p)}` is
just the sub-sum over squarefree supports `r` with `p ∤ r`, so `‖corr^{(p)}‖₁ ≤ ‖corr‖₁` for free.

**The local factor is completely explicit.**  From
`corr_p(s) = E_p(s)·(1 − p^{s−1}XY/p)/((1−X/p)(1−Y/p))`, `E_p(s) = 1 − X/p − Y/p + p^{s−1}XY/p`,

```text
∂_s corr_p(s)|_{s=1} = (log p / p²)·XY(X + Y − 2XY)/((1−X/p)(1−Y/p)),
```

whose coefficients are

```text
L_p(p^α, p^β) = (log p)·p^{-2-α-β}·( p³·[α≥2, β≥1] + p³·[α≥1, β≥2] − 2p⁴·[α≥2, β≥2] ).
```

Summing geometric series (`∑_{α≥2} p^{-α} ≤ 2p^{-2}`, `∑_{β≥1} p^{-β} ≤ 2p^{-1}`):

```text
‖L_p‖₁ ≤ (log p / p²)·(4 + 4 + 8) = 16 log p / p²,        ∑_p 16 log p / p² < ∞.
```

Hence `‖corr^{log}‖₁ ≤ (∑_p 16 log p/p²)·‖corr‖₁ < ∞`, which is all the route needs.

**Sanity check of the leading coefficient.**  The `XY` coefficient of `corr_p` is `−1/p²`
(consistent with the corpus's `selbergCorrectionWeight r u v = (μ(r)/r²)A_r(u)A_r(v)`), and
`L_p` starts at degree three with coefficient `log p / p²` — one degree higher, as it must be, since
`corr^{log}` has no `XY` term.

**Why no other derivation works.**  A weight `w(m,n)` is additive over bivariate Dirichlet
convolution iff `w(m,n) = α log m + β log n`; `log(m,n)` is not of that form, so the `s`-derivative
of the Euler product is the only route.  (What *is* available for free: `f ↦ f·log(mn)` is a
genuine derivation, and `Λ₂(diag)(d,d) = 2 log d/d = 2·diag_log`, which gives
`𝒫^{log} = ½[Λ₂(𝒫) − diag ∗ Λ₂(mp)]` — useful as a cross-check but not a substitute, because
`Λ₂(c)` is the *pure-log* weight `log(mn)`, not the gcd weight.)

Note also, for the `Λ₂(mp)` collapse if it is ever needed: the `μ·log` kernel is elementary,
`K̃_i(Y) = ∑_{u≤Y} (μ(u) log u / u)·log(Y/u)^i = log Y·K_i(Y) − K_{i+1}(Y)`, so it needs no new
Möbius theory.

## Brick 5ai — the differentiated local Euler factor is built (2026-08-29)

`RHTower/Sieve/SelbergCorrectionLogLocal.lean` (axiom-clean, no warnings, wired):

* `selbergCorrectionLogLocal p α β` — the exact `(X^α, Y^β)` coefficient of
  `∂_s corr_p(s)|_{s=1} = (log p/p²)·XY(X+Y−2XY)/((1−X/p)(1−Y/p))`, namely
  `(log p)·p^{-2-α-β}·(p³[α≥2,β≥1] + p³[α≥1,β≥2] − 2p⁴[α≥2,β≥2])`;
* `geomTailTwo`, `geomTailOne` with `summable_*` and `tsum_*_le … ≤ 2` (shifted geometric tails,
  proved by the `(· + k)` reindexing, `Function.Injective.tsum_eq`);
* **`abs_selbergCorrectionLogLocal_le`** — the exact factorized majorant;
* **`summable_abs_selbergCorrectionLogLocal`** and
  **`tsum_abs_selbergCorrectionLogLocal_le`**: `∑_{α,β} |L_p(α,β)| ≤ 16 log p / p²`.

Since `∑_p 16 log p/p² < ∞`, this is the whole quantitative content of `‖corr^{log}‖₁ < ∞`.

### What is left for `corr^{log}` — the derivation framework

`corr^{log}` is a **derivation of a bivariate multiplicative function**:
`D(ac,bd) = D(a,b)·f(c,d) + f(a,b)·D(c,d)` for pair-coprime arguments, `D(1,1) = 0`.
Three facts finish the family:

1. a `BivariateDerivation f D` predicate with `eq_of_prime_pow_eq` (two derivations of the same
   multiplicative `f` agreeing on prime powers are equal) — the analogue of the existing
   `BivariateMultiplicative.eq_of_prime_pow_eq`;
2. `c·log(m,n)` is a derivation of `c` (uses the corpus's `gcd_pair_mul_of_pair_coprime`), and
   `corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫` is a derivation of `corr ∗ 𝒫 = c` (Leibniz for convolution);
3. the two agree on prime powers — a finite local computation with
   `selbergCorrectionLogLocal` and the known prime-power values of `corr`, `𝒫`, `𝒫^{log}`.

`corr^{log}` itself is then the pushforward of `L_p ⊗ corr^{(p)}`, where `corr^{(p)}` is the
existing `(r,u,v)` correction restricted to supports `r` with `p ∤ r`, so
`‖corr^{(p)}‖₁ ≤ ‖corr‖₁` for free.

## Brick 5aj — the derivation framework (2026-08-29)

Two further axiom-clean leaves, both wired, both clean on the first check:

* `RHTower/Sieve/BivariateDerivation.lean`
  - `BivariateDerivation f D` : `D 1 1 = 0` and `D (a*c) (b*d) = D a b · f c d + f a b · D c d`
    for pair-coprime arguments;
  - **`BivariateDerivation.eq_of_prime_pow_eq`** — two derivations of the same bivariate
    multiplicative function that agree on simultaneous prime-power pairs are equal (strong induction
    on `m*n` along the `p`-adic splitting, mirroring
    `BivariateMultiplicative.eq_of_prime_pow_eq`);
  - **`BivariateDerivation.convolution`** — the Leibniz rule for the product-divisor convolution:
    if `D` derives `f` and `E` derives `g`, then `D ∗ g + f ∗ E` derives `f ∗ g`.  Proved through
    the same `pairCoprimeDivisorsEquiv` reindexing as the multiplicativity of the convolution.

* `RHTower/Sieve/SelbergGcdLogCoefficient.lean`
  - `selbergOriginalGcdLogCoeff m n = c(m,n)·log (m,n)` and
    **`bivariateDerivation_selbergOriginalGcdLogCoeff`** — it is a derivation of
    `selbergOriginalCoeff`, from `gcd_pair_mul_of_pair_coprime` plus `Real.log_mul`;
  - `selbergOriginalGcdLogMonomial i j N`, the object whose asymptotic the corrected Levinson route
    consumes.

### Remaining for the gcd-log family

1. define `corr^{log}` (pushforward of `L_p ⊗ corr^{(p)}`) and prove it is a
   `BivariateDerivation selbergEulerCorrectionCoeff` with prime-power values
   `selbergCorrectionLogLocal`;
2. compute both sides of `c^{log} = corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫` on prime powers — a finite
   local identity — and conclude by `BivariateDerivation.eq_of_prime_pow_eq`
   (`BivariateDerivation.convolution` already shows the right side is a derivation of `c`);
3. feed the identity through the dilated envelope + dominated convergence, exactly as in brick 5af,
   to get

   ```text
   selbergOriginalGcdLogMonomial i j N / (log N)^{i+j}  →  i·j/((i+j−1)(i+j)).
   ```

Steps 1 and 2 are bookkeeping over the existing `(r,u,v)` parameterization; step 3 is a copy of the
already-working dominated-convergence layer.

## Brick 5ak — `corr^{log}` constructed (2026-08-29)

`RHTower/Sieve/SelbergEulerCorrectionLogCoefficient.lean` (axiom-clean, wired):

```text
selbergEulerCorrectionLogCoeff m n
  = ∑_{p ∣ mn} selbergCorrectionLogLocal p (v_p m) (v_p n) ·
      selbergEulerCorrectionCoeff (m / p^{v_p m}) (n / p^{v_p n})
```

* **`selbergEulerCorrectionLogCoeff_prime_pow`** — `corr^{log}(p^i, p^j) = L_p(i,j)`, the
  differentiated local Euler coefficient of brick 5ai;
* **`bivariateDerivation_selbergEulerCorrectionLogCoeff`** — it is a Leibniz derivation of
  `selbergEulerCorrectionCoeff`.  The proof splits the prime factors of `(ac)(bd) = (ab)(cd)` along
  `Nat.Coprime.disjoint_primeFactors`, uses `Nat.factorization_mul` +
  `Nat.factorization_eq_zero_of_not_dvd` to see that the `p`-valuation is unchanged on the side that
  does not contain `p`, and `Nat.mul_div_right_comm` + the multiplicativity of `corr` to split the
  cofactor.

Combined with brick 5aj this closes items 1 of the "remaining" list.  What is left:

* the **local identity** `c^{log}(p^i,p^j) = (corr ∗ 𝒫^{log})(p^i,p^j) + (corr^{log} ∗ 𝒫)(p^i,p^j)`
  — a finite computation with the four local Euler factors — after which
  `BivariateDerivation.eq_of_prime_pow_eq` (both sides being derivations of `c`, by
  `bivariateDerivation_selbergOriginalGcdLogCoeff` and `BivariateDerivation.convolution`) gives the
  global identity;
* `‖corr^{log}‖₁ < ∞`, from `tsum_abs_selbergCorrectionLogLocal_le` (`≤ 16 log p/p²`) and
  `‖corr‖₁ < ∞`, through the `(p, α, β, m', n')` regrouping;
* the dominated-convergence assembly, a copy of brick 5af's, giving
  `selbergOriginalGcdLogMonomial i j N / (log N)^{i+j} → i·j/((i+j−1)(i+j))`.

## The remaining local identity, worked out explicitly (2026-08-29)

With `A(k) := reciprocalMoebiusAmplitude (p^k)` (`A(0)=1`, `A(k)=(1−p)/p^k` for `k ≥ 1`; the
coefficients of `𝒜(X) = X(1−X)/(1−X/p)`) and `μrec(p^0)=1`, `μrec(p^1)=−1/p`, `μrec(p^m)=0` for
`m ≥ 2`, the four local coefficient families are

```text
c^{log}(p^i,p^j) = (log p / p)·[i = 1][j = 1]            (c vanishes off i,j ≤ 1, and log gcd = min(i,j)·log p)
corr(p^{k+1},p^{l+1}) = −(1/p²)·A(k)·A(l),  corr(p^k,1) = corr(1,p^l) = 0 (k,l ≥ 1),  corr(1,1) = 1
𝒫(p^i,p^j)      = ∑_{t ≤ min(i,j)}  p^{-t}          · μrec(p^{i−t})·μrec(p^{j−t})
𝒫^{log}(p^i,p^j)= ∑_{t ≤ min(i,j)} (t·log p·p^{-t}) · μrec(p^{i−t})·μrec(p^{j−t})
corr^{log}(p^i,p^j) = L_p(i,j)  =  selbergCorrectionLogLocal p i j
```

and the identity to prove, for every `i, j ≥ 0`, is

```text
(log p/p)·[i=1][j=1] = ∑_{k≤i, l≤j} corr(p^k,p^l)·𝒫^{log}(p^{i−k},p^{j−l})
                     + ∑_{k≤i, l≤j} L_p(k,l)·𝒫(p^{i−k},p^{j−l}).
```

Both sides are derivations of `c` (left: `bivariateDerivation_selbergOriginalGcdLogCoeff`; right:
`BivariateDerivation.convolution` applied twice, using that `diag_log` is a derivation of `diag`
and `0` is a derivation of `mp`), so **this local family is the only thing between the corpus and
the global identity**, by `BivariateDerivation.eq_of_prime_pow_eq`.

It is the exact analogue of the existing `SelbergEulerCoefficientIdentity.lean` (which proves the
undifferentiated local identity `c_p = corr_p ∗ 𝒫_p`), and should be organized the same way:
generating functions `E_p(s) = 1 − X/p − Y/p + p^{s−1}XY/p`,
`𝒫_p(s) = (1−X/p)(1−Y/p)/(1 − p^{s−1}XY/p)`, differentiate in `t := p^{s−2}` at `t = 1/p`, where

```text
∂_t[E_p·(1 − tXY)] = XY·(X/p + Y/p − 2tXY),      ∂_t[1/(1−tXY)] = XY/(1−tXY)²,
```

which is where `L_p = (log p/p²)·XY(X+Y−2XY)/((1−X/p)(1−Y/p))` and
`diag_log = log p·(XY/p)/(1−XY/p)²` come from.

**Why the crude route fails.** One cannot bound `‖corr^{log}_p‖₁` by
`‖c^{log}_p‖₁ + ‖corr_p‖₁‖𝒫^{log}_p‖₁`: both of those are `≍ log p/p`, and `∑_p log p/p` diverges.
The `log p/p²` saving is a cancellation between them, so the local identity must be proved exactly.

## The local identity collapses to two one-dimensional facts (2026-08-30)

Working the algebra out at the level of generating functions makes the remaining local computation
short.  Write `N = (1−X/p)(1−Y/p)` (`= mp`), `D = 1 − XY/p`, so `𝒫 = mp/D`, `corr = c·D/N`,
`𝒫^{log} = log p·(XY/p)·N/D²`, `corr^{log} = (log p/p²)·XY(X+Y−2XY)/N`.  Then

```text
(corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫) ∗ D
    = log p·(XY/p) ∗ (corr ∗ 𝒫) + corr^{log} ∗ N
    = log p·(XY/p) ∗ c + (log p/p²)·XY(X+Y−2XY),
```

and `c^{log} ∗ D` is the same thing because `c + (X+Y−2XY)/p = D` — a one-line polynomial identity
(`1 − X/p − Y/p + XY/p + X/p + Y/p − 2XY/p = 1 − XY/p`).  Since `D` is invertible (`D ∗ diag = δ`),
this gives the local identity.

The only nontrivial input is `corr^{log} ∗ N = (log p/p²)·XY(X+Y−2XY)`, and **that factorizes**.
With `g₂(i) := p²·p^{-i}·[i ≥ 2]` and `g₁(j) := p·p^{-j}·[j ≥ 1]` (exactly the `geomTailTwo`,
`geomTailOne` of brick 5ai),

```text
selbergCorrectionLogLocal p i j = (log p/p²)·( g₂(i)g₁(j) + g₁(i)g₂(j) − 2 g₂(i)g₂(j) ),
```

and `N` is the product `n(i)n(j)` with `n(0)=1`, `n(1)=−1/p`, `n(≥2)=0`.  So the two-dimensional
convolution factorizes into one-dimensional ones, and

```text
(g₂ ∗ n)(i) = g₂(i) − g₂(i−1)/p = [i = 2],        (g₁ ∗ n)(j) = g₁(j) − g₁(j−1)/p = [j = 1].
```

(Both are two-line checks: `i = 0,1` give `0`; `i = 2` gives `1 − 0`; `i ≥ 3` gives
`p²p^{-i} − p²p^{-i} = 0`.)  Hence
`corr^{log} ∗ N = (log p/p²)([i=2][j=1] + [i=1][j=2] − 2[i=2][j=2])`, which is exactly the numerator.

So the remaining Lean work is: the two one-dimensional convolution identities, a
product-factorization lemma for `additiveBivariateConvolution`, the diagonal identity
`diag_log ∗ D = log p·(XY/p) ∗ diag`, and the finite assembly — no case explosion.

## Brick 5al — the local gcd-logarithmic identity is CLOSED (2026-08-30)

Two axiom-clean leaves, both wired:

* `RHTower/Sieve/SelbergCorrectionLogNumerator.lean`
  - `additiveConvolution` (one-dimensional) and
    **`additiveBivariateConvolution_product`** — a product of one-variable factors convolves
    componentwise;
  - `localMoebiusFactor p` (`= 1, −1/p, 0, …`) and
    `additiveConvolution_localMoebiusFactor` (convolving with `1 − X/p` is the first difference);
  - **`additiveConvolution_geomTailTwo`** (`g₂ ∗ n = [i = 2]`) and
    **`additiveConvolution_geomTailOne`** (`g₁ ∗ n = [j = 1]`);
  - **`additiveBivariateConvolution_selbergCorrectionLogLocal_moebius`** —
    `corr^{log} ∗ N = (log p/p²)·XY(X + Y − 2XY)`, the numerator identity.
  - Supporting: `selbergCorrectionLogLocal_eq_geomTails` (the exact product form of `L_p`),
    extracted in `SelbergCorrectionLogLocal.lean`.

* `RHTower/Sieve/SelbergGcdLogLocalIdentity.lean`
  - `selbergMoebiusReciprocalCoeff_prime_pow_eq`, `localMoebiusPairFactor_eq`,
    `selbergLocalGcdLogPrincipal_eq_convolution`, `selbergLocalCorrectionLog_eq`,
    `selbergLocalDiagonalLogReciprocal_eq`, `selbergLocalDiagonalReciprocal_eq`,
    `gcd_prime_pow_eq_pow_min`, `selbergLocalOriginalGcdLog_eq`
    (`c^{log}(p^i,p^j) = (log p/p)·[i=1][j=1]`);
  - **`additiveBivariateConvolution_diagonalLog_eulerDenominator`** —
    `diag^{log} ∗ D = (log p·XY/p) ∗ diag`;
  - **`selbergLocalGcdLog_denominator_identity`** — the finite identity
    `(log p·XY/p) ∗ c + numerator = c^{log} ∗ D`;
  - `additiveBivariateConvolution_add_left`;
  - **`additiveBivariateConvolution_localGcdLog_identity`** —

    ```text
    corr ∗ 𝒫^{log} + corr^{log} ∗ 𝒫 = c^{log}   at every prime.
    ```

    Proved by convolving with `D` (using `𝒫 ∗ D = mp`, `𝒫^{log} ∗ D = M ∗ 𝒫`,
    `corr ∗ 𝒫 = c`, the numerator identity, and the finite identity) and cancelling `D` against
    `diag`.

### What is left in the gcd-log family

1. **Global identity.**  Transport the local identity to all `(m,n)` with
   `BivariateDerivation.eq_of_prime_pow_eq`.  Both sides are derivations of `c`:
   the left by `bivariateDerivation_selbergOriginalGcdLogCoeff`; the right by
   `BivariateDerivation.convolution` applied twice, which needs the two easy instances
   `BivariateDerivation selbergDiagonalReciprocalCoeff selbergDiagonalLogReciprocalCoeff`
   (pair-coprimality forces `a = b`, `c = d` on the diagonal, and `log` is additive) and
   `BivariateDerivation selbergMoebiusReciprocalPair 0`.
2. **`‖corr^{log}‖₁ < ∞`** from `tsum_abs_selbergCorrectionLogLocal_le` (`≤ 16 log p/p²`) and
   `‖corr‖₁ < ∞`, through the `(p, α, β, m', n')` regrouping.
3. **Dominated-convergence assembly**, a copy of brick 5af's, giving
   `selbergOriginalGcdLogMonomial i j N / (log N)^{i+j} → i·j/((i+j−1)(i+j))`.

## Brick 5am — the GLOBAL gcd-logarithmic identity is CLOSED (2026-08-30)

`RHTower/Sieve/SelbergGcdLogGlobalIdentity.lean` (axiom-clean, wired):

* `bivariateDerivation_zero` — `0` derives any bivariate multiplicative function;
* `diag_pair_split` — on a pair-coprime splitting, `a·c = b·d` forces `a = b` and `c = d`
  (each of `a ∣ b`, `b ∣ a` follows from `Nat.Coprime.dvd_of_dvd_mul_right`);
* **`bivariateDerivation_selbergDiagonalLogReciprocalCoeff`** — `diag^{log}` derives `diag`;
* **`bivariateDerivation_selbergGcdLogPrincipalCoeff`** — `𝒫^{log}` derives `𝒫`
  (`BivariateDerivation.convolution` with the zero derivation on the Möbius pair);
* `bivariateDerivation_gcdLogRightSide` — the right-hand side derives `c`;
* **`selbergOriginalGcdLogCoeff_eq_convolution_sum`** —

  ```text
  c(m,n)·log(m,n) = (corr^{log} ∗ 𝒫)(m,n) + (corr ∗ 𝒫^{log})(m,n)      (0 < m, 0 < n).
  ```

  By `BivariateDerivation.eq_of_prime_pow_eq`, from the local identity of brick 5al.

**Item 1 of the gcd-log family's remaining list is closed.**  What is left:

2. `‖corr^{log}‖₁ < ∞` — from `tsum_abs_selbergCorrectionLogLocal_le` (`≤ 16 log p/p²`,
   summable over primes) and `‖corr‖₁ < ∞`, through the `(p, α, β, m', n')` regrouping of
   `selbergEulerCorrectionLogCoeff m n = ∑_{p ∣ mn} L_p(v_p m, v_p n)·corr(m/p^{v_p m}, n/p^{v_p n})`;
3. the dominated-convergence assembly (a copy of brick 5af's), giving

   ```text
   selbergOriginalGcdLogMonomial i j N / (log N)^{i+j}  →  i·j/((i+j−1)(i+j)).
   ```

### Summability of `corr^{log}`: only an injection is needed (2026-08-30)

The `(p, α, β, m', n')` regrouping does **not** need a bijection.  For nonnegative majorants an
injection suffices:

```text
|corr^{log}(m,n)| ≤ ∑_{p ∣ mn} M_p(v_p m, v_p n)·|corr(m/p^{v_p m}, n/p^{v_p n})|,
```

and the triple `(m,n,p) ↦ (p, v_p m, v_p n, m/p^{v_p m}, n/p^{v_p n})` is **injective** (the pair
`(m,n)` is recovered as `(p^α m', p^β n')`).  So every finite partial sum is bounded by the full
sum over the target index set,

```text
∑_p (∑_{α,β} M_p(α,β)) · ‖corr‖₁ ≤ (∑_p 16 log p / p²)·‖corr‖₁ < ∞,
```

and `summable_of_sum_le` finishes.  The two quantitative inputs are already in the tree
(`tsum_selbergCorrectionLogMajorant_le`, `summable_abs_selbergEulerCorrectionCoeff`); the only new
analytic fact needed is `Summable (fun p => log p / p²)`, which follows from `log n ≤ 2√n` and
`Real.summable_one_div_nat_rpow` at exponent `3/2`.

## Brick 5an — `‖corr^{log}‖₁ < ∞` (2026-08-30)

`RHTower/Sieve/SelbergCorrectionLogSummable.lean` (axiom-clean, wired):

* `selbergCorrectionLogMajorant_nonneg'`, `summable_selbergCorrectionLogMajorant'`,
  `tsum_selbergCorrectionLogMajorant_le'` — the brick-5ai estimates extended to `p ∈ {0,1}`
  (where `log p = 0` makes everything vanish);
* `summable_sixteen_log_div_sq` — from the corpus's `summable_log_div_sq`;
* `summable_abs_selbergEulerCorrectionCoeff` — the `ℓ¹` mass of the correction;
* **`padicSplit_injective`** — `(m,n) ↦ ((v_p m, v_p n), (m/p^{v_p m}, n/p^{v_p n}))` is injective
  (globally, since `m = p^{v_p m}·(m/p^{v_p m})` holds for `m = 0` too);
* `padicMajorantTerm`, `splitMajorant`, `summable_splitMajorant`, `tsum_splitMajorant_eq`;
* **`tsum_padicMajorantTerm_le`** — `∑_{m,n} M_p(v_p m, v_p n)·|corr(…)| ≤ (16 log p/p²)·‖corr‖₁`,
  by `Summable.tsum_le_of_sum_le` + `Finset.sum_image` along the injection;
* `summable_padicMajorantProd`, `summable_padicMajorantSwap`,
  `summable_padicMajorantTerm_fixed`, `summable_padicMajorantSum`;
* `abs_selbergEulerCorrectionLogCoeff_le` — the pointwise majorant;
* **`summable_abs_selbergEulerCorrectionLogCoeff`** — `‖corr^{log}‖₁ < ∞`.

**Item 2 is closed.**  The gcd-log family now needs only item 3: the dominated-convergence
assembly, which is a copy of the pure-log one of brick 5af —

```text
selbergOriginalGcdLogMonomial i j N / (log N)^{i+j}  →  i·j/((i+j−1)(i+j)),
```

using `selbergOriginalGcdLogCoeff_eq_convolution_sum` (brick 5am), the `𝒫^{log}` model asymptotic
(brick 5ah), the dilated envelope `exists_abs_selbergPrincipalScaledLogPowerModel_le` (brick 5ag),
and `summable_abs_selbergEulerCorrectionLogCoeff`.

## Brick 5ao — THE GCD-LOGARITHMIC FAMILY IS CLOSED (2026-08-30)

`RHTower/Sieve/SelbergGcdLogAsymptotic.lean` (axiom-clean, wired):

* **`exists_abs_selbergGcdLogPrincipalScaledLogPowerModel_le`** — one envelope
  `|∑_d (log d/d)K_{q+1}K_{r+1}| ≤ M(log N)^{q+r+2}` valid at every pair of dilations;
* **`selbergOriginalGcdLogMonomial_eq_correction_split`** — the exact split
  `∑ c^{log}·W = ∑_{d,e} corr^{log}(d,e)·𝒫-scaled + ∑_{d,e} corr(d,e)·𝒫^{log}-scaled`,
  from the global identity of brick 5am plus the two rectangular collapses;
* `selbergGcdCorrectionScaledTerm`, `tsum_…`,
  `exists_eventually_norm_selbergGcdCorrectionScaledTerm_le`,
  `tendsto_selbergGcdCorrectionScaledTerm`, and
  **`tendsto_tsum_selbergGcdCorrectionScaledTerm`** — the main term, by dominated convergence;
* `exists_abs_gcdLogErrorTerm_le`, **`tendsto_gcdLogErrorTerm_div`** — the `corr^{log}` term is
  `O((log N)^{q+r+1}) = o((log N)^{q+r+2})`, using `‖corr^{log}‖₁ < ∞` (brick 5an);
* **`tendsto_selbergOriginalGcdLogMonomial_div_log_pow`** —

  ```text
  ∑_{m,n ≤ N} μ(m)μ(n)(m,n)/(mn)·log(N/m)^i·log(N/n)^j·log(m,n) / (log N)^{i+j}
        →  i·j / ((i+j−1)(i+j))      for all i, j ≥ 1.
  ```

### Status of the corrected arithmetic layer

| family | statement | state |
|---|---|---|
| pure-log | `∑ c(m,n)·log(N/m)^i log(N/n)^j ~ (ij/(i+j−1))·(log N)^{i+j−1}` | **CLOSED 2026-08-29** |
| gcd-log | `∑ c(m,n)·log(N/m)^i log(N/n)^j·log(m,n) ~ (ij/((i+j−1)(i+j)))·(log N)^{i+j}` | **CLOSED 2026-08-30** |

**Both Selberg families required by the corrected Levinson route are now unconditional Lean
theorems.**  Together with the verification against Young's constant recorded in brick 5af
(`P(x)=x`, `Q=1`, `R=0` gives `1 + 1/θ`), the arithmetic side of the mollified second moment is
complete for the linear mollifier; what remains on that side is only the assembly with a general
`P`, `Q` and the detector parameter, which is a finite linear combination of these two families.

The remaining brick-5 gate is therefore purely **analytic**: the twisted second moment

```text
∫_T^{2T} ζ(½+it)ζ(½−it)(h/k)^{-it} dt = T·((h,k)/√(hk))·( log(T(h,k)²/(2πhk)) + 2γ − 1 ) + error,
```

with a power-saving error uniform for `h,k ≤ T^θ`.  The corpus already owns the smooth AFE at every
Levinson abscissa, the twisted mean-value theorem with explicit error, and the displaced stationary
cross estimates; what brick 5af showed is that the cross term must be *evaluated*, not bounded.

## Consumer audit of the two cards this programme gates (2026-08-30)

Both cards in `2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry` that depend
on this programme were audited against the tree — all 17 claimed Lean declarations are present, none
stale — and their consumer sides were completed, so each is now blocked on exactly one statement
owned here.

* **`bounded-support-weil-critical-tail-uniqueness`.**  New leaf
  `RHTower/XiSimpleCriticalSuperlinearConsumer.lean` (axiom-clean, wired):
  `not_linear_bound_of_superlinear`,
  **`suzukiCompactL2Fourier_eq_zero_of_superlinear_simpleCritical`**,
  **`suzukiCutoff_eq_zero_of_superlinear_simpleCritical`**.  The card's Theorem 2 is now a Lean
  theorem whose only premise is

  ```text
  ∃ c > 0, ∀ᶠ T in atTop,  c · T · log T ≤ (xiSimpleCriticalZeroCount T : ℝ).
  ```

  That is brick 7 + brick 8 of this programme (a positive proportion of *simple* critical zeros).

* **`horizontal-singleton-zero-fibers`.**  Blocked on exactly
  `0.417293962 ≤ liminf xiCriticalRatio` and `0.407511457 ≤ liminf xiSimpleCriticalRatio`
  — bricks 7–10.

So the programme's brick list now has named external consumers, and closing bricks 7–10 closes both
cards.  (The third card in that folder, `verified-height-one-zero-turing-extension`, does not depend
on this programme; its remaining input is an external certified computation, assessed on the card.)

## Brick 5ap — the twisted second-moment diagonal is evaluated (2026-08-30)

With the arithmetic layer closed, the remaining gate is analytic.  Its first component — the
diagonal of the twisted second moment — is now a Lean theorem.

`RHTower/Sieve/TwistedDiagonalSqrtEvaluation.lean` (axiom-clean, wired):

* **`twistedDiagonalSqrtWeight`** — on the reduced ray the critical-line weight collapses:

  ```text
  1 / √( (k'd)·(h'd) )  =  ((h,k)/√(hk)) · (1/d),      h' = h/(h,k),  k' = k/(h,k).
  ```

* `twistedDiagonalSqrt_membership` — the reduced scale range is exactly
  `Icc 1 ⌊X / max(h',k')⌋` (via `min_natDiv_eq_natDiv_max`);
* **`twistedDiagonalSqrt_sum_eq`** —

  ```text
  ∑_{m,n ≤ X, nk = mh} (mn)^{-1/2}  =  ((h,k)/√(hk)) · H_{⌊X / max(h',k')⌋};
  ```

* **`abs_twistedDiagonalSqrt_sub_main_le`** — the main term with an explicit error, from the
  corpus's sharp harmonic comparison:

  ```text
  | ∑_{m,n ≤ X, nk = mh} (mn)^{-1/2}  −  ((h,k)/√(hk))·( log⌊X/max(h',k')⌋ + γ ) |
        ≤  ((h,k)/√(hk)) · 1/⌊X/max(h',k')⌋ ;
  ```

* **`reducedMax_mul_min_eq_lcm`** — `max(h',k')·min(h,k) = [h,k]`, so the weight is literally

  ```text
  log X − log[h,k] + log min(h,k),
  ```

  which is exactly the direct-head weight identified in the structural correction of brick 5af.
  The `(h,k)/√(hk)` prefactor is the classical Balasubramanian–Conrey–Heath-Brown constant.

**What this settles.**  The diagonal half of the twisted second moment is done, in precisely the
form the Levinson mollifier sum consumes, and it confirms the brick-5af accounting from the Lean
side: the direct head really does carry `+log min(h,k)`, the term whose mass makes that diagonal
diverge and which the cross must cancel.

**Next on the analytic gate.**  The shifted diagonal (weight `m^{-1/2-α}n^{-1/2-β}`, giving a
partial `ζ(1+α+β)` in place of the harmonic sum), then the reflected diagonal, then the cross main
term — the last being the genuinely hard one, and the one brick 5af proved must be *evaluated*
rather than bounded.

## Brick 5aq — the twisted main term's removable singularity is evaluated (2026-08-30)

`RHTower/Sieve/TwistedMainTermMerge.lean` (axiom-clean, wired).  The second component of the
analytic gate: the *shape* of the twisted second moment's main term.

Write `h' = h/(h,k)`, `k' = k/(h,k)`, `c = h'k'`.  The classical main term is the shifted diagonal
series together with its functional-equation reflection,

```text
bchbMergeCore X c w  =  c^{-w/2} ζ(1+w)  +  X^{-w} c^{w/2} ζ(1-w).
```

Each summand has a simple pole at `w = 0`, with residues `+1` and `-1`.

* `bchbMergeCore_eq` — the exact split `bchbMergeCore = w⁻¹·gap + reg`, where
  `gap w = c^{-w/2} - X^{-w}c^{w/2}` vanishes at `w = 0` and
  `reg w = c^{-w/2}ζ₀(1+w) + X^{-w}c^{w/2}ζ₀(1-w)` is entire (`riemannZeta₀` is mathlib's
  pole-free completion, with `riemannZeta₀ 1 = γ`).
* `hasDerivAt_bchbMergeGap` — `gap'(0) = log X − log c`.
* `tendsto_bchbMergeGap_div` — hence `w⁻¹ gap(w) → log X − log c` (difference quotient at `0`).
* `tendsto_bchbMergeReg` — `reg(w) → 2γ` by continuity.
* **`tendsto_bchbMergeCore`** —

  ```text
  bchbMergeCore X c w  ⟶  log X − log c + 2γ      (w → 0, w ≠ 0).
  ```

Reduced-ray packaging:

* `reducedProduct_mul_gcd_sq` — `h'k'(h,k)² = hk`;
* **`sqrt_reducedProduct_mul_gcd`** — `√(h'k')·(h,k) = √(hk)`, i.e. `(h'k')^{-1/2} = (h,k)/√(hk)`:
  the Balasubramanian–Conrey–Heath-Brown normalization;
* `log_reducedProduct_merge` — `log X − log(h'k') = log(X(h,k)²/(hk))`;
* **`tendsto_bchbMergeCore_reduced`** — the merged value on the reduced ray is
  `log(X(h,k)²/(hk)) + 2γ`;
* **`bchbTwistedMainTerm_eq`** — the packaged main term

  ```text
  bchbTwistedMainTerm X h k = ((h,k)/√(hk))·( log(X(h,k)²/(hk)) + 2γ )
  ```

  equals `(h'k')^{-1/2}` times the merged shifted pair.

**Consistency check against brick 5ap.**  With `X = t/2π` and `∫_0^T … dt` this is exactly

```text
T·((h,k)/√(hk))·( log(T(h,k)²/(2πhk)) + 2γ − 1 ),
```

the BCHB statement.  Brick 5ap evaluated the *direct* diagonal at cutoff `x(t) = √(t/2π)`, giving
`2·((h,k)/√(hk))·(½log(t/2π) + γ − log max(h',k'))`; integrating over `t ∈ [0,T]` this differs from
BCHB by exactly `((h,k)/√(hk))·T·log(max(h',k')/min(h',k'))`.  So the two Lean bricks now pin the
cross term's main term *numerically*, not just structurally: the reflected term
`χ(1/2+it)·(∑_{n≤x} n^{-1/2+it})²·(h/k)^{-it}` must contribute exactly

```text
T·((h,k)/√(hk))·log( max(h',k') / min(h',k') ),
```

which is the residue of the stationary point `t₀ = 2π mn k'/h'` of the phase
`−t log(t h'/(2π mn k'))`.  This is the brick that must be *evaluated*, as brick 5af showed.

## Bricks 5ar–5at — the stationary-phase keystone (2026-08-30)

Brick 5aq pinned the cross term's target value.  Evaluating it needs stationary phase *with a main
term* — an asymptotic the corpus did not own (it owned only van der Corput upper bounds).  Three
modules now build it from the corpus's own Fresnel stack.

### 5ar `RHTower/QuadraticPhaseStationary.lean` — the local model

The exact quadratic phase, with an explicit error:

```text
‖ ∫_{-R}^{R} e^{i μ t²/2} dt  −  √(2π/μ)·e^{iπ/4} ‖  ≤  8/(μR)      (μ > 0, R > 0),
```

`norm_integral_quadPhase_sub_le`, plus the conjugate `norm_integral_quadPhase_conj_sub_le` for the
reversed phase (value `√(2π/μ)e^{-iπ/4}`).  Proved by `t = x√(2/μ)` from the corpus's
`norm_integral_fresnel_sub_le` (`‖∫_0^R e^{ix²}dx − (√π/2)e^{iπ/4}‖ ≤ 2/R`) together with
`integral_quadPhase_symm` and `integral_quadPhase_scale`.

### 5as `RHTower/LogPhaseProfile.lean` — the universal profile

The key structural observation: the archimedean phases arising from `χ(1/2+it)·n^{it}` all have the
**same** local shape.  Its carrier is

```text
ψ(v) = v − (1+v) log(1+v),      ψ(0) = 0,   ψ'(v) = −log(1+v).
```

Proved: `logPhaseProfile_nonpos` (0 is a strict maximum, from `log(1+v) ≥ v/(1+v)`),
`neg_logPhaseProfile_le_sq` (`−ψ(v) ≤ v²` on all of `(−1,∞)`),
`sq_div_four_le_neg_logPhaseProfile` (`−ψ(v) ≥ v²/4` on `(−1,1]`), and strict monotonicity of `−ψ`
on each side of `0` (`strictMonoOn_neg_logPhaseProfile`, `strictAntiOn_neg_logPhaseProfile`) — the
injectivity needed to invert the Morse substitution `w = sgn(v)√(−2ψ(v))`.

Both quadratic comparisons come from one elementary gap, `K(v) = log(1+v) − v/2`, monotone on
`(−1,1]` and vanishing at `0` (`monotoneOn_halfLogGap`).

### 5at `RHTower/LogLinearPhaseReduction.lean` — the exact factorisation

For `f_B(t) = (B+1)t − t log t` (the phase of `χ(1/2+it)(mn)^{it}(h/k)^{-it}` with
`B = log(2π mn k'/h')`):

* `hasDerivAt_logLinearPhase` — `f_B'(t) = B − log t`, so the stationary point is `t₀ = e^B`;
* `logLinearPhase_exp` — `f_B(t₀) = t₀`;
* **`logLinearPhase_sub_eq`** — the *exact* identity, no approximation:

  ```text
  f_B(t₀(1+v)) − f_B(t₀) = t₀ · ψ(v);
  ```

* `logLinearPhase_drop_bounds` — hence `t₀v²/4 ≤ f_B(t₀) − f_B(t₀(1+v)) ≤ t₀v²` for `|v| ≤ 1`.

**Why this matters.**  A general stationary-phase theorem would need a `C³` Morse lemma.  Here the
substitution is a *single universal function* `ψ`, independent of `B` — exactly the situation the
corpus already handled for `J₀` (where the universal substitution was `v = 2 sin(φ/2)`).  So the
cross term reduces to the quadratic model of 5ar plus a fixed Jacobian correction, with the scale
`μ = t₀ = 2π mn k'/h'` entering only as a parameter.

**The arithmetic consequence, now visible.**  At the stationary point the phase is `t₀` itself, so
the cross term's saddle contributions carry the factor

```text
e^{i t₀} = e^{2π i · mn k'/h'},
```

a root of unity depending on `mn k' mod h'`.  For `h' = 1` all saddles are in phase and the sum is a
clean main term; for general `h'` the sum over `m,n` of these roots of unity is a **Ramanujan /
Kloosterman sum**.  That is the precise arithmetic content of the Balasubramanian–Conrey–Heath-Brown
error term, and it is the next brick.

## Bricks 5au–5av — the Morse coordinate is built (2026-08-30)

### 5au `RHTower/LogPhaseCubic.lean` — the cubic refinement

Inverting the substitution needs `-ψ` to agree with `v²/2` to third order, not merely up to
constants.  Proved, with explicit constants and no asymptotic notation:

* `abs_logRemainder_le_sq` — `|log(1+v) − v| ≤ v²` for `|v| ≤ 1/2`, from the sign of the two
  comparison functions `v² ± (log(1+v) − v)`, whose derivatives are `v(1+2v)/(1+v)` and
  `v(3+2v)/(1+v)`;
* **`abs_logPhaseCubicRemainder_le`** — `| −ψ(v) − v²/2 | ≤ |v|³/3` for `|v| ≤ 1/2`.

The module also contributes three reusable one-sided comparison helpers (vanishing at `0`, with a
signed derivative on a half-interval).

### 5av `RHTower/LogPhaseMorse.lean` — the substitution

```text
w(v) = sgn(v) · √(−2ψ(v)).
```

* `logPhaseMorse_sq` — the defining identity `w(v)² = −2ψ(v)`, i.e. `ψ(v) = −w(v)²/2`;
* `neg_logPhaseProfile_pos` — `ψ(v) < 0` strictly away from the stationary point (so `w` is
  strictly signed);
* `logPhaseMorse_pos` / `logPhaseMorse_neg` — sign preservation;
* **`strictMonoOn_logPhaseMorse`** — `w` is strictly increasing on `(−1,∞)`, hence injective: the
  substitution is a genuine reparametrisation;
* **`abs_logPhaseMorse_sub_le`** — the near-identity estimate

  ```text
  |w(v) − v| ≤ 2v²/3        for |v| ≤ 1/2,
  ```

  obtained by factoring `w² − v² = 2·(cubic remainder)` and dividing by `|w + v| ≥ |v|`, which holds
  because `w` and `v` have the same sign.

**State of the stationary-phase keystone.**  With 5ar (quadratic model, error `8/(μR)`),
5at (exact reduction `f_B(t₀(1+v)) − f_B(t₀) = t₀ψ(v)`) and 5av (`ψ = −w²/2`, `w` a strictly
monotone near-identity), the archimedean integral is

```text
∫ g(t) e^{i f_B(t)} dt
  = t₀ e^{i t₀} ∫ g(t₀(1+V(w))) e^{−i t₀ w²/2} V'(w) dw,
```

with `V` the inverse of `w`.  What remains for the cross term is (i) the Jacobian `V'(w) = 1 + O(w)`
and its integral against the quadratic kernel, and (ii) the arithmetic sum over `m,n` of the saddle
phases `e^{2πi mnk'/h'}` — a Ramanujan/Kloosterman sum.

## Brick 5aw — STRUCTURAL CORRECTION: the adapted approximate functional equation (2026-08-30)

Brick 5af concluded that the cross term of the twisted second moment must be *evaluated* rather
than bounded.  That conclusion is an artefact of the **symmetric** approximate functional equation
`x = y = √(t/2π)`, and it is removable.

**The observation.**  The Hardy–Littlewood/Riemann–Siegel AFE holds for *any* split `2πxy = t`:

```text
ζ(1/2+it) = ∑_{m ≤ x} m^{-1/2-it} + χ(1/2+it) ∑_{n ≤ y} n^{-1/2+it} + O(x^{-1/2}) + O(y^{-1/2}).
```

Choose the split **adapted to the twist**:

```text
x = √( t k / (2π h) ),      y = √( t h / (2π k) ),      xy = t/2π.  ✓
```

On the diagonal ray `nk = mh`, i.e. `m = k'd`, `n = h'd` with `h' = h/(h,k)`, `k' = k/(h,k)`, the two
cutoffs then coincide:

```text
x/k' = y/h' = D(t) = √( t (h,k)² / (2π h k) ),
```

so the diagonal condition is simply `d ≤ D(t)`, and

```text
∑_{m≤x, n≤y, nk=mh} (mn)^{-1/2}
      = ((h,k)/√(hk)) · ( log D(t) + γ + O(1/D) )
      = ((h,k)/√(hk)) · ( ½ log( t(h,k)²/(2πhk) ) + γ + O(1/D) ).
```

Doubling (the `2|A|²` of `|ζ|² = 2AB + χ̄A² + χB²`) and integrating over `t ∈ [0,T]`:

```text
2 ∫_0^T ((h,k)/√(hk)) ( ½ log(t(h,k)²/(2πhk)) + γ ) dt
      = T · ((h,k)/√(hk)) · ( log( T(h,k)²/(2πhk) ) + 2γ − 1 ),
```

which is **exactly** the Balasubramanian–Conrey–Heath-Brown main term — no discrepancy.

**Consequence for the programme.**  With the adapted split:

* the whole main term comes from the direct diagonal;
* the cross term `χ B² (h/k)^{-it}` and the direct off-diagonal are genuine *error* terms, to be
  **bounded**, not evaluated;
* no Ramanujan/Kloosterman evaluation is needed for the main term.

This supersedes the "the cross must be evaluated" conclusion of brick 5af (which remains correct
*for the symmetric split*: there the cross really does carry `log(max(h',k')/min(h',k'))`, exactly
the amount by which the symmetric cutoff wastes the diagonal range).

**Revised gate.**  The remaining analytic work is:

1. the AFE itself with a general split `2πxy = t` (`x, y ≥ 1`), with error `O(x^{-1/2}+y^{-1/2})`;
2. the adapted-cutoff diagonal (a two-cutoff refinement of brick 5ap);
3. an upper bound for the direct off-diagonal `∑_{nk ≠ mh}`;
4. an upper bound for the cross term — the corpus already owns the van der Corput first- and
   second-derivative tests (`VanDerCorputLocal.secondDerivTestOn`,
   `VanDerCorputSecond.norm_integral_cexp_secondDeriv_oneside`), and bricks 5ar/5at/5av give the
   exact phase geometry needed to apply them with the right constants.

The stationary-phase stack of 5ar–5av is not wasted: item 4 needs the same phase geometry, and the
main-term machinery of 5aq stays as the independent check that the two routes agree.

## Bricks 5ax–5ay — the adapted diagonal and its archimedean integral (2026-08-30)

The two Lean bricks that turn the structural correction 5aw into a theorem.

### 5ax `RHTower/Sieve/TwistedDiagonalAdapted.lean`

* `twisted_diagonal_reindex_pair` / `twisted_diagonal_reindex_gcd_pair` — the diagonal reindexing
  with **independent** cutoffs for the two variables (the single-cutoff version of the corpus only
  covers the symmetric split);
* `twistedDiagonalAdapted_membership` — with cutoffs `k'D` and `h'D` the diagonal range is exactly
  `1 ≤ d ≤ D`: no truncation loss;
* **`twistedDiagonalAdapted_sum_eq`** —

  ```text
  ∑_{m ≤ k'D, n ≤ h'D, nk = mh} (mn)^{-1/2} = ((h,k)/√(hk)) · H_D ;
  ```

* **`abs_twistedDiagonalAdapted_sub_main_le`** —

  ```text
  | … − ((h,k)/√(hk))·( log D + γ ) | ≤ ((h,k)/√(hk))·(1/D).
  ```

With `D = √( t(h,k)²/(2πhk) )` the cutoffs are `k'D = √(tk/(2πh))` and `h'D = √(th/(2πk))`, whose
product is `t/2π` — the adapted approximate functional equation.

### 5ay `RHTower/Sieve/BchbDensityIntegral.lean`

The archimedean integration that produces the classical `2γ − 1`:

```text
∫_a^b ( log(ct) + 2γ ) dt = b( log(cb) + 2γ − 1 ) − a( log(ca) + 2γ − 1 )
```

(`integral_bchbLogDensity`, via the antiderivative `t(log(ct) + 2γ − 1)`).  Taking
`c = (h,k)²/(2πhk)` and doubling the adapted diagonal density `½log(ct) + γ` gives exactly

```text
T · ((h,k)/√(hk)) · ( log( T(h,k)²/(2πhk) ) + 2γ − 1 ),
```

the Balasubramanian–Conrey–Heath-Brown main term.  The `−1` is produced by the integration, not by
the arithmetic — which is why the symmetric split appeared to lose it.

**Gate status.**  Main term: closed (arithmetic 5ax + archimedean 5ay, cross-checked against the
independent shifted-pair evaluation 5aq).  Remaining: the approximate functional equation with a
general split, and *upper bounds* for the direct off-diagonal and the cross term.

## Brick 5az — the corpus already owns the arbitrary-split exact AFE (2026-08-30)

Item 1 of the revised gate (5aw) turns out to be **already owned**, and in a stronger form than the
classical Hardy–Littlewood statement: the corpus has an *exact identity*, not an approximation, and
it holds for **every** split parameter.

`RHTower/SmoothAFEZetaDualReflection.lean`:

```text
riemannZeta_line_eq_two_tsum_smoothAFE_dualWeight  (hx : 0 < x) (τ : ℝ) :
  ζ(1/2+iτ) = ∑'_n (n+1)^{-(1/2+iτ)} · smoothAFECutoff((n+1)/x)
            + ∑'_n χ(1/2+iτ)·(n+1)^{(1/2+iτ)-1} · smoothAFEZetaDualWeight τ ((n+1)·x)
            − smoothAFEZetaShiftedPoleResidue (1/2+iτ) x
```

with `riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general`
(`RHTower/SmoothAFEZetaGeneral.lean`) the off-line version, and the cutoff's two-sided behaviour in
`RHTower/SmoothAFECutoffBounds.lean`:

* `exists_norm_smoothAFECutoff_le_neg_rpow` — decay above the scale;
* `exists_norm_smoothAFECutoff_sub_one_le_rpow` — `φ ≈ 1` below the scale.

**Why the adapted split is legitimate here.**  In `∫ ζ(1/2+it)·ζ(1/2−it)·(h/k)^{-it} dt` the two
factors are *separate* instances of the identity, at `τ = t` and `τ = −t`, each with its **own**
free parameter.  Taking

```text
x₁ = √( t k / (2π h) )   for the ζ(1/2+it) factor,
x₂ = √( t h / (2π k) )   for the ζ(1/2−it) factor,
```

gives `x₁x₂ = t/2π` and `x₁/k' = x₂/h' = D(t)`, which is exactly the adapted split of 5aw.  Nothing
is approximated: the identity is exact for each choice, so the whole main term is the direct×direct
diagonal, evaluated in 5ax and integrated in 5ay.

**Updated gate list.**

1. ~~the AFE with a general split~~ — **owned** (exact, smoothed, arbitrary split);
2. the adapted diagonal — **closed** (5ax), for sharp cutoffs; the smooth-cutoff version is a
   comparison against `exists_norm_smoothAFECutoff_sub_one_le_rpow` / `..._le_neg_rpow`;
3. the archimedean integration — **closed** (5ay);
4. an upper bound for the direct off-diagonal `nk ≠ mh`;
5. an upper bound for the cross term (direct × dual) — the phase geometry is 5at/5av, the
   oscillatory bounds are the corpus's van der Corput tests;
6. the dual × dual term, which by the functional equation mirrors 2–4;
7. the pole-residue term, which is `O(x^{1/2}/|t|)`-size and harmless.

No step in this list is open mathematics; all are classical and now have their Lean prerequisites in
the tree.

## Brick 7a — the Littlewood→zero-count consumer is built (2026-09-01)

The window inequality (`exists_levinson_admissible_window`) had left exactly one undetermined
quantity: the zero mass of `G♯ = (s−1)²(ζ + λζ′)` inside `[½,4] × [T₁,T₂]`.  Levinson's route to
that quantity is Littlewood's rectangle identity on the *wider* rectangle `[σ₀,4] × [T₁,T₂]` with
`σ₀ = ½ − R/log T`, followed by Jensen's inequality against a mollified mean square.  That consumer
chain is now Lean, axiom-clean and wired.

### New modules

* `RHTower/LevinsonLittlewoodZeroCount.lean`
  * `intervalIntegrable_log_norm_vertical_of_entire` — `log‖f‖` is interval integrable on every
    vertical segment for entire `f` (via `MeromorphicOn.intervalIntegrable_log_norm`); zeros on the
    segment are harmless;
  * `two_mul_integral_log_norm_le_ae` — the Jensen step with the nonvanishing hypothesis relaxed to
    a null exceptional set, which is what a vertical line through zeros needs;
  * `intervalIntegral_pos_of_continuous_global_nonneg` — positivity of the mean square from a single
    interior nonvanishing point;
  * **`exists_entire_zeroCount_le_of_meanSquare`** — for entire `f` nonvanishing on the bottom, top
    and right edges of `[c,d] × [T₁,T₂]`,

    ```text
    2π (σ − c) · ∑_{Re w ≥ σ} ord_f(w)
        ≤ ½(T₂−T₁)·log( Msq/(T₂−T₁) ) − (T₂−T₁)·log A
          + (d−c)·∫ Re (f′/f)(d+it) + ∫ (x−c) Im (f′/f)(x+iT₁) − ∫ (x−c) Im (f′/f)(x+iT₂),
    ```

    where `Msq` bounds the left-edge mean square and `A` bounds `‖f‖` from below on the right edge.

* `RHTower/EntireAdmissibleHeight.lean` — `exists_entire_admissible_height` and
  `exists_entire_admissible_height_pair`: heights whose whole horizontal segment misses the divisor
  are dense, for an arbitrary entire function and an arbitrary segment (the detector-free
  generalization of `exists_levinsonG_admissible_height`), and a single height serves both factors
  of a product.

* `RHTower/EntireDirichletPolynomial.lean` — `edPoly a s z = ∑_{n∈s} aₙ n^{-z}` as an entire
  function, `differentiable_edPoly`, `analyticOnNhd_edPoly`, `edPoly_line` (its restriction to a
  vertical line is the corpus's `cdpoly`, so the mean-value machinery applies verbatim),
  `norm_edPoly_le`, and the head-dominance lower bound `norm_edPoly_ge`.

* `RHTower/LevinsonDetectorZeroBudget.lean` — **`levinsonGEntire_zeroMass_le_of_meanSquare`**:
  multiplying by an arbitrary entire mollifier `Ψ` only raises the analytic order, so

  ```text
  2π (½ − σ₀) · ∑_{w ∈ Z(G♯) ∩ [½,4]×[T₁,T₂]} ord_{G♯}(w)  ≤  (Littlewood budget of G♯·Ψ).
  ```

* `RHTower/LevinsonOddFiberFromMeanSquare.lean` — `levinsonMollifiedBudget` and
  **`le_xiOddFiberCount_of_mollified_meanSquare`**: the composition with the window inequality,

  ```text
  (n+2)π + π + (T₂−T₁)·6/T₁² + c·log T₁ + c·log T₂ + levinsonMollifiedBudget ≤ θ(T₂) − θ(T₁)
      ⟹  n ≤ xiOddFiberCount T₂.
  ```

All declarations pass direct `lake env lean`, exact leaf `lake build`, and `#print axioms` with only
`propext, Classical.choice, Quot.sound`.

### What this changes for the two consumer cards

The chain is now

```text
mollified mean square of G♯·Ψ at σ₀   ⟹   detector zero mass   ⟹   window inequality
   ⟹   odd-fibre count O(T)   ⟹   H₁(T) ≥ (3/2)O(T) − N(T)/2   and   N₀,s ≥ O − N/3.
```

Every arrow except the first is unconditional Lean.  The remaining obligations of the consumer half
are the two boundary integrals of `G♯·Ψ` (right-edge logarithmic derivative and the two horizontal
edges — the corpus owns the `Ψ = 1` versions in `LevinsonRightEdge` and `LevinsonHorizontalEdge` and
they must be extended by `logDeriv (G♯Ψ) = logDeriv G♯ + logDeriv Ψ`), the far-right lower bound
`A ≤ ‖G♯Ψ(4+it)‖` (head dominance, `norm_edPoly_ge`), and then brick 5's mean square itself.

## Brick 7b — STRUCTURAL CORRECTION: the pole gauge must be cancelled exactly (2026-09-01)

Estimating the Littlewood budget of `G♯·Ψ = (s−1)²·(ζ+λζ′)·Ψ` edge by edge **cannot** close
Levinson's inequality, and the reason is quantitative, not technical.

**The accounting.**  Write the budget on `[σ₀,d] × [T₁,T₂]`, `L = T₂ − T₁`, `½ − σ₀ = R/log T`.
The zero mass obeys `2π(½−σ₀)·N_{G♯} ≤ budget`, and the target is `N_{G♯}/N(T) < 1/3`, i.e.

```text
budget  ≤  (L/2)·log c + o(L),        c = the mollified mean square,
```

because `N(T) ~ T log T/2π` and `2π(½−σ₀) = 2πR/log T`.  **Every `O(L)` term in the budget with a
nonzero constant survives into the final ratio at the same order as `½ log c`.**  With Levinson's
own margin `1 − log c/R > 1/3` holding only by `≈ 0.009`, no `O(L)` slack is affordable.

Three sources of `O(L)` loss in the naive route, and their fixes:

1. *The gauge `(s−1)²`.*  Bounding `|σ₀−1+it|⁴` by its window maximum and `|d−1+it|²` by its window
   minimum costs `L·log(T₂²/T₁²)`, which is `Θ(L log T)` on a long window — fatal.  **Fix: the gauge
   cancels exactly.**  `weightedLittlewoodBoundary` is additive over products, and Littlewood's own
   identity applied to `u(s) = (s−1)²` on a rectangle with `1 ∉ [σ₀,d]×[T₁,T₂]` (guaranteed by
   `T₁ ≥ 20`) gives `weightedLittlewoodBoundary u = 2π·0 = 0`.  Hence

   ```text
   weightedLittlewoodBoundary (G♯·Ψ) = weightedLittlewoodBoundary ((ζ+λζ′)·Ψ),
   ```

   and the whole argument runs on the *meromorphic* detector `G·Ψ`, whose boundary data has no
   height growth at all.  This also removes the pole-gauge horizontal edge from the estimate list.

2. *The far-right logarithm `∫ log‖GΨ(d+it)‖ dt`.*  The pointwise bound `Re G(4+it) ≥ 7/16` costs
   `L·log(16/7) ≈ 0.83 L` — also fatal (the whole margin is `0.009`).  Pushing `d` to the right only
   shrinks the loss like `2^{-d}`, and the required `d` is large and delicate.  **Fix: it is `O(1)`,
   not `O(L)`, by analyticity and decay.**  On `Re s ≥ d` the function `F = Log(GΨ)` is analytic
   (because `‖GΨ − 1‖ < 1` there) and satisfies `‖F(s)‖ ≪ 2^{-Re s}`.  Cauchy's theorem on
   `[d,X]×[T₁,T₂]` with `X → ∞` gives

   ```text
   i·∫_{T₁}^{T₂} F(d+it) dt = ∫_d^∞ F(x+iT₂) dx − ∫_d^∞ F(x+iT₁) dx,
   ```

   whose right-hand side is bounded by `(2/log 2)·sup‖coefficient mass‖`, an absolute constant.
   The same lemma applied to `F′ = logDeriv (GΨ)` makes the right-edge logarithmic-derivative term
   `O(1)` as well.  (This is the Lean form of the classical remark that `log(Vψ)` is an absolutely
   convergent Dirichlet series with no constant term.)

3. *The horizontal edges.*  Already `O(log T) = o(L)`; nothing to fix.  With the gauge cancelled the
   two needed estimates are exactly the ones landed in brick 7a:
   `exists_horizontal_weighted_levinsonG_bound` for `G` and
   `abs_integral_weighted_im_logDeriv_edPoly_le` for `Ψ`, joined by
   `logDeriv (G·Ψ) = logDeriv G + logDeriv Ψ`.

**Consequence.**  A *single* window `[T₀,T]` with `T₀ ≥ 20` fixed suffices — no dyadic subdivision
and no summation of window counts is needed, because after the gauge cancellation nothing in the
budget grows with the height.  The budget becomes

```text
(L/2)·log( (1/L)∫_{T₀}^{T} ‖GΨ(σ₀+it)‖² dt )  +  O(1)  +  O(log T),
```

which is exactly `(L/2) log c + o(L)`.

**Revised remaining consumer list.**

| # | item | state |
|---|---|---|
| 1 | `weightedLittlewoodBoundary` additivity over products | to build |
| 2 | `weightedLittlewoodBoundary ((·−1)^k) = 0` off the rectangle | to build |
| 3 | Cauchy/decay right-edge `O(1)` lemma (for `F` and `F′`) | to build |
| 4 | `‖GΨ − 1‖ < 1` on `Re s ≥ d` with explicit `d` | to build (`ZetaFarRightDecay` + `norm_edPoly_ge`) |
| 5 | horizontal edges for `G` and `Ψ` | **DONE** (brick 7a) |
| 6 | Jensen left edge from the mean square | **DONE** (brick 7a) |
| 7 | zero-mass ≥ `(½−σ₀)·count` | **DONE** (brick 7a) |
| 8 | mollified mean square `(1/L)∫‖GΨ(σ₀+it)‖²` | brick 5/6, the gate |

## Brick 7c — the two structural fixes are Lean (2026-09-01)

Both corrections identified in brick 7b are now unconditional Lean theorems, axiom-clean, wired, and
exact-leaf built.

### `RHTower/LittlewoodPoleGaugeCancellation.lean`

* `exists_entire_zeroCount_le_boundary` — the *raw* Littlewood counting inequality, with no estimate
  applied to any edge:

  ```text
  2π (σ − c) · ∑_{Re w ≥ σ} ord_f(w)  ≤  weightedLittlewoodBoundary f c d T₁ T₂ .
  ```

* `intervalIntegrable_log_norm_vertical_of_analyticAt`, `continuousOn_re_logDeriv_vertical`,
  `continuousOn_weighted_im_logDeriv_horizontal` — the integrability of the four boundary integrands
  for a function merely analytic on the closed rectangle (not entire).

* `weightedLittlewoodBoundary_poleGauge_eq_zero` — Littlewood's own identity applied to
  `u(s) = (s−1)²` on a rectangle missing `s = 1` gives `weightedLittlewoodBoundary u = 0`.

* **`weightedLittlewoodBoundary_poleGauge_mul`** —

  ```text
  weightedLittlewoodBoundary (fun z => (z−1)² * g z) c d T₁ T₂
      = weightedLittlewoodBoundary g c d T₁ T₂
  ```

  for `g` analytic on the closed rectangle, nonvanishing on its bottom, top and right edges, with a
  finite left-edge zero set.  The four boundary integrands split additively (the left edge only
  almost everywhere, which is why the finite zero set is required), and the gauge's own contribution
  is zero.  **The height growth of `(s−1)²` therefore never enters the budget.**

### `RHTower/HalfPlaneDecayVerticalIntegral.lean`

* `integral_exp_neg_le` — `∫_d^X K e^{-αx} dx ≤ K e^{-αd}/α`, with the explicit antiderivative.

* **`norm_integral_vertical_le_of_halfPlane_decay`** — for `F` analytic on `Re s ≥ d` with
  `‖F(s)‖ ≤ K e^{-α Re s}` there,

  ```text
  ‖∫_{T₁}^{T₂} F(d+it) dt‖  ≤  2 K e^{-αd} / α ,
  ```

  **independently of the window length**.  Proved by Cauchy's rectangle theorem
  (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) on `[d,X] × [T₁,T₂]` with the
  far-right edge pushed to infinity; the connecting vertical integral is `O((T₂−T₁)e^{-αX}) → 0`.

  Applied to `F = Log(GΨ)` this makes `∫ log‖GΨ(d+it)‖ dt` an `O(1)`; applied to
  `F = logDeriv (GΨ)` it makes the right-edge logarithmic-derivative term an `O(1)` as well.  These
  are the two `O(L)` losses that brick 7b showed to be fatal.

### `RHTower/LevinsonMollifiedEdges.lean`

`abs_im_two_div_sub_one_le`, `abs_integral_weighted_im_pole_le` (the `O(1/T)` pole-gauge horizontal
edge, kept as a cross-check), and `logDeriv_levinsonGEntire_mul`
(`logDeriv (G♯Ψ) = 2/(s−1) + logDeriv G + logDeriv Ψ`).

### Remaining consumer items

1. far-right decay of the mollified detector: `‖GΨ − 1‖ ≤ K e^{-α Re s}` on `Re s ≥ d`, hence
   `Log(GΨ)` analytic there with the same decay, and `logDeriv (GΨ)` by Cauchy on the unit disc;
2. the budget assembly: `weightedLittlewoodBoundary (GΨ) ≤ (L/2)·log(meanSquare/L) + O(1) + O(log T)`;
3. the mollified mean square itself (brick 5/6).

## Brick 7d — the far-right edge is closed (2026-09-01)

`RHTower/MollifiedDetectorFarRightDecay.lean` (axiom-clean, wired, built):

* `exp_neg_log_two_eq`, `norm_riemannZeta_sub_one_le_exp` (`‖ζ−1‖ ≤ 3·2^{-Re s}` for `Re s ≥ 2`),
  `norm_deriv_riemannZeta_le_exp` (`‖ζ′‖ ≤ 6·2^{-Re s}` for `Re s ≥ 3`, Cauchy on the unit disc),
  **`norm_levinsonG_sub_one_le_exp`** (`‖G−1‖ ≤ 9·2^{-Re s}`);
* `sum_rpow_neg_le_exp` — `∑_{n ∈ t, n ≥ 2} n^{-x} ≤ 11·2^{-x}` for `x ≥ 2`, from `hasSum_zeta_two`;
* **`norm_edPoly_sub_one_le_exp`** — a Dirichlet polynomial with unit head and coefficients bounded
  by `1` is `1 + O(2^{-Re z})`;
* `norm_mul_sub_one_le`, `norm_clog_le_of_norm_sub_one_le` (`‖Log w‖ ≤ 2‖w−1‖` for `‖w−1‖ ≤ ½`),
  `mem_slitPlane_of_norm_sub_one_le`.

`RHTower/MollifiedDetectorFarRightEdge.lean` (axiom-clean, wired, built):

* `analyticOnNhd_clog_comp`, `deriv_clog_comp` (`deriv (Log ∘ H) = logDeriv H`);
* **`abs_integral_log_norm_farRight_le`** —
  `|∫_{T₁}^{T₂} log‖H(d+it)‖ dt| ≤ 4K e^{-αd}/α`;
* **`abs_integral_re_logDeriv_farRight_le`** —
  `|∫_{T₁}^{T₂} Re (H′/H)(d+it) dt| ≤ 4K e^{α} e^{-αd}/α`,

both for `H` analytic on `Re s > d₀` with `‖H−1‖ ≤ K e^{-α Re s} ≤ ½` there.  **Neither bound
depends on the window length**, which is exactly what brick 7b showed to be necessary.

### The shift is absorbed into the coefficients

Levinson's mollifier is `ψ(s) = ∑_{h≤M} μ(h) P(·) h^{-(s + ½ − σ₀)}`, which looks like a *shifted*
Dirichlet polynomial and would force the horizontal-edge lemmas onto a translated segment.  It is
not necessary: writing `b_h = μ(h)P(·)·h^{σ₀ − ½}` gives `ψ = edPoly b (Icc 1 M)` **unshifted**, with

* `‖b_h‖ ≤ 1` (because `σ₀ < ½` and `h ≥ 1`), `b_1 = 1`, and `b` real when `P` is,
* `ψ(σ₀ + it) = ∑_{h≤M} μ(h)P(·) h^{-½-it}` — the classical mollifier on the Levinson line, exactly.

So every module of bricks 7a/7c/7d applies verbatim, on the segment `[σ₀, 4]` with the counting
disc centred at `4`.

## Brick 7e — THE CONSUMER CHAIN IS CLOSED (2026-09-01)

Levinson's method is now, in Lean, a single implication from the mollified mean square.

`RHTower/LevinsonLeftEdgeJensen.lean` — **`integral_log_norm_le_of_meanSquare`**: Jensen's left-edge
bound for a function merely analytic on the segment, with finitely many zeros there.

`RHTower/LevinsonMollifiedBudget.lean`:
* `levinsonMollifiedDetector lam b s = fun z => (ζ + λζ′)(z) · edPoly b s z`;
* `norm_levinsonMollifiedDetector_sub_one_le_exp` / `..._le_half` — `‖g − 1‖ ≤ 22·2^{-Re z} ≤ ½`
  on `Re z ≥ 6`;
* `norm_edPolyTrace_centre_ge` — `|Re Ψ(4+iT)| ≥ 5/16`, the centre value of the mollifier's Jensen
  disc, from head dominance;
* **`exists_levinson_mollified_budget_le`** — all four edges of `[σ₀, 15/2] × [T₁,T₂]`:

  ```text
  weightedLittlewoodBoundary g σ₀ (15/2) T₁ T₂
      ≤ ½(T₂−T₁)·log( Msq/(T₂−T₁) ) + C + K·( log T₂ + log Mb )
  ```

  with absolute constants `C, K`; `Msq` bounds the mean square of `g` on `Re s = σ₀` and `Mb` the
  `n⁴`-weighted `ℓ¹` mass of the mollifier coefficients.

`RHTower/LevinsonOddFiberFinal.lean`:
* `logDeriv_congr_of_eventuallyEq'`, **`weightedLittlewoodBoundary_congr`** — the boundary functional
  only sees an open neighbourhood of the rectangle, which is what identifies the entire `G♯·Ψ` with
  `(s−1)²·(G·Ψ)`;
* **`levinsonGEntire_zeroMass_le_boundary`** — the detector zero mass in `[½,4] × [T₁,T₂]` against
  the Littlewood boundary on `[σ₀,d] × [T₁,T₂]`, `d ≥ 4`;
* **`exists_le_xiOddFiberCount_of_mollified_meanSquare`** — the capstone:

  ```text
  ∃ cw C K > 0, ∀ λ < 0 with |λ| ≤ 1, ∀ mollifier (b, N) with b₁ = 1, ‖bₙ‖ ≤ 1, b real,
    ∀ Mb ≥ 1 bounding ∑ ‖bₙ‖ n⁴, ∀ σ₀ ∈ [¼,½), T₁ ≥ 20, T₂ > T₁ at admissible heights,
    ∫_{T₁}^{T₂} ‖(ζ+λζ′)·Ψ (σ₀+it)‖² dt ≤ Msq  →
    ∀ n, (n+2)π + π + (T₂−T₁)·6/T₁² + cw log T₁ + cw log T₂
           + [ ½(T₂−T₁)·log(Msq/(T₂−T₁)) + C + K(log T₂ + log Mb) ] / (½ − σ₀)
         ≤ θ(T₂) − θ(T₁)
      →  n ≤ xiOddFiberCount T₂ .
  ```

All axiom-clean (`propext, Classical.choice, Quot.sound`), wired into `RHTower.lean`, exact leaf
builds.

**What is left.**  Two items, in order of size.

1. *(small, consumer)* Turn the window count into the density statement: choose admissible heights,
   use `gammaHardyTheta T₂ − gammaHardyTheta T₁ ≈ π(N(T₂) − N(T₁))` and
   `exists_xiZeroCount_close`, and combine with `one_sub_log_levinsonLinearOptimizationConstant_div_gt_one_third`
   to get `∃ δ > 0, ∀ᶠ T, (1/3 + δ)·N(T) ≤ xiOddFiberCount T`, hence
   `liminf O/N > 1/3`, hence `liminf xiSimpleCriticalRatio > 0` (an odd fibre of multiplicity ≥ 3
   costs three zeros, so `N₀,s ≥ O − N/3`).
2. *(the gate)* The mollified mean square itself: `∫_{T₁}^{T₂} ‖(ζ+λζ′)Ψ(σ₀+it)‖² dt ≤ (c+o(1))·L`
   with `c = levinsonLinearOptimizationConstant`.  This is bricks 5c–5e / 6, the twisted second
   moment of `ζ` against the Levinson mollifier.  Nothing else in the programme is open.

## Brick 7f — THE WHOLE CONSUMER HALF IS CLOSED: one gate, both cards (2026-09-01)

Twenty-two axiom-clean modules landed today.  The programme is now a single implication.

### The gate, stated in Lean

`RHTower/LevinsonOddFiberDensity.lean` defines

```text
LevinsonMeanSquareGate (R c : ℝ) : Prop
```

— for every `ε > 0` and every sufficiently large `U` there are an admissible Levinson window
`[T₁,T₂]` with `T₁ ∈ [20,21]`, `T₂ ∈ (U−1, U]`, a real mollifier `(b, N)` with `b₁ = 1`,
`‖bₙ‖ ≤ 1`, an `n⁴`-mass bound `Mb` with `log Mb ≤ 5 log T₂`, and the Levinson abscissa
`σ₀ ∈ [¼,½)` with `(½−σ₀)·log T₂ = R`, such that

```text
∫_{T₁}^{T₂} ‖(ζ + λζ′)·edPoly b (Icc 1 N) (σ₀+it)‖² dt ≤ (c+ε)·(T₂−T₁).
```

### The chain from the gate

| step | Lean |
|---|---|
| Littlewood identity → zero mass | `exists_entire_zeroCount_le_boundary` |
| pole gauge cancels exactly | `weightedLittlewoodBoundary_poleGauge_mul`, `weightedLittlewoodBoundary_congr` |
| left edge from the mean square | `integral_log_norm_le_of_meanSquare` |
| far-right edges are `O(1)` | `abs_integral_log_norm_farRight_le`, `abs_integral_re_logDeriv_farRight_le` |
| horizontal edges are `O(log T + log Mb)` | `exists_horizontal_weighted_levinsonG_bound`, `abs_integral_weighted_im_logDeriv_edPoly_le` |
| the whole budget | `exists_levinson_mollified_budget_le` |
| budget → window count | `exists_le_xiOddFiberCount_of_mollified_meanSquare` |
| window count → proportion | `eventually_oddFiber_ge_of_gate` |
| odd fibres → simple critical zeros | `three_mul_xiOddFiberCount_le_simple` |
| **the two card gates** | `le_liminf_xiSimpleCriticalRatio_of_gate`, `le_liminf_xiSingletonFiberRatio_of_gate` |

Explicitly:

```text
0 < R,  1 ≤ c,  0 < δ,  1/3 + 2δ < 1 − log c / R,  LevinsonMeanSquareGate R c
   ⟹  δ ≤ liminf xiSimpleCriticalRatio atTop            (card 1's gate)
   ⟹  (3/2)·δ ≤ liminf xiSingletonFiberRatio atTop      (card 2's non-vacuity)
```

`one_sub_log_levinsonLinearOptimizationConstant_div_gt_one_third` already supplies a `c` and `R`
(`P(x)=x`, `Q(x)=1−x`, `R = 13/10`, `θ = 1/2`) with `1 − log c/R > 1/3`, so a `δ` exists as soon as
the gate does.

### Everything now open, in one line

```text
LevinsonMeanSquareGate (13/10) levinsonLinearOptimizationConstant
```

i.e. bricks 5c–5e/6: the mollified second moment of `ζ + λζ′` against the Levinson mollifier on the
abscissa `σ₀ = ½ − R/log T`.  Nothing else in this programme, and nothing else in either consumer
card except the exact PRZZ decimals, is open.

### Module list (all axiom-clean, wired, exact leaf builds)

`LevinsonLittlewoodZeroCount`, `EntireAdmissibleHeight`, `EntireDirichletPolynomial`,
`LevinsonDetectorZeroBudget`, `LevinsonOddFiberFromMeanSquare`, `EntireDirichletPolynomialTrace`,
`WeightedSegmentArgumentBound`, `EntireDirichletPolynomialHorizontalEdge`,
`LevinsonWeightedHorizontalEdge`, `LevinsonMollifiedEdges`, `LittlewoodPoleGaugeCancellation`,
`HalfPlaneDecayVerticalIntegral`, `MollifiedDetectorFarRightDecay`, `MollifiedDetectorFarRightEdge`,
`LevinsonLeftEdgeJensen`, `LevinsonMollifiedBudget`, `LevinsonOddFiberFinal`,
`LevinsonDensityScale`, `LevinsonOddFiberDensity`, `OddFiberSimpleCharging`,
`LevinsonProportionGate` (plus endpoint generalizations of the two horizontal-edge modules).

## Brick 5ba — STRATEGIC FINDING: at `θ < 1/2` the mean square needs neither Montgomery–Vaughan
## nor Balasubramanian–Conrey–Heath-Brown (2026-09-01)

The programme has been treating the mollified second moment as a formalization of BCHB (twisted
second moment of `ζ` with a power-saving error uniform for `h,k ≤ T^θ`).  That is the right frame
for `θ = 4/7` (Conrey/PRZZ), but it is **not** needed for Levinson's own `θ < 1/2`, which is all the
two consumer cards require.  Three separate places where the programme expected a hard input turn
out to be elementary at `θ < 1/2`.

Throughout: `x = y ≍ √(t/2π)` are the AFE cutoffs, `M = T^θ` the mollifier length, so every
Dirichlet polynomial in sight has length `N ≍ x·M ≍ T^{1/2+θ}`, and the mollified coefficient energy
`∑_n |c_n|²` is **bounded** (that is what mollification buys).

**1. The direct×direct term needs only the corpus's own mean-value theorem.**
`RHTower/Sieve/DirichletMVT.dirichlet_meanValue_theorem` gives

```text
| ∫_0^T |∑_{n<N} c_n n^{it}|² dt − T·∑|c_n|² |  ≤  4N(1+log N)·∑|c_n|² .
```

Its own doc comment records that the sharp Montgomery–Vaughan error `O(N)` is not owned, needing a
Hilbert inequality at the frequencies `log n`.  **It is not needed.**  Because the error is
*proportional to `∑|c_n|²`*, which is `O(1)` after mollification, the total error is
`≍ T^{1/2+θ} log T = o(T)` for every fixed `θ < 1/2`.  So `smoothAFEZetaDisplacedDirectMollified_meanValue_window`
already closes the direct×direct term completely — diagonal *and* off-diagonal — with no
BCHB-style off-diagonal analysis at all.

**2. The cross term has no stationary point, and the first-derivative test suffices.**
The cross term is

```text
2 Re ∫ conj(χ(σ₀+it))·(AΨ)(t)·conj((B̃Ψ)(t)) dt
   = 2 Re ∑_{m ≤ xM} ∑_{n ≤ yM} e_m conj(f_n) ∫ exp( i( t log(t/2πe) + t log(n/m) ) ) dt .
```

The phase derivative is `log( t n / (2π m) )`, so the stationary point is `t = 2π m/n`, and it lies
in the window only if `t/2π ≤ xM ≍ √(t/2π)·T^θ`, i.e. only if `t ≤ 2π T^{2θ}`.  **For fixed
`θ < 1/2` and `t ≍ T` that never happens.**  Moreover the derivative is then bounded below by

```text
| log( t n / (2π m) ) |  ≥  (1/2 − θ) log T − O(1),
```

so the first-derivative (van der Corput) test — which the corpus owns — gives each oscillatory
integral `≪ 1/((1/2−θ) log T)` and hence a total

```text
≪ ( ∑_m |e_m| )( ∑_n |f_n| ) / ((1/2−θ) log T)  ≍  T^{1/2+θ} log T  =  o(T).
```

**No stationary phase, no Ramanujan/Kloosterman sums, no saddle-point evaluation.**  (This is the
precise sense in which brick 5aw's "the cross must be evaluated" was an artefact: it is an artefact
of the *symmetric* split *and* of pushing `θ` to `4/7`.  At `θ < 1/2` the cross is genuinely an
error term for the elementary reason that its saddle has left the window.)

**3. The dual×dual term is the direct term with an explicit slowly varying weight.**
`|χ(σ₀+it)|² = (t/2π)^{2(1/2−σ₀)} = (t/2π)^{2R/log T}`, which is exactly the `e^{2Rv}` of Young's
constant after the substitution `v = log(t)/log T`.  The polynomial factor is handled by the same
mean-value theorem; the weight is handled by partial summation in `t` (or by the block splitting of
item 4), producing the `∫_0^1 e^{2Rv}·(…) dv` of `levinsonLinearOptimizationConstant`.

**4. The moving AFE cutoff is handled by block freezing, which the corpus already owns.**
`SmoothAFEZetaDisplacedReflectedCombinedFreezingMeanSquare` and the moving/frozen decomposition of
2026-08-25 are exactly this.  Splitting `[T₁,T₂]` into `O(1/Δ)` blocks `[T, (1+Δ)T]` and freezing
the cutoff on each costs `O(Δ)` relative error, which `Δ → 0` removes.

### Revised gate list (replacing the BCHB-shaped one of brick 5az)

| # | item | state |
|---|---|---|
| 1 | exact smooth AFE at every split | **owned** (`SmoothAFEZetaDualReflection`, `SmoothAFEZetaGeneral`) |
| 2 | direct×direct mollified mean square | **owned** (`smoothAFEZetaDisplacedDirectMollified_meanValue_window`) |
| 3 | mollified coefficient energy (short + long) | arithmetic layer **closed**; the long-tail asymptotic is the remaining arithmetic item |
| 4 | cross term `o(T)` by the first-derivative test | to build — the phase-derivative lower bound `(1/2−θ)log T − O(1)` plus the corpus's van der Corput test |
| 5 | dual×dual with the `(t/2π)^{2R/log T}` weight | to build — mean value + partial summation |
| 6 | block freezing of the moving cutoff | machinery **owned**, assembly to build |
| 7 | assembly to `levinsonLinearOptimizationConstant` and `LevinsonMeanSquareGate` | to build |

**Nothing in this list requires Montgomery–Vaughan, a Hilbert inequality, Deshouillers–Iwaniec, or
Kloosterman-sum cancellation.**  Those are needed only for the PRZZ decimals (`θ = 4/7`), i.e. only
for the *advertised constant* of `horizontal-singleton-zero-fibers`, not for either card's gate.

## Brick 5bb — the cross term's two ingredients are Lean (2026-09-01)

`RHTower/DirichletCrossOscillatoryBound.lean` (axiom-clean, wired, exact leaf build):

* **`norm_integral_dirichletCross_cexp_le`** — the general oscillatory cross estimate.  For two
  finite Dirichlet polynomials and a real phase `g` with `g′` nondecreasing and every combined
  frequency `g′(x) + log n − log m` bounded below by `lam > 0`,

  ```text
  ‖ ∫_a^b (∑_{m∈S} eₘ m^{-iτ}) · conj(∑_{n∈T} fₙ n^{-iτ}) · e^{i g(τ)} dτ ‖
        ≤ (∑ ‖eₘ‖)(∑ ‖fₙ‖) · 2/lam .
  ```

  Proved by expanding into the `#S·#T` pure oscillations `exp(i(g(τ) + τ(log n − log m)))` and
  applying the corpus's first-derivative test `norm_integral_cexp_ofReal_mul_I_le_mono` to each.

* **`log_freq_lower_bound`** — the arithmetic input, i.e. *the saddle has left the window*:

  ```text
  1 ≤ m,  1 ≤ n,  m ≤ x,  0 < K,  2π·x·K ≤ τ
      ⟹  log K ≤ log(τ/2π) + (log n − log m).
  ```

  With `x ≍ T^{1/2+θ}` (AFE head times mollifier) and `τ ≍ T` this gives `K ≍ T^{1/2−θ}`, hence
  `lam ≍ (1/2 − θ)·log T`, and the cross term is

  ```text
  ≪ (∑‖e‖)(∑‖f‖)/((1/2−θ) log T)  ≍  T^{1/2+θ} log T  =  o(T)   for every fixed θ < 1/2.
  ```

Item 4 of the revised gate list (brick 5ba) is therefore reduced to *identifying the corpus's
archimedean phase* `g` (the Riemann–Siegel phase carried by `χ`, i.e. `2·gammaHardyTheta` up to the
displacement) and checking its two derivative hypotheses — `g′` nondecreasing and
`g′(τ) = log(τ/2π) + O(1/τ²)` — both of which the corpus already owns in
`HardyZPhaseAsymptotic` (`deriv_gammaHardyTheta`, `deriv_deriv_gammaHardyTheta`,
`gammaHardyPhaseRate_sub_log_conductor_tendsto_zero`).

## Brick 5bc — the archimedean cross and the weighted transfer are Lean (2026-09-01)

`RHTower/ArchimedeanCrossPhase.lean` (axiom-clean, wired, exact leaf build):

* **`norm_integral_archimedeanCross_le`** — the cross term of the mollified second moment, with the
  Riemann–Siegel phase `2·gammaHardyTheta` supplied concretely:

  ```text
  4 ≤ a ≤ b,  every direct index ≤ x,  every dual index ≥ 1,  2π·x·K ≤ a,
  0 < log K − (33/(8a²) + π/a)
    ⟹ ‖∫_a^b (∑ eₘ m^{-iτ})·conj(∑ fₙ n^{-iτ})·e^{2iθ(τ)} dτ‖
         ≤ (∑‖e‖)(∑‖f‖)·2/(log K − (33/(8a²) + π/a)).
  ```

  The phase hypotheses are discharged from the corpus's own Riemann–Siegel jets:
  `hasDerivAt_gammaHardyTheta`, `hasDerivAt_gammaHardyPhaseRate`,
  `continuous_deriv_gammaHardyPhaseRate`, `deriv_gammaHardyPhaseRate_pos` (so `θ′` is increasing),
  and the quantitative velocity law `gammaHardyPhaseRate_sub_log_conductor_bound`
  (`|θ′(t) − ½log(t/2π)| ≤ 33/(16t²) + π/(2t)`).

  **Item 4 of the revised gate list is closed in reusable form.**

`RHTower/WeightedMeanSquareTransfer.lean` (axiom-clean, wired, exact leaf build):

* **`abs_integral_weighted_meanSquare_sub_le`** — transfer of a mean-square asymptotic through a
  smooth increasing weight, by one integration by parts:

  ```text
  |∫_a^u ‖D‖² − (u−a)·M| ≤ E  for every u ∈ [a,b],   w′ ≥ 0,  w(a) ≥ 0
     ⟹ |∫_a^b w·‖D‖² − M·∫_a^b w| ≤ E·(2w(b) − w(a)).
  ```

  This is item 5's mechanism: with `w(t) = |χ(σ₀+it)|² = (t/2π)^{2R/log T}` it converts the constant
  `∑|c_n|²` of the dual polynomial into `∑|c_n|²·∫ (t/2π)^{2R/log T} dt`, which after `v = log t/log T`
  is Young's `∫_0^1 e^{2Rv} dv` factor.

`RHTower/WeightedMeanSquareTransfer.lean` also carries the weight itself:
`chiModulusWeight α t = (t/2π)^α`, `chiModulusWeight_pos`, **`hasDerivAt_chiModulusWeight`**
(`w′(t) = (α/t)·w(t)`, so `w′ ≥ 0` for `α ≥ 0` — the monotonicity the transfer needs) and
`continuousOn_deriv_chiModulusWeight`.  With `α = 2(1/2 − σ₀) = 2R/log T` this is exactly
`|χ(σ₀+it)|²`.

### State of the revised gate list after bricks 5ba–5bc

| # | item | state |
|---|---|---|
| 1 | exact smooth AFE at every split | **owned** |
| 2 | direct×direct mollified mean square | **owned** |
| 3 | mollified coefficient energy: short range | **owned**; long-tail asymptotic open |
| 4 | cross term `o(T)` | **CLOSED** (`norm_integral_archimedeanCross_le`) |
| 5 | dual×dual with the `χ`-modulus weight | mechanism **CLOSED** (`abs_integral_weighted_meanSquare_sub_le`, `chiModulusWeight`); instantiation open |
| 6 | block freezing of the moving cutoff | machinery owned; assembly open |
| 7 | assembly to `LevinsonMeanSquareGate` | open |

## Brick 5bd — the assembly skeleton (2026-09-01)

`RHTower/MeanSquareSplit.lean` (axiom-clean, wired, exact leaf build):

* **`integral_normSq_add_le_of_cross`** — the two-term split
  `∫‖D₁+D₂‖² ≤ P₁ + P₂ + 2X` from mean-square bounds `P₁, P₂` and a cross bound `X`.  This is the
  shape into which `smoothAFEZetaDisplacedDirectMollified_meanValue_window` (direct),
  `abs_integral_weighted_meanSquare_sub_le` + `chiModulusWeight` (dual) and
  `norm_integral_archimedeanCross_le` (cross) plug.
* **`integral_normSq_add_le_young`** — absorption of a small perturbation,
  `∫‖D+E‖² ≤ (1+η)P + (1+1/η)Q`.  The approximate-functional-equation error and the pole residue
  have mean square `o(L)`, so they cost only `η` of relative loss and `η → 0` removes it.

With these, items 4, 5 and the splitting half of item 7 are mechanised.  What is left for the gate:

* **item 3** — the sharp mollified coefficient energy over the *full* product range
  `∑_{n ≤ xM} |cₙ|² = ∑_{n ≤ xM} λₙ²/n + …`, i.e. Graham's harmonic-weighted Barban–Vehov
  asymptotic.  The corpus owns the Selberg diagonal sharply
  (`tendsto_barbanVehovSelbergDiagonal_div_log_one`, both halves) and the harmonic-weighted upper
  bound `sum_harmonic_sq_barbanVehovCoeff_le`, but the latter carries a `(1+2log X)(X log X)²`
  defect that is only `o(L)` once `N ≫ X²`; the sharp version over `M < n ≤ xM` is the open item.
* **item 6** — the block freezing of the moving AFE cutoff.
* **item 7** — plugging items 2–6 into `LevinsonMeanSquareGate`.

## Brick 5be — CORRECTION: item 3 is further along than the 2026-08-26 note said (2026-09-01)

The status line of 2026-08-26 ("growing-modulus upper control, differentiated full/omitted long
tails … remain required") is **stale**.  A re-audit of the tree shows both halves of the long-range
energy are already Lean theorems, and — crucially — the error term vanishes *exactly* in the range
`θ < 1/2` that the two consumer cards need.

**The long energy is approximated by an explicit polynomial main, with a `θ < 1/2` error.**
`RHTower/Sieve/DifferentiatedBarbanVehovIncludedEnergy.abs_levinsonCriticalDetectorLongEnergy_sub_includedPolynomialMain_le`:
for `1 < M` and `8M² ≤ L`,

```text
| levinsonCriticalDetectorLongEnergy λ L M − barbanVehovIncludedLongEnergyPolynomialMain λ (log L) M |
     ≤ ( M²log²M·(3/L + 12|λ|·log(LM+1)/L + 12λ²·log²(LM+1)/L) ) / log²M .
```

With the Levinson scaling `L ≍ T^{1/2+θ}` (AFE head × mollifier), `M = T^θ`, `|λ| ≍ 1/log T`:

* the hypothesis `8M² ≤ L` reads `8T^{2θ} ≤ T^{1/2+θ}`, i.e. `θ ≤ 1/2 − log 8/log T` — satisfied
  for every fixed `θ < 1/2` and `T` large;
* the `log²M` cancels, `|λ|log(LM)` and `λ²log²(LM)` are `O(1)`, so the whole error is
  `≍ M²/L = T^{θ−1/2} → 0`.

**The polynomial main has an exact limit.**
`DifferentiatedBarbanVehovTunedMinLogAsymptotic.tendsto_barbanVehovIncludedLongEnergyPolynomialMain_tuned_rho`
gives the limit `ρ²/12` (the ordinary `−ρ²/2` channel plus the Gram contribution `7ρ²/12`), and
`barbanVehovIncludedLongEnergyPolynomialMain_eq_ordinary_add_tunedRemainder` supplies the identity
behind it.  The short range already had
`tendsto_levinsonLinearMollifiedCriticalDetector_energy : ∑_{k≤M} ‖c_k‖² → 1 + (1−r)²/2 + r²/12`.

**Revised assessment.**  Item 3 is not an open sieve-theoretic problem; it is an *assembly* problem —
combining the short limit, the long limit and the `θ < 1/2` error into one statement about
`∑_{n ≤ LM} |c_n|²`, and matching the result against `levinsonLinearOptimizationConstant`.

### The gate list as it now stands

| # | item | state |
|---|---|---|
| 1 | exact smooth AFE at every split | **owned** |
| 2 | direct×direct mollified mean square | **owned** |
| 3 | mollified coefficient energy, short + long + error | **owned in pieces**; single-statement assembly open |
| 4 | cross term `o(T)` | **CLOSED** (brick 5bc) |
| 5 | dual×dual with the `χ`-modulus weight | mechanism **CLOSED** (brick 5bc) |
| 6 | block freezing of the moving AFE cutoff | machinery owned; assembly open |
| 7 | `LevinsonMeanSquareGate` | splitting mechanised (brick 5bd); assembly open |

**Every remaining item is assembly, not new mathematics.**  That is the honest state of the gate.

## Brick 5bf — the total mollified coefficient energy in one statement (2026-09-01)

`RHTower/LevinsonTotalEnergy.lean` (axiom-clean, wired, exact leaf build):

* `abs_levinsonCriticalDetectorTotalEnergy_sub_le` — composes the exact short/long split
  (`sum_levinsonCriticalDetectorFiniteEnergyTerm_eq_short_add_long`) with the long-range polynomial
  approximation, giving one statement about the **total** energy `∑_{r < LM} |c_r|²`;
* `levinsonTotalEnergy_error_le_of_lam_small` — the error collapses: whenever
  `|λ|·log(LM+1) ≤ 1` (true at Levinson's `λ ≍ 1/log T`), the whole error is at most `27·M²/L`;
* **`abs_levinsonCriticalDetectorTotalEnergy_sub_le_sq_div`** —

  ```text
  1 < M,  8M² ≤ L,  |λ|·log(LM+1) ≤ 1
     ⟹ | ∑_{r<LM}|c_r|²  −  ( ∑_{k≤L}‖c_k‖²  +  barbanVehovIncludedLongEnergyPolynomialMain λ (log L) M ) |
          ≤ 27·M²/L .
  ```

At the Levinson scaling `L ≍ T^{1/2+θ}`, `M = T^θ` this error is `≍ T^{θ−1/2} → 0` for every fixed
`θ < 1/2`, and the hypothesis `8M² ≤ L` is exactly that same condition.  **Item 3 of the gate list
is now a single quantitative theorem**; what remains of it is only to feed in the two evaluated
limits (`tendsto_levinsonLinearMollifiedCriticalDetector_energy` for the short range,
`tendsto_barbanVehovIncludedLongEnergyPolynomialMain_tuned_rho` for the long) at matched parameters.
