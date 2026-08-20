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
