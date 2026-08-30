import GaloisForLFunctions.RHTower.XiSimpleCriticalExponentialTypeBound

/-!
# The superlinear consumer for the bounded-support Weil tail

`XiSimpleCriticalExponentialTypeBound` proves the *upper* half of the
`bounded-support-weil-critical-tail-uniqueness` card: a nonzero compactly supported `L²` datum whose
Fourier transform vanishes at all but finitely many simple critical ordinates forces

`xiSimpleCriticalZeroCount T ≤ K(1+T) + #E`.

This file closes the consumer side: any superlinear lower bound `c·T·log T ≤ N₀,s(T)` contradicts
that, so the Fourier transform — and hence the compactly supported source itself — vanishes
identically.

After this file the card is blocked on exactly one unconditional statement, the superlinear
provider, which is owned by
`docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`.
-/

noncomputable section

open Complex Filter Topology

namespace RHTower

/-- A linear upper bound and a superlinear lower bound for the same counting function are
incompatible. -/
theorem not_linear_bound_of_superlinear
    {c K m : ℝ} (hc : 0 < c) {F : ℝ → ℝ}
    (hsuper : ∀ᶠ T : ℝ in atTop, c * T * Real.log T ≤ F T)
    (hlin : ∀ T : ℝ, 1 ≤ T → F T ≤ K * (1 + T) + m) : False := by
  set B : ℝ := 2 * |K| + |m| with hB
  have hlogTop : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hbig : ∀ᶠ T : ℝ in atTop, B / c < Real.log T :=
    hlogTop.eventually_gt_atTop (B / c)
  obtain ⟨T, hsuperT, hbigT, hT1⟩ :=
    (hsuper.and (hbig.and (eventually_ge_atTop (1 : ℝ)))).exists
  have hTpos : (0 : ℝ) < T := by linarith
  have hlogpos : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlin' : F T ≤ K * (1 + T) + m := hlin T hT1
  have hKle : K * (1 + T) + m ≤ B * T := by
    have hKabs : K ≤ |K| := le_abs_self K
    have hmabs : m ≤ |m| := le_abs_self m
    have hKnn : 0 ≤ |K| := abs_nonneg K
    have hmnn : 0 ≤ |m| := abs_nonneg m
    rw [hB]
    nlinarith [hKabs, hmabs, hKnn, hmnn, hT1]
  have hstep : c * T * Real.log T ≤ B * T := by linarith
  have hstep' : (c * Real.log T) * T ≤ B * T := by
    have hcomm : (c * Real.log T) * T = c * T * Real.log T := by ring
    rw [hcomm]
    exact hstep
  have hdiv : c * Real.log T ≤ B := le_of_mul_le_mul_right hstep' hTpos
  rw [div_lt_iff₀ hc] at hbigT
  linarith

/-- **The compact Fourier transform vanishes identically once the simple critical count is
superlinear.** -/
theorem suzukiCompactL2Fourier_eq_zero_of_superlinear_simpleCritical
    {c : ℝ} (hc : 0 < c)
    (hsuper : ∀ᶠ T : ℝ in atTop,
      c * T * Real.log T ≤ (xiSimpleCriticalZeroCount T : ℝ))
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        suzukiCompactL2Fourier a f (t : ℂ) = 0) :
    suzukiCompactL2Fourier a f = 0 := by
  by_contra hFne
  obtain ⟨K, hK, hlin⟩ :=
    exists_xiSimpleCriticalZeroCount_linear_of_cofinite_suzukiFourier_zeros ha f hFne E hvanish
  exact not_linear_bound_of_superlinear hc hsuper hlin

/-- **The compactly supported source vanishes once the simple critical count is superlinear.**
This is the `bounded-support-weil-critical-tail-uniqueness` card's theorem, with its single
remaining analytic input made explicit. -/
theorem suzukiCutoff_eq_zero_of_superlinear_simpleCritical
    {c : ℝ} (hc : 0 < c)
    (hsuper : ∀ᶠ T : ℝ in atTop,
      c * T * Real.log T ≤ (xiSimpleCriticalZeroCount T : ℝ))
    {a : ℝ} (ha : 0 ≤ a) (f : SoninL2) (E : Finset ℝ)
    (hvanish : ∀ t : ℝ, t ∉ E → 0 < t → xi (linePt t) = 0 →
      (analyticOrderAt xi (linePt t)).toNat = 1 →
        suzukiCompactL2Fourier a f (t : ℂ) = 0) :
    suzukiCutoff a f = 0 :=
  suzukiCutoff_eq_zero_of_compactFourier_eq_zero ha f
    (suzukiCompactL2Fourier_eq_zero_of_superlinear_simpleCritical hc hsuper ha f E hvanish)

end RHTower
