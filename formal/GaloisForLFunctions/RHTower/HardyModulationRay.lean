import GaloisForLFunctions.RHTower.HardyBlaschkeMultiplier
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation

noncomputable section

/-!
# The modulated Hardy space

The Fourier image of `L²(t,∞)` is the Hardy space multiplied by the inner function
`ξ ↦ e^{2πitξ}`.  Its Cauchy transform is the Cauchy transform of the underlying Hardy function
scaled by the value of that inner function at the point:

```text
∫ e^{2πitx} H(x)/(x - w) dx = e^{2πitw} ∫ H(x)/(x - w) dx.
```

The difference of the two integrands is the divided slope of `e^{2πitz}` at `w` times `H`, and that
divided slope is itself a Hardy function — entire, and `O(1/|z|)` on the closed upper half-plane
because the modulation is bounded there for `t ≥ 0`.  A Hardy function annihilates a Hardy function
under the bilinear pairing.

Consequently the modulated space sits inside the Hardy space, is stable under the inner Blaschke
factor, and is stable under the Blaschke symbol at a point where the Cauchy transform vanishes.
-/

open MeasureTheory Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The entire modulation `z ↦ e^{2πi t z}`. -/
def modulationEntire (t : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * (t : ℂ) * z * I)

theorem modulationEntire_ofReal (t ξ : ℝ) :
    modulationEntire t ((ξ : ℝ) : ℂ) = modulationSymbol t ξ := by
  rw [modulationEntire, modulationSymbol]
  congr 1
  push_cast
  ring

theorem differentiable_modulationEntire (t : ℝ) : Differentiable ℂ (modulationEntire t) := by
  unfold modulationEntire
  fun_prop

theorem modulationEntire_ne_zero (t : ℝ) (z : ℂ) : modulationEntire t z ≠ 0 :=
  Complex.exp_ne_zero _

theorem norm_modulationEntire (t : ℝ) (z : ℂ) :
    ‖modulationEntire t z‖ = Real.exp (-(2 * Real.pi * t * z.im)) := by
  rw [modulationEntire, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_modulationEntire_le_one {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖modulationEntire t z‖ ≤ 1 := by
  rw [norm_modulationEntire, ← Real.exp_zero]
  refine Real.exp_le_exp.mpr ?_
  have hpi := Real.pi_pos
  have : (0 : ℝ) ≤ 2 * Real.pi * t * z.im := by positivity
  linarith

/-! ## The divided modulation slope -/

/-- The divided slope of the modulation at a point off the axis: an entire function decaying on the
closed upper half-plane. -/
def modulationSlope (t : ℝ) (w z : ℂ) : ℂ := dslope (modulationEntire t) w z

theorem differentiable_modulationSlope (t : ℝ) (w : ℂ) :
    Differentiable ℂ (modulationSlope t w) := by
  have h : Differentiable ℂ (dslope (modulationEntire t) w) := by
    rw [← differentiableOn_univ]
    refine (Complex.differentiableOn_dslope (by simp)).mpr ?_
    exact (differentiable_modulationEntire t).differentiableOn
  exact h

theorem modulationSlope_of_ne {t : ℝ} {w z : ℂ} (h : z ≠ w) :
    modulationSlope t w z = (modulationEntire t z - modulationEntire t w) / (z - w) := by
  rw [modulationSlope, dslope_of_ne _ h, slope_def_field]

theorem norm_modulationSlope_le {t : ℝ} (ht : 0 ≤ t) {w z : ℂ} (hz : 0 ≤ z.im) (h : z ≠ w) :
    ‖modulationSlope t w z‖ ≤ (1 + ‖modulationEntire t w‖) / ‖z - w‖ := by
  have hpos : (0 : ℝ) < ‖z - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  rw [modulationSlope_of_ne h, norm_div]
  gcongr
  refine le_trans (norm_sub_le _ _) ?_
  linarith [norm_modulationEntire_le_one ht hz]

theorem memLp_modulationSlope {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w.im ≠ 0) :
    MemLp (fun x : ℝ => modulationSlope t w ((x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hne : ∀ x : ℝ, ((x : ℝ) : ℂ) ≠ w := fun x h => hw (by rw [← h]; simp)
  refine memLp_two_of_poisson_bound (a := w.re) (b := |w.im|)
    (D := (1 + ‖modulationEntire t w‖) ^ 2) (abs_pos.mpr hw) ?_ ?_
  · exact ((differentiable_modulationSlope t w).continuous.comp
      Complex.continuous_ofReal).aestronglyMeasurable
  · intro x
    have him : (0 : ℝ) ≤ (((x : ℝ) : ℂ)).im := by simp
    have hb := norm_modulationSlope_le ht him (hne x)
    have hden : ‖((x : ℝ) : ℂ) - w‖ ^ 2 = (x - w.re) ^ 2 + |w.im| ^ 2 := by
      rw [norm_sq_ofReal_sub, sq_abs]
    have hpos : (0 : ℝ) < ‖((x : ℝ) : ℂ) - w‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (hne x))
    have hnn : (0 : ℝ) ≤ 1 + ‖modulationEntire t w‖ := by positivity
    rw [← hden, le_div_iff₀ (by positivity)]
    have hb' : ‖modulationSlope t w ((x : ℝ) : ℂ)‖ * ‖((x : ℝ) : ℂ) - w‖
        ≤ 1 + ‖modulationEntire t w‖ := (le_div_iff₀ hpos).mp hb
    have hprodnn : (0 : ℝ) ≤ ‖modulationSlope t w ((x : ℝ) : ℂ)‖ * ‖((x : ℝ) : ℂ) - w‖ := by
      positivity
    have hsq := mul_self_le_mul_self hprodnn hb'
    nlinarith [hsq]

theorem modulationSlope_mem_hardyL2 {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : w.im ≠ 0) :
    (memLp_modulationSlope ht hw).toLp _ ∈ hardyL2 := by
  refine mem_hardyL2_of_upperHalfPlane_decay
    (u := modulationSlope t w) (M := 2 * (1 + ‖modulationEntire t w‖))
    (R := 2 * ‖w‖ + 1) (fun z _ => (differentiable_modulationSlope t w) z) (by positivity) ?_ _
  intro z hz hzR
  have hzw : z ≠ w := by
    intro h
    rw [h] at hzR
    linarith [norm_nonneg w]
  have hzn : (0 : ℝ) < ‖z‖ := by linarith [norm_nonneg w]
  have hhalf : ‖z‖ / 2 ≤ ‖z - w‖ := by
    have h := norm_sub_norm_le z w
    linarith
  have hb := norm_modulationSlope_le ht hz hzw
  have hnn : (0 : ℝ) ≤ 1 + ‖modulationEntire t w‖ := by positivity
  refine le_trans hb ?_
  rw [div_le_div_iff₀ (by linarith) hzn]
  nlinarith

/-! ## The modulated Cauchy transform -/

/-- **Modulation shifts the Cauchy transform by the value of the modulation.**  The divided slope of
the modulation is a Hardy function, so it annihilates every Hardy function under the bilinear
pairing, and what is left is the constant `e^{2πitw}`. -/
theorem integral_modulationMul_cauchy {t : ℝ} (ht : 0 ≤ t)
    {H : Lp ℂ 2 (volume : Measure ℝ)} (hH : H ∈ hardyL2) {w : ℂ} (hw : w.im ≠ 0) :
    (∫ x : ℝ, (modulationMul t H : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w))
      = modulationEntire t w * ∫ x : ℝ, (H : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w) := by
  have hne : ∀ x : ℝ, ((x : ℝ) : ℂ) ≠ w := fun x h => hw (by rw [← h]; simp)
  set U : Lp ℂ 2 (volume : Measure ℝ) := (memLp_modulationSlope ht hw).toLp
    (fun x : ℝ => modulationSlope t w ((x : ℝ) : ℂ)) with hUdef
  have hUmem : U ∈ hardyL2 := modulationSlope_mem_hardyL2 ht hw
  have hstar : star U ∈ hardyL2ᗮ := by
    rw [← map_star_hardyL2]
    exact ⟨U, hUmem, rfl⟩
  have hinner : (inner ℂ (star U) H : ℂ) = 0 :=
    inner_eq_zero_symm.mp (Submodule.mem_orthogonal _ _ |>.mp hstar H hH)
  have hzero : (∫ x : ℝ, modulationSlope t w ((x : ℝ) : ℂ) * (H : ℝ → ℂ) x) = 0 := by
    rw [← hinner, MeasureTheory.L2.inner_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.Lp.coeFn_star U, (memLp_modulationSlope ht hw).coeFn_toLp]
      with x h1 h2
    rw [RCLike.inner_apply, h1, Pi.star_apply, h2]
    show modulationSlope t w ((x : ℝ) : ℂ) * (H : ℝ → ℂ) x
      = (H : ℝ → ℂ) x * (starRingEnd ℂ) (star (modulationSlope t w ((x : ℝ) : ℂ)))
    rw [starRingEnd_apply, star_star, mul_comm]
  have hint1 : Integrable (fun x : ℝ =>
      modulationSlope t w ((x : ℝ) : ℂ) * (H : ℝ → ℂ) x) volume :=
    (memLp_modulationSlope ht hw).integrable_mul (MeasureTheory.Lp.memLp H)
  have hint2 := integrable_lp_div_sub hw H
  have hae : (fun x : ℝ => (modulationMul t H : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w))
      =ᵐ[volume] fun x : ℝ =>
        modulationSlope t w ((x : ℝ) : ℂ) * (H : ℝ → ℂ) x
          + modulationEntire t w * ((H : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) := by
    filter_upwards [coeFn_modulationMul t H] with x h
    rw [h, modulationSlope_of_ne (hne x), ← modulationEntire_ofReal t x]
    have hsub : ((x : ℝ) : ℂ) - w ≠ 0 := sub_ne_zero.mpr (hne x)
    field_simp
    ring
  rw [MeasureTheory.integral_congr_ae hae,
    MeasureTheory.integral_add hint1 (hint2.const_mul _),
    MeasureTheory.integral_const_mul, hzero, zero_add]

/-! ## The modulated Hardy space -/

/-- The Fourier image of `L²(t,∞)`: the Hardy space modulated by `e^{2πitξ}`. -/
def hardyRay (t : ℝ) : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  Submodule.map (modulationMul t).toLinearMap hardyL2

theorem mem_hardyRay_iff (t : ℝ) (G : Lp ℂ 2 (volume : Measure ℝ)) :
    G ∈ hardyRay t ↔ modulationMul (-t) G ∈ hardyL2 := by
  constructor
  · rintro ⟨H, hH, rfl⟩
    show modulationMul (-t) (modulationMul t H) ∈ hardyL2
    rw [modulationMul_neg_modulationMul]
    exact hH
  · intro h
    refine ⟨modulationMul (-t) G, h, ?_⟩
    show modulationMul t (modulationMul (-t) G) = G
    rw [modulationMul_modulationMul, add_neg_cancel, modulationMul_zero_apply]

theorem hardyRay_zero : hardyRay 0 = hardyL2 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨H, hH, rfl⟩
    show modulationMul 0 H ∈ hardyL2
    rw [modulationMul_zero_apply]
    exact hH
  · intro G hG
    refine ⟨G, hG, ?_⟩
    show modulationMul 0 G = G
    rw [modulationMul_zero_apply]

theorem hardyRay_le_hardyL2 {t : ℝ} (ht : 0 ≤ t) : hardyRay t ≤ hardyL2 := by
  rintro _ ⟨H, hH, rfl⟩
  show modulationMul t H ∈ hardyL2
  refine mem_hardyL2_of_cauchyTransform_eq_zero ?_
  intro v hv
  rw [integral_modulationMul_cauchy ht hH (ne_of_lt hv),
    integral_cauchyTransform_eq_zero hH hv, mul_zero]

/-! ## Blaschke stability of the modulated Hardy space -/

theorem modulationMul_blaschkeMul (t : ℝ) (w : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modulationMul t (blaschkeMul w f) = blaschkeMul w (modulationMul t f) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_modulationMul t (blaschkeMul w f), coeFn_blaschkeMul w f,
    coeFn_blaschkeMul w (modulationMul t f), coeFn_modulationMul t f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

theorem modulationMul_blaschkeMulInv (t : ℝ) (w : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    modulationMul t (blaschkeMulInv w f) = blaschkeMulInv w (modulationMul t f) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [coeFn_modulationMul t (blaschkeMulInv w f), coeFn_blaschkeMulInv w f,
    coeFn_blaschkeMulInv w (modulationMul t f), coeFn_modulationMul t f] with x h1 h2 h3 h4
  rw [h1, h2, h3, h4]
  ring

theorem blaschkeMulInv_mem_hardyRay {t : ℝ} {w : ℂ} (hw : 0 < w.im)
    {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ∈ hardyRay t) :
    blaschkeMulInv w G ∈ hardyRay t := by
  rw [mem_hardyRay_iff] at hG ⊢
  rw [modulationMul_blaschkeMulInv]
  exact blaschkeMulInv_mem_hardyL2 hw hG

theorem blaschkeMul_mem_hardyRay {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 < w.im)
    {G : Lp ℂ 2 (volume : Measure ℝ)} (hG : G ∈ hardyRay t)
    (hzero : (∫ x : ℝ, (G : ℝ → ℂ) x / (((x : ℝ) : ℂ) - w)) = 0) :
    blaschkeMul w G ∈ hardyRay t := by
  rw [mem_hardyRay_iff] at hG ⊢
  rw [modulationMul_blaschkeMul]
  refine blaschkeMul_mem_hardyL2 hw hG ?_
  have hGeq : modulationMul t (modulationMul (-t) G) = G := by
    rw [modulationMul_modulationMul, add_neg_cancel, modulationMul_zero_apply]
  have hshift := integral_modulationMul_cauchy ht hG (ne_of_gt hw)
  rw [hGeq, hzero] at hshift
  exact (mul_eq_zero.mp hshift.symm).resolve_left (modulationEntire_ne_zero t w)


end RHTower
