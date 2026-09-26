import GaloisForLFunctions.RHTower.ThetaPowerCuspConstantSplit
import GaloisForLFunctions.RHTower.ThetaPowerStripRigidity

/-!
# Real zeros of the theta-power transform at small parameter

For every `U` and `ρ < 1/2` there is `a₀ > 0` such that for `0 < a < a₀` every zero `w` of `Λ_a` with `|Re w| ≤ U`,
`|Im w| ≤ ρ` is real.

With `E = πa/4`, `L = log(1/E)` and `A(w) = (1/E)^{z}Γ(z)`, `z = (1/2 - iw)/2`, the transform is
`Λ_a = c_a (A(w) + A(-w)) + β_a` with `c_a = 2^a/4` and `β_a` bounded (`ThetaPowerCuspConstantSplit`).  Since
`z(-w) = conj(z(w) - v)` for `v = Im w`, `|A(w) + A(-w)| ≥ e^{L/4} v (gL - M₁)` with `g = |Γ(z(w))|`, so a zero with
`v > 0` has `v ≤ 8C e^{-L/4}/(m₀L)`.  Its conjugate `w̄` is also a zero (`Λ_a` is real on `ℝ` and even), while on the
segment `[w̄, w]` the derivative stays within half of `-i c_a L A(w)`: the transform is injective there.
-/

open Complex Real Filter Topology MeasureTheory Set Metric

namespace RHTower

noncomputable section

open Bottcher

variable {a : ℝ}

/-- **Segment injectivity.** If `f'` stays within `‖c‖/2` of `c ≠ 0` along the segment `[p, q]`, `p ≠ q`, then
`f p ≠ f q`. -/
theorem ne_of_norm_deriv_sub_le_half {f : ℂ → ℂ} {p q c : ℂ} (hpq : p ≠ q) (hc : c ≠ 0)
    (hf : ∀ x ∈ segment ℝ p q, DifferentiableAt ℂ f x)
    (hd : ∀ x ∈ segment ℝ p q, ‖deriv f x - c‖ ≤ ‖c‖ / 2) : f p ≠ f q := by
  intro hfpq
  set g : ℂ → ℂ := fun x => f x - c * x with hg
  have hgd : ∀ x ∈ segment ℝ p q, DifferentiableAt ℂ g x := fun x hx =>
    (hf x hx).sub ((differentiableAt_id).const_mul c)
  have hgder : ∀ x ∈ segment ℝ p q, ‖deriv g x‖ ≤ ‖c‖ / 2 := by
    intro x hx
    have h : HasDerivAt g (deriv f x - c * 1) x :=
      (hf x hx).hasDerivAt.sub ((hasDerivAt_id' x).const_mul c)
    rw [h.deriv, mul_one]; exact hd x hx
  have hmv := (convex_segment p q).norm_image_sub_le_of_norm_deriv_le hgd hgder
    (left_mem_segment ℝ p q) (right_mem_segment ℝ p q)
  have hgq : g q - g p = -(c * (q - p)) := by rw [hg]; simp only; rw [hfpq]; ring
  rw [hgq, norm_neg, norm_mul] at hmv
  have hqp : 0 < ‖q - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hpq))
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  nlinarith

/-- `Λ_a` is real on the real axis: `Λ_a(w̄) = conj Λ_a(w)`. -/
theorem thetaPowerXiC_conj (a : ℝ) (w : ℂ) :
    thetaPowerXiC a ((starRingEnd ℂ) w) = (starRingEnd ℂ) (thetaPowerXiC a w) := by
  have hreal : ∀ x : ℝ, (starRingEnd ℂ) (modTail (thetaPowerForm a) 0 x) = modTail (thetaPowerForm a) 0 x := by
    intro x
    unfold modTail modAxisPoint
    have hF := thetaPowerForm_I_mul_real a (Real.exp_pos (2 * x))
    rw [sub_zero, hF, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, map_ofNat]
  rw [← thetaPowerXiC_neg a ((starRingEnd ℂ) w)]
  unfold thetaPowerXiC
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [map_mul, hreal, ← Complex.exp_conj]
  congr 2
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

theorem half_sub_I_mul_neg (w : ℂ) : (1 / 2 - I * -w) / 2 = 1 / 2 - (1 / 2 - I * w) / 2 := by ring

theorem re_z_pos_of_im {w : ℂ} (hw : |w.im| < 1 / 2) : 0 < ((1 / 2 - I * w) / 2).re := by
  rw [re_half_sub_I_mul_div_two]; linarith [(abs_lt.mp hw).1]

/-- The norm of the Gamma factor: `‖A(w)‖ = (1/E)^{Re z} ‖Γ(z)‖`. -/
theorem norm_thetaPowerCuspGamma (ha : 0 < a) (w : ℂ) :
    ‖thetaPowerCuspGamma a w‖ = (1 / (π * (a / 4))) ^ ((1 / 2 - I * w) / 2).re *
      ‖Complex.Gamma ((1 / 2 - I * w) / 2)‖ := by
  unfold thetaPowerCuspGamma
  rw [norm_mul, show (1 / ((π * (a / 4) : ℝ) : ℂ)) = ((1 / (π * (a / 4)) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]

/-- **Derivative of the Gamma factor.** `A'(w) = -(i/2) (1/E)^z (L Γ(z) + Γ'(z))`, `L = log(1/E)`. -/
theorem hasDerivAt_thetaPowerCuspGamma (ha : 0 < a) {w : ℂ} (hw : 0 < ((1 / 2 - I * w) / 2).re) :
    HasDerivAt (thetaPowerCuspGamma a)
      (-(I / 2) * ((1 / ((π * (a / 4) : ℝ) : ℂ)) ^ ((1 / 2 - I * w) / 2) *
        ((Real.log (1 / (π * (a / 4))) : ℂ) * Complex.Gamma ((1 / 2 - I * w) / 2) +
          deriv Complex.Gamma ((1 / 2 - I * w) / 2)))) w := by
  have hE : (0 : ℝ) < 1 / (π * (a / 4)) := by positivity
  have hz : HasDerivAt (fun w : ℂ => (1 / 2 - I * w) / 2) (-(I / 2)) w := by
    have := (((hasDerivAt_id' w).const_mul I).const_sub (1 / 2 : ℂ)).div_const 2
    rw [show -(I / 2) = -(I * 1) / 2 by ring]
    exact this
  have hc : (1 / ((π * (a / 4) : ℝ) : ℂ)) ≠ 0 := by
    rw [show (1 / ((π * (a / 4) : ℝ) : ℂ)) = ((1 / (π * (a / 4)) : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast hE.ne'
  have h1 := hz.const_cpow (c := 1 / ((π * (a / 4) : ℝ) : ℂ)) (Or.inl hc)
  have hΓ : HasDerivAt Complex.Gamma (deriv Complex.Gamma ((1 / 2 - I * w) / 2)) ((1 / 2 - I * w) / 2) :=
    (Complex.differentiableAt_Gamma _ fun m hm => by
      have := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]).hasDerivAt
  have h2 := hΓ.comp w hz
  have hlog : Complex.log (1 / ((π * (a / 4) : ℝ) : ℂ)) = (Real.log (1 / (π * (a / 4))) : ℂ) := by
    rw [show (1 / ((π * (a / 4) : ℝ) : ℂ)) = ((1 / (π * (a / 4)) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log hE.le]
  unfold thetaPowerCuspGamma
  refine (h1.mul h2).congr_deriv ?_
  simp only [Function.comp_apply]
  rw [hlog]
  ring

/-- The rectangle `|Re z - 1/4| ≤ ρ/2`, `|Im z| ≤ U/2` of Gamma arguments. -/
def gammaRect (U ρ : ℝ) : Set ℂ := {z : ℂ | 1 / 4 - ρ / 2 ≤ z.re ∧ z.re ≤ 1 / 4 + ρ / 2 ∧ |z.im| ≤ U / 2}

theorem convex_gammaRect (U ρ : ℝ) : Convex ℝ (gammaRect U ρ) := by
  have h1 : Convex ℝ {z : ℂ | 1 / 4 - ρ / 2 ≤ z.re} :=
    convex_halfSpace_ge (f := Complex.re) Complex.reLm.isLinear _
  have h2 : Convex ℝ {z : ℂ | z.re ≤ 1 / 4 + ρ / 2} :=
    convex_halfSpace_le (f := Complex.re) Complex.reLm.isLinear _
  have h3 : Convex ℝ {z : ℂ | |z.im| ≤ U / 2} := by
    have ha : Convex ℝ {z : ℂ | z.im ≤ U / 2} := convex_halfSpace_le Complex.imLm.isLinear _
    have hb : Convex ℝ {z : ℂ | -(U / 2) ≤ z.im} := convex_halfSpace_ge Complex.imLm.isLinear _
    convert ha.inter hb using 1
    ext z; simp [abs_le, and_comm]
  exact h1.inter (h2.inter h3)

theorem re_pos_of_mem_gammaRect {U ρ : ℝ} (hρ : ρ < 1 / 2) {z : ℂ} (hz : z ∈ gammaRect U ρ) :
    0 < z.re := by linarith [hz.1]

theorem isCompact_gammaRect (U ρ : ℝ) : IsCompact (gammaRect U ρ) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · refine (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |1 / 4 - ρ / 2| + |1 / 4 + ρ / 2| + |U / 2|)).subset
      fun z hz => ?_
    rw [mem_closedBall, dist_zero_right]
    have hre : |z.re| ≤ |1 / 4 - ρ / 2| + |1 / 4 + ρ / 2| := by
      rw [abs_le]; constructor
      · linarith [hz.1, neg_abs_le (1 / 4 - ρ / 2), abs_nonneg (1 / 4 + ρ / 2)]
      · linarith [hz.2.1, le_abs_self (1 / 4 + ρ / 2), abs_nonneg (1 / 4 - ρ / 2)]
    have him : |z.im| ≤ |U / 2| := hz.2.2.trans (le_abs_self _)
    linarith [Complex.norm_le_abs_re_add_abs_im z]

/-- **Gamma bounds on the rectangle.** -/
theorem exists_gamma_bounds_gammaRect (U : ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2) (hU : 0 ≤ U) :
    ∃ m₀ M₀ M₁ : ℝ, 0 < m₀ ∧ 0 ≤ M₀ ∧ 0 ≤ M₁ ∧ ∀ z ∈ gammaRect U ρ,
      m₀ ≤ ‖Complex.Gamma z‖ ∧ ‖Complex.Gamma z‖ ≤ M₀ ∧ ‖deriv Complex.Gamma z‖ ≤ M₁ := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z fun m hm => by
      have := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at this
      have : (0 : ℝ) < z.re := hz
      linarith [Nat.cast_nonneg (α := ℝ) m]).differentiableWithinAt
  have hsub : gammaRect U ρ ⊆ {z : ℂ | 0 < z.re} := fun z hz => re_pos_of_mem_gammaRect hρ hz
  have hK := isCompact_gammaRect U ρ
  have hne : (gammaRect U ρ).Nonempty := by
    refine ⟨(1 / 4 : ℂ), ?_, ?_, ?_⟩
    · have : ((1 / 4 : ℂ)).re = 1 / 4 := by norm_num
      rw [this]; linarith
    · have : ((1 / 4 : ℂ)).re = 1 / 4 := by norm_num
      rw [this]; linarith
    · have : ((1 / 4 : ℂ)).im = 0 := by norm_num
      rw [this, abs_zero]; linarith
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne (hdiff.continuousOn.mono hsub).norm
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hdiff.continuousOn.mono hsub)
  obtain ⟨M₁, hM₁⟩ := hK.exists_bound_of_continuousOn ((hdiff.deriv hopen).continuousOn.mono hsub)
  refine ⟨‖Complex.Gamma z₀‖, max M₀ 0, max M₁ 0,
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (hsub hz₀)), le_max_right _ _, le_max_right _ _,
    fun z hz => ⟨hmin hz, (hM₀ z hz).trans (le_max_left _ _), (hM₁ z hz).trans (le_max_left _ _)⟩⟩

theorem im_half_sub_I_mul_div_two (w : ℂ) : ((1 / 2 - I * w) / 2).im = -w.re / 2 := by
  simp

theorem mem_gammaRect_of {U ρ : ℝ} {w : ℂ} (hu : |w.re| ≤ U) (hv : |w.im| ≤ ρ) :
    (1 / 2 - I * w) / 2 ∈ gammaRect U ρ := by
  have hre := re_half_sub_I_mul_div_two w
  have him := im_half_sub_I_mul_div_two w
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]; linarith [(abs_le.mp hv).1]
  · rw [hre]; linarith [(abs_le.mp hv).2]
  · rw [him, abs_div, abs_neg, abs_two]; linarith

theorem one_div_E_rpow (ha : 0 < a) (x : ℝ) :
    (1 / (π * (a / 4))) ^ x = Real.exp (Real.log (1 / (π * (a / 4))) * x) := by
  rw [Real.rpow_def_of_pos (by positivity)]

/-- **Domination off the line.** For `v = Im w ≥ 0`,
`‖A(w) + A(-w)‖ ≥ e^{L/4} v (m₀ L - M₁)`. -/
theorem norm_add_thetaPowerCuspGamma_ge (ha : 0 < a) {U ρ m₀ M₁ : ℝ} (hρ : ρ < 1 / 2) (hM₁ : 0 ≤ M₁)
    (hΓ : ∀ z ∈ gammaRect U ρ, m₀ ≤ ‖Complex.Gamma z‖ ∧ ‖deriv Complex.Gamma z‖ ≤ M₁)
    (hL : 0 ≤ Real.log (1 / (π * (a / 4)))) {w : ℂ} (hu : |w.re| ≤ U) (hv0 : 0 ≤ w.im) (hv : w.im ≤ ρ) :
    Real.exp (Real.log (1 / (π * (a / 4))) / 4) * w.im * (m₀ * Real.log (1 / (π * (a / 4))) - M₁) ≤
      ‖thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w)‖ := by
  set L := Real.log (1 / (π * (a / 4))) with hLdef
  set v := w.im with hvdef
  set z : ℂ := (1 / 2 - I * w) / 2 with hz
  have hvabs : |w.im| ≤ ρ := abs_le.mpr ⟨by linarith, hv⟩
  have hzZ : z ∈ gammaRect U ρ := mem_gammaRect_of hu hvabs
  have hzre : z.re = 1 / 4 + v / 2 := re_half_sub_I_mul_div_two w
  -- `z(-w) = conj (z - v)`
  have hzneg : (1 / 2 - I * -w) / 2 = (starRingEnd ℂ) (z - (v : ℂ)) := by
    apply Complex.ext
    · rw [Complex.conj_re, Complex.sub_re, Complex.ofReal_re, hzre, re_half_sub_I_mul_div_two,
        Complex.neg_im]
      ring
    · rw [Complex.conj_im, Complex.sub_im, Complex.ofReal_im, sub_zero, hz, im_half_sub_I_mul_div_two,
        im_half_sub_I_mul_div_two, Complex.neg_re]
      ring
  -- Lipschitz step `‖Γ(z - v)‖ ≤ ‖Γ(z)‖ + M₁ v`
  have hseg : segment ℝ (z - (v : ℂ)) z ⊆ gammaRect U ρ := by
    refine (convex_gammaRect U ρ).segment_subset ?_ hzZ
    refine ⟨?_, ?_, ?_⟩
    · simp only [Complex.sub_re, Complex.ofReal_re]; rw [hzre]; linarith
    · simp only [Complex.sub_re, Complex.ofReal_re]; rw [hzre]; linarith
    · simpa using hzZ.2.2
  have hlip : ‖Complex.Gamma z - Complex.Gamma (z - (v : ℂ))‖ ≤ M₁ * ‖z - (z - (v : ℂ))‖ := by
    refine (convex_segment _ _).norm_image_sub_le_of_norm_deriv_le (fun x hx => ?_)
      (fun x hx => (hΓ x (hseg hx)).2) (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
    exact Complex.differentiableAt_Gamma x fun m hm => by
      have := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [re_pos_of_mem_gammaRect hρ (hseg hx), Nat.cast_nonneg (α := ℝ) m]
  rw [show z - (z - (v : ℂ)) = (v : ℂ) by ring, Complex.norm_real, Real.norm_of_nonneg hv0] at hlip
  have hΓneg : ‖Complex.Gamma ((1 / 2 - I * -w) / 2)‖ ≤ ‖Complex.Gamma z‖ + M₁ * v := by
    rw [hzneg, Complex.Gamma_conj, RCLike.norm_conj]
    have := norm_sub_norm_le (Complex.Gamma (z - (v : ℂ))) (Complex.Gamma z)
    rw [norm_sub_rev] at hlip
    linarith
  have hg := (hΓ z hzZ).1
  -- norms of the two terms
  have hA : ‖thetaPowerCuspGamma a w‖ = Real.exp (L * (1 / 4 + v / 2)) * ‖Complex.Gamma z‖ := by
    rw [norm_thetaPowerCuspGamma ha, ← hz, hzre, one_div_E_rpow ha]
  have hA' : ‖thetaPowerCuspGamma a (-w)‖ =
      Real.exp (L * (1 / 4 - v / 2)) * ‖Complex.Gamma ((1 / 2 - I * -w) / 2)‖ := by
    rw [norm_thetaPowerCuspGamma ha, re_half_sub_I_mul_div_two, one_div_E_rpow ha, Complex.neg_im]
    congr 3; ring
  have hsinh : L * v ≤ Real.exp (L * v / 2) - Real.exp (-(L * v / 2)) := by
    have hx : 0 ≤ L * v / 2 := by positivity
    have h := Real.self_le_sinh_iff.mpr hx
    rw [Real.sinh_eq] at h
    linarith
  have hexp1 : Real.exp (L * (1 / 4 + v / 2)) = Real.exp (L / 4) * Real.exp (L * v / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hexp2 : Real.exp (L * (1 / 4 - v / 2)) = Real.exp (L / 4) * Real.exp (-(L * v / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hle1 : Real.exp (-(L * v / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ L * v := mul_nonneg hL hv0; linarith)
  have hmain : ‖thetaPowerCuspGamma a w‖ - ‖thetaPowerCuspGamma a (-w)‖ ≤
      ‖thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w)‖ := by
    have := norm_sub_norm_le (thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w))
      (thetaPowerCuspGamma a (-w))
    rw [add_sub_cancel_right] at this
    have h2 := norm_add_le (thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w))
      (-thetaPowerCuspGamma a (-w))
    rw [add_neg_cancel_right, norm_neg] at h2
    linarith
  refine le_trans ?_ hmain
  rw [hA, hA', hexp1, hexp2]
  set g := ‖Complex.Gamma z‖
  set e := Real.exp (L / 4)
  have he : 0 < e := Real.exp_pos _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hneg0 : 0 ≤ ‖Complex.Gamma ((1 / 2 - I * -w) / 2)‖ := norm_nonneg _
  -- `e (e^{x} g - e^{-x} ‖Γ(z(-w))‖) ≥ e (g L v - M₁ v)`
  have key : g * (L * v) - M₁ * v ≤
      Real.exp (L * v / 2) * g - Real.exp (-(L * v / 2)) * ‖Complex.Gamma ((1 / 2 - I * -w) / 2)‖ := by
    have hN1 : Real.exp (-(L * v / 2)) * ‖Complex.Gamma ((1 / 2 - I * -w) / 2)‖ ≤
        Real.exp (-(L * v / 2)) * (g + M₁ * v) :=
      mul_le_mul_of_nonneg_left hΓneg (Real.exp_pos _).le
    have hN2 : Real.exp (-(L * v / 2)) * (M₁ * v) ≤ M₁ * v :=
      mul_le_of_le_one_left (mul_nonneg hM₁ hv0) hle1
    have hN3 : g * (L * v) ≤ g * (Real.exp (L * v / 2) - Real.exp (-(L * v / 2))) :=
      mul_le_mul_of_nonneg_left hsinh hg0
    nlinarith
  have hmv : e * v * (m₀ * L - M₁) ≤ e * (g * (L * v) - M₁ * v) := by
    have : m₀ * L * v ≤ g * L * v := by
      have := mul_le_mul_of_nonneg_right hg (mul_nonneg hL hv0)
      nlinarith
    nlinarith
  calc e * v * (m₀ * L - M₁) ≤ e * (g * (L * v) - M₁ * v) := hmv
    _ ≤ e * (Real.exp (L * v / 2) * g - Real.exp (-(L * v / 2)) *
          ‖Complex.Gamma ((1 / 2 - I * -w) / 2)‖) := mul_le_mul_of_nonneg_left key he.le
    _ = e * Real.exp (L * v / 2) * g - e * Real.exp (-(L * v / 2)) *
          ‖Complex.Gamma ((1 / 2 - I * -w) / 2)‖ := by ring

/-- The derivative value of the Gamma factor. -/
def cuspGammaDeriv (a : ℝ) (w : ℂ) : ℂ :=
  -(I / 2) * ((1 / ((π * (a / 4) : ℝ) : ℂ)) ^ ((1 / 2 - I * w) / 2) *
    ((Real.log (1 / (π * (a / 4))) : ℂ) * Complex.Gamma ((1 / 2 - I * w) / 2) +
      deriv Complex.Gamma ((1 / 2 - I * w) / 2)))

theorem norm_one_div_E_cpow (ha : 0 < a) (w : ℂ) :
    ‖(1 / ((π * (a / 4) : ℝ) : ℂ)) ^ ((1 / 2 - I * w) / 2)‖ =
      Real.exp (Real.log (1 / (π * (a / 4))) * (1 / 4 + w.im / 2)) := by
  rw [show (1 / ((π * (a / 4) : ℝ) : ℂ)) = ((1 / (π * (a / 4)) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), re_half_sub_I_mul_div_two, one_div_E_rpow ha]

theorem norm_one_div_E_cpow_le (ha : 0 < a) (hL : 0 ≤ Real.log (1 / (π * (a / 4)))) {w : ℂ} {t : ℝ}
    (hw : |w.im| ≤ t) :
    ‖(1 / ((π * (a / 4) : ℝ) : ℂ)) ^ ((1 / 2 - I * w) / 2)‖ ≤
      Real.exp (Real.log (1 / (π * (a / 4))) * (1 / 4 + t / 2)) := by
  rw [norm_one_div_E_cpow ha]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hw).2]) hL)

/-- Bounds on the Gamma factor and its derivative on `|Re w| ≤ U`, `|Im w| ≤ t ≤ ρ`. -/
theorem cuspGamma_bounds (ha : 0 < a) (hL : 0 ≤ Real.log (1 / (π * (a / 4)))) {U ρ M₀ M₁ t : ℝ}
    (hΓ : ∀ z ∈ gammaRect U ρ, ‖Complex.Gamma z‖ ≤ M₀ ∧ ‖deriv Complex.Gamma z‖ ≤ M₁) {w : ℂ} (hu : |w.re| ≤ U) (hwt : |w.im| ≤ t) (ht : t ≤ ρ) :
    ‖thetaPowerCuspGamma a w‖ ≤ Real.exp (Real.log (1 / (π * (a / 4))) * (1 / 4 + t / 2)) * M₀ ∧
      ‖cuspGammaDeriv a w‖ ≤ Real.exp (Real.log (1 / (π * (a / 4))) * (1 / 4 + t / 2)) *
        ((Real.log (1 / (π * (a / 4))) * M₀ + M₁) / 2) := by
  set L := Real.log (1 / (π * (a / 4)))
  have hz := mem_gammaRect_of hu (hwt.trans ht)
  obtain ⟨hG, hD⟩ := hΓ _ hz
  have hE := norm_one_div_E_cpow_le ha hL hwt
  have hE0 : 0 ≤ Real.exp (L * (1 / 4 + t / 2)) := (Real.exp_pos _).le
  constructor
  · unfold thetaPowerCuspGamma
    rw [norm_mul]
    exact mul_le_mul hE hG (norm_nonneg _) hE0
  · unfold cuspGammaDeriv
    rw [norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_two, norm_mul]
    have hin : ‖(L : ℂ) * Complex.Gamma ((1 / 2 - I * w) / 2) + deriv Complex.Gamma ((1 / 2 - I * w) / 2)‖ ≤
        L * M₀ + M₁ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ hD)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL]
      exact mul_le_mul_of_nonneg_left hG hL
    calc 1 / 2 * (‖(1 / ((π * (a / 4) : ℝ) : ℂ)) ^ ((1 / 2 - I * w) / 2)‖ *
          ‖(L : ℂ) * Complex.Gamma ((1 / 2 - I * w) / 2) + deriv Complex.Gamma ((1 / 2 - I * w) / 2)‖)
        ≤ 1 / 2 * (Real.exp (L * (1 / 4 + t / 2)) * (L * M₀ + M₁)) := by
          gcongr
      _ = _ := by ring

/-- **Derivative of the main term.** -/
theorem hasDerivAt_thetaPowerCuspMain (ha : 0 < a) {w : ℂ} (hw : |w.im| < 1 / 2) :
    HasDerivAt (thetaPowerCuspMain a)
      ((((2 : ℝ) ^ a / 4 : ℝ) : ℂ) * (cuspGammaDeriv a w - cuspGammaDeriv a (-w))) w := by
  have h1 := hasDerivAt_thetaPowerCuspGamma ha (re_z_pos_of_im hw)
  have hw' : |(-w).im| < 1 / 2 := by rwa [Complex.neg_im, abs_neg]
  have h2 := (hasDerivAt_thetaPowerCuspGamma ha (re_z_pos_of_im hw')).comp w (hasDerivAt_neg w)
  unfold thetaPowerCuspMain
  refine ((h1.add h2).const_mul _).congr_deriv ?_
  unfold cuspGammaDeriv
  ring

theorem differentiableOn_thetaPowerCuspMain (ha : 0 < a) :
    DifferentiableOn ℂ (thetaPowerCuspMain a) {w : ℂ | |w.im| < 1 / 2} := fun _ hw =>
  (hasDerivAt_thetaPowerCuspMain ha hw).differentiableAt.differentiableWithinAt

/-- **Cauchy bound for the remainder derivative.** If `‖Λ_a - main‖ ≤ C` on `|Im w| ≤ ρ₁ < 1/2` then its derivative
is at most `C/r` on `|Im w| ≤ ρ₁ - r`. -/
theorem norm_deriv_remainder_le (ha : 0 < a) {ρ₁ C r : ℝ} (hρ₁ : ρ₁ < 1 / 2) (hr : 0 < r)
    (hC : ∀ w : ℂ, |w.im| ≤ ρ₁ → ‖thetaPowerXiC a w - thetaPowerCuspMain a w‖ ≤ C)
    {w : ℂ} (hw : |w.im| ≤ ρ₁ - r) :
    ‖deriv (fun ζ => thetaPowerXiC a ζ - thetaPowerCuspMain a ζ) w‖ ≤ C / r := by
  have hopen : IsOpen {ζ : ℂ | |ζ.im| < 1 / 2} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hdiff : DifferentiableOn ℂ (fun ζ => thetaPowerXiC a ζ - thetaPowerCuspMain a ζ)
      {ζ : ℂ | |ζ.im| < 1 / 2} :=
    (differentiable_thetaPowerXiC ha).differentiableOn.sub (differentiableOn_thetaPowerCuspMain ha)
  have hball : closedBall w r ⊆ {ζ : ℂ | |ζ.im| ≤ ρ₁} := by
    intro ζ hζ
    rw [mem_closedBall, dist_eq_norm] at hζ
    have h := (Complex.abs_im_le_norm (ζ - w)).trans hζ
    rw [Complex.sub_im] at h
    show |ζ.im| ≤ ρ₁
    have := abs_sub_abs_le_abs_sub ζ.im w.im
    linarith
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hdiff.diffContOnCl_ball fun ζ hζ => ?_) fun ζ hζ => hC ζ (hball (sphere_subset_closedBall hζ))
  have := hball hζ
  show |ζ.im| < 1 / 2
  exact lt_of_le_of_lt this hρ₁

/-- Points of the segment `[w̄, w]`, `Im w ≥ 0`: same real part, `|Im| ≤ Im w`, distance to `w` at most `2 Im w`. -/
theorem segment_conj_facts {w ζ : ℂ} (hv : 0 ≤ w.im) (hζ : ζ ∈ segment ℝ ((starRingEnd ℂ) w) w) :
    ζ.re = w.re ∧ |ζ.im| ≤ w.im ∧ ‖ζ - w‖ ≤ 2 * w.im := by
  rw [segment_eq_image] at hζ
  obtain ⟨θ, ⟨hθ0, hθ1⟩, rfl⟩ := hζ
  have hre : ((1 - θ) • (starRingEnd ℂ) w + θ • w).re = w.re := by
    simp only [Complex.add_re, Complex.smul_re, Complex.conj_re, smul_eq_mul]; ring
  have him : ((1 - θ) • (starRingEnd ℂ) w + θ • w).im = (2 * θ - 1) * w.im := by
    simp only [Complex.add_im, Complex.smul_im, Complex.conj_im, smul_eq_mul]; ring
  refine ⟨hre, ?_, ?_⟩
  · rw [him, abs_le]; constructor <;> nlinarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, hre, him, sub_self, abs_zero, zero_add,
      show (2 * θ - 1) * w.im - w.im = -(2 * (1 - θ) * w.im) by ring, abs_neg,
      abs_of_nonneg (by nlinarith)]
    nlinarith

/-- `D(w) = (1/E)^{z} Γ'(z)`. -/
def cuspGammaD (a : ℝ) (w : ℂ) : ℂ :=
  (1 / ((π * (a / 4) : ℝ) : ℂ)) ^ ((1 / 2 - I * w) / 2) * deriv Complex.Gamma ((1 / 2 - I * w) / 2)

theorem cuspGammaDeriv_eq (a : ℝ) (w : ℂ) :
    cuspGammaDeriv a w = -(I / 2) * ((Real.log (1 / (π * (a / 4))) : ℂ) * thetaPowerCuspGamma a w +
      cuspGammaD a w) := by
  unfold cuspGammaDeriv thetaPowerCuspGamma cuspGammaD; ring

/-- **Pointwise derivative estimate.** -/
theorem norm_deriv_thetaPowerXiC_sub_le (ha0 : 0 < a) {ρ r C : ℝ} (hr : 0 < r) (hρr : ρ + r < 1 / 2)
    (hC : ∀ w : ℂ, |w.im| ≤ ρ + r → ‖thetaPowerXiC a w - thetaPowerCuspMain a w‖ ≤ C)
    {ζ w : ℂ} (hζ : |ζ.im| ≤ ρ) {X₁ X₂ X₃ : ℝ}
    (hA1 : ‖thetaPowerCuspGamma a ζ - thetaPowerCuspGamma a w‖ ≤ X₁)
    (hA2 : ‖thetaPowerCuspGamma a (-ζ) - thetaPowerCuspGamma a (-w)‖ ≤ X₁)
    (hpair : ‖thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w)‖ ≤ X₂)
    (hD1 : ‖cuspGammaD a ζ‖ ≤ X₃) (hD2 : ‖cuspGammaD a (-ζ)‖ ≤ X₃)
    (hL0 : 0 ≤ Real.log (1 / (π * (a / 4)))) :
    ‖deriv (thetaPowerXiC a) ζ - -I * (((2 : ℝ) ^ a / 4 : ℝ) : ℂ) *
        (Real.log (1 / (π * (a / 4))) : ℂ) * thetaPowerCuspGamma a w‖ ≤
      (2 : ℝ) ^ a / 4 / 2 * (Real.log (1 / (π * (a / 4))) * (2 * X₁ + X₂) + 2 * X₃) + C / r := by
  have hζ12 : |ζ.im| < 1 / 2 := by linarith
  have hmain := hasDerivAt_thetaPowerCuspMain ha0 hζ12
  have hd : HasDerivAt (fun ξ => thetaPowerXiC a ξ - thetaPowerCuspMain a ξ)
      (deriv (thetaPowerXiC a) ζ - deriv (thetaPowerCuspMain a) ζ) ζ :=
    (differentiable_thetaPowerXiC ha0 ζ).hasDerivAt.sub hmain.differentiableAt.hasDerivAt
  have hsplit : deriv (thetaPowerXiC a) ζ = deriv (thetaPowerCuspMain a) ζ +
      deriv (fun ξ => thetaPowerXiC a ξ - thetaPowerCuspMain a ξ) ζ := by
    rw [hd.deriv]; ring
  have hβ := norm_deriv_remainder_le ha0 (ρ₁ := ρ + r) hρr hr hC (w := ζ) (by linarith)
  set L := Real.log (1 / (π * (a / 4)))
  set ca : ℝ := (2 : ℝ) ^ a / 4 with hca
  have hca0 : 0 ≤ ca := by positivity
  rw [hsplit, hmain.deriv]
  have hid : (ca : ℂ) * (cuspGammaDeriv a ζ - cuspGammaDeriv a (-ζ)) - -I * (ca : ℂ) * (L : ℂ) *
      thetaPowerCuspGamma a w =
      (ca : ℂ) * (-(I / 2)) * ((L : ℂ) * ((thetaPowerCuspGamma a ζ - thetaPowerCuspGamma a w) -
        (thetaPowerCuspGamma a (-ζ) - thetaPowerCuspGamma a (-w)) -
        (thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w))) + (cuspGammaD a ζ - cuspGammaD a (-ζ))) := by
    rw [cuspGammaDeriv_eq, cuspGammaDeriv_eq]; ring
  have hin : ‖(L : ℂ) * ((thetaPowerCuspGamma a ζ - thetaPowerCuspGamma a w) -
      (thetaPowerCuspGamma a (-ζ) - thetaPowerCuspGamma a (-w)) -
      (thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w))) + (cuspGammaD a ζ - cuspGammaD a (-ζ))‖ ≤
      L * (2 * X₁ + X₂) + 2 * X₃ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hL0]
      refine mul_le_mul_of_nonneg_left ?_ hL0
      refine (norm_sub_le _ _).trans ?_
      have := (norm_sub_le (thetaPowerCuspGamma a ζ - thetaPowerCuspGamma a w)
        (thetaPowerCuspGamma a (-ζ) - thetaPowerCuspGamma a (-w)))
      linarith
    · have := norm_sub_le (cuspGammaD a ζ) (cuspGammaD a (-ζ))
      linarith
  have hfirst : ‖(ca : ℂ) * (cuspGammaDeriv a ζ - cuspGammaDeriv a (-ζ)) - -I * (ca : ℂ) * (L : ℂ) *
      thetaPowerCuspGamma a w‖ ≤ ca / 2 * (L * (2 * X₁ + X₂) + 2 * X₃) := by
    rw [hid, norm_mul, norm_mul, norm_neg, norm_div, Complex.norm_I, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg hca0]
    calc ca * (1 / 2) * _ ≤ ca * (1 / 2) * (L * (2 * X₁ + X₂) + 2 * X₃) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = _ := by ring
  have hre : (ca : ℂ) * (cuspGammaDeriv a ζ - cuspGammaDeriv a (-ζ)) +
      deriv (fun ξ => thetaPowerXiC a ξ - thetaPowerCuspMain a ξ) ζ - -I * (ca : ℂ) * (L : ℂ) *
        thetaPowerCuspGamma a w =
      ((ca : ℂ) * (cuspGammaDeriv a ζ - cuspGammaDeriv a (-ζ)) - -I * (ca : ℂ) * (L : ℂ) *
        thetaPowerCuspGamma a w) + deriv (fun ξ => thetaPowerXiC a ξ - thetaPowerCuspMain a ξ) ζ := by ring
  rw [hre]
  exact (norm_add_le _ _).trans (add_le_add hfirst hβ)

/-- **Arithmetic closing the injectivity step.** -/
theorem injectivity_budget {ca L e v m₀ M₀ M₁ C r An : ℝ} (hca : 1 / 4 ≤ ca) (hL1 : 1 ≤ L) (he : 0 < e)
    (hm₀ : 0 < m₀) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hC : 0 ≤ C) (hr : 0 < r)
    (hL8 : 8 * M₁ ≤ m₀ * L) (hLvC : e * (L * v) * m₀ ≤ 8 * C)
    (hLK : 2 * (32 * C * M₀ / m₀ + 32 * C * M₁ / m₀ + 4 * C + 8 * C / r) ≤ m₀ * e)
    (hAn : e * m₀ ≤ An) :
    ca / 2 * (L * (2 * (2 * e * ((L * M₀ + M₁) / 2) * (2 * v)) + 4 * C) + 2 * (2 * e * M₁)) + C / r ≤
      ca * L * An / 2 := by
  set K := 32 * C * M₀ / m₀ + 32 * C * M₁ / m₀ + 4 * C + 8 * C / r with hKdef
  have h1 : L * (4 * e * (L * M₀ + M₁) * v) ≤ 32 * C * (L * M₀ + M₁) / m₀ := by
    rw [le_div_iff₀ hm₀]
    have := mul_le_mul_of_nonneg_left hLvC (show 0 ≤ 4 * (L * M₀ + M₁) by positivity)
    nlinarith
  have h2 : 32 * C * (L * M₀ + M₁) / m₀ + 4 * C * L + 8 * C / r ≤ L * K := by
    have t1 : 32 * C * (L * M₀ + M₁) / m₀ = L * (32 * C * M₀ / m₀) + 32 * C * M₁ / m₀ := by
      field_simp
    have t2 : 32 * C * M₁ / m₀ ≤ L * (32 * C * M₁ / m₀) := le_mul_of_one_le_left (by positivity) hL1
    have t3 : 8 * C / r ≤ L * (8 * C / r) := le_mul_of_one_le_left (by positivity) hL1
    rw [hKdef, t1]
    nlinarith
  have h3 : L * K ≤ L * e * m₀ / 2 := by
    have := mul_le_mul_of_nonneg_left hLK (show 0 ≤ L by linarith)
    nlinarith
  have h4 : 4 * e * M₁ ≤ L * e * m₀ / 2 := by nlinarith
  have hCr : C / r ≤ ca / 2 * (8 * C / r) := by
    have : 0 ≤ C / r := by positivity
    rw [show ca / 2 * (8 * C / r) = (4 * ca) * (C / r) by ring]
    nlinarith
  have hbr : L * (2 * (2 * e * ((L * M₀ + M₁) / 2) * (2 * v)) + 4 * C) + 2 * (2 * e * M₁) + 8 * C / r ≤
      L * e * m₀ := by
    have : L * (2 * (2 * e * ((L * M₀ + M₁) / 2) * (2 * v)) + 4 * C) =
        L * (4 * e * (L * M₀ + M₁) * v) + 4 * C * L := by ring
    rw [this]
    linarith
  have hmain : ca / 2 * (L * (2 * (2 * e * ((L * M₀ + M₁) / 2) * (2 * v)) + 4 * C) + 2 * (2 * e * M₁)) +
      ca / 2 * (8 * C / r) ≤ ca / 2 * (L * e * m₀) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hbr (by positivity)
  have hfin : ca / 2 * (L * e * m₀) ≤ ca * L * An / 2 := by
    have := mul_le_mul_of_nonneg_left hAn (show 0 ≤ ca * L by positivity)
    nlinarith
  linarith

/-- **No zeros just above the real axis.** -/
theorem thetaPowerXiC_ne_zero_of_small_im (ha0 : 0 < a) {U ρ r C m₀ M₀ M₁ : ℝ}
    (hρ0 : 0 ≤ ρ) (hr : 0 < r) (hρr : ρ + r < 1 / 2) (hC0 : 0 ≤ C)
    (hC : ∀ w : ℂ, |w.im| ≤ ρ + r → ‖thetaPowerXiC a w - thetaPowerCuspMain a w‖ ≤ C)
    (hm₀ : 0 < m₀) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hΓ : ∀ z ∈ gammaRect U ρ, m₀ ≤ ‖Complex.Gamma z‖ ∧ ‖Complex.Gamma z‖ ≤ M₀ ∧ ‖deriv Complex.Gamma z‖ ≤ M₁)
    (hL1 : 1 ≤ Real.log (1 / (π * (a / 4)))) (hL8 : 8 * M₁ ≤ m₀ * Real.log (1 / (π * (a / 4))))
    (hLC : 8 * C ≤ m₀ * Real.exp (Real.log (1 / (π * (a / 4))) / 4))
    (hLK : 2 * (32 * C * M₀ / m₀ + 32 * C * M₁ / m₀ + 4 * C + 8 * C / r) ≤
      m₀ * Real.exp (Real.log (1 / (π * (a / 4))) / 4))
    {w : ℂ} (hu : |w.re| ≤ U) (hv0 : 0 < w.im) (hv : w.im ≤ ρ) : thetaPowerXiC a w ≠ 0 := by
  intro hz
  set L := Real.log (1 / (π * (a / 4))) with hLdef
  set v := w.im with hvdef
  set e := Real.exp (L / 4) with he
  have hca0 : 1 / 4 ≤ (2 : ℝ) ^ a / 4 := by
    have := Real.one_le_rpow (show (1 : ℝ) ≤ 2 by norm_num) ha0.le; linarith
  have he0 : 0 < e := Real.exp_pos _
  have hL0 : 0 ≤ L := by linarith
  -- the Gamma pair is small at the zero
  have hpair : ‖thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w)‖ ≤ 4 * C := by
    have h1 := hC w (by rw [abs_of_pos hv0]; linarith)
    rw [hz, zero_sub, norm_neg] at h1
    unfold thetaPowerCuspMain at h1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h1
    have : (1 / 4) * ‖thetaPowerCuspGamma a w + thetaPowerCuspGamma a (-w)‖ ≤ C :=
      le_trans (mul_le_mul_of_nonneg_right hca0 (norm_nonneg _)) h1
    linarith
  -- domination bounds `v`
  have hdom := norm_add_thetaPowerCuspGamma_ge ha0 (U := U) (ρ := ρ) (m₀ := m₀) (M₁ := M₁)
    (by linarith) hM₁ (fun z hz => ⟨(hΓ z hz).1, (hΓ z hz).2.2⟩) hL0 hu hv0.le hv
  have h1 : e * v * (m₀ * L / 2) ≤ 4 * C :=
    le_trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (hdom.trans hpair)
  have hLvC : e * (L * v) * m₀ ≤ 8 * C := by
    have : e * (L * v) * m₀ = 2 * (e * v * (m₀ * L / 2)) := by ring
    linarith
  have hLv : L * v ≤ 1 := by
    by_contra h
    push Not at h
    have : e * m₀ < e * (L * v) * m₀ := by nlinarith [mul_pos he0 hm₀]
    linarith
  have hexpv : Real.exp (L * (1 / 4 + v / 2)) ≤ 2 * e := by
    rw [he, show L * (1 / 4 + v / 2) = L / 4 + L * v / 2 by ring, Real.exp_add]
    have hhalf : Real.exp (1 / 2) ≤ 2 := by
      have h := Real.exp_one_lt_d9
      have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
        rw [← Real.exp_nat_mul]; norm_num
      nlinarith [Real.exp_pos (1 / 2)]
    have : Real.exp (L * v / 2) ≤ 2 := (Real.exp_le_exp.mpr (by linarith)).trans hhalf
    nlinarith [Real.exp_pos (L / 4)]
  have hAw : e * m₀ ≤ ‖thetaPowerCuspGamma a w‖ := by
    rw [norm_thetaPowerCuspGamma ha0, re_half_sub_I_mul_div_two, one_div_E_rpow ha0]
    have hg := (hΓ _ (mem_gammaRect_of hu (by rw [abs_of_pos hv0]; exact hv))).1
    have : e ≤ Real.exp (L * (1 / 4 + v / 2)) := by
      rw [he]; exact Real.exp_le_exp.mpr (by nlinarith)
    exact mul_le_mul this hg hm₀.le (Real.exp_pos _).le
  set c₀ : ℂ := -I * (((2 : ℝ) ^ a / 4 : ℝ) : ℂ) * (L : ℂ) * thetaPowerCuspGamma a w with hc₀
  have hc₀n : ‖c₀‖ = (2 : ℝ) ^ a / 4 * L * ‖thetaPowerCuspGamma a w‖ := by
    rw [hc₀, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hL0]
    ring
  have hc₀pos : 0 < ‖c₀‖ := by
    rw [hc₀n]
    exact mul_pos (mul_pos (by linarith) (by linarith)) (lt_of_lt_of_le (mul_pos he0 hm₀) hAw)
  have hΓ' : ∀ z ∈ gammaRect U ρ, ‖Complex.Gamma z‖ ≤ M₀ ∧ ‖deriv Complex.Gamma z‖ ≤ M₁ :=
    fun z hz => ⟨(hΓ z hz).2.1, (hΓ z hz).2.2⟩
  have hLM : 0 ≤ (L * M₀ + M₁) / 2 := by positivity
  -- bounds along the segment
  have hbd : ∀ ξ ∈ segment ℝ ((starRingEnd ℂ) w) w,
      ‖cuspGammaDeriv a ξ‖ ≤ 2 * e * ((L * M₀ + M₁) / 2) ∧
      ‖cuspGammaDeriv a (-ξ)‖ ≤ 2 * e * ((L * M₀ + M₁) / 2) := by
    intro ξ hξ
    obtain ⟨hξre, hξim, -⟩ := segment_conj_facts hv0.le hξ
    constructor
    · exact (cuspGamma_bounds ha0 hL0 hΓ' (by rw [hξre]; exact hu) hξim hv).2.trans
        (mul_le_mul_of_nonneg_right hexpv hLM)
    · exact (cuspGamma_bounds ha0 hL0 hΓ' (w := -ξ) (by rw [Complex.neg_re, abs_neg, hξre]; exact hu)
        (by rwa [Complex.neg_im, abs_neg]) hv).2.trans (mul_le_mul_of_nonneg_right hexpv hLM)
  have hre12 : ∀ ξ ∈ segment ℝ ((starRingEnd ℂ) w) w, |ξ.im| < 1 / 2 := fun ξ hξ => by
    obtain ⟨-, h2, -⟩ := segment_conj_facts hv0.le hξ; linarith
  have hderiv : ∀ ζ ∈ segment ℝ ((starRingEnd ℂ) w) w, ‖deriv (thetaPowerXiC a) ζ - c₀‖ ≤ ‖c₀‖ / 2 := by
    intro ζ hζ
    obtain ⟨hζre, hζim, hζw⟩ := segment_conj_facts hv0.le hζ
    have hA1 : ‖thetaPowerCuspGamma a ζ - thetaPowerCuspGamma a w‖ ≤
        2 * e * ((L * M₀ + M₁) / 2) * (2 * v) := by
      have := (convex_segment ((starRingEnd ℂ) w) w).norm_image_sub_le_of_norm_deriv_le
        (f := thetaPowerCuspGamma a) (C := 2 * e * ((L * M₀ + M₁) / 2))
        (fun ξ hξ => (hasDerivAt_thetaPowerCuspGamma ha0 (re_z_pos_of_im (hre12 ξ hξ))).differentiableAt)
        (fun ξ hξ => by
          rw [(hasDerivAt_thetaPowerCuspGamma ha0 (re_z_pos_of_im (hre12 ξ hξ))).deriv]
          exact (hbd ξ hξ).1)
        (right_mem_segment ℝ _ _) hζ
      exact this.trans (mul_le_mul_of_nonneg_left hζw (by positivity))
    have hA2 : ‖thetaPowerCuspGamma a (-ζ) - thetaPowerCuspGamma a (-w)‖ ≤
        2 * e * ((L * M₀ + M₁) / 2) * (2 * v) := by
      have hder : ∀ ξ ∈ segment ℝ ((starRingEnd ℂ) w) w,
          HasDerivAt (fun x => thetaPowerCuspGamma a (-x)) (cuspGammaDeriv a (-ξ) * (-1)) ξ := by
        intro ξ hξ
        have h' : |(-ξ).im| < 1 / 2 := by rw [Complex.neg_im, abs_neg]; exact hre12 ξ hξ
        exact (hasDerivAt_thetaPowerCuspGamma ha0 (re_z_pos_of_im h')).comp ξ (hasDerivAt_neg ξ)
      have := (convex_segment ((starRingEnd ℂ) w) w).norm_image_sub_le_of_norm_deriv_le
        (f := fun x => thetaPowerCuspGamma a (-x)) (C := 2 * e * ((L * M₀ + M₁) / 2))
        (fun ξ hξ => (hder ξ hξ).differentiableAt)
        (fun ξ hξ => by rw [(hder ξ hξ).deriv, norm_mul, norm_neg, norm_one, mul_one]; exact (hbd ξ hξ).2)
        (right_mem_segment ℝ _ _) hζ
      exact this.trans (mul_le_mul_of_nonneg_left hζw (by positivity))
    have hD : ∀ ξ : ℂ, |ξ.re| ≤ U → |ξ.im| ≤ v → ‖cuspGammaD a ξ‖ ≤ 2 * e * M₁ := by
      intro ξ hξu hξv
      unfold cuspGammaD
      rw [norm_mul]
      exact mul_le_mul ((norm_one_div_E_cpow_le ha0 hL0 hξv).trans hexpv)
        (hΓ _ (mem_gammaRect_of hξu (hξv.trans hv))).2.2 (norm_nonneg _) (by positivity)
    have hD1 := hD ζ (by rw [hζre]; exact hu) hζim
    have hD2 := hD (-ζ) (by rw [Complex.neg_re, abs_neg, hζre]; exact hu) (by rwa [Complex.neg_im, abs_neg])
    have hP := norm_deriv_thetaPowerXiC_sub_le ha0 hr hρr hC (hζim.trans hv) hA1 hA2 hpair hD1 hD2 hL0
    refine hP.trans ?_
    rw [hc₀n]
    exact injectivity_budget hca0 hL1 he0 hm₀ hM₀ hM₁ hC0 hr hL8 hLvC hLK hAw
  have hzc : thetaPowerXiC a ((starRingEnd ℂ) w) = 0 := by rw [thetaPowerXiC_conj, hz, map_zero]
  have hne : (starRingEnd ℂ) w ≠ w := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    linarith
  exact ne_of_norm_deriv_sub_le_half hne (norm_pos_iff.mp hc₀pos)
    (fun x _ => differentiable_thetaPowerXiC ha0 x) hderiv (hzc.trans hz.symm)

/-- **Local real-rootedness at small parameter.** For every `U` and `ρ < 1/2` there is `a₀ > 0` such that for
`0 < a < a₀` every zero `w` of `Λ_a` with `|Re w| ≤ U`, `|Im w| ≤ ρ` is real.  In particular the off-line zeros of
`Λ_a` (which exist for transcendental `a`) escape to infinity as `a → 0⁺`, unconditionally. -/
theorem thetaPowerXiC_zeros_real_of_small (U : ℝ) {ρ : ℝ} (hρ : ρ < 1 / 2) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ → ∀ w : ℂ, |w.re| ≤ U → |w.im| ≤ ρ →
      thetaPowerXiC a w = 0 → w.im = 0 := by
  set U' := max U 0 with hU'
  set ρ' := max ρ 0 with hρ'
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  have hρ'lt : ρ' < 1 / 2 := max_lt hρ (by norm_num)
  set r : ℝ := (1 / 2 - ρ') / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hρr : ρ' + r < 1 / 2 := by rw [hr]; linarith
  obtain ⟨C, hC0, hC⟩ := exists_norm_thetaPowerXiC_sub_cuspMain_le hρr
  obtain ⟨m₀, M₀, M₁, hm₀, hM₀, hM₁, hΓ⟩ := exists_gamma_bounds_gammaRect U' hρ'0 hρ'lt (le_max_right _ _)
  set K : ℝ := 32 * C * M₀ / m₀ + 32 * C * M₁ / m₀ + 4 * C + 8 * C / r with hK
  set B : ℝ := max (8 * C / m₀) (2 * K / m₀) + 1 with hB
  have h8C : 0 ≤ 8 * C / m₀ := by positivity
  have hmax1 := le_max_left (8 * C / m₀) (2 * K / m₀)
  have hmax2 := le_max_right (8 * C / m₀) (2 * K / m₀)
  have hB1 : 1 ≤ B := by linarith
  set L₀ : ℝ := max (max 1 (8 * M₁ / m₀)) (4 * Real.log B) with hL₀
  refine ⟨min (1 / 2) (4 * Real.exp (-L₀) / π), lt_min (by norm_num) (by positivity), ?_⟩
  intro a ha0 ha w hu hv hz
  have ha1 : a ≤ 1 / 2 := (le_of_lt (lt_of_lt_of_le ha (min_le_left _ _)))
  have haE : π * (a / 4) < Real.exp (-L₀) := by
    have := lt_of_lt_of_le ha (min_le_right _ _)
    rw [lt_div_iff₀ Real.pi_pos] at this
    linarith
  set L := Real.log (1 / (π * (a / 4))) with hLdef
  have hLL₀ : L₀ < L := by
    rw [hLdef, one_div, Real.log_inv, lt_neg]
    calc Real.log (π * (a / 4)) < Real.log (Real.exp (-L₀)) :=
          Real.log_lt_log (by positivity) haE
      _ = -L₀ := Real.log_exp _
  have hm1 := le_max_left (max 1 (8 * M₁ / m₀)) (4 * Real.log B)
  have hm2 := le_max_right (max 1 (8 * M₁ / m₀)) (4 * Real.log B)
  have hm3 := le_max_left 1 (8 * M₁ / m₀)
  have hm4 := le_max_right 1 (8 * M₁ / m₀)
  have hL1 : 1 ≤ L := by linarith
  have hL8 : 8 * M₁ ≤ m₀ * L := by
    have : 8 * M₁ / m₀ ≤ L := by linarith
    rw [div_le_iff₀ hm₀] at this; linarith
  have hexpB : B ≤ Real.exp (L / 4) := by
    have : 4 * Real.log B ≤ L := by linarith
    calc B = Real.exp (Real.log B) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (L / 4) := Real.exp_le_exp.mpr (by linarith)
  have hLC : 8 * C ≤ m₀ * Real.exp (L / 4) := by
    have : 8 * C / m₀ ≤ Real.exp (L / 4) := by linarith
    rw [div_le_iff₀ hm₀] at this; linarith
  have hLK : 2 * K ≤ m₀ * Real.exp (L / 4) := by
    have : 2 * K / m₀ ≤ Real.exp (L / 4) := by linarith
    rw [div_le_iff₀ hm₀] at this; linarith
  have hC' : ∀ ζ : ℂ, |ζ.im| ≤ ρ' + r → ‖thetaPowerXiC a ζ - thetaPowerCuspMain a ζ‖ ≤ C :=
    fun ζ hζ => hC a ha0 ha1 ζ hζ
  have huU : ∀ ζ : ℂ, |ζ.re| ≤ U → |ζ.re| ≤ U' := fun ζ h => h.trans (le_max_left _ _)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hz' : thetaPowerXiC a (-w) = 0 := by rw [thetaPowerXiC_neg, hz]
    exact thetaPowerXiC_ne_zero_of_small_im ha0 hρ'0 hr0 hρr hC0 hC' hm₀ hM₀ hM₁ hΓ hL1 hL8 hLC hLK
      (w := -w) (by rw [Complex.neg_re, abs_neg]; exact huU w hu) (by rw [Complex.neg_im]; linarith)
      (by rw [Complex.neg_im]; linarith [(abs_le.mp hv).1, le_max_left ρ 0]) hz'
  · exact thetaPowerXiC_ne_zero_of_small_im ha0 hρ'0 hr0 hρr hC0 hC' hm₀ hM₀ hM₁ hΓ hL1 hL8 hLC hLK
      (huU w hu) hpos (by linarith [(abs_le.mp hv).2, le_max_left ρ 0]) hz

end

end RHTower
