import GaloisForLFunctions.HTGeometry.MellinGammaNegativeStrip
import GaloisForLFunctions.HTGeometry.GaussianMellinMoments
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# The converse theta relation

A completed Dirichlet series with a reflection law determines the theta transformation law of its
theta function (`converse_theta_relation`).  Abstractly: if `M θ₁(s/2)` and `ε M θ₂((1-s)/2)`
agree, after removing the same polar part `α Γ_ℝ(s) + β Γ_ℝ(s - 1)`, with one function `E`
that is holomorphic and `O(1/(1 + t²))` on the strip `-1/2 ≤ Re s ≤ 3/2`, then

`θ₁(x) = ε x^{-1/2} θ₂(1/x) + α + β x^{-1/2}`   for all `x > 0`.

The polar part is removed by an explicit function on each side.  To the right of the poles
`α e^{-πt} + β t^{-1/2} e^{-πt}` has Mellin transform `α Γ_ℝ(s) + β Γ_ℝ(s - 1)` at `s/2`.  To the left
`α (e^{-πt} - 1) + β t^{-1/2} (e^{-πt} - 1)` has the same transform (`MellinGammaNegativeStrip`).
Both corrected functions are Mellin inversions of `E` on lines of the strip, and the contour shift
identifies them.  Their difference `α + β t^{-1/2}` is the polar term of the theta law.

This is the analytic step of Hamburger's characterization of `ζ` by its functional equation.  No
residue calculus is needed: the poles are absorbed into the two explicit corrections.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- `e^{-πt}`, as a complex-valued function of a real variable. -/
def expNegPi (t : ℝ) : ℂ := ((Real.exp (-(Real.pi * t)) : ℝ) : ℂ)

theorem continuous_expNegPi : Continuous expNegPi := by
  unfold expNegPi
  fun_prop

theorem expNegSubOne_pi_mul (t : ℝ) : expNegSubOne (Real.pi * t) = expNegPi t - 1 := by
  simp [expNegSubOne, expNegPi]

/-- Mellin convergence only depends on the real part of the exponent. -/
theorem MellinConvergent.of_re_eq {f : ℝ → ℂ} {w w' : ℂ} (hf : MellinConvergent f w)
    (h : w.re = w'.re) : MellinConvergent f w' := by
  unfold MellinConvergent at *
  have hm : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (w' - w) * ((t : ℂ) ^ (w - 1) • f t)) (volume.restrict (Ioi 0)) :=
    (ContinuousOn.aestronglyMeasurable (fun t ht =>
      (continuousAt_ofReal_cpow_const t _ (Or.inr (ne_of_gt ht))).continuousWithinAt)
      measurableSet_Ioi).mul hf.aestronglyMeasurable
  have heq : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (w' - w) * ((t : ℂ) ^ (w - 1) • f t) =
      (t : ℂ) ^ (w' - 1) • f t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
    rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Complex.cpow_add _ _ ht0]
    congr 2
    ring
  refine Integrable.mono' hf.norm (hm.congr ?_) ?_
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall heq)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have htpos : (0 : ℝ) < t := ht
    rw [norm_smul, norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos,
      Complex.norm_cpow_eq_rpow_re_of_pos htpos, sub_re, sub_re, h]

theorem mellinConvergent_exp_neg_pi_mul {w : ℂ} (hw : 0 < w.re) : MellinConvergent expNegPi w := by
  have hbase : MellinConvergent (fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ)) w := by
    refine (Complex.GammaIntegral_convergent hw).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    ring
  exact (MellinConvergent.comp_mul_left (f := fun t : ℝ => ((Real.exp (-t) : ℝ) : ℂ))
    Real.pi_pos).mpr hbase

theorem mellin_expNegPi_half {s : ℂ} (hs : 0 < s.re) :
    mellin expNegPi (s / 2) = Complex.Gammaℝ s := by
  have h := mellin_exp_neg_pi_mul (z := s / 2) (by simp; linarith)
  rw [Complex.Gammaℝ_def, neg_div]
  exact h

/-- The polar correction to the right of the poles: `α e^{-πt} + β t^{-1/2} e^{-πt}` has Mellin
transform `α Γ_ℝ(s) + β Γ_ℝ(s - 1)` at `s/2`, for `Re s > 1`. -/
theorem hasMellin_polarRight (α β : ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun t : ℝ => α * expNegPi t + β * ((t : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi t))
      (s / 2) (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by
  have h1 : MellinConvergent expNegPi (s / 2) :=
    mellinConvergent_exp_neg_pi_mul (by simp; linarith)
  have h2 : MellinConvergent (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegPi t) (s / 2) :=
    MellinConvergent.cpow_smul.mpr (mellinConvergent_exp_neg_pi_mul (by simp; linarith))
  have hv1 : mellin expNegPi (s / 2) = Complex.Gammaℝ s := mellin_expNegPi_half (by linarith)
  have hv2 : mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegPi t) (s / 2) =
      Complex.Gammaℝ (s - 1) := by
    rw [mellin_cpow_smul, show s / 2 + -(1 / 2 : ℂ) = (s - 1) / 2 by ring]
    exact mellin_expNegPi_half (by simp; linarith)
  have hA := hasMellin_const_smul h1 α
  have hB := hasMellin_const_smul h2 β
  have hC := hasMellin_add hA.1 hB.1
  refine ⟨hC.1, ?_⟩
  show mellin (fun t : ℝ => α • expNegPi t + β • ((t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegPi t))
    (s / 2) = _
  rw [hC.2, hA.2, hB.2, hv1, hv2]
  rfl

/-- The polar correction to the left of the poles: `α (e^{-πt} - 1) + β t^{-1/2} (e^{-πt} - 1)`
has Mellin transform `α Γ_ℝ(s) + β Γ_ℝ(s - 1)` at `s/2`, for `-1 < Re s < 0`. -/
theorem hasMellin_polarLeft (α β : ℂ) {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 0) :
    HasMellin (fun t : ℝ => α * expNegSubOne (Real.pi * t) +
      β * ((t : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * t)))
      (s / 2) (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by
  have hc1 : MellinConvergent (fun t : ℝ => expNegSubOne (Real.pi * t)) (s / 2) :=
    mellinConvergent_exp_neg_pi_sub_one_half (by linarith) h2
  have hc2 : MellinConvergent
      (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegSubOne (Real.pi * t)) (s / 2) := by
    refine MellinConvergent.cpow_smul.mpr ?_
    rw [show s / 2 + -(1 / 2 : ℂ) = (s - 1) / 2 by ring]
    exact mellinConvergent_exp_neg_pi_sub_one_half (by simp; linarith) (by simp; linarith)
  have hv1 := mellin_exp_neg_pi_sub_one_half (s := s) (by linarith) h2
  have hv2 : mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegSubOne (Real.pi * t)) (s / 2) =
      Complex.Gammaℝ (s - 1) := by
    rw [mellin_cpow_smul, show s / 2 + -(1 / 2 : ℂ) = (s - 1) / 2 by ring]
    exact mellin_exp_neg_pi_sub_one_half (by simp; linarith) (by simp; linarith)
  have hA := hasMellin_const_smul hc1 α
  have hB := hasMellin_const_smul hc2 β
  have hC := hasMellin_add hA.1 hB.1
  refine ⟨hC.1, ?_⟩
  show mellin (fun t : ℝ => α • expNegSubOne (Real.pi * t) +
    β • ((t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegSubOne (Real.pi * t))) (s / 2) = _
  rw [hC.2, hA.2, hB.2, hv1, hv2]
  rfl

/-- The dual term `t^{-1/2} θ(1/t)` has Mellin transform `M θ ((1 - s)/2)` at `s/2`. -/
theorem hasMellin_dual {θ : ℝ → ℂ} {s : ℂ} (hθ : MellinConvergent θ ((1 - s) / 2)) :
    HasMellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) * θ t⁻¹) (s / 2)
      (mellin θ ((1 - s) / 2)) := by
  have hinv : (fun t : ℝ => θ t⁻¹) = fun t : ℝ => θ (t ^ (-1 : ℝ)) := by
    funext t
    rw [Real.rpow_neg_one]
  have hconv : MellinConvergent (fun t : ℝ => θ t⁻¹) (s / 2 + -(1 / 2 : ℂ)) := by
    rw [hinv, MellinConvergent.comp_rpow (by norm_num : (-1 : ℝ) ≠ 0),
      show (s / 2 + -(1 / 2 : ℂ)) / ((-1 : ℝ) : ℂ) = (1 - s) / 2 by push_cast; ring]
    exact hθ
  refine ⟨MellinConvergent.cpow_smul.mpr hconv, ?_⟩
  show mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • θ t⁻¹) (s / 2) = _
  rw [mellin_cpow_smul, mellin_comp_inv]
  congr 1
  ring

/-- The inverse-Mellin integrand `y ↦ x^{-(σ+iy)} E(2(σ+iy))` is integrable when `E` decays like
`1/(1 + t²)` on a strip containing the line `Re s = 2σ`. -/
theorem integrable_cpow_mul_comp_line {E : ℂ → ℂ} {a b C : ℝ}
    (hE : ContinuousOn E (verticalStrip a b))
    (hdecay : ∀ s ∈ verticalStrip a b, ‖E s‖ ≤ C / (1 + s.im ^ 2))
    {σ : ℝ} (hσa : a ≤ 2 * σ) (hσb : 2 * σ ≤ b) {x : ℝ} (hx : 0 < x) :
    Integrable fun y : ℝ => (x : ℂ) ^ (-((σ : ℂ) + y * I)) * E (2 * ((σ : ℂ) + y * I)) := by
  have hmem : ∀ y : ℝ, 2 * ((σ : ℂ) + y * I) ∈ verticalStrip a b := by
    intro y
    rw [mem_verticalStrip]
    simp only [mul_re, re_ofNat, add_re, ofReal_re, ofReal_im, I_re, I_im, im_ofNat]
    constructor <;> linarith
  have hcont : Continuous fun y : ℝ =>
      (x : ℂ) ^ (-((σ : ℂ) + y * I)) * E (2 * ((σ : ℂ) + y * I)) := by
    refine Continuous.mul ?_ ?_
    · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hx.ne'))
    · exact hE.comp_continuous (by fun_prop) hmem
  have hC : 0 ≤ C := by
    have h := hdecay _ (hmem 0)
    have h' : 0 ≤ C / (1 + (2 * ((σ : ℂ) + ((0 : ℝ) : ℂ) * I)).im ^ 2) := (norm_nonneg _).trans h
    simpa using h'
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (x ^ (-σ) * C))
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-((σ : ℂ) + y * I)).re = -σ := by simp
  have him : (2 * ((σ : ℂ) + y * I)).im = 2 * y := by simp
  rw [hre]
  have hb := hdecay _ (hmem y)
  rw [him] at hb
  have h2 : C / (1 + (2 * y) ^ 2) ≤ C * (1 + y ^ 2)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg y])) hC
  calc x ^ (-σ) * ‖E (2 * ((σ : ℂ) + y * I))‖ ≤ x ^ (-σ) * (C * (1 + y ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (hb.trans h2) (by positivity)
    _ = x ^ (-σ) * C * (1 + y ^ 2)⁻¹ := by ring

/-- The horizontal edge of the shifted inverse-Mellin integrand is `O(1/(1 + 4H²))`. -/
theorem norm_integral_horizontal_cpow_mul_comp_le {E : ℂ → ℂ} {a b C : ℝ}
    (hdecay : ∀ s ∈ verticalStrip a b, ‖E s‖ ≤ C / (1 + s.im ^ 2))
    {c d : ℝ} (hcd : c ≤ d) (hca : a ≤ 2 * c) (hdb : 2 * d ≤ b) {x : ℝ} (hx : 0 < x) (H : ℝ) :
    ‖∫ u in c..d, (x : ℂ) ^ (-((u : ℂ) + (H : ℂ) * I)) * E (2 * ((u : ℂ) + (H : ℂ) * I))‖ ≤
      (x ^ (-c) + x ^ (-d)) * (C / (1 + (2 * H) ^ 2)) * |d - c| := by
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
  rw [uIoc_of_le hcd] at hu
  have hmem : 2 * ((u : ℂ) + (H : ℂ) * I) ∈ verticalStrip a b := by
    rw [mem_verticalStrip]
    simp only [mul_re, re_ofNat, add_re, ofReal_re, ofReal_im, I_re, I_im, im_ofNat]
    constructor <;> nlinarith [hu.1, hu.2]
  have hb := hdecay _ hmem
  have him : (2 * ((u : ℂ) + (H : ℂ) * I)).im = 2 * H := by simp
  rw [him] at hb
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-((u : ℂ) + (H : ℂ) * I)).re = -u := by simp
  rw [hre]
  have hxu : x ^ (-u) ≤ x ^ (-c) + x ^ (-d) := by
    rcases le_total 1 x with h1 | h1
    · have := Real.rpow_le_rpow_of_exponent_le h1 (show -u ≤ -c by linarith [hu.1])
      linarith [Real.rpow_pos_of_pos hx (-d)]
    · have := Real.rpow_le_rpow_of_exponent_ge hx h1 (show -d ≤ -u by linarith [hu.2])
      linarith [Real.rpow_pos_of_pos hx (-c)]
  exact mul_le_mul hxu hb (norm_nonneg _) (by positivity)

theorem tendsto_integral_horizontal_cpow_mul_comp {E : ℂ → ℂ} {a b C : ℝ}
    (hdecay : ∀ s ∈ verticalStrip a b, ‖E s‖ ≤ C / (1 + s.im ^ 2))
    {c d : ℝ} (hcd : c ≤ d) (hca : a ≤ 2 * c) (hdb : 2 * d ≤ b) {x : ℝ} (hx : 0 < x)
    {h : ℝ → ℝ} (hh : ∀ T, h T ^ 2 = T ^ 2) :
    Tendsto (fun T : ℝ => ∫ u in c..d,
      (x : ℂ) ^ (-((u : ℂ) + ((h T : ℝ) : ℂ) * I)) * E (2 * ((u : ℂ) + ((h T : ℝ) : ℂ) * I)))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (x ^ (-c) + x ^ (-d)) * (C / (1 + (2 * T) ^ 2)) * |d - c|)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℝ => 1 + (2 * T) ^ 2) atTop atTop := by
      refine tendsto_atTop_add_const_left _ 1 ?_
      exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_id.const_mul_atTop two_pos)
    have h2 : Tendsto (fun T : ℝ => C / (1 + (2 * T) ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    simpa using (h2.const_mul (x ^ (-c) + x ^ (-d))).mul_const |d - c|
  refine squeeze_zero_norm (fun T => ?_) hlim
  have := norm_integral_horizontal_cpow_mul_comp_le hdecay hcd hca hdb hx (h T)
  rwa [show (2 * h T) ^ 2 = (2 * T) ^ 2 by rw [mul_pow, mul_pow, hh T]] at this

theorem differentiableOn_cpow_mul_comp {E : ℂ → ℂ} {a b c d : ℝ}
    (hE : DifferentiableOn ℂ E (verticalStrip a b)) (hca : a ≤ 2 * c) (hdb : 2 * d ≤ b)
    {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (fun w : ℂ => (x : ℂ) ^ (-w) * E (2 * w)) (verticalStrip c d) := by
  refine DifferentiableOn.mul ?_ ?_
  · intro w _
    exact (differentiableAt_id.neg.const_cpow
      (Or.inl (by exact_mod_cast hx.ne'))).differentiableWithinAt
  · refine hE.comp (differentiable_id.const_mul (2 : ℂ)).differentiableOn fun w hw => ?_
    rw [mem_verticalStrip] at hw ⊢
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    constructor <;> linarith [hw.1, hw.2]

/-- **The converse theta relation.**  Let `θ₁, θ₂` be continuous on `(0, ∞)` and
Mellin-convergent at `3/4`.  Suppose a function `E`, holomorphic on the strip
`-1/2 ≤ Re s ≤ 3/2` with `‖E(s)‖ ≤ C/(1 + (Im s)²)` there, satisfies
`M θ₁(s/2) = E(s) + α Γ_ℝ(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2` and
`ε M θ₂((1-s)/2) = E(s) + α Γ_ℝ(s) + β Γ_ℝ(s - 1)` on `Re s = -1/2`.  Then
`θ₁(x) = ε x^{-1/2} θ₂(1/x) + α + β x^{-1/2}` for every `x > 0`.

On the right line the polar correction is the Mellin transform of `α e^{-πt} + β t^{-1/2} e^{-πt}`,
and on the left line that of `α (e^{-πt} - 1) + β t^{-1/2} (e^{-πt} - 1)`.  Mellin inversion on
the two lines, joined by the contour shift across the strip, identifies the two corrected
functions.  The constants `α + β x^{-1/2}` are what the two polar corrections differ by. -/
theorem converse_theta_relation {θ₁ θ₂ : ℝ → ℂ} {E : ℂ → ℂ} {α β ε : ℂ} {C : ℝ}
    (hθ₁c : ContinuousOn θ₁ (Ioi 0)) (hθ₂c : ContinuousOn θ₂ (Ioi 0))
    (hθ₁m : MellinConvergent θ₁ (3 / 4)) (hθ₂m : MellinConvergent θ₂ (3 / 4))
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      mellin θ₁ (s / 2) = E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 →
      ε * mellin θ₂ ((1 - s) / 2) = E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    {x : ℝ} (hx : 0 < x) :
    θ₁ x = ε * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * θ₂ x⁻¹) + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
  set φ₁ : ℝ → ℂ := fun t => θ₁ t - (α * expNegPi t + β * ((t : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi t))
    with hφ₁def
  set φ₂ : ℝ → ℂ := fun t => ε * ((t : ℂ) ^ (-(1 / 2 : ℂ)) * θ₂ t⁻¹) -
    (α * expNegSubOne (Real.pi * t) + β * ((t : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * t)))
    with hφ₂def
  have hEc : ContinuousOn E (verticalStrip (-1 / 2) (3 / 2)) := hE.continuousOn
  -- Mellin data of the corrected functions on the two lines
  have hφ₁ : ∀ y : ℝ, HasMellin φ₁ (((3 / 4 : ℝ) : ℂ) + y * I)
      (E (2 * (((3 / 4 : ℝ) : ℂ) + y * I))) := by
    intro y
    set w : ℂ := ((3 / 4 : ℝ) : ℂ) + y * I with hw
    have hs : (2 * w).re = 3 / 2 := by simp [hw]; norm_num
    have h2w : 2 * w / 2 = w := by ring
    have hpol := hasMellin_polarRight α β (s := 2 * w) (by rw [hs]; norm_num)
    rw [h2w] at hpol
    have hθ : MellinConvergent θ₁ w := MellinConvergent.of_re_eq hθ₁m (by simp [hw])
    have hsub := hasMellin_sub hθ hpol.1
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hpol.2]
    have := hR (2 * w) hs
    rw [h2w] at this
    rw [this]
    ring
  have hφ₂ : ∀ y : ℝ, HasMellin φ₂ (((-1 / 4 : ℝ) : ℂ) + y * I)
      (E (2 * (((-1 / 4 : ℝ) : ℂ) + y * I))) := by
    intro y
    set w : ℂ := ((-1 / 4 : ℝ) : ℂ) + y * I with hw
    have hs : (2 * w).re = -1 / 2 := by simp [hw]; norm_num
    have h2w : 2 * w / 2 = w := by ring
    have hpol := hasMellin_polarLeft α β (s := 2 * w) (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    rw [h2w] at hpol
    have hθ : MellinConvergent θ₂ ((1 - 2 * w) / 2) :=
      MellinConvergent.of_re_eq hθ₂m (by simp [hw]; norm_num)
    have hdual := hasMellin_dual hθ
    rw [h2w] at hdual
    have hεdual := hasMellin_const_smul hdual.1 ε
    have hsub : HasMellin φ₂ w _ := hasMellin_sub hεdual.1 hpol.1
    have hεv : mellin (fun t : ℝ => ε * ((t : ℂ) ^ (-(1 / 2 : ℂ)) * θ₂ t⁻¹)) w =
        ε * mellin θ₂ ((1 - 2 * w) / 2) := by
      rw [← hdual.2]
      exact hεdual.2
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hεv, hpol.2, hL (2 * w) hs]
    ring
  -- Mellin inversion on both lines
  have hcont₁ : ContinuousAt φ₁ x := by
    have h1 : ContinuousAt θ₁ x := hθ₁c.continuousAt (Ioi_mem_nhds hx)
    have h2 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ))) x :=
      continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')
    exact h1.sub ((continuousAt_const.mul continuous_expNegPi.continuousAt).add
      (continuousAt_const.mul (h2.mul continuous_expNegPi.continuousAt)))
  have hcont₂ : ContinuousAt φ₂ x := by
    have h1 : ContinuousAt (fun t : ℝ => θ₂ t⁻¹) x :=
      (hθ₂c.continuousAt (Ioi_mem_nhds (inv_pos.mpr hx))).comp (continuousAt_inv₀ hx.ne')
    have h2 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ))) x :=
      continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')
    have h3 : ContinuousAt (fun t : ℝ => expNegSubOne (Real.pi * t)) x :=
      (continuous_expNegSubOne.comp (continuous_const.mul continuous_id)).continuousAt
    exact (continuousAt_const.mul (h2.mul h1)).sub ((continuousAt_const.mul h3).add
      (continuousAt_const.mul (h2.mul h3)))
  have hvert₁ : VerticalIntegrable (mellin φ₁) (3 / 4 : ℝ) := by
    have h := integrable_cpow_mul_comp_line hEc hdecay (σ := 3 / 4) (by norm_num) (by norm_num)
      (x := 1) one_pos
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [ofReal_one, one_cpow, one_mul]
    exact ((hφ₁ y).2).symm
  have hvert₂ : VerticalIntegrable (mellin φ₂) (-1 / 4 : ℝ) := by
    have h := integrable_cpow_mul_comp_line hEc hdecay (σ := -1 / 4) (by norm_num) (by norm_num)
      (x := 1) one_pos
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [ofReal_one, one_cpow, one_mul]
    exact ((hφ₂ y).2).symm
  have hconv₁ : MellinConvergent φ₁ ((3 / 4 : ℝ) : ℂ) := by simpa using (hφ₁ 0).1
  have hconv₂ : MellinConvergent φ₂ ((-1 / 4 : ℝ) : ℂ) := by simpa using (hφ₂ 0).1
  have hinv₁ := mellinInv_mellin_eq (3 / 4 : ℝ) φ₁ hx hconv₁ hvert₁ hcont₁
  have hinv₂ := mellinInv_mellin_eq (-1 / 4 : ℝ) φ₂ hx hconv₂ hvert₂ hcont₂
  -- the contour shift
  set G : ℂ → ℂ := fun w => (x : ℂ) ^ (-w) * E (2 * w) with hG
  have hI₁ : mellinInv (3 / 4 : ℝ) (mellin φ₁) x =
      (1 / (2 * Real.pi)) • ∫ y : ℝ, G (((3 / 4 : ℝ) : ℂ) + y * I) := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hG, smul_eq_mul]
    rw [(hφ₁ y).2]
  have hI₂ : mellinInv (-1 / 4 : ℝ) (mellin φ₂) x =
      (1 / (2 * Real.pi)) • ∫ y : ℝ, G (((-1 / 4 : ℝ) : ℂ) + y * I) := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hG, smul_eq_mul]
    rw [(hφ₂ y).2]
  have hshift : (∫ y : ℝ, G (((3 / 4 : ℝ) : ℂ) + y * I)) =
      ∫ y : ℝ, G (((-1 / 4 : ℝ) : ℂ) + y * I) := by
    refine integral_vertical_line_eq_of_horizontal_tendsto (by norm_num)
      (differentiableOn_cpow_mul_comp hE (by norm_num) (by norm_num) hx)
      (integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hx)
      (integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hx) ?_ ?_
    · exact tendsto_integral_horizontal_cpow_mul_comp hdecay (by norm_num) (by norm_num)
        (by norm_num) hx (h := fun T => -T) (fun T => by ring)
    · exact tendsto_integral_horizontal_cpow_mul_comp hdecay (by norm_num) (by norm_num)
        (by norm_num) hx (h := fun T => T) (fun T => rfl)
  have heq : φ₁ x = φ₂ x := by
    rw [← hinv₁, ← hinv₂, hI₁, hI₂, hshift]
  simp only [hφ₁def, hφ₂def, expNegSubOne_pi_mul] at heq
  linear_combination heq

end GaloisForLFunctions.HTGeometry
