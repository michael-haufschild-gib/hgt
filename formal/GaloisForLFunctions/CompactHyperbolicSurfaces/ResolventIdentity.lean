import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventKernelBounds
import GaloisForLFunctions.CompactHyperbolicSurfaces.ConvolutionProfiles

/-!
# The resolvent identity for the kernels `k_s`

For `1 < a < s`:

  `k_s ⋆ k_a = (k_a − k_s)/(s(s − 1) − a(a − 1))`

as point-pair kernels (`convK_resKernel_ae`): for every `z`, for almost every `w`,
`∫ k_s(u(z, ξ)) k_a(u(ξ, w)) dμ(ξ) = D_{a,s}(u(z, w))/(s(s − 1) − a(a − 1))`.

Abel transforms turn `⋆` into convolution on `ℝ` (`abelL_convProfile`), and with `α = s − ½`,
`β = a − ½` the exponentials convolve explicitly,

  `∫ e^{−α|σ|} e^{−β|τ − σ|} dσ = 2(α e^{−β|τ|} − β e^{−α|τ|})/(α² − β²)`  (`lintegral_exp_abs_conv`),

which is the Abel transform of the right-hand side (`abelL_diffKernel`).  Abel inversion
(`ae_eq_of_abelL_eq`) and the absence of null-set mass of `u(z, ·)` finish the proof.
-/

open MeasureTheory Set Filter Real UpperHalfPlane
open scoped ENNReal

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Reflection invariance of Lebesgue measure for lower integrals. -/
theorem lintegral_comp_neg_eq (f : ℝ → ℝ≥0∞) : ∫⁻ x : ℝ, f (-x) = ∫⁻ x : ℝ, f x := by
  have hmap := Real.map_volume_mul_left (show (-1 : ℝ) ≠ 0 by norm_num)
  have h1 : ∫⁻ x : ℝ, f (-1 * x) = ∫⁻ x : ℝ, f x ∂(Measure.map ((-1 : ℝ) * ·) volume) :=
    (lintegral_map_equiv f (Homeomorph.mulLeft₀ (-1 : ℝ) (by norm_num)).toMeasurableEquiv).symm
  simp only [neg_one_mul] at h1 hmap
  rw [h1, hmap, lintegral_smul_measure]
  norm_num

theorem setLIntegral_exp_mul_Ioi {c : ℝ} (hc : c < 0) (x₀ : ℝ) :
    ∫⁻ σ in Ioi x₀, ENNReal.ofReal (Real.exp (c * σ)) = ENNReal.ofReal (-Real.exp (c * x₀) / c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi hc x₀)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_mul_Ioi hc]

theorem setLIntegral_exp_mul_Iic {c : ℝ} (hc : 0 < c) (x₀ : ℝ) :
    ∫⁻ σ in Iic x₀, ENNReal.ofReal (Real.exp (c * σ)) = ENNReal.ofReal (Real.exp (c * x₀) / c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Iic hc x₀)
    (Eventually.of_forall fun _ => (Real.exp_pos _).le), integral_exp_mul_Iic hc]

theorem setLIntegral_exp_mul_Ioc {c : ℝ} (hc : c ≠ 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫⁻ σ in Ioc 0 τ, ENNReal.ofReal (Real.exp (c * σ)) =
      ENNReal.ofReal ((Real.exp (c * τ) - 1) / c) := by
  have hint : IntegrableOn (fun σ => Real.exp (c * σ)) (Ioc 0 τ) :=
    (by fun_prop : Continuous fun σ : ℝ => Real.exp (c * σ)).integrableOn_Ioc
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => (Real.exp_pos _).le),
    ← intervalIntegral.integral_of_le hτ]
  congr 1
  have hd : ∀ x ∈ uIcc 0 τ, HasDerivAt (fun σ => Real.exp (c * σ) / c) (Real.exp (c * x)) x := by
    intro x _
    have := ((Real.hasDerivAt_exp (c * x)).comp x ((hasDerivAt_id x).const_mul c)).div_const c
    refine this.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous fun σ : ℝ => Real.exp (c * σ)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  ring

/-- **Convolution of two exponentials.**  For `α ≠ β` positive,
`∫ e^{−α|σ|} e^{−β|τ − σ|} dσ = 2(α e^{−β|τ|} − β e^{−α|τ|})/(α² − β²)`. -/
theorem lintegral_exp_abs_conv {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α) (τ : ℝ) :
    ∫⁻ σ : ℝ, ENNReal.ofReal (Real.exp (-(α * |σ|))) * ENNReal.ofReal (Real.exp (-(β * |τ - σ|))) =
      ENNReal.ofReal (2 * (α * Real.exp (-(β * |τ|)) - β * Real.exp (-(α * |τ|))) / (α ^ 2 - β ^ 2)) := by
  -- reduce to `τ ≥ 0`
  wlog hτ : 0 ≤ τ generalizing τ
  · have h := this (-τ) (by linarith)
    rw [abs_neg] at h
    rw [← h, ← lintegral_comp_neg_eq]
    refine lintegral_congr fun σ => ?_
    rw [abs_neg, show -τ - σ = -(τ - -σ) by ring, abs_neg]
  set f : ℝ → ℝ≥0∞ := fun σ =>
    ENNReal.ofReal (Real.exp (-(α * |σ|))) * ENNReal.ofReal (Real.exp (-(β * |τ - σ|)))
  have hf : Measurable f := by fun_prop
  have hsplit : ∫⁻ σ, f σ =
      (∫⁻ σ in Iic 0, f σ) + ((∫⁻ σ in Ioc 0 τ, f σ) + ∫⁻ σ in Ioi τ, f σ) := by
    rw [← lintegral_union measurableSet_Ioi (Ioc_disjoint_Ioi_same), Ioc_union_Ioi_eq_Ioi hτ,
      ← compl_Ioi, add_comm, lintegral_add_compl f measurableSet_Ioi]
  have h1 : ∫⁻ σ in Iic 0, f σ = ENNReal.ofReal (Real.exp (-(β * τ)) / (α + β)) := by
    have : ∀ σ ∈ Iic (0 : ℝ), f σ = ENNReal.ofReal (Real.exp (-(β * τ))) *
        ENNReal.ofReal (Real.exp ((α + β) * σ)) := by
      intro σ hσ
      have hσ' : σ ≤ 0 := hσ
      simp only [f, abs_of_nonpos hσ', abs_of_nonneg (by linarith : 0 ≤ τ - σ)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    rw [setLIntegral_congr_fun measurableSet_Iic this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_exp_mul_Iic (by linarith), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1; simp; ring
  have h2 : ∫⁻ σ in Ioc 0 τ, f σ =
      ENNReal.ofReal ((Real.exp (-(α * τ)) - Real.exp (-(β * τ))) / (β - α)) := by
    have : ∀ σ ∈ Ioc (0 : ℝ) τ, f σ = ENNReal.ofReal (Real.exp (-(β * τ))) *
        ENNReal.ofReal (Real.exp ((β - α) * σ)) := by
      intro σ hσ
      simp only [f, abs_of_pos hσ.1, abs_of_nonneg (by linarith [hσ.2] : 0 ≤ τ - σ)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    rw [setLIntegral_congr_fun measurableSet_Ioc this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_exp_mul_Ioc (by linarith) hτ, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [mul_div_assoc', mul_sub, mul_one, ← Real.exp_add]
    congr 2; ring_nf
  have h3 : ∫⁻ σ in Ioi τ, f σ = ENNReal.ofReal (Real.exp (-(α * τ)) / (α + β)) := by
    have : ∀ σ ∈ Ioi τ, f σ = ENNReal.ofReal (Real.exp (β * τ)) *
        ENNReal.ofReal (Real.exp ((-(α + β)) * σ)) := by
      intro σ hσ
      have hσ' : τ < σ := hσ
      simp only [f, abs_of_pos (by linarith : 0 < σ), abs_of_neg (by linarith : τ - σ < 0)]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_add, ← Real.exp_add]
      congr 2; ring
    rw [setLIntegral_congr_fun measurableSet_Ioi this, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      setLIntegral_exp_mul_Ioi (by linarith), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [neg_div_neg_eq, mul_div_assoc', ← Real.exp_add]
    congr 2; ring
  rw [hsplit, h1, h2, h3, abs_of_nonneg hτ]
  have hp1 : 0 ≤ Real.exp (-(β * τ)) / (α + β) := by positivity
  have hp3 : 0 ≤ Real.exp (-(α * τ)) / (α + β) := by positivity
  have hp2 : 0 ≤ (Real.exp (-(α * τ)) - Real.exp (-(β * τ))) / (β - α) := by
    have : Real.exp (-(α * τ)) ≤ Real.exp (-(β * τ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    exact div_nonneg_of_nonpos (by linarith) (by linarith)
  rw [← ENNReal.ofReal_add hp2 hp3, ← ENNReal.ofReal_add hp1 (add_nonneg hp2 hp3)]
  congr 1
  have hne1 : α + β ≠ 0 := by linarith
  have hne2 : β - α ≠ 0 := by linarith
  have hne3 : α ^ 2 - β ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-! ### The identity -/

section identity

variable {a s : ℝ} (ha : 1 < a) (has : a < s)
include ha has

theorem resConst_pos : 0 < s * (s - 1) - a * (a - 1) := by nlinarith

/-- `𝒜(k_s ⋆ k_a) = 𝒜((k_a − k_s)/(s(s−1) − a(a−1)))`. -/
theorem abelL_convProfile_resKernel (τ : ℝ) :
    abelL (convProfile (resKernel s) (resKernel a)) τ =
      abelL (fun u => ENNReal.ofReal (diffKernel a s u / (s * (s - 1) - a * (a - 1)))) τ := by
  have ha' : 1 / 2 < a := by linarith
  have hs' : 1 / 2 < s := by linarith
  have hc := resConst_pos ha has
  rw [abelL_convProfile (measurable_resKernel s) (measurable_resKernel a)]
  simp_rw [abelL_resKernel hs', abelL_resKernel ha']
  have h2s0 : 0 < 2 * s - 1 := by linarith
  have h2a0 : 0 < 2 * a - 1 := by linarith
  have hconv : ∀ σ : ℝ, ENNReal.ofReal (Real.exp (-((s - 1 / 2) * |σ|)) / (2 * s - 1)) *
      ENNReal.ofReal (Real.exp (-((a - 1 / 2) * |τ - σ|)) / (2 * a - 1)) =
      ENNReal.ofReal (1 / ((2 * s - 1) * (2 * a - 1))) *
        (ENNReal.ofReal (Real.exp (-((s - 1 / 2) * |σ|))) *
          ENNReal.ofReal (Real.exp (-((a - 1 / 2) * |τ - σ|)))) := by
    intro σ
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (one_div_pos.mpr (mul_pos h2s0 h2a0)).le,
      ← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le h2s0.le)]
    congr 1; field_simp
  simp_rw [hconv]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_exp_abs_conv (by linarith) (by linarith) (by linarith) τ]
  have hD : abelL (fun u => ENNReal.ofReal (diffKernel a s u / (s * (s - 1) - a * (a - 1)))) τ =
      ENNReal.ofReal (1 / (s * (s - 1) - a * (a - 1))) *
        abelL (fun u => ENNReal.ofReal (diffKernel a s u)) τ := by
    rw [abelL, abelL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun η => ?_
    rw [← ENNReal.ofReal_mul (one_div_pos.mpr hc).le, div_eq_mul_one_div, mul_comm]
  rw [hD, abelL_diffKernel ha' has.le, ← ENNReal.ofReal_mul (one_div_pos.mpr (mul_pos h2s0 h2a0)).le,
    ← ENNReal.ofReal_mul (one_div_pos.mpr hc).le]
  congr 1
  generalize Real.exp (-((a - 1 / 2) * |τ|)) = E1
  generalize Real.exp (-((s - 1 / 2) * |τ|)) = E2
  rw [show (s - 1 / 2) ^ 2 - (a - 1 / 2) ^ 2 = s * (s - 1) - a * (a - 1) by ring]
  field_simp

/-- **The resolvent identity for the profiles.** -/
theorem convProfile_resKernel_ae :
    convProfile (resKernel s) (resKernel a) =ᵐ[volume.restrict (Ioi 0)]
      fun u => ENNReal.ofReal (diffKernel a s u / (s * (s - 1) - a * (a - 1))) := by
  have ha' : 1 / 2 < a := by linarith
  have hc := resConst_pos ha has
  refine ae_eq_of_abelL_eq (measurable_convProfile (measurable_resKernel s) (measurable_resKernel a))
    (ENNReal.measurable_ofReal.comp ((continuous_diffKernel ha' has.le).measurable.div_const _))
    (abelL_convProfile_resKernel ha has) fun v hv => ?_
  obtain ⟨C, hC0, hC⟩ := exists_resKernel_le_rpow_neg ha'
  have hb : ∀ u ∈ Ioi v, ENNReal.ofReal (diffKernel a s u / (s * (s - 1) - a * (a - 1))) ≤
      ENNReal.ofReal (C / (s * (s - 1) - a * (a - 1)) * u ^ (-a)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hv hu
    have h1 := (ofReal_diffKernel_le ha' has.le hu0).trans (hC u hu0)
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc]
    exact h1
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hb) ?_
  exact ((integrableOn_Ioi_rpow_of_lt (by linarith) hv).const_mul _).lintegral_lt_top

/-- **The resolvent identity.**  For every `z` and almost every `w`,
`(k_s ⋆ k_a)(z, w) = D_{a,s}(u(z, w))/(s(s − 1) − a(a − 1))`. -/
theorem convK_resKernel_ae (z : ℍ) :
    ∀ᵐ w : ℍ, convK (resKernel s) (resKernel a) z w =
      ENNReal.ofReal (diffKernel a s (pairU z w) / (s * (s - 1) - a * (a - 1))) := by
  have ha' : 1 / 2 < a := by linarith
  set κ := convProfile (resKernel s) (resKernel a)
  set κ' : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (diffKernel a s u / (s * (s - 1) - a * (a - 1)))
  have hE : MeasurableSet {u : ℝ | κ u ≠ κ' u} :=
    (measurableSet_eq_fun (measurable_convProfile (measurable_resKernel s) (measurable_resKernel a))
      (ENNReal.measurable_ofReal.comp ((continuous_diffKernel ha' has.le).measurable.div_const _))).compl
  have hnull : volume ({u : ℝ | κ u ≠ κ' u} ∩ Ioi 0) = 0 := by
    rw [← Measure.restrict_apply hE]
    exact ae_iff.mp (convProfile_resKernel_ae ha has)
  have h0 : volume ({0} : Set ℝ) = 0 := Real.volume_singleton
  have hA := volume_pairU_preimage_eq_zero z (hE.inter measurableSet_Ioi) hnull
  have hB := volume_pairU_preimage_eq_zero z (measurableSet_singleton 0) h0
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_union_null hA hB)
  intro w hw
  simp only [mem_setOf_eq] at hw
  rw [convK_eq_convProfile] at hw
  rcases (pairU_nonneg z w).lt_or_eq with h | h
  · exact Or.inl ⟨hw, h⟩
  · exact Or.inr h.symm

end identity

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
