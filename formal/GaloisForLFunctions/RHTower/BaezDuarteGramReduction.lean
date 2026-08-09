import GaloisForLFunctions.RHTower.BaezDuarteLeastSquares

/-!
# Reducing the Gram diagonal to two scalars

`BaezDuarteLeastSquares` leaves the Báez-Duarte distances as a function of `bdGram` alone, so `bdGram` is
the single unevaluated object in the whole reduction of the Riemann hypothesis carried out in this folder.
This file takes the elementary part of it as far as it goes and names precisely what remains.

For the diagonal, expanding the square gives three tail integrals of products of fractional parts.  Two of
them collapse under the dilation identity used for the target pairing:

`∫₁^∞ {θv}² v^{-2} dv = θ(1−θ) + θ·fractSqConst`,  `fractSqConst = ∫₁^∞ {v}² v^{-2} dv`,

because `{v}²v^{-2} = 1` on `(θ,1)`.  The third does not: the cross term
`fractCrossTail θ = ∫₁^∞ {θv}{v} v^{-2} dv` mixes two incommensurable dilations and no substitution
separates them.  The outcome is

`bdGram θ θ = θ(1−θ) + θ(1+θ)·fractSqConst − 2θ·fractCrossTail θ`.

So the diagonal is elementary modulo **two** scalars: one constant (`fractSqConst`, classically
`log 2π − 1` territory, i.e. a Stirling-type quantity) and one function of `θ` (`fractCrossTail`, the
Vasyunin/cotangent object for rational `θ`).  Neither is reachable by the dilation-and-split technique that
carried every other computation in this lane — that is the honest boundary, and this file draws it with a
theorem instead of a remark.

Also proved here, and free: `explained_mass_le_one`, the unconditional constraint `−∑ᵢ cᵢθᵢ log θᵢ ≤ 1` on
every solution of a Báez-Duarte normal system, from `d² ≥ 0` and the unit target.
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-! ## The three tail integrals -/

/-- `{v}²·v^{-2}`, the kernel of the squared tail. -/
def fractSqInvSq (v : ℝ) : ℝ := (Int.fract v) ^ 2 * (v⁻¹) ^ 2

theorem measurable_fractSqInvSq : Measurable fractSqInvSq :=
  (measurable_fract.pow_const 2).mul ((measurable_id.inv).pow_const 2)

theorem norm_fractSqInvSq_le {v : ℝ} (hv : 0 < v) : ‖fractSqInvSq v‖ ≤ (v⁻¹) ^ 2 := by
  rw [fractSqInvSq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Int.fract v) ^ 2),
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (v⁻¹) ^ 2)]
  refine mul_le_of_le_one_left (by positivity) ?_
  calc (Int.fract v) ^ 2 ≤ 1 ^ 2 :=
        pow_le_pow_left₀ (Int.fract_nonneg v) (Int.fract_lt_one v).le 2
    _ = 1 := one_pow 2

theorem integrableOn_fractSqInvSq_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn fractSqInvSq (Ioi c) := by
  refine Integrable.mono' (g := fun v => v ^ (-2 : ℝ))
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hc)
    measurable_fractSqInvSq.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := lt_trans hc (mem_Ioi.mp hv)
  rw [← inv_sq_eq_rpow hv0]
  exact norm_fractSqInvSq_le hv0

/-- The squared tail constant `∫₁^∞ {v}² v^{-2} dv`. -/
def fractSqConst : ℝ := ∫ v in Ioi (1 : ℝ), fractSqInvSq v

/-- The cross tail `∫₁^∞ {θv}{v} v^{-2} dv`: the piece no substitution separates. -/
def fractCrossTail (θ : ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), Int.fract (θ * v) * Int.fract v * (v⁻¹) ^ 2

/-! ## The dilation identity for the squared tail -/

theorem integral_Ioc_fractSqInvSq {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (∫ v in Ioc θ 1, fractSqInvSq v) = 1 - θ := by
  have hcongr : ∀ v ∈ Ioo θ 1, fractSqInvSq v = 1 := by
    intro v hv
    have hv0 : (0 : ℝ) < v := lt_trans hθ0 hv.1
    have hfr : Int.fract v = v := Int.fract_eq_self.mpr ⟨hv0.le, hv.2⟩
    rw [fractSqInvSq, hfr]
    field_simp
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr, setIntegral_const, smul_eq_mul, mul_one,
    Real.volume_real_Ioo_of_le hθ1]

/-- **The squared tail of a dilate.**  Elementary: only the constant `fractSqConst` survives. -/
theorem integral_Ioi_one_fractSq_dilate {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    (∫ u in Ioi (1 : ℝ), (Int.fract (θ * u)) ^ 2 * (u⁻¹) ^ 2)
      = θ * (1 - θ) + θ * fractSqConst := by
  have hkey := integral_comp_mul_left_Ioi fractSqInvSq 1 hθ0
  rw [mul_one] at hkey
  have hcongr : ∀ u ∈ Ioi (1 : ℝ),
      (Int.fract (θ * u)) ^ 2 * (u⁻¹) ^ 2 = θ ^ 2 * fractSqInvSq (θ * u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hθne : θ ≠ 0 := ne_of_gt hθ0
    have hune : u ≠ 0 := ne_of_gt hu0
    rw [fractSqInvSq]
    field_simp
  have hdisj : Disjoint (Ioc θ 1) (Ioi 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc θ 1 ∪ Ioi 1 = Ioi θ := Set.Ioc_union_Ioi_eq_Ioi hθ1
  have hray : (∫ v in Ioi θ, fractSqInvSq v)
      = (∫ v in Ioc θ 1, fractSqInvSq v) + ∫ v in Ioi (1:ℝ), fractSqInvSq v := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioi
      ((integrableOn_fractSqInvSq_Ioi hθ0).mono_set
        (by rw [← hunion]; exact Set.subset_union_left))
      ((integrableOn_fractSqInvSq_Ioi hθ0).mono_set
        (by rw [← hunion]; exact Set.subset_union_right))
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul, hkey, smul_eq_mul, hray,
    integral_Ioc_fractSqInvSq hθ0 hθ1, fractSqConst]
  field_simp

/-! ## The diagonal -/

/-- **The Gram diagonal, reduced.**  Two scalars remain: the constant `fractSqConst` and the cross tail. -/
theorem bdGram_self_eq (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    bdGram θ θ = θ * (1 - θ) + θ * (1 + θ) * fractSqConst - 2 * θ * fractCrossTail θ := by
  have hbound : ∀ (f : ℝ → ℝ), Measurable f → (∀ v ∈ Ioi (1:ℝ), ‖f v‖ ≤ (v⁻¹) ^ 2) →
      IntegrableOn f (Ioi 1) := by
    intro f hf hb
    refine Integrable.mono' (g := fun v => v ^ (-2 : ℝ))
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos) hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one (mem_Ioi.mp hv)
    rw [← inv_sq_eq_rpow hv0]
    exact hb v hv
  have hI1 : IntegrableOn (fun u => (Int.fract (θ * u)) ^ 2 * (u⁻¹) ^ 2) (Ioi 1) := by
    refine hbound _ ((measurable_fract.comp (measurable_const_mul θ)).pow_const 2 |>.mul
      ((measurable_id.inv).pow_const 2)) ?_
    intro v hv
    have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one (mem_Ioi.mp hv)
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (Int.fract (θ * v)) ^ 2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (v⁻¹) ^ 2)]
    refine mul_le_of_le_one_left (by positivity) ?_
    calc (Int.fract (θ * v)) ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (Int.fract_nonneg _) (Int.fract_lt_one _).le 2
      _ = 1 := one_pow 2
  have hI2 : IntegrableOn (fun u => Int.fract (θ * u) * Int.fract u * (u⁻¹) ^ 2) (Ioi 1) := by
    refine hbound _ (((measurable_fract.comp (measurable_const_mul θ)).mul measurable_fract).mul
      ((measurable_id.inv).pow_const 2)) ?_
    intro v hv
    have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one (mem_Ioi.mp hv)
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (Int.fract_nonneg _), abs_of_nonneg (Int.fract_nonneg _),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (v⁻¹) ^ 2)]
    refine mul_le_of_le_one_left (by positivity) ?_
    calc Int.fract (θ * v) * Int.fract v ≤ 1 * 1 :=
          mul_le_mul (Int.fract_lt_one _).le (Int.fract_lt_one _).le (Int.fract_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hI3 : IntegrableOn fractSqInvSq (Ioi 1) := integrableOn_fractSqInvSq_Ioi one_pos
  have hexp : ∀ u ∈ Ioi (1:ℝ), bdGenReal θ u * bdGenReal θ u
      = (Int.fract (θ * u)) ^ 2 * (u⁻¹) ^ 2
        - 2 * θ * (Int.fract (θ * u) * Int.fract u * (u⁻¹) ^ 2)
        + θ ^ 2 * fractSqInvSq u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    have hune : u ≠ 0 := ne_of_gt hu0
    rw [bdGenReal, fractSqInvSq]
    field_simp
    ring
  rw [bdGram, setIntegral_congr_fun measurableSet_Ioi hexp,
    integral_add (by exact hI1.sub (hI2.const_mul (2 * θ))) (hI3.const_mul (θ ^ 2)),
    integral_sub hI1 (hI2.const_mul (2 * θ)), integral_const_mul, integral_const_mul,
    integral_Ioi_one_fractSq_dilate hθ0 hθ1, ← fractCrossTail, ← fractSqConst]
  ring

/-- **An unconditional constraint on every Báez-Duarte normal system.**  Since the target is a unit vector
and distances are nonnegative, the explained mass never exceeds `1`. -/
theorem explained_mass_le_one {I : Type*} [Fintype I] (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) (c : I → ℝ)
    (hc : ∀ i, ∑ j, bdGram (θ i) (θ j) * c j = -(θ i * Real.log (θ i))) :
    -∑ i, c i * (θ i * Real.log (θ i)) ≤ 1 := by
  have h := bdDist_sq_eq_of_realNormalEquations θ hθ c hc
  have hnn : 0 ≤ bdDist θ ^ 2 := by positivity
  linarith [h, hnn]

end RHTower

end
