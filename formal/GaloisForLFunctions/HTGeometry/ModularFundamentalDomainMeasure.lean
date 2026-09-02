import Mathlib.NumberTheory.Modular
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The modular fundamental domain is a fundamental domain for `dx dy / y²`

`SL(2,ℤ)` acts on `ℍ` through its quotient by the kernel `{±1}` of the action; that quotient
`PSL2Z` acts faithfully.  The closed region `𝒟 = {|Re z| ≤ 1/2, |z| ≥ 1}` is a fundamental domain
for `PSL2Z` in the measure-theoretic sense of mathlib: every orbit meets `𝒟`, and two distinct
translates of `𝒟` meet only inside the boundary `𝒟 \ 𝒟ᵒ`.  The boundary lies on the two vertical
lines `Re z = ±1/2` and the unit circle, all Lebesgue-null in `ℂ`, hence null for the invariant
measure `dx dy / y²`.
-/

open UpperHalfPlane MeasureTheory ModularGroup Set
open scoped MatrixGroups Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The action of `SL(2,ℤ)` and of its projectivisation, and the invariant measure -/

instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))

instance : Countable SL(2, ℤ) := Subtype.countable

instance : MeasurableConstSMul SL(2, ℤ) ℍ where
  measurable_const_smul g := by
    simp_rw [sl_moeb]
    exact measurable_const_smul _

instance : SMulInvariantMeasure SL(2, ℤ) ℍ volume where
  measure_preimage_smul g s hs := by
    simp_rw [sl_moeb]
    exact SMulInvariantMeasure.measure_preimage_smul _ hs

/-- The kernel of the action of `SL(2,ℤ)` on `ℍ`; it is `{±1}`. -/
abbrev modularActionKernel : Subgroup SL(2, ℤ) := (MulAction.toPermHom SL(2, ℤ) ℍ).ker

/-- The projective modular group, as the quotient of `SL(2,ℤ)` by the kernel of its action on
`ℍ`. -/
abbrev PSL2Z := SL(2, ℤ) ⧸ modularActionKernel

instance : Countable PSL2Z := Quotient.countable

instance : MulAction PSL2Z ℍ :=
  MulAction.compHom ℍ (QuotientGroup.kerLift (MulAction.toPermHom SL(2, ℤ) ℍ))

theorem PSL2Z_mk_smul (g : SL(2, ℤ)) (z : ℍ) : (QuotientGroup.mk g : PSL2Z) • z = g • z := by
  rw [MulAction.compHom_smul_def, QuotientGroup.kerLift_mk, MulAction.toPermHom_apply,
    Equiv.Perm.smul_def, MulAction.toPerm_apply]

theorem PSL2Z_mk_smul_set (g : SL(2, ℤ)) (s : Set ℍ) :
    (QuotientGroup.mk g : PSL2Z) • s = g • s := by
  ext z
  simp only [mem_smul_set, PSL2Z_mk_smul]

theorem neg_one_mem_modularActionKernel : (-1 : SL(2, ℤ)) ∈ modularActionKernel := by
  rw [MonoidHom.mem_ker, MulAction.toPermHom_apply]
  ext z
  rw [MulAction.toPerm_apply, SL_neg_smul, one_smul]
  rfl

/-- Two matrices have the same image in `PSL2Z` if they are equal up to sign. -/
theorem PSL2Z_mk_eq_of_eq_or_eq_neg {a b : SL(2, ℤ)} (h : a⁻¹ * b = 1 ∨ a⁻¹ * b = -1) :
    (QuotientGroup.mk a : PSL2Z) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq]
  rcases h with h | h
  · rw [h]; exact one_mem _
  · rw [h]; exact neg_one_mem_modularActionKernel

instance : MeasurableConstSMul PSL2Z ℍ where
  measurable_const_smul g := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      simp_rw [PSL2Z_mk_smul]
      exact measurable_const_smul g

instance : SMulInvariantMeasure PSL2Z ℍ volume where
  measure_preimage_smul g s hs := by
    induction g using QuotientGroup.induction_on with
    | H g =>
      simp_rw [PSL2Z_mk_smul]
      exact SMulInvariantMeasure.measure_preimage_smul g hs

/-! ## The boundary of `𝒟` is null -/

/-- A vertical line in `ℂ` is Lebesgue-null. -/
theorem volume_re_eq_zero (c : ℝ) : (volume : Measure ℂ) {z : ℂ | z.re = c} = 0 := by
  have : {z : ℂ | z.re = c} = Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (univ : Set ℝ)) := by
    ext z
    exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩
  rw [this, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod ℝ ℝ, Measure.prod_prod, Real.volume_singleton, zero_mul]

/-- The boundary `𝒟 \ 𝒟ᵒ` lies on the lines `Re z = ±1/2` and the unit circle. -/
theorem coe_fd_diff_fdo_subset :
    UpperHalfPlane.coe '' (fd \ fdo) ⊆
      ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -1 / 2}) ∪ Metric.sphere (0 : ℂ) 1 := by
  rintro _ ⟨z, ⟨⟨h1, h2⟩, hzo⟩, rfl⟩
  simp only [mem_union, mem_setOf_eq, Metric.mem_sphere, dist_zero_right]
  by_cases hn : 1 < Complex.normSq (z : ℂ)
  · have hre : |z.re| = 1 / 2 := le_antisymm h2 (not_lt.mp fun h => hzo ⟨hn, h⟩)
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp hre with h | h
    · exact Or.inl (Or.inl (by rw [coe_re, h]))
    · exact Or.inl (Or.inr (by rw [coe_re, h]; norm_num))
  · have : Complex.normSq (z : ℂ) = 1 := le_antisymm (not_lt.mp hn) h1
    right
    rw [Complex.normSq_eq_norm_sq] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp this

theorem volume_coe_fd_diff_fdo : (volume : Measure ℂ) (UpperHalfPlane.coe '' (fd \ fdo)) = 0 :=
  measure_mono_null coe_fd_diff_fdo_subset
    (measure_union_null (measure_union_null (volume_re_eq_zero _) (volume_re_eq_zero _))
      (Measure.addHaar_sphere volume 0 1))

/-- The boundary of the modular fundamental domain is null for `dx dy / y²`. -/
theorem volume_fd_diff_fdo : (volume : Measure ℍ) (fd \ fdo) = 0 := by
  rw [volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ volume_coe_fd_diff_fdo

/-! ## `𝒟` is a fundamental domain for `PSL2Z` -/

/-- A translate of `𝒟` by a matrix other than `±1` meets `𝒟` only in the boundary. -/
theorem fd_inter_smul_fd_subset {g : SL(2, ℤ)} (hg : g ≠ 1) (hg' : g ≠ -1) :
    fd ∩ g • fd ⊆ fd \ fdo := by
  rintro z ⟨hz, hz'⟩
  refine ⟨hz, fun hzo => ?_⟩
  obtain ⟨w, hw, rfl⟩ := hz'
  have hfd : g⁻¹ • (g • w) ∈ fd := by rwa [inv_smul_smul]
  rcases eq_one_or_neg_one_of_mem_fdo_mem_fd hzo hfd with h | h
  · exact hg (inv_eq_one.mp h)
  · exact hg' (by rw [inv_eq_iff_eq_inv.mp h, inv_neg_one])

/-- **The modular fundamental domain is a fundamental domain** for the action of `PSL2Z` on `ℍ`
with the invariant measure `dx dy / y²`. -/
theorem isFundamentalDomain_fd : IsFundamentalDomain PSL2Z fd (volume : Measure ℍ) where
  nullMeasurableSet := isClosed_fd.measurableSet.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun z => by
    obtain ⟨g, hg⟩ := exists_smul_mem_fd z
    exact ⟨QuotientGroup.mk g, by rwa [PSL2Z_mk_smul]⟩
  aedisjoint := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
    induction b using QuotientGroup.induction_on with
    | H b =>
    show volume ((QuotientGroup.mk a : PSL2Z) • fd ∩ (QuotientGroup.mk b : PSL2Z) • fd) = 0
    rw [PSL2Z_mk_smul_set, PSL2Z_mk_smul_set]
    have hne : a⁻¹ * b ≠ 1 ∧ a⁻¹ * b ≠ -1 := by
      constructor
      · intro h; exact hab (PSL2Z_mk_eq_of_eq_or_eq_neg (Or.inl h))
      · intro h; exact hab (PSL2Z_mk_eq_of_eq_or_eq_neg (Or.inr h))
    have : a • fd ∩ b • fd = a • (fd ∩ (a⁻¹ * b) • fd) := by
      rw [smul_set_inter, smul_smul, mul_inv_cancel_left]
    rw [this, measure_smul]
    exact measure_mono_null (fd_inter_smul_fd_subset hne.1 hne.2) volume_fd_diff_fdo

end

end GaloisForLFunctions.HTGeometry
