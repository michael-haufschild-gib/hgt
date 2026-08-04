import GaloisForLFunctions.RHTower.BandUncertainty
import GaloisForLFunctions.RHTower.BandOperatorContraction
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# The strict band gap

The band operator is a positive contraction, and its norm is never attained at `1`.  Two mechanisms
close the two ways `‖B_c‖ = 1` could happen, and the Fredholm alternative says these are the only
ways:

* if `1` is an eigenvalue, its eigenvector has a continuous representative whose spectral tail
  vanishes, and the uncertainty principle makes it zero — contradicting that an eigenvector is
  nonzero;
* if `1` lies in the resolvent set, mathlib's Rayleigh theory produces a uniform gap
  `rayleigh <= ‖B_c‖ - eps`, and since the form is positive the norm *is* the supremum of the
  Rayleigh quotients, so `‖B_c‖ <= ‖B_c‖ - eps`.

Hence `‖B_c‖ < 1` for every aperture: no signal supported in the band is band-limited, and the
leakage `1 - ‖B_c‖` is strictly positive — so its logarithm is defined, which is what any
logarithmic-derivative statement about the leakage needs.
-/

noncomputable section

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral FourierTransform

open _root_.RHTower

/-- The band `L²` is nontrivial: the constant test function has energy `2`. -/
theorem bandClass_one_ne_zero :
    bandClass (fun _ : ℝ => (1 : ℝ)) continuous_const ≠ 0 := by
  intro h
  have hnorm : ‖bandClass (fun _ : ℝ => (1 : ℝ)) continuous_const‖ ^ 2 = 0 := by
    rw [h, norm_zero]
    norm_num
  rw [norm_sq_bandClass] at hnorm
  have hval : (∫ _x in (-1 : ℝ)..1, (1 : ℝ) ^ 2) = 2 := by
    rw [intervalIntegral.integral_const]
    norm_num
  rw [hval] at hnorm
  norm_num at hnorm

/-- A continuous test function vanishing on the open band has vanishing energy: the two endpoints are
a null set. -/
theorem integral_sq_eq_zero_of_eqOn_zero_Ioo {Φ : ℝ → ℝ}
    (h : ∀ x ∈ Ioo (-1 : ℝ) 1, Φ x = 0) : (∫ x in (-1 : ℝ)..1, Φ x ^ 2) = 0 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    ← MeasureTheory.setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (-1 : ℝ)) (b := 1))]
  refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_
  rw [h x hx]
  ring

/-- **An eigenvector at `1` cannot exist.**  Its continuous representative has vanishing spectral
tail, so the uncertainty principle makes it zero on the open band, hence of zero energy. -/
theorem not_hasEigenvalue_one {c : ℝ} (hc : 0 < c) :
    ¬ Module.End.HasEigenvalue
        ((bandOperatorL2 c : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1) :
          RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] RealIntervalL2 (-1 : ℝ) 1) (1 : ℝ) := by
  intro heig
  obtain ⟨ψ, hmem, hne⟩ := heig.exists_hasEigenvector
  have heq : bandOperatorL2 c ψ = (1 : ℝ) • ψ := Module.End.mem_eigenspace_iff.mp hmem
  -- the continuous representative of the eigenvector
  have hΦcont : Continuous (eigenExtension c 1 ψ) := continuous_eigenExtension c 1 ψ
  have hclass : bandClass (eigenExtension c 1 ψ) hΦcont = ψ := by
    rw [Lp.ext_iff]
    exact (coeFn_bandClass (eigenExtension c 1 ψ) hΦcont).trans
      (eigenExtension_ae_eq one_ne_zero heq).symm
  -- its Rayleigh quotient is one, so its spectral tail vanishes
  have hform : (inner ℝ (bandOperatorL2 c ψ) ψ : ℝ) = ‖ψ‖ ^ 2 := by
    rw [heq, one_smul, real_inner_self_eq_norm_sq]
  have hE : (∫ x in (-1 : ℝ)..1, eigenExtension c 1 ψ x ^ 2) = ‖ψ‖ ^ 2 := by
    rw [← norm_sq_bandClass (eigenExtension c 1 ψ) hΦcont, hclass]
  have hF : (∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1,
      sincKernelSmooth c x y * (eigenExtension c 1 ψ x * eigenExtension c 1 ψ y)) = ‖ψ‖ ^ 2 := by
    rw [← inner_bandOperatorL2_bandClass c (eigenExtension c 1 ψ) hΦcont, hclass, hform]
  have htail : (∫ ξ in (Icc (-(c / (2 * Real.pi))) (c / (2 * Real.pi)))ᶜ,
      ‖𝓕 (bandTrunc (eigenExtension c 1 ψ)) ξ‖ ^ 2) = 0 := by
    rw [← leakage_eq_spectral_tail hc hΦcont, hE, hF]
    ring
  -- the uncertainty principle then kills the eigenvector
  have hzeroΦ := eqOn_zero_of_spectral_tail_eq_zero hc hΦcont htail
  have hEzero : (∫ x in (-1 : ℝ)..1, eigenExtension c 1 ψ x ^ 2) = 0 :=
    integral_sq_eq_zero_of_eqOn_zero_Ioo hzeroΦ
  rw [hE] at hEzero
  exact hne (norm_eq_zero.mp (by nlinarith [norm_nonneg ψ]))

/-- **The strict band gap.**  For every aperture the band operator has norm strictly below one, so the
band leakage is strictly positive. -/
theorem norm_bandOperatorL2_lt_one {c : ℝ} (hc : 0 < c) : ‖bandOperatorL2 c‖ < 1 := by
  rcases lt_or_ge (‖bandOperatorL2 c‖) 1 with h | h
  · exact h
  have hone : ‖bandOperatorL2 c‖ = 1 := le_antisymm (norm_bandOperatorL2_le_one hc) h
  haveI hnt : Nontrivial (RealIntervalL2 (-1 : ℝ) 1) :=
    nontrivial_of_ne _ _ bandClass_one_ne_zero
  have hsym : ((bandOperatorL2 c : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1) :
      RealIntervalL2 (-1 : ℝ) 1 →ₗ[ℝ] RealIntervalL2 (-1 : ℝ) 1).IsSymmetric := fun f g =>
    bandOperatorL2_symmetric c f g
  rcases (isCompactOperator_bandOperatorL2 c).hasEigenvalue_or_mem_resolventSet
    (μ := (1 : ℝ)) one_ne_zero with heig | hres
  · exact absurd heig (not_hasEigenvalue_one hc)
  · -- the resolvent branch contradicts the Rayleigh supremum
    have hres' : (algebraMap ℝ ℝ) ‖bandOperatorL2 c‖ ∈ resolventSet ℝ (bandOperatorL2 c) := by
      simpa [hone] using hres
    obtain ⟨ε, hε, hle⟩ :=
      (bandOperatorL2 c).rayleighQuotient_le_of_norm_mem_resolventSet hres'
    have hsup : (⨆ f : RealIntervalL2 (-1 : ℝ) 1, |(bandOperatorL2 c).rayleighQuotient f|)
        ≤ ‖bandOperatorL2 c‖ - ε := by
      refine ciSup_le fun f => ?_
      have hposq : 0 ≤ (bandOperatorL2 c).rayleighQuotient f := by
        rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
          RCLike.re_to_real]
        exact div_nonneg (inner_bandOperatorL2_nonneg hc f) (by positivity)
      rw [abs_of_nonneg hposq]
      exact hle f
    have hcontra : ‖bandOperatorL2 c‖ ≤ ‖bandOperatorL2 c‖ - ε :=
      (ContinuousLinearMap.norm_eq_iSup_rayleighQuotient (bandOperatorL2 c) hsym).trans_le hsup
    linarith

/-- **The band leakage is strictly positive.** -/
theorem one_sub_norm_bandOperatorL2_pos {c : ℝ} (hc : 0 < c) :
    0 < 1 - ‖bandOperatorL2 c‖ := by
  have h := norm_bandOperatorL2_lt_one hc
  linarith

end GaloisForLFunctions.RHTower

end
