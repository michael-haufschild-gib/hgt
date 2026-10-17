import GaloisForLFunctions.RHTower.XiCompactPolarDensity
import GaloisForLFunctions.RHTower.CompactTestXiDivisibilityObstruction

/-!
# Faithful compact-polar realization of the complete Xi Weil space

Compact source coordinates are faithful, their absolute spectral completion
is the full folded Xi divisor space, and the literal Weil pairing has zero
radical on these compact polar tests. No RH premise is used.
-/

open Complex MeasureTheory Filter Topology Set Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower

theorem compactXiEvaluation_eq_zero_iff (f : compactXiTests) :
    compactXiEvaluation f = 0 ↔ f = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply CompactTestXiDivisibility.eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero
      f.property.1.continuous f.property.2
    intro t ht
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp ht
    have he := congrArg (fun v : lp (fun _ : XiZeroCopy => ℂ) 2 => v q) h
    change compactXiEvaluation f q = 0 at he
    simpa only [compactXiEvaluation_apply, hq] using he
  · rintro rfl
    exact map_zero _

theorem compactXiEvaluation_injective : Function.Injective compactXiEvaluation := by
  intro f g h
  apply sub_eq_zero.mp
  apply (compactXiEvaluation_eq_zero_iff (f-g)).mp
  rw [map_sub, h, sub_self]

theorem compactXiPolarEvaluation_injective : Function.Injective compactXiPolarEvaluation := by
  intro f g h
  exact Subtype.ext (compactXiEvaluation_injective h)

def compactXiWeilPairing (f g : compactXiPolarTests) : ℂ :=
  xiWeilPolarization (paperFT (f : compactXiTests)) (paperFT (g : compactXiTests))

theorem compactXiWeilPairing_eq_inner (f g : compactXiPolarTests) :
    compactXiWeilPairing f g =
      inner ℂ (xiWeilLineConjLp (compactXiPolarEvaluation g)) (compactXiPolarEvaluation f) := by
  have hF := complexXi_squareSummable (f : compactXiTests)
    (compactXiTests.re_decay f) (compactXiTests.im_decay f)
  have hG := complexXi_squareSummable (g : compactXiTests)
    (compactXiTests.re_decay g) (compactXiTests.im_decay g)
  have he (h : compactXiPolarTests) (hh : XiWeilSquareSummable (paperFT (h : compactXiTests))) :
      compactXiPolarEvaluation h = xiWeilEvaluationLp (paperFT (h : compactXiTests)) hh := by
    apply Subtype.ext
    funext q
    exact compactXiPolarEvaluation_apply h q
  rw [he f hF, he g hG, inner_xiWeilLineConjLp_evaluation_eq_polarization]
  rfl

theorem reflected_compactXiPolarEvaluation_mem_core (f : compactXiPolarTests) :
    xiWeilLineConjLp (compactXiPolarEvaluation f) ∈ xiWeilCauchyHilbertSubspace := by
  let F := fun z => paperFT (f : compactXiTests) (conj z)
  have hs : XiWeilSquareSummable F := by
    have h := HilbertSchmidt.summable_coe_sq (xiWeilLineConjLp (compactXiPolarEvaluation f))
    simpa only [XiWeilSquareSummable, F, xiWeilLineConjLp_apply,
      compactXiPolarEvaluation_apply, xiSpectralPoint_lineConj] using h
  have he : xiWeilLineConjLp (compactXiPolarEvaluation f) = xiWeilEvaluationLp F hs := by
    apply Subtype.ext
    funext q
    simp only [xiWeilLineConjLp_apply, compactXiPolarEvaluation_apply,
      xiSpectralPoint_lineConj, xiWeilEvaluationLp_apply, F]
  rw [he]
  exact xiWeilEvaluationLp_mem_xiWeilCauchyHilbertSubspace F hs

theorem compactXiWeilPairing_right_radical_iff_zero (f : compactXiPolarTests) :
    (∀ g : compactXiPolarTests, compactXiWeilPairing g f = 0) ↔ f = 0 := by
  constructor
  · intro h
    let w := xiWeilLineConjLp (compactXiPolarEvaluation f)
    have hw : w ∈ compactXiPolarEvaluation.range.topologicalClosure := by
      rw [compactXiPolarEvaluation_closure_eq_cauchyHilbertSubspace]
      exact reflected_compactXiPolarEvaluation_mem_core f
    have hz : ∀ v ∈ compactXiPolarEvaluation.range.topologicalClosure, inner ℂ w v = 0 := by
      apply closure_minimal
      · rintro v ⟨g, rfl⟩
        change inner ℂ (xiWeilLineConjLp (compactXiPolarEvaluation f))
          (compactXiPolarEvaluation g) = 0
        simpa only [compactXiWeilPairing_eq_inner] using h g
      · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hzero : w = 0 := inner_self_eq_zero.mp (hz w hw)
    have hn := norm_xiWeilLineConjLp (compactXiPolarEvaluation f)
    change ‖w‖ = ‖compactXiPolarEvaluation f‖ at hn
    rw [hzero, norm_zero] at hn
    apply compactXiPolarEvaluation_injective
    rw [map_zero, ← norm_eq_zero]
    exact hn.symm
  · rintro rfl g
    rw [compactXiWeilPairing_eq_inner, map_zero]
    have hz : xiWeilLineConjLp 0 = 0 := by
      apply Subtype.ext
      funext q
      rfl
    rw [hz, inner_zero_left]

theorem compactXiWeilPairing_left_radical_iff_zero (f : compactXiPolarTests) :
    (∀ g : compactXiPolarTests, compactXiWeilPairing f g = 0) ↔ f = 0 := by
  rw [← compactXiWeilPairing_right_radical_iff_zero]
  constructor <;> intro h g
  · have hc := xiWeilPolarization_conj_symm
      (paperFT (f : compactXiTests)) (paperFT (g : compactXiTests))
    change compactXiWeilPairing g f = conj (compactXiWeilPairing f g) at hc
    rw [h g, map_zero] at hc
    exact hc
  · have hc := xiWeilPolarization_conj_symm
      (paperFT (g : compactXiTests)) (paperFT (f : compactXiTests))
    change compactXiWeilPairing f g = conj (compactXiWeilPairing g f) at hc
    rw [h g, map_zero] at hc
    exact hc

/-- Faithful source coordinates, exact spectral completion, and no compact
polar Weil radical: one unconditional realization theorem. -/
theorem compact_polar_weil_faithful_complete_realization :
    Function.Injective compactXiPolarEvaluation ∧
    compactXiPolarEvaluation.range.topologicalClosure = xiWeilCauchyHilbertSubspace ∧
    ∀ f : compactXiPolarTests,
      (∀ g : compactXiPolarTests, compactXiWeilPairing f g = 0) ↔ f = 0 :=
  ⟨compactXiPolarEvaluation_injective, compactXiPolarEvaluation_closure_eq_cauchyHilbertSubspace,
    compactXiWeilPairing_left_radical_iff_zero⟩

end RHTower
