import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartzTranslationCurve
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Every actual tempered functional factors through a finite product of bounded
weighted spatial jets. The original Schwartz topology supplies the finite
seminorm bound; complex Hahn–Banach extends the induced observer on the range.
The original Schwartz space is never supplied with a norm.
-/

open scoped SchwartzMap BoundedContinuousFunction

noncomputable section

namespace RHTower

/-- The literal bounded weighted spatial jet, as a genuine continuous linear map. -/
def thetaSchwartzWeightedJetCLM (k n : ℕ) : 𝓢(ℝ, ℂ) →L[ℂ] (ℝ →ᵇ ℂ) :=
  (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).comp
    ((SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ) ^ k)).comp
      (thetaSchwartzSpatialJetCLM n))

theorem thetaSchwartzWeightedJetCLM_apply (k n : ℕ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaSchwartzWeightedJetCLM k n φ x = (x : ℂ) ^ k * iteratedDeriv n (φ : ℝ → ℂ) x := by
  change SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ
    (SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => (y : ℂ) ^ k)
      (thetaSchwartzSpatialJetCLM n φ)) x = _
  have hg : Function.HasTemperateGrowth (fun y : ℝ => (y : ℂ) ^ k) :=
    Function.Complex.hasTemperateGrowth_ofReal.pow k
  rw [SchwartzMap.toBoundedContinuousFunctionCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg]
  change (x : ℂ) ^ k * thetaSchwartzSpatialJetCLM n φ x = _
  rw [thetaSchwartzSpatialJetCLM_apply]

theorem thetaSchwartzWeightedJetCLM_norm (k n : ℕ) (φ : 𝓢(ℝ, ℂ)) :
    ‖thetaSchwartzWeightedJetCLM k n φ‖ = SchwartzMap.seminorm ℂ k n φ := by
  have hpoint (x : ℝ) :
      ‖thetaSchwartzWeightedJetCLM k n φ x‖ = |x| ^ k * ‖iteratedDeriv n (φ : ℝ → ℂ) x‖ := by
    rw [thetaSchwartzWeightedJetCLM_apply, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs]
  apply le_antisymm
  · refine (BoundedContinuousFunction.norm_le (by positivity)).2 ?_
    intro x
    rw [hpoint]
    exact SchwartzMap.le_seminorm' ℂ k n φ x
  · apply SchwartzMap.seminorm_le_bound' ℂ k n φ (norm_nonneg _)
    intro x
    rw [← hpoint]
    exact BoundedContinuousFunction.norm_coe_le_norm _ x

/-- Concrete finite Banach target with the supremum norm on weighted jets. -/
abbrev thetaSchwartzFiniteJetBanach (s : Finset (ℕ × ℕ)) := s → (ℝ →ᵇ ℂ)

/-- The genuine finite weighted-jet continuous linear map. -/
def thetaSchwartzFiniteJetCLM (s : Finset (ℕ × ℕ)) :
    𝓢(ℝ, ℂ) →L[ℂ] thetaSchwartzFiniteJetBanach s :=
  ContinuousLinearMap.pi (fun j : s => thetaSchwartzWeightedJetCLM j.1.1 j.1.2)

theorem thetaSchwartzFiniteJetCLM_apply (s : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) (j : s) :
    thetaSchwartzFiniteJetCLM s φ j = thetaSchwartzWeightedJetCLM j.1.1 j.1.2 φ := rfl

theorem thetaSchwartzFiniteJetCLM_apply_apply
    (s : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) (j : s) (x : ℝ) :
    thetaSchwartzFiniteJetCLM s φ j x =
      (x : ℂ) ^ j.1.1 * iteratedDeriv j.1.2 (φ : ℝ → ℂ) x :=
  thetaSchwartzWeightedJetCLM_apply j.1.1 j.1.2 φ x

theorem thetaSchwartzFiniteJetCLM_component_norm
    (s : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) (j : s) :
    ‖thetaSchwartzFiniteJetCLM s φ j‖ = SchwartzMap.seminorm ℂ j.1.1 j.1.2 φ :=
  thetaSchwartzWeightedJetCLM_norm j.1.1 j.1.2 φ

theorem thetaSchwartzFiniteJetCLM_sup_le_norm (s : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ ‖thetaSchwartzFiniteJetCLM s φ‖ := by
  apply Seminorm.finset_sup_apply_le (norm_nonneg _)
  intro j hj
  change SchwartzMap.seminorm ℂ j.1 j.2 φ ≤ _
  rw [← thetaSchwartzFiniteJetCLM_component_norm s φ ⟨j, hj⟩]
  exact norm_le_pi_norm (thetaSchwartzFiniteJetCLM s φ) ⟨j, hj⟩

/-- The finite Banach bound is derived from continuity of the actual tempered functional. -/
theorem thetaTempered_norm_le_finiteJet (T : 𝓢'(ℝ, ℂ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, C ≠ 0 ∧
      ∀ φ : 𝓢(ℝ, ℂ), ‖T φ‖ ≤ (C : ℝ) * ‖thetaSchwartzFiniteJetCLM s φ‖ := by
  let t : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := T
  let q : Seminorm ℂ 𝓢(ℝ, ℂ) := (normSeminorm ℂ ℂ).comp t.toLinearMap
  have hq : Continuous q := continuous_norm.comp t.continuous
  obtain ⟨s, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  refine ⟨s, C, hC, ?_⟩
  intro φ
  have hφ := Seminorm.le_def.mp hbound φ
  change ‖T φ‖ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ) at hφ
  exact hφ.trans (mul_le_mul_of_nonneg_left (thetaSchwartzFiniteJetCLM_sup_le_norm s φ) C.property)

/-- Every actual tempered functional is an actual Banach observer of finitely many weighted jets. -/
theorem thetaTempered_exists_finiteJetFactorization (T : 𝓢'(ℝ, ℂ)) :
    ∃ s : Finset (ℕ × ℕ), ∃ L : thetaSchwartzFiniteJetBanach s →L[ℂ] ℂ,
      ∀ φ : 𝓢(ℝ, ℂ), L (thetaSchwartzFiniteJetCLM s φ) = T φ := by
  obtain ⟨s, C, _hC, hbound⟩ := thetaTempered_norm_le_finiteJet T
  let J := thetaSchwartzFiniteJetCLM s
  let t : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := T
  have hker : J.toLinearMap.ker ≤ t.toLinearMap.ker := by
    intro φ hφ
    apply LinearMap.mem_ker.mpr
    change T φ = 0
    apply norm_eq_zero.mp
    apply le_antisymm
    · have hzero : J φ = 0 := LinearMap.mem_ker.mp hφ
      have hφbound : ‖T φ‖ ≤ (C : ℝ) * ‖J φ‖ := hbound φ
      rw [hzero, norm_zero, mul_zero] at hφbound
      exact hφbound
    · exact norm_nonneg _
  let f : J.toLinearMap.range →ₗ[ℂ] ℂ :=
    ((J.toLinearMap.ker).liftQ t.toLinearMap hker).comp
      J.toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hf (φ : 𝓢(ℝ, ℂ)) : f ⟨J φ, J.toLinearMap.mem_range_self φ⟩ = T φ := by
    change (J.toLinearMap.ker).liftQ t.toLinearMap hker
      (J.toLinearMap.quotKerEquivRange.symm ⟨J φ, J.toLinearMap.mem_range_self φ⟩) = _
    exact congrArg ((J.toLinearMap.ker).liftQ t.toLinearMap hker)
      (LinearMap.quotKerEquivRange_symm_apply_image J.toLinearMap φ
        (J.toLinearMap.mem_range_self φ))
  have hnorm : ∀ y : J.toLinearMap.range, ‖f y‖ ≤ (C : ℝ) * ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨φ, rfl⟩ := hy
    change ‖f ⟨J φ, _⟩‖ ≤ (C : ℝ) * ‖J φ‖
    rw [hf]
    exact hbound φ
  let fCLM := f.mkContinuous (C : ℝ) hnorm
  obtain ⟨L, hL, _hLnorm⟩ := exists_extension_norm_eq J.toLinearMap.range fCLM
  refine ⟨s, L, ?_⟩
  intro φ
  exact (hL ⟨J φ, J.toLinearMap.mem_range_self φ⟩).trans (hf φ)

end RHTower
