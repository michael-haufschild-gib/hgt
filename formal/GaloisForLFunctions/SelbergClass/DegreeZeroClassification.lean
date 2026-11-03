import GaloisForLFunctions.SelbergClass.DegreeZeroSupport
import GaloisForLFunctions.SelbergClass.FiniteSupportRigidity

/-!
# Degree-zero classification in the full Selberg class

An empty Gamma product forces finite Dirichlet support. The Euler-product
axiom and its strict subcritical growth bound then force the Dirichlet unit.
The functional equation fixes the remaining conductor parameter and phase.
-/

noncomputable section
open Complex Filter Set Topology

namespace GaloisForLFunctions.SelbergClass

/-- Positive Gamma scales make degree zero equivalent to an empty product. -/
theorem rank_eq_zero_of_degree_eq_zero (D : RHTower.SelbergGammaData)
    (hD : D.degree = 0) : D.rank = 0 := by
  by_contra h
  have hpos := D.degree_pos_of_rank_pos (Nat.pos_of_ne_zero h)
  rw [hD] at hpos
  exact lt_irrefl _ hpos

/-- Every degree-zero full Selberg function has the coefficients of the unit. -/
theorem coeff_eq_one_of_degree_zero (F : RHTower.SelbergClass)
    (hF : F.gammaData.degree = 0) : F.coeff = 1 := by
  obtain ⟨N, hN⟩ := degreeZero_finite_support F.toExtendedSelbergClass
    (rank_eq_zero_of_degree_eq_zero F.gammaData hF)
  exact coeff_eq_one_of_support_bound F hN

private theorem degreeZeroValue_eq_one (F : RHTower.SelbergClass)
    (hF : F.gammaData.rank = 0) (ha : F.coeff = 1) (s : ℂ) :
    degreeZeroValue F.toExtendedSelbergClass s = 1 := by
  have hE := degreeZeroValue_analyticOnNhd F.toExtendedSelbergClass hF
  have hevent : degreeZeroValue F.toExtendedSelbergClass =ᶠ[𝓝 (2 : ℂ)]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    have hz1 : z ≠ 1 := by intro h; simp [h] at hz
    rw [degreeZeroValue_eq F.toExtendedSelbergClass hz1]
    change F.continuation.value z = 1
    rw [← F.lSeries_eq_value z hz, ha, ← RHTower.SelbergClass.one_coeff,
      RHTower.SelbergClass.one.lSeries_eq_value z hz,
      RHTower.SelbergClass.one_continuation_value]
  exact hE.eqOn_of_preconnected_of_eventuallyEq (fun _ _ => analyticAt_const)
    isPreconnected_univ (mem_univ (2 : ℂ)) hevent (mem_univ s)

/-- The degree-zero classification includes the conductor parameter and root number. -/
theorem degreeZero_classification (F : RHTower.SelbergClass)
    (hF : F.gammaData.degree = 0) :
    F.coeff = 1 ∧ F.gammaData.Q = 1 ∧ F.gammaData.rootNumber = 1 := by
  have hr := rank_eq_zero_of_degree_eq_zero F.gammaData hF
  have ha := coeff_eq_one_of_degree_zero F hF
  have hzero : F.toExtendedSelbergClass (0 : ℂ) = 1 := by
    have h := degreeZeroValue_eq_one F hr ha 0
    rwa [degreeZeroValue_eq F.toExtendedSelbergClass (by norm_num)] at h
  have hfactor : degreeZeroReflectionFactor F.toExtendedSelbergClass 1 = 1 := by
    have h := degreeZeroValue_eq_one F hr ha 1
    simpa [degreeZeroValue, hzero] using h
  have hexp : Real.exp (Real.log F.gammaData.Q * (1 - 2 * (1 : ℂ).re)) = 1 := by
    rw [← norm_degreeZeroReflectionFactor F.toExtendedSelbergClass hr, hfactor, norm_one]
  have hlog : Real.log F.gammaData.Q = 0 := by
    have h := (Real.exp_eq_one_iff _).mp hexp
    norm_num at h
    linarith
  have hQ : F.gammaData.Q = 1 := by
    calc F.gammaData.Q = Real.exp (Real.log F.gammaData.Q) :=
        (Real.exp_log F.gammaData.Q_pos).symm
      _ = 1 := by rw [hlog, Real.exp_zero]
  refine ⟨ha, hQ, ?_⟩
  simpa [degreeZeroReflectionFactor, gammaFactor_eq_exp_of_rank_zero F.gammaData hr, hQ]
    using hfactor

end GaloisForLFunctions.SelbergClass
