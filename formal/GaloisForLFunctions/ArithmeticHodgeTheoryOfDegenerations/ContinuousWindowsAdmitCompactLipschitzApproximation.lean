import GaloisForLFunctions.HTGeometry.SchwartzCompactContinuousDensity

/-!
Continuous functions on compact real intervals have smooth, compactly supported, globally Lipschitz uniform approximations.
-/

set_option autoImplicit false
noncomputable section
open Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- A continuous function on a compact real interval has uniformly close smooth, compactly
supported, globally Lipschitz approximants. -/
theorem exists_compact_lipschitz_uniform_approximation {g : ℝ → ℝ} {a b ε : ℝ}
    (hg : ContinuousOn g (Set.Icc a b)) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧
      LipschitzWith K f ∧ ∀ x ∈ Set.Icc a b, |f x - g x| < ε := by
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn a b g hg ε hε
  let R := max |a| |b|
  let f : SchwartzMap ℝ ℝ := SchwartzMap.realPolynomialCutoff P R
  have hR : 0 ≤ R := (abs_nonneg a).trans (le_max_left _ _)
  have hfd : ContDiff ℝ 2 f := f.smooth 2
  have hfc : HasCompactSupport f := by
    have hsub := SchwartzMap.realPolynomialCutoff_tsupport_subset P R
    change IsCompact (tsupport f)
    apply isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
    intro x hx
    exact abs_le.mp (hsub hx)
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfc hfd (by norm_num)
  refine ⟨f, K, hfd, hfc, hK, ?_⟩
  intro x hx
  have hxR : |x| ≤ R := abs_le.mpr ⟨by
      have hh : -|a| ≤ x := (neg_abs_le a).trans hx.1
      exact (neg_le_neg (le_max_left _ _)).trans hh,
    hx.2.trans ((le_abs_self b).trans (le_max_right _ _))⟩
  have hcore : |x| ≤ |R| + 1 := by rw [abs_of_nonneg hR]; linarith only [hxR]
  change |SchwartzMap.realPolynomialCutoff P R x - g x| < ε
  rw [SchwartzMap.realPolynomialCutoff_apply,
    SchwartzMap.realCompactIntervalCutoff_apply_of_abs_le_add_one R hcore, mul_one]
  exact hP x hx

#print axioms exists_compact_lipschitz_uniform_approximation
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
