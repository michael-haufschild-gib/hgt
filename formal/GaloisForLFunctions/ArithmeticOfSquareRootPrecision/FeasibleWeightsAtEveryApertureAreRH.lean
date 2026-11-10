import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.FiniteAperturePositivityCannotDecide
import GaloisForLFunctions.RHTower.TwistedArcMinimumPrincipleProof

/-!
# Feasible weights at every aperture

RH holds exactly when every positive aperture admits a real weight with
nonnegative Weil form. The weights may vary with the aperture: each finite
prime-blind test mixture fits inside one aperture, where the weights cancel.
-/

noncomputable section
open Set
open _root_.RHTower _root_.RHTower.WeilOneSided

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- Finitely many compact Weil tests fit inside a common positive aperture. -/
theorem finite_weilTests_common_aperture (s : Finset WeilTestFn) :
    ∃ A : ℝ, 0 < A ∧ ∀ f ∈ s, tsupport f.1 ⊆ Icc (-A) A := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert f s _ ih =>
    obtain ⟨A, hA, hs⟩ := ih
    obtain ⟨B, hB⟩ := f.2.2.isCompact.isBounded.subset_closedBall 0
    refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
    intro g hg u hu
    rcases Finset.mem_insert.mp hg with rfl | hg
    · have h := hB hu
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
      exact ⟨(neg_le_neg (le_max_right A B)).trans (abs_le.mp h).1,
        (abs_le.mp h).2.trans (le_max_right A B)⟩
    · exact ⟨(neg_le_neg (le_max_left A B)).trans (hs g hg hu).1,
        (hs g hg hu).2.trans (le_max_left A B)⟩

/-- Local feasibility makes every prime-blind mixture nonnegative. -/
theorem primeBlindPositive_of_feasible_at_every_aperture
    (h : ∀ A : ℝ, 0 < A → ∃ lam : ℕ → ℝ, AperturePositive A lam) :
    PrimeBlindPositive := by
  intro c hc hnull
  obtain ⟨A, hA, hs⟩ := finite_weilTests_common_aperture c.support
  obtain ⟨lam, hlam⟩ := h A hA
  have hsum : 0 ≤ c.sum fun f t =>
      t * (weilFullFunctional lam (Zeta23.EF.weilTest f.1 f.1)).re :=
    Finsupp.sum_nonneg fun f hf => mul_nonneg (hc f) (hlam f.1 f.2.1 (hs f hf))
  rw [sum_re_weilFullFunctional, linearCombination_logVector_eq_zero hnull,
    map_zero, sub_zero] at hsum
  rw [sum_weilArchRe_eq]
  exact hsum

/-- Each aperture may choose its own feasible weight; existence at all apertures is RH. -/
theorem riemannHypothesis_iff_feasible_at_every_aperture :
    RiemannHypothesis ↔
      ∀ A : ℝ, 0 < A → ∃ lam : ℕ → ℝ, AperturePositive A lam := by
  constructor
  · intro hRH A _
    exact ⟨_, aperturePositive_of_weilPositiveFull
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) A⟩
  · intro h
    exact riemannHypothesis_iff_primeBlindPositive_unconditional.mpr
      (primeBlindPositive_of_feasible_at_every_aperture h)

/-- If RH fails, one finite aperture excludes every real weight system. -/
theorem not_riemannHypothesis_iff_empty_aperture :
    ¬ RiemannHypothesis ↔
      ∃ A : ℝ, 0 < A ∧ ∀ lam : ℕ → ℝ, ¬ AperturePositive A lam := by
  rw [riemannHypothesis_iff_feasible_at_every_aperture]
  push_neg
  rfl

#print axioms riemannHypothesis_iff_feasible_at_every_aperture
#print axioms not_riemannHypothesis_iff_empty_aperture

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
