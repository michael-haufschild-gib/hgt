import GaloisForLFunctions.RHTower.XiGaussianAnnihilatorEnergy

/-!
# Fixed-time domination with arbitrary retained divisor copies

Deleting a set of factors from the finite annihilator leaves the same
head/tail argument available. A fixed polynomial multiplier and every
coefficient cross term remain inside the dominating heat summand.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower

/-- Retain exactly the factors in a prescribed set of divisor copies. -/
def xiGaussianSelectedAnnihilator (S : Set XiZeroCopy) (F : Finset XiZeroCopy) :
    Polynomial ℝ := by
  classical
  exact xiGaussianAnnihilator (F.filter (· ∈ S))

/-- At any fixed positive time, one summable head dominates all later
selected products, including an arbitrary fixed polynomial multiplier. -/
theorem exists_xiGaussianSelectedAnnihilator_dominating_head
    (S : Set XiZeroCopy) (Q : Polynomial ℝ) (t : {t : ℝ // 0 < t}) :
    ∃ H : Finset XiZeroCopy, ∀ᶠ F : Finset XiZeroCopy in atTop,
      ∀ q : XiZeroCopy,
        ‖xiPolynomialGaussianHeatTerm (Q * xiGaussianSelectedAnnihilator S F) t q‖ ≤
          ‖xiPolynomialGaussianHeatTerm (Q * xiGaussianSelectedAnnihilator S H)
            ((t : ℝ) / 2) q‖ := by
  classical
  obtain ⟨H, hH⟩ := xiSpectralPoint_inv_sq_summable.vanishing
    (Iio_mem_nhds (div_pos t.property (show (0 : ℝ) < 16 by positivity)))
  refine ⟨H, ?_⟩
  filter_upwards [eventually_ge_atTop H] with F hF q
  let A := H.filter (· ∈ S)
  let B := (F.filter (· ∈ S)) \ A
  have hdis : Disjoint B H := by
    rw [Finset.disjoint_left]
    intro p hp hpH
    have hpS := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hpH, hpS⟩)
  have htail : (∑ p ∈ B, 1 / ‖xiSpectralPoint p‖ ^ 2) < (t : ℝ) / 16 := hH B hdis
  have hsub : A ⊆ F.filter (· ∈ S) := Finset.filter_subset_filter _ hF
  have hprod : xiGaussianSelectedAnnihilator S F =
      xiGaussianSelectedAnnihilator S H * xiGaussianAnnihilator B := by
    simpa only [xiGaussianSelectedAnnihilator, A, B, Finset.union_eq_left.mpr hsub] using
      xiGaussianAnnihilator_union (F.filter (· ∈ S)) A
  let w := xiSpectralPoint q ^ 2
  have hw : 0 < w.re := xiSpectralSq_re_pos q
  have hsector : ‖w‖ < 2 * w.re := by
    simpa only [w, norm_pow, Complex.sq_norm] using
      xiSpectralPoint_normSq_lt_two_mul_sq_re q
  have hnorm : ‖evalRealPolynomial (xiGaussianAnnihilator B) w‖ ≤
      Real.exp (2 * ‖w‖ * ((t : ℝ) / 16)) :=
    (norm_eval_xiGaussianAnnihilator_le B w).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htail.le (by positivity)))
  have hsq : ‖evalRealPolynomial (xiGaussianAnnihilator B) w‖ ^ 2 ≤
      Real.exp (((t : ℝ) / 2) * w.re) := by
    calc
      _ ≤ (Real.exp (2 * ‖w‖ * ((t : ℝ) / 16))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = Real.exp (4 * ‖w‖ * ((t : ℝ) / 16)) := by
        rw [pow_two, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hsector.le t.property.le]
  rw [hprod, ← mul_assoc, norm_xiPolynomialGaussianHeatTerm,
    norm_xiPolynomialGaussianHeatTerm, evalRealPolynomial_mul, norm_mul, mul_pow]
  change (‖evalRealPolynomial (Q * xiGaussianSelectedAnnihilator S H) w‖ ^ 2 *
      ‖evalRealPolynomial (xiGaussianAnnihilator B) w‖ ^ 2) *
      Real.exp (-((t : ℝ) * w.re)) ≤
    ‖evalRealPolynomial (Q * xiGaussianSelectedAnnihilator S H) w‖ ^ 2 *
      Real.exp (-(((t : ℝ) / 2) * w.re))
  calc
    _ ≤ (‖evalRealPolynomial (Q * xiGaussianSelectedAnnihilator S H) w‖ ^ 2 *
        Real.exp (((t : ℝ) / 2) * w.re)) * Real.exp (-((t : ℝ) * w.re)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

end RHTower
