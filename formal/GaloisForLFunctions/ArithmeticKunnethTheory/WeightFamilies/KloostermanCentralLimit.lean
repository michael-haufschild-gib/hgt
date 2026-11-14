import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanCharacteristicFunction
import Mathlib.Probability.Independence.InfinitePi

/-!
# A central limit theorem for arbitrary prime sequences

The independent empirical Kloosterman laws have exactly unit variance and a
uniform cubic Taylor bound. Their normalized characteristic-function product
differs from the identically distributed reference product by `O(n⁻¹ᐟ²)`.
The usual central limit theorem for that reference law and Lévy convergence
give a Gaussian limit without any growth or distinctness requirement on primes.
-/

open Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

/-- Independent standardized empirical traces at an arbitrary sequence of primes. -/
def kloostermanSequenceMeasure (p : ℕ → Nat.Primes) : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun i => primeKloostermanLaw (p i)

instance (p : ℕ → Nat.Primes) : IsProbabilityMeasure (kloostermanSequenceMeasure p) := by
  unfold kloostermanSequenceMeasure
  infer_instance

theorem hasLaw_kloosterman_eval (p : ℕ → Nat.Primes) (i : ℕ) :
    HasLaw (Function.eval i) (primeKloostermanLaw (p i)) (kloostermanSequenceMeasure p) :=
  (measurePreserving_eval_infinitePi (fun j => primeKloostermanLaw (p j)) i).hasLaw

theorem iIndepFun_kloosterman_eval (p : ℕ → Nat.Primes) :
    iIndepFun (fun (i : ℕ) (ω : ℕ → ℝ) => ω i) (kloostermanSequenceMeasure p) :=
  iIndepFun_infinitePi (fun _ : ℕ => measurable_id)

/-- Exact factorization of the characteristic function of a normalized sum. -/
theorem charFun_kloosterman_normalized_sum (p : ℕ → Nat.Primes) (n : ℕ) (t : ℝ) :
    charFun ((kloostermanSequenceMeasure p).map
      (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ range n, ω i)) t =
      ∏ i ∈ range n, charFun (primeKloostermanLaw (p i)) ((Real.sqrt n)⁻¹ * t) := by
  rw [charFun_map_mul_comp,
    ((iIndepFun_kloosterman_eval p).restrict _).charFun_map_fun_finsetSum_eq_prod
      (fun i _ => (hasLaw_kloosterman_eval p i).aemeasurable)]
  · simp only [prod_apply, (hasLaw_kloosterman_eval p _).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun i _ => (hasLaw_kloosterman_eval p i).aemeasurable

/-- The replacement error decays at the square-root rate, uniformly in every prime. -/
theorem norm_prod_charFun_kloosterman_normalized_sub_pow
    (p : ℕ → Nat.Primes) (q : Nat.Primes) (n : ℕ) (t : ℝ) :
    ‖(∏ i ∈ range n, charFun (primeKloostermanLaw (p i)) ((Real.sqrt n)⁻¹ * t)) -
      charFun (primeKloostermanLaw q) ((Real.sqrt n)⁻¹ * t) ^ n‖ ≤
      (2 * |t| ^ 3 / 3) * (Real.sqrt n)⁻¹ := by
  have h := norm_prod_charFun_primeKloostermanLaw_sub_pow p q n ((Real.sqrt n)⁻¹ * t)
  refine h.trans_eq ?_
  by_cases hn : n = 0
  · simp [hn]
  have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  rw [abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  calc
    (n : ℝ) * (2 * ((Real.sqrt n)⁻¹ ^ 3 * |t| ^ 3) / 3) =
        Real.sqrt (n : ℝ) ^ 2 * (2 * ((Real.sqrt n)⁻¹ ^ 3 * |t| ^ 3) / 3) := by
      rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    _ = _ := by field_simp [hs]

/-- Pointwise Gaussian convergence holds for the characteristic functions of every prime sequence. -/
theorem tendsto_charFun_kloosterman_normalized_sum (p : ℕ → Nat.Primes) (t : ℝ) :
    Tendsto (fun n : ℕ => charFun ((kloostermanSequenceMeasure p).map
      (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ range n, ω i)) t)
      atTop (𝓝 (Complex.exp (-(t : ℂ) ^ 2 / 2))) := by
  have href := tendsto_charFun_inv_sqrt_mul_pow
    (P := primeKloostermanLaw (p 0)) (X := id) aemeasurable_id
    (integral_primeKloostermanLaw_id (p 0)) (integral_primeKloostermanLaw_sq (p 0)) t
  simp only [Measure.map_id] at href
  have hrate : Tendsto (fun n : ℕ => (2 * |t| ^ 3 / 3) * (Real.sqrt n)⁻¹)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp
        tendsto_natCast_atTop_atTop)).const_mul (2 * |t| ^ 3 / 3)
  have hdiff := squeeze_zero_norm'
    (Filter.Eventually.of_forall (fun n =>
      norm_prod_charFun_kloosterman_normalized_sub_pow p (p 0) n t)) hrate
  have h := hdiff.add href
  simpa only [sub_add_cancel, zero_add, charFun_kloosterman_normalized_sum] using h

/-- Independent standardized Kloosterman traces satisfy a central limit theorem for
every sequence of primes, including bounded and repeated sequences. -/
theorem tendstoInDistribution_kloosterman (p : ℕ → Nat.Primes) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → ℝ) => (Real.sqrt n)⁻¹ * ∑ i ∈ range n, ω i)
      atTop (id : ℝ → ℝ) (fun _ => kloostermanSequenceMeasure p) (gaussianReal 0 1) where
  forall_aemeasurable n :=
    .const_mul (Finset.aemeasurable_fun_sum _ fun i _ =>
      (hasLaw_kloosterman_eval p i).aemeasurable) _
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    simpa [Measure.map_id, charFun_gaussianReal, neg_div] using
      tendsto_charFun_kloosterman_normalized_sum p t

#print axioms norm_prod_charFun_kloosterman_normalized_sub_pow
#print axioms tendsto_charFun_kloosterman_normalized_sum
#print axioms tendstoInDistribution_kloosterman

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
