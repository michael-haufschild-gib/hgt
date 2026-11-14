import GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies.KloostermanCentralLimit
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.PrimeResidueDistribution
import GaloisForLFunctions.HTGeometry.PrimeSieveDensityTelescope
import GaloisForLFunctions.RHTower.PrimeLogTripleCluster

/-!
# Gaussian limits for arithmetic Kloosterman sums over complete periods

One integer parameter, sampled over the product of the first `n` primes,
produces independent prime residues by the Chinese remainder theorem.
Consequently the sum of its variance-normalized Kloosterman traces, divided
by `√n`, converges in distribution to the standard Gaussian.
-/

open Finset MeasureTheory ProbabilityTheory Filter Complex
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticHarmonicAnalysis
open scoped ENNReal Topology

namespace GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
noncomputable section

/-- The standardized sum at one common integer parameter. -/
def arithmeticKloostermanSum (S : Finset Nat.Primes) (a : ℕ) : ℝ :=
  (Real.sqrt S.card)⁻¹ * ∑ p ∈ S, standardizedKloostermanTrace p (a : ZMod p.val)

/-- Empirical law of the normalized sum on one complete squarefree period. -/
def arithmeticKloostermanLaw (S : Finset Nat.Primes) : Measure ℝ :=
  (primeSetProduct S : ℝ≥0∞)⁻¹ •
    ∑ a : Fin (primeSetProduct S), Measure.dirac (arithmeticKloostermanSum S a)

instance (S : Finset Nat.Primes) : IsProbabilityMeasure (arithmeticKloostermanLaw S) := by
  constructor
  have hp : (primeSetProduct S : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (primeSetProduct_pos S).ne'
  simp [arithmeticKloostermanLaw, Measure.coe_finsetSum]
  exact ENNReal.inv_mul_cancel hp (by simp)

/-- CRT gives exact characteristic-function factorization for the common-parameter family. -/
theorem charFun_arithmeticKloostermanLaw (S : Finset Nat.Primes) (t : ℝ) :
    charFun (arithmeticKloostermanLaw S) t =
      ∏ p ∈ S, charFun (primeKloostermanLaw p) ((Real.sqrt S.card)⁻¹ * t) := by
  let u : ℝ := (Real.sqrt S.card)⁻¹ * t
  have hexp (a : ℕ) :
      cexp ((t : ℂ) * (arithmeticKloostermanSum S a : ℂ) * I) =
        ∏ p ∈ S, cexp ((u : ℂ) * (standardizedKloostermanTrace p (a : ZMod p.val) : ℂ) * I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [arithmeticKloostermanSum, Complex.ofReal_mul, Complex.ofReal_sum,
      Finset.mul_sum, Finset.sum_mul, u]
    apply sum_congr rfl
    intro p _
    push_cast
    ring
  have hlocal (p : Nat.Primes) : charFun (primeKloostermanLaw p) u =
      (∑ a : ZMod p.val, cexp ((u : ℂ) * (standardizedKloostermanTrace p a : ℂ) * I)) /
        (p.val : ℂ) := by
    rw [charFun_apply_real, integral_primeKloostermanLaw]
    simp [Algebra.smul_def, inv_mul_eq_div]
  rw [charFun_apply_real, arithmeticKloostermanLaw, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
  simp only [integral_dirac, hexp, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    Fin.sum_univ_eq_sum_range]
  rw [sum_primeResidue_product]
  simp only [hlocal, prod_div_distrib]
  have hP : (primeSetProduct S : ℂ) = ∏ p ∈ S, (p.val : ℂ) := by
    simp only [primeSetProduct, Nat.cast_prod]
  simp [Algebra.smul_def, inv_mul_eq_div, hP]

/-- Enumerating distinct primes turns the arithmetic law into the independent-law product. -/
theorem charFun_arithmeticKloostermanLaw_prefix (e : ℕ ≃ Nat.Primes) (n : ℕ) (t : ℝ) :
    charFun (arithmeticKloostermanLaw (HTGeometry.sievePrefix e n)) t =
      charFun ((kloostermanSequenceMeasure e).map
        (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ range n, ω i)) t := by
  rw [charFun_arithmeticKloostermanLaw, charFun_kloosterman_normalized_sum]
  simp only [HTGeometry.sievePrefix, card_image_of_injective _ e.injective, card_range]
  exact prod_image (fun _ _ _ _ h => e.injective h)

/-- Complete-period arithmetic sampling has exactly the independent sum's law. -/
theorem arithmeticKloostermanLaw_prefix_eq_map (e : ℕ ≃ Nat.Primes) (n : ℕ) :
    arithmeticKloostermanLaw (HTGeometry.sievePrefix e n) =
      (kloostermanSequenceMeasure e).map
        (fun ω => (Real.sqrt n)⁻¹ * ∑ i ∈ range n, ω i) := by
  apply Measure.ext_of_charFun
  exact funext (charFun_arithmeticKloostermanLaw_prefix e n)

/-- Complete-period arithmetic sampling has a Gaussian limit for every ordering of primes. -/
theorem tendstoInDistribution_arithmeticKloostermanLaw (e : ℕ ≃ Nat.Primes) :
    TendstoInDistribution (fun _ : ℕ => (id : ℝ → ℝ)) atTop (id : ℝ → ℝ)
      (fun n => arithmeticKloostermanLaw (HTGeometry.sievePrefix e n)) (gaussianReal 0 1) where
  forall_aemeasurable _ := aemeasurable_id
  tendsto := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    simpa [Measure.map_id, charFun_arithmeticKloostermanLaw_prefix,
      charFun_gaussianReal, neg_div] using tendsto_charFun_kloosterman_normalized_sum e t

/-- The sums over the first `n` primes obey a Gaussian law under complete-period averaging. -/
theorem tendstoInDistribution_arithmeticKloosterman_first_primes :
    TendstoInDistribution (fun _ : ℕ => (id : ℝ → ℝ)) atTop (id : ℝ → ℝ)
      (fun n => arithmeticKloostermanLaw (HTGeometry.sievePrefix RHTower.nthPrimeEquiv n))
      (gaussianReal 0 1) :=
  tendstoInDistribution_arithmeticKloostermanLaw RHTower.nthPrimeEquiv

#print axioms charFun_arithmeticKloostermanLaw
#print axioms arithmeticKloostermanLaw_prefix_eq_map
#print axioms tendstoInDistribution_arithmeticKloosterman_first_primes

end
end GaloisForLFunctions.ArithmeticKunnethTheory.WeightFamilies
