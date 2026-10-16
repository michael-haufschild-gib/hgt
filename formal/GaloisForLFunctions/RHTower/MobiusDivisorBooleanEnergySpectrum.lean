import GaloisForLFunctions.RHTower.MobiusDivisorInheritedPrimeInsertionProducer
import GaloisForLFunctions.RHTower.MobiusDivisorLateBlockBooleanTransport

/-!
# The complete Boolean energy spectrum

The density-normalized Euler multiplier is exactly `1 - cₚ cos(t log p)`.
Consequently every alternating energy coefficient is a signed cosine-product
integral of the original source. No sign assumption enters the identity.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower
open PrimePreparation

/-- The limiting coefficient of the literal finite source energy. -/
def mobiusDivisorCoreEnergyCoefficient (P : Finset ℕ) : ℝ :=
  ∑' n, mobiusDivisorFixedCoreBlockMass P n

namespace PrimePreparation

def coreDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity * ∏ p ∈ P, (p : ℝ) / (p + 1)

def primeCosineFactor (p : ℕ) : ℝ := 2 * Real.sqrt p / (p + 1)

lemma coreDensity_pos (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    0 < coreDensity P := by
  apply mul_pos
  · rw [Sieve.squarefreeDensity_eq]; positivity
  · exact prod_pos (fun p hp => div_pos (by exact_mod_cast (hP p hp).pos) (by positivity))

lemma primeCosineFactor_pos {p : ℕ} (hp : p.Prime) : 0 < primeCosineFactor p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold primeCosineFactor
  positivity

private lemma energy_diagonal (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    mobiusDivisorCoreEnergyCoefficient P = coreDensity P * mobiusDivisorDilationMean P 1 := by
  have h1 : 1 ∉ P := fun h => Nat.not_prime_one (hP 1 h)
  have hprim (n : ℕ) (t : ℝ) : mobiusDivisorPrimeCorrelationPrimitive P 1 n t =
      2 * mobiusDivisorHeadBlockPrimitive P n t := by
    simp [mobiusDivisorPrimeCorrelationPrimitive, mobiusDivisorHeadBlockPrimitive]
    ring
  have hm (n : ℕ) : mobiusDivisorPrimeCorrelationMass P 1 n =
      mobiusDivisorFixedCoreBlockMass P n := by
    simp only [mobiusDivisorPrimeCorrelationMass, mobiusDivisorFixedCoreBlockMass, hprim]
    split_ifs
    · rfl
    · rw [prod_insert h1]
      ring
  have h := hasSum_mobiusDivisorPrimeCorrelationMass_integral P hP (by omega : 0 < 1)
  rw [show mobiusDivisorPrimeCorrelationMass P 1 = mobiusDivisorFixedCoreBlockMass P
    from funext hm] at h
  rw [integral_mobiusDivisorPrimeCorrelationKernel_eq_dilationMean P (by omega : 0 < 1),
    prod_insert h1] at h
  have he := h.tsum_eq
  convert he using 1 <;> norm_num [mobiusDivisorCoreEnergyCoefficient, coreDensity]
  ring

lemma coreEnergy_spectrum (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, p.Prime) :
    mobiusDivisorCoreEnergyCoefficient P =
      (1 / (2 * Real.pi)) * ∫ t, coreDensity P * clusterWeight P t := by
  rw [energy_diagonal P hprime, cluster_dilation_spectrum P hP hprime (by norm_num)]
  simp only [Real.log_one, zero_mul, Real.cos_zero, mul_one, integral_const_mul]
  ring

private lemma normalized_prime_wave {p : ℕ} (hp : p.Prime) (t : ℝ) :
    (p : ℝ) / (p + 1) * ‖1 - primeWave p t‖ ^ 2 =
      1 - primeCosineFactor p * Real.cos (Real.log p * t) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpR
  have hsq := Real.sq_sqrt hpR.le
  have hre : (primeWave p t).re =
      (Real.sqrt p)⁻¹ * Real.cos (Real.log p * t) := by
    simp only [primeWave, Complex.mul_re, Complex.mul_im, Complex.exp_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, mul_one, zero_add, Real.exp_zero,
      one_mul, Real.cos_neg, mul_comm]
  have hn := Complex.normSq_sub (1 : ℂ) (primeWave p t)
  simp only [Complex.normSq_eq_norm_sq, norm_one, one_pow, one_mul, Complex.conj_re,
    primeWave_norm, inv_pow, hsq, hre] at hn
  rw [hn]
  unfold primeCosineFactor
  field_simp
  linear_combination 2 * Real.cos (Real.log p * t) * hsq

private lemma normalized_union (P U : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hU : ∀ p ∈ U, p.Prime)
    (hPU : Disjoint P U) (t : ℝ) :
    coreDensity (P ∪ U) * clusterWeight (P ∪ U) t =
      coreDensity P * clusterWeight P t *
        ∏ p ∈ U, (1 - primeCosineFactor p * Real.cos (Real.log p * t)) := by
  have he : (∏ p ∈ U, (p : ℝ) / (p + 1)) *
      ‖divisorCoreMellinEuler U (1 + (t : ℂ) * Complex.I)‖ ^ 2 =
      ∏ p ∈ U, (1 - primeCosineFactor p * Real.cos (Real.log p * t)) := by
    rw [cluster_euler_product U hU, norm_prod, ← Finset.prod_pow, ← prod_mul_distrib]
    exact prod_congr rfl (fun p hp => normalized_prime_wave (hU p hp) t)
  rw [clusterWeight_union P U hP hU hPU]
  have hd : coreDensity (P ∪ U) = coreDensity P * ∏ p ∈ U, (p : ℝ) / (p + 1) := by
    simp only [coreDensity, prod_union hPU]
    ring
  rw [hd, ← he]
  ring

private lemma normalized_boolean (P A : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hA : ∀ p ∈ A, p.Prime)
    (hPA : Disjoint P A) (t : ℝ) :
    mobiusDivisorBooleanAlternating P A (fun Q => coreDensity Q * clusterWeight Q t) =
      coreDensity P * clusterWeight P t *
        ∏ p ∈ A, (primeCosineFactor p * Real.cos (Real.log p * t)) := by
  have hprod := Finset.prod_sub (fun _ : ℕ => (1 : ℝ))
    (fun p => 1 - primeCosineFactor p * Real.cos (Real.log p * t)) A
  simp only [sub_sub_cancel, prod_const_one, mul_one] at hprod
  rw [hprod, mul_sum]
  unfold mobiusDivisorBooleanAlternating
  apply sum_congr rfl
  intro U hU
  have hUA := mem_powerset.mp hU
  dsimp only
  rw [normalized_union P U hP (fun p hp => hA p (hUA hp)) (hPA.mono_right hUA)]
  ring

lemma cosineProduct_integrable (P A : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀ p ∈ P, p.Prime) :
    Integrable (fun t => clusterWeight P t * ∏ p ∈ A, Real.cos (Real.log p * t)) := by
  have hc : Continuous (fun t : ℝ => ∏ p ∈ A, Real.cos (Real.log p * t)) := by fun_prop
  apply (clusterWeight_integrable P hP hprime).mul_bdd hc.aestronglyMeasurable (c := 1)
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_prod]
  calc
    _ ≤ ∏ _p ∈ A, (1 : ℝ) := prod_le_prod (fun p _ => abs_nonneg _)
      (fun p _ => Real.abs_cos_le_one _)
    _ = 1 := prod_const_one

end PrimePreparation

/-- Every Boolean grade is the exact cosine-product spectrum of the literal
energy, with its strictly positive arithmetic normalization. -/
theorem mobiusDivisorCoreEnergyCoefficient_boolean_spectrum
    (P A : Finset ℕ) (hP : P.Nonempty) (hprime : ∀ p ∈ P, p.Prime)
    (hA : ∀ p ∈ A, p.Prime) (hPA : Disjoint P A) :
    mobiusDivisorBooleanAlternating P A mobiusDivisorCoreEnergyCoefficient =
      (coreDensity P / (2 * Real.pi) * ∏ p ∈ A, primeCosineFactor p) *
        ∫ t, clusterWeight P t * ∏ p ∈ A, Real.cos (Real.log p * t) := by
  classical
  have hpr (U : Finset ℕ) (hU : U ∈ A.powerset) : ∀ p ∈ P ∪ U, p.Prime := by
    intro p hp
    exact (mem_union.mp hp).elim (hprime p) (fun hp => hA p (mem_powerset.mp hU hp))
  have hi (U : Finset ℕ) (hU : U ∈ A.powerset) :
      Integrable (fun t => (-1 : ℝ) ^ U.card *
        (coreDensity (P ∪ U) * clusterWeight (P ∪ U) t)) :=
    ((clusterWeight_integrable _ (hP.mono subset_union_left) (hpr U hU)).const_mul _).const_mul _
  have he : mobiusDivisorBooleanAlternating P A mobiusDivisorCoreEnergyCoefficient =
      (1 / (2 * Real.pi)) * ∫ t,
        mobiusDivisorBooleanAlternating P A (fun Q => coreDensity Q * clusterWeight Q t) := by
    unfold mobiusDivisorBooleanAlternating
    rw [integral_finsetSum _ hi, mul_sum]
    apply sum_congr rfl
    intro U hU
    rw [coreEnergy_spectrum _ (hP.mono subset_union_left) (hpr U hU)]
    simp only [integral_const_mul]
    ring
  rw [he]
  simp_rw [PrimePreparation.normalized_boolean P A hprime hA hPA, prod_mul_distrib]
  have heq (t : ℝ) : coreDensity P * clusterWeight P t *
      ((∏ p ∈ A, primeCosineFactor p) * ∏ p ∈ A, Real.cos (Real.log p * t)) =
      (coreDensity P * ∏ p ∈ A, primeCosineFactor p) *
        (clusterWeight P t * ∏ p ∈ A, Real.cos (Real.log p * t)) := by ring
  simp_rw [heq]
  rw [integral_const_mul]
  ring

/-- Finite Boolean differences commute with the fixed-core energy limit. -/
theorem tendsto_mobiusDivisorBooleanEnergy_div_sq
    (P A : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hA : ∀ p ∈ A, p.Prime) :
    Tendsto (fun M : ℕ => mobiusDivisorBooleanAlternating P A
      (mobiusDivisorSelectionEnergy M) / (M : ℝ) ^ 2) atTop
      (𝓝 (mobiusDivisorBooleanAlternating P A mobiusDivisorCoreEnergyCoefficient)) := by
  unfold mobiusDivisorBooleanAlternating
  simp_rw [sum_div, mul_div_assoc]
  apply tendsto_finsetSum
  intro U hU
  apply Tendsto.const_mul
  exact tendsto_mobiusDivisorSelectionEnergy_div_sq (P ∪ U) (by
    intro p hp
    exact (mem_union.mp hp).elim (hP p) (fun hp => hA p (mem_powerset.mp hU hp)))

end RHTower
