import GaloisForLFunctions.HilbertMetric.QuantumInformation.ToeplitzPartialTranspose
import GaloisForLFunctions.RHTower.XiCosineShiftSechHandoff
import Mathlib.Analysis.Complex.Circle

/-!
# Positive phase moments for the Cauchy charge state

The positive moment representation in Qian and Zhang (arXiv:2611.24473,
Theorem 4(b)) is explicit for the Cauchy kernel. A single random phase with
the hyperbolic secant law drives all sites. Its pushforward to the phase
torus represents every multidegree moment, and in particular the whole
qubit density matrix as an average of equatorial product states.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace GaloisForLFunctions.HilbertMetric.CauchyPhase

noncomputable section

private def density (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (RHTower.sechPort (1 / 2) t)

private def noise : Measure ℝ := volume.withDensity density

private theorem half_pos : 0 < (1 / 2 : ℝ) := by positivity

private instance : IsProbabilityMeasure noise := by
  rw [isProbabilityMeasure_iff, noise, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold density
  rw [← ofReal_integral_eq_lintegral_ofReal (RHTower.integrable_sechPort half_pos)
    (Eventually.of_forall fun t => (RHTower.sechPort_pos half_pos t).le),
    RHTower.integral_sechPort half_pos, ENNReal.ofReal_one]

private theorem integral_noise_character (d : ℝ) :
    (∫ t : ℝ, Complex.exp (-(Complex.I * (t : ℂ) * (d : ℂ))) ∂noise) =
      ((Real.cosh (d / 2))⁻¹ : ℝ) := by
  have hm : Measurable density :=
    (ENNReal.continuous_ofReal.comp (RHTower.continuous_sechPort (1 / 2))).measurable
  rw [noise, integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [density, ENNReal.toReal_ofReal (RHTower.sechPort_pos half_pos _).le, Complex.real_smul]
  rw [RHTower.integral_sechPort_mul_cexp half_pos, show (1 / 2 : ℝ) * d = d / 2 by ring,
    one_div]

variable {σ : Type*} [Fintype σ]

/-- A common phase at all sites, with the indicated real charges. -/
def phaseCurve (w : σ → ℝ) (t : ℝ) : σ → Circle :=
  fun i => Circle.exp (-(t * w i))

private theorem continuous_phaseCurve (w : σ → ℝ) : Continuous (phaseCurve w) := by
  apply continuous_pi
  intro i
  exact Circle.exp.continuous.comp (by fun_prop : Continuous fun t : ℝ => -(t * w i))

/-- Positive representing measure on the entire site phase torus. -/
def phaseLaw (w : σ → ℝ) : ProbabilityMeasure (σ → Circle) :=
  (⟨noise, inferInstance⟩ : ProbabilityMeasure ℝ).map (continuous_phaseCurve w).aemeasurable

/-- The torus character at any integer multidegree. -/
def character (n : σ → ℤ) (z : σ → Circle) : ℂ := ∏ i, (z i : ℂ) ^ n i

private theorem continuous_character (n : σ → ℤ) : Continuous (character n) := by
  unfold character
  apply continuous_finset_prod
  intro i _
  have h : Continuous (fun z : σ → Circle => (z i) ^ n i) := (continuous_apply i).zpow _
  simpa only [Circle.coe_zpow] using continuous_subtype_val.comp h

private theorem character_phaseCurve (w : σ → ℝ) (n : σ → ℤ) (t : ℝ) :
    character n (phaseCurve w t) =
      Complex.exp (-(Complex.I * (t : ℂ) * ((∑ i, (n i : ℝ) * w i : ℝ) : ℂ))) := by
  simp only [character, phaseCurve, Circle.coe_exp, ← Complex.exp_int_mul, ← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- All integer moments are sech of half of the charge pairing. -/
theorem integral_character_phaseLaw (w : σ → ℝ) (n : σ → ℤ) :
    (∫ z, character n z ∂(phaseLaw w : Measure (σ → Circle))) =
      ((Real.cosh ((∑ i, (n i : ℝ) * w i) / 2))⁻¹ : ℝ) := by
  rw [phaseLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (continuous_phaseCurve w).aemeasurable (continuous_character n).aestronglyMeasurable]
  simp_rw [character_phaseCurve]
  exact integral_noise_character _

private def bitDifference (x y : σ → Bool) (i : σ) : ℤ :=
  (if x i then 1 else 0) - (if y i then 1 else 0)

private theorem charge_difference (w : σ → ℝ) (x y : σ → Bool) :
    ∑ i, (bitDifference x y i : ℝ) * w i = bitCharge w x - bitCharge w y := by
  rw [bitCharge, bitCharge, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hx : x i <;> cases hy : y i <;> simp [bitDifference, hx, hy]

/-- An equatorial product-state matrix, obtained by multiplying the local
one-qubit phase entries and dividing by the dimension. -/
def equatorialProduct (z : σ → Circle) (x y : σ → Bool) : ℂ :=
  (Fintype.card (σ → Bool) : ℂ)⁻¹ * character (bitDifference x y) z

/-- Normalized local vector with the specified equatorial phase. -/
def equatorialAmplitude (z : Circle) (b : Bool) : ℂ :=
  (if b then (z : ℂ) else 1) / (Real.sqrt 2 : ℂ)

/-- The mixture atoms are literal products of local pure-state entries. -/
theorem equatorialProduct_eq_local (z : σ → Circle) (x y : σ → Bool) :
    equatorialProduct z x y =
      ∏ i, equatorialAmplitude (z i) (x i) * star (equatorialAmplitude (z i) (y i)) := by
  have hcard : (Fintype.card (σ → Bool) : ℂ)⁻¹ = ∏ _ : σ, (1 / 2 : ℂ) := by
    simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
      Finset.prod_const, Finset.card_univ, one_div, inv_pow]
  unfold equatorialProduct character
  rw [hcard, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity : 0 ≤ (2 : ℝ))]
    norm_cast
  have hi : (z i : ℂ)⁻¹ = (starRingEnd ℂ) (z i : ℂ) :=
    Complex.inv_eq_conj (Circle.norm_coe _)
  have hu : (z i : ℂ) * (starRingEnd ℂ) (z i : ℂ) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, Circle.norm_coe]
    norm_num
  rw [equatorialAmplitude, equatorialAmplitude, Complex.star_def, map_div₀,
    Complex.conj_ofReal, div_mul_div_comm, hs]
  cases hx : x i <;> cases hy : y i <;>
    simp [bitDifference, hx, hy, hi, hu, div_eq_mul_inv, mul_comm]

/-- The Cauchy charge state is exactly the average of these product-state
entries. The representing measure is a probability for any real charges. -/
theorem cauchyChargeState_apply_integral (w : σ → ℝ) (x y : σ → Bool) :
    cauchyChargeState w x y =
      ∫ z, equatorialProduct z x y ∂(phaseLaw w : Measure (σ → Circle)) := by
  unfold equatorialProduct
  rw [integral_const_mul, integral_character_phaseLaw, charge_difference]
  simp only [cauchyChargeState, chargeDifferenceMatrix, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast]

#print axioms integral_character_phaseLaw
#print axioms equatorialProduct_eq_local
#print axioms cauchyChargeState_apply_integral

end

end GaloisForLFunctions.HilbertMetric.CauchyPhase
