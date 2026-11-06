import GaloisForLFunctions.RHTower.Representation.EndpointExteriorSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import GaloisForLFunctions.RHTower.ScalarPowerSeriesUniqueness

/-!
# The exact endpoint exterior product

Pairing opposite arguments of the centered Hadamard product cancels the genus-one
exponentials. Dividing the squared lift at two square coordinates gives an ordinary
product of the normalized endpoint factors. Absolute summability expands that product
as a sum over all finite subsets, retaining the complex endpoint weights.
-/

noncomputable section
open Complex Filter Topology
open scoped BigOperators ComplexOrder
namespace RHTower

/-- Opposite centered arguments give the genus-zero product for the squared lift. -/
theorem hasProd_xiCentreLift_sq (y : ℂ) :
    HasProd (fun q : XiZeroCopy => 1 + y / xiSpectralPoint q ^ 2)
      ((xiCentreLift y / xiCentreLift 0) ^ 2) := by
  let z := Complex.sqrt (-y)
  have hz : z ^ 2 = -y := Complex.cpow_nat_inv_pow _ (by norm_num)
  have hp := xiCanonicalProduct_hasProdLocallyUniformlyOn.hasProd (Set.mem_univ z)
  have hm := xiCanonicalProduct_hasProdLocallyUniformlyOn.hasProd (Set.mem_univ (-z))
  have h := hp.mul hm
  have he (q : XiZeroCopy) :
      weierstrassE1 (z / xiSpectralPoint q) *
          weierstrassE1 (-z / xiSpectralPoint q) = 1 + y / xiSpectralPoint q ^ 2 := by
    calc
      _ = (1 - z / xiSpectralPoint q) * (1 + z / xiSpectralPoint q) *
          (Complex.exp (z / xiSpectralPoint q) * Complex.exp (-(z / xiSpectralPoint q))) := by
        simp only [weierstrassE1, neg_div]
        ring
      _ = 1 - z ^ 2 / xiSpectralPoint q ^ 2 := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]
        ring
      _ = _ := by rw [hz]; ring
  have hfun := funext he
  rw [hfun] at h
  have hval (w : ℂ) : xiCanonicalProduct w = XiC w / XiC 0 := by
    apply (eq_div_iff XiC_zero_ne).mpr
    simpa only [Pi.mul_apply, mul_comm] using
      (congrFun XiC_eq_constant_mul_canonicalProduct w).symm
  have hG : xiCentreLift y = XiC z := by
    have hh := xiCentreLift_neg_sq z
    simpa only [hz, neg_neg] using hh
  have hG0 : xiCentreLift 0 = XiC 0 := by
    simpa only [zero_pow (by omega : (2 : ℕ) ≠ 0), neg_zero] using xiCentreLift_neg_sq 0
  simpa only [hval, XiC_even, hG, hG0, pow_two] using h

private lemma endpoint_factor_ratio (a t m z : ℂ) (ht : t ≠ 0) (hm : m ≠ 0)
    (ha : a + t ^ 2 ≠ 0) :
    (1 + (a + z / m) / t ^ 2) / (1 + a / t ^ 2) =
      1 + z * (a + t ^ 2)⁻¹ / m := by
  have hd : 1 + a / t ^ 2 ≠ 0 := by
    rw [one_add_div (pow_ne_zero 2 ht)]
    exact div_ne_zero (by simpa only [add_comm] using ha) (pow_ne_zero 2 ht)
  apply (div_eq_iff hd).mpr
  field_simp [ht, hm, ha]
  ring

/-- Every normalized endpoint factor occurs with its actual divisor multiplicity. -/
theorem hasProd_xiEndpointExteriorSeries (z : ℂ) :
    HasProd (fun q : XiZeroCopy => 1 + z * xiStripEdgeWeight q / xiEndpointColorMass)
      (xiEndpointExteriorSeries z) := by
  have hM : (xiEndpointColorMass : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr xiEndpointColorMass_pos.ne'
  have hG : xiCentreLift (1 / 4) ≠ 0 := by rw [xiCentreLift_quarter]; norm_num
  have hG0 := xiCentreLift_zero_ne_zero
  have hn : (xiCentreLift (1 / 4) / xiCentreLift 0) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (div_ne_zero hG hG0)
  have hnum := hasProd_xiCentreLift_sq (1 / 4 + z / xiEndpointColorMass)
  have hden := hasProd_xiCentreLift_sq (1 / 4)
  have ht := (show Tendsto
    (fun S : Finset XiZeroCopy => ∏ q ∈ S,
      (1 + (1 / 4 + z / xiEndpointColorMass) / xiSpectralPoint q ^ 2)) atTop
      (𝓝 ((xiCentreLift (1 / 4 + z / xiEndpointColorMass) / xiCentreLift 0) ^ 2)) from hnum).div
    (show Tendsto (fun S : Finset XiZeroCopy => ∏ q ∈ S,
      (1 + (1 / 4 : ℂ) / xiSpectralPoint q ^ 2)) atTop
      (𝓝 ((xiCentreLift (1 / 4) / xiCentreLift 0) ^ 2)) from hden) hn
  have he (q : XiZeroCopy) :
      (1 + (1 / 4 + z / xiEndpointColorMass) / xiSpectralPoint q ^ 2) /
          (1 + (1 / 4 : ℂ) / xiSpectralPoint q ^ 2) =
        1 + z * xiStripEdgeWeight q / xiEndpointColorMass := by
    have ha : (1 / 4 : ℂ) + xiSpectralPoint q ^ 2 ≠ 0 := by
      intro hh
      have hhpos := xiStripEdgeWeight_re_pos q
      rw [xiStripEdgeWeight_eq_spectral, hh, inv_zero, Complex.zero_re] at hhpos
      exact lt_irrefl _ hhpos
    rw [xiStripEdgeWeight_eq_spectral]
    exact endpoint_factor_ratio _ _ _ _ (xiSpectralPoint_ne_zero q) hM ha
  have hval :
      ((xiCentreLift (1 / 4 + z / xiEndpointColorMass) / xiCentreLift 0) ^ 2) /
          ((xiCentreLift (1 / 4) / xiCentreLift 0) ^ 2) = xiEndpointExteriorSeries z := by
    unfold xiEndpointExteriorSeries
    field_simp [hG0, hG]
  change Tendsto (fun S : Finset XiZeroCopy =>
    (∏ q ∈ S, (1 + (1 / 4 + z / xiEndpointColorMass) / xiSpectralPoint q ^ 2)) /
    (∏ q ∈ S, (1 + (1 / 4 : ℂ) / xiSpectralPoint q ^ 2))) atTop _ at ht
  change Tendsto (fun S : Finset XiZeroCopy =>
    ∏ q ∈ S, (1 + z * xiStripEdgeWeight q / xiEndpointColorMass)) atTop
    (𝓝 (xiEndpointExteriorSeries z))
  simpa only [← Finset.prod_div_distrib, he, hval] using ht

/-- Absolute convergence of all subset products follows from summability of endpoint norms. -/
theorem summable_xiEndpointExteriorSubset (z : ℂ) :
    Summable (fun S : Finset XiZeroCopy =>
      ∏ q ∈ S, z * xiStripEdgeWeight q / xiEndpointColorMass) := by
  apply summable_finsetProd_of_summable_norm
  simp only [norm_div, norm_mul]
  exact (summable_xiStripEdgeWeight.norm.mul_left ‖z‖).div_const ‖(xiEndpointColorMass : ℂ)‖

/-- The arithmetic exterior series is the absolutely convergent sum of all endpoint subset masses. -/
theorem hasSum_xiEndpointExteriorSubset (z : ℂ) :
    HasSum (fun S : Finset XiZeroCopy =>
      ∏ q ∈ S, z * xiStripEdgeWeight q / xiEndpointColorMass) (xiEndpointExteriorSeries z) := by
  have hs := (summable_xiEndpointExteriorSubset z).hasSum
  have hp := hasProd_one_add_of_hasSum_prod hs
  have he := hp.unique (hasProd_xiEndpointExteriorSeries z)
  rwa [he] at hs

/-- The elementary endpoint mass at a fixed cardinality, with complex weights retained. -/
def xiEndpointExteriorCoefficient (n : ℕ) : ℂ :=
  ∑' S : {S : Finset XiZeroCopy // S.card = n},
    ∏ q ∈ S.val, xiStripEdgeWeight q / xiEndpointColorMass

/-- Grouping the absolutely convergent subset expansion by cardinality gives a scalar series. -/
theorem hasSum_xiEndpointExteriorCoefficient (z : ℂ) :
    HasSum (fun n => xiEndpointExteriorCoefficient n * z ^ n) (xiEndpointExteriorSeries z) := by
  have h := (hasSum_xiEndpointExteriorSubset z).tsum_fiberwise Finset.card
  refine h.congr_fun fun n => ?_
  symm
  change (∑' S : {S : Finset XiZeroCopy // S.card = n},
    ∏ q ∈ S.val, z * xiStripEdgeWeight q / xiEndpointColorMass) = _
  have he (S : {S : Finset XiZeroCopy // S.card = n}) :
      (∏ q ∈ S.val, z * xiStripEdgeWeight q / xiEndpointColorMass) =
        (∏ q ∈ S.val, xiStripEdgeWeight q / xiEndpointColorMass) * z ^ n := by
    simp only [mul_div_assoc, Finset.prod_mul_distrib, Finset.prod_const, S.property]
    exact mul_comm _ _
  simp only [he, tsum_mul_right, xiEndpointExteriorCoefficient]

/-- Each subset coefficient is the corresponding Taylor coefficient of the arithmetic series. -/
theorem xiEndpointExteriorCoefficient_eq_deriv (n : ℕ) :
    xiEndpointExteriorCoefficient n = iteratedDeriv n xiEndpointExteriorSeries 0 / n.factorial := by
  exact PowerSeriesUniqueness.coeff_eq_iteratedDeriv_div_factorial_of_hasSum
    (r := 1) (by norm_num) (fun z _ => hasSum_xiEndpointExteriorCoefficient z) n

/-- Every elementary-symmetric endpoint sum is real and nonnegative, without RH. -/
theorem xiEndpointExteriorCoefficient_nonneg (n : ℕ) :
    0 ≤ xiEndpointExteriorCoefficient n := by
  rw [xiEndpointExteriorCoefficient_eq_deriv]
  exact div_nonneg (nonnegTaylorAtZero_xiEndpointExteriorSeries.2 n) (by positivity)

end RHTower
