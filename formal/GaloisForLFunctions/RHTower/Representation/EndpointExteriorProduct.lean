import GaloisForLFunctions.RHTower.Representation.EndpointExteriorSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The exact endpoint exterior product

Pairing opposite arguments of the centered Hadamard product cancels the genus-one
exponentials. Dividing the squared lift at two square coordinates gives an ordinary
product of the normalized endpoint factors. Absolute summability expands that product
as a sum over all finite subsets, retaining the complex endpoint weights.
-/

noncomputable section
open Complex Filter Topology
open scoped BigOperators
namespace RHTower

/-- Opposite centered arguments give the genus-zero product for the squared lift. -/
theorem hasProd_xiCentreLift_sq (y : ℂ) :
    HasProd (fun q : XiZeroCopy => 1 + y / xiSpectralPoint q ^ 2)
      ((xiCentreLift y / xiCentreLift 0) ^ 2) := by
  let z := Complex.sqrt (-y)
  have hz : z ^ 2 = -y := Complex.sq_sqrt _
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
    field_simp [xiSpectralPoint_ne_zero q, ha, hM]
    <;> ring
  have hval :
      ((xiCentreLift (1 / 4 + z / xiEndpointColorMass) / xiCentreLift 0) ^ 2) /
          ((xiCentreLift (1 / 4) / xiCentreLift 0) ^ 2) = xiEndpointExteriorSeries z := by
    unfold xiEndpointExteriorSeries
    field_simp [hG0, hG]
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

end RHTower
