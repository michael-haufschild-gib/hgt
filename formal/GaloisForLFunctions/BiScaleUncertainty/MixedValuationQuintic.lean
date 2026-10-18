import GaloisForLFunctions.BiScaleUncertainty.SixthValuationPhaseRecovery

/-!
# Fifth-order coupling between distinct two-adic valuation classes

A primitive triple in a lower valuation class and a primitive pair in a higher
class have the same frequency sum. Their difference is an explicit quintic
resonance. Its literal translated-moment readout is the cube of the lower
coordinate times the square of the higher coordinate, with exact normalization.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.MixedValuation
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

def lowerOrder (k p : ℕ) : ℕ := 2^k * (2*p+1)

def upperOrder (k s q : ℕ) : ℕ := 2^(k+(s+1)) * (2*q+1)

/-- Every nonnegative slack gives an actual cutoff containing both orders. -/
def cutoff (n k s p q : ℕ) : ℕ := max (lowerOrder k p) (upperOrder k s q) + n

def pairCoefficient (s q : ℕ) : ℕ := 2^(s+1) * (2*q+1) - 1

private theorem lower_mem (n k s p q : ℕ) :
    lowerOrder k p ∈ Finset.Icc 1 (cutoff n k s p q) := by
  have hp : 0 < lowerOrder k p := by unfold lowerOrder; positivity
  have hm := le_max_left (lowerOrder k p) (upperOrder k s q)
  unfold cutoff
  exact Finset.mem_Icc.mpr ⟨hp, by omega⟩

private theorem upper_mem (n k s p q : ℕ) :
    upperOrder k s q ∈ Finset.Icc 1 (cutoff n k s p q) := by
  have hp : 0 < upperOrder k s q := by unfold upperOrder; positivity
  have hm := le_max_right (lowerOrder k p) (upperOrder k s q)
  unfold cutoff
  exact Finset.mem_Icc.mpr ⟨hp, by omega⟩

private theorem coefficient_odd (s q : ℕ) : Odd (pairCoefficient s q) := by
  have hp : 0 < 2^s * (2*q+1) := by positivity
  have he : 2^(s+1) * (2*q+1) = 2 * (2^s * (2*q+1)) := by
    rw [pow_succ]
    ring
  refine ⟨2^s * (2*q+1) - 1, ?_⟩
  unfold pairCoefficient
  rw [he]
  omega

private theorem coefficient_coprime (k s q : ℕ) :
    Nat.Coprime (upperOrder k s q) (pairCoefficient s q) := by
  have hA : 1 ≤ 2^(s+1) * (2*q+1) := by
    have : 0 < 2^(s+1) * (2*q+1) := by positivity
    omega
  have hc : Nat.Coprime (2^(s+1) * (2*q+1)) (pairCoefficient s q) :=
    (Nat.coprime_self_sub_right hA).mpr (Nat.coprime_one_right _)
  have hq : Nat.Coprime (2*q+1) (pairCoefficient s q) :=
    hc.coprime_dvd_left ⟨2^(s+1), by ring⟩
  exact Nat.coprime_mul_iff_left.mpr
    ⟨(coefficient_odd s q).coprime_two_left.pow_left (k+(s+1)), hq⟩

/-- Two primitive upper-order frequencies whose sum belongs to the lower two-adic class. -/
def upperPair (N k s q : ℕ) : Fin 2 → ZMod N.factorial :=
  let r : ZMod N.factorial := (N.factorial / upperOrder k s q : ℕ)
  ![r, pairCoefficient s q • r]

private theorem upperPair_order (n k s p q : ℕ) (i : Fin 2) :
    addOrderOf (upperPair (cutoff n k s p q) k s q i) = upperOrder k s q := by
  have hr := frequency_order (upper_mem n k s p q)
  fin_cases i
  · exact hr
  · change addOrderOf (pairCoefficient s q •
        (((cutoff n k s p q).factorial / upperOrder k s q : ℕ) :
          ZMod (cutoff n k s p q).factorial)) = _
    have hc : Nat.Coprime (addOrderOf
        ((((cutoff n k s p q).factorial / upperOrder k s q : ℕ)) :
          ZMod (cutoff n k s p q).factorial)) (pairCoefficient s q) := by
      rw [hr]
      exact coefficient_coprime k s q
    exact hc.addOrderOf_nsmul.trans hr

private theorem upperPair_sum (n k s p q : ℕ) :
    (∑ i, upperPair (cutoff n k s p q) k s q i) =
      (((cutoff n k s p q).factorial / 2^k : ℕ) :
        ZMod (cutoff n k s p q).factorial) := by
  let N := cutoff n k s p q
  have he := upper_mem n k s p q
  have hdvd : upperOrder k s q ∣ N.factorial :=
    Nat.dvd_factorial (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
  obtain ⟨t,ht⟩ := hdvd
  have hD : 0 < upperOrder k s q := by unfold upperOrder; positivity
  have h2 : 0 < (2 : ℕ)^k := by positivity
  have hA : 1 ≤ 2^(s+1) * (2*q+1) := by
    have : 0 < 2^(s+1) * (2*q+1) := by positivity
    omega
  have hfactor : upperOrder k s q = 2^k * (2^(s+1) * (2*q+1)) := by
    unfold upperOrder
    rw [pow_add]
    ring
  have hdiv : N.factorial / upperOrder k s q = t := by
    rw [ht, Nat.mul_div_cancel_left _ hD]
  have hcenter : N.factorial / 2^k = (2^(s+1) * (2*q+1)) * t := by
    rw [ht, hfactor, Nat.mul_assoc, Nat.mul_div_cancel_left _ h2]
  change (∑ i, upperPair N k s q i) = ((N.factorial / 2^k : ℕ) : ZMod N.factorial)
  rw [Fin.sum_univ_two]
  change ((N.factorial / upperOrder k s q : ℕ) : ZMod N.factorial) +
    pairCoefficient s q • ((N.factorial / upperOrder k s q : ℕ) : ZMod N.factorial) = _
  rw [hdiv, hcenter, nsmul_eq_mul]
  unfold pairCoefficient
  push_cast [Nat.cast_sub hA]
  ring

/-- Three lower-order frequencies balanced by two higher-order frequencies. -/
def frequencies (n k s p q : ℕ) : Fin 5 → ZMod (cutoff n k s p q).factorial :=
  let N := cutoff n k s p q
  ![valuationTriple N k (2*p+1) 0, valuationTriple N k (2*p+1) 1,
    valuationTriple N k (2*p+1) 2, -upperPair N k s q 0, -upperPair N k s q 1]

theorem frequencies_sum (n k s p q : ℕ) : (∑ i, frequencies n k s p q i) = 0 := by
  have hp : Odd (2*p+1) := ⟨p, rfl⟩
  have hlow := valuationTriple_sum hp (lower_mem n k s p q)
  have hupp := upperPair_sum n k s p q
  simp only [Fin.sum_univ_three] at hlow
  simp only [Fin.sum_univ_two] at hupp
  rw [Fin.sum_univ_five]
  change valuationTriple (cutoff n k s p q) k (2*p+1) 0 +
    valuationTriple (cutoff n k s p q) k (2*p+1) 1 +
    valuationTriple (cutoff n k s p q) k (2*p+1) 2 +
    -upperPair (cutoff n k s p q) k s q 0 +
    -upperPair (cutoff n k s p q) k s q 1 = 0
  linear_combination hlow - hupp

theorem frequencies_order_product (n k s p q : ℕ) (v : ℕ → ℂ) :
    (∏ i, v (addOrderOf (frequencies n k s p q i))) =
      v (lowerOrder k p)^3 * v (upperOrder k s q)^2 := by
  have hp : Odd (2*p+1) := ⟨p, rfl⟩
  rw [Fin.prod_univ_five]
  change v (addOrderOf (valuationTriple (cutoff n k s p q) k (2*p+1) 0)) *
    v (addOrderOf (valuationTriple (cutoff n k s p q) k (2*p+1) 1)) *
    v (addOrderOf (valuationTriple (cutoff n k s p q) k (2*p+1) 2)) *
    v (addOrderOf (-upperPair (cutoff n k s p q) k s q 0)) *
    v (addOrderOf (-upperPair (cutoff n k s p q) k s q 1)) = _
  rw [addOrderOf_neg, addOrderOf_neg,
    valuationTriple_order hp (lower_mem n k s p q),
    valuationTriple_order hp (lower_mem n k s p q),
    valuationTriple_order hp (lower_mem n k s p q), upperPair_order, upperPair_order]
  change v (lowerOrder k p) * v (lowerOrder k p) * v (lowerOrder k p) *
    v (upperOrder k s q) * v (upperOrder k s q) = _
  ring

/-- Literal fifth translated moments, Fourier transformed in their five lag variables. -/
def fifthReadout (n k s p q : ℕ) (c : ℕ → ℝ) : ℝ :=
  (momentDFT
    (fun h : Fin 5 → ZMod (cutoff n k s p q).factorial =>
      (translatedMoment (cutoff n k s p q) c (fun i => (h i).val) : ℂ))
    (frequencies n k s p q)).re

/-- An unconditional mixed-valuation formula on the actual divisor-sieve observations. -/
theorem fifthReadout_eq (n k s p q : ℕ) (c : ℕ → ℝ) :
    fifthReadout n k s p q c = ((cutoff n k s p q).factorial : ℝ)^5 *
      selbergMultiplesCoord (cutoff n k s p q) c (lowerOrder k p)^3 *
      selbergMultiplesCoord (cutoff n k s p q) c (upperOrder k s q)^2 := by
  unfold fifthReadout
  simp_rw [translatedMoment_complex_eq, ZMod.natCast_zmod_val]
  rw [momentDFT_sieve, if_pos (frequencies_sum n k s p q), frequencies_order_product]
  rw [coordinate_ofReal, coordinate_ofReal]
  norm_cast
  ring

/-- Upper magnitude and the quintic observation orient the lower coordinate,
with the exact zero exception. No nonvanishing assumption is imposed. -/
theorem fifthReadout_and_upper_sq_iff (n k s p q : ℕ) (c e : ℕ → ℝ) :
    let N := cutoff n k s p q
    let a := selbergMultiplesCoord N c
    let b := selbergMultiplesCoord N e
    (fifthReadout n k s p q c = fifthReadout n k s p q e ∧
      a (upperOrder k s q)^2 = b (upperOrder k s q)^2) ↔
    (a (upperOrder k s q)^2 = b (upperOrder k s q)^2 ∧
      (a (upperOrder k s q) = 0 ∨ a (lowerOrder k p) = b (lowerOrder k p))) := by
  dsimp only
  rw [fifthReadout_eq, fifthReadout_eq]
  let a := selbergMultiplesCoord (cutoff n k s p q) c
  let b := selbergMultiplesCoord (cutoff n k s p q) e
  let d := lowerOrder k p
  let u := upperOrder k s q
  let C := ((cutoff n k s p q).factorial : ℝ)^5
  change (C * a d^3 * a u^2 = C * b d^3 * b u^2 ∧ a u^2 = b u^2) ↔
    (a u^2 = b u^2 ∧ (a u = 0 ∨ a d = b d))
  have hC : C ≠ 0 := by dsimp [C]; positivity
  constructor
  · rintro ⟨hr, hu⟩
    refine ⟨hu, ?_⟩
    by_cases hz : a u = 0
    · exact Or.inl hz
    · right
      rw [← hu] at hr
      have hh : a d^3 * a u^2 = b d^3 * a u^2 :=
        mul_left_cancel₀ hC (by simpa only [mul_assoc] using hr)
      exact (show Odd (3 : ℕ) from ⟨1, rfl⟩).pow_injective
        (mul_right_cancel₀ (pow_ne_zero 2 hz) hh)
  · rintro ⟨hu, hz | hl⟩
    · refine ⟨?_, hu⟩
      rw [← hu, hz]
      simp
    · exact ⟨by rw [hl, hu], hu⟩

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.MixedValuation
