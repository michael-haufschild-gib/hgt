import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketCoercivity
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.RelativePrimeHeads

/-!
# Adjunction energy retained above a conductor space

Orthogonality makes the low conductor coefficients small through the Gram
remainder. The direct prime-defect lower bound therefore supplies both a
logarithmic gap and a fixed fraction of the entire adjunction energy.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory CriticalScaleArithmeticRigidity
  ArithmeticElectrostatics

/-- A nearly unit conductor packet orthogonal to the low conductor space retains
adjunction energy at least two fifths of the cutoff logarithm. -/
theorem primeAdjunctionMass_ge_log_of_packet_orthogonal {Q R N : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hRR : R * R ≤ N)
    (hlog : 1080 * (1 + Real.log R) ≤ Real.log N)
    (a : ℕ → ℝ)
    (huQ : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace Q N)ᗮ)
    (hu_lo : 3 / 4 ≤ ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2)
    (hu_hi : ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ≤ 1) :
    (2 / 5 : ℝ) * Real.log Q ≤ primeAdjunctionMass R a := by
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let v := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let B := ∑ m ∈ Icc 1 Q, a m ^ 2
  have hR : 2 ≤ R := hQ.trans hQR
  have hH : 0 ≤ 1 + Real.log R := by positivity
  have h18 : 18 * (1 + Real.log R) ≤ Real.log N := by linarith only [hlog, hH]
  have hL : 0 < Real.log N := by
    have hh := Real.log_natCast_nonneg R
    linarith only [hlog, hh]
  have hQlog : Real.log Q ≤ Real.log R := Real.log_le_log
    (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast hQR)
  have h18Q : 18 * (1 + Real.log Q) ≤ Real.log N := by linarith only [h18, hQlog]
  have hQQ : Q * Q ≤ N := (Nat.mul_le_mul hQR hQR).trans hRR
  have hA : 1 / 2 ≤ A := by
    have hh := (half_and_three_halves_riesz_of_log_le hR hRR h18 a).2
    change ‖u‖ ^ 2 ≤ (3 / 2 : ℝ) * A at hh
    change 3 / 4 ≤ ‖u‖ ^ 2 at hu_lo
    linarith only [hh, hu_lo]
  have hv : ‖v‖ ≤ 1 / 20 := by
    have hh := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ Q) hQR hR hRR h18 huQ).2
    change ‖v‖ ≤ (54 * (1 + Real.log R) / Real.log N) * ‖u‖ at hh
    have hb : 54 * (1 + Real.log R) / Real.log N ≤ 1 / 20 := by
      apply (div_le_iff₀ hL).mpr
      linarith only [hlog]
    exact hh.trans ((mul_le_mul hb hu_hi (norm_nonneg u) (by norm_num)).trans_eq
      (by ring : (1 / 20 : ℝ) * 1 = 1 / 20))
  have hB : B ≤ 1 / 200 := by
    have hh := (half_and_three_halves_riesz_of_log_le hQ hQQ h18Q a).1
    change (1 / 2 : ℝ) * B ≤ ‖v‖ ^ 2 at hh
    have hs : ‖v‖ ^ 2 ≤ (1 / 20 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) hv 2
    linarith only [hh, hs]
  have hlow : (∑ m ∈ Icc 1 R, if m ≤ Q then a m ^ 2 else 0) = B := by
    symm
    change (∑ m ∈ Icc 1 Q, a m ^ 2) = _
    calc
      _ = ∑ m ∈ Icc 1 Q, if m ≤ Q then a m ^ 2 else 0 :=
        sum_congr rfl fun m hm => (if_pos (mem_Icc.mp hm).2).symm
      _ = _ := sum_subset (Icc_subset_Icc le_rfl hQR) fun m hm hn => by
        exact if_neg (fun h => hn (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩))
  have hdiag : Real.log Q * (A - B) ≤ primeAdjunctionMass R a := by
    rw [← hlow, show A = ∑ m ∈ Icc 1 R, a m ^ 2 from rfl, ← sum_sub_distrib,
      mul_sum]
    unfold primeAdjunctionMass
    apply sum_le_sum
    intro m hm
    by_cases hmQ : m ≤ Q
    · rw [if_pos hmQ, sub_self, mul_zero]
      exact mul_nonneg (add_nonneg (Real.log_natCast_nonneg m) (tameDifferent_nonneg m))
        (sq_nonneg _)
    · rw [if_neg hmQ, sub_zero]
      have hl : Real.log Q ≤ Real.log m := Real.log_le_log
        (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast (not_le.mp hmQ).le)
      exact mul_le_mul_of_nonneg_right
        (hl.trans (le_add_of_nonneg_right (tameDifferent_nonneg m))) (sq_nonneg _)
  have hmass : (2 / 5 : ℝ) ≤ A - B := by linarith only [hA, hB]
  calc
    (2 / 5 : ℝ) * Real.log Q = Real.log Q * (2 / 5 : ℝ) := mul_comm _ _
    _ ≤ Real.log Q * (A - B) := mul_le_mul_of_nonneg_left hmass (Real.log_natCast_nonneg Q)
    _ ≤ _ := hdiag

/-- Direct prime coercivity retains an eighth of the full adjunction energy,
in addition to a quarter of the low cutoff logarithm. -/
theorem primePacket_energy_ge_adjunction_and_log_of_orthogonal {Q R N : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hRR : R * R ≤ N)
    (hlog : 1080 * (1 + Real.log R) ≤ Real.log N)
    (a : ℕ → ℝ)
    (huQ : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace Q N)ᗮ)
    (hu_lo : 3 / 4 ≤ ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2)
    (hu_hi : ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ≤ 1) :
    (1 / 8 : ℝ) * primeAdjunctionMass R a + (1 / 4 : ℝ) * Real.log Q -
        (Real.log 4 + 4) ≤
      renormalizedPrimeEnergy N (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hR : 2 ≤ R := hQ.trans hQR
  have hN : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
  have hlogR : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hL : 0 < Real.log N := by linarith only [hlog, hlogR]
  have htheta : (3 / 4 : ℝ) ≤ (Real.log N - 3 * Real.log R - 1) / Real.log N := by
    rw [le_div_iff₀ hL]
    linarith only [hlog, hlogR]
  have hdef := poleDefect_normalizedRamanujanPacket_ge_logarithmic hR hN a
  change ((Real.log N - 3 * Real.log R - 1) / Real.log N) * primeAdjunctionMass R a ≤
    poleDefect N (primeHorizonExtension u) at hdef
  have hd : (3 / 4 : ℝ) * primeAdjunctionMass R a ≤ poleDefect N (primeHorizonExtension u) :=
    (mul_le_mul_of_nonneg_right htheta (primeAdjunctionMass_nonneg R a)).trans hdef
  have hE := primeAdjunctionMass_ge_log_of_packet_orthogonal hQ hQR hRR hlog a huQ hu_lo hu_hi
  have hr := poleDefect_le_primeEnergy_add_row_cost u
  have hn : ‖u‖ ^ 2 ≤ 1 := by
    exact (pow_le_pow_left₀ (norm_nonneg u) hu_hi 2).trans_eq (one_pow 2)
  have hc : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  have hrow := mul_le_mul_of_nonneg_left hn hc
  linarith only [hd, hE, hr, hrow]

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.primeAdjunctionMass_ge_log_of_packet_orthogonal
#print axioms GaloisForLFunctions.CompletedArithmeticForms.primePacket_energy_ge_adjunction_and_log_of_orthogonal
