import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketCoercivity
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.RelativePrimeHeads

/-!
# Adjunction energy retained above a conductor space

Orthogonality to the low conductors forces coefficient mass above the cutoff. The direct
prime-defect lower bound therefore supplies both a logarithmic gap and a fixed fraction of the
entire adjunction energy, on every conductor span in the Riesz range `4 log R + 18 ≤ log N`.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory CriticalScaleArithmeticRigidity
  ArithmeticElectrostatics

/-- **Adjunction above a conductor space.** A nearly unit packet orthogonal to the low conductors
retains adjunction energy at least half the cutoff logarithm. Orthogonality gives
`‖u_{>Q}‖² = ‖u‖² + ‖u_{≤Q}‖² ≥ ‖u‖²`, and the upper Riesz bound turns this into coefficient mass
above `Q`. -/
theorem half_log_le_primeAdjunctionMass_of_orthogonal {Q R N : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hRR : R * R ≤ N)
    (hlog : 4 * Real.log R + 18 ≤ Real.log N)
    (a : ℕ → ℝ)
    (huQ : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace Q N)ᗮ)
    (hu_lo : 3 / 4 ≤ ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2) :
    (1 / 2 : ℝ) * Real.log Q ≤ primeAdjunctionMass R a := by
  let aHigh : ℕ → ℝ := fun m => if m ≤ Q then 0 else a m
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let v := ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N
  let w := ∑ m ∈ Icc 1 R, aHigh m • normalizedRamanujanHorizonVector m N
  have hR : 2 ≤ R := hQ.trans hQR
  have hvmem : v ∈ conductorSubspace Q N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N a
  have huv : ⟪v, u⟫ = 0 := (Submodule.mem_orthogonal (conductorSubspace Q N) u).mp huQ v hvmem
  have hvlow : v = ∑ m ∈ Icc 1 R, (if m ≤ Q then a m else 0) •
      normalizedRamanujanHorizonVector m N := by
    calc
      v = ∑ m ∈ Icc 1 Q, (if m ≤ Q then a m else 0) • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]
      _ = _ := sum_subset (Icc_subset_Icc le_rfl hQR) fun m hmR hmQ => by
        have hnot : ¬m ≤ Q := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
        rw [if_neg hnot, zero_smul]
  have hsplit : u = v + w := by
    rw [hvlow]
    change _ = _ + ∑ m ∈ Icc 1 R, aHigh m • normalizedRamanujanHorizonVector m N
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    dsimp only [aHigh]
    split_ifs <;> simp
  have hnorm : ‖u‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    have hw : w = u - v := by rw [hsplit]; abel
    have hexp : ‖w‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
      rw [hw, @norm_sub_sq_real, real_inner_comm, huv]
      ring
    nlinarith only [hexp, sq_nonneg ‖v‖]
  have hriesz := (half_and_three_halves_riesz_of_four_log_le hR hRR hlog aHigh).2
  change ‖w‖ ^ 2 ≤ _ at hriesz
  change 3 / 4 ≤ ‖u‖ ^ 2 at hu_lo
  have hmass : (1 / 2 : ℝ) ≤ ∑ m ∈ Icc 1 R, aHigh m ^ 2 := by
    linarith only [hriesz, hnorm, hu_lo]
  have hdiag : Real.log Q * ∑ m ∈ Icc 1 R, aHigh m ^ 2 ≤ primeAdjunctionMass R a := by
    rw [mul_sum]
    unfold primeAdjunctionMass
    refine sum_le_sum fun m hm => ?_
    dsimp only [aHigh]
    by_cases hmQ : m ≤ Q
    · rw [if_pos hmQ, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg (add_nonneg (Real.log_natCast_nonneg m) (tameDifferent_nonneg m))
        (sq_nonneg _)
    · rw [if_neg hmQ]
      have hl : Real.log Q ≤ Real.log m := Real.log_le_log
        (by exact_mod_cast (show 0 < Q by omega)) (by exact_mod_cast (not_le.mp hmQ).le)
      exact mul_le_mul_of_nonneg_right
        (hl.trans (le_add_of_nonneg_right (tameDifferent_nonneg m))) (sq_nonneg _)
  calc
    (1 / 2 : ℝ) * Real.log Q = Real.log Q * (1 / 2 : ℝ) := mul_comm _ _
    _ ≤ Real.log Q * ∑ m ∈ Icc 1 R, aHigh m ^ 2 :=
      mul_le_mul_of_nonneg_left hmass (Real.log_natCast_nonneg Q)
    _ ≤ _ := hdiag

/-- A nearly unit conductor packet orthogonal to the low conductor space retains
adjunction energy at least two fifths of the cutoff logarithm. -/
theorem primeAdjunctionMass_ge_log_of_packet_orthogonal {Q R N : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hRR : R * R ≤ N)
    (hlog : 1080 * (1 + Real.log R) ≤ Real.log N)
    (a : ℕ → ℝ)
    (huQ : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace Q N)ᗮ)
    (hu_lo : 3 / 4 ≤ ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2)
    (_hu_hi : ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ≤ 1) :
    (2 / 5 : ℝ) * Real.log Q ≤ primeAdjunctionMass R a := by
  have hlogR := Real.log_natCast_nonneg R
  have h := half_log_le_primeAdjunctionMass_of_orthogonal hQ hQR hRR (by linarith only [hlog, hlogR])
    a huQ hu_lo
  linarith only [h, Real.log_natCast_nonneg Q]

/-- **Prime coercivity in the Riesz range.** Above a conductor space, direct prime coercivity retains
an eighth of the adjunction energy and a sixteenth of the cutoff logarithm. The pole defect keeps a
fraction `(log N − 3 log R − 1)/log N ≥ 1/4` of the adjunction energy. -/
theorem primePacket_energy_ge_adjunction_and_log_of_four_log {Q R N : ℕ}
    (hQ : 2 ≤ Q) (hQR : Q ≤ R) (hRR : R * R ≤ N)
    (hlog : 4 * Real.log R + 18 ≤ Real.log N)
    (a : ℕ → ℝ)
    (huQ : (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
      (conductorSubspace Q N)ᗮ)
    (hu_lo : 3 / 4 ≤ ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2)
    (hu_hi : ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ≤ 1) :
    (1 / 8 : ℝ) * primeAdjunctionMass R a + (1 / 16 : ℝ) * Real.log Q -
        (Real.log 4 + 4) ≤
      renormalizedPrimeEnergy N (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) := by
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  have hR : 2 ≤ R := hQ.trans hQR
  have hN : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
  have hlogR : 0 ≤ Real.log R := Real.log_natCast_nonneg R
  have hL : 0 < Real.log N := by linarith only [hlog, hlogR]
  have htheta : (1 / 4 : ℝ) ≤ (Real.log N - 3 * Real.log R - 1) / Real.log N := by
    rw [le_div_iff₀ hL]
    linarith only [hlog, hlogR]
  have hdef := poleDefect_normalizedRamanujanPacket_ge_logarithmic hR hN a
  change ((Real.log N - 3 * Real.log R - 1) / Real.log N) * primeAdjunctionMass R a ≤
    poleDefect N (primeHorizonExtension u) at hdef
  have hd : (1 / 4 : ℝ) * primeAdjunctionMass R a ≤ poleDefect N (primeHorizonExtension u) :=
    (mul_le_mul_of_nonneg_right htheta (primeAdjunctionMass_nonneg R a)).trans hdef
  have hE := half_log_le_primeAdjunctionMass_of_orthogonal hQ hQR hRR hlog a huQ hu_lo
  have hr := poleDefect_le_primeEnergy_add_row_cost u
  have hn : ‖u‖ ^ 2 ≤ 1 := by
    exact (pow_le_pow_left₀ (norm_nonneg u) hu_hi 2).trans_eq (one_pow 2)
  have hc : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  have hrow := mul_le_mul_of_nonneg_left hn hc
  linarith only [hd, hE, hr, hrow]

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
  have hE := half_log_le_primeAdjunctionMass_of_orthogonal hQ hQR hRR
    (by linarith only [hlog, hlogR]) a huQ hu_lo
  have hr := poleDefect_le_primeEnergy_add_row_cost u
  have hn : ‖u‖ ^ 2 ≤ 1 := by
    exact (pow_le_pow_left₀ (norm_nonneg u) hu_hi 2).trans_eq (one_pow 2)
  have hc : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); positivity
  have hrow := mul_le_mul_of_nonneg_left hn hc
  linarith only [hd, hE, hr, hrow, Real.log_natCast_nonneg Q]

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.primeAdjunctionMass_ge_log_of_packet_orthogonal
#print axioms GaloisForLFunctions.CompletedArithmeticForms.primePacket_energy_ge_adjunction_and_log_of_orthogonal
#print axioms GaloisForLFunctions.CompletedArithmeticForms.primePacket_energy_ge_adjunction_and_log_of_four_log
