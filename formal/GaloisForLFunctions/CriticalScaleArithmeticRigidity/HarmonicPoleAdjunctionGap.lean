import GaloisForLFunctions.CriticalScaleArithmeticRigidity.AdjunctionResidualCoercivity
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.HarmonicPoleCentering
import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketCoercivity

/-!
# Adjunction control on the actual harmonic pole hyperplane

Polarized harmonic Gram control bounds the constant coefficient of a
physically pole-neutral packet. The exact first arithmetic excitation
then controls its entire coefficient mass. The relative prime residual
bound consequently retains the actual finite-horizon pole constraint.
-/

noncomputable section

open Finset
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms SignedArithmeticHodgeTheory

/-- The packet's Euclidean pole pairing is exactly its physical harmonic functional. -/
theorem horizonPacket_inner_pole_eq_harmonicSum (Q N : ℕ) (a : ℕ → ℝ) :
    ⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector 1 N⟫ =
        SelectiveMultiscaleArithmeticPositivity.harmonicSum N (conductorHorizonProfile Q a) /
          Real.log N := by
  have hpole (n : ℕ) : ramanujanPoleProfile 1 n = (Real.sqrt n)⁻¹ := by
    have hc := BezoutValuationIncidence.ramanujanLagCoefficient_of_dvd (one_dvd n)
    simp only [Nat.totient_one, Nat.cast_one] at hc
    simp only [ramanujanPoleProfile,
      normalizedRamanujanMode_eq_coefficient (by decide : 0 < (1 : ℕ)), hc,
      Nat.totient_one, Nat.cast_one, Real.sqrt_one, div_one, one_div]
  have hsum : (∑ m ∈ Icc 1 Q, a m *
      ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile 1 n) =
        SelectiveMultiscaleArithmeticPositivity.harmonicSum N (conductorHorizonProfile Q a) := by
    simp only [mul_sum, hpole,
      SelectiveMultiscaleArithmeticPositivity.harmonicSum, conductorHorizonProfile,
      normalizedConductorPacket]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    simp only [ramanujanPoleProfile, sum_div]
    apply sum_congr rfl
    intro m _
    ring
  calc
    _ = ∑ m ∈ Icc 1 Q, a m *
        ((∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile 1 n) / Real.log N) := by
      simp only [sum_inner, real_inner_smul_left, normalizedRamanujanHorizonVector_inner]
    _ = (∑ m ∈ Icc 1 Q, a m *
        ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile 1 n) / Real.log N := by
      simp only [sum_div, mul_div_assoc]
    _ = _ := by rw [hsum]

/-- The explicit coefficient centering realizes the Euclidean pole hyperplane as well. -/
theorem harmonicCentered_horizonPacket_inner_pole {Q N : ℕ} (hQ : 1 ≤ Q) (hN : 1 ≤ N)
    (a : ℕ → ℝ) :
    ⟪∑ m ∈ Icc 1 Q, harmonicCenteredCoefficients Q N a m • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector 1 N⟫ = 0 := by
  rw [horizonPacket_inner_pole_eq_harmonicSum, harmonicSum_centeredCoefficients hQ hN, zero_div]

private theorem coefficient_mass_split {Q : ℕ} (hQ : 1 ≤ Q) (a : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Q, a m ^ 2) =
      (∑ m ∈ Icc 1 Q, removeConstantConductor a m ^ 2) + a 1 ^ 2 := by
  have hterm (m : ℕ) : a m ^ 2 = removeConstantConductor a m ^ 2 +
      if m = 1 then a 1 ^ 2 else 0 := by
    by_cases hm : m = 1
    · subst m
      simp [removeConstantConductor]
    · simp only [removeConstantConductor, if_neg hm, add_zero]
  calc
    _ = ∑ m ∈ Icc 1 Q,
        (removeConstantConductor a m ^ 2 + if m = 1 then a 1 ^ 2 else 0) :=
      sum_congr rfl fun m _ => hterm m
    _ = _ := by
      rw [sum_add_distrib, sum_ite_eq', if_pos (mem_Icc.mpr ⟨le_rfl, hQ⟩)]

/-- Literal orthogonality to the physical pole bounds the constant conductor coefficient. -/
theorem constantCoefficient_sq_le_quarter_mass_of_harmonic_neutral {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N) (a : ℕ → ℝ)
    (ha : ⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector 1 N⟫ = 0) :
    a 1 ^ 2 ≤ (1 / 4 : ℝ) * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
  let b : ℕ → ℝ := fun m => if m = 1 then 1 else 0
  have h1 : 1 ∈ Icc 1 Q := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hb : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) =
      normalizedRamanujanHorizonVector 1 N := by simp [b, h1]
  have hpair : (∑ m ∈ Icc 1 Q, a m * b m) = a 1 := by simp [b, h1]
  have hmass : (∑ m ∈ Icc 1 Q, b m ^ 2) = 1 := by simp [b, h1]
  have h := abs_inner_sum_normalizedRamanujanHorizonVector_sub_le hQ hQN a b
  rw [hb, ha, hpair, hmass, Real.sqrt_one, mul_one, zero_sub, abs_neg] at h
  have hL : 0 < Real.log (N : ℝ) := by
    linarith only [hlog, Real.log_natCast_nonneg Q]
  have hdelta : 9 * (1 + Real.log Q) / Real.log N ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hL]
    linarith only [hlog]
  have habs := h.trans (mul_le_mul_of_nonneg_right hdelta
    (Real.sqrt_nonneg (∑ m ∈ Icc 1 Q, a m ^ 2)))
  have hM : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hprod := mul_nonneg (sub_nonneg.mpr habs)
    (add_nonneg (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2))
      (abs_nonneg (a 1)))
  nlinarith only [hprod, Real.sq_sqrt hM, sq_abs (a 1)]

/-- The true harmonic pole hyperplane retains three quarters of the exact excitation gap. -/
theorem coefficient_mass_le_harmonic_neutral_adjunction_gap {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log N) (a : ℕ → ℝ)
    (ha : ⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector 1 N⟫ = 0) :
    ((3 / 2 : ℝ) * Real.log 2) * (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
      primeAdjunctionMass Q a := by
  have hground := constantCoefficient_sq_le_quarter_mass_of_harmonic_neutral hQ hQN hlog a ha
  have hsplit := coefficient_mass_split (by omega : 1 ≤ Q) a
  have hmass : (3 / 4 : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
      ∑ m ∈ Icc 1 Q, removeConstantConductor a m ^ 2 := by
    linarith only [hground, hsplit]
  have hscaled := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))
  have hgap := coefficient_mass_le_adjunction_gap Q a
  nlinarith only [hscaled, hgap]

/-- The source-relative prime residual bound holds on the actual finite-horizon pole
hyperplane, with a quadratic logarithmic conductor cost. -/
theorem exists_primeResidual_harmonic_neutral_relative_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Q N : ℕ, 2 ≤ Q → 2 ≤ N → Q * Q ≤ N →
      18 * (1 + Real.log Q) ≤ Real.log N → ∀ a : ℕ → ℝ,
      ⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N,
        normalizedRamanujanHorizonVector 1 N⟫ = 0 →
      (∑ n ∈ Icc 1 N, (∑ m ∈ Icc 1 Q, a m * ramanujanPrimeResidual m N n) ^ 2) / Real.log N ≤
        C * (1 + Real.log Q) ^ 2 / Real.log N * primeAdjunctionMass Q a := by
  obtain ⟨C, hC, hres⟩ := exists_primeResidual_packet_relative_log_sq_le
  have hgap : 0 < (3 / 2 : ℝ) * Real.log 2 := mul_pos (by norm_num) (Real.log_pos (by norm_num))
  refine ⟨C / ((3 / 2 : ℝ) * Real.log 2) + 532, by positivity, ?_⟩
  intro Q N hQ hN hQN hlog a ha
  have h := hres Q N hQ hN a
  have hM := coefficient_mass_le_harmonic_neutral_adjunction_gap hQ hQN hlog a ha
  have hL := primeAdjunctionMass_nonneg Q a
  have hH : 0 ≤ 1 + Real.log (Q : ℝ) := by positivity
  have hH2 : 1 + Real.log (Q : ℝ) ≤ (1 + Real.log (Q : ℝ)) ^ 2 := by
    nlinarith only [Real.log_natCast_nonneg Q, sq_nonneg (Real.log (Q : ℝ))]
  have hCM : C * (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
      (C / ((3 / 2 : ℝ) * Real.log 2)) * primeAdjunctionMass Q a := by
    calc
      _ = (C / ((3 / 2 : ℝ) * Real.log 2)) *
          (((3 / 2 : ℝ) * Real.log 2) * ∑ m ∈ Icc 1 Q, a m ^ 2) := by
        rw [← mul_assoc, div_mul_cancel₀ _ hgap.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left hM (div_nonneg hC.le hgap.le)
  have hlinear := mul_le_mul_of_nonneg_left hCM hH
  have hquadratic := mul_le_mul_of_nonneg_right hH2
    (mul_nonneg (div_nonneg hC.le hgap.le) hL)
  have hnum :
      C * (1 + Real.log Q) * (∑ m ∈ Icc 1 Q, a m ^ 2) +
          532 * (1 + Real.log Q) ^ 2 * primeAdjunctionMass Q a ≤
        (C / ((3 / 2 : ℝ) * Real.log 2) + 532) * (1 + Real.log Q) ^ 2 * primeAdjunctionMass Q a := by
    nlinarith only [hlinear, hquadratic]
  exact (h.trans (div_le_div_of_nonneg_right hnum (Real.log_natCast_nonneg N))).trans_eq (by ring)

#print axioms constantCoefficient_sq_le_quarter_mass_of_harmonic_neutral
#print axioms horizonPacket_inner_pole_eq_harmonicSum
#print axioms harmonicCentered_horizonPacket_inner_pole
#print axioms coefficient_mass_le_harmonic_neutral_adjunction_gap
#print axioms exists_primeResidual_harmonic_neutral_relative_sq_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
