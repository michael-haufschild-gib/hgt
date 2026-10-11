import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticBinomial
import GaloisForLFunctions.HTGeometry.CentralBinomialConvolutionAsymptotic

/-! The arithmetic reference mass has an exact two-order plateau and square-root growth. -/

noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry

theorem finiteWeilArithmeticMass_even_wallis (m : ℕ) :
    finiteWeilArithmeticMass (2 * m) * normalizedCentralBinom (m + 1) = 1 := by
  have hchoose : Nat.centralBinom (m + 1) = 2 * (2 * m + 1).choose m := by
    rw [Nat.centralBinom_eq_two_mul_choose,
      show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      Nat.choose_succ_succ', Nat.choose_symm_half]
    omega
  have hC : 0 < ((2 * m + 1).choose m : ℝ) := by
    have hc := Nat.centralBinom_pos (m + 1)
    rw [hchoose] at hc
    exact_mod_cast (show 0 < (2 * m + 1).choose m by omega)
  have hpow : (4 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ (2 * m + 1) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul,
      show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ]
    ring
  rw [finiteWeilArithmeticMass_eq_binomial, show (2 * m + 1) / 2 = m by omega,
    normalizedCentralBinom, hchoose, Nat.cast_mul, Nat.cast_ofNat, hpow]
  field_simp [hC.ne']

theorem finiteWeilArithmeticMass_odd_wallis (m : ℕ) :
    finiteWeilArithmeticMass (2 * m + 1) * normalizedCentralBinom (m + 1) = 1 := by
  have hC : (Nat.centralBinom (m + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos (m + 1)).ne'
  have hpow : (2 : ℝ) ^ (2 * m + 1 + 1) = 4 ^ (m + 1) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
    congr 1
  rw [finiteWeilArithmeticMass_eq_binomial,
    show (2 * m + 1 + 1) / 2 = m + 1 by omega,
    show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
    ← Nat.centralBinom_eq_two_mul_choose]
  rw [show (2 : ℝ) ^ (2 * (m + 1)) = 4 ^ (m + 1) by
    simpa only [show 2 * m + 1 + 1 = 2 * (m + 1) by omega] using hpow]
  unfold normalizedCentralBinom
  field_simp [hC]

/-- Every order uses the next central-binomial coefficient after halving the order. -/
theorem finiteWeilArithmeticMass_mul_normalizedCentralBinom (r : ℕ) :
    finiteWeilArithmeticMass r * normalizedCentralBinom (r / 2 + 1) = 1 := by
  rcases (show r = 2 * (r / 2) ∨ r = 2 * (r / 2) + 1 by omega) with h | h
  · simpa only [← h] using finiteWeilArithmeticMass_even_wallis (r / 2)
  · simpa only [← h] using finiteWeilArithmeticMass_odd_wallis (r / 2)

/-- Consecutive even and odd moment orders have exactly equal reference mass. -/
theorem finiteWeilArithmeticMass_pair (m : ℕ) :
    finiteWeilArithmeticMass (2 * m) = finiteWeilArithmeticMass (2 * m + 1) := by
  have he := finiteWeilArithmeticMass_even_wallis m
  have ho := finiteWeilArithmeticMass_odd_wallis m
  have hc : 0 < normalizedCentralBinom (m + 1) := by
    unfold normalizedCentralBinom
    exact div_pos (by exact_mod_cast Nat.centralBinom_pos (m + 1)) (by positivity)
  nlinarith only [he, ho, hc]

/-- The exact Wallis identity gives a parity-sensitive lower bound on squared mass. -/
theorem finiteWeilArithmeticMass_sq_lower (r : ℕ) :
    ((2 * (r / 2) + 3 : ℕ) : ℝ) ≤ finiteWeilArithmeticMass r ^ 2 := by
  let m := r / 2 + 1
  let c := normalizedCentralBinom m
  let G := finiteWeilArithmeticMass r
  have hc : G * c = 1 := finiteWeilArithmeticMass_mul_normalizedCentralBinom r
  have hW := one_le_Wallis_W m
  have hid := wallis_mul_normalizedCentralBinom_sq m
  have hden : 0 < 2 * (m : ℝ) + 1 := by positivity
  have hsq : c ^ 2 ≤ 1 / (2 * (m : ℝ) + 1) := by
    calc
      c ^ 2 ≤ Real.Wallis.W m * c ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hW (sq_nonneg c)
      _ = _ := hid
  have hbound := (le_div_iff₀ hden).mp hsq
  have hmul := mul_le_mul_of_nonneg_right hbound (sq_nonneg G)
  have hprod : c ^ 2 * G ^ 2 = 1 := by
    calc
      _ = (G * c) ^ 2 := by ring
      _ = 1 := by rw [hc]; norm_num
  have hresult : 2 * (m : ℝ) + 1 ≤ G ^ 2 := by
    calc
      _ = (2 * (m : ℝ) + 1) * (c ^ 2 * G ^ 2) := by rw [hprod]; ring
      _ = (c ^ 2 * (2 * (m : ℝ) + 1)) * G ^ 2 := by ring
      _ ≤ _ := by simpa only [one_mul] using hmul
  have hm : 2 * (m : ℝ) + 1 = ((2 * (r / 2) + 3 : ℕ) : ℝ) := by
    dsimp [m]
    push_cast
    ring
  rw [hm] at hresult
  exact hresult

theorem finiteWeilArithmeticMass_sqrt_lower (r : ℕ) :
    Real.sqrt ((r + 2 : ℕ) : ℝ) ≤ finiteWeilArithmeticMass r := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith only [finiteWeilArithmeticMass_ge_two r]
  · have h := finiteWeilArithmeticMass_sq_lower r
    have hr : ((r + 2 : ℕ) : ℝ) ≤ ((2 * (r / 2) + 3 : ℕ) : ℝ) := by
      exact_mod_cast (show r + 2 ≤ 2 * (r / 2) + 3 by omega)
    exact hr.trans h

end RHTower
