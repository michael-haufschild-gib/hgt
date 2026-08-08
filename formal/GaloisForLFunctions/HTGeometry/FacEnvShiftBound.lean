import GaloisForLFunctions.HTGeometry.TruncatedJetCoeffBound

/-!
# The endpoint remainder against the envelope at the shifted index

The remainder of an endpoint expansion at index `M + R`, truncated at height `M`, carries the
binomial saving `C(M+R, R)^r`.  That saving is exactly what is needed to move the factorial envelope
from `M + R` back to `M`:

`facEnv r 𝔞 (M+R) ≤ (2^R R!)^r · 𝔞^R · C(M+R,R)^r · facEnv r 𝔞 M`,

because `(M+R)! = (M+R)_R · M!`, `(M+R)_R ≤ (M+R)^R`, and `(M+R)^R ≤ 2^R R! C(M+R,R)`.

Cancelling the binomial therefore bounds the remainder by the envelope at `M` times a constant
depending only on `R` — with no residual growth in `M` beyond the fixed polynomial weight.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The factorial of a shifted index factors through the descending factorial. -/
theorem factorial_add_eq_descFactorial_mul (M R : ℕ) :
    (M + R).factorial = (M + R).descFactorial R * M.factorial := by
  have h1 : R ≤ M + R := by omega
  have h2 := Nat.choose_mul_factorial_mul_factorial h1
  have h3 := Nat.descFactorial_eq_factorial_mul_choose (M + R) R
  have h4 : M + R - R = M := by omega
  rw [h4] at h2
  rw [h3]
  linarith [h2]

/-- **The envelope moves back across a shift at the cost of the binomial.** -/
theorem facEnv_add_le_choose {r 𝔞 : ℝ} (hr : 0 ≤ r) (h𝔞 : 0 < 𝔞) {M R : ℕ} (hRM : R ≤ M) :
    facEnv r 𝔞 (M + R)
      ≤ (((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * 𝔞 ^ R
        * ((((M + R).choose R : ℕ) : ℝ)) ^ r * facEnv r 𝔞 M := by
  have hfac := factorial_add_eq_descFactorial_mul M R
  have h2R : 2 * R ≤ M + R := by omega
  have hnat : (M + R).descFactorial R ≤ 2 ^ R * (R.factorial * (M + R).choose R) :=
    le_trans (Nat.descFactorial_le_pow _ _)
      (pow_le_two_pow_mul_factorial_mul_choose (M := M + R) (R := R) h2R)
  have hcast : (((M + R).descFactorial R : ℕ) : ℝ)
      ≤ (((2 ^ R * R.factorial : ℕ) : ℝ)) * ((((M + R).choose R : ℕ) : ℝ)) := by
    have hR : ((2 ^ R * (R.factorial * (M + R).choose R) : ℕ) : ℝ)
        = (((2 ^ R * R.factorial : ℕ) : ℝ)) * ((((M + R).choose R : ℕ) : ℝ)) := by
      push_cast
      ring
    rw [← hR]
    exact_mod_cast hnat
  have hdescnn : (0 : ℝ) ≤ (((M + R).descFactorial R : ℕ) : ℝ) := by positivity
  have hrpow : ((((M + R).descFactorial R : ℕ) : ℝ)) ^ r
      ≤ (((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * ((((M + R).choose R : ℕ) : ℝ)) ^ r := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow hdescnn hcast hr
  have hMnn : (0 : ℝ) ≤ ((M.factorial : ℕ) : ℝ) := by positivity
  have hsplit : facEnv r 𝔞 (M + R)
      = ((((M + R).descFactorial R : ℕ) : ℝ)) ^ r * 𝔞 ^ R * facEnv r 𝔞 M := by
    rw [facEnv, facEnv, hfac, Nat.cast_mul, Real.mul_rpow hdescnn hMnn, pow_add]
    ring
  rw [hsplit]
  have hfacpos : 0 < facEnv r 𝔞 M := facEnv_pos (r := r) h𝔞 M
  have hpos : (0 : ℝ) ≤ 𝔞 ^ R * facEnv r 𝔞 M := by positivity
  calc ((((M + R).descFactorial R : ℕ) : ℝ)) ^ r * 𝔞 ^ R * facEnv r 𝔞 M
      = ((((M + R).descFactorial R : ℕ) : ℝ)) ^ r * (𝔞 ^ R * facEnv r 𝔞 M) := by ring
    _ ≤ ((((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * ((((M + R).choose R : ℕ) : ℝ)) ^ r)
        * (𝔞 ^ R * facEnv r 𝔞 M) := mul_le_mul_of_nonneg_right hrpow hpos
    _ = (((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * 𝔞 ^ R
        * ((((M + R).choose R : ℕ) : ℝ)) ^ r * facEnv r 𝔞 M := by ring

/-- **The endpoint remainder is bounded by the envelope at the base index.** -/
theorem norm_coeff_le_of_truncDom_shift {r 𝔞 : ℝ} (hr : 0 ≤ r) (h𝔞 : 0 < 𝔞) {B : ℕ} {cc : ℝ}
    {G : PowerSeries ℂ} {M R : ℕ} (hRM : R ≤ M) (hdom : TruncDom r 𝔞 M B cc G) :
    ‖PowerSeries.coeff (M + R) G‖
      ≤ cc * (((M + R : ℕ) : ℝ) + 1) ^ B * ((((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * 𝔞 ^ R)
        * facEnv r 𝔞 M := by
  have hidx : (M + R) - M = R := by omega
  have hd := hdom (M + R)
  rw [hidx] at hd
  have hchoosepos : 0 < (M + R).choose R := Nat.choose_pos (by omega)
  have hcpos : (0 : ℝ) < ((((M + R).choose R : ℕ) : ℝ)) ^ r := by
    have : (0 : ℝ) < (((M + R).choose R : ℕ) : ℝ) := by exact_mod_cast hchoosepos
    positivity
  have henv := facEnv_add_le_choose (r := r) (𝔞 := 𝔞) hr h𝔞 hRM
  have hccnn : (0 : ℝ) ≤ cc * (((M + R : ℕ) : ℝ) + 1) ^ B := by
    have h0 := hdom 0
    have hlhs : (0 : ℝ) ≤ ‖PowerSeries.coeff 0 G‖ * (((Nat.choose 0 (0 - M) : ℕ) : ℝ)) ^ r := by
      positivity
    have hnn := le_trans hlhs h0
    have hcc : (0 : ℝ) ≤ cc := by simpa using hnn
    positivity
  have hstep : ‖PowerSeries.coeff (M + R) G‖ * ((((M + R).choose R : ℕ) : ℝ)) ^ r
      ≤ (cc * (((M + R : ℕ) : ℝ) + 1) ^ B * ((((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * 𝔞 ^ R)
          * facEnv r 𝔞 M) * ((((M + R).choose R : ℕ) : ℝ)) ^ r := by
    refine le_trans hd ?_
    calc cc * (((M + R : ℕ) : ℝ) + 1) ^ B * facEnv r 𝔞 (M + R)
        ≤ cc * (((M + R : ℕ) : ℝ) + 1) ^ B
          * ((((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * 𝔞 ^ R
            * ((((M + R).choose R : ℕ) : ℝ)) ^ r * facEnv r 𝔞 M) :=
          mul_le_mul_of_nonneg_left henv hccnn
      _ = (cc * (((M + R : ℕ) : ℝ) + 1) ^ B * ((((2 ^ R * R.factorial : ℕ) : ℝ)) ^ r * 𝔞 ^ R)
            * facEnv r 𝔞 M) * ((((M + R).choose R : ℕ) : ℝ)) ^ r := by ring
  exact le_of_mul_le_mul_right hstep hcpos

end

end GaloisForLFunctions.HTGeometry
