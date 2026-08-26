import GaloisForLFunctions.RHTower.Sieve.FibreThirdPowerBound

/-!
# Uniform conditions for third-derivative Vaughan fibres

A dyadic prime block, near-diagonal shift bound, and one top-scale curvature inequality discharge
all fibrewise hypotheses used by the third-derivative Type I estimate.
-/

namespace RHTower.Sieve

noncomputable section

theorem thirdDerivative_fibre_conditions {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B K : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A)
    (hKA : K ≤ A) (h8 : 8 * r ≤ (A : ℝ))
    (hcurv : T * r * (K : ℝ) ^ 3 ≤ 72 * Real.pi * (A : ℝ) ^ 4) :
    ∀ b ∈ Finset.Icc 1 K,
      ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤ ((A - 1) / b + 1)
        ∧ r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda3 T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1 := by
  intro b hbmem
  rw [Finset.mem_Icc] at hbmem
  obtain ⟨hb1, hbK⟩ := hbmem
  have hbA : b ≤ A := le_trans hbK hKA
  have hspan : ((B - 1) / b + 1) - ((A - 1) / b + 1) - 1 ≤
      ((A - 1) / b + 1) := by
    have hAceil : A ≤ (((A - 1) / b + 1) * b) := by
      have hlt : A - 1 < (((A - 1) / b + 1) * b) := by
        have := (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).mp
          (Nat.lt_succ_self ((A - 1) / b))
        simpa [mul_comm] using this
      omega
    have hBceil : (B - 1) / b + 1 ≤ 2 * ((A - 1) / b + 1) := by
      have hlt : B - 1 < (2 * ((A - 1) / b + 1)) * b := by
        have htwice : 2 * A ≤ 2 * (((A - 1) / b + 1) * b) :=
          Nat.mul_le_mul_left 2 hAceil
        have hBA' : B ≤ 2 * (((A - 1) / b + 1) * b) := le_trans hBA htwice
        have heq : 2 * (((A - 1) / b + 1) * b) =
            (2 * ((A - 1) / b + 1)) * b := by simp [mul_assoc]
        rw [heq] at hBA'
        omega
      have hdiv : (B - 1) / b < 2 * ((A - 1) / b + 1) :=
        (Nat.div_lt_iff_lt_mul (by omega : 0 < b)).mpr hlt
      omega
    omega
  have hrA : r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ) := by
    have hb0 : (0 : ℝ) < b := by exact_mod_cast hb1
    have hlow := le_cast_fibre_low hA hb1
    have hrA' : r ≤ (A : ℝ) := by nlinarith
    exact le_trans (div_le_div_of_nonneg_right hrA' hb0.le) hlow
  have hlamUp := nearDiagonalLambda3_fibre_le hT hr hA hb1
  have hbcast : (b : ℝ) ≤ K := by exact_mod_cast hbK
  have hbpow : (b : ℝ) ^ 3 ≤ (K : ℝ) ^ 3 := by gcongr
  have hnum : T * r * (b : ℝ) ^ 3 ≤ T * r * (K : ℝ) ^ 3 := by
    exact mul_le_mul_of_nonneg_left hbpow (by positivity)
  have hfrac : T * r * (b : ℝ) ^ 3 / (72 * Real.pi * (A : ℝ) ^ 4) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact le_trans hnum hcurv
  exact ⟨hspan, hrA, le_trans hlamUp hfrac⟩

end

end RHTower.Sieve
