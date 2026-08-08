import GaloisForLFunctions.HTGeometry.FactorialSlopeEnvelope
import GaloisForLFunctions.HTGeometry.FacEnvShiftBound
import GaloisForLFunctions.HTGeometry.PowerSeriesJetCoeff

/-!
# The jets of a factorial-slope series are envelope-dominated

Each formal derivative of a factorial-slope series has coefficients dominated by the same factorial
envelope, up to a fixed polynomial weight:

`‖[X^n] F^{(j)}‖ ≤ K (n+1)^B · facEnv r 𝔞 n`.

Two shifts are involved and both cost only polynomial factors.  The descending-factorial weight of
the jet is at most `(n+j)^j ≤ ((n+1)(j+1))^j`, and moving the envelope from `n+j` back to `n` costs
`((n+j)_j)^r · 𝔞^j`, bounded the same way after rounding the exponent `j·r` up to an integer.

This is the hypothesis of the endpoint remainder estimate: it is what allows the remainder of an
endpoint expansion to be bounded against the envelope at the base index.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- The shifted index is at most the product of the two shifted factors. -/
theorem add_le_mul_succ (n j : ℕ) : n + j ≤ (n + 1) * (j + 1) := by
  nlinarith [Nat.zero_le (n * j)]

/-- **Moving the envelope back across a fixed shift costs a polynomial factor.** -/
theorem facEnv_shift_le {r 𝔞 : ℝ} (hr : 0 ≤ r) (h𝔞 : 0 < 𝔞) (n j : ℕ) :
    facEnv r 𝔞 (n + j)
      ≤ (((n : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊) * (((j : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊) * 𝔞 ^ j))
        * facEnv r 𝔞 n := by
  have hfac := factorial_add_eq_descFactorial_mul n j
  have hdescnat : (n + j).descFactorial j ≤ ((n + 1) * (j + 1)) ^ j :=
    le_trans (Nat.descFactorial_le_pow _ _) (Nat.pow_le_pow_left (add_le_mul_succ n j) j)
  have hbase : (1 : ℝ) ≤ ((n : ℝ) + 1) * ((j : ℝ) + 1) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    nlinarith
  have hdesc : ((((n + j).descFactorial j : ℕ)) : ℝ) ≤ (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j := by
    have := hdescnat
    have hcast : ((((n + 1) * (j + 1)) ^ j : ℕ) : ℝ) = (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j := by
      push_cast
      ring
    rw [← hcast]
    exact_mod_cast this
  -- the rpow of the descending factorial
  have hrp : ((((n + j).descFactorial j : ℕ)) : ℝ) ^ r
      ≤ ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j) ^ r :=
    Real.rpow_le_rpow (by positivity) hdesc hr
  have hexp : ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j) ^ r
      = (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ ((j : ℝ) * r) := by
    rw [← Real.rpow_natCast (((n : ℝ) + 1) * ((j : ℝ) + 1)) j, ← Real.rpow_mul (by linarith)]
  have hceil : (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ ((j : ℝ) * r)
      ≤ (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ (⌈(j : ℝ) * r⌉₊) := by
    rw [← Real.rpow_natCast (((n : ℝ) + 1) * ((j : ℝ) + 1)) (⌈(j : ℝ) * r⌉₊)]
    exact Real.rpow_le_rpow_of_exponent_le hbase (Nat.le_ceil _)
  have hall : ((((n + j).descFactorial j : ℕ)) : ℝ) ^ r
      ≤ ((n : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊) * ((j : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊) := by
    refine le_trans hrp (le_trans (le_of_eq hexp) (le_trans hceil ?_))
    rw [mul_pow]
  have hnn : (0 : ℝ) ≤ ((n.factorial : ℕ) : ℝ) := by positivity
  have hdnn : (0 : ℝ) ≤ ((((n + j).descFactorial j : ℕ)) : ℝ) := by positivity
  have hsplit : facEnv r 𝔞 (n + j)
      = ((((n + j).descFactorial j : ℕ)) : ℝ) ^ r * 𝔞 ^ j * facEnv r 𝔞 n := by
    rw [facEnv, facEnv, hfac, Nat.cast_mul, Real.mul_rpow hdnn hnn, pow_add]
    ring
  rw [hsplit]
  have hpos : (0 : ℝ) ≤ 𝔞 ^ j * facEnv r 𝔞 n := by
    have := facEnv_pos (r := r) h𝔞 n
    positivity
  calc ((((n + j).descFactorial j : ℕ)) : ℝ) ^ r * 𝔞 ^ j * facEnv r 𝔞 n
      = ((((n + j).descFactorial j : ℕ)) : ℝ) ^ r * (𝔞 ^ j * facEnv r 𝔞 n) := by ring
    _ ≤ (((n : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊) * ((j : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊))
        * (𝔞 ^ j * facEnv r 𝔞 n) := mul_le_mul_of_nonneg_right hall hpos
    _ = (((n : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊) * (((j : ℝ) + 1) ^ (⌈(j : ℝ) * r⌉₊) * 𝔞 ^ j))
        * facEnv r 𝔞 n := by ring

/-! ## The jet coefficient envelope -/

/-- **The coefficients of a fixed jet are envelope-dominated.** -/
theorem exists_jet_coeff_envelope (hyp : FactorialSlope a α Λ Cc c) (j : ℕ) :
    ∃ (B : ℕ) (K : ℝ), 0 ≤ K ∧ ∀ n : ℕ,
      ‖PowerSeries.coeff n ((⇑(d⁄dX ℂ))^[j] (PowerSeries.mk a))‖
        ≤ K * ((n : ℝ) + 1) ^ B * facEnv α.re (slopeRatio α Λ) n := by
  classical
  obtain ⟨B₁, K₁, hK₁, henv⟩ := exists_slope_envelope hyp
  have hr : (0 : ℝ) ≤ α.re := le_of_lt hyp.re_pos
  have h𝔞 : 0 < slopeRatio α Λ := slopeRatio_pos hyp.lam_ne
  set D : ℕ := ⌈(j : ℝ) * α.re⌉₊ with hD
  set B : ℕ := B₁ + D + j with hB
  set K : ℝ := max ‖a 0‖ (K₁ * (((j : ℝ) + 1) ^ B * slopeRatio α Λ ^ j)) with hK
  have hKnn : 0 ≤ K := le_trans (norm_nonneg _) (le_max_left _ _)
  refine ⟨B, K, hKnn, fun n => ?_⟩
  have hcoeff : PowerSeries.coeff n ((⇑(d⁄dX ℂ))^[j] (PowerSeries.mk a))
      = a (n + j) * ((((n + j).descFactorial j : ℕ)) : ℂ) := by
    rw [coeff_iterate_derivative, PowerSeries.coeff_mk]
  have hfacpos : 0 < facEnv α.re (slopeRatio α Λ) n := facEnv_pos (r := α.re) h𝔞 n
  have hbase : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rcases Nat.eq_zero_or_pos (n + j) with hz | hpos
  · -- the only index below one
    have hn0 : n = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hn0
    subst hj0
    rw [hcoeff]
    simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.zero_add]
    have hKle : ‖a 0‖ ≤ K := le_max_left _ _
    have hfac0 : facEnv α.re (slopeRatio α Λ) 0 = 1 := facEnv_zero _ _
    simp only [hfac0, Nat.cast_zero, zero_add, one_pow, mul_one]
    exact hKle
  · -- the generic index
    have hone : 1 ≤ n + j := hpos
    obtain ⟨hup, -⟩ := henv (n + j) hone
    have hmulle : ((n : ℝ) + (j : ℝ)) ≤ ((n : ℝ) + 1) * ((j : ℝ) + 1) := by
      have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h2 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      nlinarith
    have hcast : (((n + j : ℕ)) : ℝ) = (n : ℝ) + (j : ℝ) := by push_cast; ring
    have hpow1 : (((n + j : ℕ)) : ℝ) ^ B₁ ≤ (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ B₁ := by
      rw [hcast]
      exact pow_le_pow_left₀ (by positivity) hmulle B₁
    have hdescnat : (n + j).descFactorial j ≤ ((n + 1) * (j + 1)) ^ j :=
      le_trans (Nat.descFactorial_le_pow _ _) (Nat.pow_le_pow_left (add_le_mul_succ n j) j)
    have hdesc : ((((n + j).descFactorial j : ℕ)) : ℝ) ≤ (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j := by
      have hc : ((((n + 1) * (j + 1)) ^ j : ℕ) : ℝ) = (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j := by
        push_cast
        ring
      rw [← hc]
      exact_mod_cast hdescnat
    have hshift := facEnv_shift_le (r := α.re) (𝔞 := slopeRatio α Λ) hr h𝔞 n j
    -- assemble
    rw [hcoeff, norm_mul, Complex.norm_natCast]
    have hstep1 : ‖a (n + j)‖ * ((((n + j).descFactorial j : ℕ)) : ℝ)
        ≤ (K₁ * (((n + j : ℕ)) : ℝ) ^ B₁ * facEnv α.re (slopeRatio α Λ) (n + j))
          * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j) := by
      refine mul_le_mul hup hdesc (by positivity) ?_
      have := facEnv_pos (r := α.re) h𝔞 (n + j)
      positivity
    refine le_trans hstep1 ?_
    have hstep2 : (K₁ * (((n + j : ℕ)) : ℝ) ^ B₁ * facEnv α.re (slopeRatio α Λ) (n + j))
        * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j)
        ≤ (K₁ * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ B₁)
            * ((((n : ℝ) + 1) ^ D * ((((j : ℝ) + 1) ^ D * slopeRatio α Λ ^ j)))
              * facEnv α.re (slopeRatio α Λ) n))
          * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j) := by
      have hmulnn : (0 : ℝ) ≤ (((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j := by positivity
      refine mul_le_mul_of_nonneg_right ?_ hmulnn
      have hA : K₁ * (((n + j : ℕ)) : ℝ) ^ B₁ ≤ K₁ * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ B₁) :=
        mul_le_mul_of_nonneg_left hpow1 (le_of_lt hK₁)
      have hnn : (0 : ℝ) ≤ K₁ * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ B₁) := by positivity
      calc K₁ * (((n + j : ℕ)) : ℝ) ^ B₁ * facEnv α.re (slopeRatio α Λ) (n + j)
          ≤ K₁ * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ B₁)
            * facEnv α.re (slopeRatio α Λ) (n + j) :=
            mul_le_mul_of_nonneg_right hA (le_of_lt (facEnv_pos (r := α.re) h𝔞 (n + j)))
        _ ≤ K₁ * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ B₁)
            * ((((n : ℝ) + 1) ^ D * ((((j : ℝ) + 1) ^ D * slopeRatio α Λ ^ j)))
              * facEnv α.re (slopeRatio α Λ) n) := mul_le_mul_of_nonneg_left hshift hnn
    refine le_trans hstep2 ?_
    have hexpand : (K₁ * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ B₁)
          * ((((n : ℝ) + 1) ^ D * ((((j : ℝ) + 1) ^ D * slopeRatio α Λ ^ j)))
            * facEnv α.re (slopeRatio α Λ) n))
        * ((((n : ℝ) + 1) * ((j : ℝ) + 1)) ^ j)
        = (K₁ * (((j : ℝ) + 1) ^ B * slopeRatio α Λ ^ j))
          * ((n : ℝ) + 1) ^ B * facEnv α.re (slopeRatio α Λ) n := by
      rw [hB, mul_pow, mul_pow]
      ring
    rw [hexpand]
    have hKle : K₁ * (((j : ℝ) + 1) ^ B * slopeRatio α Λ ^ j) ≤ K := le_max_right _ _
    have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ B * facEnv α.re (slopeRatio α Λ) n := by positivity
    nlinarith [hKle, hnn]

end

end GaloisForLFunctions.HTGeometry
