import GaloisForLFunctions.RHTower.NearDiagonalPhaseCurvature

/-!
# Stability of the near-diagonal phase against the pure reciprocal phase

The phase `F_r(u) = (T/2π)·log(1 + r/u)` and its first two derivatives are relative `O(r/u)`
perturbations of the pure reciprocal phase `X/u` with `X = Tr/2π`.  Each comparison is a rational
identity in `r` and `u` followed by one elementary logarithmic bound, so it holds with explicit
absolute constants and no asymptotics.  This is what transfers a derivative test proved for `e(X/u)`
to `e(F_r(u))`.
-/

namespace RHTower.Sieve

open Real

noncomputable section

/-- The reciprocal parameter of the near-diagonal phase. -/
def reciprocalParam (T r : ℝ) : ℝ := T * r / (2 * Real.pi)

/-- `|log(1+z) − z| ≤ z²` for every `z ≥ 0`. -/
theorem abs_log_one_add_sub_le_sq {z : ℝ} (hz0 : 0 ≤ z) :
    |Real.log (1 + z) - z| ≤ z ^ (2 : ℕ) := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  have hupper : Real.log (1 + z) ≤ z := by
    have h := Real.log_le_sub_one_of_pos h1z
    linarith
  have hlower : z - z ^ (2 : ℕ) ≤ Real.log (1 + z) := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 / (1 + z) by positivity)
    have hid : Real.log (1 / (1 + z)) = -Real.log (1 + z) := by
      rw [Real.log_div (by norm_num) h1z.ne', Real.log_one]
      ring
    rw [hid] at h
    have hstep : z / (1 + z) ≤ Real.log (1 + z) := by
      have hid2 : (1 : ℝ) / (1 + z) - 1 = -(z / (1 + z)) := by field_simp; ring
      rw [hid2] at h
      linarith
    have hfrac : z - z ^ (2 : ℕ) ≤ z / (1 + z) := by
      rw [le_div_iff₀ h1z]
      nlinarith [hz0]
    linarith
  rw [abs_le]
  constructor <;> nlinarith [hupper, hlower, sq_nonneg z]

/-- **Order zero.**  The phase is a relative `O(r/u)` perturbation of `X/u`. -/
theorem abs_nearDiagonalPhase_sub_le {T r u ε : ℝ} (hT : 0 ≤ T) (hr : 0 < r) (hu : 0 < u)
    (hε : r / u ≤ ε) :
    |nearDiagonalPhase T r u - reciprocalParam T r / u| ≤ ε * (reciprocalParam T r / u) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set z : ℝ := r / u with hz
  have hz0 : (0 : ℝ) < z := by rw [hz]; positivity
  have hbase := abs_log_one_add_sub_le_sq hz0.le
  have hid : nearDiagonalPhase T r u - reciprocalParam T r / u
      = (T / (2 * Real.pi)) * (Real.log (1 + z) - z) := by
    rw [nearDiagonalPhase, reciprocalParam, hz]
    field_simp
  rw [hid, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ T / (2 * Real.pi))]
  have hXu : reciprocalParam T r / u = (T / (2 * Real.pi)) * z := by
    rw [reciprocalParam, hz]
    field_simp
  rw [hXu]
  have hstep : |Real.log (1 + z) - z| ≤ ε * z := by
    refine hbase.trans ?_
    nlinarith [hz0.le, hε]
  calc T / (2 * Real.pi) * |Real.log (1 + z) - z|
      ≤ T / (2 * Real.pi) * (ε * z) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ε * (T / (2 * Real.pi) * z) := by ring

/-- **Order one.**  The first derivative is a relative `O(r/u)` perturbation of `−X/u²`. -/
theorem abs_nearDiagonalPhaseD1_add_le {T r u ε : ℝ} (hT : 0 ≤ T) (hr : 0 < r) (hu : 0 < u)
    (hε : r / u ≤ ε) :
    |nearDiagonalPhaseD1 T r u + reciprocalParam T r / u ^ (2 : ℕ)|
      ≤ ε * (reciprocalParam T r / u ^ (2 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hur : (0 : ℝ) < u + r := by linarith
  have hid : nearDiagonalPhaseD1 T r u + reciprocalParam T r / u ^ (2 : ℕ)
      = (reciprocalParam T r / u ^ (2 : ℕ)) * (r / (u + r)) := by
    rw [nearDiagonalPhaseD1, reciprocalParam]
    field_simp
    ring
  rw [hid, abs_mul]
  have hX : (0 : ℝ) ≤ reciprocalParam T r / u ^ (2 : ℕ) := by
    rw [reciprocalParam]; positivity
  rw [abs_of_nonneg hX, abs_of_nonneg (by positivity : (0:ℝ) ≤ r / (u + r))]
  have hmono : r / (u + r) ≤ r / u := div_le_div_of_nonneg_left hr.le hu (by linarith)
  calc (reciprocalParam T r / u ^ (2 : ℕ)) * (r / (u + r))
      ≤ (reciprocalParam T r / u ^ (2 : ℕ)) * ε :=
        mul_le_mul_of_nonneg_left (le_trans hmono hε) hX
    _ = ε * (reciprocalParam T r / u ^ (2 : ℕ)) := by ring

/-- **Order two.**  The second derivative is a relative `O(r/u)` perturbation of `2X/u³`. -/
theorem abs_nearDiagonalPhaseD2_sub_le {T r u ε : ℝ} (hT : 0 ≤ T) (hr : 0 < r) (hu : 0 < u)
    (hε : r / u ≤ ε) :
    |nearDiagonalPhaseD2 T r u - 2 * reciprocalParam T r / u ^ (3 : ℕ)|
      ≤ 3 * ε * (reciprocalParam T r / u ^ (3 : ℕ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hur : (0 : ℝ) < u + r := by linarith
  have hX : (0 : ℝ) ≤ reciprocalParam T r / u ^ (3 : ℕ) := by
    rw [reciprocalParam]; positivity
  have hid : nearDiagonalPhaseD2 T r u - 2 * reciprocalParam T r / u ^ (3 : ℕ)
      = -((reciprocalParam T r / u ^ (3 : ℕ)) * (r * (3 * u + 2 * r) / (u + r) ^ (2 : ℕ))) := by
    rw [nearDiagonalPhaseD2, reciprocalParam]
    field_simp
    ring
  rw [hid, abs_neg, abs_mul, abs_of_nonneg hX,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ r * (3 * u + 2 * r) / (u + r) ^ (2 : ℕ))]
  have hfac : r * (3 * u + 2 * r) / (u + r) ^ (2 : ℕ) ≤ 3 * (r / u) := by
    rw [div_le_iff₀ (by positivity)]
    have hexp : 3 * (r / u) * (u + r) ^ (2 : ℕ) = 3 * r * (u + r) ^ (2 : ℕ) / u := by ring
    rw [hexp, le_div_iff₀ hu]
    nlinarith [hr.le, hu.le, sq_nonneg r, sq_nonneg u, mul_pos hr hu]
  calc (reciprocalParam T r / u ^ (3 : ℕ)) * (r * (3 * u + 2 * r) / (u + r) ^ (2 : ℕ))
      ≤ (reciprocalParam T r / u ^ (3 : ℕ)) * (3 * (r / u)) := mul_le_mul_of_nonneg_left hfac hX
    _ ≤ (reciprocalParam T r / u ^ (3 : ℕ)) * (3 * ε) :=
        mul_le_mul_of_nonneg_left (by linarith) hX
    _ = 3 * ε * (reciprocalParam T r / u ^ (3 : ℕ)) := by ring

end

end RHTower.Sieve
