import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalRootedBianchiCofinalNoGo
import GaloisForLFunctions.RHTower.VonMangoldtGammaAffineBoundaryBalance

/-!
# Critical divergence after affine two-boundary Cauchy cancellation

The midpoint Lorentz numerator from Suzuki's marked secant completion is exactly the numerator
of the existing affine two-boundary Cauchy residual.  This makes the residual at the critical
endpoints `a = 1/2`, `w = 0` a canonical candidate for repairing the rooted prime mass.

This file proves that the candidate still diverges.  At a prime `p`, its squared critical mass
dominates `1 / (6400000 * p)`.  Euler's divergence of the prime harmonic series therefore rules
out summability unconditionally.  The obstruction is structural: finitely many inverse powers
of `log p` do not cancel the critical power scale inherited from `Λ(p) / sqrt p`.
-/

namespace RHTower

noncomputable section

/-- Real critical specialization of the affine two-boundary Cauchy residual. -/
def suzukiCriticalAffineCauchyResidual (p : Nat.Primes) : ℝ :=
  let L := Real.log (p : ℝ); -(1 / (4 * L * (L + 1 / 2) * (L - 1 / 2)))

/-- Rooted critical prime mass after the canonical affine two-boundary cancellation. -/
def suzukiCriticalAffineCauchyResidualMass (p : Nat.Primes) : ℝ :=
  suzukiCriticalRootedBianchiPrimeMass p *
    suzukiCriticalAffineCauchyResidual p ^ 2

private theorem half_lt_prime_log (p : Nat.Primes) :
    (1 / 2 : ℝ) < Real.log (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hp hp2
  exact (by nlinarith [Real.log_two_gt_d9] : (1 / 2 : ℝ) < Real.log 2) |>.trans_le hlog

/-- Exact connector to the corpus's affine two-boundary Gamma--Cauchy residual. -/
theorem suzukiCriticalAffineCauchyResidual_eq_twoBoundary
    (p : Nat.Primes) :
    (suzukiCriticalAffineCauchyResidual p : ℂ) =
      twoBoundaryCauchyAffineResidual (1 / 2) 0
        ((Real.log (p : ℝ) : ℝ) : ℂ) := by
  have hL : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (lt_trans (by norm_num) (half_lt_prime_log p))
  have hpR : (1 / 2 : ℝ) + Real.log (p : ℝ) ≠ 0 := by
    exact ne_of_gt (add_pos (by norm_num) (lt_trans (by norm_num) (half_lt_prime_log p)))
  have hp : (1 / 2 : ℂ) + (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    convert Complex.ofReal_ne_zero.mpr hpR using 1
    all_goals norm_num
  have hmR : -(1 / 2 : ℝ) + Real.log (p : ℝ) ≠ 0 := by
    exact ne_of_gt (by nlinarith [half_lt_prime_log p])
  have hm : -(1 / 2 : ℂ) + (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    convert Complex.ofReal_ne_zero.mpr hmR using 1
    all_goals norm_num
  have hLC : (0 : ℂ) + (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr hL
  rw [twoBoundaryCauchyAffineResidual_eq (by norm_num) hLC hp hm]
  have hreal :
      -(1 / (4 * Real.log (p : ℝ) * (Real.log (p : ℝ) + 1 / 2) *
        (Real.log (p : ℝ) - 1 / 2))) =
        ((0 : ℝ) ^ 2 - (1 / 2) ^ 2) /
          (((0 : ℝ) + Real.log (p : ℝ)) *
            (1 / 2 + Real.log (p : ℝ)) *
            (-(1 / 2) + Real.log (p : ℝ))) := by
    field_simp [hL, hpR, hmR]
    ring
  unfold suzukiCriticalAffineCauchyResidual
  dsimp only
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hreal
  convert hc using 1
  all_goals norm_num

private theorem residual_sq_lower (p : Nat.Primes) :
    1 / (64 * Real.log (p : ℝ) ^ 6) ≤
      suzukiCriticalAffineCauchyResidual p ^ 2 := by
  let L := Real.log (p : ℝ)
  have hLhalf : (1 / 2 : ℝ) < L := half_lt_prime_log p
  have hL : 0 < L := lt_trans (by norm_num) hLhalf
  have hplus : L + 1 / 2 ≤ 2 * L := by linarith
  have hminus : 0 ≤ L - 1 / 2 := by linarith
  have hprod1 : L * (L + 1 / 2) ≤ L * (2 * L) :=
    mul_le_mul_of_nonneg_left hplus hL.le
  have hprod2 : L * (L + 1 / 2) * (L - 1 / 2) ≤ L * (2 * L) * L := by
    calc
      L * (L + 1 / 2) * (L - 1 / 2) ≤ L * (2 * L) * (L - 1 / 2) :=
        mul_le_mul_of_nonneg_right hprod1 hminus
      _ ≤ L * (2 * L) * L := by
        exact mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg hL.le (by positivity))
  have hDpos : 0 < 4 * L * (L + 1 / 2) * (L - 1 / 2) := by
    positivity
  have hD : 4 * L * (L + 1 / 2) * (L - 1 / 2) ≤ 8 * L ^ 3 := by
    nlinarith [hprod2]
  have hDsq : (4 * L * (L + 1 / 2) * (L - 1 / 2)) ^ 2 ≤
      (8 * L ^ 3) ^ 2 :=
    pow_le_pow_left₀ hDpos.le hD 2
  unfold suzukiCriticalAffineCauchyResidual
  dsimp only
  change 1 / (64 * L ^ 6) ≤
    (-(1 / (4 * L * (L + 1 / 2) * (L - 1 / 2)))) ^ 2
  rw [neg_sq]
  have hden : 0 < (4 * L * (L + 1 / 2) * (L - 1 / 2)) ^ 2 :=
    sq_pos_of_pos hDpos
  have hupper :
      (4 * L * (L + 1 / 2) * (L - 1 / 2)) ^ 2 ≤ 64 * L ^ 6 := by
    nlinarith [hDsq]
  simpa only [one_div, inv_pow] using one_div_le_one_div_of_le hden hupper

private theorem log_five_le_ten_pow_five_mul_sqrt (p : Nat.Primes) :
    Real.log (p : ℝ) ^ 5 ≤ 10 ^ 5 * Real.sqrt (p : ℝ) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hp0 : 0 ≤ (p : ℝ) := hp.le
  have hlog0 : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.prop.one_lt.le)
  have hlog : Real.log (p : ℝ) ≤ 10 * (p : ℝ) ^ (1 / 10 : ℝ) := by
    have h := Real.log_le_rpow_div hp0 (by norm_num : (0 : ℝ) < 1 / 10)
    convert h using 1
    all_goals ring
  have hpow := pow_le_pow_left₀ hlog0 hlog 5
  calc
    Real.log (p : ℝ) ^ 5 ≤ (10 * (p : ℝ) ^ (1 / 10 : ℝ)) ^ 5 := hpow
    _ = 10 ^ 5 * Real.sqrt (p : ℝ) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_mul_natCast hp0]
      convert (Real.sqrt_eq_rpow (p : ℝ)).symm using 1
      all_goals norm_num

/-- Quantitative harmonic lower bound for the affine-balanced critical mass. -/
theorem scaled_primeHarmonic_le_suzukiCriticalAffineCauchyResidualMass
    (p : Nat.Primes) :
    (1 / 6400000 : ℝ) * (1 / (p : ℝ)) ≤
      suzukiCriticalAffineCauchyResidualMass p := by
  let L := Real.log (p : ℝ)
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  have hL : 0 < L := lt_trans (by norm_num) (half_lt_prime_log p)
  have hres := residual_sq_lower p
  have hmass : suzukiCriticalRootedBianchiPrimeMass p = L / Real.sqrt (p : ℝ) := by
    rw [suzukiCriticalRootedBianchiPrimeMass,
      ArithmeticFunction.vonMangoldt_apply_prime p.prop]
  have hfirst :
      1 / (64 * Real.sqrt (p : ℝ) * L ^ 5) ≤
        suzukiCriticalAffineCauchyResidualMass p := by
    rw [suzukiCriticalAffineCauchyResidualMass, hmass]
    calc
      1 / (64 * Real.sqrt (p : ℝ) * L ^ 5) =
          (L / Real.sqrt (p : ℝ)) * (1 / (64 * L ^ 6)) := by
            field_simp
      _ ≤ (L / Real.sqrt (p : ℝ)) * suzukiCriticalAffineCauchyResidual p ^ 2 := by
        gcongr
  have hlog5 := log_five_le_ten_pow_five_mul_sqrt p
  have hden : 64 * Real.sqrt (p : ℝ) * L ^ 5 ≤ 6400000 * (p : ℝ) := by
    calc
      64 * Real.sqrt (p : ℝ) * L ^ 5 ≤
          64 * Real.sqrt (p : ℝ) * (10 ^ 5 * Real.sqrt (p : ℝ)) := by
            gcongr
      _ = 6400000 * (p : ℝ) := by
        calc
          64 * Real.sqrt (p : ℝ) * (10 ^ 5 * Real.sqrt (p : ℝ)) =
              64 * 10 ^ 5 *
                (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) := by ring
          _ = 6400000 * (p : ℝ) := by
            rw [Real.mul_self_sqrt hp.le]
            norm_num
  have hdenpos : 0 < 64 * Real.sqrt (p : ℝ) * L ^ 5 := by positivity
  calc
    (1 / 6400000 : ℝ) * (1 / (p : ℝ)) = 1 / (6400000 * (p : ℝ)) := by ring
    _ ≤ 1 / (64 * Real.sqrt (p : ℝ) * L ^ 5) :=
      one_div_le_one_div_of_le hdenpos hden
    _ ≤ suzukiCriticalAffineCauchyResidualMass p := hfirst

/-- The canonical affine two-boundary repair remains nonsummable at Suzuki's critical mass. -/
theorem not_summable_suzukiCriticalAffineCauchyResidualMass :
    ¬ Summable suzukiCriticalAffineCauchyResidualMass := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes =>
      (1 / 6400000 : ℝ) * (1 / (p : ℝ))) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · exact scaled_primeHarmonic_le_suzukiCriticalAffineCauchyResidualMass
    · exact hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (1 / 6400000 : ℝ) ≠ 0)).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

end

end RHTower
