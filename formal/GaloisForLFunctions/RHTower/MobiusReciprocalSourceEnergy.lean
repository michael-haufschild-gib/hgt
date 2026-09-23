import GaloisForLFunctions.RHTower.MobiusLaplaceGammaHankelWall

/-!
# Finite reciprocal/original Möbius--Laplace source isometry

The reciprocal pencil at order three uses the same signed coefficients as the original
Laplace pencil. Their weighted energies differ by exactly the factor eight. This
finite identity preserves every off-diagonal arithmetic covariance and provides the
kernel bridge for the high-order reciprocal packet target. No energy-saving estimate
is asserted here.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

private def rup (n : ℕ) : ℝ := ((n + 1 : ℕ) : ℝ)

private def rrate (m n : ℕ) : ℝ := 2 / rup m + 2 / rup n

private theorem rrate_pos (m n : ℕ) : 0 < rrate m n := by
  unfold rrate rup
  positivity

private theorem gamma_three : Real.Gamma 3 = 2 := by
  convert Real.Gamma_nat_eq_factorial 2 using 1 <;> norm_num

private theorem reciprocal_atom (m n : ℕ) :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-(rrate m n * t))) =
      2 / (rrate m n) ^ 3 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ) < 3)
    (rrate_pos m n)
  simpa [show (3:ℝ)-1 = 2 by norm_num, Real.rpow_natCast,
    gamma_three, div_eq_mul_inv, mul_comm] using h

private theorem reciprocal_atom_integrable (m n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-(rrate m n * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (2 : ℝ)) (b := rrate m n)
    (by norm_num) (by norm_num) (rrate_pos m n)
  simpa [Real.rpow_one, Real.rpow_natCast, mul_comm] using h

/-- Finite order-three reciprocal Laplace pencil, with arbitrary real coefficients. -/
def finiteReciprocalPencil (a : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N,
    (a n / rup n ^ 3) * Real.exp (-(2 / rup n * t))

private theorem reciprocal_pair_algebra (m n : ℕ) :
    (1 / rup m ^ 3) * (1 / rup n ^ 3) * (2 / rrate m n ^ 3) =
      1 / (rup m + rup n) ^ 3 / 4 := by
  have hm : rup m ≠ 0 := by unfold rup; positivity
  have hn : rup n ≠ 0 := by unfold rup; positivity
  have hs : rup m + rup n ≠ 0 := by unfold rup; positivity
  have hrr : rrate m n = 2 * (rup m + rup n) / (rup m * rup n) := by
    unfold rrate
    field_simp [hm, hn]
    ring
  rw [hrr]
  field_simp [hm, hn, hs]
  ring

/-- The original and reciprocal finite Laplace energies have the same signed
Gamma--Hankel form, up to the exact factor eight. -/
theorem finite_reciprocal_source_energy
    (a : ℕ → ℝ) (N : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ 2 * finiteRealLaplacePencil a N x ^ 2) =
      8 * (∫ t : ℝ in Ioi 0, t ^ 2 * finiteReciprocalPencil a N t ^ 2) := by
  let S : ℝ := ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
    a m * a n / (rup m + rup n) ^ 3
  have hleft :
      (∫ x : ℝ in Ioi 0, x ^ 2 * finiteRealLaplacePencil a N x ^ 2) =
        2 * S := by
    have h := integral_finiteRealLaplacePencil_sq a N
      (by norm_num : (0:ℝ) < 3)
    have hpow (x : ℝ) : x ^ ((3 : ℝ) - 1) = x ^ (2 : ℕ) := by
      rw [show (3 : ℝ) - 1 = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]
    simp only [hpow] at h
    calc
      _ = finiteGammaHankelEnergy a N 3 := h
      _ = 2 * S := by
        unfold finiteGammaHankelEnergy S
        rw [gamma_three]
        apply congrArg (fun z : ℝ => 2 * z)
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro n hn
        have hden : rup m + rup n = ((m + n + 2 : ℕ) : ℝ) := by
          unfold rup
          push_cast
          ring
        rw [hden]
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast]
  have hfun : (fun t : ℝ => t ^ 2 * finiteReciprocalPencil a N t ^ 2) =
      fun t : ℝ => ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
        ((a m / rup m ^ 3) * (a n / rup n ^ 3)) *
          (t ^ 2 * Real.exp (-(rrate m n * t))) := by
    funext t
    simp only [finiteReciprocalPencil]
    rw [show (∑ n ∈ Finset.range N,
        a n / rup n ^ 3 * Real.exp (-(2 / rup n * t))) ^ 2 =
      (∑ n ∈ Finset.range N,
        a n / rup n ^ 3 * Real.exp (-(2 / rup n * t))) *
      (∑ n ∈ Finset.range N,
        a n / rup n ^ 3 * Real.exp (-(2 / rup n * t))) by ring]
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    calc
      t ^ 2 *
          ((a m / rup m ^ 3 * Real.exp (-(2 / rup m * t))) *
            (a n / rup n ^ 3 * Real.exp (-(2 / rup n * t)))) =
          (a m / rup m ^ 3 * (a n / rup n ^ 3)) *
            (t ^ 2 * (Real.exp (-(2 / rup m * t)) *
              Real.exp (-(2 / rup n * t)))) := by ring
      _ = (a m / rup m ^ 3 * (a n / rup n ^ 3)) *
            (t ^ 2 * Real.exp (-(rrate m n * t))) := by
          rw [← Real.exp_add]
          congr 2
          unfold rrate
          ring
  have hright :
      (∫ t : ℝ in Ioi 0, t ^ 2 * finiteReciprocalPencil a N t ^ 2) =
        S / 4 := by
    rw [hfun]
    have hatom (m n : ℕ) : IntegrableOn
        (fun t : ℝ => (a m / rup m ^ 3 * (a n / rup n ^ 3)) *
          (t ^ 2 * Real.exp (-(rrate m n * t)))) (Ioi 0) :=
      (reciprocal_atom_integrable m n).const_mul _
    calc
      (∫ t : ℝ in Ioi 0, ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (a m / rup m ^ 3 * (a n / rup n ^ 3)) *
            (t ^ 2 * Real.exp (-(rrate m n * t)))) =
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          ∫ t : ℝ in Ioi 0,
            (a m / rup m ^ 3 * (a n / rup n ^ 3)) *
              (t ^ 2 * Real.exp (-(rrate m n * t))) := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro m hm
          rw [integral_finsetSum]
          intro n hn
          exact hatom m n
        · intro m hm
          exact integrable_finsetSum _ fun n hn => hatom m n
      _ = S / 4 := by
        unfold S
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro n hn
        rw [integral_const_mul, reciprocal_atom]
        have hp := reciprocal_pair_algebra m n
        calc
          (a m / rup m ^ 3 * (a n / rup n ^ 3)) *
              (2 / rrate m n ^ 3) =
            (a m * a n) *
              ((1 / rup m ^ 3) * (1 / rup n ^ 3) *
                (2 / rrate m n ^ 3)) := by ring
          _ = (a m * a n) * (1 / (rup m + rup n) ^ 3 / 4) := by rw [hp]
          _ = (a m * a n / (rup m + rup n) ^ 3) / 4 := by ring
  rw [hleft, hright]
  ring

end
end RHTower
