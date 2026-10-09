import GaloisForLFunctions.RHTower.MobiusRieszSquareSourceQuadrature
import GaloisForLFunctions.RHTower.FermiNymanLogMobiusHead

/-!
The square-sampled Chebyshev remainder is an exact signed logarithmic Mobius
action on quadratic residue prefixes, together with its scalar counterterm.
Each residue prefix splits into complete periods and one incomplete period.
The incomplete periods from moduli at most `D` cost at most `D² log D`,
uniformly in the sampling cutoff. In particular they fit the critical `N²`
budget whenever `D³ ≤ N²`.

The complete periods, remaining moduli, and scalar counterterm still require
joint cancellation. This file does not prove the RH-equivalent upper bound.
-/

open scoped BigOperators
open Finset ArithmeticFunction

namespace RHTower

/-- Sum of the least nonnegative square residues along the first `N` indices. -/
noncomputable def quadraticResiduePrefix (N d : ℕ) : ℝ :=
  ∑ s ∈ range N, ((s ^ 2 % d : ℕ) : ℝ)

/-- Signed contribution of incomplete quadratic-residue periods below a modulus cutoff. -/
noncomputable def logMobiusQuadraticRemainderAction (N D : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 D, (((moebius d : ℤ) : ℝ) * Real.log d / d) *
    quadraticResiduePrefix (N % d) d

/-- Exact full-period and remainder decomposition, also valid for modulus zero. -/
theorem quadraticResiduePrefix_period_decomposition (N d : ℕ) :
    quadraticResiduePrefix N d =
      (N / d : ℕ) * quadraticResiduePrefix d d + quadraticResiduePrefix (N % d) d := by
  have hblock (q r : ℕ) : quadraticResiduePrefix (d * q + r) d =
      quadraticResiduePrefix (d * q) d + quadraticResiduePrefix r d := by
    unfold quadraticResiduePrefix
    rw [sum_range_add]
    congr 1
    apply sum_congr rfl
    intro s _
    simp [Nat.pow_mod, Nat.add_mod]
  have hmul (q : ℕ) : quadraticResiduePrefix (d * q) d =
      (q : ℝ) * quadraticResiduePrefix d d := by
    induction q with
    | zero => simp [quadraticResiduePrefix]
    | succ q ih =>
      rw [Nat.mul_succ, hblock, ih]
      push_cast
      ring
  have hN : N = d * (N / d) + N % d := by
    have := Nat.mod_add_div N d
    omega
  calc
    _ = quadraticResiduePrefix (d * (N / d) + N % d) d := by rw [← hN]
    _ = _ := by rw [hblock, hmul]

/-- The elementary residue range bound. -/
theorem quadraticResiduePrefix_nonneg_le (N : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ quadraticResiduePrefix N d ∧ quadraticResiduePrefix N d ≤ (N : ℝ) * d := by
  constructor
  · exact sum_nonneg fun _ _ => Nat.cast_nonneg _
  · calc
      _ ≤ ∑ _s ∈ range N, (d : ℝ) := by
        apply sum_le_sum
        intro s _
        exact_mod_cast (Nat.mod_lt (s ^ 2) (by omega : 0 < d)).le
      _ = _ := by simp

/-- An incomplete period has at most quadratic mass in its modulus. -/
theorem quadraticResiduePrefix_remainder_le {N d : ℕ} (hd : 1 ≤ d) :
    0 ≤ quadraticResiduePrefix (N % d) d ∧
      quadraticResiduePrefix (N % d) d ≤ (d : ℝ) ^ 2 := by
  have h := quadraticResiduePrefix_nonneg_le (N % d) hd
  have hmod : ((N % d : ℕ) : ℝ) ≤ d := by
    exact_mod_cast (Nat.mod_lt N (by omega : 0 < d)).le
  exact ⟨h.1, h.2.trans (by nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])⟩

/-- Unconditional incomplete-period bound, uniform in the square-sampling aperture. -/
theorem abs_logMobiusQuadraticRemainderAction_le (N : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    |logMobiusQuadraticRemainderAction N D| ≤ (D : ℝ) ^ 2 * Real.log D := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlogD := Real.log_nonneg hD1
  calc
    _ ≤ ∑ d ∈ Icc 1 D, |(((moebius d : ℤ) : ℝ) * Real.log d / d) *
        quadraticResiduePrefix (N % d) d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Icc 1 D, (D : ℝ) * Real.log D := by
      apply sum_le_sum
      intro d hd
      have hd' := mem_Icc.mp hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd'.1
      have hdD : (d : ℝ) ≤ D := by exact_mod_cast hd'.2
      have hlogd := Real.log_nonneg hd1
      have hlog := Real.log_le_log hdpos hdD
      have hmu : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      have hv := quadraticResiduePrefix_remainder_le (N := N) hd'.1
      simp only [abs_mul, abs_div, abs_of_pos hdpos, abs_of_nonneg hlogd,
        abs_of_nonneg hv.1]
      calc
        _ ≤ (1 * Real.log d / d) * (d : ℝ) ^ 2 := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hmu hlogd) hdpos.le
          · exact hv.2
          · exact hv.1
          · positivity
        _ = (d : ℝ) * Real.log d := by field_simp
        _ ≤ _ := mul_le_mul hdD hlog hlogd (Nat.cast_nonneg _)
    _ = _ := by simp; ring

/-- Small-modulus incomplete periods already fit the critical quadratic budget. -/
theorem abs_logMobiusQuadraticRemainderAction_le_aperture_sq {N D : ℕ}
    (hD : 1 ≤ D) (hDN : D ^ 3 ≤ N ^ 2) :
    |logMobiusQuadraticRemainderAction N D| ≤ (N : ℝ) ^ 2 := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hlog : Real.log (D : ℝ) ≤ D := by
    linarith [Real.log_le_sub_one_of_pos hDpos]
  calc
    _ ≤ (D : ℝ) ^ 2 * Real.log D := abs_logMobiusQuadraticRemainderAction_le N hD
    _ ≤ (D : ℝ) ^ 2 * D := mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
    _ = (D : ℝ) ^ 3 := by ring
    _ ≤ _ := by exact_mod_cast hDN

private theorem nat_floor_logMobius (n A : ℕ) (hnA : n ≤ A) :
    (∑ d ∈ Icc 1 A, ((moebius d : ℤ) : ℝ) * Real.log d * ((n / d : ℕ) : ℝ)) =
      -chebyshevPsi n := by
  have h := sum_moebius_log_mul_floor A (x := (n : ℝ)) (by positivity)
    (by simpa using hnA)
  simp_rw [real_floor_div_eq_nat_div _ (by positivity : (0 : ℝ) ≤ n),
    Nat.floor_natCast] at h
  simpa only [chebyshevPsi_eq_psi] using h

private theorem psiRemainder_eq_logMobiusResidues {n A : ℕ} (hnA : n ≤ A) :
    psiRemainder n =
      (∑ d ∈ Icc 1 A, (((moebius d : ℤ) : ℝ) * Real.log d / d) * ((n % d : ℕ) : ℝ)) -
        (1 + ∑ d ∈ Icc 1 A, ((moebius d : ℤ) : ℝ) * Real.log d / d) * n := by
  have h := nat_floor_logMobius n A hnA
  have hterm (d : ℕ) (hd : d ∈ Icc 1 A) :
      ((moebius d : ℤ) : ℝ) * Real.log d * ((n / d : ℕ) : ℝ) =
        (((moebius d : ℤ) : ℝ) * Real.log d / d) * n -
          (((moebius d : ℤ) : ℝ) * Real.log d / d) * ((n % d : ℕ) : ℝ) := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
    have hmod : ((n % d : ℕ) : ℝ) + (d : ℝ) * ((n / d : ℕ) : ℝ) = n := by
      exact_mod_cast Nat.mod_add_div n d
    have hquot : ((n / d : ℕ) : ℝ) = ((n : ℝ) - ((n % d : ℕ) : ℝ)) / d := by
      apply (eq_div_iff hdpos.ne').mpr
      nlinarith
    rw [hquot]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul] at h
  unfold psiRemainder
  linarith

/-- Exact arithmetic square-source identity; the scalar counterterm stays coupled. -/
theorem psiRemainder_squareSum_eq_quadraticResidues {N : ℕ} (hN : 1 ≤ N) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      (∑ d ∈ Icc 1 (N ^ 2), (((moebius d : ℤ) : ℝ) * Real.log d / d) *
        quadraticResiduePrefix N d) -
      (1 + ∑ d ∈ Icc 1 (N ^ 2), ((moebius d : ℤ) : ℝ) * Real.log d / d) *
        ∑ s ∈ range N, (s : ℝ) ^ 2 := by
  have hzero : psiRemainder 0 = 0 := by simp [psiRemainder, chebyshevPsi]
  rw [sum_Ico_eq_sub _ hN]
  simp only [sum_range_one, zero_pow (by omega : 2 ≠ 0), hzero, sub_zero]
  have hterm (s : ℕ) (hs : s ∈ range N) :=
    psiRemainder_eq_logMobiusResidues (n := s ^ 2) (A := N ^ 2)
      (by have := mem_range.mp hs; nlinarith)
  rw [sum_congr rfl hterm, sum_sub_distrib, sum_comm]
  simp only [Nat.cast_pow]
  rw [← mul_sum]
  congr 1
  apply sum_congr rfl
  intro d _
  rw [← mul_sum]
  rfl

/-- Complete residue periods, incomplete periods, and the scalar counterterm reconstruct
the actual Chebyshev square sum without estimates or sign removal. -/
theorem psiRemainder_squareSum_eq_periods_add_remainders {N : ℕ} (hN : 1 ≤ N) :
    (∑ s ∈ Ico 1 N, psiRemainder (s ^ 2)) =
      (∑ d ∈ Icc 1 (N ^ 2), (((moebius d : ℤ) : ℝ) * Real.log d / d) *
        ((N / d : ℕ) * quadraticResiduePrefix d d)) +
      logMobiusQuadraticRemainderAction N (N ^ 2) -
      (1 + ∑ d ∈ Icc 1 (N ^ 2), ((moebius d : ℤ) : ℝ) * Real.log d / d) *
        ∑ s ∈ range N, (s : ℝ) ^ 2 := by
  rw [psiRemainder_squareSum_eq_quadraticResidues hN]
  simp_rw [quadraticResiduePrefix_period_decomposition N, mul_add]
  rw [sum_add_distrib]
  rfl

end RHTower
