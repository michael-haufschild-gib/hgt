import GaloisForLFunctions.RHTower.PrimePowerSumBound
import GaloisForLFunctions.RHTower.Sieve.Mertens

open Filter Topology

namespace RHTower

noncomputable section

/-- One absolute constant for the prime-log shell estimate, uniform in the exponent. -/
def uniformPrimeLogRpowConst : ℝ :=
  4 * Classical.choose exists_chebyshevTheta_le_linear / Real.log 2

private theorem thetaLinearConst_pos :
    0 < Classical.choose exists_chebyshevTheta_le_linear :=
  (Classical.choose_spec exists_chebyshevTheta_le_linear).1

private theorem theta_le_linear (x : ℝ) (hx : 1 ≤ x) :
    Chebyshev.theta x ≤ Classical.choose exists_chebyshevTheta_le_linear * x :=
  (Classical.choose_spec exists_chebyshevTheta_le_linear).2 x hx

theorem uniformPrimeLogRpowConst_pos : 0 < uniformPrimeLogRpowConst := by
  rw [uniformPrimeLogRpowConst]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos (mul_pos (by norm_num) thetaLinearConst_pos) hlog

private theorem half_mul_le_one_sub_two_rpow_neg {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    a * Real.log 2 / 2 ≤ 1 - (2 : ℝ) ^ (-a) := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hu0 : 0 < a * Real.log 2 := mul_pos ha0 hlog0
  have hu1 : a * Real.log 2 ≤ 1 := by nlinarith
  have hinv : Real.exp (-(a * Real.log 2)) ≤ (1 + a * Real.log 2)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (by linarith)).2 (by
      simpa [add_comm] using Real.add_one_le_exp (a * Real.log 2))
  have hfrac : a * Real.log 2 / 2 ≤ 1 - (1 + a * Real.log 2)⁻¹ := by
    have hpos : 0 < 1 + a * Real.log 2 := by linarith
    rw [inv_eq_one_div]
    field_simp [ne_of_gt hpos]
    nlinarith
  have hrpow : (2 : ℝ) ^ (-a) = Real.exp (-(a * Real.log 2)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hrpow]
  linarith

/-- Uniform Chebyshev-shell bound for the subcritical prime-log power sum. -/
theorem primeLogSum_rpow_sub_one_le_uniform {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    : ∀ Y : ℝ, 0 ≤ Y →
      primeLogSum (fun t : ℝ => t ^ (a - 1)) 0 Y ≤
        uniformPrimeLogRpowConst / a * Y ^ a := by
  let C : ℝ := Classical.choose exists_chebyshevTheta_le_linear
  have hC0 : 0 < C := thetaLinearConst_pos
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hU0 : 0 < uniformPrimeLogRpowConst := uniformPrimeLogRpowConst_pos
  have hhalf := half_mul_le_one_sub_two_rpow_neg ha0 ha1
  have hrec : 2 * C + (uniformPrimeLogRpowConst / a) * (2 : ℝ) ^ (-a)
      ≤ uniformPrimeLogRpowConst / a := by
    have hane : a ≠ 0 := ne_of_gt ha0
    have hlogne : Real.log 2 ≠ 0 := ne_of_gt hlog0
    rw [uniformPrimeLogRpowConst]
    dsimp [C]
    field_simp
    nlinarith [hhalf, thetaLinearConst_pos]
  intro Y
  induction' hn : ⌊Y⌋₊ using Nat.strong_induction_on with n ih generalizing Y
  intro hY0
  rcases lt_or_ge Y 2 with hsmall | hbig
  · have hfl : ⌊Y⌋₊ ≤ 1 := by
      have h2 : Y < ((2 : ℕ) : ℝ) := by push_cast; linarith
      have := (Nat.floor_lt hY0).2 h2
      omega
    have hempty : (Finset.Ioc 0 ⌊Y⌋₊).filter (fun p => Nat.Prime p) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun p hp => ?_
      rw [Finset.mem_Ioc] at hp
      intro hprime
      have : 2 ≤ p := hprime.two_le
      omega
    have hzero : primeLogSum (fun t : ℝ => t ^ (a - 1)) 0 Y = 0 := by
      rw [primeLogSum, Nat.floor_zero, hempty, Finset.sum_empty]
    rw [hzero]
    positivity
  · have hY0' : (0 : ℝ) < Y := by linarith
    have hhalfY : (0 : ℝ) ≤ Y / 2 := by linarith
    have hfl1 : ⌊(0 : ℝ)⌋₊ ≤ ⌊Y / 2⌋₊ := by simp
    have hfl2 : ⌊Y / 2⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono (by linarith)
    have hsplit := primeLogSum_add (f := fun t : ℝ => t ^ (a - 1)) hfl1 hfl2
    have hshell : primeLogSum (fun t : ℝ => t ^ (a - 1)) (Y / 2) Y
        ≤ (Y / 2) ^ (a - 1) * (Chebyshev.theta Y - Chebyshev.theta (Y / 2)) := by
      refine primeLogSum_le hhalfY hfl2 fun p hprime h1 h2 => ?_
      exact Real.rpow_le_rpow_of_nonpos (by linarith) h1.le (by linarith)
    have htheta : Chebyshev.theta Y - Chebyshev.theta (Y / 2) ≤ C * Y := by
      have h1 := theta_le_linear Y (by linarith)
      have h2 := chebyshevTheta_nonneg (Y / 2)
      dsimp [C]
      linarith
    have hhalfpow : (Y / 2) ^ (a - 1) = (2 : ℝ) ^ (1 - a) * Y ^ (a - 1) := by
      rw [Real.div_rpow hY0'.le (by norm_num),
        show (1 : ℝ) - a = -(a - 1) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    have hYmul : Y ^ (a - 1) * Y = Y ^ a := by
      calc
        Y ^ (a - 1) * Y = Y ^ (a - 1) * Y ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = Y ^ ((a - 1) + 1) := (Real.rpow_add hY0' _ _).symm
        _ = Y ^ a := by ring_nf
    have htwo : (2 : ℝ) ^ (1 - a) ≤ 2 := by
      have hbase : (1 : ℝ) ≤ 2 := by norm_num
      have hexp : 1 - a ≤ 1 := by linarith
      simpa using Real.rpow_le_rpow_of_exponent_le hbase hexp
    have htop : primeLogSum (fun t : ℝ => t ^ (a - 1)) (Y / 2) Y
        ≤ 2 * C * Y ^ a := by
      have hmult0 : (0 : ℝ) ≤ (2 : ℝ) ^ (1 - a) * Y ^ (a - 1) := by positivity
      have hstep := mul_le_mul_of_nonneg_left htheta hmult0
      have hshell' := hshell
      rw [hhalfpow] at hshell'
      have hpow0 : (0 : ℝ) ≤ Y ^ (a - 1) := Real.rpow_nonneg hY0'.le _
      have hYa0 : (0 : ℝ) ≤ Y ^ a := Real.rpow_nonneg hY0'.le _
      calc
        primeLogSum (fun t : ℝ => t ^ (a - 1)) (Y / 2) Y
            ≤ (2 : ℝ) ^ (1 - a) * Y ^ (a - 1) * (C * Y) := hshell'.trans hstep
        _ = C * (2 : ℝ) ^ (1 - a) * Y ^ a := by rw [← hYmul]; ring
        _ ≤ 2 * C * Y ^ a := by
          exact mul_le_mul_of_nonneg_right
            (by nlinarith [mul_le_mul_of_nonneg_left htwo hC0.le]) hYa0
    have hlt : ⌊Y / 2⌋₊ < n := by
      have h1 : 1 ≤ ⌊Y / 2⌋₊ := Nat.le_floor (by norm_num; linarith)
      have h2 : 2 * ⌊Y / 2⌋₊ ≤ ⌊Y⌋₊ := by
        refine Nat.le_floor ?_
        have := Nat.floor_le hhalfY
        push_cast
        linarith
      omega
    have hih := ih ⌊Y / 2⌋₊ hlt (Y / 2) rfl hhalfY
    have hhalfpow2 : (Y / 2) ^ a = (2 : ℝ) ^ (-a) * Y ^ a := by
      rw [Real.div_rpow hY0'.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
    rw [hhalfpow2] at hih
    have hYa0 : (0 : ℝ) ≤ Y ^ a := Real.rpow_nonneg hY0'.le _
    calc
      primeLogSum (fun t : ℝ => t ^ (a - 1)) 0 Y
          = primeLogSum (fun t : ℝ => t ^ (a - 1)) 0 (Y / 2)
            + primeLogSum (fun t : ℝ => t ^ (a - 1)) (Y / 2) Y := hsplit.symm
      _ ≤ (uniformPrimeLogRpowConst / a) * ((2 : ℝ) ^ (-a) * Y ^ a)
            + 2 * C * Y ^ a := add_le_add hih htop
      _ = (2 * C + (uniformPrimeLogRpowConst / a) * (2 : ℝ) ^ (-a)) * Y ^ a := by ring
      _ ≤ uniformPrimeLogRpowConst / a * Y ^ a :=
        mul_le_mul_of_nonneg_right hrec hYa0

/-- Pointwise split behind the uniform unweighted prime-power bound. -/
theorem prime_rpow_sub_one_le_exp_div_add_log {a : ℝ} (ha0 : 0 < a) {p : ℕ}
    (hp : p.Prime) :
    (p : ℝ) ^ (a - 1) ≤ Real.exp 1 / (p : ℝ) +
      a * ((p : ℝ) ^ (a - 1) * Real.log p) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  have hpow0 : 0 ≤ (p : ℝ) ^ (a - 1) := Real.rpow_nonneg hp0.le _
  by_cases hsmall : a * Real.log (p : ℝ) ≤ 1
  · have hpa : (p : ℝ) ^ a ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hp0]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hsplit : (p : ℝ) ^ (a - 1) = (p : ℝ) ^ a / (p : ℝ) := by
      rw [Real.rpow_sub hp0, Real.rpow_one]
    have hmain : (p : ℝ) ^ (a - 1) ≤ Real.exp 1 / (p : ℝ) := by
      rw [hsplit]
      exact div_le_div_of_nonneg_right hpa hp0.le
    have htail : 0 ≤ a * ((p : ℝ) ^ (a - 1) * Real.log p) := by positivity
    linarith
  · have hlarge : 1 ≤ a * Real.log (p : ℝ) := by linarith
    have hmain : (p : ℝ) ^ (a - 1) ≤
        a * ((p : ℝ) ^ (a - 1) * Real.log p) := by
      have := mul_le_mul_of_nonneg_left hlarge hpow0
      nlinarith
    have hexp0 : 0 ≤ Real.exp 1 / (p : ℝ) := by positivity
    linarith

/-- Uniform unweighted prime-power bound.  The Mertens term pays the small values of
`a log p`; Chebyshev's shell estimate pays the rest. -/
theorem sum_primesLE_rpow_sub_one_le_uniform {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (z : ℕ) :
    ∑ p ∈ Nat.primesLE z, (p : ℝ) ^ (a - 1) ≤
      Real.exp 1 * RHTower.Sieve.mertensS z + uniformPrimeLogRpowConst * (z : ℝ) ^ a := by
  have hpoint : ∑ p ∈ Nat.primesLE z, (p : ℝ) ^ (a - 1) ≤
      ∑ p ∈ Nat.primesLE z,
        (Real.exp 1 / (p : ℝ) + a * ((p : ℝ) ^ (a - 1) * Real.log p)) := by
    exact Finset.sum_le_sum fun p hp =>
      prime_rpow_sub_one_le_exp_div_add_log ha0 (Nat.prime_of_mem_primesLE hp)
  have hprimeLog : RHTower.primeLogSum (fun t : ℝ => t ^ (a - 1)) 0 (z : ℝ) =
      ∑ p ∈ Nat.primesLE z, (p : ℝ) ^ (a - 1) * Real.log p := by
    rw [primeLogSum, Nat.floor_zero, Nat.floor_natCast]
    have hfin : (Finset.Ioc 0 z).filter (fun p => Nat.Prime p) = Nat.primesLE z := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨hp0, hpz⟩, hp⟩
        exact ⟨hpz, hp⟩
      · rintro ⟨hpz, hp⟩
        exact ⟨⟨hp.pos, hpz⟩, hp⟩
    rw [hfin]
    exact Finset.sum_congr rfl fun p _ => by ring
  have hweighted := primeLogSum_rpow_sub_one_le_uniform ha0 ha1 (z : ℝ)
    (Nat.cast_nonneg z)
  rw [hprimeLog] at hweighted
  have ha0' : 0 ≤ a := ha0.le
  have hmul := mul_le_mul_of_nonneg_left hweighted ha0'
  have hsum : ∑ p ∈ Nat.primesLE z,
        (Real.exp 1 / (p : ℝ) + a * ((p : ℝ) ^ (a - 1) * Real.log p)) =
      Real.exp 1 * RHTower.Sieve.mertensS z +
        a * ∑ p ∈ Nat.primesLE z, ((p : ℝ) ^ (a - 1) * Real.log p) := by
    rw [Finset.sum_add_distrib]
    congr 1
    · unfold RHTower.Sieve.mertensS
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    · rw [Finset.mul_sum]
  have hane : a ≠ 0 := ne_of_gt ha0
  calc
    ∑ p ∈ Nat.primesLE z, (p : ℝ) ^ (a - 1)
      ≤ ∑ p ∈ Nat.primesLE z,
          (Real.exp 1 / (p : ℝ) + a * ((p : ℝ) ^ (a - 1) * Real.log p)) := hpoint
    _ = Real.exp 1 * RHTower.Sieve.mertensS z +
        a * ∑ p ∈ Nat.primesLE z, ((p : ℝ) ^ (a - 1) * Real.log p) := hsum
    _ ≤ Real.exp 1 * RHTower.Sieve.mertensS z +
          a * (uniformPrimeLogRpowConst / a * (z : ℝ) ^ a) := by linarith
    _ = Real.exp 1 * RHTower.Sieve.mertensS z +
        uniformPrimeLogRpowConst * (z : ℝ) ^ a := by field_simp

/-- Uniform squarefree Euler-product bound at a shrinking Rankin exponent. -/
theorem prod_primesLE_one_add_rpow_sub_one_le_uniform {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (z : ℕ) :
    ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ) ^ (a - 1)) ≤
      Real.exp (Real.exp 1 * RHTower.Sieve.mertensS z +
        uniformPrimeLogRpowConst * (z : ℝ) ^ a) := by
  have hnonneg : ∀ p ∈ Nat.primesLE z, (0 : ℝ) ≤ 1 + (p : ℝ) ^ (a - 1) := by
    intro p _
    positivity
  have hstep : ∀ p ∈ Nat.primesLE z,
      1 + (p : ℝ) ^ (a - 1) ≤ Real.exp ((p : ℝ) ^ (a - 1)) := by
    intro p _
    simpa [add_comm] using Real.add_one_le_exp ((p : ℝ) ^ (a - 1))
  calc
    ∏ p ∈ Nat.primesLE z, (1 + (p : ℝ) ^ (a - 1))
      ≤ ∏ p ∈ Nat.primesLE z, Real.exp ((p : ℝ) ^ (a - 1)) :=
        Finset.prod_le_prod hnonneg hstep
    _ = Real.exp (∑ p ∈ Nat.primesLE z, (p : ℝ) ^ (a - 1)) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp (Real.exp 1 * RHTower.Sieve.mertensS z +
        uniformPrimeLogRpowConst * (z : ℝ) ^ a) :=
      Real.exp_le_exp.2 (sum_primesLE_rpow_sub_one_le_uniform ha0 ha1 z)

end

end RHTower
