import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.RHTower.PrimeClockShaleDiagonal

/-!
# Finite-cutoff scaling of the reflected prime-clock energy

At a symmetric displacement `ε` from the critical line, the finite prime-clock energy has the exact
hyperbolic form

`E_N(ε) = ∑_{p ≤ N} 4 sinh²(ε log p) / p`.

This module formalizes the algebraic core and proves from Mertens' first theorem that the quadratic
susceptibility is asymptotic to `(1/2) (log N)^2`.  The remaining step for the full nonlinear
crossover profile is the weak convergence of the corresponding weighted prime measures.
-/

noncomputable section

namespace RHTower

lemma reflected_rpow_diff_sq_eq_sinh {x : ℝ} (hx : 0 < x) (ε : ℝ) :
    (x ^ (-(1 / 2 + ε)) - x ^ (-(1 / 2 - ε))) ^ 2 =
      4 * Real.sinh (ε * Real.log x) ^ 2 / x := by
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, Real.sinh_eq]
  have hexplog : Real.exp (-Real.log x) = x⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hx]
  have h₁ : Real.exp (Real.log x * (-(1 / 2 + ε))) =
      Real.exp (-(Real.log x) / 2) * Real.exp (-(ε * Real.log x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₂ : Real.exp (Real.log x * (-(1 / 2 - ε))) =
      Real.exp (-(Real.log x) / 2) * Real.exp (ε * Real.log x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h₁, h₂]
  have hsq : Real.exp (-(Real.log x) / 2) ^ 2 = Real.exp (-Real.log x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hdiff :
      Real.exp (-(Real.log x) / 2) * Real.exp (-(ε * Real.log x)) -
        Real.exp (-(Real.log x) / 2) * Real.exp (ε * Real.log x) =
      -Real.exp (-(Real.log x) / 2) *
        (Real.exp (ε * Real.log x) - Real.exp (-(ε * Real.log x))) := by
    ring
  rw [hdiff, mul_pow]
  have hnegsq : (-Real.exp (-(Real.log x) / 2)) ^ 2 =
      Real.exp (-(Real.log x) / 2) ^ 2 := by
    ring
  rw [hnegsq, hsq, hexplog]
  field_simp
  ring

/-- Finite reflected prime-clock displacement energy at cutoff `N`. -/
def primeClockCutoffEnergy (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE N,
    ((p : ℝ) ^ (-(1 / 2 + ε)) - (p : ℝ) ^ (-(1 / 2 - ε))) ^ 2

/-- Hyperbolic-sine form of the finite reflected prime-clock energy. -/
theorem primeClockCutoffEnergy_eq_sinh (N : ℕ) (ε : ℝ) :
    primeClockCutoffEnergy N ε =
      ∑ p ∈ Nat.primesLE N, 4 * Real.sinh (ε * Real.log p) ^ 2 / p := by
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime := (Nat.mem_primesLE.mp hp).2
  exact reflected_rpow_diff_sq_eq_sinh (by exact_mod_cast hpprime.pos) ε

/-- Quadratic susceptibility of the finite prime-clock system. -/
def primeClockSusceptibility (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesLE N, Real.log p ^ 2 / p

lemma sq_le_sinh_sq (x : ℝ) : x ^ 2 ≤ Real.sinh x ^ 2 := by
  rw [sq_le_sq, Real.abs_sinh]
  exact Real.self_le_sinh_iff.mpr (abs_nonneg x)

/-- The reflected energy dominates its quadratic response at the critical line. -/
theorem primeClockCutoffEnergy_quadratic_lower (N : ℕ) (ε : ℝ) :
    4 * ε ^ 2 * primeClockSusceptibility N ≤ primeClockCutoffEnergy N ε := by
  rw [primeClockCutoffEnergy_eq_sinh, primeClockSusceptibility, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpprime : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hs := sq_le_sinh_sq (ε * Real.log p)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinv : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr hp0.le
  calc
    4 * ε ^ 2 * (Real.log p ^ 2 * (p : ℝ)⁻¹) =
        4 * ((ε * Real.log p) ^ 2 * (p : ℝ)⁻¹) := by ring
    _ ≤ 4 * (Real.sinh (ε * Real.log p) ^ 2 * (p : ℝ)⁻¹) := by nlinarith
    _ = 4 * Real.sinh (ε * Real.log ↑p) ^ 2 * (p : ℝ)⁻¹ := by ring

@[simp] theorem primeClockCutoffEnergy_zero (N : ℕ) :
    primeClockCutoffEnergy N 0 = 0 := by
  rw [primeClockCutoffEnergy_eq_sinh]
  simp

theorem primeClockCutoffEnergy_neg (N : ℕ) (ε : ℝ) :
    primeClockCutoffEnergy N (-ε) = primeClockCutoffEnergy N ε := by
  rw [primeClockCutoffEnergy_eq_sinh, primeClockCutoffEnergy_eq_sinh]
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_mul, Real.sinh_neg]
  ring

theorem primeClockSusceptibility_nonneg (N : ℕ) :
    0 ≤ primeClockSusceptibility N := by
  apply Finset.sum_nonneg
  intro p hp
  positivity

end RHTower
namespace RHTower

open Finset Filter Topology
open scoped BigOperators Topology

private def primeLogWeight (n : ℕ) : ℝ :=
  if n.Prime then Real.log n / n else 0

private def primeLogHarmonicRange (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), primeLogWeight n

private theorem primeLogHarmonicRange_eq (N : ℕ) :
    primeLogHarmonicRange N =
      ∑ n ∈ Finset.Icc 1 N with n.Prime, Real.log n / (n : ℝ) := by
  rw [primeLogHarmonicRange,
    show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega,
    Finset.sum_insert (by simp)]
  simp only [primeLogWeight, Nat.not_prime_zero, ↓reduceIte, zero_add]
  rw [Finset.sum_filter]

private theorem primeLogHarmonicRange_error_bound (N : ℕ) (hN : 1 ≤ N) :
    |primeLogHarmonicRange N - Real.log N| ≤
      (Real.log 4 + 4) + (8 + Mertens.mertensTail) := by
  rw [primeLogHarmonicRange_eq]
  exact Mertens.mertens_first_prime N hN

private def primeLogSusceptibilityRange (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), Real.log n * primeLogWeight n

private theorem primeLogSusceptibilityRange_eq (N : ℕ) :
    primeLogSusceptibilityRange N = primeClockSusceptibility N := by
  rw [primeLogSusceptibilityRange, primeClockSusceptibility]
  rw [show Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) by
      ext n
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega,
    Finset.sum_insert (by simp)]
  rw [show Nat.primesLE N = (Finset.Icc 1 N).filter Nat.Prime by
      ext n
      simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hnN, hp⟩
        exact ⟨⟨hp.one_le, hnN⟩, hp⟩
      · rintro ⟨⟨hn1, hnN⟩, hp⟩
        exact ⟨hnN, hp⟩]
  rw [Finset.sum_filter]
  norm_num [primeLogWeight]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp only [hp, ↓reduceIte]
    ring
  · simp [hp]

private theorem primeLogSusceptibilityRange_abel (N : ℕ) (hN : 0 < N) :
    primeLogSusceptibilityRange N =
      Real.log N * primeLogHarmonicRange N -
        ∑ n ∈ Finset.Ioc 0 (N - 1),
          (Real.log (n + 1) - Real.log n) * primeLogHarmonicRange n := by
  have hab := Finset.sum_Ioc_by_parts (fun n : ℕ => Real.log n) primeLogWeight hN
  have hleft :
      (∑ n ∈ Finset.Ioc 0 N, Real.log n * primeLogWeight n) =
        primeLogSusceptibilityRange N := by
    rw [primeLogSusceptibilityRange,
      show Finset.range (N + 1) = insert 0 (Finset.Ioc 0 N) by
        ext n
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
        omega,
      Finset.sum_insert (by simp)]
    simp [primeLogWeight]
  simp only [smul_eq_mul] at hab
  rw [hleft] at hab
  simpa [primeLogHarmonicRange, primeLogWeight] using hab

end RHTower

namespace RHTower

open Finset

private def logStep (n : ℕ) : ℝ := Real.log (n + 1) - Real.log n

private theorem logStep_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ logStep n := by
  rw [logStep]
  exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hn)) (by norm_num))

private theorem logStep_le_one {n : ℕ} (hn : 1 ≤ n) : logStep n ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hratio : (0 : ℝ) < (n + 1 : ℕ) / (n : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (by positivity) (by positivity)] at hlog
  have hdiv : ((n + 1 : ℕ) : ℝ) / n - 1 = 1 / (n : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
    norm_num
  rw [hdiv] at hlog
  have hinv : 1 / (n : ℝ) ≤ 1 := by
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hn)
  simpa [logStep] using hlog.trans hinv

private theorem sum_logStep (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n = Real.log N := by
  rw [show Finset.Ioc 0 (N - 1) = Finset.Ico 1 N by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega]
  simp_rw [logStep]
  rw [Finset.sum_Ico_eq_sub _ hN]
  have hNtel : ∑ k ∈ Finset.range N, (Real.log ((k : ℝ) + 1) - Real.log k) =
      Real.log N - Real.log 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      Finset.sum_range_sub (fun n : ℕ => Real.log (n : ℝ)) N
  have h1tel : ∑ k ∈ Finset.range 1, (Real.log ((k : ℝ) + 1) - Real.log k) =
      Real.log 1 - Real.log 0 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
      Finset.sum_range_sub (fun n : ℕ => Real.log (n : ℝ)) 1
  rw [hNtel, h1tel]
  norm_num

private theorem sum_logStep_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2 ≤ Real.log N := by
  calc
    ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2 ≤
        ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := by simpa using! (Finset.mem_Ioc.mp hn).1
      have h0 := logStep_nonneg hn1
      have h1 := logStep_le_one hn1
      nlinarith
    _ = Real.log N := sum_logStep N hN

private theorem logStep_square_identity (N : ℕ) (hN : 1 ≤ N) :
    2 * (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * Real.log n) +
        ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2 = Real.log N ^ 2 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  calc
    ∑ x ∈ Finset.Ioc 0 (N - 1),
        (2 * (logStep x * Real.log ↑x) + logStep x ^ 2) =
      ∑ x ∈ Finset.Ioc 0 (N - 1),
        (Real.log (x + 1) ^ 2 - Real.log x ^ 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [logStep]
      ring
    _ = Real.log N ^ 2 := by
      rw [show Finset.Ioc 0 (N - 1) = Finset.Ico 1 N by
          ext n
          simp only [Finset.mem_Ioc, Finset.mem_Ico]
          omega,
        Finset.sum_Ico_eq_sub _ hN]
      have hNtel : ∑ k ∈ Finset.range N,
          (Real.log ((k : ℝ) + 1) ^ 2 - Real.log k ^ 2) =
          Real.log N ^ 2 - Real.log 0 ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
          Finset.sum_range_sub (fun n : ℕ => Real.log (n : ℝ) ^ 2) N
      have h1tel : ∑ k ∈ Finset.range 1,
          (Real.log ((k : ℝ) + 1) ^ 2 - Real.log k ^ 2) =
          Real.log 1 ^ 2 - Real.log 0 ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
          Finset.sum_range_sub (fun n : ℕ => Real.log (n : ℝ) ^ 2) 1
      rw [hNtel, h1tel]
      norm_num

end RHTower

namespace RHTower

private def primeMertensBound : ℝ :=
  (Real.log 4 + 4) + (8 + Mertens.mertensTail)

private theorem primeMertensBound_nonneg : 0 ≤ primeMertensBound := by
  have htail : 0 ≤ Mertens.mertensTail := by
    rw [Mertens.mertensTail]
    exact tsum_nonneg fun i => by positivity
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [primeMertensBound]
  positivity

private def primeLogError (N : ℕ) : ℝ :=
  primeLogHarmonicRange N - Real.log N

private theorem primeLogError_bound (N : ℕ) (hN : 1 ≤ N) :
    |primeLogError N| ≤ primeMertensBound := by
  exact primeLogHarmonicRange_error_bound N hN

private theorem primeLogSusceptibility_decomposition (N : ℕ) (hN : 1 ≤ N) :
    primeLogSusceptibilityRange N - (1 / 2 : ℝ) * Real.log N ^ 2 =
      (1 / 2 : ℝ) * (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2) +
      Real.log N * primeLogError N -
      ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogError n := by
  have hab := primeLogSusceptibilityRange_abel N (Nat.zero_lt_of_lt hN)
  have hsq := logStep_square_identity N hN
  have herrsum :
      (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogError n) =
        (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogHarmonicRange n) -
        ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * Real.log n := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [primeLogError]
    ring
  rw [hab, herrsum, primeLogError]
  simp only [logStep] at hsq ⊢
  linarith

end RHTower

namespace RHTower

private theorem primeLogSusceptibility_error_bound (N : ℕ) (hN : 1 ≤ N) :
    |primeLogSusceptibilityRange N - (1 / 2 : ℝ) * Real.log N ^ 2| ≤
      ((1 / 2 : ℝ) + 2 * primeMertensBound) * Real.log N := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hC : 0 ≤ primeMertensBound := primeMertensBound_nonneg
  have hsq0 : 0 ≤ ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2 :=
    Finset.sum_nonneg fun n hn => sq_nonneg _
  have hsqle := sum_logStep_sq_le N hN
  have hmainAbs :
      |(1 / 2 : ℝ) * (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2)| ≤
        (1 / 2 : ℝ) * Real.log N := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hsq0)]
    nlinarith
  have hendpointAbs :
      |Real.log N * primeLogError N| ≤ Real.log N * primeMertensBound := by
    rw [abs_mul, abs_of_nonneg hlogN]
    exact mul_le_mul_of_nonneg_left (primeLogError_bound N hN) hlogN
  have hsumAbs :
      |∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogError n| ≤
        primeMertensBound * Real.log N := by
    calc
      |∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogError n| ≤
          ∑ n ∈ Finset.Ioc 0 (N - 1), |logStep n * primeLogError n| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeMertensBound := by
        apply Finset.sum_le_sum
        intro n hn
        have hn1 : 1 ≤ n := by simpa using! (Finset.mem_Ioc.mp hn).1
        have hstep : 0 ≤ logStep n := logStep_nonneg hn1
        rw [abs_mul, abs_of_nonneg hstep]
        exact mul_le_mul_of_nonneg_left (primeLogError_bound n hn1) hstep
      _ = primeMertensBound * Real.log N := by
        calc
          ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeMertensBound =
              primeMertensBound * ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            ring
          _ = primeMertensBound * Real.log N := by rw [sum_logStep N hN]
  have hdec := primeLogSusceptibility_decomposition N hN
  rw [hdec]
  calc
    |(1 / 2 : ℝ) * (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2) +
        Real.log N * primeLogError N -
        ∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogError n| ≤
      |(1 / 2 : ℝ) * (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2) +
        Real.log N * primeLogError N| +
      |∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogError n| := abs_sub _ _
    _ ≤
      (|(1 / 2 : ℝ) * (∑ n ∈ Finset.Ioc 0 (N - 1), logStep n ^ 2)| +
        |Real.log N * primeLogError N|) +
      |∑ n ∈ Finset.Ioc 0 (N - 1), logStep n * primeLogError n| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ ((1 / 2 : ℝ) + 2 * primeMertensBound) * Real.log N := by
      nlinarith

end RHTower

namespace RHTower

open Filter Topology

/-- The prime-clock susceptibility has the universal quadratic asymptotic
`chi_N ~ (1/2) (log N)^2`. -/
theorem tendsto_primeClockSusceptibility_div_log_sq :
    Tendsto (fun N : ℕ => primeClockSusceptibility N / Real.log N ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let K : ℝ := (1 / 2 : ℝ) + 2 * primeMertensBound
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hKzero : Tendsto (fun N : ℕ => K / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _)
    (show ∀ᶠ N : ℕ in atTop,
      ‖primeClockSusceptibility N / Real.log N ^ 2 - (1 / 2 : ℝ)‖ ≤
        K / Real.log N by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hN1 : 1 ≤ N := by omega
      have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
      have herr := primeLogSusceptibility_error_bound N hN1
      rw [primeLogSusceptibilityRange_eq] at herr
      have halg :
          primeClockSusceptibility N / Real.log N ^ 2 - (1 / 2 : ℝ) =
            (primeClockSusceptibility N - (1 / 2 : ℝ) * Real.log N ^ 2) /
              Real.log N ^ 2 := by
        field_simp
      rw [halg, Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hlogpos)]
      calc
        |primeClockSusceptibility N - (1 / 2 : ℝ) * Real.log N ^ 2| /
              Real.log N ^ 2 ≤
            (((1 / 2 : ℝ) + 2 * primeMertensBound) * Real.log N) /
              Real.log N ^ 2 :=
          div_le_div_of_nonneg_right herr (sq_nonneg _)
        _ = K / Real.log N := by
          rw [show K = (1 / 2 : ℝ) + 2 * primeMertensBound by rfl]
          field_simp
          )
  exact hKzero

end RHTower
namespace RHTower

open Set

lemma abs_sinh_le_abs_mul_cosh {x C : ℝ} (hC : 0 ≤ C) (hx : |x| ≤ C) :
    |Real.sinh x| ≤ |x| * Real.cosh C := by
  have habs : |x| ∈ Icc (0 : ℝ) C := ⟨abs_nonneg x, hx⟩
  have hderiv : ∀ y ∈ Icc (0 : ℝ) C,
      HasDerivWithinAt Real.sinh (Real.cosh y) (Icc (0 : ℝ) C) y := by
    intro y hy
    exact (Real.hasDerivAt_sinh y).hasDerivWithinAt
  have hbound : ∀ y ∈ Ico (0 : ℝ) C, ‖Real.cosh y‖ ≤ Real.cosh C := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos y)]
    exact Real.cosh_le_cosh.mpr (by
      rw [abs_of_nonneg hy.1, abs_of_nonneg hC]
      exact hy.2.le)
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound |x| habs
  rw [Real.sinh_zero, sub_zero, Real.norm_eq_abs, Real.abs_sinh,
    abs_abs, sub_zero, mul_comm] at hmv
  simpa only [Real.abs_sinh] using hmv

lemma sinh_sq_le_sq_mul_cosh_sq {x C : ℝ} (hC : 0 ≤ C) (hx : |x| ≤ C) :
    Real.sinh x ^ 2 ≤ x ^ 2 * Real.cosh C ^ 2 := by
  have h := abs_sinh_le_abs_mul_cosh hC hx
  have hsq : |Real.sinh x| ^ 2 ≤ (|x| * Real.cosh C) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.cosh_pos C).le)).2 h
  simpa only [sq_abs, mul_pow] using hsq

/-- Uniform upper bound in a finite critical window. -/
theorem primeClockCutoffEnergy_quadratic_upper
    (N : ℕ) (ε C : ℝ) (hC : 0 ≤ C)
    (hwindow : |ε| * Real.log N ≤ C) :
    primeClockCutoffEnergy N ε ≤
      4 * Real.cosh C ^ 2 * ε ^ 2 * primeClockSusceptibility N := by
  rw [primeClockCutoffEnergy_eq_sinh, primeClockSusceptibility,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have hpdata := Nat.mem_primesLE.mp hp
  have hpprime : p.Prime := hpdata.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
  have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
  have hlogle : Real.log p ≤ Real.log N :=
    Real.log_le_log hp0 (by exact_mod_cast hpdata.1)
  have harg : |ε * Real.log p| ≤ C := by
    rw [abs_mul, abs_of_nonneg hlogp0]
    exact (mul_le_mul_of_nonneg_left hlogle (abs_nonneg ε)).trans hwindow
  have hs := sinh_sq_le_sq_mul_cosh_sq hC harg
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hinv : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr hp0.le
  calc
    4 * Real.sinh (ε * Real.log ↑p) ^ 2 * (p : ℝ)⁻¹ ≤
        4 * ((ε * Real.log p) ^ 2 * Real.cosh C ^ 2) * (p : ℝ)⁻¹ := by
      gcongr
    _ = 4 * Real.cosh C ^ 2 * ε ^ 2 * (Real.log ↑p ^ 2 * (p : ℝ)⁻¹) := by
      ring

end RHTower

namespace RHTower

open Filter Topology

/-- Finite cutoff energy is nonnegative. -/
theorem primeClockCutoffEnergy_nonneg (N : ℕ) (ε : ℝ) :
    0 ≤ primeClockCutoffEnergy N ε := by
  rw [primeClockCutoffEnergy_eq_sinh]
  apply Finset.sum_nonneg
  intro p hp
  positivity

/-- Inside a window narrower than `1 / log N`, the reflected finite-prime energy tends to zero. -/
theorem tendsto_primeClockCutoffEnergy_zero_of_scaled_tendsto_zero
    (ε : ℕ → ℝ)
    (hscaled : Tendsto (fun N : ℕ => ε N * Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => primeClockCutoffEnergy N (ε N)) atTop (𝓝 0) := by
  let K : ℝ := 4 * Real.cosh 1 ^ 2
  have hratio := tendsto_primeClockSusceptibility_div_log_sq
  have hsquare : Tendsto (fun N : ℕ => (ε N * Real.log N) ^ 2) atTop (𝓝 0) := by
    simpa using hscaled.pow 2
  have hupper0 : Tendsto
      (fun N : ℕ => K * ((ε N * Real.log N) ^ 2 *
        (primeClockSusceptibility N / Real.log N ^ 2))) atTop (𝓝 0) := by
    have h := (hsquare.mul hratio).const_mul K
    simpa [K] using h
  have hupper0' : Tendsto
      (fun N : ℕ => K * ε N ^ 2 * primeClockSusceptibility N) atTop (𝓝 0) := by
    apply hupper0.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogne : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    field_simp
  have hwindow : ∀ᶠ N : ℕ in atTop, |ε N| * Real.log N ≤ 1 := by
    have hmetric := (Metric.tendsto_atTop.mp hscaled) 1 zero_lt_one
    rcases hmetric with ⟨N₀, hN₀⟩
    filter_upwards [eventually_ge_atTop N₀, eventually_ge_atTop 2] with N hNN₀ hN2
    have hdist := (hN₀ N hNN₀).le
    rw [Real.dist_eq, sub_zero, abs_mul,
      abs_of_nonneg (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ N by omega)))] at hdist
    exact hdist
  apply squeeze_zero' (Eventually.of_forall fun N => primeClockCutoffEnergy_nonneg N (ε N))
    (show ∀ᶠ N : ℕ in atTop,
      primeClockCutoffEnergy N (ε N) ≤ K * ε N ^ 2 * primeClockSusceptibility N by
      filter_upwards [hwindow] with N hN
      simpa [K] using primeClockCutoffEnergy_quadratic_upper N (ε N) 1 (by norm_num) hN)
  exact hupper0'

end RHTower

namespace RHTower

open Filter Topology

/-- Outside every `1 / log N` window, the reflected finite-prime energy diverges. -/
theorem tendsto_primeClockCutoffEnergy_atTop_of_scaled_tendsto_atTop
    (ε : ℕ → ℝ)
    (hscaled : Tendsto (fun N : ℕ => |ε N| * Real.log N) atTop atTop) :
    Tendsto (fun N : ℕ => primeClockCutoffEnergy N (ε N)) atTop atTop := by
  let a : ℕ → ℝ := fun N => |ε N| * Real.log N
  have ha : Tendsto a atTop atTop := hscaled
  have hasq : Tendsto (fun N => a N ^ 2) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (show ∀ᶠ N : ℕ in atTop, a N ≤ a N ^ 2 by
        filter_upwards [ha.eventually_ge_atTop 1] with N hN
        nlinarith)
    exact ha
  have hratio := tendsto_primeClockSusceptibility_div_log_sq
  have hprod : Tendsto
      (fun N : ℕ => (primeClockSusceptibility N / Real.log N ^ 2) * a N ^ 2)
      atTop atTop := hratio.pos_mul_atTop (by norm_num) hasq
  have hlowerTop : Tendsto
      (fun N : ℕ => 4 * ε N ^ 2 * primeClockSusceptibility N) atTop atTop := by
    have hscaledProd := hprod.const_mul_atTop (by norm_num : (0 : ℝ) < 4)
    apply hscaledProd.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlogne : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
    dsimp [a]
    rw [mul_pow, sq_abs]
    field_simp
  apply tendsto_atTop_mono' atTop
    (Eventually.of_forall fun N => primeClockCutoffEnergy_quadratic_lower N (ε N))
    hlowerTop

end RHTower
namespace RHTower

/-- Exact finite-cutoff sandwich in the critical scaling `ε = c / log N`. -/
theorem primeClockCutoffEnergy_critical_scaled_sandwich
    (N : ℕ) (c : ℝ) (hN : 2 ≤ N) :
    4 * c ^ 2 * (primeClockSusceptibility N / Real.log N ^ 2) ≤
        primeClockCutoffEnergy N (c / Real.log N) ∧
      primeClockCutoffEnergy N (c / Real.log N) ≤
        4 * Real.cosh |c| ^ 2 * c ^ 2 *
          (primeClockSusceptibility N / Real.log N ^ 2) := by
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  have hlogne : Real.log N ≠ 0 := hlogpos.ne'
  constructor
  · have h := primeClockCutoffEnergy_quadratic_lower N (c / Real.log N)
    calc
      4 * c ^ 2 * (primeClockSusceptibility N / Real.log N ^ 2) =
          4 * (c / Real.log N) ^ 2 * primeClockSusceptibility N := by
        field_simp
      _ ≤ primeClockCutoffEnergy N (c / Real.log N) := h
  · have hwindow : |c / Real.log N| * Real.log N ≤ |c| := by
      rw [abs_div, abs_of_pos hlogpos]
      field_simp
      exact le_rfl
    have h := primeClockCutoffEnergy_quadratic_upper N (c / Real.log N) |c|
      (abs_nonneg c) hwindow
    calc
      primeClockCutoffEnergy N (c / Real.log N) ≤
          4 * Real.cosh |c| ^ 2 * (c / Real.log N) ^ 2 *
            primeClockSusceptibility N := h
      _ = 4 * Real.cosh |c| ^ 2 * c ^ 2 *
          (primeClockSusceptibility N / Real.log N ^ 2) := by
        field_simp

end RHTower
