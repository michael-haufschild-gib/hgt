import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.RingTheory.Binomial
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Filter Topology

namespace DRVerticalRootWork

example : True := by
  have := @Metric.uniformContinuous_iff.{0, 0}
  have := @Nat.exists_infinite_primes
  have := @Nat.mod_add_div
  have := @Real.log_le_sub_one_of_pos
  have := @Real.log_div
  have := @Real.log_le_log
  have := @exists_nat_gt.{0}
  trivial

theorem exists_close_prime_multiple_logs {δ : ℝ} (hδ : 0 < δ) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ 6 ∣ m ∧
      dist (Real.log p) (Real.log m) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (6 + 6 / δ)
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  let m : ℕ := 6 * (p / 6)
  have hrem : p % 6 < 6 := Nat.mod_lt p (by norm_num)
  have hdecomp : p % 6 + m = p := Nat.mod_add_div p 6
  have hpR : 6 + 6 / δ < (p : ℝ) := hN.trans_le (by exact_mod_cast hpN)
  have hp6 : 6 < p := by
    have : (6 : ℝ) < p := by linarith [div_pos (by norm_num : (0 : ℝ) < 6) hδ]
    exact_mod_cast this
  have hm : 0 < m := by omega
  have hmp : m ≤ p := by omega
  have hpm : p < m + 6 := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hmδ : 6 / δ < (m : ℝ) := by
    have hh : (p : ℝ) < (m : ℝ) + 6 := by exact_mod_cast hpm
    linarith
  have hmul : 6 < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hmδ
  have hratio : (p : ℝ) / m < δ + 1 := (div_lt_iff₀ hmR).mpr (by
    have hh : (p : ℝ) < (m : ℝ) + 6 := by exact_mod_cast hpm
    nlinarith)
  have hlog : Real.log (p : ℝ) - Real.log (m : ℝ) ≤ (p : ℝ) / m - 1 := by
    rw [← Real.log_div hpR0.ne' hmR.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hpR0 hmR)
  refine ⟨p, m, hp, hm, ⟨p / 6, rfl⟩, ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr
    (Real.log_le_log hmR (by exact_mod_cast hmp)))]
  linarith

theorem no_uniformContinuous_log_interpolant_of_prime_multiple_gap
    {a : ℕ → ℝ} {b c : ℝ} (hgap : b < c)
    (hprime : ∀ p : ℕ, p.Prime → a p = c)
    (hmultiple : ∀ m : ℕ, 0 < m → 6 ∣ m → a m ≤ b) :
    ¬ ∃ f : ℝ → ℝ, UniformContinuous f ∧
      ∀ n : ℕ, 0 < n → f (Real.log n) = a n := by
  rintro ⟨f, hf, hmatch⟩
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hf (c - b) (sub_pos.mpr hgap)
  obtain ⟨p, m, hp, hm, hm6, hlogs⟩ := exists_close_prime_multiple_logs hδ
  have h := hclose hlogs
  rw [hmatch p hp.pos, hmatch m hm, hprime p hp, Real.dist_eq] at h
  have hsmall := hmultiple m hm hm6
  rw [abs_of_nonneg (by linarith)] at h
  linarith

end DRVerticalRootWork

namespace DRVerticalRootWork

example : True := by
  have := @Matrix.det_vandermonde_ne_zero_iff.{0}
  have := @Matrix.isUnit_iff_isUnit_det.{0, 0}
  have := @Matrix.mulVec_surjective_iff_isUnit.{0, 0}
  have := @Complex.exp_inj_of_neg_pi_lt_of_le_pi
  have := @Complex.exp_nat_mul
  have := @Real.log_injOn_pos
  trivial

theorem exists_finite_vertical_interpolation (N : ℕ) (a : Fin N → ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ w : Fin N → ℂ, ∀ n : Fin N,
      (∑ j : Fin N, w j * Complex.exp
        (-(((j.val : ℝ) * δ * Real.log ((n.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)) = a n := by
  classical
  let L : ℝ := Real.log ((N + 1 : ℕ) : ℝ) + 1
  have hL : 0 < L := by
    have hlog : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos N)
    dsimp [L]
    linarith
  let δ : ℝ := Real.pi / L
  have hδ : 0 < δ := div_pos Real.pi_pos hL
  have hδL : δ * L = Real.pi := div_mul_cancel₀ _ hL.ne'
  let phase (n : Fin N) : ℂ := -((δ * Real.log ((n.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I
  let z (n : Fin N) : ℂ := Complex.exp (phase n)
  have him (n : Fin N) : (phase n).im = -(δ * Real.log ((n.val + 1 : ℕ) : ℝ)) := by
    simp [phase]
  have hphase (n : Fin N) : -Real.pi < (phase n).im ∧ (phase n).im ≤ Real.pi := by
    have hn0 : 0 < ((n.val + 1 : ℕ) : ℝ) := by positivity
    have hnlog : 0 ≤ Real.log ((n.val + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos n.val)
    have hnL : Real.log ((n.val + 1 : ℕ) : ℝ) < L := by
      exact (Real.log_le_log hn0 (by exact_mod_cast Nat.succ_le_succ n.isLt.le)).trans_lt
        (lt_add_one _)
    have hb := mul_lt_mul_of_pos_left hnL hδ
    rw [hδL] at hb
    rw [him]
    constructor
    · linarith
    · nlinarith [Real.pi_pos]
  have hz : Function.Injective z := by
    intro i j hij
    have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (hphase i).1 (hphase i).2 (hphase j).1 (hphase j).2 hij
    have hi := congrArg Complex.im he
    rw [him, him] at hi
    have hlogs : Real.log ((i.val + 1 : ℕ) : ℝ) = Real.log ((j.val + 1 : ℕ) : ℝ) := by
      nlinarith
    have hvals := Real.log_injOn_pos (by positivity : (0 : ℝ) < (i.val + 1 : ℕ))
      (by positivity : (0 : ℝ) < (j.val + 1 : ℕ)) hlogs
    have hnat : i.val + 1 = j.val + 1 := by exact_mod_cast hvals
    exact Fin.ext (by omega)
  have hunit : IsUnit (Matrix.vandermonde z) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hz))
  obtain ⟨w, hw⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) a
  refine ⟨δ, hδ, w, fun n => ?_⟩
  have hwn := congrFun hw n
  change (∑ j : Fin N, z n ^ j.val * w j) = a n at hwn
  rw [← hwn]
  apply Finset.sum_congr rfl
  intro j _
  have he : Complex.exp
      (-(((j.val : ℝ) * δ * Real.log ((n.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) = z n ^ j.val := by
    rw [show z n = Complex.exp (phase n) from rfl, ← Complex.exp_nat_mul]
    congr 1
    dsimp [phase]
    push_cast
    ring
  rw [he, mul_comm]

end DRVerticalRootWork

namespace DRVerticalRootWork

noncomputable def rootLocal (α : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (α + j) / ((j : ℝ) + 1)

@[simp] theorem rootLocal_zero (α : ℝ) : rootLocal α 0 = 1 := by simp [rootLocal]
@[simp] theorem rootLocal_one (α : ℝ) : rootLocal α 1 = α := by simp [rootLocal]

theorem rootLocal_succ (α : ℝ) (k : ℕ) :
    rootLocal α (k + 1) = rootLocal α k * ((α + k) / ((k : ℝ) + 1)) := by
  exact Finset.prod_range_succ _ k

theorem rootLocal_nonneg {α : ℝ} (hα : 0 ≤ α) (k : ℕ) : 0 ≤ rootLocal α k := by
  apply Finset.prod_nonneg
  intro j _
  positivity

theorem rootLocal_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    rootLocal α k ≤ 1 := by
  apply Finset.prod_le_one
  · intro j _
    positivity
  · intro j _
    exact (div_le_one (by positivity)).mpr (by linarith)

theorem rootLocal_succ_le_alpha {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    rootLocal α (k + 1) ≤ α := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [rootLocal_succ]
    exact (mul_le_of_le_one_right (rootLocal_nonneg hα0 (k + 1))
      ((div_le_one (by positivity)).mpr (by linarith))).trans ih

theorem rootLocal_le_alpha {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) {k : ℕ} (hk : 0 < k) :
    rootLocal α k ≤ α := by
  cases k with
  | zero => omega
  | succ k => exact rootLocal_succ_le_alpha hα0 hα1 k

noncomputable def rootCoeff (α : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else n.factorization.prod (fun _ k => rootLocal α k)

@[simp] theorem rootCoeff_zero (α : ℝ) : rootCoeff α 0 = 0 := by simp [rootCoeff]
@[simp] theorem rootCoeff_one (α : ℝ) : rootCoeff α 1 = 1 := by simp [rootCoeff]

theorem rootCoeff_prime (α : ℝ) {p : ℕ} (hp : p.Prime) : rootCoeff α p = α := by
  rw [rootCoeff, if_neg hp.ne_zero, hp.factorization, Finsupp.prod_single_index] <;> simp

theorem rootCoeff_nonneg {α : ℝ} (hα : 0 ≤ α) (n : ℕ) : 0 ≤ rootCoeff α n := by
  unfold rootCoeff
  split_ifs
  · exact le_rfl
  · apply Finset.prod_nonneg
    intro p _
    exact rootLocal_nonneg hα _

theorem rootCoeff_le_one {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (n : ℕ) :
    rootCoeff α n ≤ 1 := by
  unfold rootCoeff
  split_ifs
  · norm_num
  · apply Finset.prod_le_one
    · intro p _
      exact rootLocal_nonneg hα0 _
    · intro p _
      exact rootLocal_le_one hα0 hα1 _

theorem rootCoeff_multiple_six_le_sq {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {n : ℕ} (hn : 0 < n) (hn6 : 6 ∣ n) : rootCoeff α n ≤ α ^ 2 := by
  classical
  have h2 : 0 < n.factorization 2 := Nat.prime_two.factorization_pos_of_dvd hn.ne'
    (dvd_trans (by norm_num : 2 ∣ 6) hn6)
  have h3 : 0 < n.factorization 3 := Nat.prime_three.factorization_pos_of_dvd hn.ne'
    (dvd_trans (by norm_num : 3 ∣ 6) hn6)
  have hsub : ({2, 3} : Finset ℕ) ⊆ n.factorization.support := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Finsupp.mem_support_iff.mpr h2.ne'
    · exact Finsupp.mem_support_iff.mpr h3.ne'
  have hb := Finset.prod_le_prod_of_subset_of_le_one
    (f := fun p => rootLocal α (n.factorization p)) hsub
    (fun p _ => rootLocal_nonneg hα0 _)
    (fun p _ _ => rootLocal_le_one hα0 hα1 _)
  calc
    rootCoeff α n ≤ rootLocal α (n.factorization 2) * rootLocal α (n.factorization 3) := by
      simpa [rootCoeff, hn.ne', Finsupp.prod] using hb
    _ ≤ α * α := mul_le_mul (rootLocal_le_alpha hα0 hα1 h2)
      (rootLocal_le_alpha hα0 hα1 h3) (rootLocal_nonneg hα0 _) hα0
    _ = α ^ 2 := (sq α).symm

theorem no_uniformContinuous_rootCoeff_log_interpolant {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ¬ ∃ f : ℝ → ℝ, UniformContinuous f ∧
      ∀ n : ℕ, 0 < n → f (Real.log n) = rootCoeff α n := by
  apply no_uniformContinuous_log_interpolant_of_prime_multiple_gap
    (a := rootCoeff α) (b := α ^ 2) (c := α)
  · nlinarith
  · intro p hp
    exact rootCoeff_prime α hp
  · intro m hm hm6
    exact rootCoeff_multiple_six_le_sq hα0.le hα1.le hm hm6

end DRVerticalRootWork
