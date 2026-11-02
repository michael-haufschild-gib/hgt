import GaloisForLFunctions.ArithmeticCouplingTheory.TheCompleteFormOnTheCoherentSector
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The exact harmonic diagonal of prime incidence defects

An incidence jump changes one prime coordinate. Squaring its coefficient
therefore converts the Dirichlet energy into a linear source-target drift.
The drift has zero total mass and an exact harmonic sum on each divisibility
class, giving a diagonal at every finite horizon.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CompletedArithmeticForms
open ArithmeticCouplingTheory

private def horizonDrift (N n : ℕ) : ℝ :=
  (Real.log n - mertensSum (N / n)) / n

private theorem sum_horizonDrift_eq_zero (N : ℕ) :
    (∑ n ∈ Icc 1 N, horizonDrift N n) = 0 := by
  have ht := sum_dilation_target_eq N (fun _ => (1 : ℝ))
  have hs := sum_dilation_source_eq N (fun n => (1 : ℝ) / n)
  simp only [one_mul] at ht
  have he : (∑ n ∈ Icc 1 N, Real.log n / n) =
      ∑ n ∈ Icc 1 N, mertensSum (N / n) / n := by
    calc
      _ = _ := ht.symm
      _ = _ := hs
      _ = _ := sum_congr rfl fun n _ => by ring
  simp only [horizonDrift, sub_div, sum_sub_distrib, he, sub_self]

private theorem jumpEnergy_incidence_eq_drift (P : Finset ℕ) (b : ℕ → ℝ)
    (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    jumpEnergy N (incidencePacket P b) =
      ∑ n ∈ Icc 1 N, incidencePacket P (fun p => b p ^ 2) n * horizonDrift N n := by
  let G := incidencePacket P (fun p => b p ^ 2)
  have hlinear : jumpEnergy N (incidencePacket P b) =
      ∑ kn ∈ dilationPairs N, vonMangoldt kn.1 / kn.1 *
        ((G (kn.1 * kn.2) - G kn.2) / kn.2) := by
    apply sum_congr rfl
    intro kn _
    by_cases hΛ : vonMangoldt kn.1 = 0
    · simp only [hΛ, zero_div, zero_mul]
    · dsimp only [G]
      rw [incidencePacket_dilation_jump hP b (vonMangoldt_ne_zero_iff.mp hΛ),
        incidencePacket_dilation_jump hP (fun p => b p ^ 2) (vonMangoldt_ne_zero_iff.mp hΛ)]
      split_ifs <;> simp only [zero_pow (by decide : 2 ≠ 0)]
  calc
    _ = (∑ kn ∈ dilationPairs N, vonMangoldt kn.1 / kn.1 *
          (G (kn.1 * kn.2) / kn.2)) -
        ∑ kn ∈ dilationPairs N, vonMangoldt kn.1 / kn.1 * (G kn.2 / kn.2) := by
      rw [hlinear, ← sum_sub_distrib]
      exact sum_congr rfl fun kn _ => by ring
    _ = (∑ n ∈ Icc 1 N, G n * Real.log n / n) -
        ∑ n ∈ Icc 1 N, G n / n * mertensSum (N / n) := by
      rw [sum_dilation_target_eq N G, sum_dilation_source_eq N (fun n => G n / n)]
    _ = _ := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun n _ => by dsimp only [horizonDrift, G]; ring

private theorem harmonic_real_eq_sum (N : ℕ) :
    (harmonic N : ℝ) = ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

private theorem sum_multiples_horizonDrift (N d : ℕ) (hd : 0 < d) :
    (∑ n ∈ (Icc 1 N).filter (d ∣ ·), horizonDrift N n) =
      Real.log d / d * (harmonic (N / d) : ℝ) := by
  have hreindex : (∑ n ∈ (Icc 1 N).filter (d ∣ ·), horizonDrift N n) =
      ∑ j ∈ Icc 1 (N / d), horizonDrift N (d * j) := by
    refine (sum_bij' (fun j _ => d * j) (fun n _ => n / d) ?_ ?_ ?_ ?_ ?_).symm
    · intro j hj
      simp only [mem_Icc, mem_filter] at hj ⊢
      refine ⟨⟨Nat.mul_pos hd (by omega), ?_⟩, ⟨j, rfl⟩⟩
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hj.2
    · intro n hn
      simp only [mem_filter, mem_Icc] at hn ⊢
      rcases hn with ⟨⟨hn1, hnN⟩, hdn⟩
      exact ⟨Nat.div_pos (Nat.le_of_dvd hn1 hdn) hd, Nat.div_le_div_right hnN⟩
    · intro j _
      exact Nat.mul_div_cancel_left j hd
    · intro n hn
      exact (Nat.mul_comm d (n / d)).trans (Nat.div_mul_cancel (mem_filter.mp hn).2)
    · intro j _
      rfl
  have hterm (j : ℕ) (hj : j ∈ Icc 1 (N / d)) :
      horizonDrift N (d * j) = Real.log d / d * (1 / (j : ℝ)) +
        (1 / (d : ℝ)) * horizonDrift (N / d) j := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hj).1)
    dsimp only [horizonDrift]
    rw [← Nat.div_div_eq_div_mul]
    simp only [Nat.cast_mul]
    rw [Real.log_mul hdR hjR]
    field_simp
    ring
  rw [hreindex, sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← mul_sum,
    sum_horizonDrift_eq_zero, mul_zero, add_zero, ← harmonic_real_eq_sum]

/-- Every finite prime family has an exact harmonic defect diagonal, including
all higher prime-power edges and without a conductor-size restriction. -/
theorem jumpEnergy_prime_incidence_eq_harmonic_diagonal (P : Finset ℕ)
    (b : ℕ → ℝ) (hP : ∀ p ∈ P, p.Prime) (N : ℕ) :
    jumpEnergy N (incidencePacket P b) =
      ∑ p ∈ P, Real.log p / p * (harmonic (N / p) : ℝ) * b p ^ 2 := by
  rw [jumpEnergy_incidence_eq_drift P b hP N]
  simp only [incidencePacket, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  have hind : (∑ n ∈ Icc 1 N,
      ((if p ∣ n then 1 else 0) : ℝ) * horizonDrift N n) =
      Real.log p / p * (harmonic (N / p) : ℝ) := by
    calc
      _ = ∑ n ∈ (Icc 1 N).filter (p ∣ ·), horizonDrift N n := by
        rw [sum_filter]
        apply sum_congr rfl
        intro n _
        split_ifs <;> simp only [one_mul, zero_mul]
      _ = _ := sum_multiples_horizonDrift N p (hP p hp).pos
  calc
    _ = b p ^ 2 * ((∑ n ∈ Icc 1 N,
          ((if p ∣ n then 1 else 0) : ℝ) * horizonDrift N n) -
        (1 / (p : ℝ)) * (∑ n ∈ Icc 1 N, horizonDrift N n)) := by
      rw [mul_sum, ← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun n _ => by ring
    _ = _ := by rw [hind, sum_horizonDrift_eq_zero]; ring

end GaloisForLFunctions.CompletedArithmeticForms
