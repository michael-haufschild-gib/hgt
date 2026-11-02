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
      rw [sum_dilation_target_eq, sum_dilation_source_eq]
    _ = _ := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun n _ => by dsimp only [horizonDrift, G]; ring

end GaloisForLFunctions.CompletedArithmeticForms
