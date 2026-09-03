import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamare
import GaloisForLFunctions.RHTower.Sieve.DirichletBlockAbel

/-!
# Reciprocal Abel transfer for Menon's harmonic Ramaré cofactor

The exact Ramaré cofactor coefficient acquires one factor `1/n` in Menon's harmonic polynomial.
Discrete Abel summation transfers a uniform bound for every prefix of the undamped cofactor block
to the harmonic block with exactly the reciprocal of the block's left endpoint.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The harmonic Ramaré coefficient is the ordinary coefficient divided by its index. -/
theorem harmonicRamareCofactorCoeff_eq_div (P : Finset ℕ) (n : ℕ) :
    harmonicRamareCofactorCoeff P n = ramareCofactorCoeff P n / (n : ℂ) := by
  rw [harmonicRamareCofactorCoeff, harmonicMoebiusC, ramareCofactorCoeff]
  ring

/-- On a positive interval, the harmonic cofactor polynomial is the ordinary phased coefficient
weighted by `1/n`. -/
theorem logPoly_harmonicRamareCofactor_Ico_eq (P : Finset ℕ) {Y M : ℕ}
    (w : ℝ) :
    logPoly (harmonicRamareCofactorCoeff P) (Finset.Ico Y M) w =
      ∑ n ∈ Finset.Ico Y M,
        (((1 / (n : ℝ) : ℝ) : ℂ)) *
          (ramareCofactorCoeff P n * unitLogPhase w n) := by
  rw [logPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [harmonicRamareCofactorCoeff_eq_div]
  have hcast : ((((1 : ℝ) / (n : ℝ) : ℝ)) : ℂ) = 1 / (n : ℂ) := by
    apply Complex.ext <;> simp
  rw [hcast]
  rw [unitLogPhase]
  ring

/-- Reciprocal Abel transfer on an arbitrary finite interval.  A uniform bound `E` for every
ordinary cofactor prefix `[Y,m)` yields the harmonic bound `E/Y` on `[Y,M)`. -/
theorem norm_logPoly_harmonicRamareCofactor_Ico_le_of_prefix (P : Finset ℕ)
    {Y M : ℕ} (hY : 1 ≤ Y) (hYM : Y ≤ M) (w : ℝ) {E : ℝ}
    (hE : ∀ m : ℕ, Y ≤ m → m ≤ M →
      ‖logPoly (ramareCofactorCoeff P) (Finset.Ico Y m) w‖ ≤ E) :
    ‖logPoly (harmonicRamareCofactorCoeff P) (Finset.Ico Y M) w‖
      ≤ E / (Y : ℝ) := by
  let a : ℕ → ℂ := fun n => ramareCofactorCoeff P n * unitLogPhase w n
  have hprefix : ∀ m : ℕ, Y ≤ m → m ≤ M →
      ‖∑ n ∈ Finset.Ico Y m, a n‖ ≤ E := by
    intro m hmY hmM
    simpa [a, logPoly, unitLogPhase] using hE m hmY hmM
  have hanti : ∀ m : ℕ, Y ≤ m → m < M →
      (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ 1 / (m : ℝ) := by
    intro m hm _
    have hm0 : (0 : ℝ) < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < Y) hm)
    exact one_div_le_one_div_of_le hm0 (by push_cast; linarith)
  have hM0 : (0 : ℝ) ≤ (1 : ℝ) / (M : ℝ) := by positivity
  have hab := abel_block_bound a (fun n => (1 : ℝ) / (n : ℝ)) Y M hYM hM0 hanti E hprefix
  rw [logPoly_harmonicRamareCofactor_Ico_eq P w]
  refine hab.trans_eq ?_
  field_simp

/-- Closed-interval form used by common cofactor blocks. -/
theorem norm_logPoly_harmonicRamareCofactor_Icc_le_of_prefix (P : Finset ℕ)
    {Y B : ℕ} (hY : 1 ≤ Y) (hYB : Y ≤ B) (w : ℝ) {E : ℝ}
    (hE : ∀ b : ℕ, Y ≤ b → b ≤ B →
      ‖logPoly (ramareCofactorCoeff P) (Finset.Icc Y b) w‖ ≤ E) :
    ‖logPoly (harmonicRamareCofactorCoeff P) (Finset.Icc Y B) w‖
      ≤ E / (Y : ℝ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  apply norm_logPoly_harmonicRamareCofactor_Ico_le_of_prefix P hY (by omega) w
  intro m hmY hmM
  rcases Nat.eq_or_lt_of_le hmY with rfl | hm
  · rw [Finset.Ico_self, logPoly, Finset.sum_empty, norm_zero]
    have hE0 := hE Y le_rfl hYB
    exact le_trans (norm_nonneg _) hE0
  · rw [show Finset.Ico Y m = Finset.Icc Y (m - 1) by
      rw [← Finset.Ico_add_one_right_eq_Icc]
      congr
      omega]
    exact hE (m - 1) (by omega) (by omega)

end

end RHTower.Sieve
