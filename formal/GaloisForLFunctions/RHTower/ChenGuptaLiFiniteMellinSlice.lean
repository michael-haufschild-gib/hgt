/-
# Chen--Gupta--Li finite Mellin zero-detection slice

Chen--Gupta--Li equation (12.1) begins with Mellin inversion of an
exponentially smoothed Dirichlet tail. This module formalizes the exact
finite-slice version for a Dirichlet character: it needs no coefficient-growth
estimate, no zero hypothesis, and no contour shift. The subsequent shift to
the critical strip remains a separate analytic step.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiDetectorTail
import GaloisForLFunctions.RHTower.Sieve.InghamExponentialMellinInversion

open Complex LSeries DirichletCharacter
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A finite post-cutoff detector-tail slice, shifted by an arbitrary complex
argument. The support is literal, so it permits exact Mellin inversion without
any unproved global coefficient-growth bound. -/
def cglDetectorTailSlice (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : ℂ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Icc (X + 2) (N + 1) then
    cglDetectorTailCoefficient X q χ n * (n : ℂ) ^ (-s)
  else 0

/-- A positive finite support bound for literal Mellin-slice coefficients. -/
def cglDetectorTailSliceBound (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : ℂ) : ℝ :=
  1 + ∑ n ∈ Finset.Icc (X + 2) (N + 1),
    ‖cglDetectorTailCoefficient X q χ n * (n : ℂ) ^ (-s)‖

theorem cglDetectorTailSliceBound_pos (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : ℂ) : 0 < cglDetectorTailSliceBound X N q χ s := by
  unfold cglDetectorTailSliceBound
  positivity

theorem norm_cglDetectorTailSlice_le_bound (X N q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : ℂ) (n : ℕ) :
    ‖cglDetectorTailSlice X N q χ s n‖ ≤ cglDetectorTailSliceBound X N q χ s := by
  by_cases hn : n ∈ Finset.Icc (X + 2) (N + 1)
  · rw [cglDetectorTailSlice, if_pos hn]
    unfold cglDetectorTailSliceBound
    calc
      ‖cglDetectorTailCoefficient X q χ n * (n : ℂ) ^ (-s)‖ ≤
          ∑ m ∈ Finset.Icc (X + 2) (N + 1),
            ‖cglDetectorTailCoefficient X q χ m * (m : ℂ) ^ (-s)‖ := by
        exact Finset.single_le_sum
          (f := fun m => ‖cglDetectorTailCoefficient X q χ m * (m : ℂ) ^ (-s)‖)
          (fun m hm => norm_nonneg _) hn
      _ ≤ 1 + ∑ m ∈ Finset.Icc (X + 2) (N + 1),
            ‖cglDetectorTailCoefficient X q χ m * (m : ℂ) ^ (-s)‖ := by linarith
  · rw [cglDetectorTailSlice, if_neg hn]
    simpa using (cglDetectorTailSliceBound_pos X N q χ s).le

theorem cglDetectorTailSlice_zero (X N q : ℕ) (χ : DirichletCharacter ℂ (q + 1))
    (s : ℂ) : cglDetectorTailSlice X N q χ s 0 = 0 := by
  unfold cglDetectorTailSlice
  simp

/-- The literal exponential profile of finite shifted detector tail is its
finite source sum. -/
theorem coeffLaplaceProfile_cglDetectorTailSlice_eq_sum (X N q : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : ℂ) (x : ℝ) :
    coeffLaplaceProfile (cglDetectorTailSlice X N q χ s) x =
      ∑ n ∈ Finset.Icc (X + 2) (N + 1),
        (cglDetectorTailCoefficient X q χ n * (n : ℂ) ^ (-s)) *
          Complex.exp (-((n : ℝ) * x : ℝ)) := by
  unfold coeffLaplaceProfile
  rw [tsum_eq_sum (s := Finset.Icc (X + 2) (N + 1))]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [cglDetectorTailSlice, if_pos hn]
  · intro n hn
    rw [cglDetectorTailSlice, if_neg hn]
    simp

/-- **Finite Mellin detector identity.** With positive smoothing scale
`(Y+1)⁻¹`, literal exponential finite tail is inverse Mellin transform of its
Gamma-completed finite Dirichlet series on fixed line `Re(z)=2`. -/
theorem cglDetectorTailSlice_mellin_identity (X N q Y : ℕ)
    (χ : DirichletCharacter ℂ (q + 1)) (s : ℂ) :
    mellinInv 2 (fun z => Complex.Gamma z * LSeries (cglDetectorTailSlice X N q χ s) z)
      ((Y + 1 : ℕ) : ℝ)⁻¹ =
      ∑ n ∈ Finset.Icc (X + 2) (N + 1),
        (cglDetectorTailCoefficient X q χ n * (n : ℂ) ^ (-s)) *
          Complex.exp (-((n : ℝ) * ((Y + 1 : ℕ) : ℝ)⁻¹ : ℝ)) := by
  have hx : 0 < ((Y + 1 : ℕ) : ℝ)⁻¹ := by positivity
  rw [RHTower.Sieve.mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile_of_bound
    (cglDetectorTailSliceBound_pos X N q χ s)
    (norm_cglDetectorTailSlice_le_bound X N q χ s)
    (cglDetectorTailSlice_zero X N q χ s) hx]
  exact coeffLaplaceProfile_cglDetectorTailSlice_eq_sum X N q χ s _

end RHTower
