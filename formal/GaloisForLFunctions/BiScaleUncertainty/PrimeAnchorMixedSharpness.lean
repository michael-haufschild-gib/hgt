import GaloisForLFunctions.BiScaleUncertainty.PrimeAnchorMixedRecovery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Sharpness of terminal-prime mixed recovery

Mixed coordinates are polarizations of squared linear measurements. A
single squarefree coefficient perturbation shows that no inverse exponent
above one is possible, however small the coefficient neighborhood.
-/

open Finset Filter Topology RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
noncomputable section
set_option autoImplicit false

/-- A mixed row requires squared sums in addition to the diagonal squares. -/
theorem mixed_polarization (N p q : ℕ) (c : ℕ → ℝ) :
    2 * mixed N p c q =
      (selbergMultiplesCoord N c p + selbergMultiplesCoord N c q) ^ 2 -
        selbergMultiplesCoord N c p ^ 2 - selbergMultiplesCoord N c q ^ 2 := by
  unfold mixed
  ring

private theorem no_superlinear_scalar (A α : ℝ) (hA : 0 ≤ A) (hα : 1 < α) :
    ¬ ∃ C R : ℝ, 0 < R ∧ ∀ t : ℝ, 0 < t → t ≤ R → t ≤ C * (A*t)^α := by
  rintro ⟨C, R, hR, h⟩
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hs : ∀ᶠ t : ℝ in 𝓝[>] 0, t < R :=
    nhdsWithin_le_nhds (eventually_lt_nhds hR)
  have hp := (tendsto_rpow_neg_nhdsGT_zero (by linarith : 1-α < 0)).eventually
    (eventually_gt_atTop (C*A^α))
  obtain ⟨t, ht, hs, hp⟩ := (ht.and (hs.and hp)).exists
  have hb := h t ht hs.le
  rw [Real.mul_rpow hA ht.le] at hb
  have hdiv : t ^ (1-α) ≤ C*A^α := by
    rw [Real.rpow_sub ht, Real.rpow_one]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos ht α)).mpr
    nlinarith only [hb]
  exact hp.not_ge hdiv

/-- Exact unit perturbations exclude every superlinear local inverse modulus. -/
theorem moebius_no_superlinear_inverse {N p : ℕ} (hp : p ∈ sievePrimeTail N)
    (w : ℕ → ℝ) (α : ℝ) (hα : 1 < α) :
    ¬ ∃ C R : ℝ, 0 < R ∧ ∀ t : ℝ, 0 < t → t ≤ R →
      |unitPerturb (fun d => (μ d : ℝ) * w d) t 1 - (μ 1 : ℝ) * w 1| ≤
        C * error N p (unitPerturb (fun d => (μ d : ℝ) * w d) t)
          (fun d => (μ d : ℝ) * w d) 1 ^ α := by
  rintro ⟨C, R, hR, h⟩
  apply no_superlinear_scalar |w p / (p : ℝ)| α (abs_nonneg _) hα
  refine ⟨C, R, hR, ?_⟩
  intro t ht htR
  have hh := h t ht htR
  rcases moebius_conditioning_witness hp w t with ⟨hd, he⟩
  rw [hd, he, abs_of_pos ht] at hh
  exact hh

end
end GaloisForLFunctions.BiScaleUncertainty.PrimeAnchor
