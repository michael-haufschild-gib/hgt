import GaloisForLFunctions.RHTower.Sieve.DirichletMVTWindow
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

/-!
# Dirichlet mean value on a negative-frequency window

The direct smooth-AFE head uses `dirPoly N a (-t)`.  Coefficient conjugation reflects frequency,
so the existing arbitrary-window mean-value theorem transfers without changing coefficient energy.
-/

open Finset MeasureTheory intervalIntegral

namespace RHTower.Sieve

noncomputable section

/-- Mean-value theorem for the negative-frequency convention used by the
direct smooth-AFE head. -/
theorem dirichlet_meanValue_window_neg
    (N : ℕ) (a : Fin N → ℂ) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖dirPoly N a (-t)‖ ^ (2 : ℕ)) -
        (T₂ - T₁) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ)|
      ≤ 8 * (N : ℝ) * (1 + Real.log N) * ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
  have hpoint : ∀ t : ℝ,
      ‖dirPoly N a (-t)‖ ^ (2 : ℕ) =
        ‖dirPoly N (fun n => (starRingEnd ℂ) (a n)) t‖ ^ (2 : ℕ) := by
    intro t
    rw [dirPoly_conj_neg, RCLike.norm_conj]
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  have hbase :=
    dirichlet_meanValue_window N (fun n => (starRingEnd ℂ) (a n)) T₁ T₂
  have hcoeff :
      (∑ m : Fin N, ‖(starRingEnd ℂ) (a m)‖ ^ (2 : ℕ)) =
        ∑ m : Fin N, ‖a m‖ ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro m hm
    change ‖star (a m)‖ ^ (2 : ℕ) = _
    rw [norm_star]
  rwa [hcoeff] at hbase

end

end RHTower.Sieve
