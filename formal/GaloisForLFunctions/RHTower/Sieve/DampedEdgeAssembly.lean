import GaloisForLFunctions.RHTower.Sieve.DampedRectangleShift
import GaloisForLFunctions.RHTower.Sieve.PerronEdgeAssembly

/-!
# The damped smoothed sum, bounded by the four edges

The damped analogue of `Sieve/PerronEdgeAssembly.norm_tsum_moebius_smoothWeight_le_edges`.  Both of
its `μ`-specific inputs are now available for the damped series — the smoothed Perron formula
(`Sieve/DampedSmoothPerron`) and the rectangle identity (`Sieve/DampedRectangleShift`) — and the
combination lemma `norm_le_of_contour_edges` is generic in the four complex quantities, so the
assembly is the same.
-/

namespace RHTower.Sieve

open Finset Complex GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The smoothed damped sum as a vertical integral of `dampedInvZeta`.** -/
theorem tsum_damped_smoothWeight_eq_dampedInvZeta_integral {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) {d : ℝ} (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) := by
  rw [tsum_dampedOmegaMoebius_smoothWeight_eq_integral ht0 ht1 hN hH hd]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  have hs : 1 < ((d : ℂ) + (y : ℝ) * Complex.I).re := by rw [hre]; exact hd
  have hser := tsum_damped_eq_prod_mul_tsum_moebius hPprime ht0 ht1 hs
  have hmu : ∑' n : ℕ, twistedSummand (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
      ((d : ℂ) + (y : ℝ) * Complex.I) n
      = invZeta ((d : ℂ) + (y : ℝ) * Complex.I) := by
    rw [show (fun n : ℕ => twistedSummand (fun m => ((ArithmeticFunction.moebius m : ℤ) : ℂ))
        ((d : ℂ) + (y : ℝ) * Complex.I) n)
        = fun n : ℕ => ((ArithmeticFunction.moebius n : ℂ))
            * (n : ℂ) ^ (-((d : ℂ) + (y : ℝ) * Complex.I)) from rfl]
    exact tsum_moebius_cpow_eq_invZeta hs
  have hlhs : (∑' n : ℕ, dampedOmegaMoebius P t n
      * (n : ℂ) ^ (-((d : ℂ) + (y : ℝ) * Complex.I)))
      = ∑' n : ℕ, twistedSummand (dampedOmegaMoebius P t)
          ((d : ℂ) + (y : ℝ) * Complex.I) n := rfl
  rw [hlhs, hser, hmu, dampedInvZeta]
  ring

/-- **The damped smoothed sum, bounded by the four edges.** -/
theorem norm_tsum_damped_smoothWeight_le_edges {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T E₁ E₂ E₃ E₄ : ℝ} (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    (htrunc : ‖(∫ y : ℝ, dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T, dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
    (htop : ‖∫ x : ℝ in c..d, dampedInvZeta P t ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        * mellin (fun x' : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d, dampedInvZeta P t ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        * mellin (fun x' : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hleft : ‖∫ y : ℝ in (-T)..T, dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ E₁ + E₂ + E₃ + E₄ := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  rw [tsum_damped_smoothWeight_eq_dampedInvZeta_integral hPprime ht0 ht1 hN hH hd]
  exact norm_le_of_contour_edges
    (integral_dampedInvZetaW_vertical_sub_eq_horizontal_rect hP2 t hH hc hcd hzf)
    htrunc htop hbot hleft

end

end RHTower.Sieve
