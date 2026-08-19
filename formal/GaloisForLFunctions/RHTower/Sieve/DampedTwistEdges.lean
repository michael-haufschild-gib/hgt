import GaloisForLFunctions.RHTower.Sieve.DampedTwistEdgeAssembly

/-!
# The twisted damped sum, bounded by the four edges

The damped analogue of `Sieve/MoebiusTwistEdgeAssembly.norm_tsum_moebiusTwist_smoothWeight_le_edges`.
The Perron identity is the generic one applied to `dampedTwist`, and the rectangle identity is
`Sieve/InvZetaRegular.integral_vertical_sub_eq_horizontal_rect` at the shifted integrand, whose
holomorphy is `Sieve/DampedTwistEdgeAssembly.differentiableOn_dampedInvZetaTwistW_rect`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The twisted damped smoothed sum as a shifted vertical integral.** -/
theorem tsum_dampedTwist_smoothWeight_eq_dampedInvZeta_integral {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) {d : ℝ} (hd : 1 < d) (τ : ℝ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) := by
  rw [tsum_mul_smoothWeight_eq_integral (a := dampedTwist P t τ)
    (norm_dampedTwist_le_one ht0 ht1 τ) (dampedTwist_zero P t τ) hN hH hd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  have hs : 1 < ((d : ℂ) + (y : ℝ) * Complex.I).re := by rw [hre]; exact hd
  rw [tsum_dampedTwist_cpow hPprime ht0 ht1 τ hs]

/-- **The twisted damped sum bounded by the four edges.** -/
theorem norm_tsum_dampedTwist_smoothWeight_le_edges {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) {c d T E₁ E₂ E₃ E₄ : ℝ} (τ : ℝ)
    (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0)
    (htrunc : ‖(∫ y : ℝ,
          dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T,
          dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
    (htop : ‖∫ x : ℝ in c..d,
        dampedInvZeta P t ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x' : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d,
        dampedInvZeta P t ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x' : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hleft : ‖∫ y : ℝ in (-T)..T,
        dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ E₁ + E₂ + E₃ + E₄ := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  rw [tsum_dampedTwist_smoothWeight_eq_dampedInvZeta_integral hPprime ht0 ht1 hN hH hd τ]
  exact norm_le_of_contour_edges
    (integral_vertical_sub_eq_horizontal_rect T
      (differentiableOn_dampedInvZetaTwistW_rect hP2 t τ hH hc hcd hT hzf))
    htrunc htop hbot hleft

end

end RHTower.Sieve
