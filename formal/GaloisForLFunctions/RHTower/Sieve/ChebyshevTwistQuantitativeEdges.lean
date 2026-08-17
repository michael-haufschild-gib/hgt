import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistNoPoleShift
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity
import GaloisForLFunctions.RHTower.Sieve.VerticalMassSharp

/-!
# The quantitative edges of the twisted contour

Every edge of the twisted rectangle reduces to an untwisted edge estimate applied to a shifted
integrand.  The truncation tail is controlled by the Dirichlet series at the abscissa, which does
not see the twist at all: `‖ζ'/ζ(d + i(y+τ))‖ ≤ ∑ Λ(n) n^{-d}` uniformly in both `y` and `τ`.

The regular part is the one place the twist is felt, and only through the height at which the
zero-free region is read: a rectangle of half-height `T` centred on the twist `τ` lives at heights up
to `|τ| + T`, so the width — and with it the abscissa — is the width at that parameter.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The twisted point on a vertical line, as a translate of the untwisted one. -/
theorem twist_line_eq {d y τ : ℝ} :
    (d : ℂ) + ((y + τ : ℝ)) * Complex.I
      = (d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I := by
  push_cast
  ring

/-- **The twisted Chebyshev integrand is continuous on the Perron line.** -/
theorem continuous_neg_logDeriv_twist_line {d τ : ℝ} (hd : 1 < d) :
    Continuous fun y : ℝ =>
      -logDeriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by
  have hbase : Continuous fun u : ℝ =>
      -logDeriv riemannZeta ((d : ℂ) + (u : ℝ) * Complex.I) := by
    refine (continuous_neg_logDeriv_line hd).congr fun u => ?_
    rw [logDeriv_apply, neg_div]
  have hcomp : Continuous fun y : ℝ =>
      -logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I) :=
    hbase.comp (by fun_prop : Continuous fun y : ℝ => y + τ)
  exact hcomp.congr fun y => by rw [twist_line_eq]

/-- **The twisted Chebyshev integrand is bounded on the Perron line**, by the same series as the
untwisted one: the twist is a vertical translation and the bounding series depends on the abscissa
alone. -/
theorem norm_neg_logDeriv_twist_le_line {d y τ : ℝ} (hd : 1 < d) :
    ‖-logDeriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖
      ≤ ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d) := by
  have h := norm_neg_logDeriv_le_line (d := d) (y := y + τ) hd
  rw [neg_div] at h
  rw [← twist_line_eq, logDeriv_apply]
  exact h

/-- **The truncation error for the twisted Chebyshev Perron integral.** -/
theorem norm_truncation_error_chebyshev_twist {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {d T C : ℝ}
    (τ : ℝ) (hd : 1 < d) (hT : 1 ≤ T)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖(∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T := by
  have hfun : (fun y : ℝ => (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
      = fun y : ℝ =>
        (fun s : ℂ => -logDeriv riemannZeta (s + (τ : ℂ) * Complex.I))
            ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I) := by
    funext y
    rw [twist_line_eq]
  rw [hfun]
  refine norm_truncation_error_le (N := N) (H := H) (d := d) (T := T) (C := C)
    (M := ∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d))
    (F := fun s : ℂ => -logDeriv riemannZeta (s + (τ : ℂ) * Complex.I))
    hN hH (by linarith) hT tsum_vonMangoldt_rpow_nonneg hbd
    (continuous_neg_logDeriv_twist_line hd) (fun y => norm_neg_logDeriv_twist_le_line hd)

/-- **The twisted regular part is continuous on a zero-free segment.** -/
theorem continuousOn_zetaLogDerivRegTwist_segment {c T τ : ℝ}
    (hzu : ∀ y ∈ Set.uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 0) :
    ContinuousOn (fun y : ℝ =>
        zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      (Set.uIcc (-T) T) := by
  intro y hy
  have hinner : ContinuousAt
      (fun u : ℝ => (c : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I) y := by fun_prop
  have hcomp := (differentiableAt_zetaLogDerivReg (hzu y hy)).continuousAt.comp_of_eq hinner rfl
  exact hcomp.continuousWithinAt

/-- **The left edge of the twisted regular part.** -/
theorem norm_integral_left_vertical_zetaLogDerivRegTwist_le {N H c T C M τ : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hc0 : 0 < c) (hT : 1 ≤ T) (hM : 0 ≤ M)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    (hzu : ∀ y ∈ Set.uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 0)
    (hreg : ∀ y ∈ Set.Icc (-T) T,
      ‖zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ M) :
    ‖∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ M * (2 * ((N + H) ^ c / c) + 2 * C) :=
  norm_integral_vertical_edge_le hN hH hc0 hT hM hbd
    (F := fun s : ℂ => zetaLogDerivReg (s + (τ : ℂ) * Complex.I))
    (continuousOn_zetaLogDerivRegTwist_segment hzu) hreg

/-- **A horizontal edge of the twisted regular part.** -/
theorem norm_horizontal_edge_zetaLogDerivRegTwist_le {N H : ℝ} (j : ℕ) {c d T M C τ : ℝ}
    (hc : 0 < c) (hcd : c ≤ d) (hT : T ≠ 0) (hM : 0 ≤ M)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    (hreg : ∀ x ∈ Set.Ioc c d,
      ‖zetaLogDerivReg ((x : ℂ) + (T : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ M) :
    ‖∫ x : ℝ in c..d,
        zetaLogDerivReg ((x : ℂ) + (T : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + (T : ℝ) * Complex.I)‖
      ≤ M * C / |T| ^ (j + 1) * (d - c) :=
  norm_horizontal_edge_le j hc hcd hT hM hbd
    (F := fun s : ℂ => zetaLogDerivReg (s + (τ : ℂ) * Complex.I)) hreg

/-- **A horizontal edge of the twisted pole term.** -/
theorem norm_horizontal_edge_twistPoleInv_le {N H : ℝ} (j : ℕ) {c d T C τ : ℝ}
    (hc : 0 < c) (hcd : c ≤ d) (hT : T ≠ 0) (hτ : |T| < |τ|)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ x : ℝ in c..d,
        ((x : ℂ) + (T : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + (T : ℝ) * Complex.I)‖
      ≤ (|τ| - |T|)⁻¹ * C / |T| ^ (j + 1) * (d - c) :=
  norm_horizontal_edge_le j hc hcd hT (inv_nonneg.2 (by linarith)) hbd
    (F := fun s : ℂ => (s + (τ : ℂ) * Complex.I - 1)⁻¹)
    (fun x _ => norm_inv_shift_height_le hτ (le_refl |T|))

end RHTower.Sieve
