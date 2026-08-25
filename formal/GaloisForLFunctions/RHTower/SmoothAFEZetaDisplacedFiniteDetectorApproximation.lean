import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFiniteDetectorDirichlet
import GaloisForLFunctions.RHTower.LevinsonDetectorFE

/-!
# Quantitative finite approximation to the displaced Levinson detector

The classical value AFE and differentiated AFE are combined with the exact
conversion from height derivative to the complex derivative.  Every direct,
reflected, conductor, and pole error remains explicit.
-/

noncomputable section

namespace RHTower

open Complex

theorem exists_norm_levinsonG_displaced_sub_finiteClassicalDetector_le
    {lam d eta x tau : ℝ} (hd : 0 < d) (hdquarter : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaquarter : eta ≤ 1 / 4)
    (hx : 0 < x) (htau : 4 ≤ tau) :
    ∃ C K E D F : ℝ,
      0 ≤ C ∧ 0 ≤ K ∧ 0 ≤ E ∧ 0 ≤ D ∧ 0 ≤ F ∧
      ∀ L : ℕ, 1 ≤ L →
      ‖levinsonG (lam : ℂ) (displacedLinePt d tau) -
          smoothAFEZetaDisplacedFiniteClassicalDetector
            lam d x tau L‖ ≤
        (C * x * ((L : ℝ) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * ((L : ℝ) ^ (-(1 / 2 + d)) / (1 / 2 + d)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta))) +
        |lam| *
          (D * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
            (1 + |tau|) ^ 3 *
              ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) +
          F * x ^ (d + eta) / tau ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
            (Real.log tau +
              (GaloisForLFunctions.digammaVerticalLogConstant +
                |Real.log Real.pi|) +
              Real.log L + 1 / tau)) := by
  have hdhalf : d < 1 / 2 := hdquarter.trans_lt (by norm_num)
  have hetaHalf : eta < 1 / 2 := hetaquarter.trans_lt (by norm_num)
  obtain ⟨C, K, E, hC, hK, hE, hvalue⟩ :=
    exists_riemannZeta_displaced_sub_two_smoothAFE_classical_heads_le
      hd.le hdhalf heta hetaHalf hd le_rfl hx tau
  obtain ⟨D, F, hD, hF, hderiv⟩ :=
    exists_norm_deriv_riemannZeta_mul_I_displaced_sub_finiteClassical_le
      hd hdquarter heta hetaquarter hx
  refine ⟨C, K, E, D, F, hC, hK, hE, hD, hF, fun L hL => ?_⟩
  let Z : ℂ := riemannZeta (displacedLinePt d tau)
  let Zp : ℂ := deriv riemannZeta (displacedLinePt d tau)
  let V : ℂ := smoothAFEZetaDisplacedFiniteClassicalValue d x tau L
  let H : ℂ :=
    smoothAFEZetaDisplacedFiniteClassicalHeightDerivative d x tau L
  have hvalue' :
      ‖Z - V‖ ≤
        C * x * ((L : ℝ) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * ((L : ℝ) ^ (-(1 / 2 + d)) / (1 / 2 + d)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) := by
    dsimp only [Z, V, smoothAFEZetaDisplacedFiniteClassicalValue]
    simpa only [smoothAFEZetaDisplacedDirectTerm,
      smoothAFEZetaDisplacedReflectedMainTerm,
      Nat.cast_add, Nat.cast_one] using
      hvalue L L hL hL
  have hderiv' :
      ‖Zp * I - H‖ ≤
        D * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
          (1 + |tau|) ^ 3 *
            ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) +
        F * x ^ (d + eta) / tau ^ eta *
          (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
          (Real.log tau +
            (GaloisForLFunctions.digammaVerticalLogConstant +
              |Real.log Real.pi|) +
            Real.log L + 1 / tau) := by
    dsimp only [Zp, H]
    exact hderiv htau L hL
  have hdecomp :
      levinsonG (lam : ℂ) (displacedLinePt d tau) -
          smoothAFEZetaDisplacedFiniteClassicalDetector lam d x tau L =
        (Z - V) + (lam : ℂ) * (-I) * (Zp * I - H) := by
    dsimp only [Z, Zp, V, H]
    unfold levinsonG smoothAFEZetaDisplacedFiniteClassicalDetector
    ring_nf
    rw [pow_two, I_mul_I]
    ring
  rw [hdecomp]
  calc
    ‖(Z - V) + (lam : ℂ) * (-I) * (Zp * I - H)‖ ≤
        ‖Z - V‖ + ‖(lam : ℂ) * (-I) * (Zp * I - H)‖ :=
      norm_add_le _ _
    _ = ‖Z - V‖ + |lam| * ‖Zp * I - H‖ := by
      rw [norm_mul, norm_mul, norm_neg, norm_I, Complex.norm_real,
        Real.norm_eq_abs]
      ring
    _ ≤
        (C * x * ((L : ℝ) ^ (-(1 / 2 - d)) / (1 / 2 - d)) +
          K * ((L : ℝ) ^ (-(1 / 2 + d)) / (1 / 2 + d)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta))) +
        |lam| *
          (D * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
            (1 + |tau|) ^ 3 *
              ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) +
          F * x ^ (d + eta) / tau ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
            (Real.log tau +
              (GaloisForLFunctions.digammaVerticalLogConstant +
                |Real.log Real.pi|) +
              Real.log L + 1 / tau)) := by
      exact add_le_add hvalue'
        (mul_le_mul_of_nonneg_left hderiv' (abs_nonneg lam))

end RHTower
