import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedUniformValueTruncation
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedFiniteDetectorApproximation

/-!
# Height-uniform finite approximation to Levinson's displaced detector

Value and derivative truncation constants are chosen before the detector
parameter and height.  This is the uniform analytic input required by the
mollified mean-square step.
-/

noncomputable section

namespace RHTower

open Complex

theorem exists_norm_levinsonG_displaced_sub_finiteClassicalDetector_uniform_le
    {d eta x : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4)
    (heta : 0 < eta) (hetaq : eta ≤ 1 / 4) (hx : 0 < x) :
    ∃ (A B E K F : ℝ) (N : ℕ),
      0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ E ∧ 0 ≤ K ∧ 0 ≤ F ∧
      ∀ (lam tau : ℝ), 4 ≤ tau → ∀ L : ℕ, 1 ≤ L →
      ‖levinsonG (lam : ℂ) (displacedLinePt d tau) -
          smoothAFEZetaDisplacedFiniteClassicalDetector
            lam d x tau L‖ ≤
        (A * (L : ℝ) ^ (-1 : ℝ) +
          B * (1 + |tau|) ^ N *
            ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta))) +
        |lam| *
          (K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
            (1 + |tau|) ^ 3 *
              ((L : ℝ) ^ (-(1 / 2 + d / 2)) / (1 / 2 + d / 2))) +
          F * x ^ (d + eta) / tau ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) *
            (Real.log tau +
              (GaloisForLFunctions.digammaVerticalLogConstant +
                |Real.log Real.pi|) +
              Real.log L + 1 / tau)) := by
  obtain ⟨A, B, E, N, hA, hB, hE, hvalue⟩ :=
    exists_norm_riemannZeta_displaced_sub_finiteClassicalValue_uniform_le
      hx hd hdq heta hetaq
  obtain ⟨K, F, hK, hF, hderiv⟩ :=
    exists_norm_deriv_riemannZeta_mul_I_displaced_sub_finiteClassical_le
      hd hdq heta hetaq hx
  refine ⟨A, B, E, K, F, N, hA, hB, hE, hK, hF,
    fun lam tau htau L hL => ?_⟩
  let Z : ℂ := riemannZeta (displacedLinePt d tau)
  let Zp : ℂ := deriv riemannZeta (displacedLinePt d tau)
  let V : ℂ := smoothAFEZetaDisplacedFiniteClassicalValue d x tau L
  let H : ℂ :=
    smoothAFEZetaDisplacedFiniteClassicalHeightDerivative d x tau L
  have hvalue' :
      ‖Z - V‖ ≤
        A * (L : ℝ) ^ (-1 : ℝ) +
          B * (1 + |tau|) ^ N *
            ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta)) := by
    dsimp only [Z, V]
    exact hvalue tau L hL
  have hderiv' :
      ‖Zp * I - H‖ ≤
        K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
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
        (A * (L : ℝ) ^ (-1 : ℝ) +
          B * (1 + |tau|) ^ N *
            ((L : ℝ) ^ (-(7 / 2 : ℝ)) / (7 / 2 : ℝ)) +
          E * x ^ (d + eta) / (max 1 |tau|) ^ eta *
            (1 + (L : ℝ) ^ (1 / 2 + eta) / (1 / 2 + eta))) +
        |lam| *
          (K * ((L : ℝ) ^ (-(3 / 4 : ℝ)) / (3 / 4 : ℝ) +
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
