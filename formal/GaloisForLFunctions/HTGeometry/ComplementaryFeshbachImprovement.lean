import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Complementary Feshbach improvement

Eliminating a high block measures its effect through a self-energy.  Eliminating the low block
instead gives a second exact description: the high correction is precisely the improvement over
the low-only inverse solve.  This file proves that identity for bounded operators between complex
Hilbert spaces.

No spectral or arithmetic premise is built into the definitions.  In an application, `Ainv` and
`Oinv` are the low-block and complementary-Schur inverses, while `B.adjoint` is the reverse
coupling.  The final scalar lemmas convert the operator split into an exact defect drop and the
`15/16`, `7/8`, `1/16` threshold dichotomy used by the Suzuki source audit.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-- Complementary Schur block obtained by eliminating the low coordinate. -/
def complementarySchurBlock
    (D : Y →L[ℂ] Y) (C : X →L[ℂ] Y) (Ainv : X →L[ℂ] X) (B : Y →L[ℂ] X) :
    Y →L[ℂ] Y :=
  D - C ∘L Ainv ∘L B

/-- Analysis residual left in the high coordinate by the low inverse solve. -/
def complementarySchurResidual
    (v : Y) (C : X →L[ℂ] Y) (Ainv : X →L[ℂ] X) (u : X) : Y :=
  v - C (Ainv u)

omit [CompleteSpace X] [CompleteSpace Y] in
/-- Exact complementary elimination. Solving the low block first leaves precisely the Schur
residual in the high block. -/
theorem complementarySchur_eliminate_low
    (A Ainv : X →L[ℂ] X) (B : Y →L[ℂ] X)
    (C : X →L[ℂ] Y) (D Oinv : Y →L[ℂ] Y)
    (u x : X) (v y : Y)
    (hAinv : Ainv ∘L A = 1)
    (hOinv : Oinv ∘L complementarySchurBlock D C Ainv B = 1)
    (hLow : A x + B y = u)
    (hHigh : C x + D y = v) :
    x = Ainv u - Ainv (B y) ∧
      y = Oinv (complementarySchurResidual v C Ainv u) := by
  have hAx : Ainv (A x) = x := by
    have h := DFunLike.congr_fun hAinv x
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h
  have hx : x = Ainv u - Ainv (B y) := by
    have h := congrArg Ainv hLow
    rw [map_add, hAx] at h
    rw [← h]
    abel
  have hOmega : complementarySchurBlock D C Ainv B y =
      complementarySchurResidual v C Ainv u := by
    rw [complementarySchurBlock, complementarySchurResidual,
      sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hx] at hHigh
    rw [map_sub] at hHigh
    rw [← hHigh]
    abel
  refine ⟨hx, ?_⟩
  have h := congrArg Oinv hOmega
  have hOy : Oinv (complementarySchurBlock D C Ainv B y) = y := by
    have h' := DFunLike.congr_fun hOinv y
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h'
  rw [hOy] at h
  exact h

/-- Exact complementary quadratic split.  When the off-diagonal blocks are adjoints and the low
inverse is self-adjoint, full source leverage is low leverage plus high residual pairing. -/
theorem complementarySchur_inner_split
    (Ainv : X →L[ℂ] X) (B : Y →L[ℂ] X) (C : X →L[ℂ] Y)
    (u x : X) (v y : Y)
    (hAinv : IsSelfAdjoint Ainv) (hC : C = B.adjoint)
    (hx : x = Ainv u - Ainv (B y)) :
    inner ℂ u x + inner ℂ v y =
      inner ℂ u (Ainv u) +
        inner ℂ (complementarySchurResidual v C Ainv u) y := by
  have hAadj : Ainv.adjoint = Ainv :=
    ContinuousLinearMap.isSelfAdjoint_iff'.mp hAinv
  have hcross : inner ℂ u (Ainv (B y)) = inner ℂ (C (Ainv u)) y := by
    calc
      inner ℂ u (Ainv (B y))
          = inner ℂ (Ainv u) (B y) := by
              have h := Ainv.adjoint_inner_right u (B y)
              rw [hAadj] at h
              exact h
      _ = inner ℂ (B.adjoint (Ainv u)) y :=
            (B.adjoint_inner_left y (Ainv u)).symm
      _ = inner ℂ (C (Ainv u)) y := by rw [hC]
  rw [hx, complementarySchurResidual, inner_sub_right, inner_sub_left, hcross]
  abel

/-- Full inverse quadratic-form split obtained by combining complementary elimination with the
adjoint pairing law. -/
theorem complementarySchur_inverse_inner_split
    (A Ainv : X →L[ℂ] X) (B : Y →L[ℂ] X)
    (C : X →L[ℂ] Y) (D Oinv : Y →L[ℂ] Y)
    (u x : X) (v y : Y)
    (hAinvLeft : Ainv ∘L A = 1)
    (hOinvLeft : Oinv ∘L complementarySchurBlock D C Ainv B = 1)
    (hAinvSelf : IsSelfAdjoint Ainv) (hC : C = B.adjoint)
    (hLow : A x + B y = u) (hHigh : C x + D y = v) :
    inner ℂ u x + inner ℂ v y =
      inner ℂ u (Ainv u) +
        inner ℂ (complementarySchurResidual v C Ainv u)
          (Oinv (complementarySchurResidual v C Ainv u)) := by
  obtain ⟨hx, hy⟩ := complementarySchur_eliminate_low A Ainv B C D Oinv u x v y
    hAinvLeft hOinvLeft hLow hHigh
  calc
    inner ℂ u x + inner ℂ v y =
        inner ℂ u (Ainv u) + inner ℂ (complementarySchurResidual v C Ainv u) y :=
      complementarySchur_inner_split Ainv B C u x v y hAinvSelf hC hx
    _ = inner ℂ u (Ainv u) +
        inner ℂ (complementarySchurResidual v C Ainv u)
          (Oinv (complementarySchurResidual v C Ainv u)) := by rw [hy]

omit [CompleteSpace Y] in
/-- Complementary residual pairing is nonnegative whenever the Schur block is positive and the
displayed vector is its inverse solve. -/
theorem complementarySchur_gain_nonneg
    (Omega : Y →L[ℂ] Y) (e y : Y)
    (hOmega : Omega.IsPositive) (hsolve : Omega y = e) :
    0 ≤ (inner ℂ e y).re := by
  rw [← hsolve]
  exact hOmega.re_inner_nonneg_left y

omit [CompleteSpace Y] in
/-- A positive Schur block with a right inverse has nonnegative inverse residual leverage. -/
theorem complementarySchur_inverse_gain_nonneg
    (Omega Oinv : Y →L[ℂ] Y) (e : Y)
    (hOmega : Omega.IsPositive) (hRight : Omega ∘L Oinv = 1) :
    0 ≤ (inner ℂ e (Oinv e)).re := by
  apply complementarySchur_gain_nonneg Omega e (Oinv e) hOmega
  have h := DFunLike.congr_fun hRight e
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h

/-- In leverage/defect coordinates, complementary Schur gain is exactly the low-to-full defect
drop. -/
theorem complementarySchur_gain_eq_defect_drop {full low gain : ℝ}
    (hsplit : full = low + gain) :
    gain = (1 - low) - (1 - full) := by
  linarith

/-- Numerical split behind the Route-G low-only/high-assisted alternative. -/
theorem fifteenSixteenths_lt_low_or_high {low gain : ℝ}
    (htotal : 15 / 16 < low + gain) :
    7 / 8 < low ∨ 1 / 16 < gain := by
  rcases lt_or_ge (7 / 8) low with hlow | hlow
  · exact Or.inl hlow
  · exact Or.inr (by linarith)

omit [CompleteSpace Y] in
/-- A residual inverse with norm bounded by the normalized Schur gap obeys the canonical
cross-coherence envelope. -/
theorem inverse_residual_gain_le_of_norm
    (R : Y →L[ℂ] Y) (e : Y) (tau ell rho : ℝ)
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (he : ‖e‖ ≤ Real.sqrt tau + rho * Real.sqrt ell)
    (hR : ‖R‖ ≤ (1 - rho ^ (2 : ℕ))⁻¹) :
    (inner ℂ e (R e)).re ≤
      (Real.sqrt tau + rho * Real.sqrt ell) ^ (2 : ℕ) / (1 - rho ^ (2 : ℕ)) := by
  have hden : 0 < 1 - rho ^ (2 : ℕ) := by nlinarith
  have hsum : 0 ≤ Real.sqrt tau + rho * Real.sqrt ell := by positivity
  calc
    (inner ℂ e (R e)).re ≤ ‖inner ℂ e (R e)‖ := Complex.re_le_norm _
    _ ≤ ‖e‖ * ‖R e‖ := norm_inner_le_norm _ _
    _ ≤ ‖e‖ * (‖R‖ * ‖e‖) := by
      gcongr
      exact R.le_opNorm e
    _ ≤ (Real.sqrt tau + rho * Real.sqrt ell) *
        ((1 - rho ^ (2 : ℕ))⁻¹ * (Real.sqrt tau + rho * Real.sqrt ell)) := by
      gcongr
    _ = (Real.sqrt tau + rho * Real.sqrt ell) ^ (2 : ℕ) / (1 - rho ^ (2 : ℕ)) := by
      field_simp

/-- The target constants force normalized cross-coherence square strictly above `1/15` once the
direct high-source term has vanished. -/
theorem crossCoherence_sq_gt_oneFifteenth
    {rho ell gain : ℝ}
    (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hell : ell ≤ 7 / 8)
    (hgain : 1 / 16 < gain)
    (henvelope : gain ≤ rho ^ (2 : ℕ) * ell / (1 - rho ^ (2 : ℕ))) :
    1 / 15 < rho ^ (2 : ℕ) := by
  have hden : 0 < 1 - rho ^ (2 : ℕ) := by nlinarith
  have hscaled : gain * (1 - rho ^ (2 : ℕ)) ≤ rho ^ (2 : ℕ) * ell :=
    (le_div_iff₀ hden).mp henvelope
  nlinarith

end GaloisForLFunctions.HTGeometry
