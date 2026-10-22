import GaloisForLFunctions.HTGeometry.FiniteGaussCutoff
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedSuccessorSource

/-! # The real-rooted minimizer of the seventh signed theta section

The positive rank-six source section fixes a monic degree-six polynomial with
six simple real roots. Its signed squared norm equals the complete native
successor integral. Nonnegativity of that norm remains the seventh-rank target.
-/

open Polynomial Set
open GaloisForLFunctions.HTGeometry
namespace RHTower
noncomputable section

/-- The monic test polynomial determined by the positive rank-six signed theta section. -/
def thetaCuspCenterMixedCutoffPolynomial (a : ℝ) : Polynomial ℝ :=
  HTGeometry.monicOrtho (thetaCuspCenterMixedSignedJet a) 6

private theorem thetaCuspCenterMixed_positive_below_six
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    HTGeometry.PositiveMomentFormBelow (thetaCuspCenterMixedSignedJet a) 6 :=
  HTGeometry.positiveMomentFormBelow_of_hankelPosDef
    (thetaCuspCenterMixedSignedHankel_six_posDef ha0 ha)

/-- The first undecided-rank polynomial already splits over the reals. -/
theorem thetaCuspCenterMixedCutoffPolynomial_splits
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedCutoffPolynomial a).Splits :=
  HTGeometry.monicOrtho_splits_at_cutoff
    (thetaCuspCenterMixed_positive_below_six ha0 ha) (n := 5) (by omega)

/-- All six real roots are simple without assuming positivity at rank seven. -/
theorem thetaCuspCenterMixedCutoffPolynomial_roots_nodup
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedCutoffPolynomial a).roots.Nodup :=
  HTGeometry.monicOrtho_roots_nodup_at_cutoff
    (thetaCuspCenterMixed_positive_below_six ha0 ha) (n := 5) (by omega)

/-- The cutoff polynomial has exactly six real roots. -/
theorem thetaCuspCenterMixedCutoffPolynomial_card_roots
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedCutoffPolynomial a).roots.card = 6 := by
  rw [← (thetaCuspCenterMixedCutoffPolynomial_splits ha0 ha).natDegree_eq_card_roots]
  exact HTGeometry.natDegree_monicOrtho_eq _ 6

/-- Its signed squared norm is precisely the remaining successor source scalar. -/
theorem thetaCuspCenterMixedCutoffPolynomial_norm_eq_schur
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    HTGeometry.momentInner (thetaCuspCenterMixedSignedJet a)
        (thetaCuspCenterMixedCutoffPolynomial a) (thetaCuspCenterMixedCutoffPolynomial a) =
      thetaCuspCenterMixedSuccessorSchur a 6 :=
  HTGeometry.monicOrtho_cutoff_norm_eq_schur
    (thetaCuspCenterMixedSignedHankel_six_posDef ha0 ha)

/-- The real-rooted cutoff polynomial retains the complete native source integral. -/
theorem thetaCuspCenterMixedCutoffPolynomial_norm_eq_integral_native
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    HTGeometry.momentInner (thetaCuspCenterMixedSignedJet a)
        (thetaCuspCenterMixedCutoffPolynomial a) (thetaCuspCenterMixedCutoffPolynomial a) =
      ∫ r : ℝ in Ioi 0, r * Real.sinh (a*r) * thetaCuspNativeSuccessorSource a 6 (r/2) := by
  rw [thetaCuspCenterMixedCutoffPolynomial_norm_eq_schur ha0 ha]
  exact thetaCuspCenterMixedSuccessorSchur_eq_integral_native ha0.le ha 6

/-- This real-rooted polynomial is the strict minimizer of the signed norm among
all other monic degree-six polynomials. -/
theorem thetaCuspCenterMixedCutoffPolynomial_norm_lt
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) {p : Polynomial ℝ}
    (hp : p.Monic) (hdeg : p.natDegree = 6)
    (hne : p ≠ thetaCuspCenterMixedCutoffPolynomial a) :
    HTGeometry.momentInner (thetaCuspCenterMixedSignedJet a)
        (thetaCuspCenterMixedCutoffPolynomial a) (thetaCuspCenterMixedCutoffPolynomial a) <
      HTGeometry.momentInner (thetaCuspCenterMixedSignedJet a) p p :=
  HTGeometry.monicOrtho_cutoff_norm_lt
    (thetaCuspCenterMixed_positive_below_six ha0 ha) hp hdeg hne

/-- The seventh section is positive semidefinite exactly when this minimal norm
is nonnegative. -/
theorem thetaCuspCenterMixedSignedHankel_seven_posSemidef_iff_cutoff_norm_nonneg
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1/2) :
    (thetaCuspCenterMixedSignedHankel a 7).PosSemidef ↔
      0 ≤ HTGeometry.momentInner (thetaCuspCenterMixedSignedJet a)
        (thetaCuspCenterMixedCutoffPolynomial a) (thetaCuspCenterMixedCutoffPolynomial a) := by
  rw [thetaCuspCenterMixedSignedHankel_seven_posSemidef_iff_nativeIntegral_nonneg ha0 ha,
    thetaCuspCenterMixedCutoffPolynomial_norm_eq_integral_native ha0 ha]

end
end RHTower
