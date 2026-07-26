import GaloisForLFunctions.HTGeometry.MomentFunctionalHaviland
import GaloisForLFunctions.RHTower.PrimeArchThetaGibbsEquipartition
import GaloisForLFunctions.RHTower.ThetaSingleGibbsEssentialMomentClosure

/-!
# Theta first-Gibbs support-Haviland universality

The exact first-Gibbs polynomial integral representation controls the full cone of polynomials
nonnegative on its positive half-line support.  This upgrades the existing square-only statement
to support-local Haviland positivity and order preservation.
-/

open Real MeasureTheory Set Polynomial

namespace RHTower

noncomputable section

/-- Full support-local Haviland positivity for the first theta Gibbs moment functional. -/
theorem momentFunctional_thetaCuspFirstAtomGibbs_nonneg_of_nonneg_on_Ioi
    (p : Polynomial ℝ) (hp : ∀ x : ℝ, 0 < x → 0 ≤ p.eval x) :
    0 ≤ HTGeometry.momentFunctional
      (fun m => thetaCuspLiouvilleGibbsMoment m 1) p := by
  rw [momentFunctional_thetaCuspFirstAtomGibbs_eq_integral]
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (hp x hx) (thetaCuspLiouvilleGibbsAtom_nonneg 1 x)

/-- The first theta Gibbs moment functional preserves pointwise polynomial order on its exact
positive half-line support. -/
theorem momentFunctional_thetaCuspFirstAtomGibbs_mono_on_Ioi
    (p q : Polynomial ℝ)
    (hpq : ∀ x : ℝ, 0 < x → p.eval x ≤ q.eval x) :
    HTGeometry.momentFunctional
        (fun m => thetaCuspLiouvilleGibbsMoment m 1) p ≤
      HTGeometry.momentFunctional
        (fun m => thetaCuspLiouvilleGibbsMoment m 1) q := by
  let s : ℕ → ℝ := fun m => thetaCuspLiouvilleGibbsMoment m 1
  have hnonneg :
      0 ≤ HTGeometry.momentFunctional s (q - p) := by
    apply momentFunctional_thetaCuspFirstAtomGibbs_nonneg_of_nonneg_on_Ioi
    intro x hx
    rw [eval_sub]
    exact sub_nonneg.mpr (hpq x hx)
  have hlin :
      HTGeometry.momentFunctional s (q - p) =
        HTGeometry.momentFunctional s q - HTGeometry.momentFunctional s p := by
    rw [sub_eq_add_neg, HTGeometry.momentFunctional_add]
    rw [show -p = (-1 : ℝ) • p by simp, HTGeometry.momentFunctional_smul]
    ring
  rw [hlin] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Exact representation, full support cone positivity, order preservation, and square positivity
for the first theta Gibbs moments. -/
structure ThetaFirstGibbsSupportHavilandCertificate : Prop where
  exactRepresentation : ∀ p : Polynomial ℝ,
    HTGeometry.momentFunctional
        (fun m => thetaCuspLiouvilleGibbsMoment m 1) p =
      ∫ x : ℝ in Ioi 0,
        p.eval x * thetaCuspLiouvilleGibbsAtom 1 x
  supportHaviland : ∀ p : Polynomial ℝ,
    (∀ x : ℝ, 0 < x → 0 ≤ p.eval x) →
      0 ≤ HTGeometry.momentFunctional
        (fun m => thetaCuspLiouvilleGibbsMoment m 1) p
  orderPreserving : ∀ p q : Polynomial ℝ,
    (∀ x : ℝ, 0 < x → p.eval x ≤ q.eval x) →
      HTGeometry.momentFunctional
          (fun m => thetaCuspLiouvilleGibbsMoment m 1) p ≤
        HTGeometry.momentFunctional
          (fun m => thetaCuspLiouvilleGibbsMoment m 1) q
  squareNonnegative : ∀ p : Polynomial ℝ,
    0 ≤ HTGeometry.momentFunctional
      (fun m => thetaCuspLiouvilleGibbsMoment m 1) (p ^ 2)

/-- **Theta first-Gibbs support-Haviland universality law.** -/
theorem thetaFirstGibbs_supportHavilandUniversality :
    ThetaFirstGibbsSupportHavilandCertificate where
  exactRepresentation := momentFunctional_thetaCuspFirstAtomGibbs_eq_integral
  supportHaviland :=
    momentFunctional_thetaCuspFirstAtomGibbs_nonneg_of_nonneg_on_Ioi
  orderPreserving :=
    momentFunctional_thetaCuspFirstAtomGibbs_mono_on_Ioi
  squareNonnegative := fun p =>
    momentFunctional_thetaCuspFirstAtomGibbs_nonneg_of_nonneg_on_Ioi
      (p ^ 2) (fun x _ => by
        rw [eval_pow]
        exact sq_nonneg _)

end

end RHTower
