import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalGreen
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalTail
import GaloisForLFunctions.HTGeometry.PeriodicStripGreen
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Mixed cuspidal boundary current

This file packages the finite-deck mixed source--test boundary current and its
Green density.  The target is a genuine full cusp limit: integrability of this
current and its derivative will force the current to vanish at infinity.
-/

open UpperHalfPlane Set Filter Topology Complex MeasureTheory
open scoped ContDiff

namespace GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
open MaassCongruenceL2 SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
  SelbergMaassMean GaloisForLFunctions.HTGeometry
noncomputable section

/-- The upper boundary current pairing_modularDirichletFormClosable the actual exceptional source with a
finite-deck test form.  Retraction is fixed at height one, so this agrees with
the literal source current throughout the cusp tail. -/
def sourceTestBoundaryCurrent
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) (y : ℝ) : ℂ :=
  ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
    stripDeriv (0, 1) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q) (x, y) *
      star (retractedDeckComponent 1 F q (x, y))

private theorem sourceTestBoundaryIntegrand_continuous
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) (q : Deck N) :
    Continuous (fun p : ℝ × ℝ =>
      stripDeriv (0, 1) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q) p *
        star (retractedDeckComponent 1 F q p)) := by
  have hU := retractedSourceDeckComponent_contDiff_two N lam f (by norm_num : (0 : ℝ) < 1) q
  have hV := contDiff_retractedDeckComponent (by norm_num : (0 : ℝ) < 1) F q
  have hUy : Continuous (fun p : ℝ × ℝ =>
      stripDeriv (0, 1) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q) p) := by
    change Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q) p (0, 1))
    exact (hU.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  exact hUy.mul hV.continuous.star

/-- The mixed source--test upper current is continuous in the cusp height. -/
theorem sourceTestBoundaryCurrent_continuous
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) :
    Continuous (sourceTestBoundaryCurrent N lam f F) := by
  unfold sourceTestBoundaryCurrent
  apply continuous_finsetSum
  intro q _
  have hq := sourceTestBoundaryIntegrand_continuous N lam f F q
  have hq' : Continuous (Function.uncurry fun y x =>
      stripDeriv (0, 1) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q) (x, y) *
        star (retractedDeckComponent 1 F q (x, y))) := by
    exact hq.comp (continuous_snd.prodMk continuous_fst)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hq' 0 (N + 1 : ℝ)

/-- One finite-deck coordinate of the mixed Green density. -/
def sourceTestGreenCoordinateIntegrand
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) (q : Deck N) (p : ℝ × ℝ) : ℂ :=
    (stripDeriv (1, 0)
        (stripDeriv (1, 0)
          (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)) p *
        star (retractedDeckComponent 1 F q p) +
      stripDeriv (1, 0) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q) p *
        star (stripDeriv (1, 0) (retractedDeckComponent 1 F q) p)) +
    (stripDeriv (0, 1)
        (stripDeriv (0, 1)
          (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)) p *
        star (retractedDeckComponent 1 F q p) +
      stripDeriv (0, 1) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q) p *
        star (stripDeriv (0, 1) (retractedDeckComponent 1 F q) p))

/-- The density whose height integral is the finite-strip increment of the
mixed boundary current. -/
def sourceTestGreenDensity
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) (y : ℝ) : ℂ :=
  ∑ q : Deck N, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
    sourceTestGreenCoordinateIntegrand N lam f F q (x, y)

private theorem sourceTestGreenIntegrand_continuous
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) (q : Deck N) :
    Continuous (sourceTestGreenCoordinateIntegrand N lam f F q) := by
  unfold sourceTestGreenCoordinateIntegrand
  have hU := retractedSourceDeckComponent_contDiff_two N lam f (by norm_num : (0 : ℝ) < 1) q
  have hV := contDiff_retractedDeckComponent (by norm_num : (0 : ℝ) < 1) F q
  have hUx : Continuous (stripDeriv (1, 0)
      (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)) :=
    (contDiff_stripDeriv (1, 0) _ hU).continuous
  have hUy : Continuous (stripDeriv (0, 1)
      (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)) :=
    (contDiff_stripDeriv (0, 1) _ hU).continuous
  have hUxx : Continuous (stripDeriv (1, 0)
      (stripDeriv (1, 0)
        (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q))) := by
    change Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (stripDeriv (1, 0)
        (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)) p (1, 0))
    exact ((contDiff_stripDeriv (1, 0) _ hU).continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hUyy : Continuous (stripDeriv (0, 1)
      (stripDeriv (0, 1)
        (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q))) := by
    change Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (stripDeriv (0, 1)
        (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)) p (0, 1))
    exact ((contDiff_stripDeriv (0, 1) _ hU).continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hVx : Continuous (stripDeriv (1, 0) (retractedDeckComponent 1 F q)) := by
    change Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (retractedDeckComponent 1 F q) p (1, 0))
    exact (hV.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hVy : Continuous (stripDeriv (0, 1) (retractedDeckComponent 1 F q)) := by
    change Continuous (fun p : ℝ × ℝ =>
      fderiv ℝ (retractedDeckComponent 1 F q) p (0, 1))
    exact (hV.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  exact ((hUxx.mul hV.continuous.star).add (hUx.mul hVx.star)).add
    ((hUyy.mul hV.continuous.star).add (hUy.mul hVy.star))

private theorem sourceTestGreenCoordinateDensity_continuous
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) (q : Deck N) :
    Continuous (fun y : ℝ => ∫ x in (0 : ℝ)..(N + 1 : ℝ),
      sourceTestGreenCoordinateIntegrand N lam f F q (x, y)) := by
  let G : ℝ → ℝ → ℂ := fun y x =>
    sourceTestGreenCoordinateIntegrand N lam f F q (x, y)
  have hG : Continuous G.uncurry := by
    change Continuous (sourceTestGreenCoordinateIntegrand N lam f F q ∘
      fun p : ℝ × ℝ => (p.2, p.1))
    exact (sourceTestGreenIntegrand_continuous N lam f F q).comp
      (continuous_snd.prodMk continuous_fst)
  change Continuous fun y => ∫ x in (0 : ℝ)..(N + 1 : ℝ), G y x
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hG 0 (N + 1 : ℝ)

/-- The Green density is continuous in the cusp height. -/
theorem sourceTestGreenDensity_continuous
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) :
    Continuous (sourceTestGreenDensity N lam f F) := by
  unfold sourceTestGreenDensity
  apply continuous_finsetSum
  intro q _
  let G : ℝ → ℝ → ℂ := fun y x =>
    sourceTestGreenCoordinateIntegrand N lam f F q (x, y)
  have hG : Continuous G.uncurry := by
    change Continuous (sourceTestGreenCoordinateIntegrand N lam f F q ∘
      fun p : ℝ × ℝ => (p.2, p.1))
    exact (sourceTestGreenIntegrand_continuous N lam f F q).comp
      (continuous_snd.prodMk continuous_fst)
  change Continuous fun y => ∫ x in (0 : ℝ)..(N + 1 : ℝ), G y x
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    hG 0 (N + 1 : ℝ)

/-- On every strip above height one, the mixed Green density integrates to the
top-minus-bottom source--test current. -/
theorem sourceTestGreenDensity_increment
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (F : formPreDomain N) {c d : ℝ}
    (hhigh : ∀ y ∈ uIcc c d, 1 < y) :
    (∫ y in c..d, sourceTestGreenDensity N lam f F y) =
      sourceTestBoundaryCurrent N lam f F d - sourceTestBoundaryCurrent N lam f F c := by
  unfold sourceTestGreenDensity sourceTestBoundaryCurrent
  rw [intervalIntegral.integral_finsetSum (fun q _ =>
    (sourceTestGreenCoordinateDensity_continuous N lam f F q).intervalIntegrable c d),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  have hcont : Continuous (Function.uncurry fun x y =>
      sourceTestGreenCoordinateIntegrand N lam f F q (x, y)) := by
    change Continuous (sourceTestGreenCoordinateIntegrand N lam f F q)
    exact sourceTestGreenIntegrand_continuous N lam f F q
  calc
    (∫ y in c..d, ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        sourceTestGreenCoordinateIntegrand N lam f F q (x, y)) =
      ∫ x in (0 : ℝ)..(N + 1 : ℝ), ∫ y in c..d,
        sourceTestGreenCoordinateIntegrand N lam f F q (x, y) :=
      (intervalIntegral_intervalIntegral_swap_of_continuous hcont 0 (N + 1 : ℝ) c d).symm
    _ = (∫ x in (0 : ℝ)..(N + 1 : ℝ),
        stripDeriv (0, 1) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)
          (x, d) * star (retractedDeckComponent 1 F q (x, d))) -
      ∫ x in (0 : ℝ)..(N + 1 : ℝ),
        stripDeriv (0, 1) (retractedDeckComponent 1 (sourceInFormPreDomain N lam f) q)
          (x, c) * star (retractedDeckComponent 1 F q (x, c)) := by
        simpa only [sourceTestGreenCoordinateIntegrand] using
          retractedSource_test_periodic_strip_green N lam f F q
            (by norm_num : (0 : ℝ) < 1) hhigh

end
end GaloisForLFunctions.RHTower.MaassFiniteDeckDirichlet
