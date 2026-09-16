import GaloisForLFunctions.HTGeometry.WaveEnergyGreenIdentity
import GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus

/-!
# Complex compact Green transposition

The literal Hawking--Peierls source is complex valued.  This file supplies the
coordinatewise compact Green identity in that codomain: one derivative is
skew under the bilinear integral pairing and two equal coordinate derivatives
are self-transpose.  The compact support is required only of the test factor,
so an interior smooth causal field may be paired without any global L2 claim.
-/

open MeasureTheory
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

private theorem contDiff_coordDeriv {d : ℕ} {f : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ContDiff ℝ ∞ (ScalarTwoJet.coordDeriv i f) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- A compact complex test transfers one coordinate derivative to the other
factor with the exact minus sign. -/
theorem complex_integral_mul_coordDeriv {d : ℕ} {f g : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (i : Fin d) :
    (∫ x : Fin d → ℝ, f x * ScalarTwoJet.coordDeriv i g x) =
      -∫ x : Fin d → ℝ, ScalarTwoJet.coordDeriv i f x * g x := by
  let v : Fin d → ℝ := Pi.single i 1
  have hdf := contDiff_coordDeriv hf i
  have hdg := contDiff_coordDeriv hg i
  have hsdf : HasCompactSupport (ScalarTwoJet.coordDeriv i f) := by
    exact hfs.fderiv_apply ℝ v
  have h1 : Integrable (fun x : Fin d → ℝ => ScalarTwoJet.coordDeriv i f x * g x) :=
    (hdf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hsdf.mul_right
  have h2 : Integrable (fun x : Fin d → ℝ => f x * ScalarTwoJet.coordDeriv i g x) :=
    (hf.continuous.mul hdg.continuous).integrable_of_hasCompactSupport hfs.mul_right
  have h3 : Integrable (fun x : Fin d → ℝ => f x * g x) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfs.mul_right
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hg.differentiable (by simp) x)

/-- Two equal coordinate derivatives are self-transpose against a compact
complex test.  This is the temporal and horizontal part of the literal
compact-test wave transposition. -/
theorem complex_integral_mul_coordDeriv_two {d : ℕ} {f g : (Fin d → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfs : HasCompactSupport f) (i : Fin d) :
    (∫ x : Fin d → ℝ,
      f x * ScalarTwoJet.coordDeriv i (ScalarTwoJet.coordDeriv i g) x) =
      ∫ x : Fin d → ℝ, ScalarTwoJet.coordDeriv i (ScalarTwoJet.coordDeriv i f) x * g x := by
  have hdf := contDiff_coordDeriv hf i
  rw [complex_integral_mul_coordDeriv hf (contDiff_coordDeriv hg i) hfs i,
    complex_integral_mul_coordDeriv hdf hg (hfs.fderiv_apply ℝ (Pi.single i 1)) i]
  ring

/-- Literal one-dimensional Green transposition on a finite cutoff interval.
Unlike the compact whole-space identities above, its endpoint concomitant is
retained explicitly.  This is the radial cutoff-face form needed before any
noncompact causal limit can be asserted. -/
theorem complex_intervalIntegral_green_two {a b : ℝ}
    {u v du dv duu dvv : ℝ → ℂ}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (du x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (dv x) x)
    (hdu : ∀ x ∈ Set.uIcc a b, HasDerivAt du (duu x) x)
    (hdv : ∀ x ∈ Set.uIcc a b, HasDerivAt dv (dvv x) x)
    (hduI : IntervalIntegrable du volume a b)
    (hdvI : IntervalIntegrable dv volume a b)
    (hduuI : IntervalIntegrable duu volume a b)
    (hdvvI : IntervalIntegrable dvv volume a b) :
    (∫ x in a..b, u x * dvv x) =
      u b * dv b - u a * dv a - du b * v b + du a * v a +
        ∫ x in a..b, duu x * v x := by
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hdv hduI hdvvI
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul hdu hv hduuI hdvI
  rw [hfirst, hsecond]
  ring

/-- Literal two-coordinate Green balance on a finite rectangle.  The horizontal
and temporal boundary concomitants are deliberately kept separate: this is the
cutoff-face identity to which a causal two-leg field must be specialized before
any noncompact Peierls limit is meaningful. -/
theorem complex_rectangle_green_balance {a b c d : ℝ}
    {u v ut vt utt vtt ux vx uxx vxx : ℝ → ℝ → ℂ}
    (hux : ∀ t x, x ∈ Set.uIcc c d → HasDerivAt (fun y => u t y) (ux t x) x)
    (hvx : ∀ t x, x ∈ Set.uIcc c d → HasDerivAt (fun y => v t y) (vx t x) x)
    (huxx : ∀ t x, x ∈ Set.uIcc c d → HasDerivAt (fun y => ux t y) (uxx t x) x)
    (hvxx : ∀ t x, x ∈ Set.uIcc c d → HasDerivAt (fun y => vx t y) (vxx t x) x)
    (hut : ∀ t x, t ∈ Set.uIcc a b → HasDerivAt (fun y => u y x) (ut t x) t)
    (hvt : ∀ t x, t ∈ Set.uIcc a b → HasDerivAt (fun y => v y x) (vt t x) t)
    (hutt : ∀ t x, t ∈ Set.uIcc a b → HasDerivAt (fun y => ut y x) (utt t x) t)
    (hvtt : ∀ t x, t ∈ Set.uIcc a b → HasDerivAt (fun y => vt y x) (vtt t x) t)
    (huxI : ∀ t, IntervalIntegrable (ux t) volume c d)
    (hvxI : ∀ t, IntervalIntegrable (vx t) volume c d)
    (huxxI : ∀ t, IntervalIntegrable (uxx t) volume c d)
    (hvxxI : ∀ t, IntervalIntegrable (vxx t) volume c d)
    (hutI : ∀ x, IntervalIntegrable (fun t => ut t x) volume a b)
    (hvtI : ∀ x, IntervalIntegrable (fun t => vt t x) volume a b)
    (huttI : ∀ x, IntervalIntegrable (fun t => utt t x) volume a b)
    (hvttI : ∀ x, IntervalIntegrable (fun t => vtt t x) volume a b) :
    (∫ t in a..b, (∫ x in c..d, u t x * vxx t x) -
      ∫ x in c..d, uxx t x * v t x) -
      (∫ x in c..d, (∫ t in a..b, u t x * vtt t x) -
        ∫ t in a..b, utt t x * v t x) =
      (∫ t in a..b, u t d * vx t d - u t c * vx t c - ux t d * v t d + ux t c * v t c) -
        ∫ x in c..d, u b x * vt b x - u a x * vt a x - ut b x * v b x + ut a x * v a x := by
  have hx (t : ℝ) :
      (∫ x in c..d, u t x * vxx t x) - ∫ x in c..d, uxx t x * v t x =
        u t d * vx t d - u t c * vx t c - ux t d * v t d + ux t c * v t c := by
    have h := complex_intervalIntegral_green_two (a := c) (b := d)
      (u := fun x => u t x) (v := fun x => v t x) (du := fun x => ux t x)
      (dv := fun x => vx t x) (duu := fun x => uxx t x) (dvv := fun x => vxx t x)
      (fun x hx => hux t x hx) (fun x hx => hvx t x hx)
      (fun x hx => huxx t x hx) (fun x hx => hvxx t x hx)
      (huxI t) (hvxI t) (huxxI t) (hvxxI t)
    linear_combination h
  have ht (x : ℝ) :
      (∫ t in a..b, u t x * vtt t x) - ∫ t in a..b, utt t x * v t x =
        u b x * vt b x - u a x * vt a x - ut b x * v b x + ut a x * v a x := by
    have h := complex_intervalIntegral_green_two (a := a) (b := b)
      (u := fun t => u t x) (v := fun t => v t x) (du := fun t => ut t x)
      (dv := fun t => vt t x) (duu := fun t => utt t x) (dvv := fun t => vtt t x)
      (fun t ht => hut t x ht) (fun t ht => hvt t x ht)
      (fun t ht => hutt t x ht) (fun t ht => hvtt t x ht)
      (hutI x) (hvtI x) (huttI x) (hvttI x)
    linear_combination h
  congr 1
  · apply intervalIntegral.integral_congr
    intro t _
    exact hx t
  · apply intervalIntegral.integral_congr
    intro x _
    exact ht x

end GaloisForLFunctions.HTGeometry
