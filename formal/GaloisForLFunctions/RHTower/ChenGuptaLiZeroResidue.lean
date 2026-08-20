/-
# Chen--Gupta--Li detector: zero cancellation at the Mellin pole

For a certified zero in the critical strip, the Mellin integrand
`Γ(w) M_X(ρ+w,χ)L(ρ+w,χ)` has zero residue at `w = 0`.  This is the local
analytic input required before shifting the initial Mellin line in the
Chen--Gupta--Li zero-detection argument.  It proves neither a contour-shift
formula nor any zero-density estimate.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiInfiniteMellinDetector

open Complex LSeries DirichletCharacter Filter MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- A certified Dirichlet `L`-zero in the half-open critical strip.  The strip
bounds are fields of the zero datum, so every theorem below has no incoming
mathematical proposition premise. -/
structure CGLCriticalStripLZero (q : ℕ) extends CGLDirichletLZero q where
  half_le : (1 / 2 : ℝ) ≤ point.re
  lt_one : point.re < 1

/-- A certified critical-strip zero is away from the possible pole of the
Dirichlet `L`-function at `1`. -/
theorem CGLCriticalStripLZero.point_ne_one (z : CGLCriticalStripLZero q) : z.point ≠ 1 := by
  intro h
  have hreal := congrArg Complex.re h
  norm_num at hreal
  linarith [z.lt_one]

/-- The finite detector polynomial is continuous at every complex point. -/
theorem continuousAt_zeroDetectionMobiusPolynomial (X q : ℕ)
    (χ : DirichletCharacter ℂ q) (s : ℂ) :
    ContinuousAt (zeroDetectionMobiusPolynomial X q χ) s := by
  unfold zeroDetectionMobiusPolynomial
  apply Continuous.continuousAt
  apply continuous_finsetSum
  intro d hd
  have hdne : (d : ℂ) ≠ 0 := by
    have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
    exact_mod_cast (Nat.ne_of_gt hdpos)
  have hpow : Continuous (fun w : ℂ => (d : ℂ) ^ (-w)) := by
    rw [continuous_iff_continuousAt]
    intro w
    exact (continuousAt_const_cpow hdne).comp continuousAt_neg
  exact (continuous_const.mul continuous_const).mul hpow

/-- The Mellin integrand used to detect a zero after shifting the initial
line. -/
def cglDetectorMellinIntegrand (X q : ℕ) (z : CGLCriticalStripLZero q) (w : ℂ) : ℂ :=
  Complex.Gamma w *
    (zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
      DirichletCharacter.LFunction z.character (z.point + w))

/-- At a certified critical-strip zero, the would-be residue coefficient at
the Gamma pole is zero. -/
theorem cglDetectorMellinIntegrand_residueCoefficient_at_criticalZero (X q : ℕ)
    (z : CGLCriticalStripLZero q) :
    zeroDetectionMobiusPolynomial X (q + 1) z.character z.point *
      DirichletCharacter.LFunction z.character z.point = 0 := by
  rw [z.toCGLDirichletLZero.vanishes, mul_zero]

/-- **Zero cancellation at the Mellin pole.**  The apparent simple Gamma pole
at `w = 0` is cancelled at every certified critical-strip zero. -/
theorem cglDetectorMellinIntegrand_poleLimit_at_criticalZero (X q : ℕ)
    (z : CGLCriticalStripLZero q) :
    Tendsto (fun w : ℂ => w * cglDetectorMellinIntegrand X q z w)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) := by
  have hpoly : ContinuousAt (zeroDetectionMobiusPolynomial X (q + 1) z.character) z.point :=
    continuousAt_zeroDetectionMobiusPolynomial X (q + 1) z.character z.point
  have hl : ContinuousAt (DirichletCharacter.LFunction z.character) z.point :=
    (DirichletCharacter.differentiableAt_LFunction z.character z.point
      (Or.inl z.point_ne_one)).continuousAt
  have hproduct : ContinuousAt
      (fun u : ℂ => zeroDetectionMobiusPolynomial X (q + 1) z.character u *
        DirichletCharacter.LFunction z.character u) z.point := hpoly.mul hl
  have hshift : Tendsto (fun w : ℂ => z.point + w)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds z.point) := by
    have hid : Tendsto (fun w : ℂ => w) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds.add hid :
      Tendsto (fun w : ℂ => z.point + w)
        (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds (z.point + 0)))
  have hfactor : Tendsto (fun w : ℂ =>
      zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
        DirichletCharacter.LFunction z.character (z.point + w))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) := by
    have h := hproduct.tendsto.comp hshift
    rw [cglDetectorMellinIntegrand_residueCoefficient_at_criticalZero X q z] at h
    change Tendsto (fun w : ℂ =>
      zeroDetectionMobiusPolynomial X (q + 1) z.character (z.point + w) *
        DirichletCharacter.LFunction z.character (z.point + w))
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) at h
    exact h
  have hgamma : Tendsto (fun w : ℂ => w * Complex.Gamma w)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 1) :=
    Complex.tendsto_self_mul_Gamma_nhds_zero
  have h := hgamma.mul hfactor
  simpa only [cglDetectorMellinIntegrand, mul_assoc, mul_zero] using h

end RHTower
