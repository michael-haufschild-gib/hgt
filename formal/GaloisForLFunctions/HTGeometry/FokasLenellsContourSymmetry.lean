import GaloisForLFunctions.HTGeometry.FokasLenellsGlobalSmallScattering
import GaloisForLFunctions.HTGeometry.FokasLenellsScatteringChannels

/-!
# Pauli transport across all four Fokas–Lenells spectral rays

The contour in arXiv:2607.19649 is `Im(k²)=0`. Its four nonzero rays are
parameterized without any nonvanishing premise. The Pauli matrices already
present in the interaction corpus transport the original Lax equation and
its free phases to each ray. Imaginary rays use the exact potential transform
`q(x) ↦ I*q(-x)`, whose square is scalar negation.

The positive control density is reflected by this transform, hence its mass
and the global potential normalization are invariant. One fixed rescaled
potential therefore works on all four rays. The contour exhaustion theorem
records the degenerate origin separately.
-/

open Complex Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Reflection and multiplication by `I` rotate the original spectral problem onto its imaginary rays. -/
def twistedPotential (q : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  I • RHTower.negSchwartz' q

@[simp] theorem twistedPotential_apply (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    twistedPotential q x = I*q (-x) := by simp [twistedPotential, RHTower.negSchwartz'_apply]

theorem twistedPotential_deriv (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (twistedPotential q) x = I*reflectedDerivative q x := by
  have he : (twistedPotential q : ℝ → ℂ) = fun x => I*q (-x) := funext (twistedPotential_apply q)
  rw [he, deriv_const_mul_field, reflectedDerivative_apply]

theorem twistedPotential_reflectedDerivative (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    reflectedDerivative (twistedPotential q) x = I*deriv q x := by
  rw [reflectedDerivative_apply]
  have he : (fun y : ℝ => twistedPotential q (-y)) = fun y => I*q y := by
    funext y
    simp
  rw [he, deriv_const_mul_field]

/-- The transformation has fourth order; its square is scalar negation. -/
theorem twistedPotential_twice (q : SchwartzMap ℝ ℂ) : twistedPotential (twistedPotential q) = -q := by
  ext x
  simp [← mul_assoc]

def contourSource (q : SchwartzMap ℝ ℂ) (vertical : Bool) : SchwartzMap ℝ ℂ :=
  if vertical then twistedPotential q else q

/-- Pauli conjugations give all four nonzero rays of the continuous spectrum. -/
def contourConjugator (vertical negative : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  if vertical then
    if negative then _root_.HTGeometry.ConstraintRelativity.pauliY
    else _root_.HTGeometry.ConstraintRelativity.pauliX
  else
    if negative then _root_.HTGeometry.ConstraintRelativity.pauliZ else 1

def contourParameter (vertical negative : Bool) (κ : ℝ) : ℂ :=
  (if negative then -1 else 1)*(if vertical then I else 1)*(Real.exp κ : ℂ)

def contourSquaredParameter (vertical : Bool) (κ : ℝ) : ℝ :=
  if vertical then -(Real.exp κ)^2 else (Real.exp κ)^2

theorem contourConjugator_square (vertical negative : Bool) :
    contourConjugator vertical negative*contourConjugator vertical negative = 1 := by
  cases vertical <;> cases negative <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [contourConjugator, _root_.HTGeometry.ConstraintRelativity.pauliX,
      _root_.HTGeometry.ConstraintRelativity.pauliY, _root_.HTGeometry.ConstraintRelativity.pauliZ,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem contourParameter_square (vertical negative : Bool) (κ : ℝ) :
    contourParameter vertical negative κ^2 = (contourSquaredParameter vertical κ : ℂ) := by
  cases vertical <;> cases negative <;>
    simp [contourParameter, contourSquaredParameter, mul_pow]

theorem contourParameter_norm (vertical negative : Bool) (κ : ℝ) :
    ‖contourParameter vertical negative κ‖ = Real.exp κ := by
  cases vertical <;> cases negative <;>
    simp [contourParameter]

theorem contourParameter_ne_zero (vertical negative : Bool) (κ : ℝ) :
    contourParameter vertical negative κ ≠ 0 := by
  apply norm_pos_iff.mp
  rw [contourParameter_norm]
  exact Real.exp_pos _

/-- Every constructed ray lies on `Im(k²)=0`, the contour in Section 2.2. -/
theorem contourParameter_square_im (vertical negative : Bool) (κ : ℝ) :
    (contourParameter vertical negative κ^2).im = 0 := by
  rw [contourParameter_square]
  rfl

/-- Exact original Lax covariance; imaginary rays use the transformed potential. -/
theorem spatialLax_contour_conjugation (q : SchwartzMap ℝ ℂ) (vertical negative : Bool)
    (κ x : ℝ) :
    spatialLax (deriv q x) (reflectedDerivative q x) (contourParameter vertical negative κ) =
      contourConjugator vertical negative*
        spatialLax (deriv (contourSource q vertical) x)
          (reflectedDerivative (contourSource q vertical) x) (Complex.exp (κ:ℂ))*
        contourConjugator vertical negative := by
  cases vertical <;> cases negative <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [contourSource, contourParameter, contourConjugator, spatialLax,
      twistedPotential_deriv, twistedPotential_reflectedDerivative, ← Complex.ofReal_exp,
      _root_.HTGeometry.ConstraintRelativity.pauliX, _root_.HTGeometry.ConstraintRelativity.pauliY,
      _root_.HTGeometry.ConstraintRelativity.pauliZ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp

/-- The same Pauli conjugation transports the free spatial phases. -/
theorem diagonalFrame_contour_conjugation (vertical negative : Bool) (κ x : ℝ) :
    diagonalFrame (contourSquaredParameter vertical κ) x =
      contourConjugator vertical negative*diagonalFrame ((Real.exp κ)^2) x*
        contourConjugator vertical negative := by
  cases vertical <;> cases negative <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [contourConjugator, contourSquaredParameter, diagonalFrame,
      _root_.HTGeometry.ConstraintRelativity.pauliX, _root_.HTGeometry.ConstraintRelativity.pauliY,
      _root_.HTGeometry.ConstraintRelativity.pauliZ, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp

/-- The four rays exhaust the nonzero contour; the origin is recorded separately. -/
theorem contourParameter_exhaustive (k : ℂ) :
    (k^2).im = 0 ↔ k = 0 ∨ ∃ vertical negative κ, k = contourParameter vertical negative κ := by
  constructor
  · intro hk
    have hri : k.re = 0 ∨ k.im = 0 := by
      have he : 2*k.re*k.im = 0 := by
        rw [pow_two, Complex.mul_im] at hk
        nlinarith
      rcases mul_eq_zero.mp he with he | he
      · exact Or.inl ((mul_eq_zero.mp he).resolve_left (by positivity))
      · exact Or.inr he
    by_cases hz : k = 0
    · exact Or.inl hz
    · right
      rcases hri with hr | hi
      · have hn : k.im ≠ 0 := by
          intro hi
          apply hz
          exact Complex.ext (by simpa using hr) (by simpa using hi)
        by_cases hs : 0 < k.im
        · refine ⟨true,false,Real.log k.im,?_⟩
          apply Complex.ext <;> simp [contourParameter, Real.exp_log hs, hr]
        · have hs' : 0 < -k.im := by rcases lt_or_gt_of_ne hn with h | h <;> linarith
          refine ⟨true,true,Real.log (-k.im),?_⟩
          dsimp only [contourParameter]
          rw [Real.exp_log hs']
          apply Complex.ext <;> simp [hr]
      · have hn : k.re ≠ 0 := by
          intro hr
          apply hz
          exact Complex.ext (by simpa using hr) (by simpa using hi)
        by_cases hs : 0 < k.re
        · refine ⟨false,false,Real.log k.re,?_⟩
          apply Complex.ext <;> simp [contourParameter, Real.exp_log hs, hi]
        · have hs' : 0 < -k.re := by rcases lt_or_gt_of_ne hn with h | h <;> linarith
          refine ⟨false,true,Real.log (-k.re),?_⟩
          dsimp only [contourParameter]
          rw [Real.exp_log hs']
          apply Complex.ext <;> simp [hi]
  · rintro (rfl | ⟨vertical,negative,κ,rfl⟩)
    · simp
    · exact contourParameter_square_im vertical negative κ

theorem twistedPotential_second_deriv (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    deriv (deriv (twistedPotential q)) x = I*deriv (deriv q) (-x) := by
  have he : deriv (twistedPotential q) = fun y => -I*deriv q (-y) := by
    funext y
    simp [twistedPotential_deriv, reflectedDerivative, RHTower.negSchwartz'_apply,
      SchwartzMap.derivCLM_apply]
  rw [he, deriv_const_mul_field, deriv_comp_neg]
  ring

/-- The positive effective-potential majorant is exactly reflected by the imaginary-ray twist. -/
theorem twistedPotential_controlDensity (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    effectiveControlDensity (SchwartzMap.derivCLM ℂ ℂ (twistedPotential q))
      (reflectedDerivative (twistedPotential q))
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (twistedPotential q))) x =
    effectiveControlDensity (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) (-x) := by
  have hd (r : SchwartzMap ℝ ℂ) (y : ℝ) :
      SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ r) y = deriv (deriv r) y := by
    have he : (SchwartzMap.derivCLM ℂ ℂ r : ℝ → ℂ) = deriv r :=
      funext (SchwartzMap.derivCLM_apply ℂ r)
    rw [SchwartzMap.derivCLM_apply, he]
  simp [effectiveControlDensity, hd, SchwartzMap.derivCLM_apply,
    twistedPotential_deriv, twistedPotential_second_deriv,
    reflectedDerivative, RHTower.negSchwartz'_apply]

theorem twistedPotential_controlMass (q : SchwartzMap ℝ ℂ) :
    effectiveControlMass (SchwartzMap.derivCLM ℂ ℂ (twistedPotential q))
      (reflectedDerivative (twistedPotential q))
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ (twistedPotential q))) =
    effectiveControlMass (SchwartzMap.derivCLM ℂ ℂ q) (reflectedDerivative q)
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ q)) := by
  simp only [effectiveControlMass, twistedPotential_controlDensity]
  exact MeasureTheory.integral_neg_eq_self _ MeasureTheory.volume

theorem globalScatteringScale_twistedPotential (q : SchwartzMap ℝ ℂ) :
    globalScatteringScale (twistedPotential q) = globalScatteringScale q := by
  simp only [globalScatteringScale, twistedPotential_controlMass]

theorem twistedPotential_smul (q : SchwartzMap ℝ ℂ) (c : ℂ) :
    twistedPotential (c • q) = c • twistedPotential q := by
  ext x
  simp
  ring

/-- One normalization works on real and imaginary rays because it commutes with the twist. -/
theorem globalSmallScatteringPotential_twisted (q : SchwartzMap ℝ ℂ) :
    globalSmallScatteringPotential (twistedPotential q) = twistedPotential (globalSmallScatteringPotential q) := by
  simp only [globalSmallScatteringPotential, globalScatteringScale_twistedPotential, twistedPotential_smul]

theorem contourSource_globalSmall (q : SchwartzMap ℝ ℂ) (vertical : Bool) :
    contourSource (globalSmallScatteringPotential q) vertical = globalSmallScatteringPotential (contourSource q vertical) := by
  cases vertical
  · rfl
  · exact (globalSmallScatteringPotential_twisted q).symm

end
end GaloisForLFunctions.HTGeometry.FokasLenells
