import GaloisForLFunctions.RHTower.QuadraticScaleSpectralRH
import GaloisForLFunctions.RHTower.WeightOneCliffordPositiveClosure

/-!
# The weight-one inversion produces a source Clifford--Dirac square

Center the scale generator `D = t d/dt` at the fixed point of functional-equation reflection:
`C = D + 1/2`.  The exact source identity `J D J = -(D+1)` for the weight-one inversion gives
`C J = -J C`.  Thus, for every real coupling `a`, the static source operator

`Q_a = C + a J`

has the Clifford square `Q_a^2 = C^2 + a^2`.  This file proves the anticommutation and square on
smooth real scale profiles without referring to Xi zeros.  It also records the Mellin symbol
`a^2 + (w-1/2)^2`; reality of this symbol at every Xi zero is exactly the existing quadratic-scale
RH criterion.

The closed positive-ray realization, exact transported `H¹/H²` domains, physical inversion
formula, natural square, and self-adjoint square are supplied by
`WeightOneCliffordPositiveClosure`. The remaining arithmetic problem is to identify a source
spectral determinant or scattering denominator with Xi in this quadratic parameter.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- The centered scale generator `C = D + 1/2`. -/
def centeredScaleGenerator (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  multiplicativeDeriv f t + (1 / 2 : ℝ) * f t

/-- The source Clifford--Dirac expression `Q_a = C + aJ`. -/
def weightOneCliffordDirac (a : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  centeredScaleGenerator f t + a * weightOneInversion f t

theorem centeredScaleGenerator_add {f g : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    centeredScaleGenerator (fun x => f x + g x) t =
      centeredScaleGenerator f t + centeredScaleGenerator g t := by
  have hderiv : deriv (fun x => f x + g x) t = deriv f t + deriv g t :=
    (hf.hasDerivAt.add hg.hasDerivAt).deriv
  rw [centeredScaleGenerator, centeredScaleGenerator, centeredScaleGenerator,
    multiplicativeDeriv, multiplicativeDeriv, multiplicativeDeriv, hderiv]
  ring

theorem centeredScaleGenerator_const_mul {f : ℝ → ℝ} {a t : ℝ}
    (hf : DifferentiableAt ℝ f t) :
    centeredScaleGenerator (fun x => a * f x) t =
      a * centeredScaleGenerator f t := by
  rw [centeredScaleGenerator, centeredScaleGenerator,
    multiplicativeDeriv, multiplicativeDeriv,
    (hf.hasDerivAt.const_mul a).deriv]
  ring

/-- **Source Clifford anticommutation.**  Centering removes the affine shift in
`JDJ = -(D+1)`, so the scale generator becomes exactly odd under the inversion. -/
theorem centeredScaleGenerator_weightOneInversion {f : ℝ → ℝ} {t : ℝ}
    (ht : t ≠ 0) (hf : DifferentiableAt ℝ f t⁻¹) :
    centeredScaleGenerator (weightOneInversion f) t =
      -weightOneInversion (centeredScaleGenerator f) t := by
  rw [centeredScaleGenerator,
    multiplicativeDeriv_weightOneInversion ht hf]
  unfold weightOneInversion centeredScaleGenerator
  ring

theorem weightOneInversion_add (f g : ℝ → ℝ) (t : ℝ) :
    weightOneInversion (fun x => f x + g x) t =
      weightOneInversion f t + weightOneInversion g t := by
  unfold weightOneInversion
  ring

theorem weightOneInversion_const_mul (a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    weightOneInversion (fun x => a * f x) t =
      a * weightOneInversion f t := by
  unfold weightOneInversion
  ring

/-- **The explicit source Dirac square.**  The mixed terms in `(C+aJ)^2` cancel pointwise on
smooth scale profiles, leaving `C^2+a^2`. -/
theorem weightOneCliffordDirac_sq
    (a : ℝ) (f : ℝ → ℝ) {t : ℝ} (ht : t ≠ 0)
    (hf : Differentiable ℝ f)
    (hDf : Differentiable ℝ (multiplicativeDeriv f)) :
    weightOneCliffordDirac a (weightOneCliffordDirac a f) t =
      centeredScaleGenerator (centeredScaleGenerator f) t + a ^ 2 * f t := by
  have hCf : DifferentiableAt ℝ (centeredScaleGenerator f) t := by
    unfold centeredScaleGenerator
    fun_prop
  have hJf : DifferentiableAt ℝ (weightOneInversion f) t :=
    (hasDerivAt_weightOneInversion ht (hf t⁻¹).hasDerivAt).differentiableAt
  unfold weightOneCliffordDirac
  rw [centeredScaleGenerator_add hCf
      ((hJf.hasDerivAt.const_mul a).differentiableAt),
    centeredScaleGenerator_const_mul hJf,
    centeredScaleGenerator_weightOneInversion ht (hf t⁻¹),
    weightOneInversion_add,
    weightOneInversion_const_mul,
    weightOneInversion_weightOneInversion f ht]
  ring

/-- The Mellin-symbol energy of the weight-one Clifford square. -/
def weightOneCliffordEnergy (a : ℝ) (w : ℂ) : ℂ :=
  (a : ℂ) ^ 2 + (w - 1 / 2) ^ 2

/-- The Clifford energy is a real affine transform of the Berry--Keating coordinate. -/
theorem weightOneCliffordEnergy_eq_berryKeatingU (a : ℝ) (w : ℂ) :
    weightOneCliffordEnergy a w =
      ((a ^ 2 + 1 / 4 : ℝ) : ℂ) - berryKeatingU w := by
  rw [weightOneCliffordEnergy, berryKeatingU_eq_centered]
  push_cast
  ring

/-- Reality of the weight-one Clifford-square spectral parameter at every Xi zero. -/
def XiWeightOneCliffordSpectralReality (a : ℝ) : Prop :=
  ∀ ρ : ℂ, xi ρ = 0 → (weightOneCliffordEnergy a ρ).im = 0

theorem xiWeightOneCliffordSpectralReality_iff_quadratic (a : ℝ) :
    XiWeightOneCliffordSpectralReality a ↔ XiQuadraticSpectralReality := by
  constructor
  · intro h ρ hρ
    have hr := h ρ hρ
    rw [weightOneCliffordEnergy_eq_berryKeatingU] at hr
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at hr
    exact neg_eq_zero.mp hr
  · intro h ρ hρ
    have hr := h ρ hρ
    rw [weightOneCliffordEnergy_eq_berryKeatingU]
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub]
    exact neg_eq_zero.mpr hr

/-- The right end of the source Clifford--Dirac detour is exact: reality of its quadratic Mellin
symbol at every Xi zero is equivalent to RH, for every real coupling. -/
theorem xiWeightOneCliffordSpectralReality_iff_riemannHypothesis (a : ℝ) :
    XiWeightOneCliffordSpectralReality a ↔ RiemannHypothesis :=
  (xiWeightOneCliffordSpectralReality_iff_quadratic a).trans
    xiQuadraticSpectralReality_iff_riemannHypothesis

end


end RHTower
