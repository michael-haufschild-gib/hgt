import GaloisForLFunctions.HTGeometry.GaussianSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# The Hermite functions are Fourier eigenfunctions

The Fourier transform on the line has a family of eigenfunctions — the Hermite functions — with
eigenvalues the four fourth roots of unity.  Mathlib has the Gaussian's Fourier transform, the
Hermite *polynomials*, and the Schwartz space, but nowhere the eigenrelation itself; this module
supplies it.

The proof is purely operator-algebraic and needs no integral asymptotics.  Write

```text
M f = x · f,      D f = f',      A = 2π M − D
```

for coordinate multiplication, differentiation, and the **creation operator**.  On Schwartz
functions the two classical transform rules

```text
𝓕(f')(ξ) = 2πi ξ · 𝓕f(ξ)          i.e.   𝓕 D = 2πi · M 𝓕
(𝓕f)'(ξ) = 𝓕(−2πi x f)(ξ)         i.e.   D 𝓕 = −2πi · 𝓕 M
```

combine into a single intertwining relation

```text
𝓕 A = (−i) · A 𝓕,
```

because the transform exchanges the two summands of `A`, picking up opposite factors of `i` on
them.  The Gaussian is a Fourier fixed point, so iterating the relation from it gives

```text
𝓕 (Aⁿ g) = (−i)ⁿ Aⁿ g.
```

Nothing about Hermite polynomials, orthogonality, or the oscillator spectrum is used: the
eigenrelation follows from the commutation rule alone.

The relation is then transported to `L²`, which is where it is consumed: the project's `L²`
Fourier unitary is `MeasureTheory.Lp.fourierTransformₗᵢ`, and `SchwartzMap.toLp_fourier_eq` is
the bridge, so each `hermiteSchwartz n` yields an honest `L²` eigenvector of that unitary.  A
parity statement is included, since the even-index Hermite functions are the ones living in the
even subspace where the constrained prolate problem is posed.
-/

open scoped Real FourierTransform SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The two elementary operators on Schwartz space -/

theorem hasTemperateGrowth_coeReal :
    Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) :=
  Function.Complex.hasTemperateGrowth_ofReal

/-- Multiplication by the coordinate, as a continuous linear operator on Schwartz space. -/
def mulXCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

@[simp] theorem mulXCLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    mulXCLM f x = (x : ℂ) * f x := by
  rw [mulXCLM, SchwartzMap.smulLeftCLM_apply_apply hasTemperateGrowth_coeReal, smul_eq_mul]

theorem coe_mulXCLM (f : 𝓢(ℝ, ℂ)) :
    (mulXCLM f : ℝ → ℂ) = fun x : ℝ => (x : ℂ) * f x :=
  funext fun x => mulXCLM_apply f x

/-- Differentiation, as a continuous linear operator on Schwartz space. -/
def derivSCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := SchwartzMap.derivCLM ℂ ℂ

@[simp] theorem derivSCLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    derivSCLM f x = deriv (f : ℝ → ℂ) x :=
  SchwartzMap.derivCLM_apply ℂ f x

theorem coe_derivSCLM (f : 𝓢(ℝ, ℂ)) :
    (derivSCLM f : ℝ → ℂ) = deriv (f : ℝ → ℂ) :=
  funext fun x => derivSCLM_apply f x

/-! ## Integrability side conditions -/

theorem integrable_deriv_schwartz (f : 𝓢(ℝ, ℂ)) :
    Integrable (deriv (f : ℝ → ℂ)) := by
  rw [← coe_derivSCLM f]
  exact (derivSCLM f).integrable

theorem integrable_smul_id_schwartz (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => x • (f x)) := by
  have h : (fun x : ℝ => x • (f x)) = (mulXCLM f : ℝ → ℂ) := by
    rw [coe_mulXCLM]
    funext x
    rw [Complex.real_smul]
  rw [h]
  exact (mulXCLM f).integrable

/-! ## The Fourier transform as a Schwartz-space operator -/

/-- The Fourier transform as a continuous linear operator on `𝓢(ℝ, ℂ)`. -/
def fourierSCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := SchwartzMap.fourierTransformCLM ℂ

theorem fourierSCLM_eq (f : 𝓢(ℝ, ℂ)) : fourierSCLM f = 𝓕 f := rfl

theorem coe_fourierSCLM (f : 𝓢(ℝ, ℂ)) :
    (fourierSCLM f : ℝ → ℂ) = 𝓕 (f : ℝ → ℂ) := rfl

@[simp] theorem fourierSCLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    fourierSCLM f x = 𝓕 (f : ℝ → ℂ) x := rfl

/-- **Transform of a derivative:** `𝓕 f' = 2πi · x · 𝓕 f`. -/
theorem fourierSCLM_derivSCLM (f : 𝓢(ℝ, ℂ)) :
    fourierSCLM (derivSCLM f) = (2 * (π : ℂ) * I) • mulXCLM (fourierSCLM f) := by
  have h := Real.fourier_deriv (f := (f : ℝ → ℂ)) f.integrable f.differentiable
    (integrable_deriv_schwartz f)
  apply SchwartzMap.ext
  intro x
  have hl : fourierSCLM (derivSCLM f) x = 𝓕 (deriv (f : ℝ → ℂ)) x := by
    rw [fourierSCLM_apply, coe_derivSCLM]
  rw [hl, h]
  simp only [SchwartzMap.smul_apply, mulXCLM_apply, fourierSCLM_apply, smul_eq_mul]
  ring

/-- **Derivative of a transform:** `(𝓕 f)' = 𝓕 (−2πi · x · f)`. -/
theorem derivSCLM_fourierSCLM (f : 𝓢(ℝ, ℂ)) :
    derivSCLM (fourierSCLM f) = (-2 * (π : ℂ) * I) • fourierSCLM (mulXCLM f) := by
  have h := Real.deriv_fourier (f := (f : ℝ → ℂ)) f.integrable (integrable_smul_id_schwartz f)
  have hmul : fourierSCLM ((-2 * (π : ℂ) * I) • mulXCLM f)
      = (-2 * (π : ℂ) * I) • fourierSCLM (mulXCLM f) := map_smul _ _ _
  rw [← hmul]
  apply SchwartzMap.ext
  intro x
  have hl : derivSCLM (fourierSCLM f) x = deriv (𝓕 (f : ℝ → ℂ)) x := by
    rw [derivSCLM_apply, coe_fourierSCLM]
  have hfun : (((-2 * (π : ℂ) * I) • mulXCLM f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
      = fun y : ℝ => (-2 * (π : ℂ) * I * (y : ℂ)) • (f y) := by
    funext y
    simp only [SchwartzMap.smul_apply, mulXCLM_apply, smul_eq_mul]
    ring
  rw [hl, h, fourierSCLM_apply, hfun]

/-! ## The creation operator and the intertwining relation -/

/-- The **creation operator** `A f = 2πx·f − f'`. -/
def creationCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) := (2 * (π : ℂ)) • mulXCLM - derivSCLM

theorem creationCLM_eq (f : 𝓢(ℝ, ℂ)) :
    creationCLM f = (2 * (π : ℂ)) • mulXCLM f - derivSCLM f := rfl

@[simp] theorem creationCLM_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    creationCLM f x = 2 * (π : ℂ) * (x : ℂ) * f x - deriv (f : ℝ → ℂ) x := by
  rw [creationCLM_eq]
  simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, mulXCLM_apply, derivSCLM_apply,
    smul_eq_mul]
  ring

/-- **The Fourier transform intertwines the creation operator with a quarter turn:**
`𝓕 A = (−i) · A 𝓕`.  This single identity is the whole content of the eigenrelation. -/
theorem fourierSCLM_creationCLM (f : 𝓢(ℝ, ℂ)) :
    fourierSCLM (creationCLM f) = (-I) • creationCLM (fourierSCLM f) := by
  have hI : (-I) * (-2 * (π : ℂ) * I) = -(2 * (π : ℂ)) := by
    have hII : I * I = -1 := Complex.I_mul_I
    linear_combination (2 * (π : ℂ)) * hII
  have hI' : (-I) * (2 * (π : ℂ)) = -(2 * (π : ℂ) * I) := by ring
  rw [creationCLM_eq, map_sub, map_smul, fourierSCLM_derivSCLM, creationCLM_eq,
    derivSCLM_fourierSCLM, smul_sub, smul_smul, smul_smul, hI, hI', neg_smul, neg_smul,
    sub_neg_eq_add]
  abel

/-! ## The Hermite functions -/

/-- The complex Hermite function is the real profile composed with the coordinate embedding. -/
theorem coe_hermiteSchwartz (n : ℕ) :
    (hermiteSchwartz n : ℝ → ℂ)
      = fun x : ℝ => (((hermitePoly n).eval x * gaussReal x : ℝ) : ℂ) := rfl

/-- The derivative of a Hermite function is the cast of the real derivative of its profile. -/
theorem deriv_hermiteSchwartz (n : ℕ) (x : ℝ) :
    deriv (hermiteSchwartz n : ℝ → ℂ) x
      = ((deriv (fun y : ℝ => (hermitePoly n).eval y * gaussReal y) x : ℝ) : ℂ) := by
  rw [(hasDerivAt_poly_mul_gaussReal (hermitePoly n) x).deriv, coe_hermiteSchwartz]
  exact ((hasDerivAt_poly_mul_gaussReal (hermitePoly n) x).ofReal_comp).deriv

/-- **The creation operator advances the Hermite index.**  The self-dual normalization uses
`x − (1/2π) d/dx`, which is `(2π)⁻¹` times the operator `A` for which the Fourier intertwining
relation is cleanest; the two differ by a scalar, so the eigenvalue is unaffected. -/
theorem hermiteSchwartz_succ_eq (n : ℕ) :
    hermiteSchwartz (n + 1) = (2 * (π : ℂ))⁻¹ • creationCLM (hermiteSchwartz n) := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hpic : (2 * (π : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero, false_or]
    exact hpi
  apply SchwartzMap.ext
  intro x
  set p := hermitePoly n with hp
  have hreal : 2 * π * x * (p.eval x * gaussReal x)
      - deriv (fun y : ℝ => p.eval y * gaussReal y) x
      = 2 * π * ((hermiteStep p).eval x * gaussReal x) := by
    rw [← hermiteStep_apply p x]
    field_simp
  have hcast : (2 * (π : ℂ)) * (((hermiteStep p).eval x * gaussReal x : ℝ) : ℂ)
      = 2 * (π : ℂ) * (x : ℂ) * ((p.eval x * gaussReal x : ℝ) : ℂ)
        - ((deriv (fun y : ℝ => p.eval y * gaussReal y) x : ℝ) : ℂ) := by
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hreal.symm
  rw [SchwartzMap.smul_apply, creationCLM_apply, deriv_hermiteSchwartz, hermiteSchwartz_apply,
    hermiteSchwartz_apply, hermitePoly_succ, smul_eq_mul, eq_inv_mul_iff_mul_eq₀ hpic]
  exact hcast

/-- The Gaussian is a Fourier fixed point. -/
theorem fourierSCLM_gaussianSchwartz : fourierSCLM gaussianSchwartz = gaussianSchwartz :=
  fourier_gaussianSchwartz

/-- **The Hermite functions are Fourier eigenfunctions**, with eigenvalue `(−i)ⁿ`.

The classical spectral fact about the Fourier transform on the line, obtained here purely from
the intertwining relation `𝓕 A = (−i) A 𝓕` together with the Gaussian fixed point. -/
theorem fourierSCLM_hermiteSchwartz (n : ℕ) :
    fourierSCLM (hermiteSchwartz n) = (-I) ^ n • hermiteSchwartz n := by
  induction n with
  | zero =>
    rw [hermiteSchwartz_zero, pow_zero, one_smul]
    exact fourierSCLM_gaussianSchwartz
  | succ n ih =>
    rw [hermiteSchwartz_succ_eq, map_smul, fourierSCLM_creationCLM, ih, map_smul]
    simp only [smul_smul]
    congr 1
    rw [pow_succ]
    ring

/-- The pointwise form of the eigenrelation. -/
theorem fourier_hermiteSchwartz_apply (n : ℕ) (x : ℝ) :
    𝓕 (hermiteSchwartz n : ℝ → ℂ) x = (-I) ^ n * hermiteSchwartz n x := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) => g x) (fourierSCLM_hermiteSchwartz n)
  simpa [SchwartzMap.smul_apply, smul_eq_mul] using h

/-! ## Transport to `L²` -/

/-- **The Hermite functions are eigenvectors of the `L²` Fourier transform.**  This is the form
the prolate variational estimates consume: the project's `fourierUnitary` is
`MeasureTheory.Lp.fourierTransformₗᵢ`, which is exactly the transform denoted `𝓕` on `L²`. -/
theorem fourier_hermiteSchwartz_toLp (n : ℕ) :
    𝓕 ((hermiteSchwartz n).toLp 2) = (-I) ^ n • ((hermiteSchwartz n).toLp 2) := by
  rw [SchwartzMap.toLp_fourier_eq]
  have h : (𝓕 (hermiteSchwartz n) : 𝓢(ℝ, ℂ)) = (-I) ^ n • hermiteSchwartz n :=
    fourierSCLM_hermiteSchwartz n
  rw [h]
  exact map_smul (SchwartzMap.toLpCLM ℂ ℂ 2 volume) _ _

/-- The Gaussian is the `n = 0` Hermite function, so the earlier fixed-point statement is the
base case of the eigenrelation. -/
theorem fourier_hermiteSchwartz_toLp_zero :
    𝓕 ((hermiteSchwartz 0).toLp 2) = (hermiteSchwartz 0).toLp 2 := by
  rw [hermiteSchwartz_zero]
  exact fourier_gaussianSchwartz_toLp

/-! ## Parity -/

/-- Each Hermite function has the parity of its index: `hₙ(−x) = (−1)ⁿ hₙ(x)`.  In particular the
even-index Hermite functions lie in the even subspace, which is where the constrained prolate
problem is posed. -/
theorem hermiteSchwartz_comp_neg (n : ℕ) :
    (fun x : ℝ => hermiteSchwartz n (-x)) = fun x : ℝ => (-1 : ℂ) ^ n * hermiteSchwartz n x := by
  induction n with
  | zero =>
    funext x
    rw [hermiteSchwartz_zero, pow_zero, one_mul, gaussianSchwartz_apply, gaussianSchwartz_apply]
    norm_cast
    rw [gaussReal, gaussReal, neg_sq]
  | succ n ih =>
    funext x
    have hpt : hermiteSchwartz n (-x) = (-1 : ℂ) ^ n * hermiteSchwartz n x := congrFun ih x
    have hd1 : deriv (fun y : ℝ => hermiteSchwartz n (-y)) x
        = -deriv (hermiteSchwartz n : ℝ → ℂ) (-x) :=
      deriv_comp_neg (hermiteSchwartz n : ℝ → ℂ) x
    have hd2 : deriv (fun y : ℝ => hermiteSchwartz n (-y)) x
        = (-1 : ℂ) ^ n * deriv (hermiteSchwartz n : ℝ → ℂ) x := by
      rw [ih]
      exact deriv_const_mul_field _
    have hd : deriv (hermiteSchwartz n : ℝ → ℂ) (-x)
        = -((-1 : ℂ) ^ n * deriv (hermiteSchwartz n : ℝ → ℂ) x) := by
      rw [← hd2, hd1, neg_neg]
    rw [hermiteSchwartz_succ_eq, SchwartzMap.smul_apply, SchwartzMap.smul_apply,
      creationCLM_apply, creationCLM_apply, hpt, hd, pow_succ, smul_eq_mul, smul_eq_mul]
    push_cast
    ring

theorem hermiteSchwartz_neg (n : ℕ) (x : ℝ) :
    hermiteSchwartz n (-x) = (-1 : ℂ) ^ n * hermiteSchwartz n x :=
  congrFun (hermiteSchwartz_comp_neg n) x

/-- The even-index Hermite functions are even. -/
theorem hermiteSchwartz_even (k : ℕ) (x : ℝ) :
    hermiteSchwartz (2 * k) (-x) = hermiteSchwartz (2 * k) x := by
  rw [hermiteSchwartz_neg, pow_mul]
  norm_num

end GaloisForLFunctions

end
