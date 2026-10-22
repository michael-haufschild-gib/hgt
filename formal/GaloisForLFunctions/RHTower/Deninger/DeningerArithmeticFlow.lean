import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticJetDuality

/-!
# Source-defined Frobenius flow

Exponentiating the entire weight-one coordinate before quotienting gives an honest complex
one-parameter group on arithmetic `H¹`:

`phi_t [F] = [exp(t(1/2 + I*z)) F]`.

This construction uses no spectral sum and no closed-operator functional calculus.  Its group law
is inherited from the exponential identity in the source algebra.  The endpoint flows are
`1` on `H⁰` and `exp(t)` on `H²`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Entire source multiplier for complex Frobenius time. -/
def deningerEntireFlowSource (t : ℂ) : DeningerEntire :=
  ⟨fun z => Complex.exp (t * (1 / 2 + Complex.I * z)), by
    change Differentiable ℂ
      (fun z => Complex.exp (t * (1 / 2 + Complex.I * z)))
    fun_prop⟩

@[simp]
theorem deningerEntireFlowSource_apply (t z : ℂ) :
    (deningerEntireFlowSource t : ℂ → ℂ) z =
      Complex.exp (t * (1 / 2 + Complex.I * z)) :=
  rfl

@[simp]
theorem deningerEntireFlowSource_zero :
    deningerEntireFlowSource 0 = 1 := by
  apply DeningerEntire.ext
  intro z
  simp [deningerEntireFlowSource_apply]

/-- Source exponential multiplication law. -/
theorem deningerEntireFlowSource_add (t u : ℂ) :
    deningerEntireFlowSource (t + u) =
      deningerEntireFlowSource t * deningerEntireFlowSource u := by
  apply DeningerEntire.ext
  intro z
  simp only [deningerEntireFlowSource_apply, deningerEntire_mul_apply]
  rw [add_mul, Complex.exp_add]

/-- Frobenius-flow multiplier class in source middle cohomology. -/
def deningerArithmeticFlowClass (t : ℂ) :
    DeningerArithmeticH1 :=
  deningerEntireH1Class (deningerEntireFlowSource t)

/-- Complexified Frobenius flow on source middle cohomology. -/
def deningerArithmeticFlow (t : ℂ) :
    Module.End ℂ DeningerArithmeticH1 :=
  LinearMap.mulLeft ℂ (deningerArithmeticFlowClass t)

@[simp]
theorem deningerArithmeticFlow_apply
    (t : ℂ) (x : DeningerArithmeticH1) :
    deningerArithmeticFlow t x =
      deningerArithmeticFlowClass t * x :=
  rfl

/-- Time zero is the identity on middle cohomology. -/
theorem deningerArithmeticFlow_zero :
    deningerArithmeticFlow 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change deningerArithmeticFlowClass 0 * x = x
  rw [deningerArithmeticFlowClass, deningerEntireFlowSource_zero,
    map_one, one_mul]

/-- Exact one-parameter group law on middle cohomology. -/
theorem deningerArithmeticFlow_add (t u : ℂ) :
    deningerArithmeticFlow (t + u) =
      (deningerArithmeticFlow t).comp
        (deningerArithmeticFlow u) := by
  apply LinearMap.ext
  intro x
  change
    deningerEntireH1Class (deningerEntireFlowSource (t + u)) * x =
      deningerEntireH1Class (deningerEntireFlowSource t) *
        (deningerEntireH1Class (deningerEntireFlowSource u) * x)
  rw [deningerEntireFlowSource_add, map_mul, mul_assoc]

/-- Endpoint flow on `H⁰`: weight zero. -/
def deningerArithmeticFlowH0 (_t : ℂ) :
    Module.End ℂ DeningerArithmeticH0 :=
  LinearMap.id

/-- Endpoint flow on `H²`: multiplication by `exp(t)`. -/
def deningerArithmeticFlowH2 (t : ℂ) :
    Module.End ℂ DeningerArithmeticH2 :=
  Complex.exp t • LinearMap.id

@[simp]
theorem deningerArithmeticFlowH0_apply
    (t : ℂ) (x : DeningerArithmeticH0) :
    deningerArithmeticFlowH0 t x = x :=
  rfl

@[simp]
theorem deningerArithmeticFlowH2_apply
    (t : ℂ) (x : DeningerArithmeticH2) :
    deningerArithmeticFlowH2 t x = Complex.exp t * x := by
  rfl

theorem deningerArithmeticFlowH0_add (t u : ℂ) :
    deningerArithmeticFlowH0 (t + u) =
      (deningerArithmeticFlowH0 t).comp
        (deningerArithmeticFlowH0 u) := by
  rfl

theorem deningerArithmeticFlowH2_add (t u : ℂ) :
    deningerArithmeticFlowH2 (t + u) =
      (deningerArithmeticFlowH2 t).comp
        (deningerArithmeticFlowH2 u) := by
  apply LinearMap.ext
  intro x
  simp only [deningerArithmeticFlowH2_apply, LinearMap.comp_apply]
  rw [Complex.exp_add]
  ring

end

end RHTower
