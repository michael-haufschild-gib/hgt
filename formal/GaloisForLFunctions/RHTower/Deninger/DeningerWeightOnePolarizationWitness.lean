import GaloisForLFunctions.RHTower.Deninger.DeningerWeightOnePolarization
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The polarized weight-one package is non-vacuous, with eigenvalues off the real axis

`DeningerWeightOnePolarization` is the structure from which `eigenvalue_re_eq_half` derives
Deninger's purity conclusion: every eigenvalue of the Frobenius-flow generator has real part `1/2`.
The structure is consumed there and in `DeningerClosedOperatorPolarization`, and **nothing in the
tree constructs one** — so the conclusion, however correct, rests on a package no one has exhibited.

An implication whose hypothesis has no instance proves nothing.  This file gives an instance.

On `H = EuclideanSpace ℂ (Fin 2)` take

* the quaternionic Hodge star `σ(z₀, z₁) = (−conj z₁, conj z₀)`, anti-linear with `σ² = −1`;
* the symplectic cup trace `ω(x, y) = x₀ y₁ − x₁ y₀`, nondegenerate and — as in the arithmetic
  assembly — **skew**;
* the generator `θ = (1/2 + it)·e₀ ⊕ (1/2 − it)·e₁`.

Every axiom holds for every real `t`, and `θ` has eigenvalues `1/2 ± it`.  So the package is
consistent, its conclusion is not vacuous, and it is not secretly forcing the generator to be
scalar: the witnesses realise an entire line of eigenvalue pairs on the critical line.

Two structural facts fall out of the construction and are worth stating, since both constrain any
arithmetic realisation:

* `σ² = −1` is impossible in complex dimension one, so the carrier must have even dimension;
* `θ` scalar forces its eigenvalue to be real, so a witness with `t ≠ 0` must have non-scalar `θ`.
-/

noncomputable section

open scoped ComplexConjugate
open GaloisForLFunctions.RHTower

namespace RHTower

namespace WeightOneWitness

/-- The carrier of the witness. -/
abbrev Carrier : Type := EuclideanSpace ℂ (Fin 2)

/-- The quaternionic Hodge star `(z₀, z₁) ↦ (−conj z₁, conj z₀)`. -/
def sigmaFun (z : Carrier) : Carrier :=
  WithLp.toLp 2 ![-(starRingEnd ℂ) (z 1), (starRingEnd ℂ) (z 0)]

@[simp] theorem sigmaFun_zero (z : Carrier) : sigmaFun z 0 = -(starRingEnd ℂ) (z 1) := rfl

@[simp] theorem sigmaFun_one (z : Carrier) : sigmaFun z 1 = (starRingEnd ℂ) (z 0) := rfl

/-- The Hodge star as a conjugate-linear map. -/
def sigmaMap : Carrier →ₗ⋆[ℂ] Carrier where
  toFun := sigmaFun
  map_add' x y := by
    ext i
    fin_cases i
    · simp [sigmaFun]
      ring
    · simp [sigmaFun]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [sigmaFun]

/-- The odd `K`-real structure of the witness. -/
def kreal : KRealStructure true Carrier where
  sigma := sigmaMap
  sq v := by
    ext i
    fin_cases i <;>
      simp [sigmaMap, sigmaFun, kRealParityAction]

/-- The symplectic cup trace `ω(x, y) = x₀ y₁ − x₁ y₀`. -/
def cupForm : LinearMap.BilinForm ℂ Carrier :=
  LinearMap.mk₂ ℂ (fun x y => x 0 * y 1 - x 1 * y 0)
    (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)
    (fun x y z => by simp; ring)
    (fun c x y => by simp; ring)

@[simp] theorem cupForm_apply (x y : Carrier) : cupForm x y = x 0 * y 1 - x 1 * y 0 := rfl

theorem cupForm_nondegenerate : cupForm.Nondegenerate := by
  constructor
  · intro x hx
    have h0 := hx (WithLp.toLp 2 ![1, 0])
    have h1 := hx (WithLp.toLp 2 ![0, 1])
    simp at h0 h1
    ext i
    fin_cases i
    · simpa using h1
    · simpa using h0
  · intro y hy
    have h0 := hy (WithLp.toLp 2 ![1, 0])
    have h1 := hy (WithLp.toLp 2 ![0, 1])
    simp at h0 h1
    ext i
    fin_cases i
    · simpa using h1
    · simpa using h0

/-- The Frobenius-flow generator of the witness, with eigenvalues `1/2 ± i t`. -/
def theta (t : ℝ) : Module.End ℂ Carrier where
  toFun x := WithLp.toLp 2
    ![(1 / 2 + (t : ℂ) * Complex.I) * x 0, (1 / 2 - (t : ℂ) * Complex.I) * x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

@[simp] theorem theta_apply_zero (t : ℝ) (x : Carrier) :
    theta t x 0 = (1 / 2 + (t : ℂ) * Complex.I) * x 0 := rfl

@[simp] theorem theta_apply_one (t : ℝ) (x : Carrier) :
    theta t x 1 = (1 / 2 - (t : ℂ) * Complex.I) * x 1 := rfl

/-- **The witness.**  All of Deninger's weight-one polarization axioms hold, for every real `t`. -/
def polarization (t : ℝ) : DeningerWeightOnePolarization Carrier where
  theta := theta t
  cupTrace := cupForm
  cup_nondegenerate := cupForm_nondegenerate
  star := kreal
  theta_cup x y := by
    simp only [cupForm_apply, theta_apply_zero, theta_apply_one]
    ring
  star_theta x := by
    ext i
    fin_cases i <;>
      simp only [kreal, sigmaMap, sigmaFun, theta, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one,
        map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat,
        Complex.conj_I, Complex.conj_ofReal] <;>
      ring
  inner_eq_cup_star x y := by
    simp [kreal, sigmaMap, EuclideanSpace.inner_eq_star_dotProduct]

end WeightOneWitness

end RHTower
