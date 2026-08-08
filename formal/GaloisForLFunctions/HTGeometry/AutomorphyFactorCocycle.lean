import GaloisForLFunctions.HTGeometry.AlternatingHermitianDictionary

/-!
# The two-cocycle of a factor of automorphy

A nowhere-vanishing function `theta` on an additive group produces a factor of automorphy

`e (gamma, z) = theta (z + gamma) / theta z`,

which satisfies the multiplicative cocycle law formally, with no analytic input.  A logarithm `F`
of that factor, normalised by `2 pi i`, is then *quasi-additive*: it fails to be additive in the
period variable by a defect `c (gamma, gamma')` that does not depend on the base point.  Two facts
follow, and together they are the integrality half of the generalized Riemann relations.

* `isAddTwoCocycle_of_isQuasiAdditive` -- the defect is an additive two-cocycle.  This is pure
  algebra: expand `F (gamma1 + gamma2 + gamma3)` in the two possible orders and cancel.
* `exists_int_of_isQuasiAdditive_exp` -- the defect is an **integer**, because its exponential is
  the multiplicative cocycle law rearranged, hence `1`.

Feeding the result to `cocycleCommutator_isAlternatingBiadditive` and then to
`exists_hermitian_of_alternating` turns a factor of automorphy into a Hermitian form whose
imaginary part is integral on the period group.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

variable {W : Type*} [AddCommGroup W]

/-- A factor of automorphy: a family of functions satisfying the multiplicative cocycle law. -/
def IsMulTwoCocycle (e : W → W → ℂ) : Prop :=
  ∀ γ γ' z : W, e (γ + γ') z = e γ (z + γ') * e γ' z

/-- The factor of automorphy of a function. -/
noncomputable def automorphyFactor (θ : W → ℂ) (γ z : W) : ℂ := θ (z + γ) / θ z

/-- **The multiplicative cocycle law**, valid for every nowhere-vanishing function. -/
theorem automorphyFactor_add {θ : W → ℂ} (hθ : ∀ z, θ z ≠ 0) (γ γ' z : W) :
    automorphyFactor θ (γ + γ') z
      = automorphyFactor θ γ (z + γ') * automorphyFactor θ γ' z := by
  have hz : z + (γ + γ') = z + γ' + γ := by abel
  have h1 : θ (z + γ') ≠ 0 := hθ _
  have h2 : θ z ≠ 0 := hθ _
  simp only [automorphyFactor, hz]
  field_simp

theorem automorphyFactor_isMulTwoCocycle {θ : W → ℂ} (hθ : ∀ z, θ z ≠ 0) :
    IsMulTwoCocycle (automorphyFactor θ) := automorphyFactor_add hθ

theorem automorphyFactor_ne_zero {θ : W → ℂ} (hθ : ∀ z, θ z ≠ 0) (γ z : W) :
    automorphyFactor θ γ z ≠ 0 := div_ne_zero (hθ _) (hθ _)

/-- `F` is additive in the period variable up to a base-point-independent defect `c`. -/
def IsQuasiAdditive {A : Type*} [AddCommGroup A] (F : W → W → A) (c : W → W → A) : Prop :=
  ∀ γ γ' z : W, F (γ + γ') z = F γ (z + γ') + F γ' z + c γ γ'

/-- **The defect of a quasi-additive family is an additive two-cocycle.** -/
theorem isAddTwoCocycle_of_isQuasiAdditive {A : Type*} [AddCommGroup A] {F c : W → W → A}
    (h : IsQuasiAdditive F c) (z : W) : IsAddTwoCocycle c := by
  intro x y w
  have e1 : x + y + w = x + (y + w) := by abel
  have e2 : z + w + y = z + (y + w) := by abel
  have h1 := h (x + y) w z
  have h2 := h x y (z + w)
  have h3 := h x (y + w) z
  have h4 := h y w z
  rw [e1] at h1
  rw [e2] at h2
  rw [h2] at h1
  rw [h4] at h3
  have h' := h1.symm.trans h3
  have hzero : (c x y + c (x + y) w) - (c y w + c x (y + w))
      = (F x (z + (y + w)) + F y (z + w) + c x y + F w z + c (x + y) w)
        - (F x (z + (y + w)) + (F y (z + w) + F w z + c y w) + c x (y + w)) := by
    abel
  rw [← sub_eq_zero, hzero, h', sub_self]

/-- **The pointwise logarithmic defect of a factor of automorphy is an integer.**  Its exponential
is the multiplicative cocycle law rearranged, hence `1`. -/
theorem exists_int_logDefect {e : W → W → ℂ} (he : ∀ γ z, e γ z ≠ 0)
    (hcoc : IsMulTwoCocycle e) {F : W → W → ℂ}
    (hexp : ∀ γ z, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * F γ z) = e γ z) (γ γ' z : W) :
    ∃ n : ℤ, F (γ + γ') z - F γ (z + γ') - F γ' z = (n : ℂ) := by
  have hprod : Complex.exp (2 * (Real.pi : ℂ) * Complex.I
      * (F (γ + γ') z - F γ (z + γ') - F γ' z)) = 1 := by
    have hsplit : 2 * (Real.pi : ℂ) * Complex.I * (F (γ + γ') z - F γ (z + γ') - F γ' z)
        = 2 * (Real.pi : ℂ) * Complex.I * F (γ + γ') z
          - (2 * (Real.pi : ℂ) * Complex.I * F γ (z + γ')
            + 2 * (Real.pi : ℂ) * Complex.I * F γ' z) := by ring
    rw [hsplit, Complex.exp_sub, Complex.exp_add, hexp, hexp, hexp, hcoc γ γ' z]
    exact div_self (mul_ne_zero (he _ _) (he _ _))
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hprod
  refine ⟨n, ?_⟩
  have hpi : (2 : ℂ) * (Real.pi : ℂ) * Complex.I ≠ 0 := by
    have h1 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [h1, Complex.I_ne_zero]
  have hcancel : 2 * (Real.pi : ℂ) * Complex.I * (F (γ + γ') z - F γ (z + γ') - F γ' z)
      = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
    rw [hn]
    ring
  exact mul_left_cancel₀ hpi hcancel

/-- **The defect of a quasi-additive logarithm is an integer.** -/
theorem exists_int_of_isQuasiAdditive_exp {e : W → W → ℂ} (he : ∀ γ z, e γ z ≠ 0)
    (hcoc : IsMulTwoCocycle e) {F c : W → W → ℂ}
    (hexp : ∀ γ z, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * F γ z) = e γ z)
    (h : IsQuasiAdditive F c) (γ γ' z : W) :
    ∃ n : ℤ, c γ γ' = (n : ℂ) := by
  obtain ⟨n, hn⟩ := exists_int_logDefect he hcoc hexp γ γ' z
  refine ⟨n, ?_⟩
  rw [← hn]
  have := h γ γ' z
  linear_combination -this

/-- **The integral alternating form of a factor of automorphy.**  The commutator of the defect is
alternating, biadditive, and integer valued. -/
theorem automorphyFactor_commutator_int {θ : W → ℂ} (hθ : ∀ z, θ z ≠ 0) {F c : W → W → ℂ}
    (hexp : ∀ γ z, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * F γ z) = automorphyFactor θ γ z)
    (h : IsQuasiAdditive F c) (z : W) :
    IsAddTwoCocycle c ∧
    (∀ x, cocycleCommutator c x x = 0) ∧
    (∀ x y, cocycleCommutator c y x = -cocycleCommutator c x y) ∧
    (∀ x y w, cocycleCommutator c (x + y) w
      = cocycleCommutator c x w + cocycleCommutator c y w) ∧
    (∀ x y w, cocycleCommutator c x (y + w)
      = cocycleCommutator c x y + cocycleCommutator c x w) ∧
    (∀ x y, ∃ n : ℤ, cocycleCommutator c x y = (n : ℂ)) := by
  have hcoc := isAddTwoCocycle_of_isQuasiAdditive h z
  obtain ⟨h1, h2, h3, h4⟩ := cocycleCommutator_isAlternatingBiadditive hcoc
  refine ⟨hcoc, h1, h2, h3, h4, ?_⟩
  intro x y
  obtain ⟨n, hn⟩ := exists_int_of_isQuasiAdditive_exp (automorphyFactor_ne_zero hθ)
    (automorphyFactor_isMulTwoCocycle hθ) hexp h x y z
  obtain ⟨m, hm⟩ := exists_int_of_isQuasiAdditive_exp (automorphyFactor_ne_zero hθ)
    (automorphyFactor_isMulTwoCocycle hθ) hexp h y x z
  refine ⟨n - m, ?_⟩
  rw [cocycleCommutator, hn, hm]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
