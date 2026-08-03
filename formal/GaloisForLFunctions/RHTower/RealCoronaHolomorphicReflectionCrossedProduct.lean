import GaloisForLFunctions.RHTower.RealCoronaEndpointHolomorphicSmoothness

/-!
# Holomorphic reflection crossed product for the Real corona

This file constructs the actual order-two action omitted by a coefficient-only smoothness
statement.  `ReflectionParity` is the two-element group.  A holomorphic involution of an endpoint
domain preserving the complete divisor induces an action by algebra automorphisms on divisor
functions, preserves the endpoint-holomorphic dense subalgebra, and hence produces its honest skew
crossed product.

When reflection exchanges upper and lower sectors, it sends the corona idempotent to its
complement.  The final theorem combines this action with the endpoint classification: the
degree-zero Real-corona idempotent lifts through the smooth crossed-product inclusion exactly when
both sectors are finite.
-/

noncomputable section

open Set

namespace GaloisForLFunctions.RHTower

/-- Multiplicative parity group with one nontrivial reflection. -/
inductive ReflectionParity
  | even
  | odd
  deriving DecidableEq, Fintype

namespace ReflectionParity

/-- Multiplication law of the order-two reflection group. -/
def mul : ReflectionParity → ReflectionParity → ReflectionParity
  | even, q => q
  | odd, even => odd
  | odd, odd => even

instance : Group ReflectionParity where
  one := even
  mul := mul
  inv := id
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  inv_mul_cancel a := by cases a <;> rfl

@[simp] theorem one_eq : (1 : ReflectionParity) = even := rfl
@[simp] theorem even_mul (q) : mul even q = q := rfl
@[simp] theorem odd_mul_even : mul odd even = odd := rfl
@[simp] theorem odd_mul_odd : mul odd odd = even := rfl

end ReflectionParity

/-- A holomorphic involution of the endpoint domain which preserves the complete divisor. -/
structure HolomorphicDivisorReflection (U Z : Set ℂ) where
  rho : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ rho U
  mapsToU : MapsTo rho U U
  mapsToZ : MapsTo rho Z Z
  involutive : Function.Involutive rho

namespace HolomorphicDivisorReflection

variable {U Z : Set ℂ}

/-- Restriction of the holomorphic involution to the divisor. -/
noncomputable def divisorEquiv (R : HolomorphicDivisorReflection U Z) : Z ≃ Z where
  toFun z := ⟨R.rho z, R.mapsToZ z.property⟩
  invFun z := ⟨R.rho z, R.mapsToZ z.property⟩
  left_inv z := Subtype.ext (R.involutive z)
  right_inv z := Subtype.ext (R.involutive z)

@[simp] theorem divisorEquiv_coe
    (R : HolomorphicDivisorReflection U Z) (z : Z) :
    ((R.divisorEquiv z : Z) : ℂ) = R.rho z := rfl

/-- The two-element reflection group acts on divisor functions by precomposition. -/
@[reducible] noncomputable def functionAction
    (R : HolomorphicDivisorReflection U Z) :
    MulSemiringAction ReflectionParity (Z → ℂ) where
  smul p f := match p with
    | .even => f
    | .odd => fun z => f (R.divisorEquiv z)
  one_smul f := rfl
  mul_smul p q f := by
    funext z
    cases p <;> cases q
    · rfl
    · rfl
    · rfl
    · change f z = f (R.divisorEquiv (R.divisorEquiv z))
      apply congrArg f
      apply Subtype.ext
      exact (R.involutive z).symm
  smul_zero p := by cases p <;> rfl
  smul_add p f g := by cases p <;> rfl
  smul_one p := by cases p <;> rfl
  smul_mul p f g := by cases p <;> rfl

/-- Reflection of divisor functions commutes with complex scalar multiplication. -/
theorem functionSmulCommClass (R : HolomorphicDivisorReflection U Z) :
    letI := R.functionAction
    SMulCommClass ReflectionParity ℂ (Z → ℂ) := by
  letI := R.functionAction
  constructor
  intro p c f
  cases p <;> rfl

/-- Holomorphic reflection preserves the endpoint-holomorphic coefficient algebra. -/
theorem endpointInvariant (R : HolomorphicDivisorReflection U Z) :
    letI := R.functionAction
    ∀ (p : ReflectionParity) {f : Z → ℂ},
      f ∈ endpointHolomorphicSubalgebra U Z →
        p • f ∈ endpointHolomorphicSubalgebra U Z := by
  letI := R.functionAction
  intro p f hf
  rcases hf with ⟨h, hA, heq⟩
  cases p with
  | even => exact ⟨h, hA, heq⟩
  | odd =>
      refine ⟨h ∘ R.rho, hA.comp R.analytic R.mapsToU, ?_⟩
      intro z
      change h (R.rho z) = f (R.divisorEquiv z)
      exact heq (R.divisorEquiv z)

/-- If holomorphic reflection exchanges the two disjoint divisor sectors, it sends the
Real-corona idempotent to its complement. -/
theorem odd_smul_endpointRealCoronaIdempotent_eq_complement
    {upper lower : Set ℂ}
    (R : HolomorphicDivisorReflection U (upper ∪ lower))
    (hdisj : Disjoint upper lower)
    (hSwap : ∀ z : (upper ∪ lower : Set ℂ),
      ((R.divisorEquiv z : (upper ∪ lower : Set ℂ)) : ℂ) ∈ upper ↔
        (z : ℂ) ∈ lower) :
    letI := R.functionAction
    ReflectionParity.odd • endpointRealCoronaIdempotent upper lower =
      1 - endpointRealCoronaIdempotent upper lower := by
  letI := R.functionAction
  funext z
  by_cases hz : (z : ℂ) ∈ upper
  · have hznotlower : (z : ℂ) ∉ lower :=
      fun hzl => Set.disjoint_left.1 hdisj hz hzl
    have hrnotupper :
        ((R.divisorEquiv z : (upper ∪ lower : Set ℂ)) : ℂ) ∉ upper := by
      intro hr
      exact hznotlower ((hSwap z).mp hr)
    have hrnotrho : R.rho z ∉ upper := by simpa using hrnotupper
    change endpointRealCoronaIdempotent upper lower (R.divisorEquiv z) =
      1 - endpointRealCoronaIdempotent upper lower z
    simp [endpointRealCoronaIdempotent, hz, hrnotrho]
  · have hzlower : (z : ℂ) ∈ lower := z.property.resolve_left hz
    have hrupper :
        ((R.divisorEquiv z : (upper ∪ lower : Set ℂ)) : ℂ) ∈ upper :=
      (hSwap z).mpr hzlower
    have hrrho : R.rho z ∈ upper := by simpa using hrupper
    change endpointRealCoronaIdempotent upper lower (R.divisorEquiv z) =
      1 - endpointRealCoronaIdempotent upper lower z
    simp [endpointRealCoronaIdempotent, hz, hrrho]

/-- The holomorphic-reflection crossed product is genuinely dense in the ambient algebraic
crossed product for coefficientwise convergence. -/
theorem reflectedEndpointCrossedProduct_denseRange
    (R : HolomorphicDivisorReflection U Z) :
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ (Z → ℂ) := R.functionSmulCommClass
    letI : TopologicalSpace
        (ambientCrossedProduct (G := ReflectionParity) (A := Z → ℂ)) :=
      crossedProductCoefficientwiseTopology
    DenseRange
      (InvariantSubalgebra.crossedProductInclusion
        (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) := by
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ (Z → ℂ) := R.functionSmulCommClass
  letI : TopologicalSpace
      (ambientCrossedProduct (G := ReflectionParity) (A := Z → ℂ)) :=
    crossedProductCoefficientwiseTopology
  exact InvariantSubalgebra.crossedProductInclusion_denseRange_coefficientwise
    (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)
    (endpointHolomorphicSubalgebra_dense U Z)

/-- Exact P3 classification in the holomorphic reflection crossed product. -/
theorem reflectedEndpointCorona_crossedProduct_iff_finite
    {upper lower : Set ℂ} {zUpper zLower : ℂ}
    (R : HolomorphicDivisorReflection U (upper ∪ lower))
    (hU : IsPreconnected U)
    (hupperU : upper ⊆ U) (hlowerU : lower ⊆ U)
    (hupper_nonempty : upper.Nonempty) (hlower_nonempty : lower.Nonempty)
    (hzUpper : zUpper ∈ U) (hzLower : zLower ∈ U)
    (hupper_acc : upper.Infinite → zUpper ∈ closure (upper \ {zUpper}))
    (hlower_acc : lower.Infinite → zLower ∈ closure (lower \ {zLower}))
    (hdisj : Disjoint upper lower) :
    letI := R.functionAction
    letI : SMulCommClass ReflectionParity ℂ
        (((upper ∪ lower : Set ℂ) → ℂ)) := R.functionSmulCommClass
    SkewMonoidAlgebra.single (1 : ReflectionParity)
        (endpointRealCoronaIdempotent upper lower) ∈
      Set.range
        (InvariantSubalgebra.crossedProductInclusion
          (endpointHolomorphicInvariantSubalgebra R.endpointInvariant)) ↔
      upper.Finite ∧ lower.Finite := by
  letI := R.functionAction
  letI : SMulCommClass ReflectionParity ℂ
      (((upper ∪ lower : Set ℂ) → ℂ)) := R.functionSmulCommClass
  exact endpointRealCoronaDegreeZero_mem_crossedProductRange_iff_finite
    R.endpointInvariant hU hupperU hlowerU hupper_nonempty hlower_nonempty
    hzUpper hzLower hupper_acc hlower_acc hdisj

end HolomorphicDivisorReflection

/-- Negation supplies the canonical holomorphic reflection on every negation-invariant divisor. -/
noncomputable def negationHolomorphicDivisorReflection
    (Z : Set ℂ) (hneg : MapsTo (-·) Z Z) :
    HolomorphicDivisorReflection Set.univ Z where
  rho := (-·)
  analytic := analyticOnNhd_id.neg
  mapsToU := mapsTo_univ _ _
  mapsToZ := hneg
  involutive z := neg_neg z

end GaloisForLFunctions.RHTower
