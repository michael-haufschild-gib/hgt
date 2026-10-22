import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Basic
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveProfileFormation

/-!
# The positive envelope of a reflected function algebra

An involution `r` of a set `X` (a functional reflection) makes the functions `X → ℂ` into a commutative
complex star-algebra with the reflected star `f*(x) = conj(f(r x))`. For finite `X`, every star-algebra
map from this algebra into a C*-ring kills the indicator of every point that `r` moves, because
`e_x* e_x = 0` there. Hence every such map factors uniquely through restriction to the fixed points of
`r`, so the positive (C*) envelope of the reflected algebra is the commutative algebra of functions on
the fixed-point set. In particular the characters are exactly evaluations at fixed points, the elements
invisible to all receivers are those vanishing on fixed points, and a faithful star-representation into
`X → ℂ` exists only when `r` is the identity.

## Main results

- `receiver_kills_atom`: a star-algebra map into a C*-ring kills the atom at every non-fixed point.
- `receiver_factors_uniquely`: every star-algebra map into a C*-ring factors uniquely through
  `restrictFixed`, restriction to the fixed points.
- `positiveCharacter_unique_fixedPoint`: every star-character is evaluation at a unique fixed point.
- `invisible_fixedReceiver_iff`: an element is killed by every receiver into functions on the fixed
  points iff it vanishes on the fixed points.
- `faithful_positive_receiver_iff`: an injective star-algebra map into `X → ℂ` exists iff `r` fixes
  every point.

## Hypotheses

Unconditional. `X` is finite with decidable equality where sums over atoms are used, and the target `B`
is a normed C*-ring that is a complex star-algebra.
-/

open scoped ComplexConjugate

universe u v

namespace GaloisForLFunctions.HTGeometry

/-- A functional reflection: an involution `act` of the set `X`. -/
structure FunctionalReflection (X : Type u) where
  act : X → X
  involutive : Function.Involutive act

/-- Complex functions on `X`, to be equipped with the star operation twisted by the reflection `r`. -/
structure ReflectedFunction {X : Type u} (r : FunctionalReflection X) where
  val : X → ℂ

namespace ReflectedFunction

variable {X : Type u} (r : FunctionalReflection X)

instance : CoeFun (ReflectedFunction r) (fun _ => X → ℂ) := ⟨val⟩

@[ext] theorem ext {f g : ReflectedFunction r} (h : ∀ x, f x = g x) : f = g := by
  cases f with
  | mk f =>
    cases g with
    | mk g => congr 1; funext x; exact h x

def equiv : ReflectedFunction r ≃ (X → ℂ) where
  toFun := val
  invFun := fun f => ReflectedFunction.mk f
  left_inv := by intro f; cases f; rfl
  right_inv := by intro f; rfl

@[simp] theorem equiv_apply (f : ReflectedFunction r) : equiv r f = f.val := rfl

instance : CommRing (ReflectedFunction r) := Equiv.commRing (equiv r)
instance : Algebra ℂ (ReflectedFunction r) := Equiv.algebra ℂ (equiv r)

@[simp] theorem zero_apply (x : X) : (0 : ReflectedFunction r) x = 0 := by
  change (equiv r (0 : ReflectedFunction r)) x = 0
  simpa using congrFun ((Equiv.ringEquiv (equiv r)).map_zero) x
@[simp] theorem one_apply (x : X) : (1 : ReflectedFunction r) x = 1 := by
  change (equiv r (1 : ReflectedFunction r)) x = 1
  simpa using congrFun ((Equiv.ringEquiv (equiv r)).map_one) x
@[simp] theorem add_apply (f g : ReflectedFunction r) (x : X) : (f + g) x = f x + g x := by
  change (equiv r (f + g)) x = _
  simpa using congrFun ((Equiv.ringEquiv (equiv r)).map_add f g) x
@[simp] theorem sub_apply (f g : ReflectedFunction r) (x : X) : (f - g) x = f x - g x := by
  change (equiv r (f - g)) x = _
  simpa using congrFun ((Equiv.ringEquiv (equiv r)).map_sub f g) x
@[simp] theorem mul_apply (f g : ReflectedFunction r) (x : X) : (f * g) x = f x * g x := by
  change (equiv r (f * g)) x = _
  simpa using congrFun ((Equiv.ringEquiv (equiv r)).map_mul f g) x
@[simp] theorem smul_apply (c : ℂ) (f : ReflectedFunction r) (x : X) : (c • f) x = c * f x := by
  change (equiv r (c • f)) x = _
  simpa [Algebra.smul_def] using congrFun (map_smul (Equiv.algEquiv ℂ (equiv r)) c f) x

/-- The reflected star `f*(x) = conj(f(r x))`. -/
instance : Star (ReflectedFunction r) where
  star f := ⟨fun x => star (f (r.act x))⟩

@[simp] theorem star_apply (f : ReflectedFunction r) (x : X) :
    (star f) x = star (f (r.act x)) := rfl

instance : InvolutiveStar (ReflectedFunction r) where
  star_involutive f := by ext x; simp [r.involutive x]

instance : StarRing (ReflectedFunction r) where
  star_mul f g := by ext x; simp [mul_comm]
  star_add f g := by ext x; simp

instance : StarModule ℂ (ReflectedFunction r) where
  star_smul c f := by ext x; simp

/-- The fixed points of the reflection. -/
def FixedPoint := {x : X // r.act x = x}

variable [Fintype X] [DecidableEq X]

instance fixedPointFintype : Fintype (FixedPoint r) :=
  Fintype.ofFinset (Finset.univ.filter fun x => r.act x = x) (by
    intro x
    change x ∈ Finset.univ.filter (fun x => r.act x = x) ↔ r.act x = x
    simp)

instance fixedPointDecidableEq : DecidableEq (FixedPoint r) :=
  fun x y => decidable_of_iff (x.1 = y.1) Subtype.coe_injective.eq_iff

/-- The indicator function of the point `x`. -/
def atom (x : X) : ReflectedFunction r :=
  ⟨fun y => if y = x then 1 else 0⟩

omit [Fintype X] in
@[simp] theorem atom_apply (x y : X) : atom r x y = if y = x then 1 else 0 := rfl

omit [Fintype X] in
theorem atom_ne_zero (x : X) : atom r x ≠ 0 := by
  intro h
  have h' := congrArg (fun f : ReflectedFunction r => f x) h
  change (if x = x then (1 : ℂ) else 0) = 0 at h'
  rw [if_pos rfl] at h'
  exact one_ne_zero h'

omit [Fintype X] in
/-- The reflected star of the atom at `x` is the atom at `r x`. -/
@[simp] theorem star_atom (x : X) : star (atom r x) = atom r (r.act x) := by
  ext y
  have hiff : r.act y = x ↔ y = r.act x := by
    constructor
    · intro h
      calc
        y = r.act (r.act y) := (r.involutive y).symm
        _ = r.act x := congrArg r.act h
    · intro h
      calc
        r.act y = r.act (r.act x) := congrArg r.act h
        _ = x := r.involutive x
  simp [atom, hiff]

omit [Fintype X] in
/-- At a point moved by the reflection, the atom satisfies `e_x* e_x = 0`. -/
theorem star_atom_mul_self (x : X) (hx : r.act x ≠ x) :
    star (atom r x) * atom r x = 0 := by
  rw [star_atom]
  ext y
  by_cases hy : y = x
  · simp [atom, hy, Ne.symm hx]
  · simp [atom, hy]

/-- Restriction to the fixed points, a star-algebra map onto the functions on the fixed-point set. -/
def restrictFixed : ReflectedFunction r →⋆ₐ[ℂ] (FixedPoint r → ℂ) where
  toFun f := fun x => f x.1
  map_one' := by ext x; simp
  map_mul' f g := by ext x; simp
  map_zero' := by ext x; simp
  map_add' f g := by ext x; simp
  commutes' c := by
    ext x
    change (equiv r ((algebraMap ℂ (ReflectedFunction r)) c)) x.1 = c
    rw [Equiv.algebraMap_def]
    rfl
  map_star' f := by ext x; simp [x.property]

omit [Fintype X] [DecidableEq X] in
@[simp] theorem restrictFixed_apply (f : ReflectedFunction r) (x : FixedPoint r) :
    restrictFixed r f x = f x.1 := rfl

/-- Extension by zero from the fixed points to all of `X`. -/
def extendFixed (g : FixedPoint r → ℂ) : ReflectedFunction r :=
  ⟨fun x => if hx : r.act x = x then g ⟨x, hx⟩ else 0⟩

omit [Fintype X] in
@[simp] theorem restrictFixed_extendFixed (g : FixedPoint r → ℂ) :
    restrictFixed r (extendFixed r g) = g := by
  ext x
  simp [extendFixed, x.property]

omit [Fintype X] in
/-- Restriction to the fixed points is surjective. -/
theorem restrictFixed_surjective : Function.Surjective (restrictFixed r) :=
  fun g => ⟨extendFixed r g, restrictFixed_extendFixed r g⟩

/-- Every reflected function is the finite sum `Σ_x f(x) e_x` of its atoms. -/
theorem atom_expansion (f : ReflectedFunction r) :
    f = ∑ x : X, f x • atom r x := by
  ext y
  change f.val y = (Equiv.algEquiv ℂ (equiv r) (∑ x : X, f x • atom r x)) y
  rw [map_sum]
  simp [atom]

variable {B : Type v} [NormedRing B] [StarRing B] [CStarRing B] [Algebra ℂ B]

omit [Fintype X] in
/-- A star-algebra map into a C*-ring kills the atom at every point moved by the reflection, by the C*
identity applied to `e_x* e_x = 0`. -/
theorem receiver_kills_atom (π : ReflectedFunction r →⋆ₐ[ℂ] B) (x : X)
    (hx : r.act x ≠ x) : π (atom r x) = 0 := by
  rw [← CStarRing.star_mul_self_eq_zero_iff (π (atom r x))]
  rw [← map_star π, ← map_mul, star_atom_mul_self r x hx, map_zero]

/-- A star-algebra map into a C*-ring kills every function that vanishes on the fixed points. -/
theorem receiver_kills_restrictKernel (π : ReflectedFunction r →⋆ₐ[ℂ] B)
    {f : ReflectedFunction r} (hf : restrictFixed r f = 0) : π f = 0 := by
  rw [atom_expansion r f, map_sum]
  apply Finset.sum_eq_zero
  intro x hxmem
  by_cases hx : r.act x = x
  · have hfx : f x = 0 := by
      have hval := congrFun hf (⟨x, hx⟩ : FixedPoint r)
      change f x = (0 : ℂ) at hval
      exact hval
    simp [hfx]
  · simp [receiver_kills_atom r π x hx]

/-- A star-algebra map into a C*-ring depends only on the restriction to the fixed points. -/
theorem receiver_eq_of_restrict_eq (π : ReflectedFunction r →⋆ₐ[ℂ] B)
    {f g : ReflectedFunction r} (h : restrictFixed r f = restrictFixed r g) :
    π f = π g := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply receiver_kills_restrictKernel r π
  ext x
  have hx := congrFun h x
  simpa using sub_eq_zero.mpr hx

/-- The induced star-algebra map on functions on the fixed points, `g ↦ π(extendFixed g)`. -/
noncomputable def factorReceiver (π : ReflectedFunction r →⋆ₐ[ℂ] B) :
    (FixedPoint r → ℂ) →⋆ₐ[ℂ] B where
  toFun g := π (extendFixed r g)
  map_one' := by
    rw [← map_one π]
    apply receiver_eq_of_restrict_eq r π
    simp
  map_mul' f g := by
    rw [← map_mul π]
    apply receiver_eq_of_restrict_eq r π
    simp
  map_zero' := by
    rw [← map_zero π]
    apply receiver_eq_of_restrict_eq r π
    simp
  map_add' f g := by
    rw [← map_add π]
    apply receiver_eq_of_restrict_eq r π
    simp
  commutes' c := by
    rw [← π.commutes c]
    apply receiver_eq_of_restrict_eq r π
    rw [restrictFixed_extendFixed]
    exact ((restrictFixed r).commutes c).symm
  map_star' f := by
    rw [← map_star π]
    apply receiver_eq_of_restrict_eq r π
    rw [restrictFixed_extendFixed, map_star, restrictFixed_extendFixed]

/-- The induced map composed with restriction recovers the original receiver. -/
@[simp] theorem factorReceiver_comp_restrictFixed
    (π : ReflectedFunction r →⋆ₐ[ℂ] B) :
    (factorReceiver r π).comp (restrictFixed r) = π := by
  ext f
  apply receiver_eq_of_restrict_eq r π
  simp

/-- Uniqueness of the factorization through restriction to the fixed points. -/
theorem factorReceiver_unique (π : ReflectedFunction r →⋆ₐ[ℂ] B)
    (φ : (FixedPoint r → ℂ) →⋆ₐ[ℂ] B)
    (hφ : φ.comp (restrictFixed r) = π) :
    φ = factorReceiver r π := by
  ext g
  have h := congrArg (fun ψ : ReflectedFunction r →⋆ₐ[ℂ] B =>
    ψ (extendFixed r g)) hφ
  change φ g = π (extendFixed r g)
  simpa [StarAlgHom.comp_apply] using h

/-- Every star-algebra map into a C*-ring factors uniquely through restriction to the fixed points. -/
theorem receiver_factors_uniquely (π : ReflectedFunction r →⋆ₐ[ℂ] B) :
    ∃! φ : (FixedPoint r → ℂ) →⋆ₐ[ℂ] B,
      φ.comp (restrictFixed r) = π := by
  refine ⟨factorReceiver r π, factorReceiver_comp_restrictFixed r π, ?_⟩
  intro φ hφ
  exact factorReceiver_unique r π φ hφ

/-- The indicator function of a fixed point, as a function on the fixed-point set. -/
def fixedAtom (x : FixedPoint r) : FixedPoint r → ℂ :=
  fun y => if y = x then 1 else 0

omit [Fintype X] in
@[simp] theorem fixedAtom_apply (x y : FixedPoint r) :
    fixedAtom r x y = if y = x then 1 else 0 := rfl

@[simp] theorem sum_fixedAtom : (∑ x : FixedPoint r, fixedAtom r x) = 1 := by
  ext y
  simp [fixedAtom]

omit [Fintype X] in
@[simp] theorem fixedAtom_mul_self (x : FixedPoint r) :
    fixedAtom r x * fixedAtom r x = fixedAtom r x := by
  ext y
  by_cases h : y = x <;> simp [fixedAtom, h]

omit [Fintype X] in
theorem fixedAtom_mul_eq_zero {x y : FixedPoint r} (hxy : x ≠ y) :
    fixedAtom r x * fixedAtom r y = 0 := by
  ext z
  by_cases hzx : z = x
  · simp [fixedAtom, hzx, hxy]
  · simp [fixedAtom, hzx]

/-- Every star-character of the function algebra on the fixed points is evaluation at a unique point. -/
theorem productCharacter_unique_coordinate
    (φ : (FixedPoint r → ℂ) →⋆ₐ[ℂ] ℂ) :
    ∃! x : FixedPoint r, ∀ g, φ g = g x := by
  have hidem (x : FixedPoint r) : φ (fixedAtom r x) = 0 ∨ φ (fixedAtom r x) = 1 := by
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    rw [IsIdempotentElem, ← map_mul, fixedAtom_mul_self]
  have hex : ∃ x : FixedPoint r, φ (fixedAtom r x) = 1 := by
    by_contra h
    have hne : ∀ x : FixedPoint r, φ (fixedAtom r x) ≠ 1 :=
      fun x hx => h ⟨x, hx⟩
    have hz : ∀ x : FixedPoint r, φ (fixedAtom r x) = 0 := by
      intro x
      exact (hidem x).resolve_right (hne x)
    have hone : (1 : ℂ) = 0 := by
      calc
        1 = φ (1 : FixedPoint r → ℂ) := (map_one φ).symm
        _ = φ (∑ x : FixedPoint r, fixedAtom r x) := by rw [sum_fixedAtom]
        _ = ∑ x : FixedPoint r, φ (fixedAtom r x) := by rw [map_sum]
        _ = 0 := by simp [hz]
    exact one_ne_zero hone
  rcases hex with ⟨x, hx⟩
  have heval : ∀ g, φ g = g x := by
    intro g
    have hmul : g * fixedAtom r x = g x • fixedAtom r x := by
      ext y
      by_cases hy : y = x <;> simp [fixedAtom, hy]
    have hmap := congrArg φ hmul
    simpa [map_mul, map_smul, hx] using hmap
  refine ⟨x, heval, ?_⟩
  intro y hy
  by_contra hxy
  have hx' := heval (fixedAtom r x)
  have hy' := hy (fixedAtom r y)
  have : (1 : ℂ) = 0 := by
    calc
      1 = φ (fixedAtom r x) * φ (fixedAtom r y) := by simp [hx', hy']
      _ = φ (fixedAtom r x * fixedAtom r y) := (map_mul φ _ _).symm
      _ = φ 0 := by rw [fixedAtom_mul_eq_zero r (Ne.symm hxy)]
      _ = 0 := map_zero φ
  exact one_ne_zero this

/-- Every star-character of the reflected function algebra is evaluation at a unique fixed point of the
reflection. -/
theorem positiveCharacter_unique_fixedPoint
    (π : ReflectedFunction r →⋆ₐ[ℂ] ℂ) :
    ∃! x : FixedPoint r, ∀ f, π f = f x.1 := by
  rcases productCharacter_unique_coordinate r (factorReceiver r π) with ⟨x, hx, huniq⟩
  refine ⟨x, ?_, ?_⟩
  · intro f
    calc
      π f = factorReceiver r π (restrictFixed r f) := by
        change π f = ((factorReceiver r π).comp (restrictFixed r)) f
        rw [factorReceiver_comp_restrictFixed]
      _ = restrictFixed r f x := hx _
      _ = f x.1 := rfl
  · intro y hy
    apply huniq y
    intro g
    calc
      factorReceiver r π g = π (extendFixed r g) := rfl
      _ = extendFixed r g y.1 := hy _
      _ = g y := by simp [extendFixed, y.property]

/-- A reflected function is killed by every star-algebra map into functions on the fixed points iff it
vanishes on the fixed points. -/
theorem invisible_fixedReceiver_iff (f : ReflectedFunction r) :
    GaloisForLFunctions.HTGeometry.StarReceiverInvisible (FixedPoint r → ℂ) f ↔
      restrictFixed r f = 0 := by
  constructor
  · intro h
    exact h (restrictFixed r)
  · intro hf π
    exact receiver_kills_restrictKernel r π hf

omit [Fintype X] in
/-- An injective star-algebra map into a C*-ring forces the reflection to be the identity. -/
theorem injective_receiver_forces_fixed (π : ReflectedFunction r →⋆ₐ[ℂ] B)
    (hπ : Function.Injective π) : ∀ x : X, r.act x = x := by
  intro x
  by_contra hx
  apply atom_ne_zero r x
  apply hπ
  simpa using receiver_kills_atom r π x hx

/-- When the reflection is the identity, the identity map into `X → ℂ` is a star-algebra map. -/
def standardPositiveReceiver (hfix : ∀ x : X, r.act x = x) :
    ReflectedFunction r →⋆ₐ[ℂ] (X → ℂ) where
  toAlgHom := (Equiv.algEquiv ℂ (equiv r)).toAlgHom
  map_star' f := by
    ext x
    simp [hfix x]

omit [Fintype X] [DecidableEq X] in
theorem standardPositiveReceiver_injective (hfix : ∀ x : X, r.act x = x) :
    Function.Injective (standardPositiveReceiver r hfix) :=
  (equiv r).injective

/-- A faithful star-representation of the reflected algebra into `X → ℂ` exists iff the reflection
fixes every point. -/
theorem faithful_positive_receiver_iff :
    (∃ π : ReflectedFunction r →⋆ₐ[ℂ] (X → ℂ), Function.Injective π) ↔
      ∀ x : X, r.act x = x := by
  constructor
  · rintro ⟨π, hπ⟩
    exact injective_receiver_forces_fixed (B := X → ℂ) r π hπ
  · intro hfix
    exact ⟨standardPositiveReceiver r hfix, standardPositiveReceiver_injective r hfix⟩

/-- The reflection acting on ordinary functions `X → ℂ` by `f ↦ f ∘ r`, a star-algebra automorphism. -/
def standardReflection : (X → ℂ) ≃⋆ₐ[ℂ] (X → ℂ) where
  toFun f := fun x => f (r.act x)
  invFun f := fun x => f (r.act x)
  left_inv f := by ext x; simp [r.involutive x]
  right_inv f := by ext x; simp [r.involutive x]
  map_add' f g := by ext x; simp
  map_mul' f g := by ext x; simp
  map_star' f := by ext x; simp
  map_smul' c f := by ext x; simp

def standardAtom (x : X) : X → ℂ := fun y => if y = x then 1 else 0

omit [Fintype X] in
/-- The standard reflection sends the atom at `x` to the atom at `r x`. -/
@[simp] theorem standardReflection_atom (x : X) :
    standardReflection r (standardAtom x) = standardAtom (r.act x) := by
  ext y
  have hiff : r.act y = x ↔ y = r.act x := by
    constructor
    · intro h
      calc
        y = r.act (r.act y) := (r.involutive y).symm
        _ = r.act x := congrArg r.act h
    · intro h
      calc
        r.act y = r.act (r.act x) := congrArg r.act h
        _ = x := r.involutive x
  simp [standardReflection, standardAtom, hiff]

omit [Fintype X] in
theorem standardAtom_ne_zero (x : X) : standardAtom x ≠ 0 := by
  intro h
  have h' := congrFun h x
  change (if x = x then (1 : ℂ) else 0) = 0 at h'
  rw [if_pos rfl] at h'
  exact one_ne_zero h'

end ReflectedFunction
end GaloisForLFunctions.HTGeometry
