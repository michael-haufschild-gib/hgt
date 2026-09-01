import GaloisForLFunctions.RHTower.RealCoronaQuaternionicCyclic
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Universal Real-corona transgression and bounded-to-local fracture

An involution that exchanges two idempotent sectors produces a Clifford orientation, while a
fixed idempotent is the exact square defect. Crossed-product descent turns the free orientation
into a commutator. On normed complex modules, an odd operator has commutator with its exchanged
projector of exactly the same pointwise norm as the operator itself; hence a genuinely unbounded
odd operator cannot contain that projector in its Lipschitz algebra. The final section computes
the fixed-sector rank as central analytic rank plus off-central real multiplicity, uniformly in
families.
-/

noncomputable section

open scoped ComplexConjugate

namespace GaloisForLFunctions.RHTower

section Fracture

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def cliffordExchangeProjector (m : Module.End ℂ V) : Module.End ℂ V :=
  (2 : ℂ)⁻¹ • (m + LinearMap.id)

def coronaCommutator (D e : Module.End ℂ V) : Module.End ℂ V :=
  D * e - e * D

theorem cliffordExchangeProjector_orientation
    (m : Module.End ℂ V) :
    realCoronaOrientation (cliffordExchangeProjector m) = m := by
  apply LinearMap.ext
  intro x
  simp [realCoronaOrientation, cliffordExchangeProjector]
  module

theorem cliffordExchangeProjector_isIdempotent
    {m : Module.End ℂ V} (hm : m * m = 1) :
    IsIdempotentElem (cliffordExchangeProjector m) := by
  rw [IsIdempotentElem]
  apply LinearMap.ext
  intro x
  have hmx := LinearMap.congr_fun hm x
  simp [cliffordExchangeProjector] at hmx ⊢
  rw [hmx]
  module

theorem coronaCommutator_cliffordExchangeProjector
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D)) :
    coronaCommutator D (cliffordExchangeProjector m) = D * m := by
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hodd x
  simp [coronaCommutator, cliffordExchangeProjector] at hx ⊢
  rw [hx]
  module

theorem norm_coronaCommutator_cliffordExchangeProjector
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D))
    (hiso : ∀ x, ‖m x‖ = ‖x‖) (x : V) :
    ‖coronaCommutator D (cliffordExchangeProjector m) x‖ = ‖D x‖ := by
  rw [coronaCommutator_cliffordExchangeProjector hodd]
  change ‖D (m x)‖ = ‖D x‖
  have hx : D (m x) = -m (D x) := LinearMap.congr_fun hodd x
  rw [hx, norm_neg, hiso]

def HasLinearOperatorBound (T : Module.End ℂ V) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖

theorem hasLinearOperatorBound_commutator_iff
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D))
    (hiso : ∀ x, ‖m x‖ = ‖x‖) :
    HasLinearOperatorBound
        (coronaCommutator D (cliffordExchangeProjector m)) ↔
      HasLinearOperatorBound D := by
  constructor <;> rintro ⟨C, hC, hbound⟩
  · refine ⟨C, hC, fun x => ?_⟩
    rw [← norm_coronaCommutator_cliffordExchangeProjector hodd hiso x]
    exact hbound x
  · refine ⟨C, hC, fun x => ?_⟩
    rw [norm_coronaCommutator_cliffordExchangeProjector hodd hiso x]
    exact hbound x

/-- An algebraic linear operator on a normed space is genuinely unbounded when it has no global
operator-norm bound. -/
def IsGenuinelyUnbounded (T : Module.End ℂ V) : Prop :=
  ¬HasLinearOperatorBound T

theorem genuinelyUnbounded_commutator_iff
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D))
    (hiso : ∀ x, ‖m x‖ = ‖x‖) :
    IsGenuinelyUnbounded
        (coronaCommutator D (cliffordExchangeProjector m)) ↔
      IsGenuinelyUnbounded D := by
  exact not_congr (hasLinearOperatorBound_commutator_iff hodd hiso)

/-! ### Densely defined operators -/

/-- Domain invariance of the exchanged projector follows from invariance under its orientation. -/
theorem linearPMapExchangeProjector_mem
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    cliffordExchangeProjector m x ∈ D.domain := by
  rw [cliffordExchangeProjector]
  exact D.domain.smul_mem _ (D.domain.add_mem (hdomm x) x.property)

/-- The exchanged projector restricted to an invariant domain. -/
def linearPMapExchangeProjectorDomainMap
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) :
    D.domain →ₗ[ℂ] D.domain :=
  ((cliffordExchangeProjector m).comp D.domain.subtype).codRestrict
    D.domain (fun x => linearPMapExchangeProjector_mem D m hdomm x)

/-- Restriction of a domain-preserving orientation to the operator domain. -/
def linearPMapOrientationDomainMap
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) :
    D.domain →ₗ[ℂ] D.domain :=
  (m.comp D.domain.subtype).codRestrict D.domain hdomm

/-- The commutator with the orientation itself, on the exact operator domain. -/
def linearPMapOrientationCommutator
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) : V →ₗ.[ℂ] V where
  domain := D.domain
  toFun := D.toFun.comp (linearPMapOrientationDomainMap D m hdomm) -
    m.comp D.toFun

@[simp]
theorem linearPMapOrientationCommutator_apply
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    linearPMapOrientationCommutator D m hdomm x =
      D ⟨m x, hdomm x⟩ - m (D x) := by
  rfl

/-- The commutator with the exchanged projector on the exact domain of a partially defined
operator.  It is a `LinearPMap`, not an everywhere-defined surrogate for an unbounded operator. -/
def linearPMapExchangeCommutator
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) : V →ₗ.[ℂ] V where
  domain := D.domain
  toFun := D.toFun.comp (linearPMapExchangeProjectorDomainMap D m hdomm) -
    (cliffordExchangeProjector m).comp D.toFun

@[simp]
theorem linearPMapExchangeCommutator_apply
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain) (x : D.domain) :
    linearPMapExchangeCommutator D m hdomm x =
      D ⟨cliffordExchangeProjector m x,
        linearPMapExchangeProjector_mem D m hdomm x⟩ -
        cliffordExchangeProjector m (D x) := by
  rfl

/-- Bounded-to-local fracture on the exact domain: if `D` is odd for `m`, then its commutator
with `(1 + m) / 2` is precisely `D m`. -/
theorem linearPMapExchangeCommutator_eq
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (x : D.domain) :
    linearPMapExchangeCommutator D m hdomm x =
      D ⟨m x, hdomm x⟩ := by
  let mx : D.domain := ⟨m x, hdomm x⟩
  let ex : D.domain :=
    ⟨cliffordExchangeProjector m x,
      linearPMapExchangeProjector_mem D m hdomm x⟩
  have hex : ex = (2 : ℂ)⁻¹ • (mx + x) := by
    apply Subtype.ext
    simp [ex, mx, cliffordExchangeProjector]
  have hDmx : D mx = -m (D x) := hodd x
  rw [linearPMapExchangeCommutator_apply,
    show (⟨cliffordExchangeProjector m x,
      linearPMapExchangeProjector_mem D m hdomm x⟩ : D.domain) = ex from rfl,
    hex, D.map_smul, D.map_add]
  change (2 : ℂ)⁻¹ • (D mx + D x) -
      (2 : ℂ)⁻¹ • (m (D x) + D x) = D mx
  rw [hDmx]
  module

theorem norm_linearPMapExchangeCommutator
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (hiso : ∀ x : V, ‖m x‖ = ‖x‖) (x : D.domain) :
    ‖linearPMapExchangeCommutator D m hdomm x‖ = ‖D x‖ := by
  rw [linearPMapExchangeCommutator_eq D m hdomm hodd x,
    hodd x, norm_neg, hiso]

theorem linearPMapOrientationCommutator_eq_two_smul
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (x : D.domain) :
    linearPMapOrientationCommutator D m hdomm x =
      (2 : ℂ) • D ⟨m x, hdomm x⟩ := by
  rw [linearPMapOrientationCommutator_apply, hodd x]
  module

theorem norm_linearPMapOrientationCommutator
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (hiso : ∀ x : V, ‖m x‖ = ‖x‖) (x : D.domain) :
    ‖linearPMapOrientationCommutator D m hdomm x‖ = 2 * ‖D x‖ := by
  rw [linearPMapOrientationCommutator_eq_two_smul D m hdomm hodd x,
    norm_smul, Complex.norm_ofNat, hodd x, norm_neg, hiso]

/-- A partially defined operator is bounded on its domain when one constant controls its graph
norm against the ambient norm.  For a dense domain this is exactly the estimate needed for a
bounded extension. -/
def HasLinearPMapBoundOnDomain (T : V →ₗ.[ℂ] V) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : T.domain, ‖T x‖ ≤ C * ‖(x : V)‖

theorem hasLinearPMapBoundOnDomain_exchangeCommutator_iff
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (hiso : ∀ x : V, ‖m x‖ = ‖x‖) :
    HasLinearPMapBoundOnDomain (linearPMapExchangeCommutator D m hdomm) ↔
      HasLinearPMapBoundOnDomain D := by
  constructor <;> rintro ⟨C, hC, hbound⟩
  · refine ⟨C, hC, fun x => ?_⟩
    rw [← norm_linearPMapExchangeCommutator D m hdomm hodd hiso x]
    exact hbound x
  · refine ⟨C, hC, fun x => ?_⟩
    rw [norm_linearPMapExchangeCommutator D m hdomm hodd hiso x]
    exact hbound x

theorem hasLinearPMapBoundOnDomain_orientationCommutator_iff
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (hiso : ∀ x : V, ‖m x‖ = ‖x‖) :
    HasLinearPMapBoundOnDomain (linearPMapOrientationCommutator D m hdomm) ↔
      HasLinearPMapBoundOnDomain D := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun x => ?_⟩
    have h := hbound x
    rw [norm_linearPMapOrientationCommutator D m hdomm hodd hiso x] at h
    exact le_trans (by nlinarith [norm_nonneg (D x)]) h
  · rintro ⟨C, hC, hbound⟩
    refine ⟨2 * C, mul_nonneg (by norm_num) hC, fun x => ?_⟩
    rw [norm_linearPMapOrientationCommutator D m hdomm hodd hiso x]
    nlinarith [hbound x, norm_nonneg (x : V)]

def IsGenuinelyUnboundedLinearPMap (T : V →ₗ.[ℂ] V) : Prop :=
  ¬HasLinearPMapBoundOnDomain T

theorem genuinelyUnboundedLinearPMap_exchangeCommutator_iff
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (hiso : ∀ x : V, ‖m x‖ = ‖x‖) :
    IsGenuinelyUnboundedLinearPMap (linearPMapExchangeCommutator D m hdomm) ↔
      IsGenuinelyUnboundedLinearPMap D := by
  exact not_congr
    (hasLinearPMapBoundOnDomain_exchangeCommutator_iff D m hdomm hodd hiso)

theorem genuinelyUnboundedLinearPMap_orientationCommutator_iff
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hodd : ∀ x : D.domain, D ⟨m x, hdomm x⟩ = -m (D x))
    (hiso : ∀ x : V, ‖m x‖ = ‖x‖) :
    IsGenuinelyUnboundedLinearPMap (linearPMapOrientationCommutator D m hdomm) ↔
      IsGenuinelyUnboundedLinearPMap D := by
  exact not_congr
    (hasLinearPMapBoundOnDomain_orientationCommutator_iff D m hdomm hodd hiso)

/-! ### Intrinsic odd Real-corona data -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Operator-theoretic data for the attempted intrinsic local realization of a Real-corona
orientation.  The grading is a bounded self-adjoint involution, the Dirac operator is genuinely
unbounded and self-adjoint, its domain is grading-invariant, and it is odd for that grading. -/
structure IntrinsicRealCoronaOddDatum (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  D : H →ₗ.[ℂ] H
  orientation : H →L[ℂ] H
  D_selfAdjoint : IsSelfAdjoint D
  orientation_selfAdjoint : IsSelfAdjoint orientation
  orientation_involutive :
    orientation.comp orientation = ContinuousLinearMap.id ℂ H
  orientation_isometry : ∀ x : H, ‖orientation x‖ = ‖x‖
  domain_invariant : ∀ x : D.domain, orientation x ∈ D.domain
  odd : ∀ x : D.domain,
    D ⟨orientation x, domain_invariant x⟩ = -orientation (D x)
  genuinely_unbounded : IsGenuinelyUnboundedLinearPMap D

def IntrinsicRealCoronaOddDatum.projector
    (F : IntrinsicRealCoronaOddDatum H) : Module.End ℂ H :=
  cliffordExchangeProjector F.orientation.toLinearMap

def IntrinsicRealCoronaOddDatum.projectorCommutator
    (F : IntrinsicRealCoronaOddDatum H) : H →ₗ.[ℂ] H :=
  linearPMapExchangeCommutator F.D F.orientation.toLinearMap F.domain_invariant

def IntrinsicRealCoronaOddDatum.orientationCommutator
    (F : IntrinsicRealCoronaOddDatum H) : H →ₗ.[ℂ] H :=
  linearPMapOrientationCommutator F.D F.orientation.toLinearMap F.domain_invariant

theorem IntrinsicRealCoronaOddDatum.dense_domain
    (F : IntrinsicRealCoronaOddDatum H) : Dense (F.D.domain : Set H) :=
  F.D_selfAdjoint.dense_domain

theorem IntrinsicRealCoronaOddDatum.closed
    (F : IntrinsicRealCoronaOddDatum H) : F.D.IsClosed :=
  F.D_selfAdjoint.isClosed

theorem IntrinsicRealCoronaOddDatum.orientation_toLinearMap_involutive
    (F : IntrinsicRealCoronaOddDatum H) :
    F.orientation.toLinearMap * F.orientation.toLinearMap = 1 := by
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun T : H →L[ℂ] H => T x) F.orientation_involutive
  simpa using hx

theorem IntrinsicRealCoronaOddDatum.projector_isIdempotent
    (F : IntrinsicRealCoronaOddDatum H) : IsIdempotentElem F.projector := by
  exact cliffordExchangeProjector_isIdempotent F.orientation_toLinearMap_involutive

/-- Intrinsic local-index obstruction: the commutator with the projector cut out by the same odd
grading is genuinely unbounded. -/
theorem IntrinsicRealCoronaOddDatum.projectorCommutator_genuinelyUnbounded
    (F : IntrinsicRealCoronaOddDatum H) :
    IsGenuinelyUnboundedLinearPMap F.projectorCommutator := by
  exact (genuinelyUnboundedLinearPMap_exchangeCommutator_iff
    F.D F.orientation.toLinearMap F.domain_invariant F.odd
      F.orientation_isometry).mpr F.genuinely_unbounded

theorem IntrinsicRealCoronaOddDatum.projectorCommutator_not_bounded
    (F : IntrinsicRealCoronaOddDatum H) :
    ¬HasLinearPMapBoundOnDomain F.projectorCommutator :=
  F.projectorCommutator_genuinelyUnbounded

theorem IntrinsicRealCoronaOddDatum.orientationCommutator_genuinelyUnbounded
    (F : IntrinsicRealCoronaOddDatum H) :
    IsGenuinelyUnboundedLinearPMap F.orientationCommutator := by
  exact (genuinelyUnboundedLinearPMap_orientationCommutator_iff
    F.D F.orientation.toLinearMap F.domain_invariant F.odd
      F.orientation_isometry).mpr F.genuinely_unbounded

theorem IntrinsicRealCoronaOddDatum.orientationCommutator_not_bounded
    (F : IntrinsicRealCoronaOddDatum H) :
    ¬HasLinearPMapBoundOnDomain F.orientationCommutator :=
  F.orientationCommutator_genuinelyUnbounded

/-- First-order local-index prerequisite for representing the Real-corona orientation in the
Lipschitz algebra of its intrinsic odd Dirac operator. -/
def IntrinsicRealCoronaOddDatum.HasLocalIndexFirstOrderPrerequisite
    (F : IntrinsicRealCoronaOddDatum H) : Prop :=
  HasLinearPMapBoundOnDomain F.orientationCommutator

theorem IntrinsicRealCoronaOddDatum.not_hasLocalIndexFirstOrderPrerequisite
    (F : IntrinsicRealCoronaOddDatum H) :
    ¬F.HasLocalIndexFirstOrderPrerequisite :=
  F.orientationCommutator_not_bounded

/-- First-order smoothness prerequisite for the exchanged Real-corona projector. -/
def IntrinsicRealCoronaOddDatum.HasSmoothProjectorFirstOrderPrerequisite
    (F : IntrinsicRealCoronaOddDatum H) : Prop :=
  HasLinearPMapBoundOnDomain F.projectorCommutator

theorem IntrinsicRealCoronaOddDatum.not_hasSmoothProjectorFirstOrderPrerequisite
    (F : IntrinsicRealCoronaOddDatum H) :
    ¬F.HasSmoothProjectorFirstOrderPrerequisite :=
  F.projectorCommutator_not_bounded

/-- Exact empty-classification law: a proposed subclass universally supplies the impossible smooth
projector prerequisite exactly when that subclass is empty. -/
theorem intrinsicRealCorona_smoothSubclass_firstOrder_iff_empty
    (P : IntrinsicRealCoronaOddDatum H → Prop) :
    (∀ F, P F → F.HasSmoothProjectorFirstOrderPrerequisite) ↔ {F | P F} = ∅ := by
  constructor
  · intro hfirst
    ext F
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hP
    exact F.not_hasSmoothProjectorFirstOrderPrerequisite (hfirst F hP)
  · intro hempty F hP
    have hmem : F ∈ {G | P G} := hP
    have : False := by simpa [hempty] using hmem
    exact this.elim

end Fracture

section OrbitDecomposition

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Three central orbit sectors for a Real involution: a free pair exchanged by the involution
and a fixed defect sector. -/
structure RealOrbitIdempotentDecomposition
    (K : KRealAlgebraStructure A) where
  ePlus : A
  eFixed : A
  eMinus : A
  plus_idempotent : IsIdempotentElem ePlus
  fixed_idempotent : IsIdempotentElem eFixed
  minus_idempotent : IsIdempotentElem eMinus
  plus_minus : ePlus * eMinus = 0
  minus_plus : eMinus * ePlus = 0
  sum_eq_one : ePlus + eFixed + eMinus = 1
  sigma_plus : K.sigma ePlus = eMinus
  sigma_fixed : K.sigma eFixed = eFixed
  sigma_minus : K.sigma eMinus = ePlus

def RealOrbitIdempotentDecomposition.orientation
    {K : KRealAlgebraStructure A}
    (E : RealOrbitIdempotentDecomposition K) : A :=
  E.ePlus - E.eMinus

theorem RealOrbitIdempotentDecomposition.orientation_sq
    {K : KRealAlgebraStructure A}
    (E : RealOrbitIdempotentDecomposition K) :
    E.orientation * E.orientation = 1 - E.eFixed := by
  exact realCoronaNonrealOrientation_sq E.plus_idempotent E.minus_idempotent
    E.plus_minus E.minus_plus E.sum_eq_one

theorem RealOrbitIdempotentDecomposition.sigma_orientation
    {K : KRealAlgebraStructure A}
    (E : RealOrbitIdempotentDecomposition K) :
    K.sigma E.orientation = -E.orientation := by
  exact K.sigma_realCoronaNonrealOrientation E.sigma_plus E.sigma_minus

theorem RealOrbitIdempotentDecomposition.fixed_eq_one_sub_orientation_sq
    {K : KRealAlgebraStructure A}
    (E : RealOrbitIdempotentDecomposition K) :
    E.eFixed = 1 - E.orientation * E.orientation := by
  rw [E.orientation_sq]
  abel

theorem realOrbitOrientation_eq_commutator
    {K : KRealAlgebraStructure A}
    (E : RealOrbitIdempotentDecomposition K) {u : A}
    (hu : u * u = 1) (hconj : u * E.ePlus * u = E.eMinus) :
    E.orientation =
      realCoronaCrossedX E.ePlus u * realCoronaCrossedY E.ePlus u -
        realCoronaCrossedY E.ePlus u * realCoronaCrossedX E.ePlus u := by
  have he := E.plus_idempotent
  rw [IsIdempotentElem] at he
  have hyx :
      realCoronaCrossedY E.ePlus u * realCoronaCrossedX E.ePlus u =
        E.eMinus := by
    change u * E.ePlus * (E.ePlus * u) = E.eMinus
    calc
      u * E.ePlus * (E.ePlus * u) = u * (E.ePlus * E.ePlus) * u := by
        simp only [mul_assoc]
      _ = u * E.ePlus * u := by rw [he]
      _ = E.eMinus := hconj
  rw [realCoronaCrossed_xy E.plus_idempotent hu, hyx]
  rfl

theorem realOrbitOrientation_trace_eq_zero
    {K : KRealAlgebraStructure A}
    (E : RealOrbitIdempotentDecomposition K)
    {G : Type*} [AddCommGroup G] (tau : A →+ G)
    (hcyclic : ∀ a b, tau (a * b) = tau (b * a)) {u : A}
    (hu : u * u = 1) (hconj : u * E.ePlus * u = E.eMinus) :
    tau E.orientation = 0 := by
  rw [realOrbitOrientation_eq_commutator E hu hconj, map_sub, hcyclic, sub_self]

end OrbitDecomposition

section FixedRank

variable {ι : Type*}

def fixedSectorDefectRank (q : ι →₀ ℕ) : ℕ :=
  q.sum fun _ n => n

def analyticRankAt (center : ι) (q : ι →₀ ℕ) : ℕ :=
  q center

def offCentralRealMultiplicity (center : ι) (q : ι →₀ ℕ) : ℕ :=
  (q.erase center).sum fun _ n => n

theorem fixedSectorDefectRank_eq_analyticRank_add_offCentral
    [DecidableEq ι] (center : ι) (q : ι →₀ ℕ) :
    fixedSectorDefectRank q =
      analyticRankAt center q + offCentralRealMultiplicity center q := by
  rw [fixedSectorDefectRank, analyticRankAt, offCentralRealMultiplicity]
  exact (Finsupp.add_sum_erase' q center (fun _ n => n) (by simp)).symm

theorem offCentralRealMultiplicity_eq_zero_iff
    [DecidableEq ι] (center : ι) (q : ι →₀ ℕ) :
    offCentralRealMultiplicity center q = 0 ↔
      ∀ i, i ≠ center → q i = 0 := by
  constructor
  · intro h i hi
    rw [offCentralRealMultiplicity, Finsupp.sum,
      Finset.sum_eq_zero_iff] at h
    by_contra hqi
    have himem : i ∈ (q.erase center).support := by
      simp [Finsupp.mem_support_iff, hi, hqi]
    have hz := h i himem
    exact hqi (by simpa [hi] using hz)
  · intro h
    rw [offCentralRealMultiplicity, Finsupp.sum]
    apply Finset.sum_eq_zero
    intro i hiSupport
    by_cases hi : i = center
    · subst i
      simp
    · simp [hi, h i hi]

theorem fixedSectorDefectRank_eq_analyticRank_iff
    [DecidableEq ι] (center : ι) (q : ι →₀ ℕ) :
    fixedSectorDefectRank q = analyticRankAt center q ↔
      ∀ i, i ≠ center → q i = 0 := by
  rw [fixedSectorDefectRank_eq_analyticRank_add_offCentral center q]
  constructor
  · intro h
    have hoff : offCentralRealMultiplicity center q = 0 := by omega
    exact (offCentralRealMultiplicity_eq_zero_iff center q).mp hoff
  · intro h
    have hoff := (offCentralRealMultiplicity_eq_zero_iff center q).mpr h
    omega

/-! ### Reflection-exact self-dual real sectors -/

def lowerRealMultiplicitySupport (center : ℝ) (q : ℝ →₀ ℕ) : Finset ℝ :=
  q.support.filter fun x => x < center

def upperRealMultiplicitySupport (center : ℝ) (q : ℝ →₀ ℕ) : Finset ℝ :=
  q.support.filter fun x => center < x

def upperRealMultiplicity (center : ℝ) (q : ℝ →₀ ℕ) : ℕ :=
  ∑ x ∈ upperRealMultiplicitySupport center q, q x

/-- Reflection identifies lower and upper off-central multiplicity exactly. -/
theorem lowerRealMultiplicity_sum_eq_upper
    (center : ℝ) (q : ℝ →₀ ℕ)
    (hsymm : ∀ x, q (2 * center - x) = q x) :
    (∑ x ∈ lowerRealMultiplicitySupport center q, q x) =
      ∑ x ∈ upperRealMultiplicitySupport center q, q x := by
  refine Finset.sum_bij'
    (fun x _ => 2 * center - x) (fun x _ => 2 * center - x) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [lowerRealMultiplicitySupport, upperRealMultiplicitySupport,
      Finset.mem_filter] at hx ⊢
    refine ⟨?_, by linarith [hx.2]⟩
    rw [Finsupp.mem_support_iff, hsymm]
    exact Finsupp.mem_support_iff.mp hx.1
  · intro x hx
    simp only [lowerRealMultiplicitySupport, upperRealMultiplicitySupport,
      Finset.mem_filter] at hx ⊢
    refine ⟨?_, by linarith [hx.2]⟩
    rw [Finsupp.mem_support_iff, hsymm]
    exact Finsupp.mem_support_iff.mp hx.1
  · intro x _
    ring
  · intro x _
    ring
  · intro x _
    exact (hsymm x).symm

theorem offCentralRealMultiplicity_eq_lower_add_upper
    (center : ℝ) (q : ℝ →₀ ℕ) :
    offCentralRealMultiplicity center q =
      (∑ x ∈ lowerRealMultiplicitySupport center q, q x) +
        ∑ x ∈ upperRealMultiplicitySupport center q, q x := by
  rw [offCentralRealMultiplicity, Finsupp.sum]
  classical
  have hsupp : (q.erase center).support = q.support.erase center := by
    ext x
    simp [Finsupp.mem_support_iff]
  rw [hsupp]
  have hpartition :
      q.support.erase center =
        lowerRealMultiplicitySupport center q ∪
          upperRealMultiplicitySupport center q := by
    ext x
    rw [Finset.mem_erase, Finset.mem_union]
    simp only [lowerRealMultiplicitySupport, upperRealMultiplicitySupport,
      Finset.mem_filter]
    constructor
    · intro hx
      rcases lt_or_gt_of_ne hx.1 with hlt | hgt
      · exact Or.inl ⟨hx.2, hlt⟩
      · exact Or.inr ⟨hx.2, hgt⟩
    · rintro (hx | hx)
      · exact ⟨ne_of_lt hx.2, hx.1⟩
      · exact ⟨ne_of_gt hx.2, hx.1⟩
  rw [hpartition, Finset.sum_union]
  · congr 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp [ne_of_lt (Finset.mem_filter.mp hx).2]
    · apply Finset.sum_congr rfl
      intro x hx
      simp [ne_of_gt (Finset.mem_filter.mp hx).2]
  · apply Finset.disjoint_left.mpr
    intro x hxLower hxUpper
    have hlower := (Finset.mem_filter.mp hxLower).2
    have hupper := (Finset.mem_filter.mp hxUpper).2
    linarith

/-- Self-dual fixed-sector law: total Real-corona defect is central analytic rank plus twice the
upper off-central real multiplicity. -/
theorem fixedSectorDefectRank_eq_analyticRank_add_twice_upper
    (center : ℝ) (q : ℝ →₀ ℕ)
    (hsymm : ∀ x, q (2 * center - x) = q x) :
    fixedSectorDefectRank q =
      analyticRankAt center q + 2 * upperRealMultiplicity center q := by
  rw [fixedSectorDefectRank_eq_analyticRank_add_offCentral center q,
    offCentralRealMultiplicity_eq_lower_add_upper center q,
    lowerRealMultiplicity_sum_eq_upper center q hsymm]
  simp [upperRealMultiplicity]
  omega

theorem fixedSectorDefectRank_modEq_analyticRank
    (center : ℝ) (q : ℝ →₀ ℕ)
    (hsymm : ∀ x, q (2 * center - x) = q x) :
    Nat.ModEq 2 (fixedSectorDefectRank q) (analyticRankAt center q) := by
  rw [fixedSectorDefectRank_eq_analyticRank_add_twice_upper center q hsymm]
  rw [add_comm (analyticRankAt center q)]
  exact Nat.ModEq.modulus_mul_add

/-- A self-dual family whose finite real-zero multiplicities respect reflection about its center. -/
structure SelfDualRealZeroFamily (T : Type*) where
  center : ℝ
  realMultiplicity : T → ℝ →₀ ℕ
  reflection_multiplicity :
    ∀ t x, realMultiplicity t (2 * center - x) = realMultiplicity t x

def SelfDualRealZeroFamily.defectRank
    {T : Type*} (F : SelfDualRealZeroFamily T) (t : T) : ℕ :=
  fixedSectorDefectRank (F.realMultiplicity t)

def SelfDualRealZeroFamily.analyticRank
    {T : Type*} (F : SelfDualRealZeroFamily T) (t : T) : ℕ :=
  analyticRankAt F.center (F.realMultiplicity t)

def SelfDualRealZeroFamily.upperOffCentralMultiplicity
    {T : Type*} (F : SelfDualRealZeroFamily T) (t : T) : ℕ :=
  upperRealMultiplicity F.center (F.realMultiplicity t)

theorem SelfDualRealZeroFamily.defectRank_eq_analyticRank_add_twice_upper
    {T : Type*} (F : SelfDualRealZeroFamily T) (t : T) :
    F.defectRank t =
      F.analyticRank t + 2 * F.upperOffCentralMultiplicity t := by
  exact fixedSectorDefectRank_eq_analyticRank_add_twice_upper
    F.center (F.realMultiplicity t) (F.reflection_multiplicity t)

theorem SelfDualRealZeroFamily.defectRank_modEq_analyticRank
    {T : Type*} (F : SelfDualRealZeroFamily T) (t : T) :
    Nat.ModEq 2 (F.defectRank t) (F.analyticRank t) := by
  exact fixedSectorDefectRank_modEq_analyticRank
    F.center (F.realMultiplicity t) (F.reflection_multiplicity t)

/-- A family of multiplicity-exact fixed sectors with a distinguished central spectral label. -/
structure SelfDualFixedSectorFamily (T ι : Type*) where
  center : ι
  realMultiplicity : T → ι →₀ ℕ

def SelfDualFixedSectorFamily.defectRank
    {T ι : Type*} (F : SelfDualFixedSectorFamily T ι) (t : T) : ℕ :=
  fixedSectorDefectRank (F.realMultiplicity t)

def SelfDualFixedSectorFamily.analyticRank
    {T ι : Type*} (F : SelfDualFixedSectorFamily T ι) (t : T) : ℕ :=
  analyticRankAt F.center (F.realMultiplicity t)

def SelfDualFixedSectorFamily.offCentralMultiplicity
    {T ι : Type*} (F : SelfDualFixedSectorFamily T ι) (t : T) : ℕ :=
  offCentralRealMultiplicity F.center (F.realMultiplicity t)

theorem SelfDualFixedSectorFamily.defectRank_eq
    {T ι : Type*} [DecidableEq ι]
    (F : SelfDualFixedSectorFamily T ι) (t : T) :
    F.defectRank t = F.analyticRank t + F.offCentralMultiplicity t := by
  exact fixedSectorDefectRank_eq_analyticRank_add_offCentral
    F.center (F.realMultiplicity t)

theorem SelfDualFixedSectorFamily.defectRank_eq_analyticRank_iff
    {T ι : Type*} [DecidableEq ι]
    (F : SelfDualFixedSectorFamily T ι) (t : T) :
    F.defectRank t = F.analyticRank t ↔
      ∀ i, i ≠ F.center → F.realMultiplicity t i = 0 := by
  exact fixedSectorDefectRank_eq_analyticRank_iff
    F.center (F.realMultiplicity t)

end FixedRank

end GaloisForLFunctions.RHTower
