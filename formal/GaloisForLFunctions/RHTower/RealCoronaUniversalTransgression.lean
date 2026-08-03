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

def linearCommutator (D e : Module.End ℂ V) : Module.End ℂ V :=
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

theorem linearCommutator_cliffordExchangeProjector
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D)) :
    linearCommutator D (cliffordExchangeProjector m) = D * m := by
  apply LinearMap.ext
  intro x
  have hx := LinearMap.congr_fun hodd x
  simp [linearCommutator, cliffordExchangeProjector] at hx ⊢
  rw [hx]
  module

theorem norm_linearCommutator_cliffordExchangeProjector
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D))
    (hiso : ∀ x, ‖m x‖ = ‖x‖) (x : V) :
    ‖linearCommutator D (cliffordExchangeProjector m) x‖ = ‖D x‖ := by
  rw [linearCommutator_cliffordExchangeProjector hodd]
  change ‖D (m x)‖ = ‖D x‖
  have hx : D (m x) = -m (D x) := LinearMap.congr_fun hodd x
  rw [hx, norm_neg, hiso]

def HasLinearOperatorBound (T : Module.End ℂ V) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖T x‖ ≤ C * ‖x‖

theorem hasLinearOperatorBound_commutator_iff
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D))
    (hiso : ∀ x, ‖m x‖ = ‖x‖) :
    HasLinearOperatorBound
        (linearCommutator D (cliffordExchangeProjector m)) ↔
      HasLinearOperatorBound D := by
  constructor <;> rintro ⟨C, hC, hbound⟩
  · refine ⟨C, hC, fun x => ?_⟩
    rw [← norm_linearCommutator_cliffordExchangeProjector hodd hiso x]
    exact hbound x
  · refine ⟨C, hC, fun x => ?_⟩
    rw [norm_linearCommutator_cliffordExchangeProjector hodd hiso x]
    exact hbound x

/-- An algebraic linear operator on a normed space is genuinely unbounded when it has no global
operator-norm bound. -/
def IsGenuinelyUnbounded (T : Module.End ℂ V) : Prop :=
  ¬HasLinearOperatorBound T

theorem genuinelyUnbounded_commutator_iff
    {m D : Module.End ℂ V} (hodd : D * m = -(m * D))
    (hiso : ∀ x, ‖m x‖ = ‖x‖) :
    IsGenuinelyUnbounded
        (linearCommutator D (cliffordExchangeProjector m)) ↔
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
