import GaloisForLFunctions.HTGeometry.SeibergWitten.Orientation
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
# Principal `Spinᶜ(4)` bundles

Mathlib supplies Clifford spin groups and quotient groups, but not a principal-bundle API.  This
module fills the algebraic core needed by Seiberg--Witten theory.  It constructs the Riemannian
`Spin(4)` group from the negative Euclidean Clifford form, proves its central sign is available,
forms `(Spin(4) × U(1)) / ⟨(-1,-1)⟩`, and supplies its squared determinant character.

`PrincipalSpinCBundle` records a free and transitive right action on each fiber.
`SeibergWitten.AssociatedBundles` supplies its algebraic associated-bundle layer.  Topology and
smooth local trivializations remain separate from this torsor-level core.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Riemannian Clifford quadratic form in the convention `c(v)^(2 : ℕ) = -‖v‖²`. -/
def fourSpinQuadraticForm : QuadraticForm ℝ FourSpace :=
  (Matrix.toQuadraticForm' (-1 : Matrix (Fin 4) (Fin 4) ℝ)).comp
    (EuclideanSpace.equiv (Fin 4) ℝ).toLinearMap

/-- The Clifford spin group for the Riemannian four-dimensional form. -/
abbrev SpinFourGroup := spinGroup fourSpinQuadraticForm

/-- First Euclidean coordinate vector, transported to the Hilbert-space four-model. -/
def fourSpinBasisZero : FourSpace :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm (Pi.basisFun ℝ (Fin 4) 0)

/-- The selected unit vector has Clifford square `-1`. -/
theorem fourSpinQuadraticForm_basisZero :
    fourSpinQuadraticForm fourSpinBasisZero = -1 := by
  change Matrix.toQuadraticForm' (-1 : Matrix (Fin 4) (Fin 4) ℝ)
    (Pi.basisFun ℝ (Fin 4) 0) = -1
  simp [Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply, Fin.sum_univ_four]

/-- The scalar Clifford element `-1` belongs to the concrete four-dimensional spin group. -/
theorem fourCliffordNegOne_mem_spin :
    (-1 : CliffordAlgebra fourSpinQuadraticForm) ∈ SpinFourGroup := by
  let e : FourSpace := fourSpinBasisZero
  have he : fourSpinQuadraticForm e = -1 := fourSpinQuadraticForm_basisZero
  have he_unit : IsUnit (fourSpinQuadraticForm e) := by
    rw [he]
    exact isUnit_neg_one
  have hι_unit : IsUnit (CliffordAlgebra.ι fourSpinQuadraticForm e) :=
    CliffordAlgebra.isUnit_ι_of_isUnit fourSpinQuadraticForm he_unit
  let u : (CliffordAlgebra fourSpinQuadraticForm)ˣ := hι_unit.unit
  have hu : (u : CliffordAlgebra fourSpinQuadraticForm) =
      CliffordAlgebra.ι fourSpinQuadraticForm e := hι_unit.unit_spec
  have hu_lipschitz : u ∈ lipschitzGroup fourSpinQuadraticForm := by
    change u ∈ Subgroup.closure
      ((fun x : (CliffordAlgebra fourSpinQuadraticForm)ˣ =>
        (x : CliffordAlgebra fourSpinQuadraticForm)) ⁻¹'
        Set.range (CliffordAlgebra.ι fourSpinQuadraticForm))
    apply Subgroup.subset_closure
    exact ⟨e, hu⟩
  apply spinGroup.mem_iff.mpr
  constructor
  · apply pinGroup.mem_iff.mpr
    constructor
    · refine ⟨u * u, (lipschitzGroup fourSpinQuadraticForm).mul_mem
        hu_lipschitz hu_lipschitz, ?_⟩
      change (u : CliffordAlgebra fourSpinQuadraticForm) * u = -1
      rw [hu, CliffordAlgebra.ι_sq_scalar, he]
      simp
    · constructor <;> simp
  · exact (CliffordAlgebra.even fourSpinQuadraticForm).neg_mem
      (CliffordAlgebra.even fourSpinQuadraticForm).one_mem

/-- A central involution supplied by a spin group. -/
structure CentralInvolution (G : Type*) [Group G] where
  sign : G
  sign_sq : sign * sign = 1
  sign_central : ∀ g : G, sign * g = g * sign

/-- The central scalar `-1` as the sign involution in `Spin(4)`. -/
def fourSpinCentralInvolution : CentralInvolution SpinFourGroup where
  sign := ⟨-1, fourCliffordNegOne_mem_spin⟩
  sign_sq := by
    apply Subtype.ext
    simp
  sign_central := by
    intro g
    apply Subtype.ext
    simp

/-- Diagonal sign relation used to form the `Spinᶜ` quotient. -/
def spinCRelation {G : Type*} [Group G]
    (data : CentralInvolution G) : Subgroup (G × Circle) :=
  Subgroup.normalClosure ({(data.sign, (-1 : Circle))} : Set (G × Circle))

instance spinCRelation_normal {G : Type*} [Group G]
    (data : CentralInvolution G) : (spinCRelation data).Normal := by
  unfold spinCRelation
  exact Subgroup.normalClosure_normal

/-- `Spinᶜ` group obtained by quotienting `Spin × U(1)` by its diagonal central sign. -/
abbrev SpinCExtension {G : Type*} [Group G]
    (data : CentralInvolution G) := (G × Circle) ⧸ spinCRelation data

/-- The genuine four-dimensional Riemannian `Spinᶜ(4)` structure group. -/
abbrev SpinC4 := SpinCExtension fourSpinCentralInvolution

/-- Squared determinant character on the covering group. -/
def spinCPreDeterminant {G : Type*} [Group G] : G × Circle →* Circle where
  toFun := fun pair => pair.2 * pair.2
  map_one' := by simp
  map_mul' := by
    intro a b
    change (a.2 * b.2) * (a.2 * b.2) = (a.2 * a.2) * (b.2 * b.2)
    ac_rfl

/-- Determinant character descending to the `Spinᶜ` quotient. -/
def spinCDeterminant {G : Type*} [Group G]
    (data : CentralInvolution G) : SpinCExtension data →* Circle :=
  QuotientGroup.lift (spinCRelation data) spinCPreDeterminant (by
    refine Subgroup.normalClosure_le_normal ?_
    intro pair hpair
    rw [Set.mem_singleton_iff.mp hpair]
    simp [spinCPreDeterminant])

/-- The quotient determinant is the square of the `U(1)` coordinate. -/
theorem spinCDeterminant_mk {G : Type*} [Group G]
    (data : CentralInvolution G) (g : G) (u : Circle) :
    spinCDeterminant data (QuotientGroup.mk' (spinCRelation data) (g, u)) = u * u :=
  QuotientGroup.lift_mk' _ _ _

/-- Algebraic principal-bundle core for a `Spinᶜ` structure group. -/
structure PrincipalSpinCBundle
    (M : Type*) {G : Type*} [Group G] (data : CentralInvolution G) where
  totalSpace : Type*
  projection : totalSpace → M
  action : totalSpace → SpinCExtension data → totalSpace
  action_one : ∀ p, action p 1 = p
  action_mul : ∀ p g h, action (action p g) h = action p (g * h)
  fiber_free : ∀ p g, action p g = p → g = 1
  fiber_transitive : ∀ p q, projection p = projection q → ∃ g, action p g = q

/-- Trivial algebraic principal `Spinᶜ` bundle on any base type. -/
def trivialPrincipalSpinCBundle
    (M : Type*) {G : Type*} [Group G] (data : CentralInvolution G) :
    PrincipalSpinCBundle M data where
  totalSpace := M × SpinCExtension data
  projection := Prod.fst
  action := fun p g => (p.1, p.2 * g)
  action_one := by intro p; simp
  action_mul := by intro p g h; simp [mul_assoc]
  fiber_free := by
    intro p g h
    have hsecond := congrArg Prod.snd h
    have hsecond' : p.2 * g = p.2 := by simpa using hsecond
    calc
      g = p.2⁻¹ * (p.2 * g) := by simp
      _ = p.2⁻¹ * p.2 := by rw [hsecond']
      _ = 1 := by simp
  fiber_transitive := by
    intro p q hpq
    refine ⟨p.2⁻¹ * q.2, ?_⟩
    apply Prod.ext
    · exact hpq
    · simp

/-- Closed trivial principal `Spinᶜ(4)` bundle on Euclidean four-space. -/
def flatTrivialPrincipalSpinC4Bundle : PrincipalSpinCBundle FourSpace fourSpinCentralInvolution :=
  trivialPrincipalSpinCBundle FourSpace fourSpinCentralInvolution

end GaloisForLFunctions.HTGeometry.SeibergWitten
