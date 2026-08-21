import GaloisForLFunctions.HTGeometry.SeibergWitten.PrincipalSpinC

/-!
# Algebraic associated bundles for principal `Spinᶜ` torsors

This module supplies the association layer missing after the algebraic principal-`Spinᶜ` torsor.
A complex representation is a homomorphism from the `Spinᶜ` quotient group to complex linear
automorphisms. `PrincipalSpinCAssociatedBundle` records an associated total space, its projection,
and the exact orbit relation `(p·g, v) ∼ (p, ρ(g)v)`.

The closed construction works for every representation over the trivial principal bundle.  It gives
positive and negative rank-two fibers and the determinant line associated to the squared `U(1)`
character over Euclidean four-space.  This is the algebraic association mechanism; smooth local
trivializations and the nontrivial standard chiral `Spinᶜ(4)` representation remain separate layers.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- A complex linear representation of a `Spinᶜ` structure group. -/
abbrev SpinCComplexRepresentation
    {G : Type*} [Group G] (data : CentralInvolution G)
    (V : Type*) [AddCommMonoid V] [Module ℂ V] :=
  SpinCExtension data →* (V ≃ₗ[ℂ] V)

/-- The trivial complex representation of every `Spinᶜ` structure group. -/
def trivialSpinCComplexRepresentation
    {G : Type*} [Group G] (data : CentralInvolution G)
    (V : Type*) [AddCommMonoid V] [Module ℂ V] :
    SpinCComplexRepresentation data V where
  toFun := fun _ => LinearEquiv.refl ℂ V
  map_one' := rfl
  map_mul' := by
    intro x y
    ext v
    rfl

/-- Algebraic associated-bundle presentation for a principal `Spinᶜ` torsor and representation. -/
structure PrincipalSpinCAssociatedBundle
    {M G : Type*} [Group G] (data : CentralInvolution G)
    (P : PrincipalSpinCBundle M data)
    (V : Type*) [AddCommMonoid V] [Module ℂ V]
    (representation : SpinCComplexRepresentation data V) where
  totalSpace : Type*
  projection : totalSpace → M
  quotientMap : P.totalSpace → V → totalSpace
  projection_quotientMap : ∀ p v, projection (quotientMap p v) = P.projection p
  equivariant : ∀ p g v,
    quotientMap (P.action p g) v = quotientMap p (representation g v)
  fiber_surjective : ∀ z, ∃ p v, quotientMap p v = z
  orbit_exact : ∀ p v q w,
    quotientMap p v = quotientMap q w ↔
      ∃ g, q = P.action p g ∧ w = representation g⁻¹ v

/-- Scalar multiplication by a unit complex number, as a complex linear automorphism. -/
def circleScalarLinearEquiv (u : Circle) : ℂ ≃ₗ[ℂ] ℂ where
  toFun := fun z => (u : ℂ) * z
  invFun := fun z => (u⁻¹ : Circle) * z
  left_inv := by
    intro z
    simp
  right_inv := by
    intro z
    simp
  map_add' := by
    intro x y
    ring
  map_smul' := by
    intro c z
    change (u : ℂ) * (c * z) = c * ((u : ℂ) * z)
    ring

/-- The standard complex scalar representation of `U(1)`. -/
def circleScalarRepresentation : Circle →* (ℂ ≃ₗ[ℂ] ℂ) where
  toFun := circleScalarLinearEquiv
  map_one' := by
    ext z
    simp [circleScalarLinearEquiv]
  map_mul' := by
    intro u v
    ext z
    simp [circleScalarLinearEquiv, mul_assoc]

/-- Determinant-line representation induced by the squared `U(1)` character of `Spinᶜ`. -/
def spinCDeterminantRepresentation {G : Type*} [Group G]
    (data : CentralInvolution G) : SpinCComplexRepresentation data ℂ :=
  circleScalarRepresentation.comp (spinCDeterminant data)

/-- Associated bundle of the trivial principal torsor for an arbitrary complex representation. -/
def trivialPrincipalSpinCAssociatedBundleOfRepresentation
    (M : Type*) {G : Type*} [Group G] (data : CentralInvolution G)
    (V : Type*) [AddCommMonoid V] [Module ℂ V]
    (representation : SpinCComplexRepresentation data V) :
    PrincipalSpinCAssociatedBundle data (trivialPrincipalSpinCBundle M data) V representation where
  totalSpace := M × V
  projection := Prod.fst
  quotientMap := fun p v => (p.1, representation p.2 v)
  projection_quotientMap := by intro p v; rfl
  equivariant := by
    intro p g v
    change (p.1, representation (p.2 * g) v) = (p.1, representation p.2 (representation g v))
    rw [representation.map_mul]
    rfl
  fiber_surjective := by
    intro z
    exact ⟨(z.1, 1), z.2, by simp⟩
  orbit_exact := by
    intro p v q w
    constructor
    · intro h
      change (p.1, representation p.2 v) = (q.1, representation q.2 w) at h
      have hbase : p.1 = q.1 := congrArg (fun z : M × V => z.1) h
      have hfiber : representation p.2 v = representation q.2 w :=
        congrArg (fun z : M × V => z.2) h
      refine ⟨p.2⁻¹ * q.2, ?_, ?_⟩
      · change q = (p.1, p.2 * (p.2⁻¹ * q.2))
        simp [hbase]
      · apply (representation q.2).injective
        change representation q.2 w =
          representation q.2 (representation (p.2⁻¹ * q.2)⁻¹ v)
        simpa [representation.map_mul] using hfiber.symm
    · rintro ⟨g, hg, hw⟩
      change (p.1, representation p.2 v) = (q.1, representation q.2 w)
      change q = (p.1, p.2 * g) at hg
      change w = representation g⁻¹ v at hw
      subst q
      subst w
      congr 1
      simp [representation.map_mul]

/-- Associated bundle of the trivial principal torsor with the trivial representation. -/
def trivialPrincipalSpinCAssociatedBundle
    (M : Type*) {G : Type*} [Group G] (data : CentralInvolution G)
    (V : Type*) [AddCommMonoid V] [Module ℂ V] :
    PrincipalSpinCAssociatedBundle data (trivialPrincipalSpinCBundle M data) V
      (trivialSpinCComplexRepresentation data V) :=
  trivialPrincipalSpinCAssociatedBundleOfRepresentation M data V
    (trivialSpinCComplexRepresentation data V)

/-- Closed positive rank-two associated bundle over the flat principal `Spinᶜ(4)` torsor. -/
def flatTrivialPositiveAssociatedSpinCBundle :
    PrincipalSpinCAssociatedBundle fourSpinCentralInvolution
      flatTrivialPrincipalSpinC4Bundle (Fin 2 → ℂ)
      (trivialSpinCComplexRepresentation fourSpinCentralInvolution (Fin 2 → ℂ)) :=
  trivialPrincipalSpinCAssociatedBundle FourSpace fourSpinCentralInvolution (Fin 2 → ℂ)

/-- Closed negative rank-two associated bundle over the flat principal `Spinᶜ(4)` torsor. -/
def flatTrivialNegativeAssociatedSpinCBundle :
    PrincipalSpinCAssociatedBundle fourSpinCentralInvolution
      flatTrivialPrincipalSpinC4Bundle (Fin 2 → ℂ)
      (trivialSpinCComplexRepresentation fourSpinCentralInvolution (Fin 2 → ℂ)) :=
  trivialPrincipalSpinCAssociatedBundle FourSpace fourSpinCentralInvolution (Fin 2 → ℂ)

/-- Closed determinant-line bundle for the squared `U(1)` character of flat `Spinᶜ(4)`. -/
def flatTrivialDeterminantAssociatedSpinCBundle :
    PrincipalSpinCAssociatedBundle fourSpinCentralInvolution
      flatTrivialPrincipalSpinC4Bundle ℂ
      (spinCDeterminantRepresentation fourSpinCentralInvolution) :=
  trivialPrincipalSpinCAssociatedBundleOfRepresentation FourSpace fourSpinCentralInvolution ℂ
    (spinCDeterminantRepresentation fourSpinCentralInvolution)

end GaloisForLFunctions.HTGeometry.SeibergWitten
