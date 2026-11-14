import GaloisForLFunctions.RepresentationLifting.QuadraticFunctoriality
import GaloisForLFunctions.RepresentationLifting.QuadraticCohomology

/-!
# Naturality and rank-one annihilation of quadratic classes

An intertwining rectangular matrix induces a morphism of both short exact
quadratic sequences. Thus the double connecting map, invariant quadratic class,
and Yoneda two-extension commute with coefficient maps. A map to a representation
of dimension at most one annihilates the class after Frobenius twisting.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace GaloisForLFunctions.RepresentationLifting
universe u
variable {k G ι κ : Type u} [CommRing k] [CharP k 2] [Group G]
  [Fintype ι] [LinearOrder ι] [Fintype κ] [LinearOrder κ]
  (ρ : G →* Matrix ι ι k) (σ : G →* Matrix κ κ k)
  (A : Matrix κ ι k) (hA : ∀ g, A * ρ g = σ g * A)

/-- The symmetric square of an equivariant rectangular matrix. -/
def quadraticSymmetricHom :
    Rep.of (quadraticSymmetricRepresentation ρ) ⟶ Rep.of (quadraticSymmetricRepresentation σ) :=
  Rep.ofHom ⟨quadraticSymmetricMap A, fun g => by
    change (quadraticSymmetricMap A).comp (Matrix.toLin' (HTGeometry.symmetricSquareMatrixGeneral (ρ g))) =
      (Matrix.toLin' (HTGeometry.symmetricSquareMatrixGeneral (σ g))).comp (quadraticSymmetricMap A)
    rw [← quadraticSymmetricMap_square, ← quadraticSymmetricMap_square,
      ← quadraticSymmetricMap_mul, ← quadraticSymmetricMap_mul, hA g]⟩

/-- The tensor square of an equivariant rectangular matrix. -/
def quadraticTensorHom :
    Rep.of (quadraticTensorRepresentation ρ) ⟶ Rep.of (quadraticTensorRepresentation σ) :=
  Rep.ofHom ⟨tensorTransport A, fun g => by
    apply LinearMap.ext
    intro T
    change tensorTransport A (tensorTransport (ρ g) T) =
      tensorTransport (σ g) (tensorTransport A T)
    rw [← tensorTransport_mul, ← tensorTransport_mul, hA g]⟩

/-- Entrywise Frobenius preserves the intertwining relation. -/
def quadraticFrobeniusHom :
    Rep.of (quadraticFrobeniusRepresentation ρ) ⟶ Rep.of (quadraticFrobeniusRepresentation σ) :=
  Rep.ofHom ⟨Matrix.toLin' (A.map (frobenius k 2)), fun g => by
    have hm := congrArg (fun B : Matrix κ ι k => B.map (frobenius k 2)) (hA g)
    rw [Matrix.map_mul, Matrix.map_mul] at hm
    change (Matrix.toLin' (A.map (frobenius k 2))).comp (Matrix.toLin' ((ρ g).map (frobenius k 2))) =
      (Matrix.toLin' ((σ g).map (frobenius k 2))).comp (Matrix.toLin' (A.map (frobenius k 2)))
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hm]⟩

/-- Restriction of tensor transport to the polarization image. -/
def quadraticMiddleMap : quadraticMiddle (k := k) (ι := ι) →ₗ[k]
    quadraticMiddle (k := k) (ι := κ) where
  toFun T := ⟨tensorTransport A T.1, tensorProjection_transport_zero A T.1 T.2⟩
  map_add' T U := Subtype.ext (map_add (tensorTransport A) T.1 U.1)
  map_smul' c T := Subtype.ext (map_smul (tensorTransport A) c T.1)

/-- The induced equivariant map on polarization images. -/
def quadraticMiddleHom :
    Rep.of (quadraticMiddleRepresentation ρ) ⟶ Rep.of (quadraticMiddleRepresentation σ) :=
  Rep.ofHom ⟨quadraticMiddleMap A, fun g => by
    apply LinearMap.ext
    intro T
    apply Subtype.ext
    change tensorTransport A (tensorTransport (ρ g) T.1) =
      tensorTransport (σ g) (tensorTransport A T.1)
    rw [← tensorTransport_mul, ← tensorTransport_mul, hA g]⟩

/-- Coefficient maps preserve the pure-square and polarization sequence. -/
def quadraticFirstSequenceHom : quadraticFirstSequence ρ ⟶ quadraticFirstSequence σ where
  τ₁ := quadraticFrobeniusHom ρ σ A hA
  τ₂ := quadraticSymmetricHom ρ σ A hA
  τ₃ := quadraticMiddleHom ρ σ A hA
  comm₁₂ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact (quadraticSymmetricMap_squareDiagonal A x).symm
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    apply Subtype.ext
    exact quadraticSymmetricMap_norm A q

/-- Coefficient maps preserve the polarization and tensor-multiplication sequence. -/
def quadraticSecondSequenceHom : quadraticSecondSequence ρ ⟶ quadraticSecondSequence σ where
  τ₁ := quadraticMiddleHom ρ σ A hA
  τ₂ := quadraticTensorHom ρ σ A hA
  τ₃ := quadraticSymmetricHom ρ σ A hA
  comm₁₂ := rfl
  comm₂₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro T
    exact (quadraticSymmetricMap_projection A T).symm

/-- Quadratic connecting maps commute with coefficient maps in every degree. -/
theorem quadraticConnecting_naturality (n : ℕ) :
    quadraticConnecting ρ n ≫
      (groupCohomology.functor k G (n + 2)).map (quadraticFrobeniusHom ρ σ A hA) =
    (groupCohomology.functor k G n).map (quadraticSymmetricHom ρ σ A hA) ≫
      quadraticConnecting σ n := by
  have h₁ := groupCohomology.δ_naturality (quadraticFirstSequence_shortExact ρ)
    (quadraticFirstSequence_shortExact σ) (quadraticFirstSequenceHom ρ σ A hA)
    (n + 1) (n + 2) rfl
  have h₂ := groupCohomology.δ_naturality (quadraticSecondSequence_shortExact ρ)
    (quadraticSecondSequence_shortExact σ) (quadraticSecondSequenceHom ρ σ A hA)
    n (n + 1) rfl
  change groupCohomology.δ (quadraticFirstSequence_shortExact ρ) (n + 1) (n + 2) rfl ≫
      (groupCohomology.functor k G (n + 2)).map (quadraticFrobeniusHom ρ σ A hA) =
    (groupCohomology.functor k G (n + 1)).map (quadraticMiddleHom ρ σ A hA) ≫
      groupCohomology.δ (quadraticFirstSequence_shortExact σ) (n + 1) (n + 2) rfl at h₁
  change groupCohomology.δ (quadraticSecondSequence_shortExact ρ) n (n + 1) rfl ≫
      (groupCohomology.functor k G (n + 1)).map (quadraticMiddleHom ρ σ A hA) =
    (groupCohomology.functor k G n).map (quadraticSymmetricHom ρ σ A hA) ≫
      groupCohomology.δ (quadraticSecondSequence_shortExact σ) n (n + 1) rfl at h₂
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => groupCohomology.δ (quadraticSecondSequence_shortExact ρ)
        n (n + 1) rfl ≫ f) h₁).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ groupCohomology.δ (quadraticFirstSequence_shortExact σ)
            (n + 1) (n + 2) rfl) h₂).trans (Category.assoc _ _ _))))

/-- A Frobenius-twisted map to a rank-one target kills every quadratic connecting class. -/
theorem quadraticConnecting_rankOne_pushforward_zero [Subsingleton κ] (n : ℕ) :
    quadraticConnecting ρ n ≫
      (groupCohomology.functor k G (n + 2)).map (quadraticFrobeniusHom ρ σ A hA) = 0 :=
  (quadraticConnecting_naturality ρ σ A hA n).trans
    ((congrArg (fun f => (groupCohomology.functor k G n).map
      (quadraticSymmetricHom ρ σ A hA) ≫ f) (quadraticConnecting_rankOne_zero σ n)).trans comp_zero)

/-- The invariant-tensor obstruction κ is natural under coefficient maps. -/
theorem quadraticCohomologyClass_naturality
    (q : (quadraticSymmetricRepresentation ρ).invariants) :
    ((groupCohomology.functor k G 2).map (quadraticFrobeniusHom ρ σ A hA)).hom
      (quadraticCohomologyClass ρ q) =
    quadraticCohomologyClass σ
      (((Rep.invariantsFunctor k G).map (quadraticSymmetricHom ρ σ A hA)).hom q) := by
  have h₀ : (groupCohomology.H0Iso (Rep.of (quadraticSymmetricRepresentation ρ))).inv ≫
      (groupCohomology.functor k G 0).map (quadraticSymmetricHom ρ σ A hA) =
    (Rep.invariantsFunctor k G).map (quadraticSymmetricHom ρ σ A hA) ≫
      (groupCohomology.H0Iso (Rep.of (quadraticSymmetricRepresentation σ))).inv :=
    (CommSq.vert_inv ⟨groupCohomology.map_id_comp_H0Iso_hom
      (quadraticSymmetricHom ρ σ A hA)⟩).w.symm
  have h := quadraticConnecting_naturality ρ σ A hA 0
  have hq := congrArg (fun f => f.hom
    ((groupCohomology.H0Iso (Rep.of (quadraticSymmetricRepresentation ρ))).inv.hom q)) h
  have hq₀ := congrArg (fun f => f.hom q) h₀
  exact hq.trans (congrArg (quadraticConnecting σ 0).hom hq₀)

/-- The quadratic Yoneda class is natural in both endpoint coefficients. -/
theorem quadraticSequenceClass_naturality :
    (quadraticSequenceClass ρ).comp (Ext.mk₀ (quadraticFrobeniusHom ρ σ A hA)) (add_zero 2) =
      (Ext.mk₀ (quadraticSymmetricHom ρ σ A hA)).comp (quadraticSequenceClass σ) (zero_add 2) := by
  have h₁ := (quadraticFirstSequence_shortExact ρ).extClass_naturality
    (quadraticFirstSequence_shortExact σ) (quadraticFirstSequenceHom ρ σ A hA)
  have h₂ := (quadraticSecondSequence_shortExact ρ).extClass_naturality
    (quadraticSecondSequence_shortExact σ) (quadraticSecondSequenceHom ρ σ A hA)
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).trans
    ((congrArg (fun f => (quadraticSecondSequence_shortExact ρ).extClass.comp f rfl) h₁).trans
      ((Ext.comp_assoc_of_second_deg_zero _ _ _ rfl).symm.trans
        ((congrArg (fun f => f.comp (quadraticFirstSequence_shortExact σ).extClass rfl) h₂).trans
          (Ext.comp_assoc _ _ _ rfl rfl rfl))))

/-- Frobenius-twisted rank-one pushforward annihilates the Yoneda class itself. -/
theorem quadraticSequenceClass_rankOne_pushforward_zero [Subsingleton κ] :
    (quadraticSequenceClass ρ).comp (Ext.mk₀ (quadraticFrobeniusHom ρ σ A hA)) (add_zero 2) = 0 :=
  (quadraticSequenceClass_naturality ρ σ A hA).trans
    ((congrArg (fun f : Ext (Rep.of (quadraticSymmetricRepresentation σ))
        (Rep.of (quadraticFrobeniusRepresentation σ)) 2 =>
      (Ext.mk₀ (quadraticSymmetricHom ρ σ A hA)).comp f (zero_add 2))
        (quadraticSequenceClass_rankOne_zero σ)).trans (Ext.comp_zero _ _ 2 2 rfl))

/-- In degree zero, every invariant quadratic tensor has zero rank-one pushforward. -/
theorem quadraticCohomologyClass_rankOne_pushforward_zero [Subsingleton κ]
    (q : (quadraticSymmetricRepresentation ρ).invariants) :
    ((groupCohomology.functor k G 2).map (quadraticFrobeniusHom ρ σ A hA)).hom
      (quadraticCohomologyClass ρ q) = 0 := by
  exact congrArg (fun f : groupCohomology (Rep.of (quadraticSymmetricRepresentation ρ)) 0 ⟶
      groupCohomology (Rep.of (quadraticFrobeniusRepresentation σ)) 2 =>
    f.hom ((groupCohomology.H0Iso (Rep.of (quadraticSymmetricRepresentation ρ))).inv.hom q))
      (quadraticConnecting_rankOne_pushforward_zero ρ σ A hA 0)

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.quadraticFirstSequenceHom
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticConnecting_naturality
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticCohomologyClass_naturality
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticSequenceClass_rankOne_pushforward_zero
#print axioms GaloisForLFunctions.RepresentationLifting.quadraticCohomologyClass_rankOne_pushforward_zero
