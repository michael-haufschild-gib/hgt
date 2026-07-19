import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraDerivation
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraAlgebraicIndependence

/-!
# Universal transverse-clock constraint fields

For an arbitrary commutative algebra `A` and ideal `I`, place countably many copies of `A ⧸ I`
in a direct-sum state space.  A fixed clock shifts the copy index, while a structural law acts by
multiplication in the quotient.  The induced derivation of the symmetric observable algebra
extends to its fraction field.

The complete field jet of the observable labelled by `a : A` occupies the independent clock
layers with the constant quotient class `[a]`.  It is therefore algebraically independent exactly
when `a ∉ I`.  More generally, the complete jets of an arbitrary law family are jointly
algebraically independent exactly when their quotient classes are linearly independent.  Hence
every ideal of every commutative algebra is recovered scheme-theoretically as the exact complete-
jet dependence ideal of one cyclic transverse-clock carrier.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {A : Type v}
  [Field K] [CommRing A] [Algebra K A]

/-- The structural constraint algebra attached to an arbitrary ideal. -/
abbrev UniversalTransverseConstraintAlgebra (I : Ideal A) := A ⧸ I

/-- Countably many independent clock layers over the structural quotient. -/
abbrev UniversalTransverseClockState (I : Ideal A) :=
  ℕ →₀ UniversalTransverseConstraintAlgebra I

/-- The transverse clock advances the layer index and preserves the structural quotient class. -/
def universalTransverseClockShift (I : Ideal A) :
    UniversalTransverseClockState I →ₗ[K] UniversalTransverseClockState I :=
  Finsupp.lmapDomain (UniversalTransverseConstraintAlgebra I) K Nat.succ

/-- One structural law acts coefficientwise on every clock layer. -/
def universalTransverseLawAction (I : Ideal A) (a : A) :
    UniversalTransverseClockState I →ₗ[K] UniversalTransverseClockState I :=
  Finsupp.mapRange.linearMap
    (LinearMap.mulLeft K (Ideal.Quotient.mk I a))

/-- Structural law action commutes with the transverse clock. -/
theorem universalTransverseClockShift_lawAction_commute
    (I : Ideal A) (a : A) :
    Function.Commute (universalTransverseClockShift I)
      (universalTransverseLawAction I a) := by
  intro x
  exact Finsupp.mapDomain_mapRange Nat.succ x
    (LinearMap.mulLeft K (Ideal.Quotient.mk I a))
    (map_zero _) (map_add _)

/-- The common cyclic state before a structural law is applied. -/
def universalTransverseRootState (I : Ideal A) :
    UniversalTransverseClockState I :=
  Finsupp.single 0 (Ideal.Quotient.mk I 1)

/-- Applying `a` to the cyclic root records its quotient class in layer zero. -/
theorem universalTransverseLawAction_rootState
    (I : Ideal A) (a : A) :
    universalTransverseLawAction I a (universalTransverseRootState I) =
      Finsupp.single 0 (Ideal.Quotient.mk I a) := by
  simp [universalTransverseLawAction, universalTransverseRootState]

/-- The symmetric polynomial observable domain of the transverse carrier. -/
abbrev UniversalTransverseConstraintPolynomial (I : Ideal A) :=
  SymmetricAlgebra K (UniversalTransverseClockState I)

/-- The rational differential field of the transverse carrier. -/
abbrev UniversalTransverseConstraintField (I : Ideal A) :=
  FractionRing (UniversalTransverseConstraintPolynomial (K := K) I)

/-- The degree-one observable selected by a structural law. -/
def universalTransverseLawPolynomialObservable
    (I : Ideal A) (a : A) : UniversalTransverseConstraintPolynomial (K := K) I :=
  SymmetricAlgebra.ι K (UniversalTransverseClockState I)
    (universalTransverseLawAction I a (universalTransverseRootState I))

/-- The polynomial derivation induced by the transverse clock. -/
def universalTransverseClockPolynomialDerivation (I : Ideal A) :
    Derivation K (UniversalTransverseConstraintPolynomial (K := K) I)
      (UniversalTransverseConstraintPolynomial (K := K) I) :=
  symmetricAlgebraDerivation (universalTransverseClockShift I)

/-- The canonical embedding of polynomial observables into the rational carrier field. -/
def universalTransverseConstraintFieldEmbedding (I : Ideal A) :
    UniversalTransverseConstraintPolynomial (K := K) I →ₐ[K]
      UniversalTransverseConstraintField (K := K) I :=
  IsScalarTower.toAlgHom K (UniversalTransverseConstraintPolynomial (K := K) I)
    (UniversalTransverseConstraintField (K := K) I)

/-- The polynomial observable domain embeds faithfully in the rational carrier field. -/
theorem universalTransverseConstraintFieldEmbedding_injective (I : Ideal A) :
    Function.Injective (universalTransverseConstraintFieldEmbedding (K := K) I) :=
  IsFractionRing.injective (UniversalTransverseConstraintPolynomial (K := K) I)
    (UniversalTransverseConstraintField (K := K) I)

@[simp]
theorem universalTransverseConstraintFieldEmbedding_apply
    (I : Ideal A) (x : UniversalTransverseConstraintPolynomial (K := K) I) :
    universalTransverseConstraintFieldEmbedding (K := K) I x =
      algebraMap (UniversalTransverseConstraintPolynomial (K := K) I)
        (UniversalTransverseConstraintField (K := K) I) x := rfl

/-- The clock derivation with polynomial input and values embedded in the rational field. -/
def universalTransverseClockSourceDerivation (I : Ideal A) :
    Derivation K (UniversalTransverseConstraintPolynomial (K := K) I)
      (UniversalTransverseConstraintField (K := K) I) :=
  (Algebra.linearMap (UniversalTransverseConstraintPolynomial (K := K) I)
      (UniversalTransverseConstraintField (K := K) I)).compDer
    (universalTransverseClockPolynomialDerivation I)

/-- The quotient-rule extension of the transverse clock to the rational carrier field. -/
def universalTransverseClockFieldDerivation (I : Ideal A) :
    Derivation K (UniversalTransverseConstraintField (K := K) I)
      (UniversalTransverseConstraintField (K := K) I) :=
  fractionRingDerivation (universalTransverseClockSourceDerivation I)

/-- The field derivation agrees with the polynomial clock on embedded observables. -/
theorem universalTransverseClockFieldDerivation_embedding
    (I : Ideal A) (x : UniversalTransverseConstraintPolynomial (K := K) I) :
    universalTransverseClockFieldDerivation I
        (universalTransverseConstraintFieldEmbedding (K := K) I x) =
      universalTransverseConstraintFieldEmbedding (K := K) I
        (universalTransverseClockPolynomialDerivation I x) := by
  rw [universalTransverseClockFieldDerivation,
    universalTransverseConstraintFieldEmbedding_apply,
    fractionRingDerivation_algebraMap]
  rfl

/-- The field observable selected from the one cyclic root by `a`. -/
def universalTransverseLawFieldObservable
    (I : Ideal A) (a : A) : UniversalTransverseConstraintField (K := K) I :=
  universalTransverseConstraintFieldEmbedding (K := K) I
    (universalTransverseLawPolynomialObservable I a)

/-- The complete ordinary differential jet of one structural observable. -/
def universalTransverseLawFieldJet
    (I : Ideal A) (a : A) (n : ℕ) :
    UniversalTransverseConstraintField (K := K) I :=
  ((universalTransverseClockFieldDerivation I :
      UniversalTransverseConstraintField (K := K) I →
        UniversalTransverseConstraintField (K := K) I)^[n])
    (universalTransverseLawFieldObservable I a)

/-- Every complete field jet occupies its matching clock layer with the same quotient class. -/
theorem universalTransverseLawFieldJet_eq_embedded_single
    (I : Ideal A) (a : A) :
    ∀ n : ℕ,
      universalTransverseLawFieldJet I a n =
        universalTransverseConstraintFieldEmbedding (K := K) I
          (SymmetricAlgebra.ι K (UniversalTransverseClockState I)
            (Finsupp.single n (Ideal.Quotient.mk I a))) := by
  intro n
  induction n with
  | zero =>
      simp [universalTransverseLawFieldJet,
        universalTransverseLawFieldObservable,
        universalTransverseLawPolynomialObservable,
        universalTransverseLawAction_rootState]
  | succ n ih =>
      rw [universalTransverseLawFieldJet, Function.iterate_succ_apply',
        ← universalTransverseLawFieldJet, ih,
        universalTransverseClockFieldDerivation_embedding,
        universalTransverseClockPolynomialDerivation,
        symmetricAlgebraDerivation_ι]
      simp [universalTransverseClockShift]

/-- Distinct clock layers carrying one nonzero quotient class are linearly independent. -/
theorem universalTransverseLawState_linearIndependent_iff
    (I : Ideal A) (a : A) :
    LinearIndependent K
        (fun n : ℕ => Finsupp.single n (Ideal.Quotient.mk I a) :
          ℕ → UniversalTransverseClockState I) ↔
      a ∉ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem.not]
  constructor
  · intro h ha
    apply h.ne_zero 0
    simp [ha]
  · intro ha
    exact Finsupp.linearIndependent_single_of_ne_zero (fun _ => ha)

/-- **Universal transverse survivor law.**  In the rational differential field, a structural
law has an algebraically independent complete jet exactly when it survives the prescribed ideal. -/
theorem universalTransverseLawFieldJet_algebraicIndependent_iff
    (I : Ideal A) (a : A) :
    AlgebraicIndependent K (universalTransverseLawFieldJet I a) ↔ a ∉ I := by
  have hjet : universalTransverseLawFieldJet I a =
      universalTransverseConstraintFieldEmbedding (K := K) I ∘
        (fun n : ℕ => SymmetricAlgebra.ι K (UniversalTransverseClockState I)
          (Finsupp.single n (Ideal.Quotient.mk I a))) := by
    funext n
    exact universalTransverseLawFieldJet_eq_embedded_single I a n
  rw [hjet]
  constructor
  · intro hAI
    have hpoly := hAI.of_comp
      (universalTransverseConstraintFieldEmbedding (K := K) I)
    have hstate :=
      (symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent _).mp hpoly
    exact (universalTransverseLawState_linearIndependent_iff I a).mp hstate
  · intro ha
    have hstate := (universalTransverseLawState_linearIndependent_iff I a).mpr ha
    have hpoly : AlgebraicIndependent K
        (fun n : ℕ => SymmetricAlgebra.ι K (UniversalTransverseClockState I)
          (Finsupp.single n (Ideal.Quotient.mk I a))) :=
      (symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent _).mpr hstate
    exact hpoly.map'
      (universalTransverseConstraintFieldEmbedding_injective (K := K) I)

/-- The complete field jets of an arbitrary family of structural laws. -/
def universalTransverseLawFieldJetFamily {α : Type w}
    (I : Ideal A) (a : α → A) :
    (Σ _ : ℕ, α) → UniversalTransverseConstraintField (K := K) I :=
  fun jn => universalTransverseLawFieldJet I (a jn.2) jn.1

/-- Independence of the layered state family is exactly independence in the structural quotient. -/
theorem universalTransverseLawStateFamily_linearIndependent_iff
    {α : Type w} (I : Ideal A) (a : α → A) :
    LinearIndependent K
        (fun jn : Σ _ : ℕ, α =>
          Finsupp.single jn.1 (Ideal.Quotient.mk I (a jn.2)) :
            (Σ _ : ℕ, α) → UniversalTransverseClockState I) ↔
      LinearIndependent K (fun j => Ideal.Quotient.mk I (a j)) := by
  constructor
  · intro h
    have hall : ∀ n : ℕ,
        LinearIndependent K (fun j : α => Ideal.Quotient.mk I (a j)) :=
      Finsupp.linearIndependent_single_iff.mp h
    exact hall 0
  · intro h
    exact Finsupp.linearIndependent_single
      (fun _ : ℕ => fun j : α => Ideal.Quotient.mk I (a j)) (fun _ => h)

/-- **Universal transverse differential matroid.**  The complete jets of any structural law
family in the rational differential field are jointly algebraically independent exactly when the
law classes are linearly independent in `A ⧸ I`. -/
theorem universalTransverseLawFieldJetFamily_algebraicIndependent_iff
    {α : Type w} (I : Ideal A) (a : α → A) :
    AlgebraicIndependent K (universalTransverseLawFieldJetFamily I a) ↔
      LinearIndependent K (fun j => Ideal.Quotient.mk I (a j)) := by
  have hjet : universalTransverseLawFieldJetFamily I a =
      universalTransverseConstraintFieldEmbedding (K := K) I ∘
        (fun jn : Σ _ : ℕ, α =>
          SymmetricAlgebra.ι K (UniversalTransverseClockState I)
            (Finsupp.single jn.1 (Ideal.Quotient.mk I (a jn.2)))) := by
    funext jn
    exact universalTransverseLawFieldJet_eq_embedded_single I (a jn.2) jn.1
  rw [hjet]
  constructor
  · intro hAI
    have hpoly := hAI.of_comp
      (universalTransverseConstraintFieldEmbedding (K := K) I)
    have hstate :=
      (symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent _).mp hpoly
    exact (universalTransverseLawStateFamily_linearIndependent_iff I a).mp hstate
  · intro ha
    have hstate :=
      (universalTransverseLawStateFamily_linearIndependent_iff I a).mpr ha
    have hpoly : AlgebraicIndependent K
        (fun jn : Σ _ : ℕ, α =>
          SymmetricAlgebra.ι K (UniversalTransverseClockState I)
            (Finsupp.single jn.1 (Ideal.Quotient.mk I (a jn.2)))) :=
      (symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent _).mpr hstate
    exact hpoly.map'
      (universalTransverseConstraintFieldEmbedding_injective (K := K) I)

/-- **Arbitrary affine-scheme universality in a differential field.**  For every ideal of every
commutative algebra, including nonradical and nonhomogeneous ideals, the structural laws whose
complete field jets fail algebraic independence are exactly that ideal. -/
theorem universalTransverseConstraintScheme_exact
    (I : Ideal A) :
    {a : A | ¬ AlgebraicIndependent K (universalTransverseLawFieldJet I a)} =
      (I : Set A) := by
  ext a
  rw [Set.mem_setOf_eq,
    universalTransverseLawFieldJet_algebraicIndependent_iff]
  simp

/-- Every proper affine constraint scheme has one hypertranscendental cyclic root in the
universal transverse rational differential field. -/
theorem universalTransverseConstraintRoot_hypertranscendental
    (I : Ideal A) (hI : I ≠ ⊤) :
    AlgebraicIndependent K (universalTransverseLawFieldJet I 1) := by
  rw [universalTransverseLawFieldJet_algebraicIndependent_iff]
  exact (Ideal.ne_top_iff_one I).mp hI

end

end GaloisForLFunctions.HTGeometry
