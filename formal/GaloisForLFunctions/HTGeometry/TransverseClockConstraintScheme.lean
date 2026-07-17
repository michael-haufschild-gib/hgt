import GaloisForLFunctions.HTGeometry.SymmetricAlgebraDerivation
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraAlgebraicIndependence

/-!
# Arbitrary constraint schemes with a transverse hypertranscendental clock

Let `I` be an arbitrary ideal in a commutative polynomial law algebra `K[X_i]`.  The quotient
`K[X_i] / I` records the complete structural constraint scheme, including nilpotents and embedded
components.  We place countably many copies of this quotient in a transverse clock state space.
The structural law acts coefficientwise, while the clock shifts the copy index.

In the symmetric observable algebra, every law polynomial outside `I` then has an algebraically
independent complete clock jet, whereas every polynomial in `I` has the zero jet.  Thus the exact
DA-relative structural annihilator is `I` for every ideal, with no radicality, homogeneity, or
reducedness hypothesis.

This is the unconditional algebraic core of affine constraint-spectrum universality.  It does not
assert that the model is realized by an entire or meromorphic function; that analytic realization
is a separate theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v w

variable {K : Type u} {ι : Type v} [Field K]

/-- The cyclic structural law algebra. -/
abbrev TransverseConstraintAlgebra (I : Ideal (MvPolynomial ι K)) :=
  MvPolynomial ι K ⧸ I

/-- Countably many clock layers over one structural constraint algebra. -/
abbrev TransverseClockState (I : Ideal (MvPolynomial ι K)) :=
  ℕ →₀ TransverseConstraintAlgebra I

/-- The transverse clock advances the layer index and does not alter structural coefficients. -/
def transverseClockShift (I : Ideal (MvPolynomial ι K)) :
    TransverseClockState I →ₗ[K] TransverseClockState I :=
  Finsupp.lmapDomain (TransverseConstraintAlgebra I) K Nat.succ

/-- A clock layer advances by exactly one step. -/
theorem transverseClockShift_single
    (I : Ideal (MvPolynomial ι K)) (n : ℕ) (a : TransverseConstraintAlgebra I) :
    transverseClockShift I (Finsupp.single n a) = Finsupp.single (n + 1) a := by
  simp [transverseClockShift]

/-- A structural law polynomial acts coefficientwise on every clock layer. -/
def transverseLawAction (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    TransverseClockState I →ₗ[K] TransverseClockState I :=
  Finsupp.mapRange.linearMap
    (LinearMap.mulLeft K (Ideal.Quotient.mk I p))

/-- Structural law and transverse clock commute exactly. -/
theorem transverseClockShift_transverseLawAction_commute
    (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    Function.Commute (transverseClockShift I) (transverseLawAction I p) := by
  intro x
  exact Finsupp.mapDomain_mapRange Nat.succ x
    (LinearMap.mulLeft K (Ideal.Quotient.mk I p))
    (map_zero _) (map_add _)

/-- The common cyclic source state before applying a structural law. -/
def transverseConstraintRootState (I : Ideal (MvPolynomial ι K)) :
    TransverseClockState I :=
  Finsupp.single 0 (Ideal.Quotient.mk I 1)

/-- Applying `p` to the common root places its quotient class in clock layer zero. -/
theorem transverseLawAction_rootState
    (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    transverseLawAction I p (transverseConstraintRootState I) =
      Finsupp.single 0 (Ideal.Quotient.mk I p) := by
  simp [transverseLawAction, transverseConstraintRootState]

/-- The symmetric observable obtained by applying one structural law to the common root. -/
def transverseLawObservable (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    SymmetricAlgebra K (TransverseClockState I) :=
  SymmetricAlgebra.ι K (TransverseClockState I)
    (transverseLawAction I p (transverseConstraintRootState I))

/-- The derivation induced by the transverse clock shift. -/
def transverseClockDerivation (I : Ideal (MvPolynomial ι K)) :
    Derivation K (SymmetricAlgebra K (TransverseClockState I))
      (SymmetricAlgebra K (TransverseClockState I)) :=
  symmetricAlgebraDerivation (transverseClockShift I)

/-- The actual complete transverse differential jet of a structural law observable. -/
def transverseLawJet (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K)
    (n : ℕ) : SymmetricAlgebra K (TransverseClockState I) :=
  ((transverseClockDerivation I :
      SymmetricAlgebra K (TransverseClockState I) →
        SymmetricAlgebra K (TransverseClockState I))^[n])
    (transverseLawObservable I p)

/-- The complete transverse jets of an arbitrary family of structural laws.  The clock layer is
the outer index so that distinct derivative orders occupy disjoint summands. -/
def transverseLawJetFamily {α : Type w}
    (I : Ideal (MvPolynomial ι K)) (p : α → MvPolynomial ι K) :
    (Σ _ : ℕ, α) → SymmetricAlgebra K (TransverseClockState I) :=
  fun jn ↦ transverseLawJet I (p jn.2) jn.1

/-- Every clock derivative moves the structural quotient class to the matching layer. -/
theorem transverseLawJet_eq_single
    (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    ∀ n : ℕ,
      transverseLawJet I p n =
        SymmetricAlgebra.ι K (TransverseClockState I)
          (Finsupp.single n (Ideal.Quotient.mk I p)) := by
  intro n
  induction n with
  | zero =>
      simp [transverseLawJet, transverseLawObservable,
        transverseLawAction_rootState]
  | succ n ih =>
      rw [transverseLawJet, Function.iterate_succ_apply', ← transverseLawJet, ih]
      rw [transverseClockDerivation, symmetricAlgebraDerivation_ι,
        transverseClockShift_single]

/-- Distinct clock layers carrying one nonzero structural class are linearly independent. -/
theorem transverseLawState_linearIndependent_iff
    (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    LinearIndependent K
        (fun n : ℕ => Finsupp.single n (Ideal.Quotient.mk I p) :
          ℕ → TransverseClockState I) ↔
      p ∉ I := by
  rw [← Ideal.Quotient.eq_zero_iff_mem.not]
  constructor
  · intro h hp
    apply h.ne_zero 0
    simp [hp]
  · intro hp
    exact Finsupp.linearIndependent_single_of_ne_zero (fun _ => hp)

/-- **Exact survivor law.**  A structural operator has a completely algebraically independent
transverse jet exactly when it survives the prescribed constraint ideal. -/
theorem transverseLawJet_algebraicIndependent_iff
    (I : Ideal (MvPolynomial ι K)) (p : MvPolynomial ι K) :
    AlgebraicIndependent K (transverseLawJet I p) ↔ p ∉ I := by
  have hjet : transverseLawJet I p =
      fun n : ℕ => SymmetricAlgebra.ι K (TransverseClockState I)
        (Finsupp.single n (Ideal.Quotient.mk I p)) :=
    funext (transverseLawJet_eq_single I p)
  rw [hjet, symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent,
    transverseLawState_linearIndependent_iff]

/-- **Exact transverse differential matroid.**  A family of structural laws has a jointly
algebraically independent packet of all clock derivatives exactly when its residue classes are
linearly independent in the prescribed constraint algebra.  Thus the construction recovers the
entire linear matroid of `K[X_i] / I`, not only its zero class. -/
theorem transverseLawJetFamily_algebraicIndependent_iff
    {α : Type w} (I : Ideal (MvPolynomial ι K)) (p : α → MvPolynomial ι K) :
    AlgebraicIndependent K (transverseLawJetFamily I p) ↔
      LinearIndependent K (fun j ↦ Ideal.Quotient.mk I (p j)) := by
  have hjet : transverseLawJetFamily I p =
      fun jn : Σ _ : ℕ, α ↦ SymmetricAlgebra.ι K (TransverseClockState I)
        (Finsupp.single jn.1 (Ideal.Quotient.mk I (p jn.2))) := by
    funext jn
    exact transverseLawJet_eq_single I (p jn.2) jn.1
  rw [hjet, symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent]
  constructor
  · intro h
    have hall : ∀ n : ℕ,
        LinearIndependent K (fun j : α ↦ Ideal.Quotient.mk I (p j)) :=
      (Finsupp.linearIndependent_single_iff.mp h)
    exact hall 0
  · intro h
    exact Finsupp.linearIndependent_single
      (fun _ : ℕ ↦ fun j : α ↦ Ideal.Quotient.mk I (p j)) (fun _ ↦ h)

/-- **Arbitrary constraint-scheme universality.**  For every ideal, including nonradical and
nonhomogeneous ideals, the operators whose complete transverse jets fail algebraic independence
are exactly the original ideal.  Nilpotent and embedded constraint structure is not lost. -/
theorem transverseClock_constraintScheme_exact
    (I : Ideal (MvPolynomial ι K)) :
    {p : MvPolynomial ι K | ¬ AlgebraicIndependent K (transverseLawJet I p)} =
      (I : Set (MvPolynomial ι K)) := by
  ext p
  rw [Set.mem_setOf_eq, transverseLawJet_algebraicIndependent_iff]
  simp

/-- Every proper constraint scheme has a single root observable with an algebraically independent
complete transverse clock jet. -/
theorem transverseConstraintRoot_hypertranscendental
    (I : Ideal (MvPolynomial ι K)) (hI : I ≠ ⊤) :
    AlgebraicIndependent K (transverseLawJet I 1) := by
  rw [transverseLawJet_algebraicIndependent_iff]
  exact (Ideal.ne_top_iff_one I).mp hI

end

end GaloisForLFunctions.HTGeometry
