import GaloisForLFunctions.HTGeometry.CommutingCyclicObservableHorizon
import GaloisForLFunctions.HTGeometry.SymmetricAlgebraDerivation

/-!
# A complete differential classification of graded cyclic commuting horizons

Let `I` be a homogeneous ideal in the commutative law algebra `K[X_i]`.  Multiplication by each
law generator acts on the cyclic state module `K[X_i] / I`.  We extend these pairwise commuting
linear actions to pairwise commuting derivations of the symmetric observable algebra
`Sym_K(K[X_i] / I)`.

For the single root observable represented by the cyclic state `1`, the `n`-th repeated directional
derivative is exactly the observable represented by the law power `(∑ c_i X_i)^n`.  It follows that
the complete differential jet is algebraically dependent precisely when the directional law form
lies in `rad(I)`.  Thus every complete hypertranscendence horizon in this graded cyclic commuting
differential model is the carrier of a vector subspace.

This is an actual differential-domain theorem, not merely a classification of a proxy state
sequence.  Together with the free-word realization theorem, it exhibits a strict phase boundary:
the nonlinear crossing horizon is realizable by one free noncommuting observable but impossible for
every graded cyclic commuting differential observable constructed here.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

universe u v

variable {K : Type u} {ι : Type v} [Field K] [Fintype ι]

/-- The cyclic state module on which the commutative law algebra acts. -/
abbrev CyclicLawState (I : Ideal (MvPolynomial ι K)) :=
  MvPolynomial ι K ⧸ I

/-- Multiplication by one law generator on the cyclic state module. -/
def cyclicLawAction (I : Ideal (MvPolynomial ι K)) (i : ι) :
    CyclicLawState I →ₗ[K] CyclicLawState I :=
  LinearMap.mulLeft K (Ideal.Quotient.mk I (X i))

omit [Fintype ι] in
/-- The generator actions commute because the law algebra is commutative. -/
theorem cyclicLawAction_commute (I : Ideal (MvPolynomial ι K)) (i j : ι) :
    Function.Commute (cyclicLawAction I i) (cyclicLawAction I j) := by
  intro q
  simp [cyclicLawAction, mul_left_comm]

/-- Multiplication by the law form of one direction. -/
def cyclicDirectionalAction (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    CyclicLawState I →ₗ[K] CyclicLawState I :=
  LinearMap.mulLeft K (Ideal.Quotient.mk I (lawLinearForm c))

/-- Directional law action is the corresponding linear combination of generator actions. -/
theorem cyclicDirectionalAction_apply_eq_sum
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) (q : CyclicLawState I) :
    cyclicDirectionalAction I c q = ∑ i, c i • cyclicLawAction I i q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K I q
  simp only [cyclicDirectionalAction, cyclicLawAction, LinearMap.mulLeft_apply]
  rw [lawLinearForm, Fintype.linearCombination_apply]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  change (Ideal.Quotient.mkₐ K I) (c i • X i) *
      (Ideal.Quotient.mkₐ K I) p = _
  rw [map_smul, smul_mul_assoc]
  rw [Ideal.Quotient.mkₐ_eq_mk]

/-- The derivation of the observable algebra induced by one law generator. -/
def cyclicLawDerivation (I : Ideal (MvPolynomial ι K)) (i : ι) :
    Derivation K (SymmetricAlgebra K (CyclicLawState I))
      (SymmetricAlgebra K (CyclicLawState I)) :=
  symmetricAlgebraDerivation (cyclicLawAction I i)

omit [Fintype ι] in
/-- The law-generator derivations commute on the full observable algebra. -/
theorem cyclicLawDerivation_commute
    (I : Ideal (MvPolynomial ι K)) (i j : ι) :
    Function.Commute (cyclicLawDerivation I i) (cyclicLawDerivation I j) :=
  symmetricAlgebraDerivation_commute _ _ (cyclicLawAction_commute I i j)

/-- The directional derivation determined by a point of law space. -/
def cyclicDirectionalDerivation (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    Derivation K (SymmetricAlgebra K (CyclicLawState I))
      (SymmetricAlgebra K (CyclicLawState I)) :=
  ∑ i, c i • cyclicLawDerivation I i

/-- The directional derivation acts on a linear observable by the directional state action. -/
theorem cyclicDirectionalDerivation_ι
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) (q : CyclicLawState I) :
    cyclicDirectionalDerivation I c
        (SymmetricAlgebra.ι K (CyclicLawState I) q) =
      SymmetricAlgebra.ι K (CyclicLawState I) (cyclicDirectionalAction I c q) := by
  classical
  rw [cyclicDirectionalDerivation]
  change (∑ i, c i • cyclicLawDerivation I i)
      (SymmetricAlgebra.ι K (CyclicLawState I) q) = _
  rw [show (∑ i, c i • cyclicLawDerivation I i)
      (SymmetricAlgebra.ι K (CyclicLawState I) q) =
        ∑ i, c i • cyclicLawDerivation I i
          (SymmetricAlgebra.ι K (CyclicLawState I) q) by
    induction (Finset.univ : Finset ι) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Derivation.add_apply, ih,
          Finset.sum_insert hi, Derivation.smul_apply]]
  simp_rw [cyclicLawDerivation, symmetricAlgebraDerivation_ι]
  rw [cyclicDirectionalAction_apply_eq_sum]
  conv_rhs => rw [map_sum]
  simp

/-- The one observable whose complete directional differential orbit is classified below. -/
def cyclicRootObservable (I : Ideal (MvPolynomial ι K)) :
    SymmetricAlgebra K (CyclicLawState I) :=
  SymmetricAlgebra.ι K (CyclicLawState I) (Ideal.Quotient.mk I 1)

/-- The actual `n`-fold directional derivative of the root observable. -/
def cyclicDirectionalJet (I : Ideal (MvPolynomial ι K)) (c : ι → K)
    (n : ℕ) : SymmetricAlgebra K (CyclicLawState I) :=
  ((cyclicDirectionalDerivation I c :
    SymmetricAlgebra K (CyclicLawState I) → SymmetricAlgebra K (CyclicLawState I))^[n])
      (cyclicRootObservable I)

/-- One directional state action advances the cyclic law-power orbit by one step. -/
theorem cyclicDirectionalAction_power
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) (n : ℕ) :
    cyclicDirectionalAction I c
        (cyclicPowerState I (lawLinearForm c) n) =
      cyclicPowerState I (lawLinearForm c) (n + 1) := by
  simp [cyclicDirectionalAction, cyclicPowerState, pow_succ, mul_comm]

/-- **Differential-orbit identity.**  Every iterated derivative of the root is the canonical
observable of the corresponding cyclic law power. -/
theorem cyclicDirectionalJet_eq_observableJet
    (I : Ideal (MvPolynomial ι K)) (c : ι → K) :
    ∀ n : ℕ, cyclicDirectionalJet I c n = commutingCyclicObservableJet I c n := by
  intro n
  induction n with
  | zero =>
      simp [cyclicDirectionalJet, cyclicRootObservable,
        commutingCyclicObservableJet, cyclicSymmetricObservableJet,
        cyclicPowerState]
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, cyclicDirectionalJet,
        Function.iterate_succ_apply', ← cyclicDirectionalJet, ih]
      rw [commutingCyclicObservableJet, cyclicSymmetricObservableJet,
        cyclicDirectionalDerivation_ι, cyclicDirectionalAction_power]
      simp [cyclicSymmetricObservableJet]

/-- **Complete cyclic differential horizon classification.**  Algebraic dependence of the full
iterated directional jet occurs exactly on the radical subspace of law directions. -/
theorem not_algebraicIndependent_cyclicDirectionalJet_iff
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K))
    (c : ι → K) :
    (¬ AlgebraicIndependent K (cyclicDirectionalJet I c)) ↔
      c ∈ commutingCyclicNilpotenceHorizon I := by
  have hjet : cyclicDirectionalJet I c = commutingCyclicObservableJet I c :=
    funext (cyclicDirectionalJet_eq_observableJet I c)
  rw [hjet]
  exact not_algebraicIndependent_commutingCyclicObservableJet_iff I hI c

/-- The complete differential-dependence horizon is literally the carrier of the radical
submodule, hence is closed under arbitrary linear superposition. -/
theorem cyclicDifferentialDependenceHorizon_eq_radicalSubspace
    (I : Ideal (MvPolynomial ι K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule ι K)) :
    {c : ι → K | ¬ AlgebraicIndependent K (cyclicDirectionalJet I c)} =
      (commutingCyclicNilpotenceHorizon I : Set (ι → K)) := by
  ext c
  exact not_algebraicIndependent_cyclicDirectionalJet_iff I hI c

/-- The nonlinear crossing cone cannot be the complete differential-dependence horizon of any
homogeneous graded cyclic commuting model. -/
theorem crossingCone_not_cyclicDifferentialDependenceHorizon
    (I : Ideal (MvPolynomial (Fin 2) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 2) K)) :
    {c : Fin 2 → K | ¬ AlgebraicIndependent K (cyclicDirectionalJet I c)} ≠
      crossingCone K := by
  rw [cyclicDifferentialDependenceHorizon_eq_radicalSubspace I hI]
  exact crossingCone_not_commutingCyclicNilpotenceHorizon I

end

end GaloisForLFunctions.HTGeometry
