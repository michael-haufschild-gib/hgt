import GaloisForLFunctions.HTGeometry.PeriodicMatrixFactorizationHorizon

/-!
# Generalized Clifford shift horizons

Let `A` be an internal principal-symbol operator satisfying `A^d = F·1`.  Suspending `A` by a
unilateral grade shift turns that finite-width relation into an exact complete
hypertranscendence horizon: the root orbit is killed at order `d` when `F = 0`, while for
`F ≠ 0` it is linearly independent because every nonzero iterate occupies a fresh grade.

The induced derivation of the symmetric observable algebra therefore has algebraically
independent complete jet exactly when `F ≠ 0`.  Applied pointwise to a linear pencil of internal
operators, this is the general shift-suspension theorem for a finite-dimensional representation
of the Roby generalized Clifford algebra of a homogeneous form.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {K : Type u} {M : Type v}
  [Field K] [AddCommGroup M] [Module K M]

/-- Suspend one internal endomorphism by one unilateral grade shift. -/
def generalizedCliffordShiftOperator (A : Module.End K M) :
    Module.End K (ℕ → M) :=
  periodicUnilateralShift.comp (periodicPointwiseEnd A)

@[simp]
theorem generalizedCliffordShiftOperator_level
    (A : Module.End K M) (n : ℕ) (m : M) :
    generalizedCliffordShiftOperator A (periodicLevel n m) =
      periodicLevel (n + 1) (A m) := by
  simp [generalizedCliffordShiftOperator]

/-- The suspended orbit records the internal orbit in successive disjoint grades. -/
theorem generalizedCliffordShiftOperator_orbit
    (A : Module.End K M) (m : M) :
    ∀ n : ℕ,
      (((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
        (periodicLevel 0 m)) =
      periodicLevel n (((A : M → M)^[n]) m) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        generalizedCliffordShiftOperator_level,
        Function.iterate_succ_apply']

/-- A nonzero scalar power relation makes the internal principal symbol injective. -/
theorem generalizedCliffordPowerRelation_injective
    (A : Module.End K M) (d : ℕ) (F : K)
    (hd : d ≠ 0) (hpower : A ^ d = F • LinearMap.id) (hF : F ≠ 0) :
    Function.Injective A := by
  apply Module.End.injective_of_iterate_injective hd
  rw [hpower]
  simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
    (smul_right_injective M hF)

/-- Off the scalar horizon, no internal iterate of a nonzero root can vanish. -/
theorem generalizedCliffordPowerRelation_orbit_ne_zero
    (A : Module.End K M) (d : ℕ) (F : K) (m : M)
    (hd : d ≠ 0) (hpower : A ^ d = F • LinearMap.id)
    (hF : F ≠ 0) (hm : m ≠ 0) :
    ∀ n : ℕ, ((A : M → M)^[n]) m ≠ 0 := by
  intro n hn
  apply hm
  apply (generalizedCliffordPowerRelation_injective A d F hd hpower hF).iterate n
  simpa using hn

/-- Off the scalar horizon, the entire suspended state orbit is linearly independent. -/
theorem generalizedCliffordShiftOperator_orbit_linearIndependent
    (A : Module.End K M) (d : ℕ) (F : K) (m : M)
    (hd : d ≠ 0) (hpower : A ^ d = F • LinearMap.id)
    (hF : F ≠ 0) (hm : m ≠ 0) :
    LinearIndependent K (fun n : ℕ ↦
      ((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
        (periodicLevel 0 m)) := by
  have horbit := generalizedCliffordShiftOperator_orbit A m
  rw [show (fun n : ℕ ↦
      ((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
        (periodicLevel 0 m)) =
      (fun n : ℕ ↦ periodicLevel n (((A : M → M)^[n]) m)) by
    funext n
    exact horbit n]
  exact periodicLevel_linearIndependent
    (fun n : ℕ ↦ ((A : M → M)^[n]) m)
    (generalizedCliffordPowerRelation_orbit_ne_zero
      A d F m hd hpower hF hm)

/-- On the scalar horizon, the suspended root orbit vanishes at the factorization degree. -/
theorem generalizedCliffordShiftOperator_orbit_eq_zero
    (A : Module.End K M) (d : ℕ) (F : K) (m : M)
    (hpower : A ^ d = F • LinearMap.id) (hF : F = 0) :
    ((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[d])
        (periodicLevel 0 m) = 0 := by
  rw [generalizedCliffordShiftOperator_orbit]
  have hAm : ((A : M → M)^[d]) m = 0 := by
    rw [← Module.End.pow_apply, hpower, hF]
    simp
  rw [hAm]
  funext n
  simp [periodicLevel]

/-- The derivation of the symmetric observable algebra induced by the suspended symbol. -/
def generalizedCliffordShiftDerivation (A : Module.End K M) :
    Derivation K (SymmetricAlgebra K (ℕ → M)) (SymmetricAlgebra K (ℕ → M)) :=
  symmetricAlgebraDerivation (generalizedCliffordShiftOperator A)

/-- The complete differential jet of the grade-zero root observable. -/
def generalizedCliffordShiftJet (A : Module.End K M) (m : M) (n : ℕ) :
    SymmetricAlgebra K (ℕ → M) :=
  ((generalizedCliffordShiftDerivation A :
      SymmetricAlgebra K (ℕ → M) → SymmetricAlgebra K (ℕ → M))^[n])
    (SymmetricAlgebra.ι K (ℕ → M) (periodicLevel 0 m))

/-- Iterated observable differentiation is exactly the suspended state orbit. -/
theorem generalizedCliffordShiftJet_eq_observableOrbit
    (A : Module.End K M) (m : M) :
    ∀ n : ℕ,
      generalizedCliffordShiftJet A m n =
        SymmetricAlgebra.ι K (ℕ → M)
          (((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
            (periodicLevel 0 m)) := by
  intro n
  induction n with
  | zero => simp [generalizedCliffordShiftJet]
  | succ n ih =>
      rw [generalizedCliffordShiftJet, Function.iterate_succ_apply',
        ← generalizedCliffordShiftJet, ih,
        generalizedCliffordShiftDerivation,
        symmetricAlgebraDerivation_ι,
        Function.iterate_succ_apply']

/-- **General Clifford principal-symbol horizon theorem.**  A nonzero root observable has an
algebraically independent complete differential jet exactly off the scalar zero locus forced by
the generalized Clifford power relation. -/
theorem generalizedCliffordShiftJet_algebraicIndependent_iff
    (A : Module.End K M) (d : ℕ) (F : K) (m : M)
    (hd : d ≠ 0) (hpower : A ^ d = F • LinearMap.id) (hm : m ≠ 0) :
    AlgebraicIndependent K (generalizedCliffordShiftJet A m) ↔ F ≠ 0 := by
  have hjet : generalizedCliffordShiftJet A m = fun n : ℕ ↦
      SymmetricAlgebra.ι K (ℕ → M)
        (((generalizedCliffordShiftOperator A : (ℕ → M) → (ℕ → M))^[n])
          (periodicLevel 0 m)) := by
    funext n
    exact generalizedCliffordShiftJet_eq_observableOrbit A m n
  rw [hjet, symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent]
  constructor
  · intro hLI hF
    exact hLI.ne_zero d
      (generalizedCliffordShiftOperator_orbit_eq_zero A d F m hpower
        hF)
  · intro hF
    exact generalizedCliffordShiftOperator_orbit_linearIndependent
      A d F m hd hpower hF hm

variable {V : Type w} [AddCommGroup V] [Module K V]

/-- **Exact law-space zero-locus theorem.**  Any linear pencil satisfying a pointwise Roby
power relation has complete differential-dependence horizon exactly the zero locus of its scalar
form. -/
theorem generalizedCliffordShift_dependenceHorizon_eq_zeroLocus
    (symbol : V →ₗ[K] Module.End K M) (F : V → K)
    (d : ℕ) (hd : d ≠ 0) (m : M) (hm : m ≠ 0)
    (hpower : ∀ c : V, (symbol c) ^ d = F c • LinearMap.id) :
    {c : V | ¬ AlgebraicIndependent K (generalizedCliffordShiftJet (symbol c) m)} =
      {c : V | F c = 0} := by
  ext c
  change (¬ AlgebraicIndependent K (generalizedCliffordShiftJet (symbol c) m)) ↔
    F c = 0
  rw [generalizedCliffordShiftJet_algebraicIndependent_iff
    (symbol c) d (F c) m hd (hpower c) hm]
  exact not_ne_iff

end

end GaloisForLFunctions.HTGeometry
