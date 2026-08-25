import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum
import GaloisForLFunctions.HTGeometry.CoordinateCorankDirectedSup
import GaloisForLFunctions.HTGeometry.RelationLatticeCorank

/-!
# Holonomy, relation-lattice corank, and finite-rank integrability

For any orbit family, the first isomorphism theorem identifies its algebraic orbit closure with the
quotient of the free coefficient module by the relation lattice.  Consequently holonomicity
(finite orbit rank), finite relation-lattice corank, and containment in a finite-rank state space are
equivalent.  The rank identity is valid at arbitrary cardinality.

For a one-sided response sequence, finite orbit rank is further equivalent to a nonzero
constant-coefficient recurrence and to uniformly bounded Hankel rank.  The arithmetic prime-log
specialization records the opposite extreme: the relation lattice is zero, every finite slice has
finite corank, but the full quotient has infinite dimension.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Finset
open scoped Matrix

universe uK uP uV

section OrbitCorank

variable {K : Type uK} {P : Type uP} {V : Type uV}
  [Field K] [AddCommGroup V] [Module K V]

/-- Relation lattice of a family of difference-orbit vectors. -/
def orbitRelationLattice (v : P → V) : Submodule K (P →₀ K) :=
  LinearMap.ker (Finsupp.linearCombination K v)

/-- Algebraic closure of the orbit: its linear span over the coefficient field. -/
def orbitClosure (v : P → V) : Submodule K V :=
  Submodule.span K (Set.range v)

/-- Difference holonomicity: the orbit closes in finite rank over the coefficient field. -/
def OrbitHolonomic (v : P → V) : Prop :=
  FiniteDimensional K (orbitClosure (K := K) v)

/-- Existence of a finite-rank state space containing the whole orbit. -/
def IntegrableToFiniteRank (v : P → V) : Prop :=
  ∃ W : Submodule K V, FiniteDimensional K W ∧ ∀ p, v p ∈ W

theorem range_orbitLinearCombination (v : P → V) :
    LinearMap.range (Finsupp.linearCombination K v) = orbitClosure (K := K) v := by
  rw [orbitClosure]
  simpa using (Finsupp.range_linearCombination K (v := v))

/-- The dimension of the algebraic orbit closure equals the corank of its relation lattice. -/
theorem orbitClosure_rank_eq_relationLattice_corank (v : P → V) :
    Cardinal.lift.{uV}
        (Module.rank K ((P →₀ K) ⧸ orbitRelationLattice (K := K) v)) =
      Cardinal.lift.{max uP uK} (Module.rank K (orbitClosure (K := K) v)) := by
  rw [orbitRelationLattice]
  have h := (Finsupp.linearCombination K v).quotKerEquivRange.lift_rank_eq
  rw [range_orbitLinearCombination] at h
  exact h

theorem finiteDimensional_orbitRelationQuotient_iff_holonomic (v : P → V) :
    FiniteDimensional K ((P →₀ K) ⧸ orbitRelationLattice (K := K) v) ↔
      OrbitHolonomic (K := K) v := by
  rw [orbitRelationLattice, OrbitHolonomic]
  constructor
  · intro h
    letI := h
    have hrange : FiniteDimensional K
        (LinearMap.range (Finsupp.linearCombination K v)) :=
      Module.Finite.equiv (Finsupp.linearCombination K v).quotKerEquivRange
    rwa [range_orbitLinearCombination] at hrange
  · intro h
    letI := h
    have hrange : FiniteDimensional K
        (LinearMap.range (Finsupp.linearCombination K v)) := by
      rwa [range_orbitLinearCombination]
    letI := hrange
    exact Module.Finite.equiv (Finsupp.linearCombination K v).quotKerEquivRange.symm

theorem orbitHolonomic_iff_integrableToFiniteRank (v : P → V) :
    OrbitHolonomic (K := K) v ↔ IntegrableToFiniteRank (K := K) v := by
  constructor
  · intro h
    exact ⟨orbitClosure (K := K) v, h, fun p => Submodule.subset_span ⟨p, rfl⟩⟩
  · rintro ⟨W, hW, hv⟩
    letI := hW
    exact Submodule.finiteDimensional_of_le (Submodule.span_le.mpr fun x hx => by
      obtain ⟨p, rfl⟩ := hx
      exact hv p)

/-- **G3 holonomy/corank/integrability dichotomy.** -/
theorem orbit_holonomy_corank_integrability_dichotomy (v : P → V) :
    OrbitHolonomic (K := K) v ↔
      (FiniteDimensional K ((P →₀ K) ⧸ orbitRelationLattice (K := K) v) ∧
        IntegrableToFiniteRank (K := K) v) := by
  constructor
  · intro h
    exact ⟨(finiteDimensional_orbitRelationQuotient_iff_holonomic v).mpr h,
      (orbitHolonomic_iff_integrableToFiniteRank v).mp h⟩
  · rintro ⟨hcorank, -⟩
    exact (finiteDimensional_orbitRelationQuotient_iff_holonomic v).mp hcorank

end OrbitCorank

/-- Forward shift orbit of a sequence. -/
def sequenceShift (m : ℕ → ℂ) (j : ℕ) : ℕ → ℂ :=
  fun n => m (n + j)

def sequenceShiftSpan (m : ℕ → ℂ) : Submodule ℂ (ℕ → ℂ) :=
  Submodule.span ℂ (Set.range (sequenceShift m))

def sequenceOrbitMap (m : ℕ → ℂ) : (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ → ℂ) :=
  Finsupp.linearCombination ℂ (sequenceShift m)

def sequenceRelationLattice (m : ℕ → ℂ) : Submodule ℂ (ℕ →₀ ℂ) :=
  LinearMap.ker (sequenceOrbitMap m)

theorem range_sequenceOrbitMap (m : ℕ → ℂ) :
    LinearMap.range (sequenceOrbitMap m) = sequenceShiftSpan m := by
  rw [sequenceOrbitMap, sequenceShiftSpan]
  simpa using (Finsupp.range_linearCombination ℂ (v := sequenceShift m))

theorem sequenceShift_mem_finite_span_of_recurrence
    {m : ℕ → ℂ} {p : Polynomial ℂ} (hp : p ≠ 0)
    (hrec : ∀ n, ∑ k ∈ Finset.range (p.natDegree + 1),
      p.coeff k * m (n + k) = 0) (j : ℕ) :
    sequenceShift m j ∈
      Submodule.span ℂ (Set.range fun k : Fin p.natDegree => sequenceShift m k) := by
  set r := p.natDegree with hr
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    by_cases hj : j < r
    · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    · have hjr : j - r + r = j := by omega
      have hlead : p.coeff r ≠ 0 := by
        rw [hr]
        exact Polynomial.leadingCoeff_ne_zero.mpr hp
      have hshift : p.coeff r • sequenceShift m j =
          ∑ k ∈ Finset.range r,
            (-(p.coeff k)) • sequenceShift m (j - r + k) := by
        funext n
        have h := hrec (n + (j - r))
        rw [Finset.sum_range_succ] at h
        simp only [Pi.smul_apply, smul_eq_mul, sequenceShift, Finset.sum_apply]
        have hcong : ∑ k ∈ Finset.range r,
            (-(p.coeff k)) * m (n + (j - r + k)) =
            -∑ k ∈ Finset.range r, p.coeff k * m (n + (j - r) + k) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun k _ => by
            rw [show n + (j - r + k) = n + (j - r) + k by omega]
            ring
        rw [hcong]
        have hlast : n + (j - r) + r = n + j := by omega
        rw [← hlast]
        linear_combination h
      have hmem : p.coeff r • sequenceShift m j ∈
          Submodule.span ℂ (Set.range fun k : Fin r => sequenceShift m k) := by
        rw [hshift]
        refine Submodule.sum_mem _ fun k hk => ?_
        refine Submodule.smul_mem _ _ (ih (j - r + k) ?_)
        have hkr : k < r := Finset.mem_range.mp hk
        omega
      have hinv : sequenceShift m j =
          (p.coeff r)⁻¹ • (p.coeff r • sequenceShift m j) := by
        rw [smul_smul, inv_mul_cancel₀ hlead, one_smul]
      rw [hinv]
      exact Submodule.smul_mem _ _ hmem

theorem finiteDimensional_sequenceShiftSpan_of_seqConstantRecurrence
    {m : ℕ → ℂ} (h : SeqConstantRecurrence m) :
    FiniteDimensional ℂ (sequenceShiftSpan m) := by
  obtain ⟨p, hp, hrec⟩ := h
  let W : Submodule ℂ (ℕ → ℂ) :=
    Submodule.span ℂ (Set.range fun k : Fin p.natDegree => sequenceShift m k)
  have hle : sequenceShiftSpan m ≤ W := by
    rw [sequenceShiftSpan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact sequenceShift_mem_finite_span_of_recurrence hp hrec j
  haveI : FiniteDimensional ℂ W :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le hle

def sequenceWindowEval (m : ℕ → ℂ) (N : ℕ) :
    sequenceShiftSpan m →ₗ[ℂ] (Fin (N + 1) → ℂ) where
  toFun f := fun i => f.1 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bddHankelRank_of_finiteDimensional_sequenceShiftSpan
    {m : ℕ → ℂ} [FiniteDimensional ℂ (sequenceShiftSpan m)] :
    BddHankelRank m := by
  refine ⟨Module.finrank ℂ (sequenceShiftSpan m), fun N => ?_⟩
  rw [Matrix.rank_eq_finrank_span_cols]
  have hsub : Submodule.span ℂ (Set.range (seqHankel m N)ᵀ) ≤
      LinearMap.range (sequenceWindowEval m N) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨⟨sequenceShift m j,
      Submodule.subset_span ⟨(j : ℕ), rfl⟩⟩, ?_⟩
    ext i
    rfl
  exact (Submodule.finrank_mono hsub).trans
    (LinearMap.finrank_range_le (sequenceWindowEval m N))

theorem seqConstantRecurrence_iff_finiteDimensional_sequenceShiftSpan
    (m : ℕ → ℂ) :
    SeqConstantRecurrence m ↔ FiniteDimensional ℂ (sequenceShiftSpan m) := by
  constructor
  · exact finiteDimensional_sequenceShiftSpan_of_seqConstantRecurrence
  · intro h
    letI := h
    exact seqConstantRecurrence_of_bddHankelRank
      bddHankelRank_of_finiteDimensional_sequenceShiftSpan

theorem finiteDimensional_relationQuotient_iff_shiftSpan
    (m : ℕ → ℂ) :
    FiniteDimensional ℂ ((ℕ →₀ ℂ) ⧸ sequenceRelationLattice m) ↔
      FiniteDimensional ℂ (sequenceShiftSpan m) := by
  rw [sequenceRelationLattice]
  constructor
  · intro h
    letI := h
    have hrange : FiniteDimensional ℂ (LinearMap.range (sequenceOrbitMap m)) :=
      Module.Finite.equiv (sequenceOrbitMap m).quotKerEquivRange
    rwa [range_sequenceOrbitMap] at hrange
  · intro h
    letI := h
    have hrange : FiniteDimensional ℂ (LinearMap.range (sequenceOrbitMap m)) := by
      rwa [range_sequenceOrbitMap]
    letI := hrange
    exact Module.Finite.equiv (sequenceOrbitMap m).quotKerEquivRange.symm

theorem sequence_holonomy_corank_dichotomy (m : ℕ → ℂ) :
    SeqConstantRecurrence m ↔
      FiniteDimensional ℂ ((ℕ →₀ ℂ) ⧸ sequenceRelationLattice m) := by
  rw [seqConstantRecurrence_iff_finiteDimensional_sequenceShiftSpan,
    finiteDimensional_relationQuotient_iff_shiftSpan]

theorem sequence_holonomy_corank_integrability_dichotomy (m : ℕ → ℂ) :
    SeqConstantRecurrence m ↔
      (FiniteDimensional ℂ ((ℕ →₀ ℂ) ⧸ sequenceRelationLattice m) ∧
        BddHankelRank m) := by
  constructor
  · intro h
    exact ⟨(sequence_holonomy_corank_dichotomy m).mp h,
      (seqConstantRecurrence_iff_bddHankelRank m).mp h⟩
  · rintro ⟨hcorank, -⟩
    exact (sequence_holonomy_corank_dichotomy m).mpr hcorank

theorem sequenceOrbitDimension_eq_relationCorank (m : ℕ → ℂ) :
    Cardinal.lift.{0} (Module.rank ℂ ((ℕ →₀ ℂ) ⧸ sequenceRelationLattice m)) =
      Cardinal.lift.{0} (Module.rank ℂ (sequenceShiftSpan m)) := by
  rw [sequenceRelationLattice]
  have h := (sequenceOrbitMap m).quotKerEquivRange.lift_rank_eq
  rw [range_sequenceOrbitMap] at h
  exact h

theorem arithmetic_zero_relationLattice_infinite_corank :
    ¬ FiniteDimensional ℚ ((ℕ →₀ ℚ) ⧸ (⊥ : Submodule ℚ (ℕ →₀ ℚ))) :=
  not_finiteDimensional_quotient_bot

/-- Arithmetic prime logarithms have `Λ = 0`, finite corank on every finite slice, and infinite
corank in the full limit. -/
theorem arithmetic_primeLog_zeroLattice_finiteSlices_infiniteCorank :
    relationSpan
        (frequencyRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ))) = ⊥ ∧
      (∀ T : Finset Nat.Primes,
        coordCorank
          (relationSpan
            (frequencyRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ)))) T = T.card) ∧
      ¬ FiniteDimensional ℚ ((Nat.Primes →₀ ℚ) ⧸
        relationSpan
          (frequencyRelationLattice (fun p : Nat.Primes => Real.log (p : ℕ)))) := by
  exact ⟨relationSpan_primeLog_eq_bot, coordCorank_primeLog,
    not_finiteDimensional_quotient_primeLog⟩

end

end GaloisForLFunctions.HTGeometry
