import GaloisForLFunctions.HTGeometry.CommutativeDGroupObservable

/-!
# Changing the basis of the Lie algebra

An invertible constant matrix applied to the logarithmic coordinates of a commutative
`D`-group presentation gives another presentation with the same coordinates: the logarithmic
derivative stays a homomorphism, the new logarithmic coordinates are still differential rational
in the coordinates, and the first-order system is recovered through the inverse matrix, whose
entries are constants and therefore commute with the derivation.

Since the coordinates are unchanged, the differential closure — hence the rank — of the
logarithmic coordinate family is unchanged: the rank of the source boundary is intrinsic, not an
artefact of the chosen basis of the Lie algebra.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {G : Type*} [CommGroup G] {C K L : Type u} [Field C] [Field K] [Field L]
  [Algebra C K] [Algebra K L] [Algebra C L] [IsScalarTower C K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L] {n d : ℕ}

/-! ### Constants are killed by the derivation and lie in every intermediate field -/

omit [Differential K] [Differential L] [DifferentialAlgebra K L] in
theorem algebraMap_C_mem (B : IntermediateField K L) (c : C) :
    algebraMap C L c ∈ B := by
  rw [IsScalarTower.algebraMap_apply C K L]
  exact B.algebraMap_mem _

theorem deriv_finsetSum {ι : Type*} (s : Finset ι) (f : ι → L) :
    (∑ i ∈ s, f i)′ = ∑ i ∈ s, (f i)′ := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, Differential.deriv.map_zero]
  | insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Differential.deriv.map_add, ih]

theorem differentialJet_finsetSum {ι : Type*} (s : Finset ι) (f : ι → L) (m : ℕ) :
    differentialJet m (∑ i ∈ s, f i) = ∑ i ∈ s, differentialJet m (f i) := by
  induction m with
  | zero =>
      rw [differentialJet_zero]
      exact (Finset.sum_congr rfl fun i _ => (differentialJet_zero (f i)).symm)
  | succ k ih =>
      rw [differentialJet_succ, ih, deriv_finsetSum]
      exact Finset.sum_congr rfl fun i _ => (differentialJet_succ k (f i)).symm

theorem differentialJet_algebraMap_C_mul (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (c : C) (x : L) (m : ℕ) :
    differentialJet m (algebraMap C L c * x) = algebraMap C L c * differentialJet m x := by
  induction m with
  | zero => rw [differentialJet_zero, differentialJet_zero]
  | succ k ih =>
      rw [differentialJet_succ, differentialJet_succ, ih, Derivation.leibniz]
      have hzero : (algebraMap C L c)′ = 0 := by
        rw [IsScalarTower.algebraMap_apply C K L, deriv_algebraMap, hC, map_zero]
      rw [hzero, smul_zero, add_zero, smul_eq_mul]

/-! ### The transformed presentation -/

/-- An invertible constant matrix transforms a presentation into another presentation with the
same coordinates. -/
def DGroupPresentation.basisChange (P : DGroupPresentation G K L n d)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (M N : Fin d → Fin d → C) (hNM : ∀ k j, (∑ i, N k i * M i j) = if k = j then 1 else 0) :
    DGroupPresentation G K L n d where
  coords := P.coords
  ell g j := ∑ k, algebraMap C L (M j k) * P.ell g k
  ell_mul g h := by
    funext j
    show (∑ k, algebraMap C L (M j k) * P.ell (g * h) k)
      = (fun j => ∑ k, algebraMap C L (M j k) * P.ell g k) j
        + (fun j => ∑ k, algebraMap C L (M j k) * P.ell h k) j
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [P.ell_mul, Pi.add_apply, mul_add]
  ell_mem_coordAdjoin g j := by
    refine (differentialAdjoin K (Set.range (P.coords g))).sum_mem fun k _ => ?_
    exact (differentialAdjoin K (Set.range (P.coords g))).mul_mem
      (algebraMap_C_mem _ _) (P.ell_mem_coordAdjoin g k)
  deriv_coords_mem g i := by
    classical
    have hjet : ∀ (k : Fin d) (m : ℕ),
        differentialJet m (P.ell g k) ∈ IntermediateField.adjoin K
          (Set.range (P.coords g) ∪ differentialJetSet
            (Set.range fun j => ∑ k', algebraMap C L (M j k') * P.ell g k')) := by
      intro k m
      have hsum : (∑ j, algebraMap C L (N k j) *
            differentialJet m (∑ k', algebraMap C L (M j k') * P.ell g k'))
          = differentialJet m (P.ell g k) := by
        have hinner : ∀ j : Fin d,
            differentialJet m (∑ k', algebraMap C L (M j k') * P.ell g k')
              = ∑ k', algebraMap C L (M j k') * differentialJet m (P.ell g k') := by
          intro j
          rw [differentialJet_finsetSum]
          exact Finset.sum_congr rfl fun k' _ => differentialJet_algebraMap_C_mul hC _ _ m
        rw [Finset.sum_congr rfl fun j _ => by rw [hinner j]]
        have hpush : ∀ j : Fin d, algebraMap C L (N k j) *
              (∑ k', algebraMap C L (M j k') * differentialJet m (P.ell g k'))
            = ∑ k', algebraMap C L (N k j) *
              (algebraMap C L (M j k') * differentialJet m (P.ell g k')) := by
          intro j
          rw [Finset.mul_sum]
        have hswap : (∑ j, algebraMap C L (N k j) *
              ∑ k', algebraMap C L (M j k') * differentialJet m (P.ell g k'))
            = ∑ k', (∑ j, algebraMap C L (N k j) * algebraMap C L (M j k'))
              * differentialJet m (P.ell g k') := by
          rw [Finset.sum_congr rfl fun j _ => hpush j, Finset.sum_comm]
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [hswap]
        have hdelta : ∀ k' : Fin d,
            (∑ j, algebraMap C L (N k j) * algebraMap C L (M j k'))
              * differentialJet m (P.ell g k')
              = if k' = k then differentialJet m (P.ell g k') else 0 := by
          intro k'
          have hentry : (∑ j, algebraMap C L (N k j) * algebraMap C L (M j k'))
              = algebraMap C L (if k = k' then 1 else 0) := by
            rw [← hNM k k', map_sum]
            exact Finset.sum_congr rfl fun j _ => (map_mul (algebraMap C L) _ _).symm
          rw [hentry]
          by_cases hk : k = k'
          · rw [if_pos hk, map_one, one_mul, if_pos hk.symm]
          · rw [if_neg hk, map_zero, zero_mul, if_neg fun h => hk h.symm]
        rw [Finset.sum_congr rfl fun k' _ => hdelta k',
          Finset.sum_ite_eq' Finset.univ k (fun k' => differentialJet m (P.ell g k')),
          if_pos (Finset.mem_univ k)]
      rw [← hsum]
      refine (IntermediateField.adjoin K _).sum_mem fun j _ => ?_
      refine (IntermediateField.adjoin K _).mul_mem (algebraMap_C_mem _ _) ?_
      exact IntermediateField.subset_adjoin K _ (Or.inr
        ⟨∑ k', algebraMap C L (M j k') * P.ell g k', ⟨j, rfl⟩, m, rfl⟩)
    have h := P.deriv_coords_mem g i
    refine (IntermediateField.adjoin_le_iff (F := K)).2 ?_ h
    rintro x (hx | ⟨y, ⟨k, rfl⟩, m, rfl⟩)
    · exact IntermediateField.subset_adjoin K _ (Or.inl hx)
    · exact hjet k m

/-- **The rank of the source boundary is intrinsic.**  Changing the basis of the Lie algebra by an
invertible constant matrix does not change the differential closure of the logarithmic coordinate
family, because both closures are the closure of the coordinate family. -/
theorem differentialClosure_ellFamily_basisChange [CharZero L]
    (P : DGroupPresentation G K L n d) (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (M N : Fin d → Fin d → C)
    (hNM : ∀ k j, (∑ i, N k i * M i j) = if k = j then 1 else 0)
    {S : Type u} [Fintype S] (g : S → G) :
    differentialClosure K (Set.range ((P.basisChange hC M N hNM).ellFamily g))
      = differentialClosure K (Set.range (P.ellFamily g)) := by
  rw [← (P.basisChange hC M N hNM).differentialClosure_coordFamily_eq_ellFamily g,
    ← P.differentialClosure_coordFamily_eq_ellFamily g]
  rfl

end

end GaloisForLFunctions.HTGeometry
