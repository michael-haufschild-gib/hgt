import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeLengthAdditivity
import GaloisForLFunctions.HTGeometry.DifferentialVariationalLatticeInterleaving
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveStandardApartment

/-!
# Integral Cartan index of completed pseudodifferential lattices

The sum of the canonical dominant relative-position coordinates is recovered as the signed
difference of two finite quotient lengths from any common lower lattice.  Interleaving supplies a
common refinement of any two choices, so that expression is independent of the lower lattice.
Length additivity then proves the exact pair-groupoid cocycle law for arbitrary completed lattices.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {r : ℕ}

/-- Integral Cartan index: sum of canonical dominant relative-position coordinates. -/
def completedPseudoDiffOpCartanIndex
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) : ℤ :=
  ∑ i, completedPseudoDiffOpDominantRelativePosition L M i

/-- Natural quotient length is invariant under simultaneous completed-skew transport. -/
theorem completedPseudoDiffOpLatticeQuotientNatLength_mapLinear
    (e : (Fin r → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
      (Fin r → CompletedPseudoDiffOp K))
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpLatticeQuotientNatLength
        (mapCompletedPseudoDiffOpLatticeLinear e L)
        (mapCompletedPseudoDiffOpLatticeLinear e M) =
      completedPseudoDiffOpLatticeQuotientNatLength L M := by
  unfold completedPseudoDiffOpLatticeQuotientNatLength
  rw [completedPseudoDiffOpDominantRelativePosition_mapLinear]

/-- Natural quotient length respects equality of both lattice endpoints. -/
theorem completedPseudoDiffOpLatticeQuotientNatLength_congr
    (L M L' M' : CompletedPseudoDiffOpLattice K (Fin r))
    (hL : L = L') (hM : M = M') :
    completedPseudoDiffOpLatticeQuotientNatLength L M =
      completedPseudoDiffOpLatticeQuotientNatLength L' M' := by
  subst L'
  subst M'
  rfl

/-- Quotient length from a nonnegative constant coweight to the standard lattice. -/
theorem completedPseudoDiffOpLatticeQuotientNatLength_constant_zero (c : ℕ) :
    completedPseudoDiffOpLatticeQuotientNatLength
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
          (fun _ : Fin r => (c : ℤ)))
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
          (fun _ : Fin r => 0)) =
      ∑ _ : Fin r, c := by
  let Q := standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
    (fun _ : Fin r => (c : ℤ))
  let Z := standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
    (fun _ : Fin r => 0)
  have hQZ : Q.carrier ≤ Z.carrier :=
    (standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
      (fun _ : Fin r => (c : ℤ)) (fun _ : Fin r => 0)).2 fun _ => by omega
  have hlen := completedPseudoDiffOpLatticeQuotient_length_eq_natLength Q Z hQZ
  have hinterval := standardCompletedPseudoDiffOpCoweightIntervalQuotient_length
    (K := K) (n := fun _ : Fin r => 0) (fun _ => c)
  have hcoweight : (fun i : Fin r => (0 : ℤ) + (c : ℤ)) =
      fun _ : Fin r => (c : ℤ) := by
    funext i
    simp
  rw [hcoweight] at hinterval
  have hinside :
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => (c : ℤ))).carrier ≤
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => 0)).carrier := hQZ
  have hlen' : Module.length (CompletedPseudoDiffOpInteger (K := K))
      (Z.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf Q Z hQZ) =
      ∑ _ : Fin r, c := by
    exact (completedPseudoDiffOpLatticeQuotient_length_congr
      Q Z
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => (c : ℤ)))
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => 0))
      hQZ hinside rfl rfl).trans hinterval
  exact ENat.coe_inj.mp (hlen.symm.trans hlen')

/-- Quotient length from a dominating constant coweight to an arbitrary coweight. -/
theorem completedPseudoDiffOpLatticeQuotientNatLength_coweight_constant
    (m : Fin r → ℤ) (c : ℕ) (hmc : ∀ i, m i ≤ c) :
    completedPseudoDiffOpLatticeQuotientNatLength
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
          (fun _ : Fin r => (c : ℤ)))
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      ∑ i, Int.toNat ((c : ℤ) - m i) := by
  let Q := standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
    (fun _ : Fin r => (c : ℤ))
  let M := standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m
  let d : Fin r → ℕ := fun i => Int.toNat ((c : ℤ) - m i)
  have hd : (fun i : Fin r => m i + (d i : ℤ)) = fun _ => (c : ℤ) := by
    funext i
    dsimp [d]
    have hi := hmc i
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hi)]
    omega
  have hQM : Q.carrier ≤ M.carrier :=
    (standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
      (fun _ : Fin r => (c : ℤ)) m).2 hmc
  have hlen := completedPseudoDiffOpLatticeQuotient_length_eq_natLength Q M hQM
  have hinterval := standardCompletedPseudoDiffOpCoweightIntervalQuotient_length
    (K := K) (n := m) d
  rw [hd] at hinterval
  have hinside :
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => (c : ℤ))).carrier ≤
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier := hQM
  have hlen' : Module.length (CompletedPseudoDiffOpInteger (K := K))
      (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf Q M hQM) =
      ∑ i, d i := by
    exact (completedPseudoDiffOpLatticeQuotient_length_congr
      Q M
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => (c : ℤ)))
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m)
      hQM hinside rfl rfl).trans hinterval
  exact ENat.coe_inj.mp (hlen.symm.trans hlen')

/-- A constant common lower lattice computes the coordinate sum in the standard apartment. -/
theorem completedPseudoDiffOpConstantCommonLower_difference_eq_sum
    (m : Fin r → ℤ) (c : ℕ) (hmc : ∀ i, m i ≤ c) :
    (completedPseudoDiffOpLatticeQuotientNatLength
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
          (fun _ : Fin r => (c : ℤ)))
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
          (fun _ : Fin r => 0)) : ℤ) -
      completedPseudoDiffOpLatticeQuotientNatLength
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
          (fun _ : Fin r => (c : ℤ)))
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      ∑ i, m i := by
  rw [completedPseudoDiffOpLatticeQuotientNatLength_constant_zero,
    completedPseudoDiffOpLatticeQuotientNatLength_coweight_constant m c hmc]
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hmc i
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hi)]
  omega

/-- Every pair has a common lower lattice realizing its Cartan index as a length difference. -/
theorem exists_completedPseudoDiffOpLattice_commonLower_cartanIndex_formula
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    ∃ Q : CompletedPseudoDiffOpLattice K (Fin r),
      Q.carrier ≤ L.carrier ∧ Q.carrier ≤ M.carrier ∧
        completedPseudoDiffOpCartanIndex L M =
          (completedPseudoDiffOpLatticeQuotientNatLength Q L : ℤ) -
            completedPseudoDiffOpLatticeQuotientNatLength Q M := by
  let d := completedPseudoDiffOpDominantCartanData L M
  obtain ⟨a, ha⟩ :=
    exists_standardCompletedPseudoDiffOpLatticeAtConstantCoweight_le
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) d.coweight)
  let c : ℕ := Int.toNat (max a 0)
  have hc_cast : (c : ℤ) = max a 0 := by
    dsimp [c]
    rw [Int.toNat_of_nonneg (le_max_right a 0)]
  have hc0 : (0 : ℤ) ≤ c := by omega
  have hmc : ∀ i, d.coweight i ≤ (c : ℤ) := by
    have hac : a ≤ (c : ℤ) := by rw [hc_cast]; exact le_max_left _ _
    have hma : ∀ i, d.coweight i ≤ a :=
      (standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
        (fun _ : Fin r => a) d.coweight).1 ha
    intro i
    exact (hma i).trans hac
  let Qstd := standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
    (fun _ : Fin r => (c : ℤ))
  let Q := mapCompletedPseudoDiffOpLatticeLinear d.frame.symm Qstd
  have hmapQ : mapCompletedPseudoDiffOpLatticeLinear d.frame Q = Qstd := by
    change mapCompletedPseudoDiffOpLatticeLinear d.frame
      (mapCompletedPseudoDiffOpLatticeLinear d.frame.symm Qstd) = Qstd
    rw [mapCompletedPseudoDiffOpLatticeLinear_trans]
    simpa using mapCompletedPseudoDiffOpLatticeLinear_refl Qstd
  have hQzero : Qstd.carrier ≤
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)).carrier := by
    rw [← standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
    exact (standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
      (fun _ : Fin r => (c : ℤ)) (fun _ : Fin r => 0)).2 fun _ => hc0
  have hQm : Qstd.carrier ≤
      (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) d.coweight).carrier :=
    (standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
      (fun _ : Fin r => (c : ℤ)) d.coweight).2 hmc
  have hQL : Q.carrier ≤ L.carrier :=
    (mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame Q L).1 (by
      rw [hmapQ, d.map_left]
      exact hQzero)
  have hQM : Q.carrier ≤ M.carrier :=
    (mapCompletedPseudoDiffOpLatticeLinear_carrier_le_iff d.frame Q M).1 (by
      rw [hmapQ, d.map_right]
      exact hQm)
  have hlenL : completedPseudoDiffOpLatticeQuotientNatLength Q L =
      completedPseudoDiffOpLatticeQuotientNatLength Qstd
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r)) := by
    rw [← completedPseudoDiffOpLatticeQuotientNatLength_mapLinear d.frame Q L]
    exact completedPseudoDiffOpLatticeQuotientNatLength_congr _ _ _ _ hmapQ d.map_left
  have hlenM : completedPseudoDiffOpLatticeQuotientNatLength Q M =
      completedPseudoDiffOpLatticeQuotientNatLength Qstd
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) d.coweight) := by
    rw [← completedPseudoDiffOpLatticeQuotientNatLength_mapLinear d.frame Q M]
    exact completedPseudoDiffOpLatticeQuotientNatLength_congr _ _ _ _ hmapQ d.map_right
  refine ⟨Q, hQL, hQM, ?_⟩
  change (∑ i, d.coweight i) = _
  rw [hlenL, hlenM, ← standardCompletedPseudoDiffOpLatticeAtCoweight_zero]
  exact (completedPseudoDiffOpConstantCommonLower_difference_eq_sum d.coweight c hmc).symm

/-- Signed common-lower quotient differences do not depend on the common lower lattice. -/
theorem completedPseudoDiffOpCommonLower_difference_independent
    (L M Q Q' : CompletedPseudoDiffOpLattice K (Fin r))
    (hQL : Q.carrier ≤ L.carrier) (hQM : Q.carrier ≤ M.carrier)
    (hQ'L : Q'.carrier ≤ L.carrier) (hQ'M : Q'.carrier ≤ M.carrier) :
    (completedPseudoDiffOpLatticeQuotientNatLength Q L : ℤ) -
        completedPseudoDiffOpLatticeQuotientNatLength Q M =
      (completedPseudoDiffOpLatticeQuotientNatLength Q' L : ℤ) -
        completedPseudoDiffOpLatticeQuotientNatLength Q' M := by
  obtain ⟨n, hn⟩ := exists_completedPseudoDiffOpLattice_interleavedAt Q Q'
  let R := leftScaleCompletedPseudoDiffOpLattice
    (completedPseudoDiffOpUniformizerUnit (K := K) ^ (n : ℤ)) Q
  have hRQ : R.carrier ≤ Q.carrier :=
    leftScale_uniformizer_zpow_carrier_le_self Q (Int.natCast_nonneg n)
  have hRQ' : R.carrier ≤ Q'.carrier := hn.1
  have hRQL := completedPseudoDiffOpLatticeQuotientNatLength_add R Q L hRQ hQL
  have hRQM := completedPseudoDiffOpLatticeQuotientNatLength_add R Q M hRQ hQM
  have hRQ'L := completedPseudoDiffOpLatticeQuotientNatLength_add R Q' L hRQ' hQ'L
  have hRQ'M := completedPseudoDiffOpLatticeQuotientNatLength_add R Q' M hRQ' hQ'M
  omega

/-- Every common lower lattice computes the exact Cartan index. -/
theorem completedPseudoDiffOpCartanIndex_eq_commonLower_difference
    (L M Q : CompletedPseudoDiffOpLattice K (Fin r))
    (hQL : Q.carrier ≤ L.carrier) (hQM : Q.carrier ≤ M.carrier) :
    completedPseudoDiffOpCartanIndex L M =
      (completedPseudoDiffOpLatticeQuotientNatLength Q L : ℤ) -
        completedPseudoDiffOpLatticeQuotientNatLength Q M := by
  obtain ⟨Q', hQ'L, hQ'M, hindex⟩ :=
    exists_completedPseudoDiffOpLattice_commonLower_cartanIndex_formula L M
  exact hindex.trans
    (completedPseudoDiffOpCommonLower_difference_independent L M Q' Q hQ'L hQ'M hQL hQM)

/-- Cartan index is an exact additive cocycle on arbitrary completed lattices. -/
theorem completedPseudoDiffOpCartanIndex_add
    (L M N : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpCartanIndex L N =
      completedPseudoDiffOpCartanIndex L M + completedPseudoDiffOpCartanIndex M N := by
  obtain ⟨Q, hQL, hQM, _⟩ :=
    exists_completedPseudoDiffOpLattice_commonLower_cartanIndex_formula L M
  obtain ⟨R, hRQ, hRN, _⟩ :=
    exists_completedPseudoDiffOpLattice_commonLower_cartanIndex_formula Q N
  have hRL : R.carrier ≤ L.carrier := hRQ.trans hQL
  have hRM : R.carrier ≤ M.carrier := hRQ.trans hQM
  rw [completedPseudoDiffOpCartanIndex_eq_commonLower_difference L N R hRL hRN,
    completedPseudoDiffOpCartanIndex_eq_commonLower_difference L M R hRL hRM,
    completedPseudoDiffOpCartanIndex_eq_commonLower_difference M N R hRM hRN]
  omega

end

end GaloisForLFunctions.HTGeometry.DiffOp
