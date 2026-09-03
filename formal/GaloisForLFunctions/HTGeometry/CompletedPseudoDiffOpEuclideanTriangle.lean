import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpEuclideanSeparation
import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpCartanIndex
import GaloisForLFunctions.HTGeometry.TopSumMajorization

/-!
# Euclidean triangle law for completed pseudodifferential lattice vertices

This leaf constructs the literal intersection of any two full completed valuation lattices.
Finite quotient-length additivity and an injective intersection-layer map give the asymmetric
length triangle.  Cartan-frame coordinates identify that length with a hinge sum.  The resulting
hinge inequalities imply every dominant Cartan top-sum inequality, and determinant-balance
centering then yields the exact Euclidean triangle inequality on projective lattice vertices.

No abstract metric-space or affine-building hypothesis is used.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type*} [Field K] [Differential K] {r : ℕ}

theorem mem_standardCompletedPseudoDiffOpLatticeAtCoweight_max_zero_iff
    (m : Fin r → ℤ) (x : Fin r → CompletedPseudoDiffOp K) :
    x ∈ (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun i => max 0 (m i))).carrier ↔
      x ∈ (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ => 0)).carrier ∧
      x ∈ (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier := by
  rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff,
    mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff,
    mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff]
  constructor
  · intro h
    constructor <;> intro i
    · have hi := h i
      rw [completedPseudoDiffOpUniformizerCoweight,
        mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
        completedPseudoDiffOpAddValue_mul,
        completedPseudoDiffOpAddValue_unit_eq_coe,
        completedPseudoDiffOpUnitAddValue_inv,
        completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hi ⊢
      exact hi.trans (add_le_add le_rfl (WithTop.coe_le_coe.mpr (by omega)))
    · have hi := h i
      rw [completedPseudoDiffOpUniformizerCoweight,
        mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
        completedPseudoDiffOpAddValue_mul,
        completedPseudoDiffOpAddValue_unit_eq_coe,
        completedPseudoDiffOpUnitAddValue_inv,
        completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hi ⊢
      exact hi.trans (add_le_add le_rfl (WithTop.coe_le_coe.mpr (by omega)))
  · rintro ⟨h0, hm⟩ i
    have h0i := h0 i
    have hmi := hm i
    rw [completedPseudoDiffOpUniformizerCoweight,
      mem_completedPseudoDiffOpInteger_iff_addValue_nonneg,
      completedPseudoDiffOpAddValue_mul,
      completedPseudoDiffOpAddValue_unit_eq_coe,
      completedPseudoDiffOpUnitAddValue_inv,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at h0i hmi ⊢
    rcases le_total 0 (m i) with hpos | hneg
    · rw [max_eq_right hpos]
      exact hmi
    · rw [max_eq_left hneg]
      exact h0i

def completedPseudoDiffOpLatticeInf
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    CompletedPseudoDiffOpLattice K (Fin r) :=
  let d := completedPseudoDiffOpDominantCartanData L M
  mapCompletedPseudoDiffOpLatticeLinear d.frame.symm
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
      (fun i => max 0 (d.coweight i)))

theorem map_completedPseudoDiffOpLatticeInf
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    mapCompletedPseudoDiffOpLatticeLinear
        (completedPseudoDiffOpDominantCartanData L M).frame
        (completedPseudoDiffOpLatticeInf L M) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun i => max 0 ((completedPseudoDiffOpDominantCartanData L M).coweight i)) := by
  rw [completedPseudoDiffOpLatticeInf,
    mapCompletedPseudoDiffOpLatticeLinear_trans]
  simpa using mapCompletedPseudoDiffOpLatticeLinear_refl
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
      (fun i => max 0 ((completedPseudoDiffOpDominantCartanData L M).coweight i)))

theorem completedPseudoDiffOpLatticeInf_carrier
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    (completedPseudoDiffOpLatticeInf L M).carrier = L.carrier ⊓ M.carrier := by
  let d := completedPseudoDiffOpDominantCartanData L M
  ext x
  rw [Submodule.mem_inf]
  have hmem (A : CompletedPseudoDiffOpLattice K (Fin r)) :
      x ∈ A.carrier ↔
        d.frame x ∈ (mapCompletedPseudoDiffOpLatticeLinear d.frame A).carrier := by
    constructor
    · intro hx
      exact (mem_mapCompletedPseudoDiffOpLatticeLinear_iff d.frame A (d.frame x)).2
        ⟨x, hx, rfl⟩
    · intro hx
      obtain ⟨y, hy, heq⟩ :=
        (mem_mapCompletedPseudoDiffOpLatticeLinear_iff d.frame A (d.frame x)).1 hx
      have hyx : y = x := d.frame.injective heq
      simpa [hyx] using hy
  rw [hmem (completedPseudoDiffOpLatticeInf L M), hmem L, hmem M,
    map_completedPseudoDiffOpLatticeInf, d.map_left, d.map_right,
    mem_standardCompletedPseudoDiffOpLatticeAtCoweight_max_zero_iff,
    standardCompletedPseudoDiffOpLatticeAtCoweight_zero]

theorem completedPseudoDiffOpLatticeInf_le_left
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    (completedPseudoDiffOpLatticeInf L M).carrier ≤ L.carrier := by
  rw [completedPseudoDiffOpLatticeInf_carrier]
  exact inf_le_left

theorem completedPseudoDiffOpLatticeInf_le_right
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    (completedPseudoDiffOpLatticeInf L M).carrier ≤ M.carrier := by
  rw [completedPseudoDiffOpLatticeInf_carrier]
  exact inf_le_right

def submoduleInfLayerInclusion
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (L M N : Submodule R V) :
    ((↑(L ⊓ M)) ⧸ nestedSubmoduleInside ((L ⊓ M) ⊓ N) (L ⊓ M)) →ₗ[R]
      ((↑M) ⧸ nestedSubmoduleInside (M ⊓ N) M) :=
  Submodule.mapQ
    (nestedSubmoduleInside ((L ⊓ M) ⊓ N) (L ⊓ M))
    (nestedSubmoduleInside (M ⊓ N) M)
    { toFun := fun x ↦ ⟨x.1, x.2.2⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (by
      intro x hx
      exact ⟨x.2.2, hx.2⟩)

theorem submoduleInfLayerInclusion_injective
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (L M N : Submodule R V) :
    Function.Injective (submoduleInfLayerInclusion L M N) := by
  intro q q'
  refine Submodule.Quotient.induction_on
    (nestedSubmoduleInside ((L ⊓ M) ⊓ N) (L ⊓ M)) q ?_
  intro x
  refine Submodule.Quotient.induction_on
    (nestedSubmoduleInside ((L ⊓ M) ⊓ N) (L ⊓ M)) q' ?_
  intro y hxy
  rw [Submodule.Quotient.eq]
  change ((x : V) - (y : V) ∈ L ⊓ M) ∧ ((x : V) - (y : V) ∈ N)
  constructor
  · exact Submodule.sub_mem (L ⊓ M) x.2 y.2
  · change Submodule.Quotient.mk
      (p := nestedSubmoduleInside (M ⊓ N) M)
        ⟨(x : V), x.2.2⟩ =
      Submodule.Quotient.mk
      (p := nestedSubmoduleInside (M ⊓ N) M)
        ⟨(y : V), y.2.2⟩ at hxy
    have hdiff := (Submodule.Quotient.eq
      (nestedSubmoduleInside (M ⊓ N) M)).1 hxy
    exact hdiff.2

theorem submoduleInfLayer_length_le
    {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (L M N : Submodule R V) :
    Module.length R
        ((↑(L ⊓ M)) ⧸ nestedSubmoduleInside ((L ⊓ M) ⊓ N) (L ⊓ M)) ≤
      Module.length R ((↑M) ⧸ nestedSubmoduleInside (M ⊓ N) M) :=
  Module.length_le_of_injective (submoduleInfLayerInclusion L M N)
    (submoduleInfLayerInclusion_injective L M N)

def completedPseudoDiffOpLatticeAsymmetricDistanceNat
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) : ℕ :=
  completedPseudoDiffOpLatticeQuotientNatLength
    (completedPseudoDiffOpLatticeInf L M) L

theorem completedPseudoDiffOpLatticeAsymmetricDistanceNat_eq_hinge
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpLatticeAsymmetricDistanceNat L M =
      ∑ i, Int.toNat (max 0
        (completedPseudoDiffOpDominantRelativePosition L M i)) := by
  let d := completedPseudoDiffOpDominantCartanData L M
  let q : Fin r → ℤ := fun i => max 0 (d.coweight i)
  have hq : Antitone q := by
    intro i j hij
    exact max_le_max le_rfl (d.dominant hij)
  unfold completedPseudoDiffOpLatticeAsymmetricDistanceNat
  unfold completedPseudoDiffOpLatticeQuotientNatLength
  rw [← completedPseudoDiffOpDominantRelativePosition_mapLinear d.frame]
  rw [d.map_left, map_completedPseudoDiffOpLatticeInf]
  rw [completedPseudoDiffOpDominantRelativePosition_standard_coweight q hq]
  rfl

def leftUniformizerShiftCompletedPseudoDiffOpLattice
    (t : ℤ) (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    CompletedPseudoDiffOpLattice K (Fin r) :=
  leftScaleCompletedPseudoDiffOpLattice
    (completedPseudoDiffOpUniformizerUnit (K := K) ^ t) L

theorem completedPseudoDiffOpDominantRelativePosition_leftUniformizerShift
    (t : ℤ) (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpDominantRelativePosition
        (leftUniformizerShiftCompletedPseudoDiffOpLattice t L) M =
      fun i => completedPseudoDiffOpDominantRelativePosition L M i - t := by
  rw [leftUniformizerShiftCompletedPseudoDiffOpLattice,
    completedPseudoDiffOpDominantRelativePosition_first_leftScale,
    completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  rfl

theorem completedPseudoDiffOpDominantRelativePosition_twoUniformizerShifts
    (s u : ℤ) (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpDominantRelativePosition
        (leftUniformizerShiftCompletedPseudoDiffOpLattice (s + u) L)
        (leftUniformizerShiftCompletedPseudoDiffOpLattice u M) =
      fun i => completedPseudoDiffOpDominantRelativePosition L M i - s := by
  unfold leftUniformizerShiftCompletedPseudoDiffOpLattice
  rw [completedPseudoDiffOpDominantRelativePosition_first_leftScale,
    completedPseudoDiffOpDominantRelativePosition_second_leftScale]
  simp only [completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  funext i
  simp [Pi.add_apply, Pi.sub_apply]

theorem completedPseudoDiffOpLatticeAsymmetricDistanceNat_leftUniformizerShift_eq_hinge
    (t : ℤ) (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpLatticeAsymmetricDistanceNat
        (leftUniformizerShiftCompletedPseudoDiffOpLattice t L) M =
      ∑ i, Int.toNat (max 0
        (completedPseudoDiffOpDominantRelativePosition L M i - t)) := by
  rw [completedPseudoDiffOpLatticeAsymmetricDistanceNat_eq_hinge,
    completedPseudoDiffOpDominantRelativePosition_leftUniformizerShift]

theorem completedPseudoDiffOpLatticeAsymmetricDistanceNat_twoUniformizerShifts_eq_hinge
    (s u : ℤ) (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpLatticeAsymmetricDistanceNat
        (leftUniformizerShiftCompletedPseudoDiffOpLattice (s + u) L)
        (leftUniformizerShiftCompletedPseudoDiffOpLattice u M) =
      ∑ i, Int.toNat (max 0
        (completedPseudoDiffOpDominantRelativePosition L M i - s)) := by
  rw [completedPseudoDiffOpLatticeAsymmetricDistanceNat_eq_hinge,
    completedPseudoDiffOpDominantRelativePosition_twoUniformizerShifts]

theorem completedPseudoDiffOpLatticeAsymmetricDistanceNat_triangle
    (L M N : CompletedPseudoDiffOpLattice K (Fin r)) :
    completedPseudoDiffOpLatticeAsymmetricDistanceNat L N ≤
      completedPseudoDiffOpLatticeAsymmetricDistanceNat L M +
        completedPseudoDiffOpLatticeAsymmetricDistanceNat M N := by
  let B := completedPseudoDiffOpLatticeInf L M
  let A := completedPseudoDiffOpLatticeInf L N
  let C := completedPseudoDiffOpLatticeInf M N
  let Q := completedPseudoDiffOpLatticeInf B N
  have hBL : B.carrier ≤ L.carrier :=
    completedPseudoDiffOpLatticeInf_le_left L M
  have hBM : B.carrier ≤ M.carrier :=
    completedPseudoDiffOpLatticeInf_le_right L M
  have hAL : A.carrier ≤ L.carrier :=
    completedPseudoDiffOpLatticeInf_le_left L N
  have hCM : C.carrier ≤ M.carrier :=
    completedPseudoDiffOpLatticeInf_le_left M N
  have hQB : Q.carrier ≤ B.carrier :=
    completedPseudoDiffOpLatticeInf_le_left B N
  have hQA : Q.carrier ≤ A.carrier := by
    rw [show Q.carrier = B.carrier ⊓ N.carrier from
      completedPseudoDiffOpLatticeInf_carrier B N,
      show B.carrier = L.carrier ⊓ M.carrier from
        completedPseudoDiffOpLatticeInf_carrier L M,
      show A.carrier = L.carrier ⊓ N.carrier from
        completedPseudoDiffOpLatticeInf_carrier L N]
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  have hlength := submoduleInfLayer_length_le
    L.carrier M.carrier N.carrier
  have hQBnat := completedPseudoDiffOpLatticeQuotient_length_eq_natLength
    Q B hQB
  have hCMnat := completedPseudoDiffOpLatticeQuotient_length_eq_natLength
    C M hCM
  change Module.length (CompletedPseudoDiffOpInteger (K := K))
      ((↑B.carrier) ⧸ nestedSubmoduleInside Q.carrier B.carrier) =
        completedPseudoDiffOpLatticeQuotientNatLength Q B at hQBnat
  change Module.length (CompletedPseudoDiffOpInteger (K := K))
      ((↑M.carrier) ⧸ nestedSubmoduleInside C.carrier M.carrier) =
        completedPseudoDiffOpLatticeQuotientNatLength C M at hCMnat
  rw [show Q.carrier = (L.carrier ⊓ M.carrier) ⊓ N.carrier by
        rw [show Q.carrier = B.carrier ⊓ N.carrier from
          completedPseudoDiffOpLatticeInf_carrier B N,
          show B.carrier = L.carrier ⊓ M.carrier from
            completedPseudoDiffOpLatticeInf_carrier L M],
      show B.carrier = L.carrier ⊓ M.carrier from
        completedPseudoDiffOpLatticeInf_carrier L M] at hQBnat
  rw [show C.carrier = M.carrier ⊓ N.carrier from
    completedPseudoDiffOpLatticeInf_carrier M N] at hCMnat
  have hlayerNat :
      completedPseudoDiffOpLatticeQuotientNatLength Q B ≤
        completedPseudoDiffOpLatticeQuotientNatLength C M := by
    exact ENat.coe_le_coe.mp (hQBnat ▸ hCMnat ▸ hlength)
  have hQAL := completedPseudoDiffOpLatticeQuotientNatLength_add
    Q A L hQA hAL
  have hQBL := completedPseudoDiffOpLatticeQuotientNatLength_add
    Q B L hQB hBL
  change completedPseudoDiffOpLatticeQuotientNatLength A L ≤
    completedPseudoDiffOpLatticeQuotientNatLength B L +
      completedPseudoDiffOpLatticeQuotientNatLength C M
  omega

theorem completedPseudoDiffOpCartan_hinge_triangle
    (s u : ℤ) (L M N : CompletedPseudoDiffOpLattice K (Fin r)) :
    (∑ i, Int.toNat (max 0
        (completedPseudoDiffOpDominantRelativePosition L N i - (s + u)))) ≤
      (∑ i, Int.toNat (max 0
        (completedPseudoDiffOpDominantRelativePosition L M i - s))) +
      ∑ i, Int.toNat (max 0
        (completedPseudoDiffOpDominantRelativePosition M N i - u)) := by
  have h := completedPseudoDiffOpLatticeAsymmetricDistanceNat_triangle
    (leftUniformizerShiftCompletedPseudoDiffOpLattice (s + u) L)
    (leftUniformizerShiftCompletedPseudoDiffOpLattice u M) N
  rw [completedPseudoDiffOpLatticeAsymmetricDistanceNat_leftUniformizerShift_eq_hinge,
    completedPseudoDiffOpLatticeAsymmetricDistanceNat_twoUniformizerShifts_eq_hinge,
    completedPseudoDiffOpLatticeAsymmetricDistanceNat_leftUniformizerShift_eq_hinge] at h
  exact h

def integralTupleReal (m : Fin r → ℤ) : Fin r → ℝ :=
  fun i => (m i : ℝ)

def integralTupleHingeReal (t : ℤ) (m : Fin r → ℤ) : ℝ :=
  ∑ i, ((max 0 (m i - t) : ℤ) : ℝ)

theorem integralTupleHingeReal_eq_natCast (t : ℤ) (m : Fin r → ℤ) :
    integralTupleHingeReal t m =
      ((∑ i, Int.toNat (max 0 (m i - t))) : ℕ) := by
  rw [integralTupleHingeReal, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  norm_cast
  rw [Int.toNat_of_nonneg (le_max_left 0 (m i - t))]

theorem topSum_integralTupleReal_of_antitone
    (m : Fin r → ℤ) (hm : Antitone m) (k : ℕ) (hk : k ≤ r) :
    topSum k (integralTupleReal m) =
      ∑ i ∈ firstIdx r k, (m i : ℝ) := by
  have hmreal : Antitone (integralTupleReal m) := by
    intro i j hij
    change (m j : ℝ) ≤ (m i : ℝ)
    exact_mod_cast hm hij
  apply le_antisymm
  · obtain ⟨s, hs, hsum⟩ := exists_sum_eq_topSum (integralTupleReal m) hk
    rw [← hsum]
    exact sum_le_sum_firstIdx hmreal hk hs
  · exact sum_le_topSum hk (card_firstIdx hk)

theorem topSum_eq_sum_firstIdx_of_antitone
    (v : Fin r → ℝ) (hv : Antitone v) (k : ℕ) (hk : k ≤ r) :
    topSum k v = ∑ i ∈ firstIdx r k, v i := by
  apply le_antisymm
  · obtain ⟨s, hs, hsum⟩ := exists_sum_eq_topSum v hk
    rw [← hsum]
    exact sum_le_sum_firstIdx hv hk hs
  · exact sum_le_topSum hk (card_firstIdx hk)

theorem topSum_centeredCoweight
    (m : Fin r → ℤ) (hm : Antitone m) (k : ℕ) (hk : k ≤ r) :
    topSum k (centeredCoweight m) =
      topSum k (integralTupleReal m) -
        (k : ℝ) * ((∑ i, (m i : ℝ)) / r) := by
  have hcenter : Antitone (centeredCoweight m) := by
    intro i j hij
    simp only [centeredCoweight]
    exact sub_le_sub_right (by exact_mod_cast hm hij) _
  rw [topSum_eq_sum_firstIdx_of_antitone (centeredCoweight m) hcenter k hk,
    topSum_integralTupleReal_of_antitone m hm k hk]
  simp only [centeredCoweight, Finset.sum_sub_distrib, Finset.sum_const,
    card_firstIdx hk, nsmul_eq_mul]
  simp

theorem sum_subset_integralTupleReal_le_threshold_hinge
    (m : Fin r → ℤ) (t : ℤ) (s : Finset (Fin r)) :
    (∑ i ∈ s, (m i : ℝ)) ≤
      (s.card : ℝ) * (t : ℝ) + integralTupleHingeReal t m := by
  have hpoint (i : Fin r) :
      (m i : ℝ) ≤ (t : ℝ) + ((max 0 (m i - t) : ℤ) : ℝ) := by
    by_cases h : t ≤ m i
    · rw [max_eq_right (sub_nonneg.mpr h)]
      norm_cast
      omega
    · rw [max_eq_left (sub_nonpos.mpr (le_of_not_ge h))]
      norm_cast
      omega
  calc
    (∑ i ∈ s, (m i : ℝ)) ≤
        ∑ i ∈ s, ((t : ℝ) + ((max 0 (m i - t) : ℤ) : ℝ)) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = (s.card : ℝ) * (t : ℝ) +
        ∑ i ∈ s, ((max 0 (m i - t) : ℤ) : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [mul_comm]
    _ ≤ (s.card : ℝ) * (t : ℝ) + integralTupleHingeReal t m := by
      rw [integralTupleHingeReal]
      have hh := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
        (fun i _ _ => show (0 : ℝ) ≤
          ((max 0 (m i - t) : ℤ) : ℝ) by positivity)
      linarith

theorem integralTupleHingeReal_eq_firstIdx
    (m : Fin r → ℤ) (hm : Antitone m) (k : ℕ) (hk0 : 0 < k) (hk : k ≤ r) :
    integralTupleHingeReal (m ⟨k - 1, by omega⟩) m =
      ∑ i ∈ firstIdx r k, ((m i - m ⟨k - 1, by omega⟩ : ℤ) : ℝ) := by
  let q : Fin r := ⟨k - 1, by omega⟩
  change integralTupleHingeReal (m q) m =
    ∑ i ∈ firstIdx r k, ((m i - m q : ℤ) : ℝ)
  rw [integralTupleHingeReal]
  calc
    (∑ i, ((max 0 (m i - m q) : ℤ) : ℝ)) =
        ∑ i, if i ∈ firstIdx r k then
          ((m i - m q : ℤ) : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ firstIdx r k
      · have hnonneg : 0 ≤ m i - m q := sub_nonneg.mpr (hm (by
          change i.val ≤ q.val
          dsimp [q]
          have hi' := mem_firstIdx.mp hi
          omega))
        rw [if_pos hi, max_eq_right hnonneg]
      · have hnonpos : m i - m q ≤ 0 := sub_nonpos.mpr (hm (by
          change q.val ≤ i.val
          dsimp [q]
          have hki : k ≤ i.val := by
            exact Nat.le_of_not_gt (fun hlt => hi (mem_firstIdx.mpr hlt))
          omega))
        rw [if_neg hi, max_eq_left hnonpos]
        norm_cast
    _ = ∑ i ∈ firstIdx r k,
        ((m i - m q : ℤ) : ℝ) := by
      simp

theorem threshold_hinge_eq_topSum_integralTupleReal
    (m : Fin r → ℤ) (hm : Antitone m) (k : ℕ) (hk0 : 0 < k) (hk : k ≤ r) :
    (k : ℝ) * (m ⟨k - 1, by omega⟩ : ℝ) +
        integralTupleHingeReal (m ⟨k - 1, by omega⟩) m =
      topSum k (integralTupleReal m) := by
  rw [integralTupleHingeReal_eq_firstIdx m hm k hk0 hk,
    topSum_integralTupleReal_of_antitone m hm k hk]
  simp only [Int.cast_sub]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_const, card_firstIdx hk]
  simp only [nsmul_eq_mul]
  ring

theorem completedPseudoDiffOpCartan_topSum_triangle
    (L M N : CompletedPseudoDiffOpLattice K (Fin r))
    (k : ℕ) (hk : k ≤ r) :
    topSum k (integralTupleReal
        (completedPseudoDiffOpDominantRelativePosition L N)) ≤
      topSum k (integralTupleReal
          (completedPseudoDiffOpDominantRelativePosition L M)) +
        topSum k (integralTupleReal
          (completedPseudoDiffOpDominantRelativePosition M N)) := by
  by_cases hk0 : k = 0
  · subst k
    simp [topSum, firstIdx]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    let a := completedPseudoDiffOpDominantRelativePosition L N
    let b := completedPseudoDiffOpDominantRelativePosition L M
    let c := completedPseudoDiffOpDominantRelativePosition M N
    let q : Fin r := ⟨k - 1, by omega⟩
    let s := b q
    let u := c q
    have hnat := completedPseudoDiffOpCartan_hinge_triangle s u L M N
    have hreal : integralTupleHingeReal (s + u) a ≤
        integralTupleHingeReal s b + integralTupleHingeReal u c := by
      rw [integralTupleHingeReal_eq_natCast,
        integralTupleHingeReal_eq_natCast,
        integralTupleHingeReal_eq_natCast]
      exact_mod_cast hnat
    obtain ⟨v, hvcard, hvtop⟩ := exists_sum_eq_topSum (integralTupleReal a) hk
    change topSum k (integralTupleReal a) ≤
      topSum k (integralTupleReal b) + topSum k (integralTupleReal c)
    rw [← hvtop]
    calc
      (∑ i ∈ v, integralTupleReal a i) ≤
          (v.card : ℝ) * ((s + u : ℤ) : ℝ) +
            integralTupleHingeReal (s + u) a :=
        sum_subset_integralTupleReal_le_threshold_hinge a (s + u) v
      _ ≤ (k : ℝ) * ((s + u : ℤ) : ℝ) +
          (integralTupleHingeReal s b + integralTupleHingeReal u c) := by
        rw [hvcard]
        linarith
      _ = ((k : ℝ) * (s : ℝ) + integralTupleHingeReal s b) +
          ((k : ℝ) * (u : ℝ) + integralTupleHingeReal u c) := by
        push_cast
        ring
      _ = topSum k (integralTupleReal b) +
          topSum k (integralTupleReal c) := by
        have hb := threshold_hinge_eq_topSum_integralTupleReal b
          (completedPseudoDiffOpDominantRelativePosition_antitone L M)
          k hkpos hk
        have hc := threshold_hinge_eq_topSum_integralTupleReal c
          (completedPseudoDiffOpDominantRelativePosition_antitone M N)
          k hkpos hk
        change (k : ℝ) * (b q : ℝ) + integralTupleHingeReal (b q) b +
            ((k : ℝ) * (c q : ℝ) + integralTupleHingeReal (c q) c) = _
        rw [hb, hc]

theorem completedPseudoDiffOpCenteredCartan_topSum_triangle
    (L M N : CompletedPseudoDiffOpLattice K (Fin r))
    (k : ℕ) (hk : k ≤ r) :
    topSum k (completedPseudoDiffOpEuclideanRelativePosition L N) ≤
      topSum k (completedPseudoDiffOpEuclideanRelativePosition L M) +
        topSum k (completedPseudoDiffOpEuclideanRelativePosition M N) := by
  let a := completedPseudoDiffOpDominantRelativePosition L N
  let b := completedPseudoDiffOpDominantRelativePosition L M
  let c := completedPseudoDiffOpDominantRelativePosition M N
  have hunc := completedPseudoDiffOpCartan_topSum_triangle L M N k hk
  change topSum k (integralTupleReal a) ≤
    topSum k (integralTupleReal b) + topSum k (integralTupleReal c) at hunc
  have hindex := completedPseudoDiffOpCartanIndex_add L M N
  change (∑ i, a i) = (∑ i, b i) + ∑ i, c i at hindex
  have hsumreal : (∑ i, (a i : ℝ)) =
      (∑ i, (b i : ℝ)) + ∑ i, (c i : ℝ) := by
    exact_mod_cast hindex
  have hmean : ((∑ i, (a i : ℝ)) / r) =
      ((∑ i, (b i : ℝ)) / r) + ((∑ i, (c i : ℝ)) / r) := by
    rw [hsumreal]
    ring
  change topSum k (centeredCoweight a) ≤
    topSum k (centeredCoweight b) + topSum k (centeredCoweight c)
  rw [topSum_centeredCoweight a
      (completedPseudoDiffOpDominantRelativePosition_antitone L N) k hk,
    topSum_centeredCoweight b
      (completedPseudoDiffOpDominantRelativePosition_antitone L M) k hk,
    topSum_centeredCoweight c
      (completedPseudoDiffOpDominantRelativePosition_antitone M N) k hk]
  nlinarith

theorem completedPseudoDiffOpEuclideanRelativePosition_sqrt_sum_sq_triangle
    (L M N : CompletedPseudoDiffOpLattice K (Fin r)) :
    Real.sqrt (∑ i, completedPseudoDiffOpEuclideanRelativePosition L N i ^ 2) ≤
      Real.sqrt (∑ i, completedPseudoDiffOpEuclideanRelativePosition L M i ^ 2) +
        Real.sqrt (∑ i, completedPseudoDiffOpEuclideanRelativePosition M N i ^ 2) := by
  apply sqrt_sum_sq_le_of_topSum_le
  · exact fun k hk => completedPseudoDiffOpCenteredCartan_topSum_triangle L M N k hk
  · rw [completedPseudoDiffOpEuclideanRelativePosition,
      completedPseudoDiffOpEuclideanRelativePosition,
      completedPseudoDiffOpEuclideanRelativePosition,
      centeredCoweight_sum_eq_zero, centeredCoweight_sum_eq_zero,
      centeredCoweight_sum_eq_zero, zero_add]

theorem completedPseudoDiffOpEuclideanRelativePositionPoint_norm_triangle
    (L M N : CompletedPseudoDiffOpLattice K (Fin r)) :
    ‖(completedPseudoDiffOpEuclideanRelativePositionPoint L N).1‖ ≤
      ‖(completedPseudoDiffOpEuclideanRelativePositionPoint L M).1‖ +
        ‖(completedPseudoDiffOpEuclideanRelativePositionPoint M N).1‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [completedPseudoDiffOpEuclideanRelativePositionPoint,
    WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs]
  change Real.sqrt (∑ i, completedPseudoDiffOpEuclideanRelativePosition L N i ^ 2) ≤
    Real.sqrt (∑ i, completedPseudoDiffOpEuclideanRelativePosition L M i ^ 2) +
      Real.sqrt (∑ i, completedPseudoDiffOpEuclideanRelativePosition M N i ^ 2)
  exact completedPseudoDiffOpEuclideanRelativePosition_sqrt_sum_sq_triangle L M N

theorem differentialVariationalProjectiveEuclideanVertexDistance_triangle
    (x y z : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    differentialVariationalProjectiveEuclideanVertexDistance x z ≤
      differentialVariationalProjectiveEuclideanVertexDistance x y +
        differentialVariationalProjectiveEuclideanVertexDistance y z := by
  refine Quotient.inductionOn₃ x y z ?_
  intro L M N
  exact completedPseudoDiffOpEuclideanRelativePositionPoint_norm_triangle L M N

end

end GaloisForLFunctions.HTGeometry.DiffOp
