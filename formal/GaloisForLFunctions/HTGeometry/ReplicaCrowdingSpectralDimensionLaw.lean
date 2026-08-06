import GaloisForLFunctions.HTGeometry.LinearIndependentMinorCertificate
import GaloisForLFunctions.HTGeometry.ReplicaActionCrowdingShortcutLaw
import GaloisForLFunctions.QuantumAlg.Util.Complex

/-!
# Replica crowding forces low-dimensional slow spectral characters

Finite-window replica-action crowding is controlled by the rational rank of its balanced
integer multiplicity differences.  A rank-`s` crowding fibre contains at most
`(2 * n + 1)^s` points, and every near-action pair supplies a spectral character whose phase
remains within `|t| * δ` of one.  These structural bounds replace an uninformative global
minimum action gap in the Gaussian and uniform recurrence-capture laws.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

example (r : ℕ) : (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
  rw [Int.card_Icc]
  omega

def replicaMultiplicityDifference
    {I : Type*} (p q : I → ℕ) (i : I) : ℤ :=
  (p i : ℤ) - (q i : ℤ)

theorem sum_replicaMultiplicityDifference_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    {p q : I → ℕ} {n : ℕ}
    (hp : p ∈ Finset.univ.piAntidiag n)
    (hq : q ∈ Finset.univ.piAntidiag n) :
    ∑ i, replicaMultiplicityDifference p q i = 0 := by
  rw [Finset.mem_piAntidiag] at hp hq
  unfold replicaMultiplicityDifference
  have hsub :
      (∑ i, ((p i : ℤ) - (q i : ℤ))) =
        (∑ i, (p i : ℤ)) - ∑ i, (q i : ℤ) := by
    simpa only using
      (Finset.sum_sub_distrib (s := (Finset.univ : Finset I))
        (fun i => (p i : ℤ)) (fun i => (q i : ℤ)))
  calc
    ∑ i, ((p i : ℤ) - (q i : ℤ)) =
        (∑ i, (p i : ℤ)) - ∑ i, (q i : ℤ) := hsub
    _ = ((∑ i, p i : ℕ) : ℤ) - ((∑ i, q i : ℕ) : ℤ) := by
      norm_cast
    _ = 0 := by rw [hp.1, hq.1]; simp

theorem replicaMultiplicityDifference_energy_eq
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (p q : I → ℕ) :
    ∑ i, (replicaMultiplicityDifference p q i : ℝ) * energy i =
      replicaMultiplicityEnergy energy p -
        replicaMultiplicityEnergy energy q := by
  unfold replicaMultiplicityDifference replicaMultiplicityEnergy
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]

theorem abs_replicaMultiplicityDifference_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {p q : I → ℕ} {n : ℕ}
    (hp : p ∈ Finset.univ.piAntidiag n)
    (hq : q ∈ Finset.univ.piAntidiag n) (i : I) :
    |replicaMultiplicityDifference p q i| ≤ (n : ℤ) := by
  rw [Finset.mem_piAntidiag] at hp hq
  have hpi : p i ≤ n := by
    calc
      p i ≤ ∑ j, p j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = n := hp.1
  have hqi : q i ≤ n := by
    calc
      q i ≤ ∑ j, q j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = n := hq.1
  unfold replicaMultiplicityDifference
  rw [abs_le]
  constructor <;> omega

theorem replicaMultiplicityDifference_ne_zero_of_near
    {I : Type*} [Fintype I] [DecidableEq I]
    {energy : I → ℝ} {n : ℕ} {δ : ℝ}
    {p q : ReplicaMultiplicityIndex I n}
    (hnear : replicaNearAction energy n δ p q) :
    replicaMultiplicityDifference p.1 q.1 ≠ 0 := by
  intro hzero
  have hpq : p.1 = q.1 := by
    funext i
    have hi : replicaMultiplicityDifference p.1 q.1 i = 0 := by
      simpa using congrFun hzero i
    unfold replicaMultiplicityDifference at hi
    omega
  have hpqsub : p = q := Subtype.ext hpq
  subst q
  exact (lt_irrefl 0) (by simpa [replicaNearAction] using hnear.1)

noncomputable def integerCoordinateBox
    (N : Type*) [Fintype N] [DecidableEq N] (r : ℕ) :
    Finset (N → ℤ) :=
  Fintype.piFinset fun (_ : N) => Finset.Icc (-(r : ℤ)) (r : ℤ)

theorem card_integerCoordinateBox
    (N : Type*) [Fintype N] [DecidableEq N] (r : ℕ) :
    (integerCoordinateBox N r).card =
      (2 * r + 1) ^ Fintype.card N := by
  classical
  rw [integerCoordinateBox, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ]
  congr 1
  omega

theorem card_le_coordinateBox_of_injective_projection
    {I N : Type*} [Fintype N] [DecidableEq N]
    (S : Finset (I → ℤ)) (φ : N → I) (r : ℕ)
    (hbound : ∀ k ∈ S, ∀ i, |k i| ≤ (r : ℤ))
    (hinj : Set.InjOn (fun k : I → ℤ => fun j => k (φ j)) S) :
    S.card ≤ (2 * r + 1) ^ Fintype.card N := by
  classical
  let proj : (I → ℤ) → (N → ℤ) := fun k j => k (φ j)
  have hsubset : S.image proj ⊆ integerCoordinateBox N r := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [integerCoordinateBox]
    change (fun j : N => k (φ j)) ∈
      Fintype.piFinset
        (fun (_ : N) => Finset.Icc (-(r : ℤ)) (r : ℤ))
    simp only [Fintype.mem_piFinset]
    exact fun j => by
      rw [Finset.mem_Icc]
      exact (abs_le.mp (hbound k hk (φ j)))
  calc
    S.card = (S.image proj).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (integerCoordinateBox N r).card := Finset.card_le_card hsubset
    _ = (2 * r + 1) ^ Fintype.card N := card_integerCoordinateBox N r

theorem exists_coordinateProjection_injective_on_submodule
    {K I : Type*} [Field K] [Fintype I]
    (V : Submodule K (I → K)) :
    ∃ φ : Fin (Module.finrank K V) → I,
      Set.InjOn
        (fun x : I → K => fun j => x (φ j)) V := by
  classical
  let b : Module.Basis (Fin (Module.finrank K V)) K V := Module.finBasis K V
  let v : Fin (Module.finrank K V) → I → K := fun j => (b j : V).1
  have hv : LinearIndependent K v := by
    exact b.linearIndependent.map' V.subtype V.ker_subtype
  obtain ⟨φ, hdet⟩ := exists_coordinateMinor_det_ne_zero v hv
  refine ⟨φ, ?_⟩
  intro x hx y hy hxy
  let xV : V := ⟨x, hx⟩
  let yV : V := ⟨y, hy⟩
  let z : V := xV - yV
  let c : Fin (Module.finrank K V) → K := fun j => b.repr z j
  have hzcoord (i : Fin (Module.finrank K V)) : z.1 (φ i) = 0 := by
    change x (φ i) - y (φ i) = 0
    exact sub_eq_zero.mpr (congrFun hxy i)
  have hmul : (coordinateMinor v φ).mulVec c = 0 := by
    funext i
    have hsum' :
        ∑ j, c j * v j (φ i) = z.1 (φ i) := by
      rw [← b.sum_repr z]
      simp only [c, v, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
    rw [Matrix.mulVec, dotProduct]
    simp only [coordinateMinor_apply]
    calc
      ∑ j, v j (φ i) * c j = ∑ j, c j * v j (φ i) := by
        exact Finset.sum_congr rfl fun j hj => by ring
      _ = z.1 (φ i) := hsum'
      _ = 0 := hzcoord i
  have hc : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have hrepr : b.repr z = 0 := by
    ext j
    exact congrFun hc j
  have hz : z = 0 := b.repr.injective (by rw [hrepr]; simp)
  have hxyV : xV = yV := sub_eq_zero.mp hz
  exact congrArg Subtype.val hxyV

def intVectorToRat {I : Type*} (k : I → ℤ) : I → ℚ :=
  fun i => (k i : ℚ)

theorem intVectorToRat_injective {I : Type*} :
    Function.Injective (@intVectorToRat I) := by
  intro k l hkl
  funext i
  have hi := congrFun hkl i
  exact Rat.intCast_inj.mp (by simpa [intVectorToRat] using hi)

theorem card_intVectors_le_pow_finrank_span
    {I : Type*} [Fintype I]
    (S : Finset (I → ℤ)) (r : ℕ)
    (hbound : ∀ k ∈ S, ∀ i, |k i| ≤ (r : ℤ)) :
    S.card ≤ (2 * r + 1) ^
      Module.finrank ℚ
        (Submodule.span ℚ
          (↑(S.image intVectorToRat) : Set (I → ℚ))) := by
  classical
  let ratS : Finset (I → ℚ) := S.image intVectorToRat
  let V : Submodule ℚ (I → ℚ) := Submodule.span ℚ (↑ratS : Set (I → ℚ))
  obtain ⟨φ, hproj⟩ := exists_coordinateProjection_injective_on_submodule V
  have hinj : Set.InjOn
      (fun k : I → ℤ => fun j => k (φ j)) S := by
    intro k hk l hl hcoords
    apply intVectorToRat_injective
    apply hproj
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
    · funext j
      have hj := congrFun hcoords j
      simpa [intVectorToRat] using congrArg (fun z : ℤ => (z : ℚ)) hj
  simpa only [V, ratS, Fintype.card_fin] using
    card_le_coordinateBox_of_injective_projection S φ r hbound hinj

theorem replicaMultiplicityDifference_left_injective
    {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (p : ReplicaMultiplicityIndex I n) :
    Function.Injective
      (fun q : ReplicaMultiplicityIndex I n =>
        replicaMultiplicityDifference q.1 p.1) := by
  intro q q' hqq'
  apply Subtype.ext
  funext i
  have hi := congrFun hqq' i
  unfold replicaMultiplicityDifference at hi
  exact Int.ofNat_inj.mp (sub_left_inj.mp hi)

noncomputable def replicaNearDifferenceSet
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) : Finset (I → ℤ) := by
  classical
  exact (Finset.univ.filter (replicaNearAction energy n δ p)).image
    (fun q => replicaMultiplicityDifference q.1 p.1)

noncomputable def replicaNearActionRankAt
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) : ℕ :=
  Module.finrank ℚ
    (Submodule.span ℚ
      (↑((replicaNearDifferenceSet energy n δ p).image intVectorToRat) :
        Set (I → ℚ)))

theorem card_filter_replicaNearAction_le_pow_rankAt
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) :
    (Finset.univ.filter (replicaNearAction energy n δ p)).card ≤
      (2 * n + 1) ^ replicaNearActionRankAt energy n δ p := by
  classical
  let S := replicaNearDifferenceSet energy n δ p
  have hcard : S.card =
      (Finset.univ.filter (replicaNearAction energy n δ p)).card := by
    unfold S replicaNearDifferenceSet
    exact Finset.card_image_of_injective _
      (replicaMultiplicityDifference_left_injective p)
  have hbound : ∀ k ∈ S, ∀ i, |k i| ≤ (n : ℤ) := by
    intro k hk i
    unfold S replicaNearDifferenceSet at hk
    rw [Finset.mem_image] at hk
    obtain ⟨q, hq, rfl⟩ := hk
    exact abs_replicaMultiplicityDifference_le q.2 p.2 i
  rw [← hcard]
  exact card_intVectors_le_pow_finrank_span S n hbound

noncomputable def replicaNearActionRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact Finset.univ.sup fun p : ReplicaMultiplicityIndex I n =>
    replicaNearActionRankAt energy n δ p

theorem replicaNearActionRankAt_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) :
    replicaNearActionRankAt energy n δ p ≤
      replicaNearActionRank energy n δ := by
  classical
  unfold replicaNearActionRank
  exact Finset.le_sup
    (s := (Finset.univ : Finset (ReplicaMultiplicityIndex I n)))
    (f := replicaNearActionRankAt energy n δ) (Finset.mem_univ p)

theorem replicaActionCrowdingDegree_le_pow_rank
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ) :
    replicaActionCrowdingDegree energy n δ ≤
      (2 * n + 1) ^ replicaNearActionRank energy n δ := by
  classical
  unfold replicaActionCrowdingDegree
  apply Finset.sup_le
  intro p hp
  exact (card_filter_replicaNearAction_le_pow_rankAt energy n δ p).trans
    (Nat.pow_le_pow_right (by omega)
      (replicaNearActionRankAt_le energy n δ p))

theorem exists_replicaNearCharacterBasisSet
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) :
    ∃ B : Set (I → ℚ),
      B ⊆
        (↑((replicaNearDifferenceSet energy n δ p).image intVectorToRat) :
          Set (I → ℚ)) ∧
      LinearIndepOn ℚ id B ∧
      Submodule.span ℚ B =
        Submodule.span ℚ
          (↑((replicaNearDifferenceSet energy n δ p).image intVectorToRat) :
            Set (I → ℚ)) ∧
      B.Finite := by
  classical
  let S : Set (I → ℚ) :=
    ↑((replicaNearDifferenceSet energy n δ p).image intVectorToRat)
  let hzero : LinearIndepOn ℚ id (∅ : Set (I → ℚ)) :=
    linearIndepOn_empty ℚ id
  let B : Set (I → ℚ) := hzero.extend (Set.empty_subset S)
  have hBsub : B ⊆ S := hzero.extend_subset (Set.empty_subset S)
  have hBind : LinearIndepOn ℚ id B :=
    hzero.linearIndepOn_extend (Set.empty_subset S)
  have hBspan : Submodule.span ℚ B = Submodule.span ℚ S :=
    hzero.span_extend_eq_span (Set.empty_subset S)
  have hSfinite : S.Finite := by
    exact Finset.finite_toSet _
  exact ⟨B, hBsub, hBind, hBspan, hSfinite.subset hBsub⟩

theorem fidelityReplicaPermutationFloor_nonneg_of_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i) (n : ℕ) :
    0 ≤ fidelityReplicaPermutationFloor weight n := by
  unfold fidelityReplicaPermutationFloor
  exact Finset.sum_nonneg fun p hp =>
    fidelityReplicaMultiplicityWeight_nonneg hweight p p

theorem norm_twistedGaussianSpectralFidelityMean_le_collision_add_rank_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
        (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  have hdegreeNat := replicaActionCrowdingDegree_le_pow_rank energy n δ
  have hdegree : (replicaActionCrowdingDegree energy n δ : ℝ) ≤
      (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) := by
    exact_mod_cast hdegreeNat
  have hfloor := fidelityReplicaPermutationFloor_nonneg_of_nonneg hweight n
  exact (norm_twistedGaussianSpectralFidelityMean_le_collision_add_degree_floor
      hweight hweightSum htwist n hT hδ).trans (by gcongr)

theorem norm_twistedFiniteSpectralFidelityMean_le_collision_add_rank_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedFiniteSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
        (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        min 1 (T * δ)⁻¹ := by
  have hdegreeNat := replicaActionCrowdingDegree_le_pow_rank energy n δ
  have hdegree : (replicaActionCrowdingDegree energy n δ : ℝ) ≤
      (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) := by
    exact_mod_cast hdegreeNat
  have hfloor := fidelityReplicaPermutationFloor_nonneg_of_nonneg hweight n
  exact (norm_twistedFiniteSpectralFidelityMean_le_collision_add_degree_floor
      hweight hweightSum htwist n hT hδ).trans (by gcongr)

theorem threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_rank_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      fidelityReplicaCollisionMass weight energy n +
        (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  exact (threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_norm
      hweight hweightSum htwist n hn hthreshold).trans
    (norm_twistedGaussianSpectralFidelityMean_le_collision_add_rank_floor
      hweight hweightSum htwist n hT hδ)

theorem threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_rank_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        volume.real
          (uniformTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      2 * T *
        (fidelityReplicaCollisionMass weight energy n +
          (((2 * n + 1) ^ replicaNearActionRank energy n δ : ℕ) : ℝ) *
            fidelityReplicaPermutationFloor weight n +
          min 1 (T * δ)⁻¹) := by
  exact (threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_norm
      n hn hT hthreshold).trans
    (mul_le_mul_of_nonneg_left
      (norm_twistedFiniteSpectralFidelityMean_le_collision_add_rank_floor
        hweight hweightSum htwist n hT hδ)
      (mul_nonneg (by norm_num) hT.le))

theorem norm_replicaNearAction_character_sub_one_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {energy : I → ℝ} {n : ℕ} {δ t : ℝ}
    {p q : ReplicaMultiplicityIndex I n}
    (hnear : replicaNearAction energy n δ p q) :
    ‖Complex.exp
        (((t * ∑ i, (replicaMultiplicityDifference p.1 q.1 i : ℝ) *
          energy i : ℝ) : ℂ) * Complex.I) - 1‖ ≤
      |t| * δ := by
  have hpair := replicaMultiplicityDifference_energy_eq energy p.1 q.1
  have hchord := QuantumAlg.norm_exp_ofReal_mul_I_sub_one_le
    (t * ∑ i, (replicaMultiplicityDifference p.1 q.1 i : ℝ) * energy i)
  rw [abs_mul, hpair] at hchord
  simpa only [hpair] using
    hchord.trans (mul_le_mul_of_nonneg_left hnear.2.le (abs_nonneg t))

theorem ncard_eq_finrank_span_of_linearIndepOn
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (B : Set V) (hfinite : B.Finite)
    (hlinear : LinearIndepOn K id B) :
    B.ncard = Module.finrank K (Submodule.span K B) := by
  classical
  letI : Fintype B := hfinite.fintype
  have hli : LinearIndependent K (fun b : B => (b : V)) := by
    simpa only [LinearIndepOn, id_eq] using hlinear
  have hspan :
      Submodule.span K (Set.range fun b : B => (b : V)) =
        Submodule.span K B := by
    congr 1
    exact Subtype.range_coe_subtype
  have hrange :
      Module.finrank K
          (Submodule.span K (Set.range fun b : B => (b : V))) =
        Fintype.card B := finrank_span_eq_card hli
  have heqv :
      Submodule.span K (Set.range fun b : B => (b : V)) ≃ₗ[K]
        Submodule.span K B :=
    LinearEquiv.ofEq _ _ hspan
  calc
    B.ncard = Fintype.card B := by simp
    _ = Module.finrank K
          (Submodule.span K (Set.range fun b : B => (b : V))) := hrange.symm
    _ = Module.finrank K (Submodule.span K B) := heqv.finrank_eq

theorem exists_replicaNearCharacterBasisSet_card_rank
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) :
    ∃ B : Set (I → ℚ),
      B ⊆
        (↑((replicaNearDifferenceSet energy n δ p).image intVectorToRat) :
          Set (I → ℚ)) ∧
      LinearIndepOn ℚ id B ∧
      Submodule.span ℚ B =
        Submodule.span ℚ
          (↑((replicaNearDifferenceSet energy n δ p).image intVectorToRat) :
            Set (I → ℚ)) ∧
      B.Finite ∧
      B.ncard = replicaNearActionRankAt energy n δ p := by
  obtain ⟨B, hsub, hlinear, hspan, hfinite⟩ :=
    exists_replicaNearCharacterBasisSet energy n δ p
  refine ⟨B, hsub, hlinear, hspan, hfinite, ?_⟩
  rw [replicaNearActionRankAt, ← hspan]
  exact ncard_eq_finrank_span_of_linearIndepOn B hfinite hlinear

end GaloisForLFunctions.HTGeometry
