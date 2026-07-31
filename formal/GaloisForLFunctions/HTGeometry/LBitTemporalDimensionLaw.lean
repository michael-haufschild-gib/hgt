import GaloisForLFunctions.HTGeometry.SeparableInteractionTemporalDimensionLaw
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz

/-!
# Exact temporal dimension of localized l-bit Hamiltonians

A finite l-bit Hamiltonian is diagonal in a fixed Boolean configuration basis, with its energy
written in the complete Walsh basis. This file proves an exact arithmetic law: the rational
dimension of all anchored energy gaps is exactly the rational dimension of the nonconstant Walsh
coefficients. Consequently, finite-order interaction truncations have a coefficient-count ceiling,
whereas arbitrarily small all-order diagonal perturbations can attain the full exponential temporal
dimension while leaving the configuration eigenbasis unchanged.
-/

open Set Filter NormedSpace Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitTemporalFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

def lbitSign (b : Bool) : ℚ :=
  if b then -1 else 1

def lbitWalshCharacter
    {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I)
    (x : I → Bool) : ℚ :=
  ∏ i : I, if i ∈ S then lbitSign (x i) else 1

theorem sum_lbitWalshCharacter_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (S T : Finset I) :
    (∑ x : I → Bool,
      lbitWalshCharacter S x *
        lbitWalshCharacter T x) =
      if S = T then (2 : ℚ) ^ Fintype.card I else 0 := by
  classical
  let localTerm : I → Bool → ℚ :=
    fun i b =>
      (if i ∈ S then lbitSign b else 1) *
        (if i ∈ T then lbitSign b else 1)
  calc
    (∑ x : I → Bool,
      lbitWalshCharacter S x *
        lbitWalshCharacter T x) =
        ∑ x : I → Bool, ∏ i : I, localTerm i (x i) := by
          apply Finset.sum_congr rfl
          intro x hx
          change
            (∏ i : I, if i ∈ S then lbitSign (x i) else 1) *
                (∏ i : I, if i ∈ T then lbitSign (x i) else 1) =
              ∏ i : I, localTerm i (x i)
          rw [Finset.prod_mul_distrib]
    _ = ∏ i : I, ∑ b : Bool, localTerm i b := by
      rw [show (Finset.univ : Finset (I → Bool)) =
          Fintype.piFinset (fun _ : I => (Finset.univ : Finset Bool)) by
        ext x
        simp]
      simpa using
        Finset.sum_prod_piFinset
          (Finset.univ : Finset Bool) localTerm
    _ = if S = T then (2 : ℚ) ^ Fintype.card I else 0 := by
      by_cases hST : S = T
      · subst T
        rw [if_pos rfl]
        have hlocal : ∀ i, (∑ b : Bool, localTerm i b) = (2 : ℚ) := by
          intro i
          by_cases hi : i ∈ S <;>
            norm_num [localTerm, hi, lbitSign]
        simp_rw [hlocal]
        simp
      · rw [if_neg hST]
        have hex : ∃ i, (i ∈ S) ≠ (i ∈ T) := by
          by_contra h
          push Not at h
          exact hST (Finset.ext fun i => iff_of_eq (h i))
        obtain ⟨i, hi⟩ := hex
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        by_cases hiS : i ∈ S <;>
          by_cases hiT : i ∈ T <;>
          simp_all [localTerm, lbitSign]

def lbitZeroConfiguration {I : Type*} : I → Bool :=
  fun _ => false

def lbitEnergy
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (x : I → Bool) : ℝ :=
  ∑ S : Finset I, lbitWalshCharacter S x • J S

def lbitGap
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (x : I → Bool) : ℝ :=
  lbitEnergy J x - lbitEnergy J lbitZeroConfiguration

theorem sum_lbitWalshCharacter_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    {S : Finset I} (hS : S.Nonempty) :
    (∑ x : I → Bool, lbitWalshCharacter S x) = 0 := by
  have h := sum_lbitWalshCharacter_mul S ∅
  rw [if_neg (Finset.nonempty_iff_ne_empty.mp hS)]
    at h
  simpa [lbitWalshCharacter] using h

theorem lbitEnergy_walshCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (S : Finset I) :
    (∑ x : I → Bool,
      lbitWalshCharacter S x • lbitEnergy J x) =
      ((2 : ℚ) ^ Fintype.card I) • J S := by
  classical
  simp_rw [lbitEnergy, Finset.smul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ T : Finset I,
      ∑ x : I → Bool,
        lbitWalshCharacter S x •
          lbitWalshCharacter T x • J T) =
        ∑ T : Finset I,
          (∑ x : I → Bool,
            lbitWalshCharacter S x *
              lbitWalshCharacter T x) • J T := by
            apply Finset.sum_congr rfl
            intro T hT
            rw [Finset.sum_smul]
            apply Finset.sum_congr rfl
            intro x hx
            rw [mul_smul]
    _ = ((2 : ℚ) ^ Fintype.card I) • J S := by
      simp_rw [sum_lbitWalshCharacter_mul]
      simp

theorem lbitGap_walshCoefficient
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) {S : Finset I} (hS : S.Nonempty) :
    (∑ x : I → Bool,
      lbitWalshCharacter S x • lbitGap J x) =
      ((2 : ℚ) ^ Fintype.card I) • J S := by
  unfold lbitGap
  simp_rw [smul_sub, Finset.sum_sub_distrib]
  rw [lbitEnergy_walshCoefficient]
  have hzero := sum_lbitWalshCharacter_eq_zero hS
  rw [← Finset.sum_smul, hzero, zero_smul, sub_zero]

def lbitCoefficientSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ
    (Set.range (fun S : {S : Finset I // S.Nonempty} => J S.1))

def lbitGapSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : Submodule ℚ ℝ :=
  Submodule.span ℚ (Set.range (lbitGap J))

def lbitTemporalRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : ℕ :=
  Module.finrank ℚ (lbitGapSubspace J)

theorem lbitGap_eq_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (x : I → Bool) :
    lbitGap J x =
      ∑ S : Finset I,
        (lbitWalshCharacter S x -
          lbitWalshCharacter S lbitZeroConfiguration) • J S := by
  classical
  unfold lbitGap lbitEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  exact (sub_smul _ _ _).symm

theorem lbitGapSubspace_le_coefficientSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitGapSubspace J ≤ lbitCoefficientSubspace J := by
  apply Submodule.span_le.2
  rintro z ⟨x, rfl⟩
  rw [lbitGap_eq_sum]
  apply Submodule.sum_mem
  intro S hS
  by_cases hSne : S.Nonempty
  · apply Submodule.smul_mem
    exact Submodule.subset_span
      ⟨⟨S, hSne⟩, rfl⟩
  · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    subst S
    simp [lbitWalshCharacter]

theorem lbitCoefficientSubspace_le_gapSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitCoefficientSubspace J ≤ lbitGapSubspace J := by
  apply Submodule.span_le.2
  rintro z ⟨S, rfl⟩
  have hcoefficient :=
    lbitGap_walshCoefficient J S.2
  have htwo : (2 : ℚ) ^ Fintype.card I ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hsum :
      (∑ x : I → Bool,
        lbitWalshCharacter S.1 x • lbitGap J x) ∈
          lbitGapSubspace J := by
    apply Submodule.sum_mem
    intro x hx
    exact Submodule.smul_mem _
      (lbitWalshCharacter S.1 x)
      (Submodule.subset_span ⟨x, rfl⟩)
  have hinv :
      ((2 : ℚ) ^ Fintype.card I)⁻¹ •
          (∑ x : I → Bool,
            lbitWalshCharacter S.1 x • lbitGap J x) ∈
        lbitGapSubspace J :=
    Submodule.smul_mem _ _ hsum
  rw [hcoefficient, inv_smul_smul₀ htwo] at hinv
  exact hinv

theorem lbitGapSubspace_eq_coefficientSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitGapSubspace J = lbitCoefficientSubspace J :=
  le_antisymm
    (lbitGapSubspace_le_coefficientSubspace J)
    (lbitCoefficientSubspace_le_gapSubspace J)

theorem lbitTemporalRank_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitTemporalRank J =
      Module.finrank ℚ (lbitCoefficientSubspace J) := by
  rw [lbitTemporalRank, lbitGapSubspace_eq_coefficientSubspace]

theorem lbitTemporalRank_le_support
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (A : Finset (Finset I))
    (hJ : ∀ S, S.Nonempty → S ∉ A → J S = 0) :
    lbitTemporalRank J ≤ A.card := by
  let Aspan : Submodule ℚ ℝ :=
    Submodule.span ℚ
      (Set.range (fun S : {S : Finset I // S ∈ A} => J S.1))
  letI : FiniteDimensional ℚ Aspan :=
    FiniteDimensional.span_of_finite ℚ
      (Set.finite_range (fun S : {S : Finset I // S ∈ A} => J S.1))
  have hle :
      lbitCoefficientSubspace J ≤ Aspan := by
    apply Submodule.span_le.2
    rintro z ⟨S, rfl⟩
    by_cases hSA : S.1 ∈ A
    · exact Submodule.subset_span ⟨⟨S.1, hSA⟩, rfl⟩
    · change J S.1 ∈ Aspan
      rw [hJ S.1 S.2 hSA]
      exact Aspan.zero_mem
  rw [lbitTemporalRank_eq]
  calc
    Module.finrank ℚ (lbitCoefficientSubspace J) ≤
        Module.finrank ℚ Aspan :=
      Submodule.finrank_mono hle
    _ ≤ Fintype.card {S : Finset I // S ∈ A} := by
      unfold Aspan
      let s : Set ℝ :=
        Set.range (fun S : {S : Finset I // S ∈ A} => J S.1)
      letI : Fintype s := s.toFinite.fintype
      calc
        Module.finrank ℚ ↥(Submodule.span ℚ s) ≤ s.toFinset.card :=
          finrank_span_le_card s
        _ ≤ Fintype.card {S : Finset I // S ∈ A} := by
          convert Fintype.card_range_le
            (fun S : {S : Finset I // S ∈ A} => J S.1) using 1
          rw [Set.toFinset_card]
    _ = A.card := Fintype.card_coe A

def lbitSupportsUpToOrder
    (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) :
    Finset (Finset I) :=
  (Finset.range (k + 1)).disjiUnion
    (fun j => (Finset.univ : Finset I).powersetCard j)
    ((Finset.univ : Finset I).pairwise_disjoint_powersetCard.set_pairwise
      (Finset.range (k + 1)))

theorem mem_lbitSupportsUpToOrder_iff
    {I : Type*} [Fintype I] [DecidableEq I]
    {k : ℕ} {S : Finset I} :
    S ∈ lbitSupportsUpToOrder I k ↔ S.card ≤ k := by
  classical
  rw [lbitSupportsUpToOrder, Finset.mem_disjiUnion]
  constructor
  · rintro ⟨j, hj, hS⟩
    have hjle : j ≤ k := by simpa using hj
    exact (Finset.mem_powersetCard.mp hS).2 ▸ hjle
  · intro hS
    refine ⟨S.card, by simpa, ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩

theorem card_lbitSupportsUpToOrder
    (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) :
    (lbitSupportsUpToOrder I k).card =
      ∑ j ∈ Finset.range (k + 1), Nat.choose (Fintype.card I) j := by
  classical
  unfold lbitSupportsUpToOrder
  rw [Finset.card_disjiUnion]
  apply Finset.sum_congr rfl
  intro j hj
  simp

theorem lbitTemporalRank_le_order
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (k : ℕ)
    (hJ : ∀ S, k < S.card → J S = 0) :
    lbitTemporalRank J ≤
      (∑ j ∈ Finset.range (k + 1), Nat.choose (Fintype.card I) j) - 1 := by
  let A := (lbitSupportsUpToOrder I k).erase ∅
  have hempty :
      ∅ ∈ lbitSupportsUpToOrder I k :=
    mem_lbitSupportsUpToOrder_iff.mpr (by simp)
  have hcard :
      A.card =
        (∑ j ∈ Finset.range (k + 1),
          Nat.choose (Fintype.card I) j) - 1 := by
    change ((lbitSupportsUpToOrder I k).erase ∅).card =
      (∑ j ∈ Finset.range (k + 1),
        Nat.choose (Fintype.card I) j) - 1
    rw [Finset.card_erase_of_mem hempty,
      card_lbitSupportsUpToOrder]
  rw [← hcard]
  apply lbitTemporalRank_le_support J A
  intro S hSne hS
  apply hJ
  by_contra hle
  apply hS
  change S ∈ (lbitSupportsUpToOrder I k).erase ∅
  rw [Finset.mem_erase]
  exact ⟨Finset.nonempty_iff_ne_empty.mp hSne,
    mem_lbitSupportsUpToOrder_iff.mpr (Nat.le_of_not_gt hle)⟩

theorem lbitTemporalRank_eq_card
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ :
      LinearIndependent ℚ
        (fun S : {S : Finset I // S.Nonempty} => J S.1)) :
    lbitTemporalRank J = 2 ^ Fintype.card I - 1 := by
  rw [lbitTemporalRank_eq]
  unfold lbitCoefficientSubspace
  rw [finrank_span_eq_card hJ]
  classical
  simp [Finset.nonempty_iff_ne_empty]

theorem exists_small_lbitEnergy_maximalTemporalRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : Finset I → ℝ,
      J ∅ = 0 ∧
      (∀ S, |J S| < δ) ∧
      LinearIndependent ℚ
        (fun S : {S : Finset I // S.Nonempty} => J S.1) ∧
      lbitTemporalRank J = 2 ^ Fintype.card I - 1 := by
  classical
  let C := {S : Finset I // S.Nonempty}
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  obtain ⟨b, hb, hbclose⟩ :=
    exists_linearIndependent_close
      (Fintype.card C) (fun _ => 0) δ hδ
  let J : Finset I → ℝ :=
    fun S => if hS : S.Nonempty then b (e ⟨S, hS⟩) else 0
  have hJind :
      LinearIndependent ℚ
        (fun S : C => J S.1) := by
    have hcomp :
        LinearIndependent ℚ (fun S : C => b (e S)) :=
      hb.comp e e.injective
    have heq :
        (fun S : C => J S.1) =
          (fun S : C => b (e S)) := by
      funext S
      simp [J, S.2]
    rw [heq]
    exact hcomp
  refine ⟨J, ?_, ?_, hJind, lbitTemporalRank_eq_card J hJind⟩
  · simp [J]
  · intro S
    by_cases hS : S.Nonempty
    · simpa [J, hS, Real.dist_eq] using hbclose (e ⟨S, hS⟩)
    · simp [J, hS, hδ]

theorem abs_lbitWalshCharacter
    {I : Type*} [Fintype I] [DecidableEq I]
    (S : Finset I) (x : I → Bool) :
    |((lbitWalshCharacter S x : ℚ) : ℝ)| = 1 := by
  classical
  have hprod :
      ∀ U : Finset I,
        |(∏ i ∈ U, lbitSign (x i))| = (1 : ℚ) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert a U ha ih =>
        rw [Finset.prod_insert ha]
        rw [abs_mul, ih]
        cases x a <;> norm_num [lbitSign]
  have hreal :
      |(((∏ i ∈ S, lbitSign (x i)) : ℚ) : ℝ)| = 1 := by
    exact_mod_cast hprod S
  simpa [lbitWalshCharacter] using hreal

def lbitCoefficientL1Distance
    {I : Type*} [Fintype I] [DecidableEq I]
    (J K : Finset I → ℝ) : ℝ :=
  ∑ S : Finset I, |J S - K S|

theorem lbitEnergy_sub_abs_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (J K : Finset I → ℝ) (x : I → Bool) :
    |lbitEnergy J x - lbitEnergy K x| ≤
      lbitCoefficientL1Distance J K := by
  classical
  unfold lbitEnergy lbitCoefficientL1Distance
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ S : Finset I,
        (lbitWalshCharacter S x • J S -
          lbitWalshCharacter S x • K S)| ≤
        ∑ S : Finset I,
          |(lbitWalshCharacter S x • J S -
            lbitWalshCharacter S x • K S)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ S : Finset I, |J S - K S| := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← smul_sub]
      simp [Rat.smul_def, abs_mul,
        abs_lbitWalshCharacter]

theorem exists_lbitCoefficients_maximal_close
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : Finset I → ℝ,
      K ∅ = J ∅ ∧
      (∀ S, |K S - J S| < δ) ∧
      LinearIndependent ℚ
        (fun S : {S : Finset I // S.Nonempty} => K S.1) ∧
      lbitTemporalRank K = 2 ^ Fintype.card I - 1 := by
  classical
  let C := {S : Finset I // S.Nonempty}
  let e : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let x : Fin (Fintype.card C) → ℝ :=
    fun i => J (e.symm i)
  obtain ⟨b, hb, hbclose⟩ :=
    exists_linearIndependent_close (Fintype.card C) x δ hδ
  let K : Finset I → ℝ :=
    fun S => if hS : S.Nonempty then b (e ⟨S, hS⟩) else J ∅
  have hKind :
      LinearIndependent ℚ
        (fun S : C => K S.1) := by
    have hcomp :
        LinearIndependent ℚ (fun S : C => b (e S)) :=
      hb.comp e e.injective
    have heq :
        (fun S : C => K S.1) =
          (fun S : C => b (e S)) := by
      funext S
      simp [K, S.2]
    rw [heq]
    exact hcomp
  refine ⟨K, ?_, ?_, hKind, lbitTemporalRank_eq_card K hKind⟩
  · simp [K]
  · intro S
    by_cases hS : S.Nonempty
    · have hclose := hbclose (e ⟨S, hS⟩)
      simpa [K, hS, x, Real.dist_eq] using hclose
    · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      subst S
      simp [K, hδ]

theorem exists_lbitEnergy_maximal_uniformly_close
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Finset I → ℝ,
      K ∅ = J ∅ ∧
      lbitCoefficientL1Distance K J < ε ∧
      (∀ x, |lbitEnergy K x - lbitEnergy J x| < ε) ∧
      lbitTemporalRank K = 2 ^ Fintype.card I - 1 := by
  classical
  let N : ℕ := 2 ^ Fintype.card I
  let δ : ℝ := ε / (N + 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨K, hKempty, hKclose, hKind, hKrank⟩ :=
    exists_lbitCoefficients_maximal_close J δ hδ
  have hL1le :
      lbitCoefficientL1Distance K J ≤ N * δ := by
    unfold lbitCoefficientL1Distance
    calc
      (∑ S : Finset I, |K S - J S|) ≤
          Fintype.card (Finset I) • δ :=
        Finset.sum_le_card_nsmul Finset.univ
          (fun S : Finset I => |K S - J S|) δ
          (fun S hS => (hKclose S).le)
      _ = N * δ := by
        simp [N, nsmul_eq_mul, mul_comm]
  have hNδ : N * δ < ε := by
    dsimp [N, δ]
    let M : ℝ := ((2 ^ Fintype.card I : ℕ) : ℝ)
    change M * (ε / (M + 1)) < ε
    have hden : 0 < M + 1 := by
      dsimp [M]
      positivity
    have hratio :
        M / (M + 1) < 1 :=
      (div_lt_one hden).2 (by norm_num)
    calc
      M * (ε / (M + 1)) =
          ε * (M / (M + 1)) := by ring
      _ < ε * 1 := mul_lt_mul_of_pos_left hratio hε
      _ = ε := mul_one ε
  have hL1 : lbitCoefficientL1Distance K J < ε :=
    lt_of_le_of_lt hL1le hNδ
  refine ⟨K, hKempty, hL1, ?_, hKrank⟩
  intro x
  exact lt_of_le_of_lt (lbitEnergy_sub_abs_le K J x) hL1

/-- Matrix Hamiltonian of the l-bit energy in its fixed Boolean configuration basis. -/
def lbitHamiltonianMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    Matrix (I → Bool) (I → Bool) ℝ :=
  Matrix.diagonal (lbitEnergy J)

/-- The diagonal conserved charge carried by one l-bit. -/
def lbitChargeMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    (i : I) :
    Matrix (I → Bool) (I → Bool) ℝ :=
  Matrix.diagonal (fun x => (lbitSign (x i) : ℝ))

/-- Every l-bit charge remains exactly conserved for every interaction order and every coefficient
family. -/
theorem lbitChargeMatrix_commutes
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (i : I) :
    lbitChargeMatrix i * lbitHamiltonianMatrix J =
      lbitHamiltonianMatrix J * lbitChargeMatrix i := by
  simp [lbitChargeMatrix, lbitHamiltonianMatrix,
    Matrix.diagonal_mul_diagonal, mul_comm]

/-- The interacting l-bit Hamiltonian has no transport between distinct configurations. -/
theorem lbitHamiltonianMatrix_offDiagonal
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) {x y : I → Bool} (hxy : x ≠ y) :
    lbitHamiltonianMatrix J x y = 0 := by
  simp [lbitHamiltonianMatrix, Matrix.diagonal, hxy]

/-- **Localization--temporal-dimension separation law.** A finite-order l-bit Hamiltonian has the
coefficient-count temporal ceiling, yet in every positive coefficient `L¹` neighborhood there is a
Hamiltonian with full exponential temporal dimension. Both Hamiltonians are diagonal in the same
configuration basis, and every l-bit charge stays exactly conserved. -/
theorem exists_localizedTemporalDimensionExplosion
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (k : ℕ)
    (hJ : ∀ S, k < S.card → J S = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Finset I → ℝ,
      lbitTemporalRank J ≤
        (∑ j ∈ Finset.range (k + 1),
          Nat.choose (Fintype.card I) j) - 1 ∧
      lbitTemporalRank K = 2 ^ Fintype.card I - 1 ∧
      lbitCoefficientL1Distance K J < ε ∧
      (∀ x, |lbitEnergy K x - lbitEnergy J x| < ε) ∧
      (∀ i,
        lbitChargeMatrix i * lbitHamiltonianMatrix K =
          lbitHamiltonianMatrix K * lbitChargeMatrix i) ∧
      (∀ {x y : I → Bool}, x ≠ y →
        lbitHamiltonianMatrix K x y = 0) := by
  obtain ⟨K, hKempty, hKdistance, hKenergy, hKrank⟩ :=
    exists_lbitEnergy_maximal_uniformly_close J ε hε
  exact
    ⟨K, lbitTemporalRank_le_order J k hJ, hKrank,
      hKdistance, hKenergy, fun i => lbitChargeMatrix_commutes K i,
      fun hxy => lbitHamiltonianMatrix_offDiagonal K hxy⟩

/-- A finite set of `n` l-bits has exactly `2^n - 1` nonconstant Walsh interaction sectors. -/
theorem card_nonemptyLBitSupports
    {I : Type*} [Fintype I] [DecidableEq I] :
    Fintype.card {S : Finset I // S.Nonempty} =
      2 ^ Fintype.card I - 1 := by
  classical
  simp [Finset.nonempty_iff_ne_empty]

/-- Mixed supports across two l-bit blocks are exactly pairs of nonempty supports, one from each
block. -/
def mixedLBitSupportEquiv
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    {S : Finset (A ⊕ B) //
      S.toLeft.Nonempty ∧ S.toRight.Nonempty} ≃
      {S : Finset A // S.Nonempty} ×
        {S : Finset B // S.Nonempty} where
  toFun := fun S =>
    (⟨S.1.toLeft, S.2.1⟩, ⟨S.1.toRight, S.2.2⟩)
  invFun := fun S =>
    ⟨S.1.1.disjSum S.2.1, by simp [S.1.2, S.2.2]⟩
  left_inv := by
    intro S
    apply Subtype.ext
    exact Finset.toLeft_disjSum_toRight
  right_inv := by
    intro S
    apply Prod.ext <;> apply Subtype.ext <;> simp

/-- The mixed l-bit sector has exactly the same multiplicative cardinality as the bipartite
rectangle-relation sector. -/
theorem card_mixedLBitSupports
    (A B : Type*) [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] :
    Fintype.card
        {S : Finset (A ⊕ B) //
          S.toLeft.Nonempty ∧ S.toRight.Nonempty} =
      (2 ^ Fintype.card A - 1) *
        (2 ^ Fintype.card B - 1) := by
  rw [Fintype.card_congr (mixedLBitSupportEquiv A B),
    Fintype.card_prod]
  simp [Finset.nonempty_iff_ne_empty]

/-- A fixed injection assigning a distinct prime to every nonempty finite support on a countable
lattice. -/
noncomputable def nonemptyFiniteSupportPrimeEmbedding :
    {S : Finset ℕ // S.Nonempty} ↪ Nat.Primes := by
  let h :=
    Countable.exists_injective_nat {S : Finset ℕ // S.Nonempty}
  let f := Classical.choose h
  have hf : Function.Injective f := Classical.choose_spec h
  exact (⟨f, hf⟩ : {S : Finset ℕ // S.Nonempty} ↪ ℕ).trans
    (Infinite.natEmbedding Nat.Primes)

/-- One coefficient assignment on all finite supports of a countably infinite lattice. -/
noncomputable def universalLBitCoefficient
    (S : Finset ℕ) : ℝ :=
  if hS : S.Nonempty then
    primeLogSupport
      (nonemptyFiniteSupportPrimeEmbedding ⟨S, hS⟩)
  else 0

/-- All nonconstant coefficients of the countable assignment are rationally independent. -/
theorem universalLBitCoefficient_linearIndependent :
    LinearIndependent ℚ
      (fun S : {S : Finset ℕ // S.Nonempty} =>
        universalLBitCoefficient S.1) := by
  have hcomp :
      LinearIndependent ℚ
        (fun S : {S : Finset ℕ // S.Nonempty} =>
          primeLogSupport (nonemptyFiniteSupportPrimeEmbedding S)) :=
    primeLogSupport_linearIndependent.comp
      nonemptyFiniteSupportPrimeEmbedding
      nonemptyFiniteSupportPrimeEmbedding.injective
  have heq :
      (fun S : {S : Finset ℕ // S.Nonempty} =>
        universalLBitCoefficient S.1) =
      (fun S : {S : Finset ℕ // S.Nonempty} =>
        primeLogSupport (nonemptyFiniteSupportPrimeEmbedding S)) := by
    funext S
    simp [universalLBitCoefficient, S.2]
  rw [heq]
  exact hcomp

/-- Canonical embedding of an arbitrary finite site type into the countable lattice. -/
noncomputable def finiteTypeNatEmbedding
    (I : Type*) [Fintype I] : I ↪ ℕ :=
  (Fintype.equivFin I).toEmbedding.trans Fin.valEmbedding

/-- Map a nonempty finite local support injectively into a nonempty lattice support. -/
def mapNonemptyLBitSupport
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I ↪ ℕ) :
    {S : Finset I // S.Nonempty} →
      {S : Finset ℕ // S.Nonempty} :=
  fun S => ⟨S.1.map e, S.2.map⟩

/-- Mapping supports along a site embedding is injective. -/
theorem mapNonemptyLBitSupport_injective
    {I : Type*} [Fintype I] [DecidableEq I]
    (e : I ↪ ℕ) :
    Function.Injective (mapNonemptyLBitSupport e) := by
  intro S T hST
  apply Subtype.ext
  exact Finset.map_injective e (congrArg Subtype.val hST)

/-- Restriction of the single countable coefficient assignment to any finite site type. -/
noncomputable def universalLBitFiniteRestriction
    (I : Type*) [Fintype I] [DecidableEq I]
    (S : Finset I) : ℝ :=
  universalLBitCoefficient
    (S.map (finiteTypeNatEmbedding I))

/-- Every finite restriction of the one countable assignment retains coefficient independence. -/
theorem universalLBitFiniteRestriction_linearIndependent
    (I : Type*) [Fintype I] [DecidableEq I] :
    LinearIndependent ℚ
      (fun S : {S : Finset I // S.Nonempty} =>
        universalLBitFiniteRestriction I S.1) := by
  let e := finiteTypeNatEmbedding I
  have hcomp :=
    universalLBitCoefficient_linearIndependent.comp
      (mapNonemptyLBitSupport e)
      (mapNonemptyLBitSupport_injective e)
  have heq :
      (fun S : {S : Finset I // S.Nonempty} =>
        universalLBitFiniteRestriction I S.1) =
      (fun S : {S : Finset I // S.Nonempty} =>
        universalLBitCoefficient
          (mapNonemptyLBitSupport e S).1) := by
    funext S
    rfl
  rw [heq]
  exact hcomp

/-- **Simultaneous infinite-window law.** One coefficient assignment on countably many sites has
full temporal dimension `2^|I| - 1` on every finite restriction, so its finite-window dimensions
are unbounded while all finite-window l-bit charges remain conserved. -/
theorem universalLBitFiniteRestriction_fullRank
    (I : Type*) [Fintype I] [DecidableEq I] :
    lbitTemporalRank (universalLBitFiniteRestriction I) =
      2 ^ Fintype.card I - 1 :=
  lbitTemporalRank_eq_card _
    (universalLBitFiniteRestriction_linearIndependent I)

end
end GaloisForLFunctions.HTGeometry
