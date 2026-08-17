import GaloisForLFunctions.HTGeometry.InverseSquareTailWitness
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry.StaticLocalScratch

abbrev Config (Q : Type*) := Q → Bool
abbrev On {Q : Type*} (A : Finset Q) := A → Bool
abbrev Off {Q : Type*} (A : Finset Q) := {q : Q // q ∉ A} → Bool

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

def splitConfig (A : Finset Q) : Config Q ≃ On A × Off A where
  toFun x := (fun q => x q.1, fun q => x q.1)
  invFun p q := if h : q ∈ A then p.1 ⟨q, h⟩ else p.2 ⟨q, h⟩
  left_inv x := by
    funext q
    simp
  right_inv p := by
    rcases p with ⟨a, b⟩
    apply Prod.ext
    · funext q
      simp
    · funext q
      simp [q.property]

@[simp] theorem splitConfig_fst_apply (A : Finset Q) (x : Config Q) (q : A) :
    (splitConfig A x).1 q = x q := rfl

@[simp] theorem splitConfig_snd_apply (A : Finset Q) (x : Config Q)
    (q : {q : Q // q ∉ A}) : (splitConfig A x).2 q = x q := rfl

def SeparatesAcross (A : Finset Q) (M : Matrix (Config Q) (Config Q) ℂ) : Prop :=
  ∃ MA : Matrix (On A) (On A) ℂ, ∃ MB : Matrix (Off A) (Off A) ℂ,
    ∀ x y, M x y = MA (splitConfig A x).1 (splitConfig A y).1 *
      MB (splitConfig A x).2 (splitConfig A y).2

theorem SeparatesAcross.exists_apply {A : Finset Q} {M : Matrix (Config Q) (Config Q) ℂ}
    (h : SeparatesAcross A M) :
    ∃ MA : Matrix (On A) (On A) ℂ, ∃ MB : Matrix (Off A) (Off A) ℂ,
      ∀ x y, M x y = MA (splitConfig A x).1 (splitConfig A y).1 *
        MB (splitConfig A x).2 (splitConfig A y).2 := h

theorem SeparatesAcross.one (A : Finset Q) :
    SeparatesAcross A (1 : Matrix (Config Q) (Config Q) ℂ) := by
  refine ⟨1, 1, fun x y => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp
  · simp only [one_apply, hxy, ↓reduceIte, mul_boole]
    by_cases hfst : (splitConfig A x).1 = (splitConfig A y).1
    · have hsnd : (splitConfig A x).2 ≠ (splitConfig A y).2 := by
        intro hsnd
        apply hxy
        exact (splitConfig A).injective (Prod.ext hfst hsnd)
      simp [hfst, hsnd]
    · simp [hfst]

#check Fintype.sum_prod_type
#check Finset.sum_mul_sum

theorem SeparatesAcross.mul {A : Finset Q} {M N : Matrix (Config Q) (Config Q) ℂ}
    (hM : SeparatesAcross A M) (hN : SeparatesAcross A N) :
    SeparatesAcross A (M * N) := by
  rcases hM with ⟨MA, MB, hM⟩
  rcases hN with ⟨NA, NB, hN⟩
  refine ⟨MA * NA, MB * NB, fun x y => ?_⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply]
  calc
    ∑ z : Config Q, M x z * N z y =
        ∑ p : On A × Off A,
          (MA (splitConfig A x).1 p.1 * MB (splitConfig A x).2 p.2) *
            (NA p.1 (splitConfig A y).1 * NB p.2 (splitConfig A y).2) := by
      apply Fintype.sum_equiv (splitConfig A)
      intro z
      rw [hM, hN]
    _ = ∑ a : On A, ∑ b : Off A,
          (MA (splitConfig A x).1 a * NA a (splitConfig A y).1) *
            (MB (splitConfig A x).2 b * NB b (splitConfig A y).2) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = (∑ a : On A, MA (splitConfig A x).1 a * NA a (splitConfig A y).1) *
          (∑ b : Off A, MB (splitConfig A x).2 b * NB b (splitConfig A y).2) := by
      rw [Finset.sum_mul_sum]

structure LocalGate (Q : Type*) [Fintype Q] [DecidableEq Q] where
  support : Finset Q
  matrix : Matrix (Config Q) (Config Q) ℂ
  arity_le_two : support.card ≤ 2
  unitary : matrix ∈ Matrix.unitaryGroup (Config Q) ℂ
  separates : ∀ A : Finset Q, support ⊆ A ∨ Disjoint support A →
    SeparatesAcross A matrix

def circuitMatrix : List (LocalGate Q) → Matrix (Config Q) (Config Q) ℂ
  | [] => 1
  | g :: c => g.matrix * circuitMatrix c

theorem circuitMatrix_unitary (c : List (LocalGate Q)) :
    circuitMatrix c ∈ Matrix.unitaryGroup (Config Q) ℂ := by
  induction c with
  | nil => exact one_mem _
  | cons g c ih =>
      exact (Matrix.unitaryGroup (Config Q) ℂ).mul_mem g.unitary ih

theorem finset_subset_or_disjoint_of_card_le_one {S A : Finset Q} (hS : S.card ≤ 1) :
    S ⊆ A ∨ Disjoint S A := by
  by_cases h : ∃ q ∈ S, q ∈ A
  · rcases h with ⟨q, hqS, hqA⟩
    left
    intro r hrS
    have hcard : ({q, r} : Finset Q).card ≤ 1 := by
      refine le_trans (Finset.card_le_card ?_) hS
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hqS, hrS⟩
    have : q = r := by
      by_contra hqr
      simp [Finset.card_pair hqr] at hcard
    simpa [← this]
  · right
    rw [Finset.disjoint_left]
    intro q hqS hqA
    exact h ⟨q, hqS, hqA⟩

theorem circuitMatrix_separatesAcross (c : List (LocalGate Q)) (A : Finset Q)
    (havoid : ∀ g ∈ c, g.support.card = 2 → Disjoint g.support A) :
    SeparatesAcross A (circuitMatrix c) := by
  induction c with
  | nil => exact SeparatesAcross.one A
  | cons g c ih =>
      apply SeparatesAcross.mul
      · apply g.separates A
        by_cases htwo : g.support.card = 2
        · exact Or.inr (havoid g (by simp) htwo)
        · have harity := g.arity_le_two
          have hle : g.support.card ≤ 1 := by omega
          exact finset_subset_or_disjoint_of_card_le_one hle
      · apply ih
        intro h hh hc
        exact havoid h (by simp [hh]) hc

abbrev PairQubit (L : ℕ) := Fin L × Bool

def twoGateCount {L : ℕ} : List (LocalGate (PairQubit L)) → ℕ
  | [] => 0
  | g :: c => (if g.support.card = 2 then 1 else 0) + twoGateCount c

def gateTouchedPairs {L : ℕ} (g : LocalGate (PairQubit L)) : Finset (Fin L) :=
  if g.support.card = 2 then g.support.image Prod.fst else ∅

def circuitTouchedPairs {L : ℕ} : List (LocalGate (PairQubit L)) → Finset (Fin L)
  | [] => ∅
  | g :: c => gateTouchedPairs g ∪ circuitTouchedPairs c

theorem gateTouchedPairs_card_le_two {L : ℕ} (g : LocalGate (PairQubit L)) :
    (gateTouchedPairs g).card ≤ 2 := by
  unfold gateTouchedPairs
  split_ifs with h
  · exact le_trans (Finset.card_image_le) g.arity_le_two
  · simp

theorem circuitTouchedPairs_card_le {L : ℕ} (c : List (LocalGate (PairQubit L))) :
    (circuitTouchedPairs c).card ≤ 2 * twoGateCount c := by
  induction c with
  | nil => simp [circuitTouchedPairs, twoGateCount]
  | cons g c ih =>
      rw [circuitTouchedPairs, twoGateCount]
      refine le_trans (Finset.card_union_le _ _) ?_
      unfold gateTouchedPairs
      by_cases htwo : g.support.card = 2
      · simp only [htwo, ↓reduceIte]
        have hg : (g.support.image Prod.fst).card ≤ 2 :=
          le_trans Finset.card_image_le g.arity_le_two
        omega
      · simp [htwo, ih]

theorem gateTouchedPairs_subset_circuitTouchedPairs {L : ℕ}
    {g : LocalGate (PairQubit L)} {c : List (LocalGate (PairQubit L))} (hg : g ∈ c) :
    gateTouchedPairs g ⊆ circuitTouchedPairs c := by
  induction c with
  | nil => simp at hg
  | cons h c ih =>
      simp only [List.mem_cons] at hg
      rw [circuitTouchedPairs]
      rcases hg with rfl | hg
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih hg) Finset.subset_union_right

def firstEndpointSites {L : ℕ} (S : Finset (Fin L)) : Finset (PairQubit L) :=
  S ×ˢ {false}

@[simp] theorem mem_firstEndpointSites {L : ℕ} {S : Finset (Fin L)} {q : PairQubit L} :
    q ∈ firstEndpointSites S ↔ q.1 ∈ S ∧ q.2 = false := by
  rcases q with ⟨j, b⟩
  simp [firstEndpointSites, Prod.ext_iff]

theorem twoGateSupport_disjoint_firstEndpoints_of_untouched {L : ℕ}
    {c : List (LocalGate (PairQubit L))} {S : Finset (Fin L)}
    (hdisj : Disjoint S (circuitTouchedPairs c)) {g : LocalGate (PairQubit L)}
    (hg : g ∈ c) (htwo : g.support.card = 2) :
    Disjoint g.support (firstEndpointSites S) := by
  rw [Finset.disjoint_left]
  intro q hqg hqS
  have hpairS : q.1 ∈ S := (mem_firstEndpointSites.mp hqS).1
  have hpairGate : q.1 ∈ gateTouchedPairs g := by
    rw [gateTouchedPairs, if_pos htwo]
    exact Finset.mem_image.mpr ⟨q, hqg, rfl⟩
  have hpairCircuit : q.1 ∈ circuitTouchedPairs c :=
    gateTouchedPairs_subset_circuitTouchedPairs hg hpairGate
  exact (Finset.disjoint_left.mp hdisj) hpairS hpairCircuit

theorem circuitMatrix_separates_firstEndpoints {L : ℕ}
    (c : List (LocalGate (PairQubit L))) (S : Finset (Fin L))
    (hdisj : Disjoint S (circuitTouchedPairs c)) :
    SeparatesAcross (firstEndpointSites S) (circuitMatrix c) := by
  apply circuitMatrix_separatesAcross
  intro g hg htwo
  exact twoGateSupport_disjoint_firstEndpoints_of_untouched hdisj hg htwo

def pairFourConfig {L : ℕ} (S : Finset (Fin L)) (a b : Bool) : Config (PairQubit L) :=
  fun q => if q.1 ∈ S then if q.2 = false then a else b else false

theorem pairFourConfig_on_eq {L : ℕ} (S : Finset (Fin L)) (a b b' : Bool) :
    (splitConfig (firstEndpointSites S) (pairFourConfig S a b)).1 =
      (splitConfig (firstEndpointSites S) (pairFourConfig S a b')).1 := by
  funext q
  have hmem := mem_firstEndpointSites.mp q.property
  simp [pairFourConfig, hmem.1, hmem.2]

theorem pairFourConfig_off_eq {L : ℕ} (S : Finset (Fin L)) (a a' b : Bool) :
    (splitConfig (firstEndpointSites S) (pairFourConfig S a b)).2 =
      (splitConfig (firstEndpointSites S) (pairFourConfig S a' b)).2 := by
  funext q
  have hnot : ¬(q.1.1 ∈ S ∧ q.1.2 = false) := by
    simpa using q.property
  by_cases hS : q.1.1 ∈ S
  · have hbool : q.1.2 = true := by
      cases hq : q.1.2
      · exact False.elim (hnot ⟨hS, hq⟩)
      · rfl
    simp [pairFourConfig, hS, hbool]
  · simp [pairFourConfig, hS]

theorem SeparatesAcross.fourPoint_diagonal {L : ℕ} {S : Finset (Fin L)}
    {W : Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ}
    (hW : SeparatesAcross (firstEndpointSites S) W) :
    W (pairFourConfig S false false) (pairFourConfig S false false) *
        W (pairFourConfig S true true) (pairFourConfig S true true) =
      W (pairFourConfig S false true) (pairFourConfig S false true) *
        W (pairFourConfig S true false) (pairFourConfig S true false) := by
  rcases hW with ⟨WA, WB, hW⟩
  rw [hW, hW, hW, hW]
  rw [pairFourConfig_on_eq S false false true,
    pairFourConfig_on_eq S true true false,
    pairFourConfig_off_eq S false true false,
    pairFourConfig_off_eq S false true true]
  ring

theorem separatesAcross_diagonal_fst (A : Finset Q) (f : On A → ℂ) :
    SeparatesAcross A (Matrix.diagonal fun x : Config Q => f (splitConfig A x).1) := by
  refine ⟨Matrix.diagonal f, 1, fun x y => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp
  · have hsplit : (splitConfig A x).1 ≠ (splitConfig A y).1 ∨
        (splitConfig A x).2 ≠ (splitConfig A y).2 := by
      by_contra h
      push_neg at h
      exact hxy ((splitConfig A).injective (Prod.ext h.1 h.2))
    rcases hsplit with hfst | hsnd
    · simp [Matrix.diagonal, hxy, hfst]
    · simp [Matrix.diagonal, hxy, hsnd]

theorem separatesAcross_diagonal_snd (A : Finset Q) (f : Off A → ℂ) :
    SeparatesAcross A (Matrix.diagonal fun x : Config Q => f (splitConfig A x).2) := by
  refine ⟨1, Matrix.diagonal f, fun x y => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp
  · have hsplit : (splitConfig A x).1 ≠ (splitConfig A y).1 ∨
        (splitConfig A x).2 ≠ (splitConfig A y).2 := by
      by_contra h
      push_neg at h
      exact hxy ((splitConfig A).injective (Prod.ext h.1 h.2))
    rcases hsplit with hfst | hsnd
    · simp [Matrix.diagonal, hxy, hfst]
    · simp [Matrix.diagonal, hxy, hsnd]

theorem exists_subset_sum_between {α : Type*} [DecidableEq α]
    (T : Finset α) (w : α → ℝ) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hw : ∀ j ∈ T, w j ≤ δ) (htotal : a ≤ ∑ j ∈ T, w j) :
    ∃ S ⊆ T, a ≤ ∑ j ∈ S, w j ∧ ∑ j ∈ S, w j ≤ a + δ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty] at htotal
      refine ⟨∅, Finset.Subset.rfl, by simpa using htotal, ?_⟩
      simp
      linarith
  | @insert q T hq ih =>
      by_cases hT : a ≤ ∑ j ∈ T, w j
      · rcases ih (fun j hj => hw j (Finset.mem_insert_of_mem hj)) hT with
          ⟨S, hST, hlo, hhi⟩
        exact ⟨S, (fun _ hx => Finset.mem_insert_of_mem (hST hx)), hlo, hhi⟩
      · refine ⟨insert q T, Finset.Subset.rfl, ?_, ?_⟩
        · exact htotal
        · rw [Finset.sum_insert hq]
          have hqle := hw q (by simp)
          linarith

def inverseSquareBlockEmbedding {L K : ℕ} (hKL : 8 * K ≤ L) : Fin (4 * K) → Fin L :=
  fun i => ⟨4 * K + i.val, by omega⟩

theorem inverseSquareBlockEmbedding_injective {L K : ℕ} (hKL : 8 * K ≤ L) :
    Function.Injective (inverseSquareBlockEmbedding hKL) := by
  intro i j hij
  apply Fin.ext
  exact Nat.add_left_cancel (congrArg Fin.val hij)

def inverseSquareBlock {L K : ℕ} (hKL : 8 * K ≤ L) : Finset (Fin L) :=
  Finset.univ.image (inverseSquareBlockEmbedding hKL)

theorem inverseSquareBlock_card {L K : ℕ} (hKL : 8 * K ≤ L) :
    (inverseSquareBlock hKL).card = 4 * K := by
  rw [inverseSquareBlock, Finset.card_image_iff.mpr]
  · simp
  · exact (inverseSquareBlockEmbedding_injective hKL).injOn

theorem inverseSquareBlock_index_bounds {L K : ℕ} (hKL : 8 * K ≤ L)
    {j : Fin L} (hj : j ∈ inverseSquareBlock hKL) :
    4 * K < j.val + 1 ∧ j.val + 1 ≤ 8 * K := by
  rw [inverseSquareBlock, Finset.mem_image] at hj
  rcases hj with ⟨i, -, rfl⟩
  change 4 * K < (4 * K + i.val) + 1 ∧ (4 * K + i.val) + 1 ≤ 8 * K
  constructor <;> omega

noncomputable def inverseSquarePhaseWeight {L : ℕ} (t : ℝ) (j : Fin L) : ℝ :=
  t / ((j.val + 1 : ℕ) : ℝ) ^ 2

theorem inverseSquarePhaseWeight_nonneg {L : ℕ} {t : ℝ} (ht : 0 ≤ t) (j : Fin L) :
    0 ≤ inverseSquarePhaseWeight t j := by
  unfold inverseSquarePhaseWeight
  positivity

theorem inverseSquarePhaseWeight_le {L K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε) (ht : t < 128 * Real.pi * ε * (K + 1))
    (hKL : 8 * K ≤ L) {j : Fin L} (hj : j ∈ inverseSquareBlock hKL) :
    inverseSquarePhaseWeight t j ≤ 2 * Real.pi * ε := by
  have hb := inverseSquareBlock_index_bounds hKL hj
  have hKposN : 0 < K := by omega
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hKposN
  have hjpos : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by positivity
  have hjlo : (4 * (K : ℝ)) < ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast hb.1
  have hp : 0 < Real.pi * ε := mul_pos Real.pi_pos hε
  have hquad : 4 * ((K : ℝ) + 1) ≤ (K : ℝ) ^ 2 := by
    have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hscale : 128 * (Real.pi * ε) * ((K : ℝ) + 1) ≤
      2 * (Real.pi * ε) * (4 * (K : ℝ)) ^ 2 := by
    have hprod := mul_nonneg (le_of_lt hp) (sub_nonneg.mpr hquad)
    nlinarith
  have hsq : (4 * (K : ℝ)) ^ 2 ≤ (((j.val + 1 : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  have htarget : t ≤ 2 * Real.pi * ε * (((j.val + 1 : ℕ) : ℝ)) ^ 2 := by
    have ht' : t < 128 * (Real.pi * ε) * ((K : ℝ) + 1) := by
      norm_num at ht ⊢
      simpa [mul_assoc] using ht
    have hmono : 2 * (Real.pi * ε) * (4 * (K : ℝ)) ^ 2 ≤
        2 * (Real.pi * ε) * (((j.val + 1 : ℕ) : ℝ)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  unfold inverseSquarePhaseWeight
  rw [div_le_iff₀ (sq_pos_of_pos hjpos)]
  simpa [mul_assoc] using htarget

theorem inverseSquarePhaseWeight_lower {L K : ℕ} {t : ℝ}
    (hK : 0 < K) (ht : 0 ≤ t) (hKL : 8 * K ≤ L)
    {j : Fin L} (hj : j ∈ inverseSquareBlock hKL) :
    t / (64 * (K : ℝ) ^ 2) ≤ inverseSquarePhaseWeight t j := by
  have hb := inverseSquareBlock_index_bounds hKL hj
  have hjpos : (0 : ℝ) < ((j.val + 1 : ℕ) : ℝ) := by positivity
  have hkpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hjhi : ((j.val + 1 : ℕ) : ℝ) ≤ 8 * (K : ℝ) := by exact_mod_cast hb.2
  have hsq : (((j.val + 1 : ℕ) : ℝ)) ^ 2 ≤ 64 * (K : ℝ) ^ 2 := by nlinarith
  unfold inverseSquarePhaseWeight
  rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hjpos)]
  nlinarith

theorem circuit_exists_inverseSquare_phase_subset {L K : ℕ}
    (c : List (LocalGate (PairQubit L))) {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (hε : 0 < ε)
    (htlo : 128 * Real.pi * ε * K ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (hcost : twoGateCount c < K) :
    ∃ S : Finset (Fin L), S ⊆ inverseSquareBlock hKL ∧
      Disjoint S (circuitTouchedPairs c) ∧
      3 * Real.pi * ε ≤ ∑ j ∈ S, inverseSquarePhaseWeight t j ∧
      ∑ j ∈ S, inverseSquarePhaseWeight t j ≤ 5 * Real.pi * ε := by
  let B := inverseSquareBlock hKL
  let T := B \ circuitTouchedPairs c
  have htouch : (circuitTouchedPairs c).card < 2 * K := by
    have hc := circuitTouchedPairs_card_le c
    omega
  have hTcard : 2 * K < T.card := by
    have hblock : B.card = 4 * K := inverseSquareBlock_card hKL
    have hcard := Finset.card_le_card_sdiff_add_card (s := B)
      (t := circuitTouchedPairs c)
    change B.card ≤ T.card + (circuitTouchedPairs c).card at hcard
    omega
  have htpos : 0 < t := by
    have hp : 0 < 128 * Real.pi * ε * (K : ℝ) := by positivity
    exact lt_of_lt_of_le hp htlo
  have htotal : 4 * Real.pi * ε < ∑ j ∈ T, inverseSquarePhaseWeight t j := by
    have hKposN : 0 < K := by omega
    have hbasepos : 0 < t / (64 * (K : ℝ) ^ 2) := div_pos htpos (by positivity)
    have hsum : (T.card : ℝ) * (t / (64 * (K : ℝ) ^ 2)) ≤
        ∑ j ∈ T, inverseSquarePhaseWeight t j := by
      calc
        (T.card : ℝ) * (t / (64 * (K : ℝ) ^ 2)) =
            ∑ _j ∈ T, t / (64 * (K : ℝ) ^ 2) := by simp
        _ ≤ ∑ j ∈ T, inverseSquarePhaseWeight t j := by
          apply Finset.sum_le_sum
          intro j hj
          apply inverseSquarePhaseWeight_lower hKposN (le_of_lt htpos) hKL
          exact (Finset.mem_sdiff.mp hj).1
    have hcardR : (2 * K : ℝ) < T.card := by exact_mod_cast hTcard
    have hstrict : (2 * K : ℝ) * (t / (64 * (K : ℝ) ^ 2)) <
        (T.card : ℝ) * (t / (64 * (K : ℝ) ^ 2)) :=
      mul_lt_mul_of_pos_right hcardR hbasepos
    have hratio : 4 * Real.pi * ε ≤ t / (32 * (K : ℝ)) := by
      rw [le_div_iff₀ (by positivity)]
      have hreassoc : 4 * Real.pi * ε * (32 * (K : ℝ)) =
          128 * Real.pi * ε * (K : ℝ) := by ring
      rw [hreassoc]
      exact htlo
    have heq : (2 * K : ℝ) * (t / (64 * (K : ℝ) ^ 2)) =
        t / (32 * (K : ℝ)) := by
      field_simp
      ring
    linarith
  have hw : ∀ j ∈ T, inverseSquarePhaseWeight t j ≤ 2 * Real.pi * ε := by
    intro j hj
    apply inverseSquarePhaseWeight_le hK hε hthi hKL
    exact (Finset.mem_sdiff.mp hj).1
  have haTotal : 3 * Real.pi * ε ≤ ∑ j ∈ T, inverseSquarePhaseWeight t j := by
    have hp := Real.pi_pos
    linarith
  rcases exists_subset_sum_between T (inverseSquarePhaseWeight t)
      (a := 3 * Real.pi * ε) (δ := 2 * Real.pi * ε)
      (by positivity) (by positivity) hw haTotal with
    ⟨S, hST, hlo, hhi⟩
  refine ⟨S, ?_, ?_, hlo, ?_⟩
  · intro j hj
    exact (Finset.mem_sdiff.mp (hST hj)).1
  · rw [Finset.disjoint_left]
    intro j hjS hjTouched
    exact (Finset.mem_sdiff.mp (hST hjS)).2 hjTouched
  · nlinarith

noncomputable def inverseSquareMatchingEnergy {L : ℕ} (x : Config (PairQubit L)) : ℝ :=
  ∑ j : Fin L, if x (j, false) = true ∧ x (j, true) = true
    then 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) else 0

noncomputable def inverseCubeBridgeEnergy {L : ℕ} (x : Config (PairQubit L)) : ℝ :=
  (1 / (L : ℝ) ^ 3) *
    ∑ j : Fin L, if h : j.val + 1 < L then
      if x (j, true) = true ∧ x (⟨j.val + 1, h⟩, false) = true then 1 else 0
    else 0

noncomputable def inverseSquareChainEnergy {L : ℕ} (x : Config (PairQubit L)) : ℝ :=
  inverseSquareMatchingEnergy x + inverseCubeBridgeEnergy x

noncomputable def inverseSquareChainHamiltonian (L : ℕ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  Matrix.diagonal (fun x => (inverseSquareChainEnergy x : ℂ))

noncomputable def inverseSquareChainEvolution (L : ℕ) (t : ℝ) :
    Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ :=
  unitaryEvolution (inverseSquareChainHamiltonian L) t

theorem inverseSquareChainEvolution_diagonal (L : ℕ) (t : ℝ) :
    inverseSquareChainEvolution L t =
      Matrix.diagonal (fun x => Complex.exp (-(Complex.I * (t * inverseSquareChainEnergy x)))) := by
  exact unitaryEvolution_diagonal _ _

theorem mem_unitaryGroup_diagonal_general {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℂ) (hw : ∀ i, ‖w i‖ = 1) :
    Matrix.diagonal w ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  have hsq : Complex.normSq (w i) = 1 := by
    have h1 := hw i
    have h2 : ‖w i‖ ^ 2 = 1 := by rw [h1]; norm_num
    rw [← Complex.normSq_eq_norm_sq] at h2
    exact h2
  have hmul : (w i) * (starRingEnd ℂ) (w i) = 1 := by
    rw [Complex.mul_conj, hsq]
    norm_num
  simpa [Pi.star_apply] using hmul

theorem inverseSquareChainEvolution_unitary (L : ℕ) (t : ℝ) :
    inverseSquareChainEvolution L t ∈
      Matrix.unitaryGroup (Config (PairQubit L)) ℂ := by
  rw [inverseSquareChainEvolution_diagonal]
  apply mem_unitaryGroup_diagonal_general
  intro x
  rw [Complex.norm_exp]
  simp

theorem inverseCubeBridgeEnergy_nonneg {L : ℕ} (x : Config (PairQubit L)) :
    0 ≤ inverseCubeBridgeEnergy x := by
  unfold inverseCubeBridgeEnergy
  apply mul_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro j hj
    split_ifs <;> norm_num

theorem inverseCubeBridgeEnergy_le {L : ℕ} (hL : 0 < L) (x : Config (PairQubit L)) :
    inverseCubeBridgeEnergy x ≤ 1 / (L : ℝ) ^ 2 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hsum :
      (∑ j : Fin L, if h : j.val + 1 < L then
        if x (j, true) = true ∧ x (⟨j.val + 1, h⟩, false) = true then (1 : ℝ) else 0
      else 0) ≤ L := by
    calc
      _ ≤ ∑ _j : Fin L, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        split_ifs <;> norm_num
      _ = L := by simp
  unfold inverseCubeBridgeEnergy
  have hcoef : 0 ≤ 1 / (L : ℝ) ^ 3 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsum hcoef
  have heq : (1 / (L : ℝ) ^ 3) * (L : ℝ) = 1 / (L : ℝ) ^ 2 := by
    field_simp
  rwa [heq] at hmul

theorem inverseSquareMatchingEnergy_pairFourConfig_false_left {L : ℕ}
    (S : Finset (Fin L)) (b : Bool) :
    inverseSquareMatchingEnergy (pairFourConfig S false b) = 0 := by
  simp [inverseSquareMatchingEnergy, pairFourConfig]

theorem inverseSquareMatchingEnergy_pairFourConfig_false_right {L : ℕ}
    (S : Finset (Fin L)) (a : Bool) :
    inverseSquareMatchingEnergy (pairFourConfig S a false) = 0 := by
  simp [inverseSquareMatchingEnergy, pairFourConfig]

theorem inverseSquareMatchingEnergy_pairFourConfig_true {L : ℕ}
    (S : Finset (Fin L)) :
    inverseSquareMatchingEnergy (pairFourConfig S true true) =
      ∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2) := by
  simp [inverseSquareMatchingEnergy, pairFourConfig]

theorem inverseCubeBridgeEnergy_pairFourConfig_false_left {L : ℕ}
    (S : Finset (Fin L)) (b : Bool) :
    inverseCubeBridgeEnergy (pairFourConfig S false b) = 0 := by
  simp [inverseCubeBridgeEnergy, pairFourConfig]

theorem inverseCubeBridgeEnergy_pairFourConfig_false_right {L : ℕ}
    (S : Finset (Fin L)) (a : Bool) :
    inverseCubeBridgeEnergy (pairFourConfig S a false) = 0 := by
  simp [inverseCubeBridgeEnergy, pairFourConfig]

theorem inverseSquareChainEnergy_pairFourConfig_false_left {L : ℕ}
    (S : Finset (Fin L)) (b : Bool) :
    inverseSquareChainEnergy (pairFourConfig S false b) = 0 := by
  simp [inverseSquareChainEnergy,
    inverseSquareMatchingEnergy_pairFourConfig_false_left,
    inverseCubeBridgeEnergy_pairFourConfig_false_left]

theorem inverseSquareChainEnergy_pairFourConfig_false_right {L : ℕ}
    (S : Finset (Fin L)) (a : Bool) :
    inverseSquareChainEnergy (pairFourConfig S a false) = 0 := by
  simp [inverseSquareChainEnergy,
    inverseSquareMatchingEnergy_pairFourConfig_false_right,
    inverseCubeBridgeEnergy_pairFourConfig_false_right]

theorem inverseSquareChainEnergy_pairFourConfig_true {L : ℕ}
    (S : Finset (Fin L)) :
    inverseSquareChainEnergy (pairFourConfig S true true) =
      (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) +
        inverseCubeBridgeEnergy (pairFourConfig S true true) := by
  rw [inverseSquareChainEnergy, inverseSquareMatchingEnergy_pairFourConfig_true]

theorem phase_chord_lower {φ : ℝ} (hφ0 : 0 ≤ φ) (hφpi : φ ≤ Real.pi) :
    2 * φ / Real.pi ≤ ‖Complex.exp (-(Complex.I * (φ : ℂ))) - 1‖ := by
  have hsin := Real.mul_le_sin (x := φ / 2) (by positivity) (by linarith)
  have hsin0 : 0 ≤ Real.sin (φ / 2) := le_trans (by positivity) hsin
  have hnorm := norm_expI_sub_eq φ 0
  have hzero : Complex.exp (-((0 : ℝ) : ℂ) * Complex.I) = 1 := by norm_num
  rw [hzero, sub_zero] at hnorm
  have hshape : Complex.exp (-(Complex.I * (φ : ℂ))) =
      Complex.exp (-((φ : ℝ) : ℂ) * Complex.I) := by
    congr 1
    ring
  rw [hshape, hnorm, abs_of_nonneg hsin0]
  have hsimp : 2 / Real.pi * (φ / 2) = φ / Real.pi := by ring
  rw [hsimp] at hsin
  have htarget : 2 * φ / Real.pi = 2 * (φ / Real.pi) := by ring
  rw [htarget]
  exact mul_le_mul_of_nonneg_left hsin (by norm_num)

theorem time_mul_inverseCubeBridgeEnergy_le_quarter {L : ℕ} {t ε : ℝ}
    (hL : 2 ≤ L) (hε : 0 ≤ ε) (ht0 : 0 ≤ t) (ht : t ≤ ε * L / 2)
    (x : Config (PairQubit L)) :
    t * inverseCubeBridgeEnergy x ≤ ε / 4 := by
  have hLposN : 0 < L := by omega
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLposN
  have hb := inverseCubeBridgeEnergy_le hLposN x
  have hmul : t * inverseCubeBridgeEnergy x ≤ t * (1 / (L : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hb ht0
  have htdiv : t * (1 / (L : ℝ) ^ 2) ≤ ε / (2 * (L : ℝ)) := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have hreassoc : ε / (2 * (L : ℝ)) * (L : ℝ) ^ 2 = ε * (L : ℝ) / 2 := by
      field_simp
    rw [hreassoc]
    exact ht
  have hlast : ε / (2 * (L : ℝ)) ≤ ε / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hLR : (2 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  linarith

theorem inverseSquareChain_twoGateCount_ge {L K : ℕ}
    (c : List (LocalGate (PairQubit L))) {t ε : ℝ}
    (hK : 8 ≤ K) (hKL : 8 * K ≤ L) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 100)
    (htlo : 128 * Real.pi * ε * K ≤ t)
    (hthi : t < 128 * Real.pi * ε * (K + 1))
    (htlab : t ≤ ε * L / 2)
    (hclose : ‖circuitMatrix c - inverseSquareChainEvolution L t‖ ≤ ε) :
    K ≤ twoGateCount c := by
  by_contra hnot
  have hcost : twoGateCount c < K := Nat.lt_of_not_ge hnot
  rcases circuit_exists_inverseSquare_phase_subset c hK hKL hε htlo hthi hcost with
    ⟨S, hSblock, hSdisj, hphaseLo, hphaseHi⟩
  let x00 := pairFourConfig S false false
  let x01 := pairFourConfig S false true
  let x10 := pairFourConfig S true false
  let x11 := pairFourConfig S true true
  let W := circuitMatrix c
  let U := inverseSquareChainEvolution L t
  let φ := t * inverseSquareChainEnergy x11
  have htpos : 0 < t := by
    have hKN : 0 < K := by omega
    have hp : 0 < 128 * Real.pi * ε * (K : ℝ) := by positivity
    exact lt_of_lt_of_le hp htlo
  have hL : 2 ≤ L := by omega
  have hfactor : W x00 x00 * W x11 x11 = W x01 x01 * W x10 x10 := by
    dsimp only [W, x00, x01, x10, x11]
    exact (circuitMatrix_separates_firstEndpoints c S hSdisj).fourPoint_diagonal
  have hentry (x : Config (PairQubit L)) : ‖U x x - W x x‖ ≤ ε := by
    have hnorm : ‖(W - U) x x‖ ≤ ‖W - U‖ := norm_entry_le_l2_opNorm _ _ _
    have hrewrite : (W - U) x x = W x x - U x x := rfl
    rw [hrewrite] at hnorm
    rw [norm_sub_rev] at hnorm
    exact le_trans hnorm hclose
  have hUdiag (x : Config (PairQubit L)) :
      U x x = Complex.exp (-(Complex.I * (t * inverseSquareChainEnergy x))) := by
    dsimp only [U]
    rw [inverseSquareChainEvolution_diagonal]
    simp
  have hU00 : U x00 x00 = 1 := by
    rw [hUdiag]
    have hz : inverseSquareChainEnergy x00 = 0 := by
      exact inverseSquareChainEnergy_pairFourConfig_false_left S false
    rw [hz]
    norm_num
  have hU01 : U x01 x01 = 1 := by
    rw [hUdiag]
    have hz : inverseSquareChainEnergy x01 = 0 := by
      exact inverseSquareChainEnergy_pairFourConfig_false_left S true
    rw [hz]
    norm_num
  have hU10 : U x10 x10 = 1 := by
    rw [hUdiag]
    have hz : inverseSquareChainEnergy x10 = 0 := by
      exact inverseSquareChainEnergy_pairFourConfig_false_right S true
    rw [hz]
    norm_num
  have hU11 : U x11 x11 = Complex.exp (-(Complex.I * (φ : ℂ))) := by
    rw [hUdiag]
    simp [φ]
  have hmatch :
      t * (∑ j ∈ S, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) =
        ∑ j ∈ S, inverseSquarePhaseWeight t j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    unfold inverseSquarePhaseWeight
    ring
  have hφsplit : φ = (∑ j ∈ S, inverseSquarePhaseWeight t j) +
      t * inverseCubeBridgeEnergy x11 := by
    dsimp only [φ, x11]
    rw [inverseSquareChainEnergy_pairFourConfig_true, mul_add, hmatch]
  have hbridge0 : 0 ≤ t * inverseCubeBridgeEnergy x11 :=
    mul_nonneg (le_of_lt htpos) (inverseCubeBridgeEnergy_nonneg x11)
  have hbridgeHi : t * inverseCubeBridgeEnergy x11 ≤ ε / 4 :=
    time_mul_inverseCubeBridgeEnergy_le_quarter hL (le_of_lt hε) (le_of_lt htpos) htlab x11
  have hφ0 : 0 ≤ φ := by
    rw [hφsplit]
    have hp := Real.pi_pos
    linarith
  have hφLo : 3 * Real.pi * ε ≤ φ := by rw [hφsplit]; linarith
  have hφHiRaw : φ ≤ 5 * Real.pi * ε + ε / 4 := by rw [hφsplit]; linarith
  have hφpi : φ ≤ Real.pi := by
    have hp := Real.pi_pos
    have hpieps : Real.pi * ε ≤ Real.pi * (1 / 100 : ℝ) :=
      mul_le_mul_of_nonneg_left hεsmall (le_of_lt hp)
    have heps4 : ε / 4 ≤ (1 / 100 : ℝ) / 4 := by linarith
    have hpi3 := Real.pi_gt_three
    have : 5 * Real.pi * ε + ε / 4 < Real.pi := by nlinarith
    exact le_trans hφHiRaw (le_of_lt this)
  have h00 : ‖(1 : ℂ) - W x00 x00‖ ≤ ε := by simpa [hU00] using hentry x00
  have h01 : ‖(1 : ℂ) - W x01 x01‖ ≤ ε := by simpa [hU01] using hentry x01
  have h10 : ‖(1 : ℂ) - W x10 x10‖ ≤ ε := by simpa [hU10] using hentry x10
  have h11 : ‖Complex.exp (-(Complex.I * (φ : ℂ))) - W x11 x11‖ ≤ ε := by
    simpa [hU11] using hentry x11
  have hWunit : W ∈ Matrix.unitaryGroup (Config (PairQubit L)) ℂ := circuitMatrix_unitary c
  have hn01 : ‖W x01 x01‖ ≤ 1 := entry_norm_bound_of_unitary hWunit _ _
  have hn11 : ‖W x11 x11‖ ≤ 1 := entry_norm_bound_of_unitary hWunit _ _
  have hchordHi : ‖Complex.exp (-(Complex.I * (φ : ℂ))) - 1‖ ≤ 4 * ε :=
    norm_sub_one_le_four_mul hfactor h00 h01 h10 h11 hn01 hn11
  have hchordLo := phase_chord_lower hφ0 hφpi
  have hsix : 6 * ε ≤ 2 * φ / Real.pi := by
    rw [le_div_iff₀ Real.pi_pos]
    have hp := Real.pi_pos
    nlinarith
  nlinarith

end GaloisForLFunctions.HTGeometry.StaticLocalScratch
