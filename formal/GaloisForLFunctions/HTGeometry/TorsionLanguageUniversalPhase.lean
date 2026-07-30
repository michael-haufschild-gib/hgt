import GaloisForLFunctions.HTGeometry.PolynomialADEPhaseIdentity
import GaloisForLFunctions.HTGeometry.PolynomialPatternWeight
import GaloisForLFunctions.HTGeometry.TorsionFaceExactification
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Torsion-language-universal Taylor phases

This module gives the phase recurrence used by geometric-magnitude exactification a literal Lean
definition.  It extracts cofinal exact occurrences of every finite torsion word and identifies the
normalized phase of each translated bounded ADE pattern with the corresponding finite character.
-/

namespace GaloisForLFunctions

open Filter Finset PowerSeries Topology

noncomputable section

/-- Every finite word in every positive-order complex torsion alphabet occurs arbitrarily far out
in the phase sequence. -/
def TorsionLanguageUniversal (u : ℕ → ℂ) : Prop :=
  ∀ (m M N : ℕ), 0 < m → ∀ s : Fin M → ℂ,
    (∀ r, s r ^ m = 1) →
      ∃ q, N ≤ q ∧ ∀ r : Fin M, u (q + (r : ℕ)) = s r

/-- Torsion-language universality is unchanged by a finite modification of the phase sequence. -/
theorem TorsionLanguageUniversal.of_eventuallyEq
    {u v : ℕ → ℂ} (hu : TorsionLanguageUniversal u)
    (huv : v =ᶠ[atTop] u) : TorsionLanguageUniversal v := by
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp huv
  intro m M N hm s hs
  obtain ⟨q, hq, hword⟩ := hu m M (max N T) hm s hs
  refine ⟨q, (le_max_left N T).trans hq, fun r => ?_⟩
  rw [hT (q + (r : ℕ)) ((le_max_right N T).trans hq |>.trans
    (Nat.le_add_right q (r : ℕ)))]
  exact hword r

/-- Arbitrarily late occurrences of one torsion word contain a strictly increasing cofinal
subsequence of exact occurrences. -/
theorem TorsionLanguageUniversal.exists_strictMono_occurrences
    {u : ℕ → ℂ} (hu : TorsionLanguageUniversal u)
    {m M : ℕ} (hm : 0 < m) (s : Fin M → ℂ)
    (hs : ∀ r, s r ^ m = 1) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ Tendsto q atTop atTop ∧
      ∀ k (r : Fin M), u (q k + (r : ℕ)) = s r := by
  let P : ℕ → Prop := fun q => ∀ r : Fin M, u (q + (r : ℕ)) = s r
  have hP : ∀ N, ∃ q > N, P q := by
    intro N
    obtain ⟨q, hq, hword⟩ := hu m M (N + 1) hm s hs
    exact ⟨q, by omega, hword⟩
  obtain ⟨q, hqmono, hqP⟩ := Nat.exists_strictMono_subsequence hP
  exact ⟨q, hqmono, hqmono.tendsto_atTop, hqP⟩

noncomputable local instance rootsOfUnityFintype (m : ℕ+) :
    Fintype (rootsOfUnity (m : ℕ) ℂ) :=
  Fintype.ofFinite _

noncomputable local instance rootsOfUnityEncodable (m : ℕ+) :
    Encodable (rootsOfUnity (m : ℕ) ℂ) :=
  Fintype.toEncodable _

private abbrev TorsionWord :=
  Σ m : ℕ+, Σ M : ℕ, Fin M → rootsOfUnity (m : ℕ) ℂ

noncomputable local instance : Encodable TorsionWord := inferInstance

private structure FiniteWord (α : Type*) where
  length : ℕ
  value : ℕ → α

private noncomputable def torsionWordAt (n : ℕ) : FiniteWord ℂ :=
  match Encodable.decode (α := TorsionWord) (Nat.unpair n).1 with
  | none => ⟨0, fun _ => 0⟩
  | some ⟨_, M, s⟩ =>
      ⟨M, fun i => if h : i < M then ((s ⟨i, h⟩ : ℂˣ) : ℂ) else 0⟩

private def finiteWordStart {α : Type*} (e : ℕ → FiniteWord α) : ℕ → ℕ
  | 0 => 0
  | n + 1 => finiteWordStart e n + (e n).length + 1

private theorem finiteWordStart_strictMono {α : Type*} (e : ℕ → FiniteWord α) :
    StrictMono (finiteWordStart e) := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp [finiteWordStart]

private theorem index_le_finiteWordStart {α : Type*} (e : ℕ → FiniteWord α) (n : ℕ) :
    n ≤ finiteWordStart e n := by
  induction n with
  | zero => simp [finiteWordStart]
  | succ n ih => simp [finiteWordStart]; omega

private def finiteWordPosition {α : Type*} (e : ℕ → FiniteWord α)
    (a : Σ n, Fin (e n).length) : ℕ :=
  finiteWordStart e a.1 + (a.2 : ℕ)

private theorem finiteWordPosition_injective {α : Type*} (e : ℕ → FiniteWord α) :
    Function.Injective (finiteWordPosition e) := by
  rintro ⟨n, r⟩ ⟨m, s⟩ h
  have hmono := finiteWordStart_strictMono e
  have hnlt : finiteWordPosition e ⟨n, r⟩ < finiteWordStart e (n + 1) := by
    simp only [finiteWordPosition, finiteWordStart]
    omega
  have hmlt : finiteWordPosition e ⟨m, s⟩ < finiteWordStart e (m + 1) := by
    simp only [finiteWordPosition, finiteWordStart]
    omega
  have hnm : n = m := by
    rcases lt_trichotomy n m with hnm | hnm | hmn
    · have hle : finiteWordStart e (n + 1) ≤ finiteWordStart e m :=
        hmono.monotone (Nat.succ_le_iff.mpr hnm)
      have hpos : finiteWordStart e m ≤ finiteWordPosition e ⟨m, s⟩ := by
        simp [finiteWordPosition]
      omega
    · exact hnm
    · have hle : finiteWordStart e (m + 1) ≤ finiteWordStart e n :=
        hmono.monotone (Nat.succ_le_iff.mpr hmn)
      have hpos : finiteWordStart e n ≤ finiteWordPosition e ⟨n, r⟩ := by
        simp [finiteWordPosition]
      omega
  subst m
  congr
  apply Fin.ext
  simpa [finiteWordPosition] using h

private noncomputable def concatenatedFiniteWords {α : Type*} [Inhabited α]
    (e : ℕ → FiniteWord α) : ℕ → α :=
  Function.extend (finiteWordPosition e)
    (fun a => (e a.1).value a.2) (fun _ => default)

private theorem concatenatedFiniteWords_apply {α : Type*} [Inhabited α]
    (e : ℕ → FiniteWord α) (a : Σ n, Fin (e n).length) :
    concatenatedFiniteWords e (finiteWordPosition e a) = (e a.1).value a.2 := by
  exact (finiteWordPosition_injective e).extend_apply _ _ _

private theorem concatenatedFiniteWords_at_block {α : Type*} [Inhabited α]
    (e : ℕ → FiniteWord α) {n : ℕ} (r : Fin (e n).length) :
    concatenatedFiniteWords e (finiteWordStart e n + (r : ℕ)) = (e n).value r := by
  simpa [finiteWordPosition] using
    (concatenatedFiniteWords_apply e ⟨n, r⟩)

/-- A chosen phase sequence obtained by concatenating a cofinally repeated enumeration of all
finite words in all positive-order complex root-of-unity alphabets. -/
noncomputable def universalTorsionPhase : ℕ → ℂ :=
  concatenatedFiniteWords torsionWordAt

/-- The concatenated root-of-unity phase contains every finite torsion word beyond every cutoff. -/
theorem universalTorsionPhase_torsionLanguageUniversal :
    TorsionLanguageUniversal universalTorsionPhase := by
  intro m M N hm s hs
  have hs0 : ∀ r, s r ≠ 0 := by
    intro r hzero
    have h := hs r
    rw [hzero, zero_pow (Nat.ne_of_gt hm)] at h
    exact zero_ne_one h
  let rootWord : Fin M → rootsOfUnity m ℂ := fun r =>
    ⟨Units.mk0 (s r) (hs0 r), by
      rw [mem_rootsOfUnity]
      apply Units.ext
      simp [hs r]⟩
  let task : TorsionWord := ⟨⟨m, hm⟩, M, rootWord⟩
  let n := Nat.pair (Encodable.encode task) N
  have hlength : (torsionWordAt n).length = M := by
    simp only [torsionWordAt, n, Nat.unpair_pair, Encodable.encodek]
    simp [task]
  have hvalue (r : Fin M) : (torsionWordAt n).value r = s r := by
    simp only [torsionWordAt, n, Nat.unpair_pair, Encodable.encodek]
    simp [task, rootWord, r.isLt]
  refine ⟨finiteWordStart torsionWordAt n, ?_, ?_⟩
  · exact (Nat.right_le_pair (Encodable.encode task) N).trans
      (index_le_finiteWordStart torsionWordAt n)
  · intro r
    let r' : Fin (torsionWordAt n).length := Fin.cast hlength.symm r
    have hv := concatenatedFiniteWords_at_block torsionWordAt r'
    have hr' : (r' : ℕ) = (r : ℕ) := by simp [r']
    rw [hr'] at hv
    exact hv.trans (hvalue r)

/-- Torsion-language-universal complex phase sequences exist. -/
theorem exists_torsionLanguageUniversal :
    ∃ u : ℕ → ℂ, TorsionLanguageUniversal u :=
  ⟨universalTorsionPhase, universalTorsionPhase_torsionLanguageUniversal⟩

private noncomputable def concatenatedFiniteWordsOne
    (e : ℕ → FiniteWord ℂ) : ℕ → ℂ :=
  Function.extend (finiteWordPosition e)
    (fun a => (e a.1).value a.2) (fun _ => 1)

private theorem concatenatedFiniteWordsOne_apply
    (e : ℕ → FiniteWord ℂ) (a : Σ n, Fin (e n).length) :
    concatenatedFiniteWordsOne e (finiteWordPosition e a) =
      (e a.1).value a.2 := by
  exact (finiteWordPosition_injective e).extend_apply _ _ _

private theorem concatenatedFiniteWordsOne_at_block
    (e : ℕ → FiniteWord ℂ) {n : ℕ} (r : Fin (e n).length) :
    concatenatedFiniteWordsOne e (finiteWordStart e n + (r : ℕ)) =
      (e n).value r := by
  simpa [finiteWordPosition] using
    (concatenatedFiniteWordsOne_apply e ⟨n, r⟩)

private theorem norm_torsionWordAt_value (n : ℕ)
    (r : Fin (torsionWordAt n).length) :
    ‖(torsionWordAt n).value r‖ = 1 := by
  unfold torsionWordAt at r ⊢
  generalize hdecode : Encodable.decode (α := TorsionWord) (Nat.unpair n).1 =
    decoded at r ⊢
  cases decoded with
  | none => exact Fin.elim0 r
  | some word =>
    rcases word with ⟨m, M, s⟩
    simp only at r
    simp only [r.isLt, ↓reduceDIte]
    exact Complex.norm_eq_one_of_mem_rootsOfUnity (s r).property

private theorem torsion_torsionWordAt_value (n : ℕ)
    (r : Fin (torsionWordAt n).length) :
    ∃ m : ℕ, 0 < m ∧ (torsionWordAt n).value r ^ m = 1 := by
  unfold torsionWordAt at r ⊢
  generalize hdecode : Encodable.decode (α := TorsionWord) (Nat.unpair n).1 =
    decoded at r ⊢
  cases decoded with
  | none => exact Fin.elim0 r
  | some word =>
    rcases word with ⟨m, M, s⟩
    simp only at r
    refine ⟨m, m.pos, ?_⟩
    simp only [r.isLt, ↓reduceDIte]
    have hp := congrArg (fun z : ℂˣ => (z : ℂ)) (s r).property
    simpa using hp

/-- A chosen torsion-language-universal phase with no zero-valued separators.  Unused positions
in the word concatenation are filled by the root of unity `1`. -/
noncomputable def universalUnitTorsionPhase : ℕ → ℂ :=
  concatenatedFiniteWordsOne torsionWordAt

/-- Every entry of the unit-filled universal torsion phase has unit norm. -/
theorem universalUnitTorsionPhase_norm (n : ℕ) :
    ‖universalUnitTorsionPhase n‖ = 1 := by
  classical
  by_cases h : ∃ a, finiteWordPosition torsionWordAt a = n
  · obtain ⟨a, rfl⟩ := h
    rw [universalUnitTorsionPhase, concatenatedFiniteWordsOne_apply]
    exact norm_torsionWordAt_value a.1 a.2
  · rw [universalUnitTorsionPhase, concatenatedFiniteWordsOne,
      Function.extend_apply' _ _ _ h]
    simp

/-- Every entry of the unit-filled universal phase is itself a root of unity of some positive
order. -/
theorem universalUnitTorsionPhase_isTorsion (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ universalUnitTorsionPhase n ^ m = 1 := by
  classical
  by_cases h : ∃ a, finiteWordPosition torsionWordAt a = n
  · obtain ⟨a, rfl⟩ := h
    rw [universalUnitTorsionPhase, concatenatedFiniteWordsOne_apply]
    exact torsion_torsionWordAt_value a.1 a.2
  · rw [universalUnitTorsionPhase, concatenatedFiniteWordsOne,
      Function.extend_apply' _ _ _ h]
    exact ⟨1, by omega, by simp⟩

/-- The unit-filled concatenation still contains every finite torsion word beyond every cutoff. -/
theorem universalUnitTorsionPhase_torsionLanguageUniversal :
    TorsionLanguageUniversal universalUnitTorsionPhase := by
  intro m M N hm s hs
  have hs0 : ∀ r, s r ≠ 0 := by
    intro r hzero
    have h := hs r
    rw [hzero, zero_pow (Nat.ne_of_gt hm)] at h
    exact zero_ne_one h
  let rootWord : Fin M → rootsOfUnity m ℂ := fun r =>
    ⟨Units.mk0 (s r) (hs0 r), by
      rw [mem_rootsOfUnity]
      apply Units.ext
      simp [hs r]⟩
  let task : TorsionWord := ⟨⟨m, hm⟩, M, rootWord⟩
  let n := Nat.pair (Encodable.encode task) N
  have hlength : (torsionWordAt n).length = M := by
    simp only [torsionWordAt, n, Nat.unpair_pair, Encodable.encodek]
    simp [task]
  have hvalue (r : Fin M) : (torsionWordAt n).value r = s r := by
    simp only [torsionWordAt, n, Nat.unpair_pair, Encodable.encodek]
    simp [task, rootWord, r.isLt]
  refine ⟨finiteWordStart torsionWordAt n, ?_, ?_⟩
  · exact (Nat.right_le_pair (Encodable.encode task) N).trans
      (index_le_finiteWordStart torsionWordAt n)
  · intro r
    let r' : Fin (torsionWordAt n).length := Fin.cast hlength.symm r
    have hv := concatenatedFiniteWordsOne_at_block torsionWordAt r'
    have hr' : (r' : ℕ) = (r : ℕ) := by simp [r']
    rw [hr'] at hv
    exact hv.trans (hvalue r)

/-- There exists a torsion-language-universal phase whose every entry has unit norm. -/
theorem exists_unitNorm_torsionLanguageUniversal :
    ∃ u : ℕ → ℂ,
      TorsionLanguageUniversal u ∧
      (∀ n, ‖u n‖ = 1) ∧
      ∀ n, ∃ m : ℕ, 0 < m ∧ u n ^ m = 1 :=
  ⟨universalUnitTorsionPhase,
    universalUnitTorsionPhase_torsionLanguageUniversal,
    universalUnitTorsionPhase_norm,
    universalUnitTorsionPhase_isTorsion⟩

/-- A translated bounded multiplicity pattern evaluates as its finite phase character. -/
theorem prod_shiftedAtomPatternKey
    {M D : ℕ} (u : ℕ → ℂ) (q K : ℕ)
    (p : Fin M → Fin (D + 1)) :
    (shiftedAtomPatternKey q K p).prod (fun i k => u i ^ k) =
      ∏ r : Fin M, u (windowShift q K (r : ℕ)) ^ (p r : ℕ) := by
  classical
  rw [shiftedAtomPatternKey_eq_sum]
  change (∑ r ∈ (Finset.univ : Finset (Fin M)),
      Finsupp.single (windowShift q K (r : ℕ)) (p r : ℕ)).prod
        (fun i k => u i ^ k) =
    ∏ r ∈ (Finset.univ : Finset (Fin M)),
      u (windowShift q K (r : ℕ)) ^ (p r : ℕ)
  rw [← Finsupp.prod_finsetSum_index]
  · simp
  · intro i
    simp
  · intro i a b
    exact pow_add _ _ _

/-- The product of coefficient-magnitude factors is the exponential of the negative atom
valuation. -/
theorem prod_exp_neg_eq_exp_neg_atomValuation
    (b : ℕ → ℝ) (ν : ℕ →₀ ℕ) :
    ν.prod (fun i k => ((Real.exp (-b i) : ℝ) : ℂ) ^ k) =
      ((Real.exp (-atomValuation b ν) : ℝ) : ℂ) := by
  classical
  change (∏ i ∈ ν.support, ((Real.exp (-b i) : ℝ) : ℂ) ^ ν i) = _
  simp_rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
  rw [← Complex.exp_sum]
  congr 1
  rw [atomValuation]
  rw [Finsupp.sum]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- If each Taylor coefficient is its prescribed magnitude times `u i`, the intrinsic normalized
atom phase is exactly the multiplicative phase monomial. -/
theorem normalizedAtomPhase_eq_phaseProd
    (F : PowerSeries ℂ) (b : ℕ → ℝ) (u : ℕ → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-b i) : ℝ) : ℂ) * u i)
    (ν : ℕ →₀ ℕ) :
    normalizedAtomPhase F b ν = ν.prod (fun i k => u i ^ k) := by
  classical
  rw [normalizedAtomPhase]
  simp_rw [hcoeff, mul_pow]
  rw [Finsupp.prod_mul, prod_exp_neg_eq_exp_neg_atomValuation]
  push_cast
  rw [← mul_assoc, ← Complex.exp_add]
  simp

/-- The normalized phase of a shifted bounded ADE atom is its finite torsion character. -/
theorem normalizedAtomPhase_shiftedAtomPatternKey_eq
    (F : PowerSeries ℂ) (b : ℕ → ℝ) (u : ℕ → ℂ)
    (hcoeff : ∀ i, PowerSeries.coeff i F =
      ((Real.exp (-b i) : ℝ) : ℂ) * u i)
    {M D : ℕ} (q K : ℕ) (p : Fin M → Fin (D + 1)) :
    normalizedAtomPhase F b (shiftedAtomPatternKey q K p) =
      ∏ r : Fin M, u (windowShift q K (r : ℕ)) ^ (p r : ℕ) := by
  rw [normalizedAtomPhase_eq_phaseProd F b u hcoeff]
  exact prod_shiftedAtomPatternKey u q K p

end

end GaloisForLFunctions
