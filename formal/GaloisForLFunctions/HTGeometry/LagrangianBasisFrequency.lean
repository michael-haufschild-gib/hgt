import GaloisForLFunctions.HTGeometry.LagrangianVectorFrequency

/-!
# How often a fixed label lies in the span of a commuting independent family

An ordered basis of a Lagrangian is a family of pairwise commuting labels whose subset sums are
pairwise distinct.  A form-preserving additive bijection permutes such families, so by transitivity
on nonzero labels every nonzero label lies in the span of the same number of them.  Counting
incidences between labels and families in two ways gives the exact frequency: a fixed nonzero label
lies in one span out of `2^n + 1`.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-- The set of subset sums of a labelled family. -/
def spanOf (b : Fin n → PauliSymp n) : Finset (PauliSymp n) :=
  Finset.univ.image fun S : Finset (Fin n) => ∑ i ∈ S, b i

theorem zero_mem_spanOf (b : Fin n → PauliSymp n) : (0 : PauliSymp n) ∈ spanOf b := by
  refine Finset.mem_image.mpr ⟨∅, Finset.mem_univ _, ?_⟩
  simp

/-- An ordered Lagrangian basis: pairwise commuting labels with `2^n` distinct subset sums. -/
def IsLagrBasis (b : Fin n → PauliSymp n) : Prop :=
  (∀ i j, symForm (b i) (b j) = 0) ∧ (spanOf b).card = 2 ^ n

instance : DecidablePred (IsLagrBasis (n := n)) := fun _ =>
  @instDecidableAnd _ _ inferInstance inferInstance

/-- The ordered Lagrangian bases of the `n`-qubit label space. -/
def lagrBases (n : ℕ) : Finset (Fin n → PauliSymp n) :=
  Finset.univ.filter IsLagrBasis

theorem mem_lagrBases {b : Fin n → PauliSymp n} : b ∈ lagrBases n ↔ IsLagrBasis b := by
  rw [lagrBases, Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- Subset sums are pairwise distinct for an ordered Lagrangian basis. -/
theorem injOn_subsetSum {b : Fin n → PauliSymp n} (hb : IsLagrBasis b) :
    Set.InjOn (fun S : Finset (Fin n) => ∑ i ∈ S, b i) (Finset.univ : Finset (Finset (Fin n))) := by
  refine Finset.injOn_of_card_image_eq ?_
  rw [← spanOf, hb.2, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]

section Action

variable {T : PauliSymp n ≃ PauliSymp n}

theorem map_finsetSum (hadd : ∀ x y, T (x + y) = T x + T y) (b : Fin n → PauliSymp n)
    (S : Finset (Fin n)) : T (∑ i ∈ S, b i) = ∑ i ∈ S, T (b i) := by
  classical
  have hzero : T 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h2 : T 0 - T 0 = T 0 + T 0 - T 0 := by rw [← h]
    rw [sub_self, add_sub_cancel_right] at h2
    exact h2.symm
  induction S using Finset.induction with
  | empty => simpa using hzero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

theorem spanOf_comp (hadd : ∀ x y, T (x + y) = T x + T y) (b : Fin n → PauliSymp n) :
    spanOf (fun i => T (b i)) = (spanOf b).image T := by
  classical
  rw [spanOf, spanOf, Finset.image_image]
  refine Finset.image_congr fun S _ => ?_
  exact (map_finsetSum hadd b S).symm

theorem isLagrBasis_comp (hadd : ∀ x y, T (x + y) = T x + T y)
    (hform : ∀ x y, symForm (T x) (T y) = symForm x y) {b : Fin n → PauliSymp n}
    (hb : IsLagrBasis b) : IsLagrBasis fun i => T (b i) := by
  classical
  refine ⟨fun i j => ?_, ?_⟩
  · rw [hform]
    exact hb.1 i j
  · rw [spanOf_comp hadd, Finset.card_image_of_injective _ T.injective]
    exact hb.2

theorem card_filter_mem_spanOf_eq (hadd : ∀ x y, T (x + y) = T x + T y)
    (hform : ∀ x y, symForm (T x) (T y) = symForm x y) (u : PauliSymp n) :
    ((lagrBases n).filter fun b => u ∈ spanOf b).card =
      ((lagrBases n).filter fun b => T u ∈ spanOf b).card := by
  classical
  have himg : ((lagrBases n).filter fun b => u ∈ spanOf b).image (fun b i => T (b i)) =
      (lagrBases n).filter fun b => T u ∈ spanOf b := by
    ext c
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨mem_lagrBases.mpr (isLagrBasis_comp hadd hform (mem_lagrBases.mp hb.1)), ?_⟩
      rw [spanOf_comp hadd]
      exact Finset.mem_image_of_mem _ hb.2
    · rintro ⟨hc, huc⟩
      refine ⟨fun i => T.symm (c i), ⟨mem_lagrBases.mpr ?_, ?_⟩, ?_⟩
      · exact isLagrBasis_comp (symm_map_add hadd) (symm_map_form hform) (mem_lagrBases.mp hc)
      · rw [spanOf_comp (symm_map_add hadd)]
        have := Finset.mem_image_of_mem (⇑T.symm) huc
        rwa [Equiv.symm_apply_apply] at this
      · funext i
        exact Equiv.apply_symm_apply T (c i)
  rw [← himg, Finset.card_image_of_injective]
  intro b c hbc
  funext i
  exact T.injective (congrFun hbc i)

end Action

/-- **Every nonzero label lies in the span of the same number of ordered Lagrangian bases.** -/
theorem card_filter_mem_spanOf_eq_of_ne_zero {u v : PauliSymp n} (hu : u ≠ 0) (hv : v ≠ 0) :
    ((lagrBases n).filter fun b => u ∈ spanOf b).card =
      ((lagrBases n).filter fun b => v ∈ spanOf b).card := by
  obtain ⟨T, hadd, hform, hTu⟩ := exists_symplectic_equiv_map hu hv
  rw [card_filter_mem_spanOf_eq hadd hform u, hTu]

section Counting

theorem card_pauliSymp' : Fintype.card (PauliSymp n) = 4 ^ n := by
  simp [PauliSymp]

theorem sum_card_filter_mem_spanOf :
    (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0,
        ((lagrBases n).filter fun b => v ∈ spanOf b).card) =
      (lagrBases n).card * (2 ^ n - 1) := by
  classical
  have h1 : ∀ v : PauliSymp n, ((lagrBases n).filter fun b => v ∈ spanOf b).card
      = ∑ b ∈ lagrBases n, (if v ∈ spanOf b then 1 else 0) := by
    intro v
    rw [Finset.sum_boole]
    simp
  have h2 : ∀ b : Fin n → PauliSymp n,
      ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ spanOf b).card
      = ∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0, (if v ∈ spanOf b then 1 else 0) := by
    intro b
    rw [Finset.sum_boole]
    simp
  have hswap : (∑ v ∈ Finset.univ.filter fun v : PauliSymp n => v ≠ 0,
      ((lagrBases n).filter fun b => v ∈ spanOf b).card) =
      ∑ b ∈ lagrBases n,
        ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ spanOf b).card := by
    simp only [h1, h2]
    exact Finset.sum_comm
  rw [hswap]
  have hinner : ∀ b ∈ lagrBases n,
      ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ spanOf b).card =
        2 ^ n - 1 := by
    intro b hb
    have hL := mem_lagrBases.mp hb
    have hset : ((Finset.univ.filter fun v : PauliSymp n => v ≠ 0).filter fun v => v ∈ spanOf b) =
        (spanOf b).erase 0 := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [hset, Finset.card_erase_of_mem (zero_mem_spanOf b), hL.2]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]

/-- **The exact span frequency of a nonzero label.** -/
theorem card_filter_mem_spanOf_mul_succ {v : PauliSymp n} (hv : v ≠ 0) :
    ((lagrBases n).filter fun b => v ∈ spanOf b).card * (2 ^ n + 1) = (lagrBases n).card := by
  classical
  set c : ℕ := ((lagrBases n).filter fun b => v ∈ spanOf b).card with hc
  have hnpos : 1 ≤ n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    subst hn0
    exact hv (funext fun i => absurd i.2 (by omega))
  have hnz : (Finset.univ.filter fun w : PauliSymp n => w ≠ 0).card = 4 ^ n - 1 := by
    have hcompl : (Finset.univ.filter fun w : PauliSymp n => w ≠ 0) =
        (Finset.univ : Finset (PauliSymp n)).erase 0 := by
      ext w
      simp [Finset.mem_erase]
    rw [hcompl, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_pauliSymp']
  have hall : ∀ w ∈ Finset.univ.filter fun w : PauliSymp n => w ≠ 0,
      ((lagrBases n).filter fun b => w ∈ spanOf b).card = c := by
    intro w hw
    rw [Finset.mem_filter] at hw
    exact card_filter_mem_spanOf_eq_of_ne_zero hw.2 hv
  have hconst : (∑ w ∈ Finset.univ.filter fun w : PauliSymp n => w ≠ 0,
      ((lagrBases n).filter fun b => w ∈ spanOf b).card) = (4 ^ n - 1) * c := by
    rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_eq_mul, hnz]
  have hdouble := sum_card_filter_mem_spanOf (n := n)
  rw [hconst] at hdouble
  have hfact : (4 : ℕ) ^ n - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    have h4 : (4 : ℕ) ^ n = 2 ^ n * 2 ^ n := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, mul_pow]
    obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega⟩
    rw [h4, hm]
    have hl : (m + 1) * (m + 1) - 1 = m * m + 2 * m := by
      have hexp : (m + 1) * (m + 1) = m * m + 2 * m + 1 := by ring
      omega
    have hr : ((m + 1) - 1) * ((m + 1) + 1) = m * m + 2 * m := by
      have h1 : (m + 1) - 1 = m := by omega
      rw [h1]
      ring
    rw [hl, hr]
  rw [hfact] at hdouble
  have hpos : 0 < 2 ^ n - 1 := by
    have h2 : 2 ≤ 2 ^ n := by
      calc (2 : ℕ) = 2 ^ (1 : ℕ) := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  have hle : (2 ^ n - 1) * ((2 ^ n + 1) * c) = (2 ^ n - 1) * (lagrBases n).card := by
    calc (2 ^ n - 1) * ((2 ^ n + 1) * c) = (2 ^ n - 1) * (2 ^ n + 1) * c := by ring
      _ = (lagrBases n).card * (2 ^ n - 1) := hdouble
      _ = (2 ^ n - 1) * (lagrBases n).card := by ring
  have hres := Nat.eq_of_mul_eq_mul_left hpos hle
  rw [mul_comm]
  exact hres

end Counting

end GaloisForLFunctions.HTGeometry
