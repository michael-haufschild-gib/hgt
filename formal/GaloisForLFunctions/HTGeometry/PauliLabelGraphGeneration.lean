import GaloisForLFunctions.HTGeometry.PauliLabelAnticommute
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Generating every Pauli label from one-site and connected-graph edge labels

A set of Pauli labels closed under products of anticommuting labels, containing every one-site
label and every two-site label on an edge of a connected graph, contains every label.  Two adjacent
edges produce the far pair, connectivity propagates that along a walk, and a heavier label is the
product of a two-site label with a strictly lighter one.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section Letters

theorem optMul_optMul_self (q p : Option (Fin 3)) : optMul q (optMul q p) = p := by
  revert q p
  decide

theorem optMul_ne_none_of_ne {a b : Fin 3} (hab : a ≠ b) :
    optMul (some a) (some b) ≠ none := by
  rw [Ne, optMul_eq_none_iff]
  intro hc
  exact hab (Option.some_injective _ hc)

theorem optMul_some_ne_left : ∀ a b : Fin 3, a ≠ b → optMul (some a) (some b) ≠ some a := by
  decide

theorem exists_letters_mul_eq (a : Fin 3) :
    ∃ α α' : Fin 3, α ≠ α' ∧ optMul (some α) (some α') = some a := by
  rcases fin3_eq_cases a with rfl | rfl | rfl
  · exact ⟨1, 2, by decide, by decide⟩
  · exact ⟨2, 0, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide⟩

theorem exists_letter_ne (a : Fin 3) : ∃ c : Fin 3, c ≠ a := by
  rcases fin3_eq_cases a with rfl | rfl | rfl
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨0, by decide⟩

end Letters

section Products

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- A three-site label times a two-site label on its first two sites is a two-site label. -/
theorem optMulLabel_tripleLabel_pairLabel {i j k : σ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (α α' f d a : Fin 3) (ha : optMul (some α) (some α') = some a) :
    optMulLabel (tripleLabel i j k α f d) (pairLabel i j α' f) = pairLabel i k a d := by
  classical
  funext t
  show optMul (tripleLabel i j k α f d t) (pairLabel i j α' f t) = _
  rw [tripleLabel_apply, pairLabel_apply, pairLabel_apply]
  by_cases hti : t = i <;> by_cases htj : t = j <;> by_cases htk : t = k <;>
    simp [hti, htj, htk, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk, ha,
      optMul_self, optMul_none_right]

theorem tripleLabel_eq_optMulLabel_of_mul {i j k : σ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (α m m' d f : Fin 3) (hf : some f = optMul (some m) (some m')) :
    tripleLabel i j k α f d = optMulLabel (pairLabel i j α m) (pairLabel j k m' d) :=
  (tripleLabel_eq_optMulLabel_iff hij hjk hik α f d α m m' d).mpr ⟨rfl, rfl, hf⟩

end Products


section Generation

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (G : SimpleGraph σ) (K : Set (σ → Option (Fin 3)))

theorem optMulLabel_optMulLabel_self (Q P : σ → Option (Fin 3)) :
    optMulLabel Q (optMulLabel Q P) = P := by
  funext t
  exact optMul_optMul_self (Q t) (P t)

/-- **Two adjacent edges produce the far pair.** -/
theorem pairLabel_mem_of_adj_of_mem
    (hedge : ∀ i j : σ, G.Adj i j → ∀ a b : Fin 3, pairLabel i j a b ∈ K)
    (hclosed : ∀ P Q : σ → Option (Fin 3), P ∈ K → Q ∈ K →
      optPhaseProd P Q ≠ optPhaseProd Q P → optMulLabel P Q ∈ K)
    {i j k : σ} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hadj : G.Adj i j)
    (hjkmem : ∀ q e : Fin 3, pairLabel j k q e ∈ K) (a d : Fin 3) :
    pairLabel i k a d ∈ K := by
  classical
  obtain ⟨α, α', hαne, hαmul⟩ := exists_letters_mul_eq a
  have hf : (some 2 : Option (Fin 3)) = optMul (some 0) (some 1) := by decide
  have hQ1 : pairLabel i j α 0 ∈ K := hedge i j hadj α 0
  have hQ2 : pairLabel j k 1 d ∈ K := hjkmem 1 d
  have hanti1 : optPhaseProd (pairLabel i j α 0) (pairLabel j k 1 d) ≠
      optPhaseProd (pairLabel j k 1 d) (pairLabel i j α 0) := by
    refine optPhaseProd_ne_of_unique_site j ⟨0, 1, ?_, ?_, by decide⟩ ?_
    · rw [pairLabel_apply, if_neg (Ne.symm hij), if_pos rfl]
    · rw [pairLabel_apply, if_pos rfl]
    · intro t htj
      by_cases hti : t = i
      · refine Or.inr (Or.inl ?_)
        rw [pairLabel_apply, hti, if_neg hij, if_neg hik]
      · by_cases htk : t = k
        · refine Or.inl ?_
          rw [pairLabel_apply, htk, if_neg (Ne.symm hik), if_neg (Ne.symm hjk)]
        · refine Or.inl ?_
          rw [pairLabel_apply, if_neg hti, if_neg htj]
  have hU : tripleLabel i j k α 2 d ∈ K := by
    rw [tripleLabel_eq_optMulLabel_of_mul hij hjk hik α 0 1 d 2 hf]
    exact hclosed _ _ hQ1 hQ2 hanti1
  have hQ3 : pairLabel i j α' 2 ∈ K := hedge i j hadj α' 2
  have hanti2 : optPhaseProd (tripleLabel i j k α 2 d) (pairLabel i j α' 2) ≠
      optPhaseProd (pairLabel i j α' 2) (tripleLabel i j k α 2 d) := by
    refine optPhaseProd_ne_of_unique_site i ⟨α, α', ?_, ?_, hαne⟩ ?_
    · rw [tripleLabel_apply, if_pos rfl]
    · rw [pairLabel_apply, if_pos rfl]
    · intro t hti
      by_cases htj : t = j
      · refine Or.inr (Or.inr ?_)
        rw [tripleLabel_apply, pairLabel_apply, htj, if_neg (Ne.symm hij), if_pos rfl,
          if_neg (Ne.symm hij), if_pos rfl]
      · by_cases htk : t = k
        · refine Or.inr (Or.inl ?_)
          rw [pairLabel_apply, htk, if_neg (Ne.symm hik), if_neg (Ne.symm hjk)]
        · refine Or.inl ?_
          rw [tripleLabel_apply, if_neg hti, if_neg htj, if_neg htk]
  have hres := hclosed _ _ hU hQ3 hanti2
  rwa [optMulLabel_tripleLabel_pairLabel hij hik hjk α α' 2 d a hαmul] at hres

/-- Connectivity propagates the two-site labels along a walk. -/
theorem pairLabel_mem_of_walk
    (hedge : ∀ i j : σ, G.Adj i j → ∀ a b : Fin 3, pairLabel i j a b ∈ K)
    (hclosed : ∀ P Q : σ → Option (Fin 3), P ∈ K → Q ∈ K →
      optPhaseProd P Q ≠ optPhaseProd Q P → optMulLabel P Q ∈ K) :
    ∀ {i k : σ} (_ : G.Walk i k), i ≠ k → ∀ a d : Fin 3, pairLabel i k a d ∈ K := by
  intro i k w
  induction w with
  | nil => intro hik; exact absurd rfl hik
  | @cons u v t hadj w ih =>
      intro hut a d
      by_cases hvt : v = t
      · subst hvt
        exact hedge u v hadj a d
      · exact pairLabel_mem_of_adj_of_mem G K hedge hclosed hadj.ne hut hvt hadj
          (fun q e => ih hvt q e) a d


theorem eq_siteLabel_of_support_singleton {P : σ → Option (Fin 3)} {v : σ} {a : Fin 3}
    (hv : P v = some a) (hsupp : labelSupport P = {v}) : P = siteLabel v a := by
  classical
  funext t
  rw [siteLabel_apply]
  by_cases htv : t = v
  · rw [if_pos htv, htv, hv]
  · rw [if_neg htv]
    by_contra hc
    have hmem : t ∈ labelSupport P := mem_labelSupport.mpr hc
    rw [hsupp, Finset.mem_singleton] at hmem
    exact htv hmem

theorem eq_pairLabel_of_support_pair {P : σ → Option (Fin 3)} {i k : σ} {a d : Fin 3}
    (hi : P i = some a) (hk : P k = some d)
    (hsupp : labelSupport P = {i, k}) : P = pairLabel i k a d := by
  classical
  funext t
  rw [pairLabel_apply]
  by_cases hti : t = i
  · rw [if_pos hti, hti, hi]
  · rw [if_neg hti]
    by_cases htk : t = k
    · rw [if_pos htk, htk, hk]
    · rw [if_neg htk]
      by_contra hc
      have hmem : t ∈ labelSupport P := mem_labelSupport.mpr hc
      rw [hsupp, Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem.elim hti htk

/-- **One-site labels and connected-graph edge labels generate every label.** -/
theorem label_mem_of_connected (hconn : G.Connected)
    (hsite : ∀ (v : σ) (a : Fin 3), siteLabel v a ∈ K)
    (hedge : ∀ i j : σ, G.Adj i j → ∀ a b : Fin 3, pairLabel i j a b ∈ K)
    (hclosed : ∀ P Q : σ → Option (Fin 3), P ∈ K → Q ∈ K →
      optPhaseProd P Q ≠ optPhaseProd Q P → optMulLabel P Q ∈ K)
    (P : σ → Option (Fin 3)) (hne : (labelSupport P).Nonempty) : P ∈ K := by
  classical
  have hpair : ∀ i k : σ, i ≠ k → ∀ a d : Fin 3, pairLabel i k a d ∈ K := by
    intro i k hik a d
    obtain ⟨w⟩ := hconn.preconnected i k
    exact pairLabel_mem_of_walk G K hedge hclosed w hik a d
  induction hcard : (labelSupport P).card using Nat.strong_induction_on generalizing P with
  | _ N ih =>
    rcases Nat.lt_or_ge N 3 with hsmall | hbig
    · interval_cases N
      · exact absurd (Finset.card_pos.mpr hne) (by omega)
      · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
        obtain ⟨a, ha⟩ : ∃ a : Fin 3, P v = some a := by
          have : v ∈ labelSupport P := by rw [hv]; exact Finset.mem_singleton_self v
          cases hpv : P v with
          | none => exact absurd hpv (mem_labelSupport.mp this)
          | some a => exact ⟨a, rfl⟩
        rw [eq_siteLabel_of_support_singleton ha hv]
        exact hsite v a
      · obtain ⟨i, k, hik, hpairsupp⟩ := Finset.card_eq_two.mp hcard
        obtain ⟨a, ha⟩ : ∃ a : Fin 3, P i = some a := by
          have : i ∈ labelSupport P := by rw [hpairsupp]; exact Finset.mem_insert_self i {k}
          cases hpv : P i with
          | none => exact absurd hpv (mem_labelSupport.mp this)
          | some a => exact ⟨a, rfl⟩
        obtain ⟨d, hd⟩ : ∃ d : Fin 3, P k = some d := by
          have : k ∈ labelSupport P := by
            rw [hpairsupp]
            exact Finset.mem_insert_of_mem (Finset.mem_singleton_self k)
          cases hpv : P k with
          | none => exact absurd hpv (mem_labelSupport.mp this)
          | some d => exact ⟨d, rfl⟩
        rw [eq_pairLabel_of_support_pair ha hd hpairsupp]
        exact hpair i k hik a d
    · obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (labelSupport P).card)
      obtain ⟨pi, hpi⟩ : ∃ pi : Fin 3, P i = some pi := by
        cases hpv : P i with
        | none => exact absurd hpv (mem_labelSupport.mp hi)
        | some a => exact ⟨a, rfl⟩
      obtain ⟨pj, hpj⟩ : ∃ pj : Fin 3, P j = some pj := by
        cases hpv : P j with
        | none => exact absurd hpv (mem_labelSupport.mp hj)
        | some a => exact ⟨a, rfl⟩
      obtain ⟨c, hc⟩ := exists_letter_ne pj
      have hQmem : pairLabel i j pi c ∈ K := hpair i j hij pi c
      have hsupp' : labelSupport (optMulLabel (pairLabel i j pi c) P) =
          (labelSupport P).erase i := by
        ext t
        rw [mem_labelSupport, Finset.mem_erase, mem_labelSupport]
        by_cases hti : t = i
        · subst hti
          have hval : optMulLabel (pairLabel t j pi c) P t = none := by
            show optMul (pairLabel t j pi c t) (P t) = none
            rw [pairLabel_apply, if_pos rfl, hpi, optMul_self]
          simp [hval]
        · by_cases htj : t = j
          · subst htj
            have hval : optMulLabel (pairLabel i t pi c) P t = optMul (some c) (some pj) := by
              show optMul (pairLabel i t pi c t) (P t) = _
              rw [pairLabel_apply, if_neg hti, if_pos rfl, hpj]
            rw [hval]
            simp [optMul_ne_none_of_ne hc, hti, mem_labelSupport.mp hj]
          · have hval : optMulLabel (pairLabel i j pi c) P t = P t := by
              show optMul (pairLabel i j pi c t) (P t) = _
              rw [pairLabel_apply, if_neg hti, if_neg htj]
              rfl
            rw [hval]
            simp [hti]
      have hcard' : (labelSupport (optMulLabel (pairLabel i j pi c) P)).card = N - 1 := by
        rw [hsupp', Finset.card_erase_of_mem hi, hcard]
      have hne' : (labelSupport (optMulLabel (pairLabel i j pi c) P)).Nonempty := by
        rw [← Finset.card_pos, hcard']
        omega
      have hPmem : optMulLabel (pairLabel i j pi c) P ∈ K :=
        ih (N - 1) (by omega) _ hne' hcard'
      have hvali : optMulLabel (pairLabel i j pi c) P i = none := by
        show optMul (pairLabel i j pi c i) (P i) = none
        rw [pairLabel_apply, if_pos rfl, hpi, optMul_self]
      obtain ⟨z, hz⟩ : ∃ z : Fin 3, optMul (some c) (some pj) = some z := by
        cases hval : optMul (some c) (some pj) with
        | none => exact absurd hval (optMul_ne_none_of_ne hc)
        | some z => exact ⟨z, rfl⟩
      have hvalj : optMulLabel (pairLabel i j pi c) P j = some z := by
        show optMul (pairLabel i j pi c j) (P j) = _
        rw [pairLabel_apply, if_neg (Ne.symm hij), if_pos rfl, hpj, hz]
      have hcz : c ≠ z := by
        intro hcc
        exact optMul_some_ne_left c pj hc (by rw [hz, hcc])
      have hanti : optPhaseProd (pairLabel i j pi c) (optMulLabel (pairLabel i j pi c) P) ≠
          optPhaseProd (optMulLabel (pairLabel i j pi c) P) (pairLabel i j pi c) := by
        refine optPhaseProd_ne_of_unique_site j ⟨c, z, ?_, hvalj, hcz⟩ ?_
        · rw [pairLabel_apply, if_neg (Ne.symm hij), if_pos rfl]
        · intro t htj
          by_cases hti : t = i
          · exact Or.inr (Or.inl (by rw [hti, hvali]))
          · exact Or.inl (by rw [pairLabel_apply, if_neg hti, if_neg htj])
      have hres := hclosed _ _ hQmem hPmem hanti
      rwa [optMulLabel_optMulLabel_self] at hres

end Generation

end GaloisForLFunctions.HTGeometry
