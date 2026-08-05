import GaloisForLFunctions.HTGeometry.FullPauliCollectiveCasimir
import GaloisForLFunctions.HTGeometry.PermutationSumIndependence

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def replicaMoveMatrix (r d : ℕ) (b a : Fin d) :
    Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ :=
  fun x y => ∑ j : Fin r, if y j = a ∧ x = Function.update y j b then 1 else 0

theorem finiteReplicaCollectiveMatrix_single_eq_replicaMoveMatrix
    (r d : ℕ) (b a : Fin d) :
    finiteReplicaCollectiveMatrix (Fin r) (Fin d) (Matrix.single b a 1) =
      replicaMoveMatrix r d b a := by
  ext x y
  rw [finiteReplicaCollectiveMatrix]
  simp only [Matrix.sum_apply, replicaMoveMatrix]
  apply Finset.sum_congr rfl
  intro j _
  rw [finiteTensorSingleSiteMatrix_apply]
  simp only [Matrix.single_apply, Matrix.one_apply]
  by_cases h : y j = a ∧ x = Function.update y j b
  · rw [if_pos h]
    rcases h with ⟨hya, rfl⟩
    rw [if_pos ⟨by simp, hya.symm⟩, one_mul]
    apply Finset.prod_eq_one
    intro k hk
    rw [if_pos]
    simp [Finset.ne_of_mem_erase hk]
  · rw [if_neg h]
    by_cases hlocal : b = x j ∧ a = y j
    · rw [if_pos hlocal, one_mul]
      have hdiff : ∃ k ∈ Finset.univ.erase j, x k ≠ y k := by
        by_contra hn
        push Not at hn
        apply h
        refine ⟨hlocal.2.symm, ?_⟩
        funext k
        by_cases hkj : k = j
        · subst k
          simp [hlocal.1]
        · simp [hkj, hn k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩)]
      obtain ⟨k, hk, hne⟩ := hdiff
      exact Finset.prod_eq_zero hk (if_neg hne)
    · rw [if_neg hlocal, zero_mul]

theorem replicaMoveMatrix_mul_apply
    (r d : ℕ) (b a : Fin d)
    (X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (x n : Fin r → Fin d) :
    (replicaMoveMatrix r d b a * X) x n =
      ∑ j : Fin r, if x j = b then X (Function.update x j a) n else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [replicaMoveMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hxb : x j = b
  · rw [if_pos hxb, Finset.sum_eq_single (Function.update x j a)]
    · simp [hxb]
    · intro z _ hz
      rw [if_neg]
      · simp
      · intro hcond
        apply hz
        rcases hcond with ⟨hzja, hx⟩
        funext k
        by_cases hkj : k = j
        · subst k
          simpa using hzja
        · have hxk := congrFun hx k
          simpa [hkj] using hxk.symm
    · simp
  · rw [if_neg hxb]
    apply Finset.sum_eq_zero
    intro z _
    rw [if_neg]
    · simp
    · intro hcond
      apply hxb
      have hxj := congrFun hcond.2 j
      simpa using hxj

theorem mul_replicaMoveMatrix_apply
    (r d : ℕ) (b a : Fin d)
    (X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ)
    (x n : Fin r → Fin d) :
    (X * replicaMoveMatrix r d b a) x n =
      ∑ j : Fin r, if n j = a then X x (Function.update n j b) else 0 := by
  rw [Matrix.mul_apply]
  simp_rw [replicaMoveMatrix, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hna : n j = a
  · rw [if_pos hna, Finset.sum_eq_single (Function.update n j b)]
    · simp [hna]
    · intro z _ hz
      rw [if_neg]
      · simp
      · intro hcond
        apply hz
        rcases hcond with ⟨hnja, hz⟩
        exact hz
    · simp
  · rw [if_neg hna]
    apply Finset.sum_eq_zero
    intro z _
    rw [if_neg]
    · simp
    · intro hcond
      exact hna hcond.1

def finiteReplicaCollectiveCommutant (r d : ℕ) :
    Submodule ℂ (Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) where
  carrier := {X | ∀ b a : Fin d,
    replicaMoveMatrix r d b a * X = X * replicaMoveMatrix r d b a}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY b a
    rw [Matrix.mul_add, Matrix.add_mul, hX b a, hY b a]
  smul_mem' := by
    intro c X hX b a
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using
      congrArg (fun Y => c • Y) (hX b a)

def replicaCount {r d : ℕ} (x : Fin r → Fin d) (a : Fin d) : ℕ :=
  ({j : Fin r | x j = a} : Finset (Fin r)).card

theorem sum_indicator_eq_replicaCount_mul
    {r d : ℕ} (x : Fin r → Fin d) (a : Fin d) (c : ℂ) :
    (∑ j : Fin r, if x j = a then c else 0) = (replicaCount x a : ℂ) * c := by
  classical
  rw [← Finset.sum_filter]
  simp [replicaCount]

theorem finiteReplicaCollectiveCommutant_entry_zero_of_count_ne
    {r d : ℕ}
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    (x n : Fin r → Fin d) (a : Fin d)
    (hne : replicaCount x a ≠ replicaCount n a) :
    X x n = 0 := by
  have hcomm := congrFun (congrFun (hX a a) x) n
  rw [replicaMoveMatrix_mul_apply, mul_replicaMoveMatrix_apply] at hcomm
  have hxupdate : ∀ j : Fin r, x j = a → Function.update x j a = x := by
    intro j hj
    rw [← hj]
    exact Function.update_eq_self j x
  have hnupdate : ∀ j : Fin r, n j = a → Function.update n j a = n := by
    intro j hj
    rw [← hj]
    exact Function.update_eq_self j n
  have hleft :
      (∑ j : Fin r, if x j = a then X (Function.update x j a) n else 0) =
        ∑ j : Fin r, if x j = a then X x n else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : x j = a
    · rw [if_pos hj, if_pos hj, hxupdate j hj]
    · rw [if_neg hj, if_neg hj]
  have hright :
      (∑ j : Fin r, if n j = a then X x (Function.update n j a) else 0) =
        ∑ j : Fin r, if n j = a then X x n else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : n j = a
    · rw [if_pos hj, if_pos hj, hnupdate j hj]
    · rw [if_neg hj, if_neg hj]
  rw [hleft, hright] at hcomm
  rw [sum_indicator_eq_replicaCount_mul,
    sum_indicator_eq_replicaCount_mul] at hcomm
  have hcast : (replicaCount x a : ℂ) ≠ replicaCount n a := by
    exact_mod_cast hne
  have hprod :
      ((replicaCount x a : ℂ) - replicaCount n a) * X x n = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact hcomm
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hcast)

def MatrixColumnZero {C : Type*} [Fintype C]
    (X : Matrix C C ℂ) (n : C) : Prop :=
  ∀ x, X x n = 0

theorem finiteReplicaCollectiveCommutant_move_column_sum_eq_zero
    {r d : ℕ}
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    {n : Fin r → Fin d} (hcol : MatrixColumnZero X n)
    (b a : Fin d) (x : Fin r → Fin d) :
    (∑ j : Fin r, if n j = a then X x (Function.update n j b) else 0) = 0 := by
  have hcomm := congrFun (congrFun (hX b a) x) n
  rw [replicaMoveMatrix_mul_apply, mul_replicaMoveMatrix_apply] at hcomm
  rw [← hcomm]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : x j = b
  · rw [if_pos hj, hcol]
  · rw [if_neg hj]

theorem finiteReplicaCollectiveCommutant_column_zero_update
    {r d : ℕ}
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    {n : Fin r → Fin d} (hn : Function.Injective n)
    (hcol : MatrixColumnZero X n)
    (j : Fin r) (b : Fin d) :
    MatrixColumnZero X (Function.update n j b) := by
  intro x
  have hsum := finiteReplicaCollectiveCommutant_move_column_sum_eq_zero
    hX hcol b (n j) x
  rw [Finset.sum_eq_single j] at hsum
  · simpa using hsum
  · intro k _ hkj
    rw [if_neg]
    intro h
    exact hkj (hn h)
  · simp

theorem finiteReplicaCollectiveCommutant_column_zero_swap_of_mem_mem
    {r d : ℕ}
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    {n : Fin r → Fin d} (hn : Function.Injective n)
    (hcol : MatrixColumnZero X n)
    {a b : Fin d} (hab : a ≠ b)
    {j k : Fin r} (hja : n j = a) (hkb : n k = b) :
    MatrixColumnZero X (fun q => Equiv.swap a b (n q)) := by
  have hjk : j ≠ k := by
    intro h
    subst k
    exact hab (hja.symm.trans hkb)
  let m := Function.update n j b
  let nswap : Fin r → Fin d := fun q => Equiv.swap a b (n q)
  have hmcol : MatrixColumnZero X m :=
    finiteReplicaCollectiveCommutant_column_zero_update hX hn hcol j b
  intro x
  have hsum := finiteReplicaCollectiveCommutant_move_column_sum_eq_zero
    hX hmcol a b x
  have hmj : m j = b := by simp [m]
  have hmk : m k = b := by simp [m, Ne.symm hjk, hkb]
  have hrecover : Function.update m j a = n := by
    funext q
    by_cases hqj : q = j
    · subst q
      simp [m, hja]
    · simp [m, hqj]
  have hswap : Function.update m k a = nswap := by
    funext q
    by_cases hqj : q = j
    · subst q
      have hu : Function.update m k a j = m j := by simp [hjk]
      rw [hu, hmj]
      change b = Equiv.swap a b (n j)
      rw [hja, Equiv.swap_apply_left]
    · by_cases hqk : q = k
      · subst q
        simp [m, nswap, hkb]
      · have hna : n q ≠ a := by
          intro h
          exact hqj (hn (h.trans hja.symm))
        have hnb : n q ≠ b := by
          intro h
          exact hqk (hn (h.trans hkb.symm))
        have hu : Function.update m k a q = m q := by simp [hqk]
        have hm : m q = n q := by simp [m, hqj]
        rw [hu, hm]
        exact (Equiv.swap_apply_of_ne_of_ne hna hnb).symm
  have hterm : ∀ q : Fin r,
      (if m q = b then X x (Function.update m q a) else 0) =
        (if q = j then X x n else 0) +
          (if q = k then X x nswap else 0) := by
    intro q
    by_cases hqj : q = j
    · subst q
      rw [if_pos rfl, if_neg hjk, if_pos hmj, hrecover, add_zero]
    · rw [if_neg hqj]
      by_cases hqk : q = k
      · subst q
        rw [if_pos rfl, if_pos hmk, hswap, zero_add]
      · rw [if_neg hqk, zero_add, if_neg]
        intro hmq
        have hnqb : n q = b := by simpa [m, hqj] using hmq
        exact hqk (hn (hnqb.trans hkb.symm))
  rw [Finset.sum_congr rfl (fun q _ => hterm q)] at hsum
  simp only [Finset.sum_add_distrib] at hsum
  simp at hsum
  simpa [hcol x] using hsum

theorem finiteReplicaCollectiveCommutant_column_zero_swap
    {r d : ℕ}
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    {n : Fin r → Fin d} (hn : Function.Injective n)
    (hcol : MatrixColumnZero X n) (a b : Fin d) :
    MatrixColumnZero X (fun q => Equiv.swap a b (n q)) := by
  by_cases hab : a = b
  · subst b
    simpa using hcol
  by_cases ha : ∃ j, n j = a
  · obtain ⟨j, hja⟩ := ha
    by_cases hb : ∃ k, n k = b
    · obtain ⟨k, hkb⟩ := hb
      exact finiteReplicaCollectiveCommutant_column_zero_swap_of_mem_mem
        hX hn hcol hab hja hkb
    · have hupd := finiteReplicaCollectiveCommutant_column_zero_update
        hX hn hcol j b
      have heq : Function.update n j b = fun q => Equiv.swap a b (n q) := by
        funext q
        by_cases hqj : q = j
        · subst q
          simp [hja]
        · have hna : n q ≠ a := by
            intro h
            exact hqj (hn (h.trans hja.symm))
          have hnb : n q ≠ b := by
            intro h
            exact hb ⟨q, h⟩
          have hu : Function.update n j b q = n q := by simp [hqj]
          rw [hu]
          exact (Equiv.swap_apply_of_ne_of_ne hna hnb).symm
      rwa [heq] at hupd
  · by_cases hb : ∃ k, n k = b
    · obtain ⟨k, hkb⟩ := hb
      have hupd := finiteReplicaCollectiveCommutant_column_zero_update
        hX hn hcol k a
      have heq : Function.update n k a = fun q => Equiv.swap a b (n q) := by
        funext q
        by_cases hqk : q = k
        · subst q
          simp [hkb]
        · have hna : n q ≠ a := by
            intro h
            exact ha ⟨q, h⟩
          have hnb : n q ≠ b := by
            intro h
            exact hqk (hn (h.trans hkb.symm))
          have hu : Function.update n k a q = n q := by simp [hqk]
          rw [hu]
          exact (Equiv.swap_apply_of_ne_of_ne hna hnb).symm
      rwa [heq] at hupd
    · have heq : (fun q => Equiv.swap a b (n q)) = n := by
        funext q
        have hna : n q ≠ a := fun h => ha ⟨q, h⟩
        have hnb : n q ≠ b := fun h => hb ⟨q, h⟩
        exact Equiv.swap_apply_of_ne_of_ne hna hnb
      rwa [heq]

theorem finiteReplicaCollectiveCommutant_column_zero_perm
    {r d : ℕ}
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    {n : Fin r → Fin d} (hn : Function.Injective n)
    (hcol : MatrixColumnZero X n) (τ : Equiv.Perm (Fin d)) :
    MatrixColumnZero X (fun q => τ (n q)) := by
  induction τ using Equiv.Perm.swap_induction_on with
  | one => simpa using hcol
  | swap_mul τ a b hab ih =>
      have hinj : Function.Injective (fun q => τ (n q)) := τ.injective.comp hn
      have hswap := finiteReplicaCollectiveCommutant_column_zero_swap
        hX hinj ih a b
      simpa [mul_apply] using hswap

def canonicalReplicaInjection {r d : ℕ} (h : r ≤ d) : Fin r → Fin d :=
  Fin.castLE h

theorem canonicalReplicaInjection_injective {r d : ℕ} (h : r ≤ d) :
    Function.Injective (canonicalReplicaInjection h) := by
  exact Fin.castLE_injective h

theorem finiteReplicaCollectiveCommutant_all_injective_columns_zero
    {r d : ℕ} (hrd : r ≤ d)
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    (hbase : MatrixColumnZero X (canonicalReplicaInjection hrd))
    {n : Fin r → Fin d} (hn : Function.Injective n) :
    MatrixColumnZero X n := by
  let i := canonicalReplicaInjection hrd
  have hi : Function.Injective i := canonicalReplicaInjection_injective hrd
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_extending_pair i n hi hn
  have hp := finiteReplicaCollectiveCommutant_column_zero_perm hX hi hbase τ
  have heq : (fun q => τ (i q)) = n := by
    funext q
    exact hτ q
  rwa [heq] at hp

def replicaRange {r d : ℕ} (n : Fin r → Fin d) : Finset (Fin d) :=
  Finset.univ.image n

theorem replicaRange_card_le {r d : ℕ} (n : Fin r → Fin d) :
    (replicaRange n).card ≤ r := by
  simpa [replicaRange] using (Finset.card_image_le :
    (Finset.univ.image n).card ≤ Finset.univ.card)

theorem replicaRange_card_eq_of_injective {r d : ℕ}
    {n : Fin r → Fin d} (hn : Function.Injective n) :
    (replicaRange n).card = r := by
  simp [replicaRange, Finset.card_image_of_injective _ hn]

theorem injective_of_replicaRange_card_eq {r d : ℕ}
    {n : Fin r → Fin d} (hcard : (replicaRange n).card = r) :
    Function.Injective n := by
  have hinjOn : Set.InjOn n (Finset.univ : Finset (Fin r)) := by
    apply Finset.card_image_iff.mp
    simpa [replicaRange] using hcard
  intro j k hjk
  exact hinjOn (Finset.mem_univ j) (Finset.mem_univ k) hjk

theorem exists_duplicate_and_missing_of_replicaRange_card_lt
    {r d : ℕ} (hrd : r ≤ d) (n : Fin r → Fin d)
    (hlt : (replicaRange n).card < r) :
    ∃ j k : Fin r, j ≠ k ∧ n j = n k ∧
      ∃ b : Fin d, b ∉ replicaRange n := by
  have hmaps : Set.MapsTo n (Finset.univ : Finset (Fin r)) (replicaRange n) := by
    intro j _
    exact Finset.mem_image_of_mem n (Finset.mem_univ j)
  obtain ⟨j, _, k, _, hjk, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simpa using hlt) hmaps
  have hranged : (replicaRange n).card <
      (Finset.univ : Finset (Fin d)).card := by
    simpa using lt_of_lt_of_le hlt hrd
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hranged
  exact ⟨j, k, hjk, heq, b, hb⟩

theorem replicaRange_update_eq_insert_of_duplicate
    {r d : ℕ} (n : Fin r → Fin d) {j k : Fin r} {b : Fin d}
    (hjk : j ≠ k) (heq : n j = n k) (hb : b ∉ replicaRange n) :
    replicaRange (Function.update n j b) = insert b (replicaRange n) := by
  ext c
  simp only [replicaRange, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hqj : q = j
    · left
      subst q
      simpa using hq.symm
    · right
      refine ⟨q, ?_⟩
      simpa [hqj] using hq
  · rintro (rfl | ⟨q, hq⟩)
    · exact ⟨j, by simp⟩
    · by_cases hqj : q = j
      · refine ⟨k, ?_⟩
        have hkj : k ≠ j := Ne.symm hjk
        simp [hkj, ← heq, ← hq, hqj]
      · exact ⟨q, by simpa [hqj] using hq⟩

theorem replicaRange_card_update_eq_succ_of_duplicate
    {r d : ℕ} (n : Fin r → Fin d) {j k : Fin r} {b : Fin d}
    (hjk : j ≠ k) (heq : n j = n k) (hb : b ∉ replicaRange n) :
    (replicaRange (Function.update n j b)).card =
      (replicaRange n).card + 1 := by
  rw [replicaRange_update_eq_insert_of_duplicate n hjk heq hb]
  simp [hb, Nat.add_comm]

theorem finiteReplicaCollectiveCommutant_all_columns_zero
    {r d : ℕ} (hrd : r ≤ d)
    {X : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ}
    (hX : X ∈ finiteReplicaCollectiveCommutant r d)
    (hbase : MatrixColumnZero X (canonicalReplicaInjection hrd)) :
    ∀ n : Fin r → Fin d, MatrixColumnZero X n := by
  let P : ℕ → Prop := fun μ => ∀ n : Fin r → Fin d,
    r - (replicaRange n).card = μ → MatrixColumnZero X n
  have hP : ∀ μ, P μ := by
    intro μ
    induction μ using Nat.strong_induction_on with
    | h μ ih =>
      intro n hμ
      by_cases hninj : Function.Injective n
      · exact finiteReplicaCollectiveCommutant_all_injective_columns_zero
          hrd hX hbase hninj
      have hrangele := replicaRange_card_le n
      have hrangelt : (replicaRange n).card < r := by
        apply lt_of_le_of_ne hrangele
        intro heq
        exact hninj (injective_of_replicaRange_card_eq heq)
      obtain ⟨j₀, k₀, hjk, heq, b, hb⟩ :=
        exists_duplicate_and_missing_of_replicaRange_card_lt hrd n hrangelt
      let a := n j₀
      have hnk : n k₀ = a := heq.symm
      intro x
      by_cases hcounts : ∀ c : Fin d, replicaCount x c = replicaCount n c
      · have hnb : ∀ q : Fin r, n q ≠ b := by
          intro q hnqb
          apply hb
          exact Finset.mem_image_of_mem n (Finset.mem_univ q) |> (by simpa [replicaRange, hnqb] using ·)
        have hxb : ∀ q : Fin r, x q ≠ b := by
          intro q hxqb
          have hxpos : 0 < replicaCount x b := by
            rw [replicaCount, Finset.card_pos]
            exact ⟨q, by simp [hxqb]⟩
          have hnzero : replicaCount n b = 0 := by
            rw [replicaCount, Finset.card_eq_zero]
            ext q
            simp [hnb q]
          rw [hcounts b, hnzero] at hxpos
          omega
        have hxapos : 0 < replicaCount x a := by
          rw [hcounts a, replicaCount, Finset.card_pos]
          exact ⟨j₀, by simp [a]⟩
        obtain ⟨j, hj⟩ : ∃ j : Fin r, x j = a := by
          rw [replicaCount, Finset.card_pos] at hxapos
          obtain ⟨j, hj⟩ := hxapos
          exact ⟨j, (Finset.mem_filter.mp hj).2⟩
        let y := Function.update x j b
        have hcomm := congrFun (congrFun (hX b a) y) n
        rw [replicaMoveMatrix_mul_apply, mul_replicaMoveMatrix_apply] at hcomm
        have hleft :
            (∑ q : Fin r, if y q = b then X (Function.update y q a) n else 0) =
              X x n := by
          rw [Finset.sum_eq_single j]
          · have hyj : y j = b := by simp [y]
            have hrecover : Function.update y j a = x := by
              funext q
              by_cases hqj : q = j
              · subst q
                simp [y, hj]
              · simp [y, hqj]
            rw [if_pos hyj, hrecover]
          · intro q _ hqj
            rw [if_neg]
            intro hyqb
            have hxqb : x q = b := by simpa [y, hqj] using hyqb
            exact hxb q hxqb
          · simp
        have hright :
            (∑ q : Fin r, if n q = a then X y (Function.update n q b) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro q _
          by_cases hnqa : n q = a
          · rw [if_pos hnqa]
            obtain ⟨k, hqk, hqeq⟩ : ∃ k : Fin r, q ≠ k ∧ n q = n k := by
              by_cases hqj : q = j₀
              · exact ⟨k₀, hqj.trans_ne hjk, by simpa [hqj, a] using hnk.symm⟩
              · exact ⟨j₀, hqj, by simpa [a] using hnqa⟩
            have hcard := replicaRange_card_update_eq_succ_of_duplicate
              n hqk hqeq hb
            have hmeasure :
                r - (replicaRange (Function.update n q b)).card < μ := by
              rw [hcard, ← hμ]
              omega
            exact ih _ hmeasure (Function.update n q b) rfl y
          · rw [if_neg hnqa]
        rw [hleft, hright] at hcomm
        exact hcomm
      · push Not at hcounts
        obtain ⟨c, hc⟩ := hcounts
        exact finiteReplicaCollectiveCommutant_entry_zero_of_count_ne hX x n c hc
  intro n
  exact hP (r - (replicaRange n).card) n rfl

def finiteReplicaCollectiveCommutantEvaluation
    {r d : ℕ} (hrd : r ≤ d) :
    finiteReplicaCollectiveCommutant r d →ₗ[ℂ]
      (Equiv.Perm (Fin r) → ℂ) where
  toFun X σ := X.1
    (fun q => canonicalReplicaInjection hrd (σ q))
    (canonicalReplicaInjection hrd)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem replicaCount_eq_tupleCount_apply
    {r d : ℕ} (n : Fin r → Fin d) (a : Fin d) :
    replicaCount n a = tupleCount n a := by
  rw [replicaCount, tupleCount_apply]

theorem finiteReplicaCollectiveCommutant_base_column_zero_of_evaluation_zero
    {r d : ℕ} (hrd : r ≤ d)
    (X : finiteReplicaCollectiveCommutant r d)
    (heval : finiteReplicaCollectiveCommutantEvaluation hrd X = 0) :
    MatrixColumnZero X.1 (canonicalReplicaInjection hrd) := by
  let i := canonicalReplicaInjection hrd
  have hi : Function.Injective i := canonicalReplicaInjection_injective hrd
  intro x
  by_cases hcounts : ∀ c : Fin d, replicaCount x c = replicaCount i c
  · have htuple : tupleCount x = tupleCount i := by
      ext c
      simpa [replicaCount_eq_tupleCount_apply] using hcounts c
    obtain ⟨σ, hσ⟩ := exists_perm_of_tupleCount_eq hi htuple
    have hcoord := congrFun heval σ
    change X.1 (fun q => i (σ q)) i = 0 at hcoord
    subst x
    simpa [i] using hcoord
  · push Not at hcounts
    obtain ⟨c, hc⟩ := hcounts
    exact finiteReplicaCollectiveCommutant_entry_zero_of_count_ne X.2 x i c hc

theorem finiteReplicaCollectiveCommutantEvaluation_injective
    {r d : ℕ} (hrd : r ≤ d) :
    Function.Injective (finiteReplicaCollectiveCommutantEvaluation hrd) := by
  rw [← LinearMap.ker_eq_bot]
  ext X
  constructor
  · intro hX
    have heval : finiteReplicaCollectiveCommutantEvaluation hrd X = 0 := hX
    have hbase :=
      finiteReplicaCollectiveCommutant_base_column_zero_of_evaluation_zero hrd X heval
    have hall := finiteReplicaCollectiveCommutant_all_columns_zero hrd X.2 hbase
    apply Subtype.ext
    ext x n
    exact hall n x
  · intro hX
    subst X
    exact Submodule.zero_mem _

/-- Stable-range Schur--Weyl upper bound, proved only from matrix-unit
commutation: an `r`-replica collective commutant has dimension at most `r!`
whenever the one-particle dimension is at least `r`. -/
theorem finiteReplicaCollectiveCommutant_finrank_le_factorial
    {r d : ℕ} (hrd : r ≤ d) :
    Module.finrank ℂ (finiteReplicaCollectiveCommutant r d) ≤ Nat.factorial r := by
  calc
    Module.finrank ℂ (finiteReplicaCollectiveCommutant r d) ≤
        Module.finrank ℂ (Equiv.Perm (Fin r) → ℂ) :=
      LinearMap.finrank_le_finrank_of_injective
        (finiteReplicaCollectiveCommutantEvaluation_injective hrd)
    _ = Nat.factorial r := by
      simp [Fintype.card_perm]

end
end GaloisForLFunctions.HTGeometry
