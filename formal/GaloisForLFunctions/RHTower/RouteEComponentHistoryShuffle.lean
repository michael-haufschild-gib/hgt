import GaloisForLFunctions.HTGeometry.TupleHistogramCount
import GaloisForLFunctions.RHTower.RouteEUniformFibreShuffle

/-!
# Route E component-history shuffle

This file makes the replica-shuffle producer literal.  A history is a finite tuple of joint
component labels.  Its shuffle cell retains exactly the histogram of every component.  We prove
the exact orbit cardinality, the anchored one-component counting ratio, and the resulting product
law for an anchored joint label.  No probability primitive or asymptotic approximation is used.
-/

namespace RHTower

open scoped BigOperators Nat

noncomputable section

open GaloisForLFunctions.HTGeometry

section OneComponentCounting

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A permutation of replica slots leaves a tuple histogram unchanged. -/
omit [Fintype I] in
theorem routeE_tupleHistogram_comp_perm {m : ℕ}
    (f : Fin m → I) (e : Equiv.Perm (Fin m)) :
    tupleHistogram (fun r => f (e r)) = tupleHistogram f := by
  funext i
  simp only [tupleHistogram, Finset.card_filter]
  exact Equiv.sum_comp e (fun r => if f r = i then 1 else 0)

/-- Decreasing one positive histogram coordinate gives the exact multinomial ratio. -/
theorem routeE_multinomial_pred_ratio
    (m : ℕ) (k : I → ℕ) (i : I)
    (hk : ∑ j, k j = m) (hki : k i ≠ 0) :
    m * Nat.multinomial Finset.univ (Function.update k i (k i - 1)) =
      k i * Nat.multinomial Finset.univ k := by
  classical
  let k' := Function.update k i (k i - 1)
  have hmpos : 0 < m := by
    have hle : k i ≤ ∑ j, k j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hk'sum : ∑ j, k' j = m - 1 := by
    dsimp [k']
    rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.erase_eq]
    have hsplit : ∑ j ∈ Finset.univ.erase i, k j + k i = ∑ j, k j :=
      Finset.sum_erase_add _ _ (Finset.mem_univ i)
    omega
  let P := ∏ j, (k j)!
  let P' := ∏ j, (k' j)!
  have hP : P = k i * P' := by
    dsimp [P, P', k']
    calc
      (∏ j, (k j)!) = (k i)! * ∏ j ∈ Finset.univ.erase i, (k j)! :=
        (Finset.mul_prod_erase (Finset.univ : Finset I) (fun j => (k j)!)
          (Finset.mem_univ i)).symm
      _ = k i * ((k i - 1)! * ∏ j ∈ Finset.univ.erase i, (k j)!) := by
        rw [← Nat.mul_factorial_pred hki]
        ring
      _ = k i * ∏ j, (Function.update k i (k i - 1) j)! := by
        congr 1
        rw [← Finset.mul_prod_erase (Finset.univ : Finset I)
          (fun j => (Function.update k i (k i - 1) j)!) (Finset.mem_univ i)]
        rw [Function.update_self]
        apply congrArg ((k i - 1)! * ·)
        apply Finset.prod_congr rfl
        intro j hj
        rw [Function.update_of_ne]
        exact (Finset.mem_erase.mp hj).1
  have hspec := Nat.multinomial_spec (Finset.univ : Finset I) k
  have hspec' := Nat.multinomial_spec (Finset.univ : Finset I) k'
  have hspecP : P * Nat.multinomial Finset.univ k = m ! := by
    simpa [P, hk] using hspec
  have hspecP' : P' * Nat.multinomial Finset.univ k' = (m - 1)! := by
    simpa [P', hk'sum] using hspec'
  have hfact : m ! = m * (m - 1)! :=
    (Nat.mul_factorial_pred (Nat.ne_of_gt hmpos)).symm
  have hPeq : P * (m * Nat.multinomial Finset.univ k') =
      P * (k i * Nat.multinomial Finset.univ k) := by
    rw [hP]
    calc
      k i * P' * (m * Nat.multinomial Finset.univ k') =
          k i * m * (P' * Nat.multinomial Finset.univ k') := by ring
      _ = k i * m * (m - 1)! := by rw [hspecP']
      _ = k i * (m !) := by rw [hfact]; ring
      _ = k i * (P * Nat.multinomial Finset.univ k) := by rw [hspecP]
      _ = k i * P * Nat.multinomial Finset.univ k := by ring
      _ = k i * P' * (k i * Nat.multinomial Finset.univ k) := by rw [hP]; ring
  exact Nat.mul_left_cancel (by positivity : 0 < P) hPeq

/-- Number of histogram-realizing tuples whose distinguished first slot equals `i`. -/
theorem routeE_card_tupleHistogram_fiber_anchor_zero
    (m : ℕ) (k : I → ℕ) (i : I) (hk : ∑ j, k j = m + 1) :
    ((Finset.univ.filter fun f : Fin (m + 1) → I => tupleHistogram f = k).filter
        fun f => f 0 = i).card =
      if k i = 0 then 0 else
        Nat.multinomial Finset.univ (Function.update k i (k i - 1)) := by
  classical
  by_cases hki : k i = 0
  · rw [if_pos hki]
    refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem fun f hf => ?_)
    rw [Finset.mem_filter, Finset.mem_filter] at hf
    obtain ⟨⟨-, hhist⟩, hf0⟩ := hf
    have hpos : 0 < tupleHistogram f i := by
      refine Finset.card_pos.mpr ⟨0, ?_⟩
      simp [hf0]
    rw [hhist, hki] at hpos
    omega
  · rw [if_neg hki]
    have hupd : ∑ j, Function.update k i (k i - 1) j = m := by
      rw [Finset.sum_update_of_mem (Finset.mem_univ i), ← Finset.erase_eq]
      have hsplit : ∑ j ∈ Finset.univ.erase i, k j + k i = ∑ j, k j :=
        Finset.sum_erase_add _ _ (Finset.mem_univ i)
      have hki' : 1 ≤ k i := Nat.one_le_iff_ne_zero.mpr hki
      omega
    rw [← card_tupleHistogram_fiber m (Function.update k i (k i - 1)) hupd]
    refine Finset.card_nbij' (fun f => Fin.tail f) (fun g => Fin.cons i g) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
      obtain ⟨hhist, hf0⟩ := hf
      funext j
      have hcons := tupleHistogram_cons (i := f 0) (g := Fin.tail f) (j := j)
      rw [Fin.cons_self_tail, hhist, hf0] at hcons
      by_cases hj : i = j
      · subst hj
        rw [if_pos rfl] at hcons
        rw [Function.update_self]
        omega
      · rw [if_neg hj] at hcons
        rw [Function.update_of_ne (fun h => hj h.symm)]
        omega
    · intro g hg
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      refine ⟨?_, by simp⟩
      funext j
      rw [tupleHistogram_cons, hg]
      by_cases hj : i = j
      · subst hj
        rw [Function.update_self, if_pos rfl]
        omega
      · rw [Function.update_of_ne (fun h => hj h.symm), if_neg hj, Nat.add_zero]
    · intro f hf
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      show Fin.cons i (Fin.tail f) = f
      rw [← hf.2]
      exact Fin.cons_self_tail f
    · intro g _
      simp

/-- Exact anchored marginal on one histogram fibre. -/
theorem routeE_tupleHistogram_anchor_zero_ratio
    (m : ℕ) (k : I → ℕ) (i : I) (hk : ∑ j, k j = m + 1) :
    ((((Finset.univ.filter fun f : Fin (m + 1) → I => tupleHistogram f = k).filter
          fun f => f 0 = i).card : ℝ) /
        ((Finset.univ.filter fun f : Fin (m + 1) → I => tupleHistogram f = k).card : ℝ)) =
      (k i : ℝ) / (m + 1 : ℕ) := by
  classical
  rw [card_tupleHistogram_fiber (m + 1) k hk,
    routeE_card_tupleHistogram_fiber_anchor_zero m k i hk]
  have hM : (Nat.multinomial Finset.univ k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.multinomial_pos Finset.univ k))
  have hm : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  by_cases hki : k i = 0
  · simp [hki]
  · rw [if_neg hki]
    apply (div_eq_div_iff hM hm).2
    have hratio := routeE_multinomial_pred_ratio (m + 1) k i hk hki
    exact_mod_cast (by simpa [mul_comm] using hratio)

end OneComponentCounting

section ComponentHistories

variable {C : Type*} [Fintype C] [DecidableEq C]
variable (J : C → Type*) [∀ c, Fintype (J c)] [∀ c, DecidableEq (J c)]

/-- Finite joint component history. -/
abbrev RouteEComponentHistory (m : ℕ) := Fin m → (∀ c, J c)

/-- Complete componentwise histogram retained by the shuffle. -/
def routeEComponentHistoryLabel {m : ℕ} (x : RouteEComponentHistory J m) :
    ∀ c, J c → ℕ := fun c => tupleHistogram (fun r => x r c)

/-- Histories realizing a declared family of component histograms. -/
def routeEComponentHistogramCell (m : ℕ) (k : ∀ c, J c → ℕ) :
    Finset (RouteEComponentHistory J m) :=
  Finset.univ.filter fun x => ∀ c, tupleHistogram (fun r => x r c) = k c

/-- Relabel a component history by swapping two distinguished slots. -/
def routeEComponentHistoryAnchorSwap {m : ℕ} (r₀ r : Fin m)
    (x : RouteEComponentHistory J m) : RouteEComponentHistory J m :=
  fun s c => x (Equiv.swap r₀ r s) c

theorem routeEComponentHistoryAnchorSwap_mem_cell_iff
    {m : ℕ} (k : ∀ c, J c → ℕ) (r₀ r : Fin m) (x : RouteEComponentHistory J m) :
    routeEComponentHistoryAnchorSwap J r₀ r x ∈ routeEComponentHistogramCell J m k ↔
      x ∈ routeEComponentHistogramCell J m k := by
  classical
  simp only [routeEComponentHistogramCell, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h c
  · have hc := h c
    change tupleHistogram (fun s => x (Equiv.swap r₀ r s) c) = k c at hc
    rw [routeE_tupleHistogram_comp_perm (fun s => x s c) (Equiv.swap r₀ r)] at hc
    exact hc
  · change tupleHistogram (fun s => x (Equiv.swap r₀ r s) c) = k c
    exact (routeE_tupleHistogram_comp_perm (fun s => x s c) (Equiv.swap r₀ r)).trans (h c)

/-- Exact cardinality of a component-history shuffle cell. -/
theorem routeE_componentHistoryOrbit_card
    {m : ℕ} (x : RouteEComponentHistory J m) :
    (routeEUniformFibre (routeEComponentHistoryLabel J) x).card =
      ∏ c, Nat.multinomial Finset.univ (routeEComponentHistoryLabel J x c) := by
  classical
  have hk : ∀ c, ∑ a, routeEComponentHistoryLabel J x c a = m := by
    intro c
    exact sum_tupleHistogram (fun r => x r c)
  simpa [routeEUniformFibre, routeEComponentHistoryLabel, funext_iff] using
    (card_componentHistogram_fiber (J := J) m
      (routeEComponentHistoryLabel J x) hk)

/-- A component-histogram cell has the product multinomial cardinality. -/
theorem routeE_componentHistogramCell_card
    (m : ℕ) (k : ∀ c, J c → ℕ) (hk : ∀ c, ∑ a, k c a = m) :
    (routeEComponentHistogramCell J m k).card =
      ∏ c, Nat.multinomial Finset.univ (k c) := by
  exact card_componentHistogram_fiber m k hk

/-- Anchoring a joint label factorizes the component-histogram cell into independent anchored
one-component fibres. -/
theorem routeE_componentHistogramCell_anchor_zero_card
    (m : ℕ) (k : ∀ c, J c → ℕ) (a : ∀ c, J c) :
    ((routeEComponentHistogramCell J (m + 1) k).filter fun x => x 0 = a).card =
      ∏ c, (((Finset.univ.filter fun g : Fin (m + 1) → J c =>
          tupleHistogram g = k c).filter fun g => g 0 = a c).card) := by
  classical
  rw [← Fintype.card_piFinset]
  refine Finset.card_nbij' (fun x c r => x r c) (fun F r c => F c r) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter, routeEComponentHistogramCell,
      Finset.mem_univ, true_and, Fintype.mem_piFinset] at hx ⊢
    obtain ⟨hhist, hanchor⟩ := hx
    intro c
    exact ⟨hhist c, congrFun hanchor c⟩
  · intro F hF
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] at hF
    simp only [Finset.mem_coe, Finset.mem_filter, routeEComponentHistogramCell,
      Finset.mem_univ, true_and]
    refine ⟨fun c => (hF c).1, ?_⟩
    funext c
    exact (hF c).2
  · intro x _
    rfl
  · intro F _
    rfl

/-- **Exact orbit slot marginal.**  Under the uniform law on a component-histogram cell, the
distinguished joint slot is the product of its component empirical marginals. -/
theorem routeE_componentHistogram_anchor_zero_joint_ratio
    (m : ℕ) (k : ∀ c, J c → ℕ) (a : ∀ c, J c)
    (hk : ∀ c, ∑ b, k c b = m + 1) :
    ((((routeEComponentHistogramCell J (m + 1) k).filter fun x => x 0 = a).card : ℝ) /
        ((routeEComponentHistogramCell J (m + 1) k).card : ℝ)) =
      ∏ c, (k c (a c) : ℝ) / (m + 1 : ℕ) := by
  classical
  rw [routeE_componentHistogramCell_anchor_zero_card J m k a,
    routeE_componentHistogramCell_card J (m + 1) k hk]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro c _hc
  simpa [card_tupleHistogram_fiber (m + 1) (k c) (hk c)] using
    (routeE_tupleHistogram_anchor_zero_ratio m (k c) (a c) (hk c))

/-- **Exact anchored character productization.**  A product character averaged over a complete
component-histogram cell is the product of its empirical one-component means. -/
theorem routeE_componentHistogram_anchor_zero_character_mean
    (m : ℕ) (k : ∀ c, J c → ℕ) (chi : ∀ c, J c → ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1) :
    ((∑ x ∈ routeEComponentHistogramCell J (m + 1) k,
          ∏ c, chi c (x 0 c)) /
        ((routeEComponentHistogramCell J (m + 1) k).card : ℝ)) =
      ∏ c, ∑ b, ((k c b : ℝ) / (m + 1 : ℕ)) * chi c b := by
  classical
  let cell := routeEComponentHistogramCell J (m + 1) k
  change ((∑ x ∈ cell, ∏ c, chi c (x 0 c)) / (cell.card : ℝ)) = _
  have hgroup :
      (∑ x ∈ cell, ∏ c, chi c (x 0 c)) =
        ∑ a, (((cell.filter fun x => x 0 = a).card : ℕ) : ℝ) *
          ∏ c, chi c (a c) := by
    have h := Finset.sum_fiberwise_of_maps_to
      (s := cell) (t := (Finset.univ : Finset (∀ c, J c)))
      (g := fun x => x 0) (fun _ _ => Finset.mem_univ _) (fun x => ∏ c, chi c (x 0 c))
    rw [← h]
    apply Finset.sum_congr rfl
    intro a _ha
    calc
      (∑ x ∈ cell with x 0 = a, ∏ c, chi c (x 0 c)) =
          ∑ _x ∈ cell.filter (fun x => x 0 = a), ∏ c, chi c (a c) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(Finset.mem_filter.mp hx).2]
      _ = (((cell.filter fun x => x 0 = a).card : ℕ) : ℝ) *
          ∏ c, chi c (a c) := by simp
  rw [hgroup, Finset.sum_div]
  calc
    (∑ a : ∀ c, J c, ((((cell.filter fun x => x 0 = a).card : ℕ) : ℝ) *
          ∏ c, chi c (a c)) / (cell.card : ℝ)) =
        ∑ a : ∀ c, J c, (∏ c, (k c (a c) : ℝ) / (m + 1 : ℕ)) *
          ∏ c, chi c (a c) := by
      apply Finset.sum_congr rfl
      intro a _ha
      have hr := routeE_componentHistogram_anchor_zero_joint_ratio J m k a hk
      change ((((cell.filter fun x => x 0 = a).card : ℕ) : ℝ) / (cell.card : ℝ)) = _ at hr
      calc
        ((((cell.filter fun x => x 0 = a).card : ℕ) : ℝ) *
            ∏ c, chi c (a c)) / (cell.card : ℝ) =
            ((((cell.filter fun x => x 0 = a).card : ℕ) : ℝ) / (cell.card : ℝ)) *
              ∏ c, chi c (a c) := by ring
        _ = _ := by rw [hr]
    _ = ∑ a : ∀ c, J c,
        ∏ c, (((k c (a c) : ℝ) / (m + 1 : ℕ)) * chi c (a c)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.prod_mul_distrib]
    _ = ∏ c, ∑ b, ((k c b : ℝ) / (m + 1 : ℕ)) * chi c b := by
      symm
      simpa using (Finset.prod_univ_sum
        (fun c => (Finset.univ : Finset (J c)))
        (fun c b => ((k c b : ℝ) / (m + 1 : ℕ)) * chi c b))

/-- Equivalent count-sum form of anchored character productization. -/
theorem routeE_componentHistogram_anchor_zero_character_mean_count_sum
    (m : ℕ) (k : ∀ c, J c → ℕ) (chi : ∀ c, J c → ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1) :
    ((∑ x ∈ routeEComponentHistogramCell J (m + 1) k,
          ∏ c, chi c (x 0 c)) /
        ((routeEComponentHistogramCell J (m + 1) k).card : ℝ)) =
      ∏ c, (1 / (m + 1 : ℕ)) * ∑ b, (k c b : ℝ) * chi c b := by
  rw [routeE_componentHistogram_anchor_zero_character_mean J m k chi hk]
  apply Finset.prod_congr rfl
  intro c _hc
  calc
    (∑ b, ((k c b : ℝ) / (m + 1 : ℕ)) * chi c b) =
        ∑ b, (1 / (m + 1 : ℕ)) * ((k c b : ℝ) * chi c b) := by
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (1 / (m + 1 : ℕ)) * ∑ b, (k c b : ℝ) * chi c b := by
      rw [Finset.mul_sum]

/-- Swapping replica labels transports any anchored product-character sum to the zero anchor. -/
theorem routeE_componentHistogram_character_sum_eq_zero_anchor
    (m : ℕ) (k : ∀ c, J c → ℕ) (chi : ∀ c, J c → ℝ) (r : Fin (m + 1)) :
    (∑ x ∈ routeEComponentHistogramCell J (m + 1) k,
        ∏ c, chi c (x r c)) =
      ∑ x ∈ routeEComponentHistogramCell J (m + 1) k,
        ∏ c, chi c (x 0 c) := by
  classical
  let swapHistory := routeEComponentHistoryAnchorSwap J 0 r
  have hmem : ∀ x, x ∈ routeEComponentHistogramCell J (m + 1) k →
      swapHistory x ∈ routeEComponentHistogramCell J (m + 1) k := by
    intro x hx
    exact (routeEComponentHistoryAnchorSwap_mem_cell_iff J k 0 r x).2 hx
  refine Finset.sum_bij' (fun x _ => swapHistory x) (fun x _ => swapHistory x)
    hmem hmem ?_ ?_ ?_
  · intro x _hx
    funext s c
    simp [swapHistory, routeEComponentHistoryAnchorSwap]
  · intro x _hx
    funext s c
    simp [swapHistory, routeEComponentHistoryAnchorSwap]
  · intro x _hx
    simp [swapHistory, routeEComponentHistoryAnchorSwap]

/-- Theorem B for an arbitrary distinguished replica slot. -/
theorem routeE_componentHistogram_anchor_character_mean_count_sum
    (m : ℕ) (k : ∀ c, J c → ℕ) (chi : ∀ c, J c → ℝ)
    (hk : ∀ c, ∑ b, k c b = m + 1) (r : Fin (m + 1)) :
    ((∑ x ∈ routeEComponentHistogramCell J (m + 1) k,
          ∏ c, chi c (x r c)) /
        ((routeEComponentHistogramCell J (m + 1) k).card : ℝ)) =
      ∏ c, (1 / (m + 1 : ℕ)) * ∑ b, (k c b : ℝ) * chi c b := by
  rw [routeE_componentHistogram_character_sum_eq_zero_anchor J m k chi r]
  exact routeE_componentHistogram_anchor_zero_character_mean_count_sum J m k chi hk

/-- Exact arbitrary-anchor joint slot marginal, obtained as the product of component indicator
characters. -/
theorem routeE_componentHistogram_anchor_joint_ratio
    (m : ℕ) (k : ∀ c, J c → ℕ) (a : ∀ c, J c)
    (hk : ∀ c, ∑ b, k c b = m + 1) (r : Fin (m + 1)) :
    ((((routeEComponentHistogramCell J (m + 1) k).filter fun x => x r = a).card : ℝ) /
        ((routeEComponentHistogramCell J (m + 1) k).card : ℝ)) =
      ∏ c, (k c (a c) : ℝ) / (m + 1 : ℕ) := by
  classical
  let chi : ∀ c, J c → ℝ := fun c b => if b = a c then 1 else 0
  have hmean := routeE_componentHistogram_anchor_character_mean_count_sum J m k chi hk r
  have hleft :
      (∑ x ∈ routeEComponentHistogramCell J (m + 1) k, ∏ c, chi c (x r c)) =
        (((routeEComponentHistogramCell J (m + 1) k).filter fun x => x r = a).card : ℕ) := by
    calc
      (∑ x ∈ routeEComponentHistogramCell J (m + 1) k, ∏ c, chi c (x r c)) =
          ∑ x ∈ routeEComponentHistogramCell J (m + 1) k,
            if x r = a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hxa : x r = a
        · simp [chi, hxa]
        · have hexists : ∃ c, x r c ≠ a c := by
            by_contra h
            push Not at h
            exact hxa (funext h)
          obtain ⟨c, hc⟩ := hexists
          simp [chi, hxa, hc, Finset.prod_eq_zero (Finset.mem_univ c)]
      _ = _ := by simp
  rw [hleft] at hmean
  calc
    ((((routeEComponentHistogramCell J (m + 1) k).filter fun x => x r = a).card : ℝ) /
        ((routeEComponentHistogramCell J (m + 1) k).card : ℝ)) =
        ∏ c, (1 / (m + 1 : ℕ)) * ∑ b, (k c b : ℝ) * chi c b := hmean
    _ = ∏ c, (k c (a c) : ℝ) / (m + 1 : ℕ) := by
      apply Finset.prod_congr rfl
      intro c _hc
      simp [chi]
      ring

/-- The component-history shuffle is the generic exact symmetric bistochastic projection. -/
theorem routeE_componentHistoryKernel_projection
    {m : ℕ} [Nonempty (RouteEComponentHistory J m)] :
    (∀ x y : RouteEComponentHistory J m,
      routeEUniformFibreKernel (routeEComponentHistoryLabel J) x y =
        routeEUniformFibreKernel (routeEComponentHistoryLabel J) y x) ∧
    (∀ x : RouteEComponentHistory J m,
      ∑ y, routeEUniformFibreKernel (routeEComponentHistoryLabel J) x y = 1) ∧
    (∀ y : RouteEComponentHistory J m,
      ∑ x, routeEUniformFibreKernel (routeEComponentHistoryLabel J) x y = 1) ∧
    (∀ x y : RouteEComponentHistory J m,
      ∑ z, routeEUniformFibreKernel (routeEComponentHistoryLabel J) x z *
          routeEUniformFibreKernel (routeEComponentHistoryLabel J) z y =
        routeEUniformFibreKernel (routeEComponentHistoryLabel J) x y) := by
  classical
  exact ⟨routeEUniformFibreKernel_symm _, routeEUniformFibreKernel_row_sum _,
    routeEUniformFibreKernel_column_sum _, routeEUniformFibreKernel_idempotent _⟩

end ComponentHistories

section BinaryEntropyFirewall

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Binary presence character: absent is positive, present is negative. -/
def routeEBinaryPresenceCharacter (b : Bool) : ℝ := if b then -1 else 1

/-- One active occurrence in every binary component creates an orbit of cardinality `M^|C|`.
Thus power-size arrangement entropy is compatible with a completely explicit anchored bias. -/
theorem routeE_binary_singleton_component_cell_card
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hone : ∀ c, k c true = 1) :
    (routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k).card =
      (m + 1) ^ Fintype.card C := by
  classical
  rw [routeE_componentHistogramCell_card (fun _ : C => Bool) (m + 1) k hk]
  calc
    (∏ c, Nat.multinomial Finset.univ (k c)) = ∏ _c : C, (m + 1) := by
      apply Finset.prod_congr rfl
      intro c _hc
      have hsum : k c true + k c false = m + 1 := by
        simpa [Fintype.sum_bool] using hk c
      rw [Fintype.univ_bool,
        Nat.binomial_one (by decide : true ≠ false) (hone c)]
      rw [hone c] at hsum
      omega
    _ = (m + 1) ^ Fintype.card C := by simp

/-- **Entropy firewall.**  On the same power-size cell, the exact anchored parity mean is
`(1 - 2/M)^|C|`; orbit cardinality alone therefore contains no parity-mixing theorem. -/
theorem routeE_binary_singleton_component_character_mean
    (m : ℕ) (k : C → Bool → ℕ)
    (hk : ∀ c, ∑ b, k c b = m + 1)
    (hone : ∀ c, k c true = 1) :
    ((∑ x ∈ routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k,
          ∏ c, routeEBinaryPresenceCharacter (x 0 c)) /
        ((routeEComponentHistogramCell (fun _ : C => Bool) (m + 1) k).card : ℝ)) =
      ((1 : ℝ) - 2 / ((m + 1 : ℕ) : ℝ)) ^ Fintype.card C := by
  rw [routeE_componentHistogram_anchor_zero_character_mean_count_sum
    (fun _ : C => Bool) m k (fun _ => routeEBinaryPresenceCharacter) hk]
  calc
    (∏ c, (1 / (m + 1 : ℕ)) *
        ∑ b, (k c b : ℝ) * routeEBinaryPresenceCharacter b) =
        ∏ _c : C, ((1 : ℝ) - 2 / ((m + 1 : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro c _hc
      have hsum : k c true + k c false = m + 1 := by
        simpa [Fintype.sum_bool] using hk c
      have hfalse : k c false = m := by
        rw [hone c] at hsum
        omega
      rw [Fintype.sum_bool, hone c, hfalse]
      simp [routeEBinaryPresenceCharacter]
      field_simp
      ring
    _ = ((1 : ℝ) - 2 / ((m + 1 : ℕ) : ℝ)) ^ Fintype.card C := by simp

end BinaryEntropyFirewall

end

end RHTower
