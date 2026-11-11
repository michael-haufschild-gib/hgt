import Mathlib

/-!
# Entropy of finite laws

For a vector `p` on a finite type, `ent p = Σ_a −p_a log p_a` and `push F p` is its pushforward along
`F`. For nonnegative vectors:

* `ent (push F p) ≤ ent p` (`ent_push_le`), from subadditivity of `t ↦ −t log t`; equality along a
  bijection (`ent_push_equiv`);
* `ent p ≤ log |α|` for a probability vector (`ent_le_log_card`);
* **submodularity** `H(A,B,C) + H(C) ≤ H(A,C) + H(B,C)` (`ent_add_ent_le`): Gibbs' inequality
  against `q = p_{AC} p_{BC}/p_C`, whose total mass is that of `p`;
* **data processing** for `D(μ‖ν) = Σ μ log μ − μ log ν` (`kl_push_le`), fibre by fibre from Gibbs
  against `ν·m/n`;
* the **event inequality** `μ(A) log(1/ν(A)) ≤ D(μ‖ν) + log 2` (`mul_neg_log_le_kl_add_log_two`),
  data processing along `1_A` and the binary entropy bound;
* for `ν = μ_X ⊗ uniform`, `D(μ‖ν) = H(X) + log |Y| − H(X,Y)` (`kl_prod_uniform`), and an event
  whose sections have relative size `≤ δ` has `μ(A) log(1/δ) ≤ H(X) + log |Y| − H(X,Y) + log 2`
  (`mass_mul_neg_log_le`).

Gibbs' inequality is used termwise: `p − q ≤ p log p − p log q` whenever `q > 0` where `p > 0`
(`sub_le_mul_log_sub_mul_log`).
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Real

noncomputable section

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Shannon entropy `Σ_a −p_a log p_a`. -/
def ent (p : α → ℝ) : ℝ := ∑ a, negMulLog (p a)

/-- The pushforward of a vector along `F`. -/
def push [DecidableEq β] (F : α → β) (p : α → ℝ) (b : β) : ℝ :=
  ∑ a ∈ univ.filter (fun a => F a = b), p a

/-- The relative entropy `Σ μ log μ − μ log ν` (meaningful when `ν > 0` wherever `μ > 0`). -/
def kl (μ ν : α → ℝ) : ℝ := ∑ a, (μ a * log (μ a) - μ a * log (ν a))

theorem ent_eq (p : α → ℝ) : ent p = -∑ a, p a * log (p a) := by
  simp [ent, negMulLog, sum_neg_distrib]

omit [Fintype β] in
theorem push_nonneg [DecidableEq β] (F : α → β) {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (b : β) :
    0 ≤ push F p b :=
  sum_nonneg fun a _ => hp a

omit [Fintype β] in
theorem le_push [DecidableEq β] (F : α → β) {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (a : α) :
    p a ≤ push F p (F a) :=
  single_le_sum (f := p) (fun a _ => hp a) (mem_filter.mpr ⟨mem_univ a, rfl⟩)

theorem sum_push [DecidableEq β] (F : α → β) (p : α → ℝ) : ∑ b, push F p b = ∑ a, p a :=
  sum_fiberwise univ F p

/-- `Σ_t p_t G(F t) = Σ_b (push F p)(b) G(b)`. -/
theorem sum_mul_comp_eq [DecidableEq β] (F : α → β) (p : α → ℝ) (G : β → ℝ) :
    ∑ a, p a * G (F a) = ∑ b, push F p b * G b := by
  simp only [push, sum_mul]
  rw [← sum_fiberwise univ F fun a => p a * G (F a)]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a ha => ?_
  rw [(mem_filter.mp ha).2]

omit [Fintype γ] in
theorem push_push [DecidableEq β] [DecidableEq γ] (F : α → β) (G : β → γ) (p : α → ℝ) :
    push G (push F p) = push (fun a => G (F a)) p := by
  funext c
  have h := sum_mul_comp_eq F p fun b => if G b = c then 1 else 0
  simp only [mul_ite, mul_one, mul_zero] at h
  simp only [push, ← sum_filter] at h ⊢
  rw [← h]

omit [Fintype β] in
theorem push_equiv_apply [DecidableEq β] (e : α ≃ β) (p : α → ℝ) (b : β) :
    push e p b = p (e.symm b) := by
  have : univ.filter (fun a => e a = b) = {e.symm b} := by
    ext a
    simp [Equiv.apply_eq_iff_eq_symm_apply]
  rw [push, this, sum_singleton]

/-- The second marginal of a vector on a product. -/
theorem push_snd_apply [DecidableEq γ] (p : α × γ → ℝ) (c : γ) :
    push Prod.snd p c = ∑ a, p (a, c) := by
  rw [push, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  simp

/-- The first marginal of a vector on a product. -/
theorem push_fst_apply [DecidableEq α] (p : α × γ → ℝ) (a : α) :
    push Prod.fst p a = ∑ c, p (a, c) := by
  rw [push, sum_filter, Fintype.sum_prod_type]
  calc ∑ x, ∑ y, (if (x, y).1 = a then p (x, y) else 0)
      = ∑ x, (if x = a then ∑ y, p (x, y) else 0) :=
        sum_congr rfl fun x _ => by split_ifs <;> simp
    _ = ∑ c, p (a, c) := by simp

/-- `−(x+y) log(x+y) ≤ −x log x − y log y` for `x, y ≥ 0`. -/
theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    negMulLog (x + y) ≤ negMulLog x + negMulLog y := by
  have key : ∀ {u v : ℝ}, 0 ≤ u → 0 ≤ v → -(u * log (u + v)) ≤ negMulLog u := by
    intro u v hu hv
    rcases hu.eq_or_lt with rfl | hu'
    · simp
    · rw [negMulLog, neg_mul, neg_le_neg_iff]
      exact mul_le_mul_of_nonneg_left (log_le_log hu' (by linarith)) hu
  have h1 := key hx hy
  have h2 := key hy hx
  rw [add_comm y x] at h2
  rw [negMulLog]
  linarith

theorem negMulLog_sum_le {ι : Type*} (s : Finset ι) {p : ι → ℝ} (hp : ∀ i ∈ s, 0 ≤ p i) :
    negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, negMulLog (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    have hs : 0 ≤ ∑ i ∈ s, p i := sum_nonneg fun i hi => hp i (mem_insert_of_mem hi)
    exact (negMulLog_add_le (hp a (mem_insert_self a s)) hs).trans
      (add_le_add le_rfl (ih fun i hi => hp i (mem_insert_of_mem hi)))

/-- Coarsening does not increase entropy. -/
theorem ent_push_le [DecidableEq β] (F : α → β) {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) :
    ent (push F p) ≤ ent p := by
  rw [ent, ent, ← sum_fiberwise univ F fun a => negMulLog (p a)]
  exact sum_le_sum fun b _ => negMulLog_sum_le _ fun a _ => hp a

/-- Entropy is invariant under a bijection of the value set. -/
theorem ent_push_equiv [DecidableEq β] (e : α ≃ β) (p : α → ℝ) : ent (push e p) = ent p := by
  rw [ent, ent]
  simp only [push_equiv_apply]
  exact Equiv.sum_comp e.symm fun a => negMulLog (p a)

theorem ent_nonneg {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) : 0 ≤ ent p := by
  refine sum_nonneg fun a _ => negMulLog_nonneg (hp a) ?_
  rw [← hsum]
  exact single_le_sum (fun a _ => hp a) (mem_univ a)

/-- **Gibbs, termwise.** `p − q ≤ p log p − p log q` when `q > 0` wherever `p > 0`. -/
theorem sub_le_mul_log_sub_mul_log {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p → 0 < q) :
    p - q ≤ p * log p - p * log q := by
  rcases hp.eq_or_lt with rfl | hp'
  · simp [hq]
  · have hq' := hpq hp'
    have h := log_le_sub_one_of_pos (div_pos hq' hp')
    rw [log_div hq'.ne' hp'.ne'] at h
    have h2 := mul_le_mul_of_nonneg_left h hp'.le
    rw [mul_sub, mul_sub, mul_div_cancel₀ _ hp'.ne', mul_one] at h2
    linarith

/-- **Gibbs.** `Σ p − Σ q ≤ D(p‖q)`. -/
theorem sum_sub_sum_le_kl {p q : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpq : ∀ a, 0 < p a → 0 < q a) : ∑ a, p a - ∑ a, q a ≤ kl p q := by
  rw [← sum_sub_distrib, kl]
  exact sum_le_sum fun a _ => sub_le_mul_log_sub_mul_log (hp a) (hq a) (hpq a)

/-- Entropy of a probability vector is at most `log |α|`. -/
theorem ent_le_log_card {p : α → ℝ} (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) :
    ent p ≤ log (Fintype.card α) := by
  have hne : 0 < Fintype.card α := by
    rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
    · rw [Fintype.card_eq_zero_iff] at h
      simp [Finset.univ_eq_empty] at hsum
    · exact h
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast hne
  have h := sum_sub_sum_le_kl (q := fun _ => 1 / (Fintype.card α : ℝ)) hp
    (fun _ => by positivity) fun _ _ => by positivity
  have hq1 : ∑ _a : α, 1 / (Fintype.card α : ℝ) = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul, mul_one_div_cancel hc.ne']
  have hlog : ∑ a, p a * log (1 / (Fintype.card α : ℝ)) = -log (Fintype.card α) := by
    rw [← sum_mul, hsum, one_div, log_inv, one_mul]
  rw [hq1, hsum, sub_self, kl, sum_sub_distrib, hlog] at h
  rw [ent_eq]
  linarith

/-! ## Submodularity -/

section Submodular

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- **Submodularity.** `H(A,B,C) + H(C) ≤ H(A,C) + H(B,C)`. -/
theorem ent_add_ent_le {p : α × β × γ → ℝ} (hp : ∀ t, 0 ≤ p t) :
    ent p + ent (push (fun t => t.2.2) p)
      ≤ ent (push (fun t => (t.1, t.2.2)) p) + ent (push (fun t => (t.2.1, t.2.2)) p) := by
  set pAC := push (fun t : α × β × γ => (t.1, t.2.2)) p with hAC
  set pBC := push (fun t : α × β × γ => (t.2.1, t.2.2)) p with hBC
  set pC := push (fun t : α × β × γ => t.2.2) p with hC
  have hACn : ∀ u, 0 ≤ pAC u := push_nonneg _ hp
  have hBCn : ∀ u, 0 ≤ pBC u := push_nonneg _ hp
  have hCn : ∀ c, 0 ≤ pC c := push_nonneg _ hp
  set q : α × β × γ → ℝ := fun t => pAC (t.1, t.2.2) * pBC (t.2.1, t.2.2) / pC t.2.2 with hq
  have hqn : ∀ t, 0 ≤ q t := fun t => div_nonneg (mul_nonneg (hACn _) (hBCn _)) (hCn _)
  have hpos : ∀ t, 0 < p t → 0 < pAC (t.1, t.2.2) ∧ 0 < pBC (t.2.1, t.2.2) ∧ 0 < pC t.2.2 :=
    fun t ht => ⟨ht.trans_le (le_push _ hp t), ht.trans_le (le_push _ hp t),
      ht.trans_le (le_push _ hp t)⟩
  have hpq : ∀ t, 0 < p t → 0 < q t := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := hpos t ht
    exact div_pos (mul_pos h1 h2) h3
  have hmargA : ∀ c, ∑ a, pAC (a, c) = pC c := by
    intro c
    rw [← push_snd_apply, hAC, push_push]
  have hmargB : ∀ c, ∑ b, pBC (b, c) = pC c := by
    intro c
    rw [← push_snd_apply, hBC, push_push]
  -- the comparison vector has the mass of `p`
  have hinner : ∀ a c, ∑ b, pAC (a, c) * pBC (b, c) / pC c = pAC (a, c) * (pC c / pC c) := by
    intro a c
    rw [← sum_div, ← mul_sum, hmargB, mul_div_assoc]
  have hqsum : ∑ t, q t = ∑ t, p t := by
    calc ∑ t, q t = ∑ a, ∑ b, ∑ c, pAC (a, c) * pBC (b, c) / pC c := by
          simp only [hq, Fintype.sum_prod_type]
      _ = ∑ a, ∑ c, ∑ b, pAC (a, c) * pBC (b, c) / pC c :=
          sum_congr rfl fun a _ => sum_comm
      _ = ∑ a, ∑ c, pAC (a, c) * (pC c / pC c) :=
          sum_congr rfl fun a _ => sum_congr rfl fun c _ => hinner a c
      _ = ∑ c, ∑ a, pAC (a, c) * (pC c / pC c) := sum_comm
      _ = ∑ c, pC c * (pC c / pC c) := by
          refine sum_congr rfl fun c _ => ?_
          rw [← sum_mul, hmargA]
      _ = ∑ c, pC c := by
          refine sum_congr rfl fun c _ => ?_
          rcases (hCn c).eq_or_lt with h | h
          · rw [← h]
            simp
          · rw [div_self h.ne', mul_one]
      _ = ∑ t, p t := sum_push _ p
  -- `log q` splits on the support of `p`
  have hlog : ∀ t, p t * log (q t) = p t * log (pAC (t.1, t.2.2))
      + p t * log (pBC (t.2.1, t.2.2)) - p t * log (pC t.2.2) := by
    intro t
    rcases (hp t).eq_or_lt with h | h
    · rw [← h]
      ring
    · obtain ⟨h1, h2, h3⟩ := hpos t h
      simp only [hq]
      rw [log_div (mul_pos h1 h2).ne' h3.ne', log_mul h1.ne' h2.ne']
      ring
  have hsumlog : ∑ t, p t * log (q t)
      = ∑ u, pAC u * log (pAC u) + ∑ u, pBC u * log (pBC u) - ∑ c, pC c * log (pC c) := by
    simp only [hlog, sum_add_distrib, sum_sub_distrib]
    rw [sum_mul_comp_eq (fun t : α × β × γ => (t.1, t.2.2)) p fun u => log (pAC u),
      sum_mul_comp_eq (fun t : α × β × γ => (t.2.1, t.2.2)) p fun u => log (pBC u),
      sum_mul_comp_eq (fun t : α × β × γ => t.2.2) p fun c => log (pC c)]
  have hg := sum_sub_sum_le_kl hp hqn hpq
  rw [hqsum, sub_self, kl, sum_sub_distrib, hsumlog] at hg
  rw [ent_eq, ent_eq, ent_eq, ent_eq]
  linarith

end Submodular

/-! ## Data processing and the event inequality -/

/-- **Data processing.** Coarsening does not increase relative entropy. -/
theorem kl_push_le [DecidableEq β] (F : α → β) {μ ν : α → ℝ} (hμ : ∀ a, 0 ≤ μ a)
    (hν : ∀ a, 0 ≤ ν a) (hμν : ∀ a, 0 < μ a → 0 < ν a) :
    kl (push F μ) (push F ν) ≤ kl μ ν := by
  rw [kl, kl, ← sum_fiberwise univ F fun a => μ a * log (μ a) - μ a * log (ν a)]
  refine sum_le_sum fun b _ => ?_
  set s := univ.filter (fun a => F a = b) with hs
  have hm_def : push F μ b = ∑ a ∈ s, μ a := rfl
  have hn_def : push F ν b = ∑ a ∈ s, ν a := rfl
  rcases (push_nonneg F hμ b).eq_or_lt with hm | hm
  · have hz : ∀ a ∈ s, μ a = 0 :=
      (sum_eq_zero_iff_of_nonneg fun a _ => hμ a).mp (hm_def ▸ hm.symm)
    have hR : ∑ a ∈ s, (μ a * log (μ a) - μ a * log (ν a)) = 0 :=
      sum_eq_zero fun a ha => by rw [hz a ha]; simp
    rw [hR, ← hm]
    simp
  · obtain ⟨a0, ha0s, ha0⟩ : ∃ a ∈ s, 0 < μ a := by
      by_contra hcon
      push Not at hcon
      have : ∑ a ∈ s, μ a ≤ 0 := sum_nonpos hcon
      linarith [hm_def ▸ hm]
    set m := push F μ b with hmdef
    set n := push F ν b with hndef
    have hn : 0 < n := (hμν a0 ha0).trans_le (hn_def ▸ single_le_sum (fun a _ => hν a) ha0s)
    have hg : ∑ a ∈ s, (μ a - ν a * m / n)
        ≤ ∑ a ∈ s, (μ a * log (μ a) - μ a * log (ν a * m / n)) :=
      sum_le_sum fun a _ => sub_le_mul_log_sub_mul_log (hμ a)
        (div_nonneg (mul_nonneg (hν a) hm.le) hn.le)
        (fun h => div_pos (mul_pos (hμν a h) hm) hn)
    have hqs : ∑ a ∈ s, ν a * m / n = m := by
      rw [← sum_div, ← sum_mul, ← hn_def]
      field_simp
    have hsplit : ∀ a ∈ s, μ a * log (ν a * m / n)
        = μ a * log (ν a) + μ a * (log m - log n) := by
      intro a _
      rcases (hμ a).eq_or_lt with h | h
      · rw [← h]
        ring
      · have hν' := hμν a h
        rw [log_div (mul_pos hν' hm).ne' hn.ne', log_mul hν'.ne' hm.ne']
        ring
    rw [sum_sub_distrib, hqs, ← hm_def, sub_self] at hg
    have hR : ∑ a ∈ s, (μ a * log (μ a) - μ a * log (ν a * m / n))
        = ∑ a ∈ s, (μ a * log (μ a) - μ a * log (ν a)) - m * (log m - log n) := by
      have e1 : ∀ a ∈ s, μ a * log (μ a) - μ a * log (ν a * m / n)
          = (μ a * log (μ a) - μ a * log (ν a)) - μ a * (log m - log n) := by
        intro a ha
        rw [hsplit a ha]
        ring
      rw [sum_congr rfl e1, sum_sub_distrib, ← sum_mul, ← hm_def]
    rw [hR] at hg
    linarith

/-- **The event inequality.** For probability vectors, `μ(A) log(1/ν(A)) ≤ D(μ‖ν) + log 2`. -/
theorem mul_neg_log_le_kl_add_log_two {μ ν : α → ℝ} (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ a, 0 ≤ ν a)
    (hμν : ∀ a, 0 < μ a → 0 < ν a) (hμ1 : ∑ a, μ a = 1) (hν1 : ∑ a, ν a = 1)
    (A : α → Prop) [DecidablePred A] :
    (∑ a ∈ univ.filter A, μ a) * (-log (∑ a ∈ univ.filter A, ν a)) ≤ kl μ ν + log 2 := by
  have hdp := kl_push_le (fun a => decide (A a)) hμ hν hμν
  set x := ∑ a ∈ univ.filter A, μ a with hx
  set y := ∑ a ∈ univ.filter A, ν a with hy
  have hpt : ∀ p : α → ℝ, push (fun a => decide (A a)) p true = ∑ a ∈ univ.filter A, p a := by
    intro p
    simp [push]
  have hpf : ∀ p : α → ℝ, push (fun a => decide (A a)) p false
      = ∑ a, p a - ∑ a ∈ univ.filter A, p a := by
    intro p
    rw [← sum_filter_add_sum_filter_not univ A p]
    simp [push]
  rw [kl, Fintype.sum_bool, hpt, hpt, hpf, hpf, hμ1, hν1, ← hx, ← hy] at hdp
  have hx0 : 0 ≤ x := sum_nonneg fun a _ => hμ a
  have hx1 : x ≤ 1 := by
    rw [← hμ1]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ => hμ a
  have hy0 : 0 ≤ y := sum_nonneg fun a _ => hν a
  have hy1 : y ≤ 1 := by
    rw [← hν1]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun a _ _ => hν a
  have hbin : negMulLog x + negMulLog (1 - x) ≤ log 2 := by
    rw [← binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    exact binEntropy_le_log_two
  have hneg : (1 - x) * log (1 - y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (log_nonpos (by linarith) (by linarith))
  simp only [negMulLog] at hbin
  nlinarith

/-- For `ν = μ_X ⊗ uniform`, `D(μ‖ν) = H(X) + log |Y|·Σμ − H(X,Y)`. -/
theorem kl_prod_uniform [DecidableEq α] [Nonempty β] {μ : α × β → ℝ} (hμ : ∀ t, 0 ≤ μ t) :
    kl μ (fun t => push Prod.fst μ t.1 / Fintype.card β)
      = ent (push Prod.fst μ) + log (Fintype.card β) * ∑ t, μ t - ent μ := by
  have hc : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ t, μ t * log (push Prod.fst μ t.1 / Fintype.card β)
      = μ t * log (push Prod.fst μ t.1) - μ t * log (Fintype.card β) := by
    intro t
    rcases (hμ t).eq_or_lt with h | h
    · rw [← h]
      ring
    · have hX : 0 < push Prod.fst μ t.1 := h.trans_le (le_push _ hμ t)
      rw [log_div hX.ne' hc.ne']
      ring
  rw [kl, sum_sub_distrib]
  simp only [hterm, sum_sub_distrib]
  rw [sum_mul_comp_eq Prod.fst μ fun a => log (push Prod.fst μ a), ← sum_mul, ent_eq, ent_eq]
  ring

/-- **Events of small sections.** If `μ` is a probability vector on `X × Y` and every section of `A`
has relative size `≤ δ < 1`, then `μ(A) log(1/δ) ≤ H(X) + log |Y| − H(X,Y) + log 2`. -/
theorem mass_mul_neg_log_le [DecidableEq α] [Nonempty β] {μ : α × β → ℝ} (hμ : ∀ t, 0 ≤ μ t)
    (hμ1 : ∑ t, μ t = 1) (A : α × β → Prop) [DecidablePred A] {δ : ℝ} (hδ0 : 0 < δ)
    (hA : ∀ x, ((univ.filter fun y => A (x, y)).card : ℝ) ≤ δ * Fintype.card β) :
    (∑ t ∈ univ.filter A, μ t) * (-log δ)
      ≤ ent (push Prod.fst μ) + log (Fintype.card β) - ent μ + log 2 := by
  have hc : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  set ν : α × β → ℝ := fun t => push Prod.fst μ t.1 / Fintype.card β with hνdef
  have hν : ∀ t, 0 ≤ ν t := fun t => div_nonneg (push_nonneg _ hμ _) hc.le
  have hμν : ∀ t, 0 < μ t → 0 < ν t := fun t h => div_pos (h.trans_le (le_push _ hμ t)) hc
  have hν1 : ∑ t, ν t = 1 := by
    simp only [hνdef, Fintype.sum_prod_type, sum_const, card_univ, nsmul_eq_mul]
    rw [← hμ1, ← sum_push Prod.fst μ]
    refine sum_congr rfl fun a _ => ?_
    field_simp
  have hev := mul_neg_log_le_kl_add_log_two hμ hν hμν hμ1 hν1 A
  rw [kl_prod_uniform hμ, hμ1, mul_one] at hev
  set x := ∑ t ∈ univ.filter A, μ t with hx
  set y := ∑ t ∈ univ.filter A, ν t with hy
  have hx0 : 0 ≤ x := sum_nonneg fun t _ => hμ t
  -- `ν(A) ≤ δ`
  have hyδ : y ≤ δ := by
    have h1 : y = ∑ a, push Prod.fst μ a / Fintype.card β
        * ((univ.filter fun b => A (a, b)).card : ℝ) := by
      rw [hy, sum_filter, Fintype.sum_prod_type]
      refine sum_congr rfl fun a _ => ?_
      rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter]
      refine sum_congr rfl fun b _ => ?_
      split_ifs <;> simp [hνdef]
    rw [h1]
    calc ∑ a, push Prod.fst μ a / Fintype.card β * ((univ.filter fun b => A (a, b)).card : ℝ)
        ≤ ∑ a, push Prod.fst μ a / Fintype.card β * (δ * Fintype.card β) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hA a)
            (div_nonneg (push_nonneg _ hμ _) hc.le)
      _ = δ * ∑ a, push Prod.fst μ a := by
          rw [mul_sum]
          refine sum_congr rfl fun a _ => ?_
          field_simp
      _ = δ := by rw [sum_push, hμ1, mul_one]
  -- relative entropy is nonnegative
  have hkl0 : 0 ≤ kl μ ν := by
    have := sum_sub_sum_le_kl hμ hν hμν
    rw [hμ1, hν1, sub_self] at this
    exact this
  rw [hνdef, kl_prod_uniform hμ, hμ1, mul_one] at hkl0
  have hlog2 : 0 ≤ log 2 := log_nonneg (by norm_num)
  rcases hy0 : (eq_or_lt_of_le (sum_nonneg fun t _ => hν t : 0 ≤ y)) with h | h
  · -- `ν(A) = 0` forces `μ(A) = 0`
    have hz : ∀ t ∈ univ.filter A, ν t = 0 :=
      (sum_eq_zero_iff_of_nonneg fun t _ => hν t).mp (hy ▸ h.symm)
    have hxz : x = 0 := sum_eq_zero fun t ht => by
      by_contra hne
      exact (hμν t (lt_of_le_of_ne (hμ t) (Ne.symm hne))).ne' (hz t ht)
    rw [hxz, zero_mul]
    linarith
  · have hlog : -log δ ≤ -log y := neg_le_neg (log_le_log h hyδ)
    calc x * (-log δ) ≤ x * (-log y) := mul_le_mul_of_nonneg_left hlog hx0
      _ ≤ _ := hev

end

end GaloisForLFunctions.LogarithmicChowla
