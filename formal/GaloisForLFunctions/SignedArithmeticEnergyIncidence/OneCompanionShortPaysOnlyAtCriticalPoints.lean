import GaloisForLFunctions.SignedArithmeticEnergyIncidence.OnLineCompanionsPayOffLineDepth

/-!
# One companion short pays only at a critical point

The local signed sampling law (`companions_pay`, `few_companions_never_pay`) leaves one count
open: a source with exactly one more degree of freedom than there are companions.  That count is
decided by the location of the depth.  With distinct companions `γ_i`, `i ∈ s`, their node
polynomial `N = Π_i (X − γ_i)` and the form `Q(p) = Σ_i p(γ_i)² − w p'(t)²`:

* **Exact price** (`companions_pay_iff`): on sources of degree `< #s`, `Q ≥ 0` iff `w Λ(t) ≤ 1`.
  The defeating source interpolates the values `ℓ_i'(t)`, where `Q = Λ(1 − wΛ)`.
* **One companion short** (`oneShort_companions_pay_iff`): on sources of degree `≤ #s`, with
  `w > 0`, `Q ≥ 0` iff `N'(t) = 0` and `w Λ(t) ≤ 1`.  A source splits as `p = r + cN` with
  `deg r < #s`; the node polynomial is invisible at the companions and moves `p'(t)` by `c N'(t)`.
* **Two short** (`twoShort_companions_never_pay`): sources of degree `≤ #s + 1` defeat every
  positive depth mass at every height, companion heights included.

Hence (`exists_payable_iff`) a positive depth mass at `t` is payable for all sources with `n`
degrees of freedom iff `n ≤ #s`, or `n = #s + 1` and `t` is a critical point of `N`; one companion
short, the payable heights are the at most `#s − 1` roots of `N'`
(`oneShort_payable_iff_mem_roots`, `card_roots_derivative_nodal_le`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

variable {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}

/-- **The Lagrange price is exact**: on sources of degree `< #s` the companion form is nonnegative
iff `w Λ(t) ≤ 1`. -/
theorem companions_pay_iff (hvs : Set.InjOn v s) {w t : ℝ} (hw : 0 ≤ w) :
    (∀ p : ℝ[X], p.degree < #s → 0 ≤ companionForm s v w t p) ↔
      w * lagrangePrice s v t ≤ 1 := by
  refine ⟨fun h => ?_, fun hΛ p hp => companions_pay hvs hp hw hΛ⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ[X],
      q = Lagrange.interpolate s v (fun i => (derivative (Lagrange.basis s v i)).eval t) :=
    ⟨_, rfl⟩
  have hq : q.degree < #s := by rw [hqdef]; exact Lagrange.degree_interpolate_lt _ hvs
  have hval : ∀ i ∈ s, q.eval (v i) = (derivative (Lagrange.basis s v i)).eval t := by
    intro i hi
    rw [hqdef, Lagrange.eval_interpolate_at_node _ hvs hi]
  have hsum : ∑ i ∈ s, (q.eval (v i)) ^ 2 = lagrangePrice s v t := by
    unfold lagrangePrice
    exact sum_congr rfl fun i hi => by rw [hval i hi]
  have hder : (derivative q).eval t = lagrangePrice s v t := by
    rw [derivative_eval_eq_sum hvs hq t]
    unfold lagrangePrice
    exact sum_congr rfl fun i hi => by rw [hval i hi, sq]
  have hΛ0 : 0 < lagrangePrice s v t := by
    by_contra h0
    push Not at h0
    nlinarith
  have hQ := h q hq
  unfold companionForm at hQ
  rw [hsum, hder] at hQ
  nlinarith

omit [DecidableEq ι] in
/-- The node polynomial `N = Π_i (X − γ_i)` has degree `#s`. -/
theorem degree_nodal_eq : (Lagrange.nodal s v).degree = #s := by
  rw [degree_eq_natDegree Lagrange.nodal_ne_zero, Lagrange.natDegree_nodal]

/-- **One companion short**: on sources of degree `≤ #s` a positive depth mass at `t` is paid
iff `t` is a critical point of the node polynomial and `w Λ(t) ≤ 1`. -/
theorem oneShort_companions_pay_iff (hvs : Set.InjOn v s) {w t : ℝ} (hw : 0 < w) :
    (∀ p : ℝ[X], p.degree ≤ #s → 0 ≤ companionForm s v w t p) ↔
      (derivative (Lagrange.nodal s v)).eval t = 0 ∧ w * lagrangePrice s v t ≤ 1 := by
  set N := Lagrange.nodal s v with hN
  constructor
  · intro h
    refine ⟨?_, (companions_pay_iff hvs hw.le).mp fun p hp => h p hp.le⟩
    have hQ := h N (le_of_eq degree_nodal_eq)
    unfold companionForm at hQ
    rw [sum_eq_zero fun i hi => by rw [hN, Lagrange.eval_nodal_at_node hi]; norm_num,
      zero_sub] at hQ
    have h2 : ((derivative N).eval t) ^ 2 = 0 :=
      le_antisymm (by nlinarith [sq_nonneg ((derivative N).eval t)]) (sq_nonneg _)
    exact pow_eq_zero_iff two_ne_zero |>.mp h2
  · rintro ⟨hcrit, hΛ⟩ p hp
    have hmon : N.Monic := Lagrange.nodal_monic
    have hsplit := modByMonic_add_div p N
    -- the quotient by `N` is a constant
    have hnat : (p /ₘ N).natDegree = 0 := by
      rw [natDegree_divByMonic p hmon, hN, Lagrange.natDegree_nodal]
      have := natDegree_le_of_degree_le hp
      omega
    have hc : p /ₘ N = C ((p /ₘ N).coeff 0) := eq_C_of_natDegree_eq_zero hnat
    have hr : (p %ₘ N).degree < #s := by
      have := degree_modByMonic_lt p hmon
      rwa [hN, degree_nodal_eq] at this
    have hval : ∀ i ∈ s, p.eval (v i) = (p %ₘ N).eval (v i) := by
      intro i hi
      conv_lhs => rw [← hsplit]
      rw [eval_add, eval_mul, hN, Lagrange.eval_nodal_at_node hi, zero_mul, add_zero]
    have hder : (derivative p).eval t = (derivative (p %ₘ N)).eval t := by
      conv_lhs => rw [← hsplit]
      rw [hc, derivative_add, derivative_mul, derivative_C, mul_zero, add_zero, eval_add,
        eval_mul, hcrit, zero_mul, add_zero]
    have hpr : companionForm s v w t p = companionForm s v w t (p %ₘ N) := by
      unfold companionForm
      rw [hder, sum_congr rfl fun i hi => by rw [hval i hi]]
    rw [hpr]
    exact companions_pay hvs hr hw.le hΛ

/-- A critical point of the node polynomial is not a companion: `N'(γ_i) = Π_{j ≠ i}(γ_i − γ_j)`. -/
theorem derivative_nodal_eval_node_ne_zero (hvs : Set.InjOn v s) {i : ι} (hi : i ∈ s) :
    (derivative (Lagrange.nodal s v)).eval (v i) ≠ 0 := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq hi]
  exact Lagrange.eval_nodal_not_at_node fun j hj hij =>
    (Finset.mem_erase.mp hj).1 (hvs (Finset.mem_of_mem_erase hj) hi hij.symm)

/-- **Two companions short never pay**, at every height: sources of degree `≤ #s + 1` defeat
every positive depth mass. -/
theorem twoShort_companions_never_pay (hvs : Set.InjOn v s) (t : ℝ) {w : ℝ} (hw : 0 < w) :
    ∃ p : ℝ[X], p.degree ≤ #s + 1 ∧ companionForm s v w t p < 0 := by
  by_cases hcrit : (derivative (Lagrange.nodal s v)).eval t = 0
  · have ht : ∀ i ∈ s, v i ≠ t := fun i hi hit =>
      derivative_nodal_eval_node_ne_zero hvs hi (by rw [hit]; exact hcrit)
    obtain ⟨p, hpdeg, hp⟩ := few_companions_never_pay ht hw
    refine ⟨p, degree_le_natDegree.trans ?_, hp⟩
    rw [hpdeg]
    norm_cast
  · refine ⟨Lagrange.nodal s v, ?_, ?_⟩
    · rw [degree_nodal_eq]
      exact_mod_cast Nat.le_succ _
    · unfold companionForm
      rw [sum_eq_zero fun i hi => by rw [Lagrange.eval_nodal_at_node hi]; norm_num, zero_sub]
      have : 0 < ((derivative (Lagrange.nodal s v)).eval t) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hcrit))
      nlinarith

/-- `deg p < #s + 1` iff `deg p ≤ #s`. -/
theorem degree_lt_succ_iff (p : ℝ[X]) (m : ℕ) :
    p.degree < ((m + 1 : ℕ) : WithBot ℕ) ↔ p.degree ≤ (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero, degree_le_iff_coeff_zero]
  constructor
  · intro h k hk
    have : m < k := by exact_mod_cast hk
    exact h k (by omega)
  · intro h k hk
    exact h k (by exact_mod_cast (by omega : m < k))

/-- **The companion count law**: a positive depth mass at `t` is payable for all sources with `n`
degrees of freedom iff `n ≤ #s`, or `n = #s + 1` and `t` is a critical point of the node
polynomial. -/
theorem exists_payable_iff (hvs : Set.InjOn v s) (t : ℝ) (n : ℕ) :
    (∃ w : ℝ, 0 < w ∧ ∀ p : ℝ[X], p.degree < n → 0 ≤ companionForm s v w t p) ↔
      n ≤ #s ∨ (n = #s + 1 ∧ (derivative (Lagrange.nodal s v)).eval t = 0) := by
  have hΛ0 := lagrangePrice_nonneg (s := s) (v := v) t
  have hw0 : 0 < 1 / (lagrangePrice s v t + 1) := by positivity
  have hwΛ : 1 / (lagrangePrice s v t + 1) * lagrangePrice s v t ≤ 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith
  constructor
  · rintro ⟨w, hw, h⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨hn, hn'⟩ := hcon
    rcases Nat.lt_or_ge n (#s + 2) with h2 | h2
    · have hn1 : n = #s + 1 := by omega
      have hpay := (oneShort_companions_pay_iff hvs hw).mp fun p hp =>
        h p (by rw [hn1]; exact (degree_lt_succ_iff p #s).mpr hp)
      exact hn' hn1 hpay.1
    · obtain ⟨p, hpdeg, hp⟩ := twoShort_companions_never_pay hvs t hw
      have hlt : p.degree < n := by
        refine lt_of_le_of_lt hpdeg ?_
        exact_mod_cast (by omega : #s + 1 < n)
      have := h p hlt
      linarith
  · rintro (hn | ⟨hn, hcrit⟩)
    · refine ⟨_, hw0, fun p hp => companions_pay hvs (lt_of_lt_of_le hp ?_) hw0.le hwΛ⟩
      exact_mod_cast hn
    · refine ⟨_, hw0, fun p hp => (oneShort_companions_pay_iff hvs hw0).mpr ⟨hcrit, hwΛ⟩ p ?_⟩
      rw [hn] at hp
      exact (degree_lt_succ_iff p #s).mp hp

/-- **The payable heights one companion short are the critical points of the node polynomial**:
for nonempty companions a positive depth mass at `t` is payable on sources of degree `≤ #s` iff
`t` is a root of `N'`. -/
theorem oneShort_payable_iff_mem_roots (hvs : Set.InjOn v s) (hs : s.Nonempty) (t : ℝ) :
    (∃ w : ℝ, 0 < w ∧ ∀ p : ℝ[X], p.degree ≤ #s → 0 ≤ companionForm s v w t p) ↔
      t ∈ (derivative (Lagrange.nodal s v)).roots := by
  have hne : derivative (Lagrange.nodal s v) ≠ 0 := by
    intro h0
    obtain ⟨i, hi⟩ := hs
    exact derivative_nodal_eval_node_ne_zero hvs hi (by rw [h0, eval_zero])
  rw [mem_roots hne, IsRoot.def]
  have hΛ0 := lagrangePrice_nonneg (s := s) (v := v) t
  constructor
  · rintro ⟨w, hw, h⟩
    exact ((oneShort_companions_pay_iff hvs hw).mp h).1
  · intro hcrit
    refine ⟨1 / (lagrangePrice s v t + 1), by positivity, ?_⟩
    refine (oneShort_companions_pay_iff hvs (by positivity)).mpr ⟨hcrit, ?_⟩
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith

omit [DecidableEq ι] in
/-- There are at most `#s − 1` payable heights one companion short. -/
theorem card_roots_derivative_nodal_le :
    (derivative (Lagrange.nodal s v)).roots.toFinset.card ≤ #s - 1 := by
  calc (derivative (Lagrange.nodal s v)).roots.toFinset.card
      ≤ Multiset.card (derivative (Lagrange.nodal s v)).roots := Multiset.toFinset_card_le _
    _ ≤ (derivative (Lagrange.nodal s v)).natDegree := card_roots' _
    _ ≤ (Lagrange.nodal s v).natDegree - 1 := natDegree_derivative_le _
    _ = #s - 1 := by rw [Lagrange.natDegree_nodal]

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
