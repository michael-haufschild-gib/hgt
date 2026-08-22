import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The Robbins–Monro recursion

A nonnegative sequence satisfying

`d (n+1) ≤ (1 - κ λ n) d n + C (λ n)²`,   `0 ≤ κ λ n ≤ 1`,

is squeezed between a geometric-type decay and the tail of `∑ λ²`:

`d n ≤ (∏_{k ∈ [N, n)} (1 - κ λ k)) d N + C ∑_{k ∈ [N, n)} (λ k)²`.

Since `1 - x ≤ e^{-x}`, the product is at most `exp(-κ ∑_{[N,n)} λ)`.  So if `∑ λ = ∞` and
`∑ λ² < ∞`, the first term can be made small by taking `n` large and the second by taking `N`
large, and `d n → 0`.  This is the deterministic core of the Robbins–Monro convergence theorem.
-/

open Filter Topology BigOperators

namespace GaloisForLFunctions.HTGeometry

/-- Each factor of the decay product is bounded by an exponential. -/
lemma prod_one_sub_le_exp_neg {κ : ℝ} {lam : ℕ → ℝ} (N n : ℕ)
    (_hnn : ∀ k, 0 ≤ κ * lam k) (hle : ∀ k, κ * lam k ≤ 1) :
    ∏ k ∈ Finset.Ico N n, (1 - κ * lam k)
      ≤ Real.exp (-(κ * ∑ k ∈ Finset.Ico N n, lam k)) := by
  have hstep : ∀ k ∈ Finset.Ico N n, (1 - κ * lam k) ≤ Real.exp (-(κ * lam k)) := by
    intro k _
    have h := Real.add_one_le_exp (-(κ * lam k))
    linarith
  have hnn' : ∀ k ∈ Finset.Ico N n, (0 : ℝ) ≤ 1 - κ * lam k := by
    intro k _
    linarith [hle k]
  calc ∏ k ∈ Finset.Ico N n, (1 - κ * lam k)
      ≤ ∏ k ∈ Finset.Ico N n, Real.exp (-(κ * lam k)) := Finset.prod_le_prod hnn' hstep
    _ = Real.exp (∑ k ∈ Finset.Ico N n, -(κ * lam k)) := by rw [Real.exp_sum]
    _ = Real.exp (-(κ * ∑ k ∈ Finset.Ico N n, lam k)) := by
        congr 1
        simp [Finset.mul_sum]

/-- The explicit solution bound for the recursion. -/
lemma robbins_le {d lam : ℕ → ℝ} {κ C : ℝ} (hC : 0 ≤ C)
    (_hd : ∀ n, 0 ≤ d n) (hlam : ∀ n, 0 ≤ κ * lam n) (hle : ∀ n, κ * lam n ≤ 1)
    (hrec : ∀ n, d (n + 1) ≤ (1 - κ * lam n) * d n + C * (lam n) ^ 2)
    (N : ℕ) : ∀ n, N ≤ n →
      d n ≤ (∏ k ∈ Finset.Ico N n, (1 - κ * lam k)) * d N
        + C * ∑ k ∈ Finset.Ico N n, (lam k) ^ 2 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hfac : (0 : ℝ) ≤ 1 - κ * lam n := by linarith [hle n]
      have hfac1 : (1 : ℝ) - κ * lam n ≤ 1 := by linarith [hlam n]
      have hSnn : (0 : ℝ) ≤ C * ∑ k ∈ Finset.Ico N n, (lam k) ^ 2 := by
        refine mul_nonneg hC (Finset.sum_nonneg fun k _ => ?_)
        positivity
      have h1 : d (n + 1) ≤ (1 - κ * lam n)
          * ((∏ k ∈ Finset.Ico N n, (1 - κ * lam k)) * d N
            + C * ∑ k ∈ Finset.Ico N n, (lam k) ^ 2) + C * (lam n) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left ih hfac
        linarith [hrec n, hmul]
      have hprod : ∏ k ∈ Finset.Ico N (n + 1), (1 - κ * lam k)
          = (∏ k ∈ Finset.Ico N n, (1 - κ * lam k)) * (1 - κ * lam n) :=
        Finset.prod_Ico_succ_top hn _
      have hsum : ∑ k ∈ Finset.Ico N (n + 1), (lam k) ^ 2
          = (∑ k ∈ Finset.Ico N n, (lam k) ^ 2) + (lam n) ^ 2 :=
        Finset.sum_Ico_succ_top hn _
      rw [hprod, hsum]
      nlinarith [h1, hSnn, hfac, hfac1]

/-- **The Robbins–Monro convergence theorem (deterministic form).** -/
theorem tendsto_zero_of_robbins {d lam : ℕ → ℝ} {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C)
    (hd : ∀ n, 0 ≤ d n) (hlam : ∀ n, 0 ≤ lam n) (hle : ∀ n, κ * lam n ≤ 1)
    (hrec : ∀ n, d (n + 1) ≤ (1 - κ * lam n) * d n + C * (lam n) ^ 2)
    (hdiv : Tendsto (fun n => ∑ k ∈ Finset.range n, lam k) atTop atTop)
    (hsq : Summable (fun n => (lam n) ^ 2)) :
    Tendsto d atTop (nhds 0) := by
  have hlamκ : ∀ n, 0 ≤ κ * lam n := fun n => mul_nonneg hκ.le (hlam n)
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · exact Eventually.of_forall fun n => lt_of_lt_of_le hc (hd n)
  -- choose `N` so that the tail of `∑ λ²` is small
  have htail : Tendsto (fun N => ∑' k, (lam k) ^ 2 - ∑ k ∈ Finset.range N, (lam k) ^ 2)
      atTop (nhds 0) := by
    have h := hsq.hasSum.tendsto_sum_nat
    have := Tendsto.const_sub (∑' k, (lam k) ^ 2) h
    simpa using this
  have hδ : (0 : ℝ) < c / (2 * (C + 1)) := by positivity
  obtain ⟨N, hN⟩ := (htail.eventually (gt_mem_nhds hδ)).exists
  have hNtail : ∀ n, N ≤ n → C * ∑ k ∈ Finset.Ico N n, (lam k) ^ 2 < c / 2 := by
    intro n hn
    have hIco : ∑ k ∈ Finset.Ico N n, (lam k) ^ 2
        = ∑ k ∈ Finset.range n, (lam k) ^ 2 - ∑ k ∈ Finset.range N, (lam k) ^ 2 := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun k => (lam k) ^ 2) (Nat.zero_le N) hn]
      ring
    have hle' : ∑ k ∈ Finset.range n, (lam k) ^ 2 ≤ ∑' k, (lam k) ^ 2 :=
      hsq.sum_le_tsum _ (fun k _ => by positivity)
    have hb : ∑ k ∈ Finset.Ico N n, (lam k) ^ 2 < c / (2 * (C + 1)) := by
      rw [hIco]; linarith [hN]
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.Ico N n, (lam k) ^ 2 :=
      Finset.sum_nonneg fun k _ => by positivity
    have h1 : C * ∑ k ∈ Finset.Ico N n, (lam k) ^ 2
        ≤ (C + 1) * ∑ k ∈ Finset.Ico N n, (lam k) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hnn
    have h2 : (C + 1) * ∑ k ∈ Finset.Ico N n, (lam k) ^ 2
        < (C + 1) * (c / (2 * (C + 1))) := mul_lt_mul_of_pos_left hb (by positivity)
    have heq : (C + 1) * (c / (2 * (C + 1))) = c / 2 := by
      field_simp
    linarith [h1, h2, heq]
  -- the decay factor tends to zero
  have hdecay : Tendsto (fun n => Real.exp (-(κ * ∑ k ∈ Finset.Ico N n, lam k)) * d N)
      atTop (nhds 0) := by
    have hSdiv : Tendsto (fun n => ∑ k ∈ Finset.Ico N n, lam k) atTop atTop := by
      have hIco : ∀ n, N ≤ n → ∑ k ∈ Finset.Ico N n, lam k
          = ∑ k ∈ Finset.range n, lam k - ∑ k ∈ Finset.range N, lam k := by
        intro n hn
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
          ← Finset.sum_Ico_consecutive lam (Nat.zero_le N) hn]
        ring
      have h1 : Tendsto (fun n => ∑ k ∈ Finset.range n, lam k
          - ∑ k ∈ Finset.range N, lam k) atTop atTop := by
        have := tendsto_atTop_add_const_right atTop (-(∑ k ∈ Finset.range N, lam k)) hdiv
        exact this.congr (fun n => by ring)
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hIco n hn).symm
    have h2 : Tendsto (fun n => -(κ * ∑ k ∈ Finset.Ico N n, lam k)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hκ hSdiv)
    have h3 : Tendsto (fun n => Real.exp (-(κ * ∑ k ∈ Finset.Ico N n, lam k)))
        atTop (nhds 0) := Real.tendsto_exp_atBot.comp h2
    simpa using h3.mul_const (d N)
  obtain ⟨N', hN'⟩ := eventually_atTop.1
    (hdecay.eventually (gt_mem_nhds (by positivity : (0:ℝ) < c / 2)))
  filter_upwards [eventually_ge_atTop (max N N')] with n hn
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN' : N' ≤ n := le_trans (le_max_right _ _) hn
  have hbound := robbins_le hC hd hlamκ hle hrec N n hnN
  have hprod : (∏ k ∈ Finset.Ico N n, (1 - κ * lam k)) * d N
      ≤ Real.exp (-(κ * ∑ k ∈ Finset.Ico N n, lam k)) * d N :=
    mul_le_mul_of_nonneg_right (prod_one_sub_le_exp_neg N n hlamκ hle) (hd N)
  have h1 := hN' n hnN'
  have h2 := hNtail n hnN
  linarith [hbound, hprod, h1, h2]

end GaloisForLFunctions.HTGeometry
