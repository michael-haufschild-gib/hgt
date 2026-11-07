import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# No uniform measure on the integers

A summable `W` on the positive integers with `W(kℕ) = S/k` for every `k` is zero, with no sign on `W`.

The sets `{r : k ∣ r}` behave as if they were independent of probability `1/k`, which no point of `ℕ`
can absorb: a fixed `n` is the only multiple `nt` with `t` prime to every prime below `X`, up to points
beyond `X`, and that set has mass `(S/n) Π_{p<X} (1 − 1/p) → 0` by the divergence of `Σ 1/p`.

This is the rigid core of the cut system: an absolutely summable kernel vector does not exist. So every
kernel vector, in particular every zero mode, is conditionally convergent.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- **The Euler product at the edge vanishes.** -/
theorem tendsto_prod_primesBelow_one_sub_inv :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, (1 - ((p : ℝ))⁻¹)) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun N : ℕ => ∑ i ∈ range N, Set.indicator {p : ℕ | p.Prime}
      (fun n : ℕ => (1 : ℝ) / n) i) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => Set.indicator_nonneg (fun _ _ => by positivity) n)).mp not_summable_one_div_on_primes
  have hsum : ∀ N : ℕ, ∑ i ∈ range N, Set.indicator {p : ℕ | p.Prime} (fun n : ℕ => (1 : ℝ) / n) i =
      ∑ p ∈ N.primesBelow, ((p : ℝ))⁻¹ := by
    intro N
    rw [Nat.primesBelow, sum_filter]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : i.Prime <;> simp [Set.indicator, h]
  have hexp : Tendsto (fun N : ℕ => Real.exp (-∑ p ∈ N.primesBelow, ((p : ℝ))⁻¹)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
    simpa only [hsum] using hdiv
  refine squeeze_zero (fun N => prod_nonneg fun p hp => ?_) (fun N => ?_) hexp
  · have hp' := (Nat.mem_primesBelow.mp hp).2
    have h1 : ((p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp'.one_lt.le)
    linarith
  · rw [← sum_neg_distrib, Real.exp_sum]
    refine prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
    · have hp' := (Nat.mem_primesBelow.mp hp).2
      have h1 : ((p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp'.one_lt.le)
      linarith
    · have := Real.add_one_le_exp (-((p : ℝ))⁻¹)
      linarith

variable {W : ℕ → ℝ}

/-- The part of `W` on the multiples `n t` with `t > 0` prime to `P`. -/
def primePart (W : ℕ → ℝ) (n : ℕ) (P : Finset ℕ) (t : ℕ) : ℝ :=
  if 0 < t ∧ ∀ p ∈ P, ¬ p ∣ t then W (n * t) else 0

theorem summable_mul_left (hW : Summable W) {n : ℕ} (hn : 1 ≤ n) :
    Summable fun t => W (n * t) :=
  hW.comp_injective fun _ _ h => Nat.eq_of_mul_eq_mul_left (by omega : 0 < n) h

theorem abs_primePart_le (W : ℕ → ℝ) (n : ℕ) (P : Finset ℕ) (t : ℕ) :
    ‖primePart W n P t‖ ≤ ‖W (n * t)‖ := by
  unfold primePart
  split_ifs
  · exact le_rfl
  · simp

theorem summable_primePart (hW : Summable W) {n : ℕ} (hn : 1 ≤ n) (P : Finset ℕ) :
    Summable (primePart W n P) :=
  Summable.of_norm_bounded (summable_mul_left hW hn).norm (abs_primePart_le W n P)

/-- Peeling one prime from `P`. The multiples of `p` among the integers prime to `P` are `p` times the
integers prime to `P`. -/
theorem tsum_primePart_insert (hW : Summable W) {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    {P : Finset ℕ} (hpP : p ∉ P) (hPr : ∀ q ∈ P, q.Prime) :
    ∑' t, primePart W n (insert p P) t =
      ∑' t, primePart W n P t - ∑' t, primePart W (n * p) P t := by
  have hnp : 1 ≤ n * p := Nat.mul_pos hn hp.pos
  set h : ℕ → ℝ := fun t => if p ∣ t then primePart W n P t else 0 with hh
  have hsplit : ∀ t, primePart W n P t = primePart W n (insert p P) t + h t := by
    intro t
    simp only [hh, primePart, mem_insert, forall_eq_or_imp]
    by_cases hd : p ∣ t
    · simp [hd]
    · by_cases ht : 0 < t ∧ ∀ q ∈ P, ¬ q ∣ t <;> simp [hd, ht]
  have hinj : Function.Injective (fun t : ℕ => p * t) :=
    fun _ _ he => Nat.eq_of_mul_eq_mul_left hp.pos he
  have hsupp : Function.support h ⊆ Set.range (fun t : ℕ => p * t) := by
    intro t ht
    simp only [Function.mem_support, hh] at ht
    by_cases hd : p ∣ t
    · obtain ⟨s, rfl⟩ := hd
      exact ⟨s, rfl⟩
    · simp [hd] at ht
  have hcomp : ∀ t, h (p * t) = primePart W (n * p) P t := by
    intro t
    simp only [hh, primePart, dvd_mul_right, if_true]
    have hiff : (0 < p * t ∧ ∀ q ∈ P, ¬ q ∣ p * t) ↔ (0 < t ∧ ∀ q ∈ P, ¬ q ∣ t) := by
      refine and_congr (by simp [hp.pos]) (forall₂_congr fun q hq => ?_)
      have hne : q ≠ p := fun he => hpP (he ▸ hq)
      refine not_congr ⟨fun hd => ?_, fun hd => Dvd.dvd.mul_left hd p⟩
      rcases ((hPr q hq).dvd_mul).mp hd with hd' | hd'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (hPr q hq) hp).mp hd') hne
      · exact hd'
    by_cases hc : 0 < t ∧ ∀ q ∈ P, ¬ q ∣ t
    · rw [if_pos (hiff.mpr hc), if_pos hc, mul_assoc]
    · rw [if_neg (fun hx => hc (hiff.mp hx)), if_neg hc]
  have htsum : ∑' t, h t = ∑' t, primePart W (n * p) P t := by
    rw [← hinj.tsum_eq hsupp]
    exact tsum_congr hcomp
  have hsh : Summable h := by
    refine Summable.of_norm_bounded (summable_primePart hW hn P).norm fun t => ?_
    simp only [hh]
    split_ifs
    · exact le_rfl
    · simp
  rw [← htsum, eq_sub_iff_add_eq, ← (summable_primePart hW hn (insert p P)).tsum_add hsh]
  exact tsum_congr fun t => (hsplit t).symm

/-- **Independence of the multiples.** If `W(kℕ) = S/k` for all `k`, the integers prime to `P` carry
the Euler product. -/
theorem mul_tsum_primePart (hW : Summable W) (hW0 : W 0 = 0) {S : ℝ}
    (hmul : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * ∑' t, W (k * t) = S) (P : Finset ℕ)
    (hPr : ∀ q ∈ P, q.Prime) :
    ∀ n : ℕ, 1 ≤ n → (n : ℝ) * ∑' t, primePart W n P t = S * ∏ p ∈ P, (1 - ((p : ℝ))⁻¹) := by
  induction P using Finset.induction_on with
  | empty =>
    intro n hn
    rw [prod_empty, mul_one, ← hmul n hn]
    congr 1
    refine tsum_congr fun t => ?_
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [primePart, hW0]
    · simp [primePart, ht]
  | insert p P hpP ih =>
    intro n hn
    have hp : p.Prime := hPr p (mem_insert_self p P)
    have hPr' : ∀ q ∈ P, q.Prime := fun q hq => hPr q (mem_insert_of_mem hq)
    have hpR : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 := ih hPr' n hn
    have h2 := ih hPr' (n * p) (Nat.mul_pos hn hp.pos)
    rw [tsum_primePart_insert hW hn hp hpP hPr', prod_insert hpP]
    push_cast at h2
    have h3 : (n : ℝ) * ∑' t, primePart W (n * p) P t =
        (S * ∏ q ∈ P, (1 - ((q : ℝ))⁻¹)) / p := by
      rw [eq_div_iff hpR, ← h2]
      ring
    rw [mul_sub, h1, h3]
    field_simp

/-- **No uniform measure.** A summable `W` on the positive integers with `k W(kℕ) = S` for every `k`
vanishes. -/
theorem eq_zero_of_uniform_multiples (hW : Summable W) (hW0 : W 0 = 0) {S : ℝ}
    (hmul : ∀ k : ℕ, 1 ≤ k → (k : ℝ) * ∑' t, W (k * t) = S) {n : ℕ} (hn : 1 ≤ n) : W n = 0 := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hval : ∀ X : ℕ, ∑' t, primePart W n X.primesBelow t =
      S * (∏ p ∈ X.primesBelow, (1 - ((p : ℝ))⁻¹)) / n := by
    intro X
    rw [eq_div_iff hnR, mul_comm]
    exact mul_tsum_primePart hW hW0 hmul _ (fun q hq => (Nat.mem_primesBelow.mp hq).2) n hn
  have hlim0 : Tendsto (fun X : ℕ => ∑' t, primePart W n X.primesBelow t) atTop (𝓝 0) := by
    simp_rw [hval]
    have := (tendsto_prod_primesBelow_one_sub_inv.const_mul S).div_const (n : ℝ)
    simpa using this
  have hlim1 : Tendsto (fun X : ℕ => ∑' t, primePart W n X.primesBelow t) atTop
      (𝓝 (∑' t, if t = 1 then W n else 0)) := by
    refine tendsto_tsum_of_dominated_convergence (summable_mul_left hW hn).norm (fun t => ?_)
      (Eventually.of_forall fun X t => abs_primePart_le W n _ t)
    by_cases h1 : t = 1
    · subst h1
      have : ∀ X : ℕ, primePart W n X.primesBelow 1 = W n := by
        intro X
        simp only [primePart, mul_one]
        rw [if_pos]
        refine ⟨one_pos, fun p hp hd => ?_⟩
        exact (Nat.mem_primesBelow.mp hp).2.one_lt.ne' (Nat.dvd_one.mp hd)
      simp [this]
    · rw [if_neg h1]
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp [primePart]
      · refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop t] with X hX
        have hp := Nat.minFac_prime h1
        have hle := Nat.minFac_le ht
        have hmem : t.minFac ∈ X.primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
        simp only [primePart]
        rw [if_neg]
        rintro ⟨_, hc⟩
        exact hc _ hmem (Nat.minFac_dvd t)
  have hsingle : (∑' t, if t = 1 then W n else 0) = W n := tsum_ite_eq 1 _
  rw [hsingle] at hlim1
  exact tendsto_nhds_unique hlim1 hlim0

end GaloisForLFunctions.RigidArithmeticOfCuts
