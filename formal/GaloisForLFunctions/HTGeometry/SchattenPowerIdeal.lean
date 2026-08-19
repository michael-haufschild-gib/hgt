/-
# Powers move down the Schatten scale

Submultiplicativity of the approximation numbers says a `k`-th power is approximated `k` times
faster, so a Schatten-`p` operator has its `k`-th power in Schatten `p/k`.  In particular every
power at or above the Schatten exponent is trace class, which is the hypothesis a regularized
determinant of order `p` needs of its operator.

Main results:
* `summable_comp_nat_div` — a nonnegative summable family stays summable after `k`-fold repetition.
* `approxNumber_pow_le_div` — the approximation numbers of a power.
* `memSchattenClass_pow` — **powers move down the Schatten scale**.
-/
import GaloisForLFunctions.HTGeometry.ApproxNumberMultiplicative

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- Repeating each term of a nonnegative summable family `k` times keeps it summable. -/
theorem summable_comp_nat_div {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hs : Summable f)
    {k : ℕ} (hk : 0 < k) : Summable fun m : ℕ => f (m / k) := by
  classical
  refine summable_of_sum_range_le (c := (k : ℝ) * ∑' n, f n) (fun m => hf _) fun N => ?_
  have hmaps : ∀ m ∈ Finset.range N, m / k ∈ Finset.range N := by
    intro m hm
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.div_le_self m k) (Finset.mem_range.mp hm))
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps (fun m => f (m / k))
  rw [← hfiber]
  have hcard : ∀ n ∈ Finset.range N,
      ((Finset.range N).filter fun m => m / k = n).card ≤ k := by
    intro n _
    have hsub : ((Finset.range N).filter fun m => m / k = n)
        ⊆ Finset.Ico (k * n) (k * n + k) := by
      intro m hm
      have hmk : m / k = n := (Finset.mem_filter.mp hm).2
      have hdm := Nat.div_add_mod m k
      have hlt := Nat.mod_lt m hk
      rw [hmk] at hdm
      refine Finset.mem_Ico.mpr ⟨?_, ?_⟩ <;> omega
    refine le_trans (Finset.card_le_card hsub) ?_
    rw [Nat.card_Ico]
    omega
  have hstep : ∀ n ∈ Finset.range N,
      (∑ m ∈ (Finset.range N).filter fun m => m / k = n, f (m / k)) ≤ (k : ℝ) * f n := by
    intro n hn
    have hconst : (∑ m ∈ (Finset.range N).filter fun m => m / k = n, f (m / k))
        = (((Finset.range N).filter fun m => m / k = n).card : ℝ) * f n := by
      rw [Finset.sum_congr rfl fun m hm => by rw [(Finset.mem_filter.mp hm).2], Finset.sum_const,
        nsmul_eq_mul]
    rw [hconst]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard n hn) (hf n)
  calc (∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).filter fun m => m / k = n, f (m / k))
      ≤ ∑ n ∈ Finset.range N, (k : ℝ) * f n := Finset.sum_le_sum hstep
    _ = (k : ℝ) * ∑ n ∈ Finset.range N, f n := by rw [Finset.mul_sum]
    _ ≤ (k : ℝ) * ∑' n, f n := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact hs.sum_le_tsum _ (fun n _ => hf n)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The approximation numbers of a `k`-th power. -/
theorem approxNumber_pow_le_div (T : H →L[ℂ] H) {k : ℕ} (hk : 0 < k) (m : ℕ) :
    approxNumber (T ^ k) m ≤ approxNumber T (m / k) ^ k := by
  have hle : k * (m / k) ≤ m := Nat.mul_div_le m k
  exact le_trans (approxNumber_antitone (T ^ k) hle) (approxNumber_pow_le T (m / k) k hk)

omit [CompleteSpace H] in
/-- **Powers move down the Schatten scale.** -/
theorem memSchattenClass_pow {p : ℝ} (hp : 0 < p) {T : H →L[ℂ] H}
    (hT : MemSchattenClass p T) {k : ℕ} (hk : 0 < k) :
    MemSchattenClass (p / k) (T ^ k) := by
  have hknz : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hdiv0 : 0 ≤ p / (k : ℝ) := le_of_lt (div_pos hp (by exact_mod_cast hk))
  refine Summable.of_nonneg_of_le
    (fun m => Real.rpow_nonneg (approxNumber_nonneg _ m) _)
    (fun m => ?_)
    (summable_comp_nat_div (fun n => Real.rpow_nonneg (approxNumber_nonneg T n) p) hT hk)
  have hbase : approxNumber (T ^ k) m ≤ approxNumber T (m / k) ^ k :=
    approxNumber_pow_le_div T hk m
  have hstep : (approxNumber (T ^ k) m) ^ (p / (k : ℝ))
      ≤ (approxNumber T (m / k) ^ k : ℝ) ^ (p / (k : ℝ)) :=
    Real.rpow_le_rpow (approxNumber_nonneg _ m) hbase hdiv0
  refine le_trans hstep (le_of_eq ?_)
  rw [← Real.rpow_natCast (approxNumber T (m / k)) k,
    ← Real.rpow_mul (approxNumber_nonneg T (m / k))]
  congr 1
  field_simp

end

end GaloisForLFunctions.HTGeometry
