import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumMajorant
import GaloisForLFunctions.RHTower.Sieve.JutilaLocalLargeValues

/-!
# Heath-Brown's pair sums in the mean-value range

For a fixed `t₂ ∈ W`, the points `t₁ − t₂` (`t₁ ∈ W`) are `1`-separated and lie in an interval of
length `T` when `W` does.  The corpus discrete mean value theorem on separated sets
(`sum_normSq_dirPoly_finset_le`) therefore bounds each row of the pair sum, and summing over `t₂`,

`Σ_{t₁,t₂∈W} |Σ_{n∈S} a_n n^{i(t₁−t₂)}|² ≤ |W| (T + 1 + 4L(1 + log L))(1 + 2 log L) Σ_{n∈S} |a_n|²`

for `S ⊆ [1, L]`.  For `|a_n| ≤ 1` on `(N, 2N]` and `T ≤ N` this is Heath-Brown's theorem
(Guth–Maynard, Theorem 1.6) in the range `N ≥ T`, with the explicit loss `20(1 + log 2N)²`:

`Σ_{t₁,t₂∈W} |Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ≤ 20 |W| N² (1 + log 2N)²`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The pair sum through the mean value theorem.**  For `W` `1`-separated of diameter at most
`T` and `S ⊆ [1, L]`, `L ≥ 2`:
`Σ_{t₁,t₂}|Σ_{n∈S} a_n n^{i(t₁−t₂)}|² ≤ |W| (T + 1 + 4L(1+log L))(1 + 2 log L) Σ_{n∈S}|a_n|²`. -/
theorem hbPairSum_le_meanValue {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W) {T : ℝ}
    (hT : 0 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {L : ℕ} (hL : 2 ≤ L)
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 L) (a : ℕ → ℂ) :
    hbPairSum W S a ≤ (W.card : ℝ) * ((T + 1 + 4 * L * (1 + Real.log L)) *
      (1 + 2 * Real.log L) * ∑ n ∈ S, ‖a n‖ ^ 2) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : Fin L → ℂ,
      c = fun i : Fin L => if (i : ℕ) + 1 ∈ S then a ((i : ℕ) + 1) else 0 := ⟨_, rfl⟩
  have hcoef : ∑ i : Fin L, ‖c i‖ ^ 2 = ∑ n ∈ S, ‖a n‖ ^ 2 := by
    have hfun : ∀ n, ‖(if n ∈ S then a n else 0)‖ ^ 2 = if n ∈ S then ‖a n‖ ^ 2 else 0 :=
      fun n => by split_ifs <;> simp
    have h := sum_fin_succ_eq_sum_Icc L (fun n => ‖(if n ∈ S then a n else 0)‖ ^ 2)
    simp only [hfun] at h
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS] at h
    rw [hc]
    simpa only [hfun] using h
  have hrow : ∀ t₂ ∈ W, ∑ t₁ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ 2 ≤
      (T + 1 + 4 * L * (1 + Real.log L)) * (1 + 2 * Real.log L) * ∑ n ∈ S, ‖a n‖ ^ 2 := by
    intro t₂ _
    have hinj : ∀ x ∈ W, ∀ y ∈ W, x - t₂ = y - t₂ → x = y := fun x _ y _ h => by linarith
    have hsep : ∀ x ∈ W.image (fun t => t - t₂), ∀ y ∈ W.image (fun t => t - t₂), x ≠ y →
        1 ≤ |x - y| := by
      intro x hx y hy hxy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hy
      have hne : t ≠ t' := fun h => hxy (by rw [h])
      rw [show t - t₂ - (t' - t₂) = t - t' by ring]
      exact hW t ht t' ht' hne
    have hdiam' : ∀ x ∈ W.image (fun t => t - t₂), ∀ y ∈ W.image (fun t => t - t₂),
        |x - y| ≤ T := by
      intro x hx y hy
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp hy
      rw [show t - t₂ - (t' - t₂) = t - t' by ring]
      exact hdiam t ht t' ht'
    have hmv := sum_normSq_dirPoly_finset_le L hL c hT hsep hdiam'
    rw [Finset.sum_image hinj, hcoef] at hmv
    refine le_of_eq_of_le (Finset.sum_congr rfl fun t₁ _ => ?_) hmv
    rw [hbPoly_eq_dirPoly hS, hc]
  rw [hbPairSum, Finset.sum_comm]
  calc ∑ t₂ ∈ W, ∑ t₁ ∈ W, ‖hbPoly S a (t₁ - t₂)‖ ^ 2
      ≤ ∑ _t₂ ∈ W, (T + 1 + 4 * L * (1 + Real.log L)) * (1 + 2 * Real.log L) *
          ∑ n ∈ S, ‖a n‖ ^ 2 := Finset.sum_le_sum hrow
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Heath-Brown's theorem in the range `N ≥ T`.**  For `W` `1`-separated of diameter at most
`T ≤ N` and `|a_n| ≤ 1` on `(N, 2N]`:
`Σ_{t₁,t₂∈W} |Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ≤ 20 |W| N² (1 + log 2N)²`. -/
theorem hbPairSum_Ioc_le_of_le {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W) {T : ℝ}
    (hT : 0 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {N : ℕ} (hN : 1 ≤ N)
    (hTN : T ≤ N) {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc N (2 * N)) a ≤
      20 * (W.card : ℝ) * (N : ℝ) ^ 2 * (1 + Real.log (2 * N)) ^ 2 := by
  have hS : Finset.Ioc N (2 * N) ⊆ Finset.Icc 1 (2 * N) := fun n hn => by
    have := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, this.2⟩
  have hmv := hbPairSum_le_meanValue hW hT hdiam (by omega : 2 ≤ 2 * N) hS a
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by push_cast; ring
  rw [hcast] at hmv
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hsum : ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 ≤ N := by
    calc ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 ≤ ∑ _n ∈ Finset.Ioc N (2 * N), (1 : ℝ) :=
          Finset.sum_le_sum fun n hn => by
            have := ha n hn
            have h0 := norm_nonneg (a n)
            nlinarith
      _ = N := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc, mul_one]
          congr 1
          omega
  have h1 : T + 1 + 4 * (2 * (N : ℝ)) * (1 + Real.log (2 * N)) ≤
      10 * N * (1 + Real.log (2 * N)) := by nlinarith
  have h2 : 1 + 2 * Real.log (2 * N) ≤ 2 * (1 + Real.log (2 * N)) := by linarith
  calc hbPairSum W (Finset.Ioc N (2 * N)) a
      ≤ (W.card : ℝ) * ((T + 1 + 4 * (2 * (N : ℝ)) * (1 + Real.log (2 * N))) *
          (1 + 2 * Real.log (2 * N)) * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2) := hmv
    _ ≤ (W.card : ℝ) * ((10 * N * (1 + Real.log (2 * N))) * (2 * (1 + Real.log (2 * N))) *
          N) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        refine mul_le_mul (mul_le_mul h1 h2 (by linarith) (by positivity)) hsum
          (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ = 20 * (W.card : ℝ) * (N : ℝ) ^ 2 * (1 + Real.log (2 * N)) ^ 2 := by ring

end

end RHTower.Sieve
