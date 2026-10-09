import GaloisForLFunctions.RHTower.ChronologicalRiemannEquivalence

/-!
# RH as a Möbius subset-sum problem

Let `β(t) = 1/t - 1/(e^t - 1)`.  For a finite set `S` of positive integers put
`r_S(t) = e^{-t} + Σ_{k ∈ S} μ(k) β(kt)`.

**Theorem** (`riemannHypothesis_iff_mobius_subset_sums`).  RH holds iff
`inf_S ‖r_S‖_{L²(0,∞)} = 0`, i.e. iff rows with every coefficient in `{0, μ(k)}` reach every
accuracy.

The coefficients are integral: one only decides which squarefree integers to keep, the signs are
forced by `μ`.

**Proof.**  `⟸` is the bounded-row receiver.  For `⟹`, start from the Báez-Duarte rows
`μ(k)w_k`, `w_k = (1 - k/X)k^{-δ} ∈ [0,1]`, which work under RH.  Round them greedily to
`{0, μ(k)}` so that the running rounding error `D(K) = Σ_{k ≤ K}(a_k - μ(k)w_k)` stays in `[-1,1]`
(`ditherState`).  Because `β` is decreasing on `(0,∞)` (`fusionBoseDefect_antitoneOn`), Abel
summation gives the pointwise bound
`|Σ_{k ≤ N} d_k β(kt)| ≤ A β(t) + B β((n₀+1)t)`, with `A` bounding `|D|` up to `n₀` and `B`
bounding it everywhere (`abs_sum_mul_fusionBoseDefect_le`).  Up to `n₀` the weights are `≈ 1`, so
the greedy rule keeps every `μ(k)` and `A` is small, while `‖β((n₀+1)·)‖ = ‖β‖/√(n₀+1)`.
Rounding therefore costs `o(1)`.  No Mellin estimate enters the rounding step.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-! ## Monotonicity of the Bose defect -/

private theorem bose_sq_mul_exp_le {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 * Real.exp t ≤ (Real.exp t - 1) ^ 2 := by
  have hs := Real.self_le_sinh_iff.mpr (by linarith : (0 : ℝ) ≤ t / 2)
  rw [Real.sinh_eq] at hs
  have he : Real.exp t = Real.exp (t / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  have he' : Real.exp (-(t / 2)) * Real.exp (t / 2) = 1 := by rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (t / 2)
  -- `t ≤ e^{t/2} - e^{-t/2}`, multiply by `e^{t/2}`
  have h1 : t * Real.exp (t / 2) ≤ Real.exp t - 1 := by
    have := mul_le_mul_of_nonneg_right (by linarith : t ≤ Real.exp (t / 2) - Real.exp (-(t / 2)))
      hpos.le
    rw [he]; nlinarith
  have h0 : 0 ≤ t * Real.exp (t / 2) := by positivity
  calc t ^ 2 * Real.exp t = (t * Real.exp (t / 2)) ^ 2 := by rw [he]; ring
    _ ≤ (Real.exp t - 1) ^ 2 := pow_le_pow_left₀ h0 h1 2

/-- `β(t) = 1/t - 1/(e^t - 1)` is decreasing on `(0,∞)`. -/
theorem fusionBoseDefect_antitoneOn : AntitoneOn fusionBoseDefect (Ioi 0) := by
  set g : ℝ → ℝ := fun t => 1 / t - 1 / (Real.exp t - 1) with hg
  have hEq : EqOn fusionBoseDefect g (Ioi 0) := fun t ht => by
    simp only [fusionBoseDefect, if_pos (show 0 < t from ht), hg]
  have hden : ∀ t ∈ Ioi (0 : ℝ), Real.exp t - 1 ≠ 0 := fun t ht => by
    have := Real.one_lt_exp_iff.mpr (show 0 < t from ht); linarith
  have hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt g (-(1 / t ^ 2) + Real.exp t / (Real.exp t - 1) ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := (show 0 < t from ht).ne'
    have h1 := (hasDerivAt_inv ht0)
    have h2 := ((Real.hasDerivAt_exp t).sub_const 1).inv (hden t ht)
    have := (h1.sub h2).congr_of_eventuallyEq (f₁ := g)
      (Eventually.of_forall fun x => by simp [hg, one_div])
    refine this.congr_deriv ?_
    rw [one_div]; ring
  have hg' : AntitoneOn g (Ioi 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) ?_ ?_ ?_
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · rw [interior_Ioi]; exact fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ioi]
      intro t ht
      rw [(hderiv t ht).deriv]
      have ht0 : 0 < t := ht
      have hd := hden t ht
      have hd' : 0 < (Real.exp t - 1) ^ 2 := by positivity
      have hkey := bose_sq_mul_exp_le ht0.le
      rw [neg_add_le_iff_le_add, add_zero, div_le_div_iff₀ hd' (by positivity)]
      nlinarith
  exact hg'.congr hEq.symm

theorem fusionBoseDefect_nonneg (t : ℝ) : 0 ≤ fusionBoseDefect t := (fusionBoseDefect_bounds t).1

/-! ## Abel summation against the Bose defect -/

/-- Telescoping of consecutive Bose differences. -/
private theorem sum_Ioc_bose_diff (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ k ∈ Finset.Ioc a b, (f k - f (k + 1)) = f (a + 1) - f (b + 1) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih => rw [Finset.sum_Ioc_succ_top hab, ih]; ring

/-- **Abel summation.**  With `D(K) = Σ_{k ≤ K} d_k`,
`Σ_{k ≤ N} d_k f_k = Σ_{k ≤ N} D(k)(f_k - f_{k+1}) + D(N) f_{N+1}`. -/
theorem sum_mul_eq_abel (d f : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Ioc 0 N, d k * f k =
      ∑ k ∈ Finset.Ioc 0 N, (∑ j ∈ Finset.Ioc 0 k, d j) * (f k - f (k + 1)) +
        (∑ j ∈ Finset.Ioc 0 N, d j) * f (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Finset.sum_Ioc_succ_top (Nat.zero_le N),
      Finset.sum_Ioc_succ_top (Nat.zero_le N)]
    ring

/-- **Pointwise Abel bound.**  If the running sums of `d` are bounded by `A` up to `n₀` and by `B`
everywhere, then `|Σ_{k ≤ N} d_k β(kt)| ≤ A β(t) + B β((n₀+1)t)` for `t > 0`. -/
theorem abs_sum_mul_fusionBoseDefect_le (d : ℕ → ℝ) (N n₀ : ℕ) {A B : ℝ}
    (hA : ∀ K ≤ n₀, |∑ k ∈ Finset.Ioc 0 K, d k| ≤ A)
    (hB : ∀ K, |∑ k ∈ Finset.Ioc 0 K, d k| ≤ B) {t : ℝ} (ht : 0 < t) :
    |∑ k ∈ Finset.Ioc 0 N, d k * fusionBoseDefect (k * t)| ≤
      A * fusionBoseDefect t + B * fusionBoseDefect ((n₀ + 1 : ℕ) * t) := by
  set f : ℕ → ℝ := fun k => fusionBoseDefect (k * t) with hf
  set D : ℕ → ℝ := fun K => ∑ k ∈ Finset.Ioc 0 K, d k with hD
  have hmono : ∀ k : ℕ, 1 ≤ k → f (k + 1) ≤ f k := by
    intro k hk
    have hk0 : (0 : ℝ) < k * t := mul_pos (by exact_mod_cast hk) ht
    exact fusionBoseDefect_antitoneOn hk0 (by
      show (0 : ℝ) < ((k + 1 : ℕ) : ℝ) * t
      exact mul_pos (by positivity) ht) (by
      push_cast; nlinarith)
  have hf0 : ∀ k, 0 ≤ f k := fun k => fusionBoseDefect_nonneg _
  have hf1 : f 1 = fusionBoseDefect t := by simp [hf]
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [show (∑ k ∈ Finset.Ioc 0 N, d k * fusionBoseDefect (k * t)) =
      ∑ k ∈ Finset.Ioc 0 N, d k * f k from rfl, sum_mul_eq_abel d f N]
  -- termwise bounds on the Abel sum
  have hterm : ∀ k ∈ Finset.Ioc 0 N, |D k * (f k - f (k + 1))| ≤
      (if k ≤ n₀ then A else B) * (f k - f (k + 1)) := by
    intro k hk
    have hk1 := (Finset.mem_Ioc.mp hk).1
    have hdiff : 0 ≤ f k - f (k + 1) := sub_nonneg.mpr (hmono k hk1)
    rw [abs_mul, abs_of_nonneg hdiff]
    refine mul_le_mul_of_nonneg_right ?_ hdiff
    split_ifs with hkn
    · exact hA k hkn
    · exact hB k
  have hsplit : (∑ k ∈ Finset.Ioc 0 N, (if k ≤ n₀ then A else B) * (f k - f (k + 1))) ≤
      A * (f 1 - f (min N n₀ + 1)) + B * (f (min N n₀ + 1) - f (N + 1)) := by
    have hdisj : Finset.Ioc 0 N = Finset.Ioc 0 (min N n₀) ∪ Finset.Ioc (min N n₀) N := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) (min_le_left _ _)]
    rw [hdisj, Finset.sum_union (Finset.disjoint_left.mpr fun x hx hx' => by
      simp only [Finset.mem_Ioc] at hx hx'; omega)]
    have h1 : (∑ k ∈ Finset.Ioc 0 (min N n₀), (if k ≤ n₀ then A else B) * (f k - f (k + 1))) =
        A * (f 1 - f (min N n₀ + 1)) := by
      rw [Finset.sum_congr rfl (fun k hk => by
        rw [if_pos (by simp only [Finset.mem_Ioc] at hk; omega)]), ← Finset.mul_sum,
        sum_Ioc_bose_diff f 0 _ (Nat.zero_le _)]
    have h2 : (∑ k ∈ Finset.Ioc (min N n₀) N, (if k ≤ n₀ then A else B) * (f k - f (k + 1))) ≤
        B * (f (min N n₀ + 1) - f (N + 1)) := by
      rw [← sum_Ioc_bose_diff f _ N (min_le_left _ _), Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      simp only [Finset.mem_Ioc] at hk
      have hk1 : 1 ≤ k := by omega
      have hdiff : 0 ≤ f k - f (k + 1) := sub_nonneg.mpr (hmono k hk1)
      rw [if_neg (by omega)]
    rw [h1]; linarith
  have hlast : |D N * f (N + 1)| ≤ (if N ≤ n₀ then A else B) * f (N + 1) := by
    rw [abs_mul, abs_of_nonneg (hf0 _)]
    refine mul_le_mul_of_nonneg_right ?_ (hf0 _)
    split_ifs with h
    · exact hA N h
    · exact hB N
  have hmin_mono : f (min N n₀ + 1) ≤ f 1 := by
    have := sum_Ioc_bose_diff f 0 (min N n₀) (Nat.zero_le _)
    have hnn : 0 ≤ ∑ k ∈ Finset.Ioc 0 (min N n₀), (f k - f (k + 1)) :=
      Finset.sum_nonneg fun k hk => sub_nonneg.mpr (hmono k (Finset.mem_Ioc.mp hk).1)
    linarith
  have hn0mono : f (n₀ + 1) ≤ f (min N n₀ + 1) ∨ N ≤ n₀ := by
    rcases le_total N n₀ with h | h
    · exact Or.inr h
    · left; rw [min_eq_right h]
  have htot : |∑ k ∈ Finset.Ioc 0 N, D k * (f k - f (k + 1)) + D N * f (N + 1)| ≤
      ∑ k ∈ Finset.Ioc 0 N, (if k ≤ n₀ then A else B) * (f k - f (k + 1)) +
        (if N ≤ n₀ then A else B) * f (N + 1) :=
    (abs_add_le _ _).trans (add_le_add ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum hterm)) hlast)
  rw [← hf1]
  rcases le_or_gt N n₀ with h | h
  · rw [min_eq_left h] at hsplit
    rw [if_pos h] at htot
    nlinarith [hf0 (n₀ + 1), hf0 (N + 1)]
  · rw [min_eq_right h.le] at hsplit
    rw [if_neg (by omega)] at htot
    nlinarith [hf0 (n₀ + 1), hf0 (N + 1)]

/-! ## Greedy rounding to `{0, μ(k)}` -/

/-- Greedy rounding state: `D(0) = 0`; at step `K+1` keep `μ(K+1)` when the running error stays in
`[-1,1]`, otherwise drop it. -/
def ditherState (b : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | K + 1 =>
    if |ditherState b K + (sharpMobiusRow (K + 1) - b (K + 1))| ≤ 1 then
      ditherState b K + (sharpMobiusRow (K + 1) - b (K + 1))
    else ditherState b K - b (K + 1)

/-- The rounded row: `μ(k)` when kept, `0` when dropped. -/
def ditherRow (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  if 0 < k ∧ |ditherState b (k - 1) + (sharpMobiusRow k - b k)| ≤ 1 then sharpMobiusRow k else 0

theorem ditherRow_mem (b : ℕ → ℝ) (k : ℕ) :
    ditherRow b k = 0 ∨ ditherRow b k = sharpMobiusRow k := by
  unfold ditherRow; split_ifs <;> simp

theorem sum_ditherRow_sub_eq_ditherState (b : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.Ioc 0 K, (ditherRow b k - b k) = ditherState b K := by
  induction K with
  | zero => simp [ditherState]
  | succ K ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le K), ih]
    simp only [ditherState, ditherRow, Nat.add_sub_cancel]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.2 h2
    · exact absurd ⟨Nat.succ_pos K, h2⟩ h1
    · ring

theorem sharpMobiusRow_eq_or (k : ℕ) :
    sharpMobiusRow k = 0 ∨ sharpMobiusRow k = 1 ∨ sharpMobiusRow k = -1 := by
  unfold sharpMobiusRow
  rcases ArithmeticFunction.moebius_eq_or k with h | h | h <;> simp [h]

/-- The greedy error never leaves `[-1, 1]` when the target row is `μ(k)w_k` with `w_k ∈ [0,1]`. -/
theorem abs_ditherState_le_one {b : ℕ → ℝ}
    (hb : ∀ k, ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ b k = sharpMobiusRow k * w) (K : ℕ) :
    |ditherState b K| ≤ 1 := by
  induction K with
  | zero => simp [ditherState]
  | succ K ih =>
    simp only [ditherState]
    split_ifs with h
    · exact h
    · obtain ⟨w, hw0, hw1, hbw⟩ := hb (K + 1)
      rw [hbw] at h ⊢
      set D := ditherState b K
      rw [abs_le] at ih ⊢
      push Not at h
      rcases sharpMobiusRow_eq_or (K + 1) with hm | hm | hm <;> rw [hm] at h ⊢
      · simp at h; exact absurd (abs_le.mpr ih) (not_le.mpr h)
      · have : 1 < D + (1 - 1 * w) := by
          rcases lt_abs.mp h with h' | h'
          · exact h'
          · linarith
        constructor <;> linarith
      · have : D + (-1 - (-1) * w) < -1 := by
          rcases lt_abs.mp h with h' | h'
          · linarith
          · linarith
        constructor <;> linarith

/-- While the accumulated weight defect stays below `1`, the greedy rule keeps every `μ(k)` and
the running error is bounded by that defect. -/
theorem abs_ditherState_le_prefix (b : ℕ → ℝ) {n₀ : ℕ} {A : ℝ}
    (hA : ∑ k ∈ Finset.Ioc 0 n₀, |sharpMobiusRow k - b k| ≤ A) (hA1 : A ≤ 1) :
    ∀ K ≤ n₀, |ditherState b K| ≤ ∑ k ∈ Finset.Ioc 0 K, |sharpMobiusRow k - b k| := by
  intro K hK
  induction K with
  | zero => simp [ditherState]
  | succ K ih =>
    have ih' := ih (by omega)
    have hsum : ∑ k ∈ Finset.Ioc 0 (K + 1), |sharpMobiusRow k - b k| ≤ A := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)) hA
      intro x hx; simp only [Finset.mem_Ioc] at hx ⊢; omega
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le K)] at hsum ⊢
    have hcand : |ditherState b K + (sharpMobiusRow (K + 1) - b (K + 1))| ≤
        ∑ k ∈ Finset.Ioc 0 K, |sharpMobiusRow k - b k| + |sharpMobiusRow (K + 1) - b (K + 1)| :=
      (abs_add_le _ _).trans (add_le_add ih' le_rfl)
    simp only [ditherState]
    rw [if_pos (hcand.trans (hsum.trans hA1))]
    exact hcand

/-! ## The rounding cost in `L²(0,∞)` -/

theorem chronologicalHeatError_sub_eq (a b : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    chronologicalHeatError a N t - chronologicalHeatError b N t =
      ∑ k ∈ Finset.Ioc 0 N, (a k - b k) * fusionBoseDefect (k * t) := by
  unfold chronologicalHeatError
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `‖β(c·)‖ = ‖β‖/√c` on `(0,∞)`. -/
theorem chronologicalL2Norm_bose_dilate {c : ℝ} (hc : 0 < c) :
    chronologicalL2Norm (fun t => fusionBoseDefect (c * t)) =
      chronologicalL2Norm fusionBoseDefect / Real.sqrt c := by
  have hm1 := chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn hc
  rw [chronologicalL2Norm_eq_sqrt hm1.1, chronologicalL2Norm_eq_sqrt chronologicalBose_memLp.1]
  have h := integral_comp_mul_left_Ioi (fun t => fusionBoseDefect t ^ 2) 0 hc
  simp only [mul_zero, smul_eq_mul] at h
  rw [h, Real.sqrt_mul (inv_nonneg.mpr hc.le), Real.sqrt_inv]
  field_simp

/-- **Rounding cost.**  If the running sums of `a - b` are bounded by `A` up to `n₀` and by `1`
everywhere, then `‖r_a‖ ≤ ‖r_b‖ + (A + 1/√(n₀+1)) ‖β‖`. -/
theorem chronologicalL2Norm_le_of_partialSums (a b : ℕ → ℝ) (N n₀ : ℕ) {A : ℝ}
    (hA : ∀ K ≤ n₀, |∑ k ∈ Finset.Ioc 0 K, (a k - b k)| ≤ A)
    (hB : ∀ K, |∑ k ∈ Finset.Ioc 0 K, (a k - b k)| ≤ 1) :
    chronologicalL2Norm (chronologicalHeatError a N) ≤
      chronologicalL2Norm (chronologicalHeatError b N) +
        (A + 1 / Real.sqrt ((n₀ + 1 : ℕ) : ℝ)) * chronologicalL2Norm fusionBoseDefect := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (Nat.zero_le _))
  set E : ℝ → ℝ := fun t => ∑ k ∈ Finset.Ioc 0 N, (a k - b k) * fusionBoseDefect (k * t) with hE
  set c : ℝ := ((n₀ + 1 : ℕ) : ℝ) with hc
  have hc0 : 0 < c := by positivity
  have hβ := chronologicalBose_memLp
  have hβc := chronological_memLp_dilate chronologicalBose_memLp chronologicalBose_continuousOn hc0
  set g : ℝ → ℝ := fun t => A * fusionBoseDefect t + 1 * fusionBoseDefect (c * t) with hg
  have hgm : MemLp g 2 chronologicalPositiveVolume := (hβ.const_mul A).add (hβc.const_mul 1)
  have hpt : ∀ t, ‖E t‖ ≤ g t := by
    intro t
    rw [Real.norm_eq_abs]
    rcases le_or_gt t 0 with ht | ht
    · have hz : ∀ k : ℕ, fusionBoseDefect (k * t) = 0 := fun k => by
        simp only [fusionBoseDefect]
        rw [if_neg (by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])]
      have hz0 : fusionBoseDefect t = 0 := by simp [fusionBoseDefect, not_lt.mpr ht]
      have hzc : fusionBoseDefect (c * t) = 0 := by
        simp only [fusionBoseDefect]; rw [if_neg (by nlinarith)]
      simp [hE, hg, hz, hz0, hzc]
    · exact abs_sum_mul_fusionBoseDefect_le (fun k => a k - b k) N n₀ hA hB ht
  have hEle : chronologicalL2Norm E ≤ chronologicalL2Norm g := by
    unfold chronologicalL2Norm
    exact lpNorm_mono_real hgm hpt
  have hgle : chronologicalL2Norm g ≤
      A * chronologicalL2Norm fusionBoseDefect +
        1 * chronologicalL2Norm (fun t => fusionBoseDefect (c * t)) := by
    unfold chronologicalL2Norm
    have hsum := lpNorm_add_le (hβ.const_mul A) (by norm_num : (1 : ENNReal) ≤ 2)
      (g := fun t => 1 * fusionBoseDefect (c * t))
    have h1 : lpNorm (fun t => A * fusionBoseDefect t) 2 chronologicalPositiveVolume =
        A * lpNorm fusionBoseDefect 2 chronologicalPositiveVolume := by
      have := lpNorm_const_smul A fusionBoseDefect chronologicalPositiveVolume (p := 2)
      simp only [Pi.smul_def, smul_eq_mul] at this
      rw [this]; simp [Real.nnnorm_of_nonneg hA0]
    have h2 : lpNorm (fun t => 1 * fusionBoseDefect (c * t)) 2 chronologicalPositiveVolume =
        1 * lpNorm (fun t => fusionBoseDefect (c * t)) 2 chronologicalPositiveVolume := by
      simp
    rw [← h1, ← h2]
    exact hsum
  have htri : chronologicalL2Norm (chronologicalHeatError a N) ≤
      chronologicalL2Norm (chronologicalHeatError b N) + chronologicalL2Norm E := by
    have hfun : chronologicalHeatError a N = chronologicalHeatError b N + E := by
      funext t; simp only [Pi.add_apply, hE]; rw [← chronologicalHeatError_sub_eq]; ring
    rw [hfun]
    unfold chronologicalL2Norm
    exact lpNorm_add_le (chronologicalHeatError_memLp b N) (by norm_num)
  rw [chronologicalL2Norm_bose_dilate hc0] at hgle
  have : (A + 1 / Real.sqrt c) * chronologicalL2Norm fusionBoseDefect =
      A * chronologicalL2Norm fusionBoseDefect + 1 * (chronologicalL2Norm fusionBoseDefect /
        Real.sqrt c) := by ring
  linarith

/-! ## Riesz rows with a small prefix defect -/

/-- The truncated negated Riesz row `μ(k)(1 - k/X)k^{-δ}` for `k ≤ N`, `0` beyond. -/
def rieszRow (N : ℕ) (δ : ℝ) (k : ℕ) : ℝ := if k ≤ N then -bdRieszCoeff N δ k else 0

theorem chronologicalHeatError_rieszRow (N : ℕ) (δ : ℝ) :
    chronologicalHeatError (rieszRow N δ) N =
      chronologicalHeatError (fun k => -bdRieszCoeff N δ k) N := by
  funext t
  unfold chronologicalHeatError
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [rieszRow, if_pos (Finset.mem_Ioc.mp hk).2]

theorem rieszRow_eq_mul (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ rieszRow N δ k = sharpMobiusRow k * w := by
  by_cases hk0 : k = 0
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    subst hk0; simp [rieszRow, bdRieszCoeff]
  by_cases hkN : k ≤ N
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
    have hX0 := perronLength_pos N
    have hX : (k : ℝ) < perronLength N := by
      unfold perronLength; have : (k : ℝ) ≤ N := by exact_mod_cast hkN
      linarith
    refine ⟨(1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ), ?_, ?_, ?_⟩
    · exact mul_nonneg (by rw [sub_nonneg, div_le_one hX0]; exact hX.le)
        (Real.rpow_nonneg (by linarith) _)
    · have h1 : 1 - (k : ℝ) / perronLength N ≤ 1 := by
        have : 0 ≤ (k : ℝ) / perronLength N := by positivity
        linarith
      have h2 : (k : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith)
      calc (1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ) ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) zero_le_one
        _ = 1 := by ring
    · simp only [rieszRow, if_pos hkN, bdRieszCoeff, sharpMobiusRow]
      ring
  · refine ⟨0, le_rfl, zero_le_one, ?_⟩
    simp [rieszRow, if_neg hkN]


theorem abs_sharpMobius_sub_rieszRow_le (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) {k : ℕ} (hk : 1 ≤ k)
    (hkN : k ≤ N) :
    |sharpMobiusRow k - rieszRow N δ k| ≤ (1 - (k : ℝ) ^ (-δ)) + k / perronLength N := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hX0 := perronLength_pos N
  have hp0 : 0 ≤ (k : ℝ) ^ (-δ) := Real.rpow_nonneg (by linarith) _
  have hp1 : (k : ℝ) ^ (-δ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hk1 (by linarith)
  have hX : (k : ℝ) < perronLength N := by
    unfold perronLength; have : (k : ℝ) ≤ N := by exact_mod_cast hkN
    linarith
  have hq0 : 0 ≤ (k : ℝ) / perronLength N := by positivity
  have hq1 : (k : ℝ) / perronLength N ≤ 1 := by rw [div_le_one hX0]; exact hX.le
  have hrow : rieszRow N δ k =
      sharpMobiusRow k * ((1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ)) := by
    simp only [rieszRow, if_pos hkN, bdRieszCoeff, sharpMobiusRow]; ring
  have hmu : |sharpMobiusRow k| ≤ 1 := by
    unfold sharpMobiusRow; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [hrow, show sharpMobiusRow k - sharpMobiusRow k * ((1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ))
    = sharpMobiusRow k * (1 - (1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ)) by ring, abs_mul]
  have hw : 0 ≤ 1 - (1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ) := by nlinarith
  rw [abs_of_nonneg hw]
  calc |sharpMobiusRow k| * (1 - (1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ))
      ≤ 1 * (1 - (1 - (k : ℝ) / perronLength N) * (k : ℝ) ^ (-δ)) :=
        mul_le_mul_of_nonneg_right hmu hw
    _ ≤ (1 - (k : ℝ) ^ (-δ)) + k / perronLength N := by nlinarith

/-- **Riesz rows with a small prefix defect under RH.** -/
theorem exists_rieszRow_small (hRH : RiemannHypothesis) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η)
    (n₀ : ℕ) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧
      chronologicalL2Norm (chronologicalHeatError (rieszRow N δ) N) < ε ∧
        ∑ k ∈ Finset.Ioc 0 n₀, |sharpMobiusRow k - rieszRow N δ k| ≤ η := by
  obtain ⟨B₂, hB₂0, hB⟩ := exists_norm_sq_bdTarget_sub_bdRiesz_le_of_rh hRH
  set M := ∫ ξ : ℝ, ‖Complex.Gamma (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2
    with hMdef
  -- choose `δ`
  have hRlim : Tendsto (fun δ : ℝ => 3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2) +
      2 * ‖invZetaCont (1 + δ)‖ ^ 2 * M) (𝓝[>] 0) (𝓝 0) := by
    have hF : Tendsto zetaShiftDefect (𝓝[>] 0) (𝓝 0) :=
      tendsto_integral_one_sub_riemannZeta_ratio_of_rh hRH
    have hI := (tendsto_invZetaCont_one_add_of_rh hRH).norm.pow 2
    have := ((hF.add (hI.const_mul B₂)).const_mul 3).add ((hI.const_mul 2).mul_const M)
    simpa using this
  have hPlim : Tendsto (fun δ : ℝ => ∑ k ∈ Finset.Ioc 0 n₀, (1 - (k : ℝ) ^ (-δ))) (𝓝[>] 0)
      (𝓝 0) := by
    have : Tendsto (fun δ : ℝ => ∑ k ∈ Finset.Ioc 0 n₀, (1 - (k : ℝ) ^ (-δ))) (𝓝 0)
        (𝓝 (∑ k ∈ Finset.Ioc 0 n₀, (1 - (k : ℝ) ^ (-(0 : ℝ))))) := by
      refine tendsto_finsetSum _ fun k hk => ?_
      have hk0 : (k : ℝ) ≠ 0 := by
        have := (Finset.mem_Ioc.mp hk).1; positivity
      exact tendsto_const_nhds.sub ((Real.continuousAt_const_rpow hk0).tendsto.comp
        (continuous_neg.tendsto 0))
    simp only [neg_zero, Real.rpow_zero, sub_self, Finset.sum_const_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, ⟨hδR, hδP⟩, hδ0, hδ1⟩ :=
    (((hRlim.eventually (gt_mem_nhds (pow_pos hε 2))).and
      (hPlim.eventually (gt_mem_nhds (half_pos hη)))).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num))).exists
  obtain ⟨B₁, hB₁⟩ := hB δ hδ0 hδ1.le
  -- choose `N`
  have hG : Tendsto (fun N : ℕ => 3 * (zetaShiftDefect δ + B₁ * perronLength N ^ (-δ) +
      B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2) + 2 * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2 * M) atTop
      (𝓝 (3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2) +
        2 * ‖invZetaCont (1 + δ)‖ ^ 2 * M)) := by
    have h1 := (tendsto_perronLength_rpow_neg hδ0).const_mul B₁
    have h2 := (tendsto_moebiusRieszPoly_one_add_of_rh hRH hδ0 (by linarith)).norm.pow 2
    have := ((((tendsto_const_nhds (x := zetaShiftDefect δ)).add h1).add
      (h2.const_mul B₂)).const_mul 3).add ((h2.const_mul 2).mul_const M)
    simpa using this
  have hQlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ioc 0 n₀, (k : ℝ) / perronLength N) atTop
      (𝓝 0) := by
    have := tendsto_finsetSum (Finset.Ioc 0 n₀) fun k _ =>
      (tendsto_const_nhds (x := (k : ℝ))).div_atTop tendsto_perronLength_atTop
    simpa using this
  obtain ⟨N, ⟨hN, hNQ⟩, hNn⟩ := (((hG.eventually (gt_mem_nhds hδR)).and
    (hQlim.eventually (gt_mem_nhds (half_pos hη)))).and (eventually_ge_atTop n₀)).exists
  refine ⟨N, δ, hδ0, ?_, ?_⟩
  · rw [chronologicalHeatError_rieszRow]
    have hS : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
    obtain ⟨-, heq⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS (bdRieszCoeff N δ)
    have hle := chronologicalL2Norm_sq_bdRiesz_le N δ
    have hd := hB₁ N
    rw [heq] at hd
    have hπ : 0 < 2 * Real.pi := by positivity
    have hint_le : (∫ t : ℝ, ‖1 + riemannZeta (1 / 2 + t * Complex.I) *
        bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + t * Complex.I)‖ ^ 2 /
          (1 / 4 + t ^ 2)) ≤
        3 * (zetaShiftDefect δ + B₁ * perronLength N ^ (-δ) +
          B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_left hd hπ.le
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul, one_mul] at this
      exact this
    have hsq : chronologicalL2Norm (chronologicalHeatError (fun k => -bdRieszCoeff N δ k) N) ^ 2 <
        ε ^ 2 := by
      rw [← hMdef] at hle
      linarith
    exact (pow_lt_pow_iff_left₀ (chronologicalL2Norm_nonneg _) hε.le two_ne_zero).mp hsq
  · calc ∑ k ∈ Finset.Ioc 0 n₀, |sharpMobiusRow k - rieszRow N δ k|
        ≤ ∑ k ∈ Finset.Ioc 0 n₀, ((1 - (k : ℝ) ^ (-δ)) + k / perronLength N) :=
          Finset.sum_le_sum fun k hk => abs_sharpMobius_sub_rieszRow_le N hδ0.le
            (Finset.mem_Ioc.mp hk).1 ((Finset.mem_Ioc.mp hk).2.trans hNn)
      _ = ∑ k ∈ Finset.Ioc 0 n₀, (1 - (k : ℝ) ^ (-δ)) +
            ∑ k ∈ Finset.Ioc 0 n₀, (k : ℝ) / perronLength N := Finset.sum_add_distrib
      _ ≤ η := by linarith

/-! ## The subset-sum criterion -/

/-- **RH as a Möbius subset-sum problem.**  RH holds iff for every `ε > 0` some row with every
coefficient in `{0, μ(k)}` has chronological error below `ε`. -/
theorem riemannHypothesis_iff_mobius_subset_sums :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, a k = 0 ∨ a k = sharpMobiusRow k) ∧
        chronologicalL2Norm (chronologicalHeatError a N) < ε := by
  constructor
  · intro hRH ε hε
    set c := chronologicalL2Norm fusionBoseDefect with hcdef
    have hc0 : 0 ≤ c := chronologicalL2Norm_nonneg _
    -- `n₀` with `c/√(n₀+1) < ε/3`
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt ((3 * (c + 1) / ε) ^ 2)
    have hsq0 : 0 < Real.sqrt ((n₀ + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hn₀' : 1 / Real.sqrt ((n₀ + 1 : ℕ) : ℝ) * c < ε / 3 := by
      have hbig : 3 * (c + 1) / ε < Real.sqrt ((n₀ + 1 : ℕ) : ℝ) := by
        rw [show 3 * (c + 1) / ε = Real.sqrt ((3 * (c + 1) / ε) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_lt_sqrt (by positivity)
        push_cast; linarith
      rw [div_lt_iff₀ hε] at hbig
      rw [one_div, inv_mul_lt_iff₀ hsq0]
      nlinarith
    set η := min 1 (ε / (3 * (c + 1))) with hηdef
    have hη0 : 0 < η := lt_min one_pos (by positivity)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηc : η * c < ε / 3 := by
      have h1 : η ≤ ε / (3 * (c + 1)) := min_le_right _ _
      have h2 : η * c ≤ ε / (3 * (c + 1)) * c := mul_le_mul_of_nonneg_right h1 hc0
      have h3 : ε / (3 * (c + 1)) * c < ε / 3 := by
        rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    obtain ⟨N, δ, hδ0, herr, hpre⟩ := exists_rieszRow_small hRH (ε := ε / 3)
      (by positivity) hη0 n₀
    set b := rieszRow N δ with hb
    refine ⟨N, ditherRow b, fun k _ => ditherRow_mem b k, ?_⟩
    have hbw : ∀ k, ∃ w : ℝ, 0 ≤ w ∧ w ≤ 1 ∧ b k = sharpMobiusRow k * w :=
      fun k => rieszRow_eq_mul N hδ0.le k
    have hA : ∀ K ≤ n₀, |∑ k ∈ Finset.Ioc 0 K, (ditherRow b k - b k)| ≤ η := by
      intro K hK
      rw [sum_ditherRow_sub_eq_ditherState]
      refine (abs_ditherState_le_prefix b hpre hη1 K hK).trans ?_
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => abs_nonneg _)) hpre
      intro x hx; simp only [Finset.mem_Ioc] at hx ⊢; omega
    have hB : ∀ K, |∑ k ∈ Finset.Ioc 0 K, (ditherRow b k - b k)| ≤ 1 := fun K => by
      rw [sum_ditherRow_sub_eq_ditherState]; exact abs_ditherState_le_one hbw K
    have hcost := chronologicalL2Norm_le_of_partialSums (ditherRow b) b N n₀ hA hB
    rw [← hcdef] at hcost
    have : (η + 1 / Real.sqrt ((n₀ + 1 : ℕ) : ℝ)) * c =
        η * c + 1 / Real.sqrt ((n₀ + 1 : ℕ) : ℝ) * c := by ring
    linarith
  · intro h
    refine riemannHypothesis_of_forall_exists_chronologicalL2Norm_lt 1 zero_le_one fun ε hε => ?_
    obtain ⟨N, a, ha, hlt⟩ := h ε hε
    refine ⟨N, a, fun k hk => ?_, hlt⟩
    rcases ha k hk with h0 | h1
    · rw [h0]; norm_num
    · rw [h1]; unfold sharpMobiusRow; exact_mod_cast ArithmeticFunction.abs_moebius_le_one

end RHTower
