import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Etemadi's weighted extension of the Cesàro limit

If the Cesàro averages `Sₙ/n` of a real sequence converge to `x₀`, then so do the weighted
averages `Wₙ⁻¹ ∑ wᵢxᵢ`, provided the positive weights satisfy

`n wₙ ≤ K Wₙ`  and  `∑_{i<n} (i+1)|w_{i+1} − wᵢ| ≤ K Wₙ`,  with `Wₙ → ∞`.

The statement is Theorem 1 of Etemadi, and although it is used there for random variables the
argument is pathwise, so the deterministic form proved here gives the almost-sure form at once.

The proof is summation by parts applied twice — once to the sequence and once to the constant
sequence `1`, whose partial sums are `n`.  Subtracting the two identities replaces the partial
sums `Sₙ` by the defects `Sₙ − x₀n`, whose size is `n` times a null sequence; the first weight
condition controls the boundary term and the second controls the sum.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.Etemadi

/-- The partial sums of a sequence. -/
def partialSum (x : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, x i

/-- The total weight `Wₙ = ∑_{i<n} wᵢ`. -/
def totalWeight (w : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, w i

/-- The defect `Sₙ − x₀·n` of the partial sums against the limit of the Cesàro averages. -/
def defect (x : ℕ → ℝ) (x₀ : ℝ) (n : ℕ) : ℝ := partialSum x n - x₀ * n

/-- The weighted total variation `Vₙ = ∑_{i<n} (i+1)|w_{i+1} − wᵢ|`. -/
def totalVar (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, ((i : ℝ) + 1) * |w (i + 1) - w i|

lemma partialSum_one (n : ℕ) : partialSum (fun _ => (1 : ℝ)) n = (n : ℝ) := by
  simp [partialSum]

/-- Summation by parts. -/
lemma sum_mul_eq (w x : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, w i * x i
      = w (n - 1) * partialSum x n
        - ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * partialSum x (i + 1) := by
  have h := Finset.sum_range_by_parts (R := ℝ) (M := ℝ) w x n
  simpa [partialSum, smul_eq_mul] using h

/-- Summation by parts for the constant sequence `1`. -/
lemma totalWeight_eq (w : ℕ → ℝ) (n : ℕ) :
    totalWeight w n = w (n - 1) * (n : ℝ)
      - ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * ((i : ℝ) + 1) := by
  have h := sum_mul_eq w (fun _ => (1 : ℝ)) n
  simp only [mul_one, partialSum_one] at h
  push_cast at h
  rw [totalWeight]
  exact h

/-- The two identities combined: the weighted sum against its limit, expressed by the defects. -/
lemma key_identity (w x : ℕ → ℝ) (x₀ : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, w i * x i) - x₀ * totalWeight w n
      = w (n - 1) * defect x x₀ n
        - ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * defect x x₀ (i + 1) := by
  have hsum : ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * defect x x₀ (i + 1)
      = (∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * partialSum x (i + 1))
        - x₀ * ∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * ((i : ℝ) + 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [defect]
    push_cast
    ring
  rw [sum_mul_eq, totalWeight_eq, hsum, defect]
  ring

/-- **Etemadi's weighted extension of the Cesàro limit.**  If the Cesàro averages of a real
sequence converge, so do its weighted averages against positive weights obeying
`n wₙ ≤ K Wₙ`, `Vₙ ≤ K Wₙ` and `Wₙ → ∞`. -/
theorem tendsto_weightedAverage {w x : ℕ → ℝ} {x₀ K : ℝ}
    (hw : ∀ n, 0 < w n)
    (hW : Tendsto (totalWeight w) atTop atTop)
    (hK1 : ∀ n : ℕ, (n : ℝ) * w (n - 1) ≤ K * totalWeight w n)
    (hK2 : ∀ n, totalVar w n ≤ K * totalWeight w n)
    (hx : Tendsto (fun n : ℕ => partialSum x n / (n : ℝ)) atTop (𝓝 x₀)) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, w i * x i) / totalWeight w n) atTop (𝓝 x₀) := by
  -- positivity and monotonicity of the total weight
  have hWpos : ∀ n : ℕ, 0 < n → 0 < totalWeight w n := by
    intro n hn
    refine Finset.sum_pos (fun i _ => hw i) ?_
    exact ⟨0, Finset.mem_range.mpr hn⟩
  have hWmono : Monotone (totalWeight w) := by
    intro m n hmn
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (fun i hi => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hmn)) ?_
    exact fun i _ _ => (hw i).le
  -- the first weight condition forces `1 ≤ K`
  have hK : (1 : ℝ) ≤ K := by
    have h := hK1 1
    have hw0 : (0 : ℝ) < w 0 := hw 0
    have h1 : totalWeight w 1 = w 0 := by simp [totalWeight]
    rw [h1] at h
    simp only [Nat.cast_one, one_mul, Nat.sub_self] at h
    nlinarith [h, hw0]
  have hKpos : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK
  -- the normalized defects form a null sequence
  set δ : ℕ → ℝ := fun n => |defect x x₀ n / (n : ℝ)| with hδdef
  have hδnn : ∀ n, 0 ≤ δ n := fun n => abs_nonneg _
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => partialSum x n / (n : ℝ) - x₀) atTop (𝓝 0) := by
      simpa using hx.sub_const x₀
    have h2 : Tendsto (fun n : ℕ => defect x x₀ n / (n : ℝ)) atTop (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      rw [show defect x x₀ n = partialSum x n - x₀ * (n : ℝ) from rfl, sub_div,
        mul_div_assoc, div_self hn', mul_one]
    simpa using h2.abs
  -- the size of a defect
  have hdef_abs : ∀ n : ℕ, 0 < n → |defect x x₀ n| = δ n * (n : ℝ) := by
    intro n hn
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [hδdef]
    simp only
    rw [abs_div, abs_of_pos hn']
    field_simp
  -- the master estimate
  have hmaster : ∀ (N n : ℕ), 0 < n → N ≤ n - 1 → ∀ η : ℝ, 0 ≤ η →
      (∀ m, N ≤ m → δ m ≤ η) →
      |(∑ i ∈ Finset.range n, w i * x i) / totalWeight w n - x₀|
        ≤ K * δ n
          + (∑ i ∈ Finset.range N, (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1))
              / totalWeight w n
          + η * K := by
    intro N n hn hNn η hη hδη
    have hWn : 0 < totalWeight w n := hWpos n hn
    -- the identity
    have hid := key_identity w x x₀ n
    -- the triangle inequality
    have habs : |(∑ i ∈ Finset.range n, w i * x i) - x₀ * totalWeight w n|
        ≤ w (n - 1) * |defect x x₀ n|
          + ∑ i ∈ Finset.range (n - 1),
              (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1) := by
      rw [hid]
      have htri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
        intro a b
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans (by rw [abs_neg])
      refine (htri _ _).trans ?_
      have hleft : |w (n - 1) * defect x x₀ n| = w (n - 1) * |defect x x₀ n| := by
        rw [abs_mul, abs_of_pos (hw (n - 1))]
      have hright : |∑ i ∈ Finset.range (n - 1), (w (i + 1) - w i) * defect x x₀ (i + 1)|
          ≤ ∑ i ∈ Finset.range (n - 1),
              (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [abs_mul, hdef_abs (i + 1) (Nat.succ_pos i)]
        push_cast
        ring
      rw [hleft]
      exact add_le_add (le_refl _) hright
    -- the boundary term
    have hb : w (n - 1) * |defect x x₀ n| ≤ (K * totalWeight w n) * δ n := by
      rw [hdef_abs n hn]
      have h1 : w (n - 1) * (δ n * (n : ℝ)) = ((n : ℝ) * w (n - 1)) * δ n := by ring
      rw [h1]
      exact mul_le_mul_of_nonneg_right (hK1 n) (hδnn n)
    -- the sum term
    have hs : ∑ i ∈ Finset.range (n - 1), (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1)
        ≤ (∑ i ∈ Finset.range N, (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1))
            + η * (K * totalWeight w n) := by
      rw [← Finset.sum_range_add_sum_Ico _ hNn]
      refine add_le_add (le_refl _) ?_
      have htail : ∑ i ∈ Finset.Ico N (n - 1), (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1)
          ≤ (∑ i ∈ Finset.Ico N (n - 1), ((i : ℝ) + 1) * |w (i + 1) - w i|) * η := by
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun i hi => ?_
        refine mul_le_mul_of_nonneg_left (hδη (i + 1) ?_) ?_
        · exact le_trans (Finset.mem_Ico.mp hi).1 (Nat.le_succ i)
        · positivity
      refine htail.trans ?_
      have hsub : ∑ i ∈ Finset.Ico N (n - 1), ((i : ℝ) + 1) * |w (i + 1) - w i|
          ≤ totalVar w (n - 1) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2) ?_
        exact fun i _ _ => by positivity
      have hV : totalVar w (n - 1) ≤ K * totalWeight w n :=
        (hK2 (n - 1)).trans (mul_le_mul_of_nonneg_left (hWmono (Nat.sub_le n 1)) hKpos.le)
      calc (∑ i ∈ Finset.Ico N (n - 1), ((i : ℝ) + 1) * |w (i + 1) - w i|) * η
          ≤ (K * totalWeight w n) * η :=
            mul_le_mul_of_nonneg_right (hsub.trans hV) hη
        _ = η * (K * totalWeight w n) := by ring
    -- divide
    have hdiv : |(∑ i ∈ Finset.range n, w i * x i) / totalWeight w n - x₀|
        = |(∑ i ∈ Finset.range n, w i * x i) - x₀ * totalWeight w n| / totalWeight w n := by
      rw [← abs_of_pos hWn, ← abs_div, abs_of_pos hWn]
      congr 1
      field_simp
    rw [hdiv, div_le_iff₀ hWn]
    have hfin := habs.trans (add_le_add hb hs)
    calc |(∑ i ∈ Finset.range n, w i * x i) - x₀ * totalWeight w n|
        ≤ (K * totalWeight w n) * δ n
          + ((∑ i ∈ Finset.range N, (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1))
            + η * (K * totalWeight w n)) := hfin
      _ = (K * δ n
            + (∑ i ∈ Finset.range N, (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1))
                / totalWeight w n
            + η * K) * totalWeight w n := by
          field_simp
          ring
  -- the ε-argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hηpos : (0 : ℝ) < ε / (4 * K) := by positivity
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hδ) (ε / (4 * K)) hηpos
  have hδη : ∀ m, N ≤ m → δ m ≤ ε / (4 * K) := by
    intro m hm
    have h := hN m hm
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hδnn m)] at h
    exact h.le
  set H : ℝ := ∑ i ∈ Finset.range N, (((i : ℝ) + 1) * |w (i + 1) - w i|) * δ (i + 1) with hHdef
  have hHnn : 0 ≤ H := by
    rw [hHdef]
    refine Finset.sum_nonneg fun i _ => ?_
    have := hδnn (i + 1)
    positivity
  obtain ⟨N₃, hN₃⟩ := (Filter.tendsto_atTop.mp hW (4 * (H + 1) / ε)).exists_forall_of_atTop
  refine ⟨max (N + 1) N₃, fun n hn => ?_⟩
  have hn1 : N + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : N₃ ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hn1
  have hNn : N ≤ n - 1 := by omega
  have hWn : 0 < totalWeight w n := hWpos n hnpos
  have hWbig : 4 * (H + 1) / ε ≤ totalWeight w n := hN₃ n hn3
  have hmain := hmaster N n hnpos hNn (ε / (4 * K)) hηpos.le hδη
  rw [Real.dist_eq]
  refine lt_of_le_of_lt hmain ?_
  have h1 : K * δ n ≤ ε / 4 := by
    have := hδη n (le_trans (Nat.le_succ N) hn1)
    have h2 : K * δ n ≤ K * (ε / (4 * K)) := mul_le_mul_of_nonneg_left this hKpos.le
    calc K * δ n ≤ K * (ε / (4 * K)) := h2
      _ = ε / 4 := by field_simp
  have h2 : H / totalWeight w n < ε / 4 := by
    have hpos : (0 : ℝ) < 4 * (H + 1) / ε := by positivity
    have hWn' : 0 < totalWeight w n := hWn
    rw [div_lt_iff₀ hWn']
    have h3 : 4 * (H + 1) / ε ≤ totalWeight w n := hWbig
    have h4 : 4 * (H + 1) ≤ ε * totalWeight w n := by
      rw [div_le_iff₀ hε] at h3
      linarith
    linarith
  have h3 : ε / (4 * K) * K = ε / 4 := by field_simp
  rw [h3]
  linarith

/-- For antitone weights the weighted total variation telescopes. -/
lemma totalVar_eq_of_antitone {w : ℕ → ℝ} (hanti : Antitone w) :
    ∀ n : ℕ, totalVar w n = totalWeight w n - (n : ℝ) * w n
  | 0 => by simp [totalVar, totalWeight]
  | n + 1 => by
    have hstep : |w (n + 1) - w n| = w n - w (n + 1) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (hanti (Nat.le_succ n)))]
      ring
    have h1 : totalVar w (n + 1) = totalVar w n + ((n : ℝ) + 1) * |w (n + 1) - w n| := by
      rw [totalVar, totalVar, Finset.sum_range_succ]
    have h2 : totalWeight w (n + 1) = totalWeight w n + w n := by
      rw [totalWeight, totalWeight, Finset.sum_range_succ]
    rw [h1, h2, totalVar_eq_of_antitone hanti n, hstep]
    push_cast
    ring

/-- For nonnegative antitone weights the second Etemadi condition holds with constant one. -/
lemma totalVar_le_of_antitone {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w) (n : ℕ) :
    totalVar w n ≤ totalWeight w n := by
  rw [totalVar_eq_of_antitone hanti n]
  have h : 0 ≤ (n : ℝ) * w n := mul_nonneg (Nat.cast_nonneg n) (hw n)
  linarith

/-- The first Etemadi condition forces its constant to be at least one. -/
lemma one_le_of_weight_cond {w : ℕ → ℝ} {K : ℝ} (hw : ∀ n, 0 < w n)
    (hK1 : ∀ n : ℕ, (n : ℝ) * w (n - 1) ≤ K * totalWeight w n) : (1 : ℝ) ≤ K := by
  have h := hK1 1
  have hw0 : (0 : ℝ) < w 0 := hw 0
  have h1 : totalWeight w 1 = w 0 := by simp [totalWeight]
  rw [h1] at h
  simp only [Nat.cast_one, one_mul, Nat.sub_self] at h
  nlinarith [h, hw0]

/-- **Etemadi's weighted extension for monotone weights.**  For antitone positive weights the
second condition is automatic, so only `n wₙ ≤ K Wₙ` and `Wₙ → ∞` have to be checked. -/
theorem tendsto_weightedAverage_of_antitone {w x : ℕ → ℝ} {x₀ K : ℝ}
    (hw : ∀ n, 0 < w n) (hanti : Antitone w)
    (hW : Tendsto (totalWeight w) atTop atTop)
    (hK1 : ∀ n : ℕ, (n : ℝ) * w (n - 1) ≤ K * totalWeight w n)
    (hx : Tendsto (fun n : ℕ => partialSum x n / (n : ℝ)) atTop (𝓝 x₀)) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, w i * x i) / totalWeight w n) atTop (𝓝 x₀) := by
  have hK : (1 : ℝ) ≤ K := one_le_of_weight_cond hw hK1
  refine tendsto_weightedAverage hw hW hK1 (fun n => ?_) hx
  refine (totalVar_le_of_antitone (fun m => (hw m).le) hanti n).trans ?_
  have hWn : 0 ≤ totalWeight w n :=
    Finset.sum_nonneg fun i _ => (hw i).le
  nlinarith [hWn, hK]

end GaloisForLFunctions.HTGeometry.Etemadi
