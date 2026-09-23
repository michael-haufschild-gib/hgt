import GaloisForLFunctions.HTGeometry.MaximumTermLegendreBound

/-!
# The deviation series under Gaussian concentration

With the uniform exponential decay away from the central index in hand, the weighted deviation
series splits into a window of half-width `N` around the central index — where the weight is at most
`N` — and two tails on which the terms decay at the rate `N / (4L)` per unit of deviation.

The result is the estimate a Wiman--Valiron argument needs: the whole remainder is `N` times the
window sum plus a geometric tail whose ratio improves as the window widens.  Unlike the estimates
built from the one-radius geometric bound, the tail here is exponentially small in `N^(2 : ℕ) / L`, so a
window of half-width comparable to `sqrt(L log ...)` already makes it negligible.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

variable {a : ℕ → ℂ}

/-- Weighted geometric series shifted by `N + 1` terms. -/
private theorem summable_shifted_weight {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (N : ℕ) :
    Summable fun j : ℕ => ((N : ℝ) + 1 + j) * q ^ (N + 1 + j) := by
  have h1 : Summable fun j : ℕ => (j : ℝ) * q ^ j := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
      (by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1)
  have h2 : Summable fun j : ℕ => q ^ j := summable_geometric_of_lt_one hq0.le hq1
  have h3 : Summable fun j : ℕ => ((N : ℝ) + 1 + j) * q ^ j := by
    refine ((h2.mul_left ((N : ℝ) + 1)).add h1).congr fun j => ?_
    ring
  refine (h3.mul_left (q ^ (N + 1))).congr fun j => ?_
  rw [pow_add]
  ring

/-- The exponential decay rate written as a power. -/
private theorem exp_rate_pow {L : ℝ} (hL : 0 < L) (N k : ℕ) :
    Real.exp (-((k : ℝ) * (N : ℝ) / (4 * L)))
      = Real.exp (-((N : ℝ) / (4 * L))) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp

/-- **The deviation series under Gaussian concentration.**  A window of half-width `N` around the
central index contributes at most `N` times the window sum; outside it the terms decay at the rate
`N / (4L)` per unit of deviation, so both tails are dominated by one shifted geometric series. -/
theorem tsum_index_deviation_le_gaussian
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) {x H L v₀ : ℝ} (hH : 0 < H) (hL : 0 < L)
    {N : ℕ} (hN0 : 0 < N) (hNK : (N : ℝ) ≤ 2 * L * H) (hNv : 2 * L * v₀ ≤ (N : ℝ))
    (hlipA : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp (x + v)) : ℝ) ≤ (centralIndex a (Real.exp x) : ℝ) + L * v)
    (hlipB : ∀ v : ℝ, v₀ ≤ v → v ≤ H →
      (centralIndex a (Real.exp x) : ℝ) - L * v ≤ (centralIndex a (Real.exp (x - v)) : ℝ))
    {W : ℝ}
    (hW : ∑ n ∈ Finset.Ico (centralIndex a (Real.exp x) - N)
              (centralIndex a (Real.exp x) + N + 1), ‖a n‖ * Real.exp x ^ n ≤ W) :
    ∑' n : ℕ, |(n : ℝ) - (centralIndex a (Real.exp x) : ℝ)| * (‖a n‖ * Real.exp x ^ n)
      ≤ (N : ℝ) * W
        + 2 * maxTerm a (Real.exp x)
            * ∑' j : ℕ, ((N : ℝ) + 1 + j)
                * Real.exp (-((N : ℝ) / (4 * L))) ^ (N + 1 + j) := by
  classical
  set r : ℝ := Real.exp x with hr
  have hrpos : 0 < r := Real.exp_pos x
  set v : ℕ := centralIndex a r with hv
  set μ : ℝ := maxTerm a r with hμdef
  have hμ : (0 : ℝ) ≤ μ := le_trans (term_nonneg a hrpos 0) (term_le_maxTerm ha hrpos 0)
  set q : ℝ := Real.exp (-((N : ℝ) / (4 * L))) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
    have : (0 : ℝ) < (N : ℝ) / (4 * L) := by positivity
    linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set D : ℕ → ℝ := fun n => |(n : ℝ) - (v : ℝ)| * (‖a n‖ * r ^ n) with hD
  have hDnn : ∀ n, 0 ≤ D n := fun n => mul_nonneg (abs_nonneg _) (term_nonneg a hrpos n)
  have hDsum : Summable D := summable_index_deviation ha hrpos v
  set f : ℕ → ℝ := fun j => ((N : ℝ) + 1 + j) * q ^ (N + 1 + j) with hf
  have hfsum : Summable f := summable_shifted_weight hq0 hq1 N
  have hfnn : ∀ j, 0 ≤ f j := by
    intro j
    have : (0 : ℝ) ≤ (N : ℝ) + 1 + j := by positivity
    exact mul_nonneg this (pow_nonneg hq0.le _)
  -- the pointwise bound outside the window, in the two directions
  have hdecay_up : ∀ j : ℕ, D (j + (v + N + 1)) ≤ μ * f j := by
    intro j
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = j + (v + N + 1) := ⟨_, rfl⟩
    rw [← hn]
    have hk : ((N : ℝ) + 1 + j) = (n : ℝ) - (v : ℝ) := by
      rw [hn]; push_cast; ring
    have hkK : (N : ℝ) ≤ (n : ℝ) - (v : ℝ) := by
      rw [← hk]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hterm := term_le_maxTerm_exp_uniform_above (x := x) ha hn₀ hH hL hNpos hNK hNv hlipA
      (n := n) (k := (n : ℝ) - (v : ℝ)) rfl hkK
    have habs : |(n : ℝ) - (v : ℝ)| = (N : ℝ) + 1 + j := by
      rw [← hk, abs_of_nonneg (by positivity)]
    have hexp : Real.exp (-(((n : ℝ) - (v : ℝ)) * (N : ℝ) / (4 * L))) = q ^ (N + 1 + j) := by
      have hcast : ((N + 1 + j : ℕ) : ℝ) = (n : ℝ) - (v : ℝ) := by
        rw [← hk]; push_cast; ring
      rw [hq, ← exp_rate_pow hL N (N + 1 + j), hcast]
    calc D n = |(n : ℝ) - (v : ℝ)| * (‖a n‖ * r ^ n) := rfl
      _ ≤ ((N : ℝ) + 1 + j) * (μ * Real.exp (-(((n : ℝ) - (v : ℝ)) * (N : ℝ) / (4 * L)))) := by
          rw [habs]
          exact mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = μ * f j := by rw [hexp, hf]; ring
  have hdecay_down : ∀ j : ℕ, j < v - N → D (v - N - 1 - j) ≤ μ * f j := by
    intro j hj
    have hvN : N < v := by omega
    obtain ⟨n, hn⟩ : ∃ n : ℕ, n = v - N - 1 - j := ⟨_, rfl⟩
    rw [← hn]
    have hle : N + 1 + j ≤ v := by omega
    have hnv : (n : ℝ) = (v : ℝ) - ((N : ℝ) + 1 + j) := by
      have hne : n = v - (N + 1 + j) := by omega
      rw [hne, Nat.cast_sub hle]
      push_cast
      ring
    have hk : ((N : ℝ) + 1 + j) = (v : ℝ) - (n : ℝ) := by rw [hnv]; ring
    have hkK : (N : ℝ) ≤ (v : ℝ) - (n : ℝ) := by
      rw [← hk]
      have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hterm := term_le_maxTerm_exp_uniform_below (x := x) ha hn₀ hH hL hNpos hNK hNv hlipB
      (n := n) (k := (v : ℝ) - (n : ℝ)) rfl hkK
    have habs : |(n : ℝ) - (v : ℝ)| = (N : ℝ) + 1 + j := by
      rw [hk, abs_sub_comm, abs_of_nonneg (by linarith [hkK, hNpos])]
    have hexp : Real.exp (-(((v : ℝ) - (n : ℝ)) * (N : ℝ) / (4 * L))) = q ^ (N + 1 + j) := by
      have hcast : ((N + 1 + j : ℕ) : ℝ) = (v : ℝ) - (n : ℝ) := by
        rw [← hk]; push_cast; ring
      rw [hq, ← exp_rate_pow hL N (N + 1 + j), hcast]
    calc D n = |(n : ℝ) - (v : ℝ)| * (‖a n‖ * r ^ n) := rfl
      _ ≤ ((N : ℝ) + 1 + j) * (μ * Real.exp (-(((v : ℝ) - (n : ℝ)) * (N : ℝ) / (4 * L)))) := by
          rw [habs]
          exact mul_le_mul_of_nonneg_left hterm (by positivity)
      _ = μ * f j := by rw [hexp, hf]; ring
  -- the window
  have hwin : ∑ n ∈ Finset.Ico (v - N) (v + N + 1), D n ≤ (N : ℝ) * W := by
    have hpt : ∀ n ∈ Finset.Ico (v - N) (v + N + 1),
        D n ≤ (N : ℝ) * (‖a n‖ * r ^ n) := by
      intro n hn
      obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
      have habs : |(n : ℝ) - (v : ℝ)| ≤ (N : ℝ) := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · rcases le_or_gt N v with hNv | hNv
          · have : v - N ≤ n := hn1
            have hcast : ((v - N : ℕ) : ℝ) = (v : ℝ) - (N : ℝ) := by
              push_cast [Nat.cast_sub hNv]; ring
            have : ((v - N : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
            rw [hcast] at this
            linarith
          · have hvN : (v : ℝ) < (N : ℝ) := by exact_mod_cast hNv
            have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            linarith
        · have : (n : ℝ) ≤ (v : ℝ) + (N : ℝ) := by
            have : n ≤ v + N := by omega
            exact_mod_cast this
          linarith
      exact mul_le_mul_of_nonneg_right habs (term_nonneg a hrpos n)
    have hstep := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum] at hstep
    exact le_trans hstep (mul_le_mul_of_nonneg_left hW (le_of_lt hNpos))
  -- the lower block
  have hlow : ∑ n ∈ Finset.Ico 0 (v - N), D n ≤ μ * ∑' j : ℕ, f j := by
    rw [← Finset.range_eq_Ico]
    have hrefl : ∑ n ∈ Finset.range (v - N), D n
        = ∑ j ∈ Finset.range (v - N), D (v - N - 1 - j) :=
      (Finset.sum_range_reflect (fun n => D n) (v - N)).symm
    rw [hrefl]
    have hbd : ∀ j ∈ Finset.range (v - N), D (v - N - 1 - j) ≤ μ * f j := by
      intro j hj
      exact hdecay_down j (Finset.mem_range.mp hj)
    refine le_trans (Finset.sum_le_sum hbd) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hμ
    exact Summable.sum_le_tsum _ (fun j _ => hfnn j) hfsum
  -- the upper block
  have hup : ∑' j : ℕ, D (j + (v + N + 1)) ≤ μ * ∑' j : ℕ, f j := by
    have hsumL : Summable fun j : ℕ => D (j + (v + N + 1)) :=
      (summable_nat_add_iff (v + N + 1)).mpr hDsum
    have hle := Summable.tsum_le_tsum hdecay_up hsumL (hfsum.mul_left μ)
    rwa [tsum_mul_left] at hle
  -- assemble
  have hsplit := Summable.sum_add_tsum_nat_add (f := D) (v + N + 1) hDsum
  have hcons : (∑ n ∈ Finset.Ico 0 (v - N), D n) + ∑ n ∈ Finset.Ico (v - N) (v + N + 1), D n
      = ∑ n ∈ Finset.Ico 0 (v + N + 1), D n :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)
  calc ∑' n : ℕ, D n
      = (∑ n ∈ Finset.Ico 0 (v + N + 1), D n) + ∑' j : ℕ, D (j + (v + N + 1)) := by
        rw [← hsplit, Finset.range_eq_Ico]
    _ = (∑ n ∈ Finset.Ico 0 (v - N), D n) + (∑ n ∈ Finset.Ico (v - N) (v + N + 1), D n)
        + ∑' j : ℕ, D (j + (v + N + 1)) := by rw [hcons]
    _ ≤ μ * (∑' j : ℕ, f j) + (N : ℝ) * W + μ * ∑' j : ℕ, f j := by
        gcongr
    _ = (N : ℝ) * W + 2 * μ * ∑' j : ℕ, f j := by ring

end GaloisForLFunctions.HTGeometry
