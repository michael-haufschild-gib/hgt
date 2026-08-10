import GaloisForLFunctions.RHTower.Sieve.FibreSmoothQuasiConcave

/-!
# Where the fibre kernel lives

Two vanishing statements confine the shifted correlation sum to a rectangle of size `h × √x`.

* **In the shift.**  An outer index `a ≥ √x` with `x ≤ a·n` and `a·(n+k) ≤ x + h√x` forces
  `a·k ≤ h√x`, hence `k ≤ h`: shifts beyond `h` contribute nothing.
* **In the inner variable.**  The same `a ≥ √x` with `a·n ≤ x + h√x ≤ 2x` forces `n ≤ 2√x`, and the
  smooth model vanishes just as fast; so both are supported on `n ≤ 3√x`.

Consequently the error term of the smooth/error split, which is bounded by `2` and has no
cancellation to offer, costs only `2 · h · 3√x` — a factor `h` below the target `o(h²√x)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- **The kernel vanishes for shifts larger than `h`.** -/
theorem fibre_kernel_eq_empty_of_shift {x h : ℝ} (hx : 4 ≤ x) {i k : ℕ}
    (hk : h < (k : ℝ)) :
    (outerBlock x h).filter
      (fun a => (i + k) ∈ innerFibre x h a ∧ i ∈ innerFibre x h a) = ∅ := by
  classical
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := two_le_sqrt hx
  refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
  rw [Finset.mem_filter, mem_outerBlock, mem_innerFibre, mem_innerFibre] at ha
  obtain ⟨⟨-, hsa, -⟩, ⟨-, -, hup⟩, -, hlow, -⟩ := ha
  have hcast1 : ((a * (i + k) : ℕ) : ℝ) = (a : ℝ) * ((i : ℝ) + (k : ℝ)) := by push_cast; ring
  have hcast2 : ((a * i : ℕ) : ℝ) = (a : ℝ) * (i : ℝ) := by push_cast; ring
  rw [hcast1] at hup
  rw [hcast2] at hlow
  have hak : (a : ℝ) * (k : ℝ) ≤ h * Real.sqrt x := by nlinarith [hup, hlow]
  have hsk : Real.sqrt x * (k : ℝ) ≤ h * Real.sqrt x := by
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hak, hsa, hk0]
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  nlinarith [hsk, hk, hs0]

/-- **The kernel vanishes once the inner variable exceeds `3√x`.** -/
theorem fibre_kernel_eq_empty_of_large {x h : ℝ} (hx : 4 ≤ x) (hhx : h ≤ Real.sqrt x)
    {i k : ℕ} (hi : 3 * Real.sqrt x ≤ (i : ℝ)) :
    (outerBlock x h).filter
      (fun a => (i + k) ∈ innerFibre x h a ∧ i ∈ innerFibre x h a) = ∅ := by
  classical
  have hs2 : (2 : ℝ) ≤ Real.sqrt x := two_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  refine Finset.eq_empty_of_forall_notMem fun a ha => ?_
  rw [Finset.mem_filter, mem_outerBlock, mem_innerFibre, mem_innerFibre] at ha
  obtain ⟨⟨-, hsa, -⟩, -, -, -, hup⟩ := ha
  have hcast : ((a * i : ℕ) : ℝ) = (a : ℝ) * (i : ℝ) := by push_cast; ring
  rw [hcast] at hup
  have hwin : h * Real.sqrt x ≤ x := by nlinarith [hhx, hsq, hs2]
  have hbig : 3 * x ≤ (a : ℝ) * (i : ℝ) := by nlinarith [hsa, hi, hsq, hs2]
  linarith

/-- **The smooth model vanishes once the inner variable exceeds `3√x`.** -/
theorem fibreSmooth_eq_zero_of_large {x h : ℝ} (hx : 16 ≤ x) (hh : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {i : ℕ} (k : ℕ) (hi : 3 * Real.sqrt x ≤ (i : ℝ)) :
    fibreSmooth x h k i = 0 := by
  have hs4 : (4 : ℝ) ≤ Real.sqrt x := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
    rw [← h16]
    exact Real.sqrt_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hwin : h * Real.sqrt x ≤ x := by nlinarith [hhx, hsq, hs4]
  have hden : (0 : ℝ) < ((i + k : ℕ) : ℝ) := by
    have : (3 : ℝ) * Real.sqrt x ≤ ((i + k : ℕ) : ℝ) := by
      have : (i : ℝ) ≤ ((i + k : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
      linarith
    linarith
  have hbig : 3 * Real.sqrt x ≤ ((i + k : ℕ) : ℝ) := by
    have : (i : ℝ) ≤ ((i + k : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
    linarith
  have hhigh : fibreHigh x h (i + k) ≤ 2 * Real.sqrt x / 3 := by
    refine le_trans (fibreHigh_le_div x h (i + k)) ?_
    rw [div_le_iff₀ hden]
    have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
    nlinarith [hbig, hwin, hsq, hs0]
  have hlow : Real.sqrt x ≤ fibreLow x i := sqrt_le_fibreLow x i
  rw [fibreSmooth, kernelSmooth, max_eq_right (by linarith)]

/-- **A bounded weight supported on an initial segment: the trivial bound.** -/
theorem abs_error_shift_sum_supported_le {e g : ℕ → ℕ → ℝ} {J : ℕ}
    (he : ∀ k j, |e k j| ≤ 2) (hsupp : ∀ k j, J ≤ j → e k j = 0)
    (hg : ∀ k j, |g k j| ≤ 1) (K N : ℕ) :
    |∑ k ∈ Finset.Icc 1 K, ∑ j ∈ Finset.range N, e k j * g k j| ≤ 2 * K * J := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hrow : ∀ k ∈ Finset.Icc 1 K,
      |∑ j ∈ Finset.range N, e k j * g k j| ≤ 2 * (J : ℝ) := by
    intro k _
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ j ∈ Finset.range N, |e k j * g k j| ≤ (if j < J then (2 : ℝ) else 0) := by
      intro j _
      by_cases hj : j < J
      · rw [if_pos hj, abs_mul]
        calc |e k j| * |g k j| ≤ |e k j| * 1 :=
              mul_le_mul_of_nonneg_left (hg k j) (abs_nonneg _)
          _ = |e k j| := mul_one _
          _ ≤ 2 := he k j
      · rw [if_neg hj, hsupp k j (by omega)]
        simp
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((((Finset.range N).filter (fun j => j < J)).card : ℕ) : ℝ) ≤ (J : ℝ) := by
      have hsub : ((Finset.range N).filter (fun j => j < J)).card ≤ J := by
        have : (Finset.range N).filter (fun j => j < J) ⊆ Finset.range J := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
          exact hj.2
        have := Finset.card_le_card this
        rwa [Finset.card_range] at this
      exact_mod_cast hsub
    linarith
  refine le_trans (Finset.sum_le_card_nsmul _ _ (2 * (J : ℝ)) hrow) ?_
  rw [nsmul_eq_mul, Nat.card_Icc]
  have hcard : (((K + 1 - 1 : ℕ) : ℝ)) ≤ (K : ℝ) := by simp
  have hJ0 : (0 : ℝ) ≤ 2 * (J : ℝ) := by positivity
  calc (((K + 1 - 1 : ℕ) : ℝ)) * (2 * (J : ℝ)) ≤ (K : ℝ) * (2 * (J : ℝ)) :=
        mul_le_mul_of_nonneg_right hcard hJ0
    _ = 2 * K * J := by ring

end RHTower.Sieve

end
