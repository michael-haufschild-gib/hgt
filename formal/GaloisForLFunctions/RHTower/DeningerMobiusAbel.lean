import GaloisForLFunctions.RHTower.DeningerMobiusPreimage
import GaloisForLFunctions.RHTower.DeningerMertensInvSquare

/-!
# Abel summation for the canonical Möbius preimage

Summation by parts moves the Möbius weight off the pullback and onto the summatory function: the
boundary term is `H_h(nx) M(n)`, which vanishes because the pullback decays like an inverse square
while `M` grows at most linearly, and what is left is the difference series

`f_h(x) = -∑_n M(n) (H_h((n+1)x) - H_h(nx))`.

This is the discrete form of the card's `(10)`.  It is what converts the arithmetic input
`∑_N |M(N)|/N² < ∞` into an estimate for the preimage, because a difference `H_h((n+1)x) - H_h(nx)`
integrates against `dx` to `1/(n(n+1))` times a fixed weighted mass of `H_h'`.

* `deningerMertensM_abs_le` : `|M(n)| ≤ n + 1`.
* `deningerAbelBoundary_tendsto_zero` : the boundary term vanishes.
* `deningerMobius_abel` : **the Abel identity, as a limit of partial sums.**
-/

namespace RHTower

open SchwartzMap ArithmeticFunction Filter Topology

noncomputable section

/-! ## The two elementary inputs -/

/-- The summatory function grows at most linearly. -/
theorem deningerMertensM_abs_le (n : ℕ) : |Sieve.mertensM n| ≤ (n : ℝ) + 1 := by
  rw [Sieve.mertensM]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ j ∈ Finset.range (n + 1), |((moebius j : ℤ) : ℝ)| ≤ 1 := by
    intro j _
    rcases moebius_eq_or j with h | h | h <;> rw [h] <;> norm_num
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  linarith

/-- The boundary term of the summation by parts vanishes. -/
theorem deningerAbelBoundary_tendsto_zero {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => deningerLogPull h ((n : ℝ) * x) * ((Sieve.mertensM n : ℝ) : ℂ))
      atTop (𝓝 0) := by
  obtain ⟨C, hCnn, hC⟩ := deningerLogPull_norm_le_inv_sq hh
  have hxsq : (0 : ℝ) < x ^ 2 := by positivity
  have hmaj : Tendsto (fun n : ℕ => (C / x ^ 2) * (1 / (n : ℝ) + 1 / (n : ℝ) ^ 2))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
      have hm := h1.mul h1
      rw [mul_zero] at hm
      refine hm.congr fun n => ?_
      rw [div_mul_div_comm, one_mul, ← pow_two]
    have := (h1.add h2).const_mul (C / x ^ 2)
    simpa using this
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnx : (0 : ℝ) < (n : ℝ) * x := mul_pos hnr hx
  have hH := (hC ((n : ℝ) * x) hnx).2
  have hM : ‖((Sieve.mertensM n : ℝ) : ℂ)‖ ≤ (n : ℝ) + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact deningerMertensM_abs_le n
  rw [norm_mul]
  have hstep : ‖deningerLogPull h ((n : ℝ) * x)‖ * ‖((Sieve.mertensM n : ℝ) : ℂ)‖
      ≤ (C / ((n : ℝ) * x) ^ 2) * ((n : ℝ) + 1) :=
    mul_le_mul hH hM (norm_nonneg _) (by positivity)
  refine le_trans hstep (le_of_eq ?_)
  field_simp

/-! ## The Abel identity -/

/-- **Abel summation for the canonical Möbius preimage.**  The difference series converges to
`-f_h(x)`: summation by parts moves the Möbius weight onto the summatory function, and the
boundary term vanishes. -/
theorem deningerMobius_abel {h : 𝓢(ℝ, ℂ)} (hh : h ∈ DeningerExpSchwartz) {x : ℝ}
    (hx : 0 < x) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
        (deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)) *
          ((Sieve.mertensM i : ℝ) : ℂ))
      atTop (𝓝 (-deningerMobiusPreimage h x)) := by
  classical
  set F : ℕ → ℂ := fun i => deningerLogPull h ((i : ℝ) * x) with hF
  set G : ℕ → ℂ := fun i => ((moebius i : ℤ) : ℂ) with hG
  have hMsum : ∀ i : ℕ, (∑ j ∈ Finset.range (i + 1), G j) = ((Sieve.mertensM i : ℝ) : ℂ) := by
    intro i
    rw [Sieve.mertensM, hG]
    push_cast
    ring
  have hparts : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, (F (i + 1) - F i) * ((Sieve.mertensM i : ℝ) : ℂ))
        = F n * ((Sieve.mertensM n : ℝ) : ℂ)
          - ∑ i ∈ Finset.range (n + 1), F i * G i := by
    intro n
    have hbp := Finset.sum_range_by_parts F G (n + 1)
    simp only [Nat.add_sub_cancel, smul_eq_mul] at hbp
    rw [hMsum n] at hbp
    have hinner : ∀ i ∈ Finset.range n,
        (F (i + 1) - F i) * (∑ j ∈ Finset.range (i + 1), G j)
          = (F (i + 1) - F i) * ((Sieve.mertensM i : ℝ) : ℂ) := by
      intro i _
      rw [hMsum i]
    rw [Finset.sum_congr rfl hinner] at hbp
    linear_combination hbp
  have hpartial : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n + 1), F i * G i)
      atTop (𝓝 (deningerMobiusPreimage h x)) := by
    have hsum := deningerMobiusRay_summable hh hx
    have hhas : HasSum (fun i : ℕ => F i * G i) (deningerMobiusPreimage h x) := by
      have hcongr : ∀ i : ℕ, F i * G i
          = ((moebius i : ℤ) : ℂ) * deningerLogPull h ((i : ℝ) * x) := by
        intro i
        rw [hF, hG]
        ring
      have := hsum.hasSum
      rw [← deningerMobiusPreimage_eq] at this
      exact this.congr_fun fun i => hcongr i
    exact (hhas.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hbdry := deningerAbelBoundary_tendsto_zero hh hx
  have hcomb : Tendsto (fun n : ℕ => F n * ((Sieve.mertensM n : ℝ) : ℂ)
      - ∑ i ∈ Finset.range (n + 1), F i * G i) atTop
      (𝓝 (0 - deningerMobiusPreimage h x)) := hbdry.sub hpartial
  have hfinal : Tendsto (fun n : ℕ =>
      ∑ i ∈ Finset.range n, (F (i + 1) - F i) * ((Sieve.mertensM i : ℝ) : ℂ)) atTop
      (𝓝 (0 - deningerMobiusPreimage h x)) := by
    refine hcomb.congr fun n => (hparts n).symm
  rw [zero_sub] at hfinal
  refine hfinal.congr fun n => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF]
  congr 3
  push_cast
  ring

end

end RHTower
