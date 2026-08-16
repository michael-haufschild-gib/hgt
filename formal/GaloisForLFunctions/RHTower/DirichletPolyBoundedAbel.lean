import GaloisForLFunctions.RHTower.DirichletSecondDifference
import GaloisForLFunctions.RHTower.DirichletWidthOne

/-!
# Polynomially bounded partial sums

Abel summation with a polynomial bound on the coefficient partial sums:

```text
‖∑_{n<N} aₙ‖ ≤ C (N+1)ᵅ    ⟹    ∑ aₙ (n+1)^{−s} converges for Re s > α .
```

The bounded case `α = 0` is `tendsto_dirichlet_partialSum_of_bounded`.  The unit first difference of
the kernel is `O(x^{−Re s−1})`, so the Abel sum is dominated by `∑ (i+1)^{α−Re s−1}`, convergent
exactly when `Re s > α`; the boundary term is `O(N^{α−Re s})`.

The exponent `α` is sharp and cannot be improved: taking the partial sums to be `(−1)^k k^α` gives
an alternating Dirichlet series whose abscissa of convergence is exactly `α`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **The unit first difference of the kernel, at any exponent with positive real part.** -/
theorem norm_cpow_unit_diff_le {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-w) - ((x + 1 : ℝ) : ℂ) ^ (-w)‖ ≤ ‖w‖ * x ^ (-w.re - 1) := by
  have hstep := norm_cpow_neg_sub_le hw hx (by linarith : x ≤ x + 1)
  have hreal := rpow_sub_rpow_succ_le hw hx
  have hcoef : (0 : ℝ) ≤ ‖w‖ / w.re := by positivity
  refine le_trans hstep ?_
  refine le_trans (mul_le_mul_of_nonneg_left hreal hcoef) ?_
  have hne : w.re ≠ 0 := ne_of_gt hw
  have hval : ‖w‖ / w.re * (w.re * x ^ (-w.re - 1)) = ‖w‖ * x ^ (-w.re - 1) := by
    field_simp
  rw [hval]

/-- **Abel summation with polynomially bounded partial sums.** -/
theorem tendsto_dirichlet_partialSum_of_poly_bounded {a : ℕ → ℂ} {C α : ℝ}
    (hC0 : 0 ≤ C) (hα : 0 ≤ α)
    (hC : ∀ N : ℕ, ‖∑ n ∈ Finset.range N, a n‖ ≤ C * ((N : ℝ) + 1) ^ α)
    {s : ℂ} (hs : α < s.re) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, a n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
      atTop (𝓝 L) := by
  classical
  have hspos : 0 < s.re := lt_of_le_of_lt hα hs
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ α := Real.one_le_rpow (by norm_num) hα
  have htwo0 : (0 : ℝ) < (2 : ℝ) ^ α := by positivity
  set b : ℕ → ℂ := fun i => (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) with hbdef
  set A : ℕ → ℂ := fun k => ∑ n ∈ Finset.range k, a n with hAdef
  have hbsucc : ∀ i : ℕ, b (i + 1) = (((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s) := by
    intro i
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = (i : ℝ) + 2 := by push_cast; ring
    show (((((i + 1 : ℕ) : ℝ)) + 1 : ℝ) : ℂ) ^ (-s) = (((i : ℝ) + 2 : ℝ) : ℂ) ^ (-s)
    rw [hcast]
  have hincr : ∀ i : ℕ, ‖b (i + 1) - b i‖ ≤ ‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1) := by
    intro i
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hstep := norm_cpow_unit_diff_le hspos hx
    have hrw : (((i : ℝ) + 1 + 1 : ℝ) : ℂ) = (((i : ℝ) + 2 : ℝ) : ℂ) := by
      congr 1
      ring
    rw [hrw] at hstep
    rw [hbsucc i, hbdef, norm_sub_rev]
    exact hstep
  have hAbound : ∀ i : ℕ, ‖A (i + 1)‖ ≤ C * (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α := by
    intro i
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have h := hC (i + 1)
    have hcast : ((i + 1 : ℕ) : ℝ) + 1 = ((i : ℝ) + 1) + 1 := by push_cast; ring
    rw [hcast] at h
    refine le_trans h ?_
    have hle : ((i : ℝ) + 1) + 1 ≤ 2 * ((i : ℝ) + 1) := by linarith
    have hmono : (((i : ℝ) + 1) + 1) ^ α ≤ (2 * ((i : ℝ) + 1)) ^ α :=
      Real.rpow_le_rpow (by positivity) hle hα
    have hsplit : (2 * ((i : ℝ) + 1)) ^ α = (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α :=
      Real.mul_rpow (by norm_num) hx.le
    rw [mul_assoc, ← hsplit]
    exact mul_le_mul_of_nonneg_left hmono hC0
  have hmaj : Summable
      (fun i : ℕ => (‖s‖ * (C * (2 : ℝ) ^ α)) * ((i : ℝ) + 1) ^ (-(s.re + 1 - α))) := by
    refine (summable_shift_rpow_neg ?_).mul_left _
    linarith
  have hsummand : Summable (fun i : ℕ => (b (i + 1) - b i) * A (i + 1)) := by
    refine Summable.of_norm_bounded hmaj fun i => ?_
    have hx : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hprod : ‖(b (i + 1) - b i) * A (i + 1)‖
        ≤ (‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1)) * (C * (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α) := by
      rw [norm_mul]
      exact mul_le_mul (hincr i) (hAbound i) (norm_nonneg _) (by positivity)
    refine le_trans hprod (le_of_eq ?_)
    have hcomb : ((i : ℝ) + 1) ^ (-s.re - 1) * ((i : ℝ) + 1) ^ α
        = ((i : ℝ) + 1) ^ (-(s.re + 1 - α)) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    calc (‖s‖ * ((i : ℝ) + 1) ^ (-s.re - 1)) * (C * (2 : ℝ) ^ α * ((i : ℝ) + 1) ^ α)
        = (‖s‖ * (C * (2 : ℝ) ^ α))
          * (((i : ℝ) + 1) ^ (-s.re - 1) * ((i : ℝ) + 1) ^ α) := by ring
      _ = (‖s‖ * (C * (2 : ℝ) ^ α)) * ((i : ℝ) + 1) ^ (-(s.re + 1 - α)) := by rw [hcomb]
  obtain ⟨T, hT⟩ := hsummand
  refine ⟨-T, ?_⟩
  have habel : ∀ N : ℕ, (∑ n ∈ Finset.range N, a n * b n)
      = b (N - 1) * A N - ∑ i ∈ Finset.range (N - 1), (b (i + 1) - b i) * A (i + 1) := by
    intro N
    have h := Finset.sum_range_by_parts b a N
    simp only [smul_eq_mul] at h
    rw [show (∑ n ∈ Finset.range N, a n * b n) = ∑ n ∈ Finset.range N, b n * a n from
      Finset.sum_congr rfl fun n _ => mul_comm _ _]
    exact h
  have hTend1 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N - 1), (b (i + 1) - b i) * A (i + 1))
      atTop (𝓝 T) :=
    hT.tendsto_sum_nat.comp (Filter.tendsto_sub_atTop_nat 1)
  have hTend2 : Tendsto (fun N : ℕ => b (N - 1) * A N) atTop (𝓝 0) := by
    have hmajT : Tendsto (fun N : ℕ => (C * (2 : ℝ) ^ α) * ((N : ℝ)) ^ (-(s.re - α)))
        atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_nat_atTop (show (0 : ℝ) < s.re - α by linarith)).const_mul
        (C * (2 : ℝ) ^ α)
      simpa using h
    refine squeeze_zero_norm' ?_ hmajT
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : (1 : ℕ) ≤ N := hN
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
      have hval : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub hN]; norm_num
      rw [hval]; ring
    have hbnorm : ‖b (N - 1)‖ = (N : ℝ) ^ (-s.re) := by
      rw [hbdef]
      simp only
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
      congr 1
    have hAn : ‖A N‖ ≤ C * (2 : ℝ) ^ α * (N : ℝ) ^ α := by
      have h := hC N
      refine le_trans h ?_
      have hle : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hmono : ((N : ℝ) + 1) ^ α ≤ (2 * (N : ℝ)) ^ α :=
        Real.rpow_le_rpow (by positivity) hle hα
      have hsplit : (2 * (N : ℝ)) ^ α = (2 : ℝ) ^ α * (N : ℝ) ^ α :=
        Real.mul_rpow (by norm_num) hNpos.le
      rw [mul_assoc, ← hsplit]
      exact mul_le_mul_of_nonneg_left hmono hC0
    rw [norm_mul, hbnorm]
    have hstep : (N : ℝ) ^ (-s.re) * ‖A N‖
        ≤ (N : ℝ) ^ (-s.re) * (C * (2 : ℝ) ^ α * (N : ℝ) ^ α) :=
      mul_le_mul_of_nonneg_left hAn (Real.rpow_nonneg hNpos.le _)
    refine le_trans hstep (le_of_eq ?_)
    rw [show (N : ℝ) ^ (-s.re) * (C * (2 : ℝ) ^ α * (N : ℝ) ^ α)
        = (C * (2 : ℝ) ^ α) * ((N : ℝ) ^ (-s.re) * (N : ℝ) ^ α) by ring,
      ← Real.rpow_add hNpos]
    congr 2
    ring
  have hcomb : Tendsto (fun N : ℕ => b (N - 1) * A N
      - ∑ i ∈ Finset.range (N - 1), (b (i + 1) - b i) * A (i + 1)) atTop (𝓝 (0 - T)) :=
    hTend2.sub hTend1
  have hfinal : Tendsto (fun N => ∑ n ∈ Finset.range N, a n * b n) atTop (𝓝 (0 - T)) :=
    hcomb.congr fun N => (habel N).symm
  simp only [hbdef] at hfinal
  rw [zero_sub] at hfinal
  exact hfinal

end GaloisForLFunctions.RHTower

end
