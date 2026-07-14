import Mathlib

/-!
# Riemann-sum error bounds for monotone integrands

For a monotone (or antitone) integrand the left-endpoint Riemann sum over unit steps differs from the
integral by at most the total rise `f(x₀+a) - f(x₀)` — first order in the step and controlled by the
total variation, the *bounded-variation* analogue of the second-order Lipschitz Riemann-sum bound.

mathlib's `Mathlib/Analysis/SumIntegralComparisons.lean` provides the one-sided sandwich
(`MonotoneOn.sum_le_integral`, `MonotoneOn.integral_le_sum`); the two-sided *error* bound below —
the shape needed for a bounded-variation quadrature `H_W` — is packaged here.  Any bounded-variation
integrand is a difference of monotone functions, so these two lemmas control its Riemann-sum error by the
variation of each monotone part.
-/

open Finset MeasureTheory intervalIntegral

namespace HTGeometry

/-- **Monotone Riemann-sum error bound.**  For `f` monotone on `[x₀, x₀+a]` (unit steps, count `a`), the
left-endpoint Riemann sum differs from the integral by at most the total rise `f(x₀+a) - f(x₀)`.  Proof:
sandwich `∑ f(x₀+i) ≤ ∫ ≤ ∑ f(x₀+i+1)` (mathlib), whose gap telescopes to `f(x₀+a) - f(x₀)`. -/
theorem abs_sum_sub_integral_le_of_monotoneOn {f : ℝ → ℝ} {x₀ : ℝ} {a : ℕ}
    (hf : MonotoneOn f (Set.Icc x₀ (x₀ + a))) :
    |(∑ i ∈ Finset.range a, f (x₀ + i)) - ∫ x in x₀..x₀ + a, f x| ≤ f (x₀ + a) - f x₀ := by
  have h1 : (∑ i ∈ Finset.range a, f (x₀ + i)) ≤ ∫ x in x₀..x₀ + a, f x := hf.sum_le_integral
  have h2 : (∫ x in x₀..x₀ + a, f x) ≤ ∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ)) := hf.integral_le_sum
  have htel : (∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ))) - (∑ i ∈ Finset.range a, f (x₀ + i))
      = f (x₀ + a) - f x₀ := by
    rw [← Finset.sum_sub_distrib]
    have := Finset.sum_range_sub (fun i => f (x₀ + (i : ℝ))) a
    push_cast at this ⊢; simpa using this
  rw [abs_of_nonpos (by linarith)]; linarith

/-- **Antitone Riemann-sum error bound.**  The mirror of the monotone case: for `f` antitone the
left-endpoint Riemann sum error is at most the total fall `f(x₀) - f(x₀+a)`.  Obtained by applying the
monotone bound to `-f`. -/
theorem abs_sum_sub_integral_le_of_antitoneOn {f : ℝ → ℝ} {x₀ : ℝ} {a : ℕ}
    (hf : AntitoneOn f (Set.Icc x₀ (x₀ + a))) :
    |(∑ i ∈ Finset.range a, f (x₀ + i)) - ∫ x in x₀..x₀ + a, f x| ≤ f x₀ - f (x₀ + a) := by
  have h := abs_sum_sub_integral_le_of_monotoneOn hf.neg
  rw [Finset.sum_neg_distrib, intervalIntegral.integral_neg] at h
  rw [show -(∑ i ∈ Finset.range a, f (x₀ + (i : ℝ))) - -(∫ x in x₀..x₀ + a, f x)
      = -((∑ i ∈ Finset.range a, f (x₀ + (i : ℝ))) - (∫ x in x₀..x₀ + a, f x)) by ring, abs_neg] at h
  linarith

/-- **Monotone Riemann-sum error at mesh `1/k`.**  For `f` monotone on `[c, c + n/k]` (`n` cells of
width `1/k`, `k > 0`), the mid-mesh Riemann sum `(1/k)·∑_{i<n} f(c + i/k)` differs from the integral by
at most `(1/k)·(f(c+n/k) - f(c))` — the total rise scaled by the mesh.  Reduced to the unit-step bound
`abs_sum_sub_integral_le_of_monotoneOn` by the affine substitution `t ↦ c + t/k`
(`intervalIntegral.integral_comp_add_mul`).  This is the quadrature error at the arithmetic mesh `n/k`
that a bounded-variation prime-window error `H_W` sums over. -/
theorem abs_sum_sub_integral_le_of_monotoneOn_scaled {g : ℝ → ℝ} {c k : ℝ} (hk : 0 < k) {n : ℕ}
    (hg : MonotoneOn g (Set.Icc c (c + n / k))) :
    |(1 / k) * (∑ i ∈ Finset.range n, g (c + i / k)) - ∫ u in c..c + n / k, g u|
      ≤ (1 / k) * (g (c + n / k) - g c) := by
  have hk0 : k ≠ 0 := hk.ne'
  have hmapsto : Set.MapsTo (fun t => c + t / k) (Set.Icc (0 : ℝ) (n : ℝ))
      (Set.Icc c (c + (n : ℝ) / k)) := by
    intro t ht
    refine ⟨by have : 0 ≤ t / k := div_nonneg ht.1 hk.le; linarith, ?_⟩
    have : t / k ≤ (n : ℝ) / k := by gcongr; exact ht.2
    linarith
  have hmono_aff : MonotoneOn (fun t => c + t / k) (Set.Icc (0 : ℝ) (n : ℝ)) := by
    intro t₁ _ t₂ _ h; simp only; gcongr
  have hf : MonotoneOn (fun t => g (c + t / k)) (Set.Icc (0 : ℝ) (0 + (n : ℝ))) := by
    rw [zero_add]; exact hg.comp hmono_aff hmapsto
  have hbase := abs_sum_sub_integral_le_of_monotoneOn (x₀ := (0 : ℝ)) (a := n) hf
  have hcov : (∫ t in (0 : ℝ)..(n : ℝ), g (c + t / k)) = k * ∫ u in c..(c + (n : ℝ) / k), g u := by
    have hint_eq : (∫ t in (0 : ℝ)..(n : ℝ), g (c + t / k))
        = ∫ t in (0 : ℝ)..(n : ℝ), g (c + k⁻¹ * t) := by
      apply intervalIntegral.integral_congr; intro t _
      show g (c + t / k) = g (c + k⁻¹ * t)
      rw [div_eq_inv_mul]
    rw [hint_eq, intervalIntegral.integral_comp_add_mul g (inv_ne_zero hk0) c, inv_inv, smul_eq_mul]
    simp only [mul_zero, add_zero, inv_mul_eq_div]
  simp only [zero_add, zero_div, add_zero] at hbase
  rw [hcov] at hbase
  have hexp : (1 / k) * (∑ i ∈ Finset.range n, g (c + i / k)) - ∫ u in c..c + (n : ℝ) / k, g u
      = (1 / k) * ((∑ i ∈ Finset.range n, g (c + i / k)) - k * ∫ u in c..c + (n : ℝ) / k, g u) := by
    field_simp
  rw [hexp, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / k)]
  exact mul_le_mul_of_nonneg_left hbase (by positivity : (0 : ℝ) ≤ 1 / k)

/-- **Antitone Riemann-sum error at mesh `1/k`.**  The mirror of the scaled monotone bound: for `g`
antitone on `[c, c+n/k]` the mesh-`1/k` Riemann-sum error is at most `(1/k)·(g(c) - g(c+n/k))`, the total
fall scaled by the mesh.  This is the direct tool for a decreasing Mellin integrand such as `u ↦ u^{-s}`
(`s > 0`) on a positive interval.  Obtained by applying the scaled monotone bound to `-g`. -/
theorem abs_sum_sub_integral_le_of_antitoneOn_scaled {g : ℝ → ℝ} {c k : ℝ} (hk : 0 < k) {n : ℕ}
    (hg : AntitoneOn g (Set.Icc c (c + n / k))) :
    |(1 / k) * (∑ i ∈ Finset.range n, g (c + i / k)) - ∫ u in c..c + n / k, g u|
      ≤ (1 / k) * (g c - g (c + n / k)) := by
  have h := abs_sum_sub_integral_le_of_monotoneOn_scaled hk hg.neg
  rw [Finset.sum_neg_distrib, intervalIntegral.integral_neg, mul_neg,
    show -((1 / k) * ∑ i ∈ Finset.range n, g (c + i / k)) - -(∫ u in c..c + n / k, g u)
      = -((1 / k) * (∑ i ∈ Finset.range n, g (c + i / k)) - ∫ u in c..c + n / k, g u) by ring,
    abs_neg] at h
  exact le_of_le_of_eq h (by ring)

/-- **Bounded-variation Riemann-sum error at mesh `1/k`.**  For an integrand given by a Jordan
decomposition `p - q` with `p, q` monotone on `[c, c + n/k]`, the mesh-`1/k` Riemann-sum error is at most
`(1/k)·(total variation)`, where the total variation `(p(c+n/k) - p c) + (q(c+n/k) - q c)` is the sum of
the two monotone rises.  Since every bounded-variation function is such a difference (its Jordan
decomposition), this controls the quadrature error of *any* BV integrand — the estimate a
bounded-variation prime-window error `H_W` is built on.  Proof: the error is additive, so it splits as
`error(p) - error(q)`, and the triangle inequality with the monotone bound
`abs_sum_sub_integral_le_of_monotoneOn_scaled` on each part gives the variation bound. -/
theorem abs_sum_sub_integral_le_of_bv_scaled {p q : ℝ → ℝ} {c k : ℝ} (hk : 0 < k) {n : ℕ}
    (hp : MonotoneOn p (Set.Icc c (c + n / k)))
    (hq : MonotoneOn q (Set.Icc c (c + n / k))) :
    |(1 / k) * (∑ i ∈ Finset.range n, (p (c + i / k) - q (c + i / k)))
        - ∫ u in c..c + n / k, (p u - q u)|
      ≤ (1 / k) * ((p (c + n / k) - p c) + (q (c + n / k) - q c)) := by
  have hle : c ≤ c + (n : ℝ) / k := by
    have h0 : (0 : ℝ) ≤ (n : ℝ) / k := by positivity
    linarith
  have huicc : Set.uIcc c (c + (n : ℝ) / k) = Set.Icc c (c + (n : ℝ) / k) := Set.uIcc_of_le hle
  have hpint : IntervalIntegrable p MeasureTheory.volume c (c + n / k) :=
    (hp.mono (by rw [huicc])).intervalIntegrable
  have hqint : IntervalIntegrable q MeasureTheory.volume c (c + n / k) :=
    (hq.mono (by rw [huicc])).intervalIntegrable
  have hp' := abs_sum_sub_integral_le_of_monotoneOn_scaled hk hp
  have hq' := abs_sum_sub_integral_le_of_monotoneOn_scaled hk hq
  rw [Finset.sum_sub_distrib, intervalIntegral.integral_sub hpint hqint]
  have hrw : (1 / k) * ((∑ i ∈ Finset.range n, p (c + i / k)) - ∑ i ∈ Finset.range n, q (c + i / k))
      - ((∫ u in c..c + n / k, p u) - ∫ u in c..c + n / k, q u)
      = ((1 / k) * (∑ i ∈ Finset.range n, p (c + i / k)) - ∫ u in c..c + n / k, p u)
        - ((1 / k) * (∑ i ∈ Finset.range n, q (c + i / k)) - ∫ u in c..c + n / k, q u) := by ring
  rw [hrw]
  calc |((1 / k) * (∑ i ∈ Finset.range n, p (c + i / k)) - ∫ u in c..c + n / k, p u)
        - ((1 / k) * (∑ i ∈ Finset.range n, q (c + i / k)) - ∫ u in c..c + n / k, q u)|
      ≤ |(1 / k) * (∑ i ∈ Finset.range n, p (c + i / k)) - ∫ u in c..c + n / k, p u|
        + |(1 / k) * (∑ i ∈ Finset.range n, q (c + i / k)) - ∫ u in c..c + n / k, q u| := abs_sub _ _
    _ ≤ (1 / k) * (p (c + n / k) - p c) + (1 / k) * (q (c + n / k) - q c) := add_le_add hp' hq'
    _ = (1 / k) * ((p (c + n / k) - p c) + (q (c + n / k) - q c)) := by ring

end HTGeometry
