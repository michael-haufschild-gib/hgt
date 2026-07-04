/-
Doc 52 (task #159): the (CR-density) proved bridges.

* `finset_chebyshev` — finite Chebyshev counting: the number of samples with
  |f| ≥ λ is at most (Σ f²)/λ². This is the variance→anti-concentration
  bridge of doc 52 §8: a second-moment bound on log|F_N| caps the number of
  near-line zeros.
* `far_kernel_lower` / `pricing_pigeonhole` — the tangency pricing of doc 52
  §3: a Poisson-kernel sum that reaches a large negative value while every
  contributing zero is at distance ≥ c must contain a zero with kernel below
  −1/c — i.e. a zero c-close to the evaluation point. The analytic
  decomposition (partial fractions + tail bound) is the named open input;
  the pigeonhole itself is machine-checked here.
-/
import Mathlib

namespace RHTower

/-- **Finite Chebyshev counting (doc 52 §8 bridge)**: samples beyond λ in
absolute value number at most (Σ f²)/λ². -/
theorem finset_chebyshev {ι : Type*} (s : Finset ι) (f : ι → ℝ) {lam : ℝ}
    (hlam : 0 < lam) :
    (((s.filter fun i => lam ≤ |f i|).card : ℝ))
      ≤ (∑ i ∈ s, f i ^ 2) / lam ^ 2 := by
  have hmul : ((s.filter fun i => lam ≤ |f i|).card : ℝ) * lam ^ 2
      ≤ ∑ i ∈ s, f i ^ 2 := by
    have h1 : ((s.filter fun i => lam ≤ |f i|).card : ℝ) * lam ^ 2
        = ∑ _i ∈ s.filter fun i => lam ≤ |f i|, lam ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [h1]
    calc ∑ i ∈ s.filter fun i => lam ≤ |f i|, lam ^ 2
        ≤ ∑ i ∈ s.filter fun i => lam ≤ |f i|, f i ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hfi := (Finset.mem_filter.mp hi).2
          calc lam ^ 2 ≤ |f i| ^ 2 := by nlinarith [abs_nonneg (f i)]
            _ = f i ^ 2 := sq_abs _
      _ ≤ ∑ i ∈ s, f i ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ s)
          intro i _ _
          positivity
  calc ((s.filter fun i => lam ≤ |f i|).card : ℝ)
      = ((s.filter fun i => lam ≤ |f i|).card : ℝ) * lam ^ 2 / lam ^ 2 := by
        field_simp
    _ ≤ (∑ i ∈ s, f i ^ 2) / lam ^ 2 := by gcongr

/-- A Poisson kernel at planar distance ≥ c from its zero is bounded below
by −1/c: far zeros cannot supply a deep kernel deficit. -/
theorem far_kernel_lower {u w c : ℝ} (hc : 0 < c) (hu : 0 ≤ u)
    (hfar : c ^ 2 ≤ u ^ 2 + w ^ 2) :
    -(1 / c) ≤ -(u / (u ^ 2 + w ^ 2)) := by
  have hden : 0 < u ^ 2 + w ^ 2 := by nlinarith
  rw [neg_le_neg_iff]
  rcases eq_or_lt_of_le hu with h0 | hupos
  · rw [← h0]
    simp only [zero_div]
    positivity
  · have hkey : u * c ≤ u ^ 2 + w ^ 2 := by
      rcases le_total u c with h | h
      · nlinarith
      · nlinarith
    have hpos : 0 < u * c := mul_pos hupos hc
    calc u / (u ^ 2 + w ^ 2) ≤ u / (u * c) := by gcongr
      _ = u * 1 / (u * c) := by ring
      _ = 1 / c := mul_div_mul_left 1 c hupos.ne'

/-- **The pricing pigeonhole (doc 52 §3)**: if a kernel sum plus a bounded
error reaches below −(B + n/c), some zero's kernel is below −1/c — by
`far_kernel_lower`, that zero is c-close to the evaluation point. -/
theorem pricing_pigeonhole {ι : Type*} {Z : Finset ι} {kernel : ι → ℝ}
    {E B c v : ℝ} (hE : |E| ≤ B)
    (hval : v = (∑ ρ ∈ Z, kernel ρ) + E)
    (hv : v < -(B + (Z.card : ℝ) / c)) :
    ∃ ρ ∈ Z, kernel ρ < -(1 / c) := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hsum := Finset.card_nsmul_le_sum Z kernel (-(1 / c)) hcon
  rw [nsmul_eq_mul] at hsum
  have hEc : -B ≤ E := by
    have := neg_abs_le E
    linarith
  have hfin : -(B + (Z.card : ℝ) / c) ≤ v := by
    rw [hval]
    have hcard : (Z.card : ℝ) * (-(1 / c)) = -((Z.card : ℝ) / c) := by ring
    rw [hcard] at hsum
    linarith
  linarith

end RHTower
