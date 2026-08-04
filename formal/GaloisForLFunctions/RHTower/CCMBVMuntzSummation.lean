import GaloisForLFunctions.RHTower.CCMSawtoothDilationMean
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import GaloisForLFunctions.RHTower.FractionalPartZeta

/-!
# The bounded-variation summation vector of a zero-mean compact source

For a source of bounded variation supported in `[0, L]` with vanishing integral, the arithmetic
summation vector

```text
E(f)(u) = √u ∑_{n ≥ 1} f (n u)
```

is bounded by `Var(f) √u`.  The estimate is a Riemann-sum discrepancy: on each interval
`((n-1)u, nu]` the right-endpoint value differs from the mean by at most the variation there, and the
variations over a partition add up to at most the total variation.

* `abs_sum_riemann_sub_integral_le` — the discrepancy bound, with no hypothesis on the support or the
  integral: `|u ∑_{n ≤ N} f(nu) - ∫_0^{Nu} f| ≤ u Var(f)`.
* `integral_eq_zero_of_support_le` — a source supported in `[0, L]` with vanishing integral has
  vanishing truncated integral past `L`.
* `abs_sum_le_variation` — the card's `(7)`: `|∑_{n ≥ 1} f(nu)| ≤ Var(f)`.
* `abs_summationVector_le` — the card's first bound in `(3)`: `|E(f)(u)| ≤ Var(f) √u`.
* `summationVector_eq_zero_of_lt` — the card's support statement in `(3)`: `E(f)` vanishes past `L`.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory intervalIntegral Set Filter Topology

/-! ## The Riemann-sum discrepancy of a function of bounded variation -/

/-- On one cell the right-endpoint value differs from the mean by at most the variation there. -/
theorem abs_cell_discrepancy_le {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hbv : BoundedVariationOn f univ) {a b : ℝ} (hab : a ≤ b) :
    |(b - a) * f b - ∫ x in a..b, f x|
      ≤ (b - a) * (eVariationOn f (Icc a b)).toReal := by
  have hbvI : BoundedVariationOn f (Icc a b) := hbv.mono (subset_univ _)
  have hfi : IntervalIntegrable f volume a b := intervalIntegrable_of_bound hm hbnd a b
  have hci : IntervalIntegrable (fun _ : ℝ => f b) volume a b := intervalIntegrable_const
  have hconst : (∫ _ in a..b, f b) = (b - a) * f b := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have hsub : (∫ x in a..b, (f b - f x)) = (b - a) * f b - ∫ x in a..b, f x := by
    rw [intervalIntegral.integral_sub hci hfi, hconst]
  have hbound : ∀ x ∈ Set.uIoc a b,
      ‖f b - f x‖ ≤ (eVariationOn f (Icc a b)).toReal := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hxmem : x ∈ Icc a b := ⟨hx.1.le, hx.2⟩
    have hbmem : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have := hbvI.dist_le hbmem hxmem
    rwa [Real.dist_eq] at this
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs, hsub] at h
  calc |(b - a) * f b - ∫ x in a..b, f x|
      ≤ (eVariationOn f (Icc a b)).toReal * |b - a| := h
    _ = (b - a) * (eVariationOn f (Icc a b)).toReal := by
        rw [abs_of_nonneg (by linarith)]
        ring

/-- The variations over a uniform partition add up to at most the total variation. -/
theorem sum_variation_cells_le {f : ℝ → ℝ} (hbv : BoundedVariationOn f univ) {u : ℝ}
    (hu : 0 < u) (N : ℕ) :
    ∑ i ∈ Finset.range N, (eVariationOn f (Icc ((i : ℝ) * u) (((i : ℝ) + 1) * u))).toReal
      ≤ (eVariationOn f univ).toReal := by
  have hI : Monotone (fun i : ℕ => (i : ℝ) * u) := by
    intro i j hij
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    nlinarith
  have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) * u = ((i : ℝ) + 1) * u := by
    intro i; push_cast; ring
  have hfin : ∀ i : ℕ,
      eVariationOn f (Icc ((i : ℝ) * u) (((i : ℝ) + 1) * u)) ≠ ⊤ := by
    intro i
    exact ne_top_of_le_ne_top hbv (eVariationOn.mono f (subset_univ _))
  have hsum := eVariationOn.sum' f hI (n := N)
  simp only [hcast] at hsum
  have hle : eVariationOn f (Icc ((0 : ℕ) * u : ℝ) ((N : ℕ) * u : ℝ))
      ≤ eVariationOn f univ := eVariationOn.mono f (subset_univ _)
  have htoReal : ∑ i ∈ Finset.range N,
      (eVariationOn f (Icc ((i : ℝ) * u) (((i : ℝ) + 1) * u))).toReal
      = (∑ i ∈ Finset.range N,
        eVariationOn f (Icc ((i : ℝ) * u) (((i : ℝ) + 1) * u))).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => hfin i)]
  rw [htoReal, hsum]
  exact ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hbv hle) hbv |>.mpr hle

/-- **The bounded-variation Riemann-sum discrepancy.**  No hypothesis on the support or the integral
is needed. -/
theorem abs_sum_riemann_sub_integral_le {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hbv : BoundedVariationOn f univ) {u : ℝ} (hu : 0 < u) (N : ℕ) :
    |u * (∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * u)) - ∫ x in (0 : ℝ)..((N : ℝ) * u), f x|
      ≤ u * (eVariationOn f univ).toReal := by
  have hI : Monotone (fun i : ℕ => (i : ℝ) * u) := by
    intro i j hij
    have : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    nlinarith
  have hcast : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) * u = ((i : ℝ) + 1) * u := by
    intro i; push_cast; ring
  -- split the integral over the cells
  have hpart := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) * u) (f := f) (n := N)
    (fun i _ => intervalIntegrable_of_bound hm hbnd _ _)
  simp only [hcast] at hpart
  have hzero : ((0 : ℕ) : ℝ) * u = 0 := by norm_num
  rw [hzero] at hpart
  -- reindex the Riemann sum
  have hreindex : ∀ M : ℕ, (∑ n ∈ Finset.Icc 1 M, f ((n : ℝ) * u))
      = ∑ i ∈ Finset.range M, f (((i : ℝ) + 1) * u) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      have hc : ((M + 1 : ℕ) : ℝ) * u = ((M : ℝ) + 1) * u := by push_cast; ring
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), Finset.sum_range_succ, ih, hc]
  -- combine cell by cell
  have hcell : ∀ i ∈ Finset.range N,
      |u * f (((i : ℝ) + 1) * u) - ∫ x in ((i : ℝ) * u)..(((i : ℝ) + 1) * u), f x|
        ≤ u * (eVariationOn f (Icc ((i : ℝ) * u) (((i : ℝ) + 1) * u))).toReal := by
    intro i _
    have hab : (i : ℝ) * u ≤ ((i : ℝ) + 1) * u := by nlinarith
    have hlen : ((i : ℝ) + 1) * u - (i : ℝ) * u = u := by ring
    have h := abs_cell_discrepancy_le hm hbnd hbv hab
    rwa [hlen] at h
  have hsplit : u * (∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * u))
      - ∫ x in (0 : ℝ)..((N : ℝ) * u), f x
      = ∑ i ∈ Finset.range N, (u * f (((i : ℝ) + 1) * u)
        - ∫ x in ((i : ℝ) * u)..(((i : ℝ) + 1) * u), f x) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hreindex N, hpart]
  rw [hsplit]
  calc |∑ i ∈ Finset.range N, (u * f (((i : ℝ) + 1) * u)
        - ∫ x in ((i : ℝ) * u)..(((i : ℝ) + 1) * u), f x)|
      ≤ ∑ i ∈ Finset.range N, |u * f (((i : ℝ) + 1) * u)
        - ∫ x in ((i : ℝ) * u)..(((i : ℝ) + 1) * u), f x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N,
        u * (eVariationOn f (Icc ((i : ℝ) * u) (((i : ℝ) + 1) * u))).toReal :=
        Finset.sum_le_sum hcell
    _ = u * ∑ i ∈ Finset.range N,
        (eVariationOn f (Icc ((i : ℝ) * u) (((i : ℝ) + 1) * u))).toReal := by
        rw [Finset.mul_sum]
    _ ≤ u * (eVariationOn f univ).toReal :=
        mul_le_mul_of_nonneg_left (sum_variation_cells_le hbv hu N) hu.le

/-! ## The summation vector of a compactly supported zero-mean source -/

theorem sum_Icc_eq_sum_range_shift (f : ℝ → ℝ) (u : ℝ) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, f ((n : ℝ) * u))
      = ∑ i ∈ Finset.range M, f (((i : ℝ) + 1) * u) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hc : ((M + 1 : ℕ) : ℝ) * u = ((M : ℝ) + 1) * u := by push_cast; ring
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), Finset.sum_range_succ, ih, hc]

/-- Past the support the truncated integral of a zero-mean compact source still vanishes. -/
theorem integral_trunc_eq_zero {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ} (hbnd : ∀ x, |f x| ≤ B)
    {L u : ℝ} {N : ℕ} (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0)
    (hint : (∫ x in (0 : ℝ)..L, f x) = 0) (hLN : L ≤ (N : ℝ) * u) :
    (∫ x in (0 : ℝ)..((N : ℝ) * u), f x) = 0 := by
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := L) (c := (N : ℝ) * u)
    (intervalIntegrable_of_bound hm hbnd 0 L)
    (intervalIntegrable_of_bound hm hbnd L ((N : ℝ) * u))
  have hzero : (∫ x in L..((N : ℝ) * u), f x) = 0 := by
    have h : (∫ x in L..((N : ℝ) * u), f x) = ∫ _ in L..((N : ℝ) * u), (0 : ℝ) := by
      refine integral_congr_of_Ioo hLN fun x hx => ?_
      exact hsupp x fun hmem => absurd hmem.2 (not_le.mpr hx.1)
    rw [h, intervalIntegral.integral_zero]
  rw [← hadj, hint, hzero, add_zero]

/-- **Equation (7).**  The arithmetic sum of a zero-mean compact source of bounded variation is
bounded by its total variation, uniformly in the sampling scale. -/
theorem abs_sum_le_variation {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ} (hbnd : ∀ x, |f x| ≤ B)
    (hbv : BoundedVariationOn f univ) {L u : ℝ} {N : ℕ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hint : (∫ x in (0 : ℝ)..L, f x) = 0)
    (hu : 0 < u) (hLN : L ≤ (N : ℝ) * u) :
    |∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * u)| ≤ (eVariationOn f univ).toReal := by
  have h := abs_sum_riemann_sub_integral_le hm hbnd hbv hu N
  rw [integral_trunc_eq_zero hm hbnd hsupp hint hLN, sub_zero, abs_mul, abs_of_pos hu] at h
  exact le_of_mul_le_mul_left h hu

/-! ## The summation vector -/

/-- **Equation (2).**  The CCM arithmetic summation vector. -/
def summationVector (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  Real.sqrt u * ∑' n : ℕ, f (((n : ℝ) + 1) * u)

theorem summationVector_eq_finset {f : ℝ → ℝ} {L u : ℝ} {N : ℕ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hu : 0 < u) (hLN : L ≤ (N : ℝ) * u) :
    summationVector f u = Real.sqrt u * ∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * u) := by
  have hvanish : ∀ b ∉ Finset.range N, f (((b : ℝ) + 1) * u) = 0 := by
    intro b hb
    rw [Finset.mem_range] at hb
    have hbN : (N : ℝ) ≤ (b : ℝ) := by
      have : N ≤ b := by omega
      exact_mod_cast this
    refine hsupp _ fun hmem => ?_
    have hgt : L < ((b : ℝ) + 1) * u := by nlinarith
    exact absurd hmem.2 (not_le.mpr hgt)
  rw [summationVector, tsum_eq_sum hvanish, sum_Icc_eq_sum_range_shift]

/-- **Equation (3), the support statement.**  The summation vector vanishes past the support. -/
theorem summationVector_eq_zero_of_lt {f : ℝ → ℝ} {L u : ℝ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hu : 0 < u) (hLu : L < u) :
    summationVector f u = 0 := by
  have h := summationVector_eq_finset hsupp hu (N := 1) (by simpa using hLu.le)
  rw [h]
  have hone : (∑ n ∈ Finset.Icc (1 : ℕ) 1, f ((n : ℝ) * u)) = f u := by
    simp
  rw [hone, hsupp u fun hmem => absurd hmem.2 (not_le.mpr hLu), mul_zero]

/-- **Equation (3), the pointwise bound.**  `|E(f)(u)| ≤ Var(f) √u`. -/
theorem abs_summationVector_le {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ} (hbnd : ∀ x, |f x| ≤ B)
    (hbv : BoundedVariationOn f univ) {L u : ℝ} {N : ℕ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hint : (∫ x in (0 : ℝ)..L, f x) = 0)
    (hu : 0 < u) (hLN : L ≤ (N : ℝ) * u) :
    |summationVector f u| ≤ (eVariationOn f univ).toReal * Real.sqrt u := by
  rw [summationVector_eq_finset hsupp hu hLN, abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg u)]
  calc Real.sqrt u * |∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * u)|
      ≤ Real.sqrt u * (eVariationOn f univ).toReal :=
        mul_le_mul_of_nonneg_left
          (abs_sum_le_variation hm hbnd hbv hsupp hint hu hLN) (Real.sqrt_nonneg u)
    _ = (eVariationOn f univ).toReal * Real.sqrt u := by ring

/-! ## Measurability and the `L²(d*u)` bound -/

theorem exists_index_ge {L u : ℝ} (hu : 0 < u) : ∃ N : ℕ, L ≤ (N : ℝ) * u := by
  refine ⟨⌈L / u⌉₊, ?_⟩
  have h := Nat.le_ceil (L / u)
  rw [div_le_iff₀ hu] at h
  linarith

theorem summationVector_eq_zero_of_nonpos {f : ℝ → ℝ} {L : ℝ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) {u : ℝ} (hu : u ≤ 0) :
    summationVector f u = 0 := by
  have hzero : ∀ n : ℕ, f (((n : ℝ) + 1) * u) = 0 := by
    intro n
    refine hsupp _ fun hmem => ?_
    have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have : ((n : ℝ) + 1) * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnn hu
    exact absurd hmem.1 (not_lt.mpr this)
  rw [summationVector]
  simp [hzero]

theorem summable_summand {f : ℝ → ℝ} {L : ℝ} (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0)
    (u : ℝ) : Summable (fun n : ℕ => f (((n : ℝ) + 1) * u)) := by
  rcases le_or_gt u 0 with hu | hu
  · have hzero : ∀ n : ℕ, f (((n : ℝ) + 1) * u) = 0 := by
      intro n
      refine hsupp _ fun hmem => ?_
      have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have : ((n : ℝ) + 1) * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnn hu
      exact absurd hmem.1 (not_lt.mpr this)
    exact summable_of_ne_finset_zero (s := ∅) fun b _ => hzero b
  · obtain ⟨N, hN⟩ := exists_index_ge (L := L) hu
    refine summable_of_ne_finset_zero (s := Finset.range N) fun b hb => ?_
    rw [Finset.mem_range] at hb
    have hbN : (N : ℝ) ≤ (b : ℝ) := by
      have : N ≤ b := by omega
      exact_mod_cast this
    refine hsupp _ fun hmem => ?_
    have hgt : L < ((b : ℝ) + 1) * u := by nlinarith
    exact absurd hmem.2 (not_le.mpr hgt)

theorem measurable_summationVector {f : ℝ → ℝ} (hm : Measurable f) {L : ℝ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) :
    Measurable (summationVector f) := by
  have hpartial : ∀ N : ℕ, Measurable fun u : ℝ =>
      Real.sqrt u * ∑ i ∈ Finset.range N, f (((i : ℝ) + 1) * u) := by
    intro N
    refine (Real.continuous_sqrt.measurable).mul ?_
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hm.comp (measurable_id.const_mul _)
  refine measurable_of_tendsto_metrizable' atTop hpartial ?_
  rw [tendsto_pi_nhds]
  intro u
  exact ((summable_summand hsupp u).hasSum.tendsto_sum_nat).const_mul _

/-- **Equation (3), the `L²(d*u)` bound.**  `‖1_(0,L] E(f)‖²_{L²(d*u)} ≤ Var(f)² L`. -/
theorem integral_sq_summationVector_le {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hbv : BoundedVariationOn f univ) {L : ℝ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hint : (∫ x in (0 : ℝ)..L, f x) = 0)
    (hL : 0 ≤ L) :
    (∫ u in (0 : ℝ)..L, (summationVector f u) ^ 2 / u)
      ≤ ((eVariationOn f univ).toReal) ^ 2 * L := by
  have hVnn : (0 : ℝ) ≤ (eVariationOn f univ).toReal := ENNReal.toReal_nonneg
  have hptw : ∀ u : ℝ, |(summationVector f u) ^ 2 / u|
      ≤ ((eVariationOn f univ).toReal) ^ 2 := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · rw [summationVector_eq_zero_of_nonpos hsupp hu]
      simp
    · obtain ⟨N, hN⟩ := exists_index_ge (L := L) hu
      have hE := abs_summationVector_le hm hbnd hbv hsupp hint hu hN
      have hsq : (summationVector f u) ^ 2
          ≤ ((eVariationOn f univ).toReal) ^ 2 * u := by
        have h1 : |summationVector f u| ^ 2
            ≤ ((eVariationOn f univ).toReal * Real.sqrt u) ^ 2 := by
          refine pow_le_pow_left₀ (abs_nonneg _) hE 2
        rw [sq_abs] at h1
        calc (summationVector f u) ^ 2
            ≤ ((eVariationOn f univ).toReal * Real.sqrt u) ^ 2 := h1
          _ = ((eVariationOn f univ).toReal) ^ 2 * u := by
              rw [mul_pow, Real.sq_sqrt hu.le]
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ hu]
      linarith
  have hmeas : Measurable fun u : ℝ => (summationVector f u) ^ 2 / u :=
    ((measurable_summationVector hm hsupp).pow_const 2).div measurable_id
  have hint2 : IntervalIntegrable (fun u : ℝ => (summationVector f u) ^ 2 / u) volume 0 L :=
    intervalIntegrable_of_bound hmeas hptw 0 L
  calc (∫ u in (0 : ℝ)..L, (summationVector f u) ^ 2 / u)
      ≤ ∫ _ in (0 : ℝ)..L, ((eVariationOn f univ).toReal) ^ 2 := by
        refine intervalIntegral.integral_mono_on hL hint2 intervalIntegrable_const ?_
        intro u _
        exact le_trans (le_abs_self _) (hptw u)
    _ = ((eVariationOn f univ).toReal) ^ 2 * L := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
        ring

/-- **Equation (3), on the whole half-line.**  `E(f)` lies in `L²(d*u)` with the explicit bound
`Var(f)² L`; the summation vector vanishes past `L`, so the truncated bound is the global one. -/
theorem integral_Ioi_sq_summationVector_le {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hbv : BoundedVariationOn f univ) {L : ℝ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hint : (∫ x in (0 : ℝ)..L, f x) = 0)
    (hL : 0 ≤ L) :
    (∫ u in Ioi (0 : ℝ), (summationVector f u) ^ 2 / u)
      ≤ ((eVariationOn f univ).toReal) ^ 2 * L := by
  have hVnn : (0 : ℝ) ≤ (eVariationOn f univ).toReal := ENNReal.toReal_nonneg
  have hptw : ∀ u : ℝ, |(summationVector f u) ^ 2 / u|
      ≤ ((eVariationOn f univ).toReal) ^ 2 := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · rw [summationVector_eq_zero_of_nonpos hsupp hu]
      simp
    · obtain ⟨N, hN⟩ := exists_index_ge (L := L) hu
      have hE := abs_summationVector_le hm hbnd hbv hsupp hint hu hN
      have hsq : (summationVector f u) ^ 2
          ≤ ((eVariationOn f univ).toReal) ^ 2 * u := by
        have h1 : |summationVector f u| ^ 2
            ≤ ((eVariationOn f univ).toReal * Real.sqrt u) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hE 2
        rw [sq_abs] at h1
        calc (summationVector f u) ^ 2
            ≤ ((eVariationOn f univ).toReal * Real.sqrt u) ^ 2 := h1
          _ = ((eVariationOn f univ).toReal) ^ 2 * u := by
              rw [mul_pow, Real.sq_sqrt hu.le]
      rw [abs_of_nonneg (by positivity), div_le_iff₀ hu]
      linarith
  have hmeas : Measurable fun u : ℝ => (summationVector f u) ^ 2 / u :=
    ((measurable_summationVector hm hsupp).pow_const 2).div measurable_id
  have hzeroPast : ∀ u : ℝ, L < u → (summationVector f u) ^ 2 / u = 0 := by
    intro u hu
    rcases le_or_gt u 0 with h | h
    · rw [summationVector_eq_zero_of_nonpos hsupp h]; simp
    · rw [summationVector_eq_zero_of_lt hsupp h hu]; simp
  have hsplit : Ioc (0 : ℝ) L ∪ Ioi L = Ioi 0 := Ioc_union_Ioi_eq_Ioi hL
  have hIoc : IntegrableOn (fun u : ℝ => (summationVector f u) ^ 2 / u) (Ioc 0 L) := by
    have h := intervalIntegrable_of_bound hmeas hptw 0 L
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mp h
  have hIoi : IntegrableOn (fun u : ℝ => (summationVector f u) ^ 2 / u) (Ioi L) := by
    refine (integrableOn_zero (μ := volume) (s := Ioi L)).congr_fun ?_ measurableSet_Ioi
    intro u hu
    show (0 : ℝ) = (summationVector f u) ^ 2 / u
    rw [hzeroPast u hu]
  have hIoiZero : (∫ u in Ioi L, (summationVector f u) ^ 2 / u) = 0 := by
    rw [MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero]
    intro u hu
    exact hzeroPast u hu
  have hunion : (∫ u in Ioi (0 : ℝ), (summationVector f u) ^ 2 / u)
      = (∫ u in Ioc (0 : ℝ) L, (summationVector f u) ^ 2 / u)
        + ∫ u in Ioi L, (summationVector f u) ^ 2 / u := by
    rw [← hsplit]
    exact MeasureTheory.setIntegral_union (Ioc_disjoint_Ioi_same) measurableSet_Ioi hIoc hIoi
  rw [hunion, hIoiZero, add_zero]
  have hinterval : (∫ u in Ioc (0 : ℝ) L, (summationVector f u) ^ 2 / u)
      = ∫ u in (0 : ℝ)..L, (summationVector f u) ^ 2 / u := by
    rw [intervalIntegral.integral_of_le hL]
  rw [hinterval]
  exact integral_sq_summationVector_le hm hbnd hbv hsupp hint hL

/-! ## The Muntz zeta-multiplier identity -/

theorem aestronglyMeasurable_ofReal_source {f : ℝ → ℝ} (hm : Measurable f) :
    AEStronglyMeasurable (fun t : ℝ => ((f t : ℝ) : ℂ)) (volume.restrict (Ioi 0)) :=
  (Complex.measurable_ofReal.comp hm).aestronglyMeasurable

theorem norm_ofReal_source (f : ℝ → ℝ) (t : ℝ) : ‖((f t : ℝ) : ℂ)‖ = |f t| := by
  rw [Complex.norm_real, Real.norm_eq_abs]

/-- The real Mellin mass of a bounded compactly supported source converges for every positive
exponent. -/
theorem integrableOn_rpow_mul_abs {f : ℝ → ℝ} (hm : Measurable f) {B L : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * |f t|) (Ioi 0) := by
  have hmeas : Measurable fun t : ℝ => t ^ (σ - 1) * |f t| := by
    have h1 : Measurable fun t : ℝ => t ^ (σ - 1) := by fun_prop
    have h2 : Measurable fun t : ℝ => |f t| := by fun_prop
    exact h1.mul h2
  rcases le_or_gt L 0 with hL | hL
  · have hzero : ∀ x : ℝ, f x = 0 := by
      intro x
      refine hsupp x fun hmem => ?_
      exact absurd (lt_of_lt_of_le hmem.1 hmem.2) (not_lt.mpr hL)
    have : (fun t : ℝ => t ^ (σ - 1) * |f t|) = fun _ : ℝ => (0 : ℝ) := by
      funext t; rw [hzero t]; simp
    rw [this]
    exact integrableOn_zero
  · have hsplit : Ioc (0 : ℝ) L ∪ Ioi L = Ioi 0 := Ioc_union_Ioi_eq_Ioi hL.le
    rw [← hsplit, integrableOn_union]
    refine ⟨?_, ?_⟩
    · have hrpow : IntegrableOn (fun t : ℝ => t ^ (σ - 1)) (Ioc 0 L) := by
        have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := L)
          (r := σ - 1) (by linarith)
        exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le).mp h
      have hBrpow : IntegrableOn (fun t : ℝ => B * t ^ (σ - 1)) (Ioc 0 L) := hrpow.const_mul B
      refine hBrpow.mono' hmeas.aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htpos : (0 : ℝ) < t := ht.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg htpos.le _), abs_abs]
      nlinarith [hbnd t, Real.rpow_nonneg htpos.le (σ - 1), abs_nonneg (f t)]
    · refine (integrableOn_zero (μ := volume) (s := Ioi L)).congr_fun ?_ measurableSet_Ioi
      intro t ht
      have hft : f t = 0 := hsupp t fun hmem => absurd hmem.2 (not_le.mpr ht)
      show (0 : ℝ) = t ^ (σ - 1) * |f t|
      rw [hft]
      simp

theorem mellinConvergent_source {f : ℝ → ℝ} (hm : Measurable f) {B L : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((f t : ℝ) : ℂ)) (Ioi 0) := by
  rw [mellin_convergent_iff_norm (subset_refl _) measurableSet_Ioi
    (aestronglyMeasurable_ofReal_source hm)]
  have hcongr : (fun t : ℝ => t ^ (s.re - 1) * ‖((f t : ℝ) : ℂ)‖)
      = fun t : ℝ => t ^ (s.re - 1) * |f t| := by
    funext t
    rw [norm_ofReal_source]
  rw [hcongr]
  exact integrableOn_rpow_mul_abs hm hbnd hsupp hs

/-- Dilating the source scales its real Mellin mass by `m^{-σ}`. -/
theorem integral_rpow_mul_abs_comp_mul {f : ℝ → ℝ} {σ m : ℝ} (hm0 : 0 < m) :
    (∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * |f (m * t)|)
      = m ^ (-σ) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x| := by
  have h := MeasureTheory.integral_comp_mul_left_Ioi
    (fun x : ℝ => (x / m) ^ (σ - 1) * |f x|) 0 hm0
  rw [mul_zero] at h
  have hlhs : (∫ t in Ioi (0 : ℝ), ((m * t) / m) ^ (σ - 1) * |f (m * t)|)
      = ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * |f (m * t)| := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [mul_comm m t, mul_div_assoc, div_self (ne_of_gt hm0), mul_one]
  rw [hlhs] at h
  have hrhs : (∫ x in Ioi (0 : ℝ), (x / m) ^ (σ - 1) * |f x|)
      = m ^ (-(σ - 1)) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x| := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hxpos : (0 : ℝ) < x := hx
    rw [Real.div_rpow hxpos.le hm0.le, Real.rpow_neg hm0.le]
    field_simp
  rw [hrhs, smul_eq_mul] at h
  rw [h]
  have hcomb : m⁻¹ * (m ^ (-(σ - 1)) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x|)
      = m ^ (-σ) * ∫ x in Ioi (0 : ℝ), x ^ (σ - 1) * |f x| := by
    have hinv : m⁻¹ = m ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
    rw [hinv, ← mul_assoc, ← Real.rpow_add hm0]
    congr 2
    ring
  rw [hcomb]

/-- **Equations (5) and (8), the Muntz identity in the region of absolute convergence.**  On
`1 < Re s` the Mellin transform of the arithmetic sum is the zeta multiple of the Mellin transform of
the source. -/
theorem mellin_arithmeticSum_eq_zeta_mul {f : ℝ → ℝ} (hm : Measurable f) {B L : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) {s : ℂ} (hs : 1 < s.re) :
    mellin (fun t : ℝ => ((∑' n : ℕ, f (((n : ℝ) + 1) * t) : ℝ) : ℂ)) s
      = riemannZeta s * mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) s := by
  have hs0 : (0 : ℝ) < s.re := by linarith
  set M : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (s.re - 1) * |f x| with hM
  set F : ℕ → ℝ → ℂ := fun n t => (t : ℂ) ^ (s - 1) • ((f (((n : ℝ) + 1) * t) : ℝ) : ℂ) with hF
  have hpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  -- each dilate is Mellin convergent
  have hint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    have hbase := mellinConvergent_source hm hbnd hsupp hs0
    have := (MellinConvergent.comp_mul_left (f := fun t : ℝ => ((f t : ℝ) : ℂ)) (s := s)
      (hpos n)).mpr hbase
    exact this
  -- the norm integrals
  have hnorm : ∀ n : ℕ, (∫ t in Ioi (0 : ℝ), ‖F n t‖) = ((n : ℝ) + 1) ^ (-s.re) * M := by
    intro n
    have hcongr : (∫ t in Ioi (0 : ℝ), ‖F n t‖)
        = ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * |f (((n : ℝ) + 1) * t)| := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have htpos : (0 : ℝ) < t := ht
      rw [hF]
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.sub_re, Complex.one_re,
        norm_ofReal_source]
    rw [hcongr, integral_rpow_mul_abs_comp_mul (hpos n), hM]
  have hsummable : Summable fun n : ℕ => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    have hbase : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-s.re) := by
      have h := (Real.summable_one_div_nat_rpow (p := s.re)).mpr hs
      have h2 := h.comp_injective (add_left_injective 1)
      refine h2.congr fun n => ?_
      simp only [Function.comp_apply]
      have hn : (0 : ℝ) < (n : ℝ) + 1 := hpos n
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast, Real.rpow_neg hn.le, one_div]
    refine (hbase.mul_right M).congr fun n => ?_
    rw [hnorm n]
  have hsum := MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsummable
  -- identify the terms
  have hterm : ∀ n : ℕ, (∫ t in Ioi (0 : ℝ), F n t)
      = ((n : ℂ) + 1) ^ (-s) • mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) s := by
    intro n
    have h := mellin_comp_mul_left (fun t : ℝ => ((f t : ℝ) : ℂ)) s (hpos n)
    have hcast : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
    rw [← hcast]
    exact h
  -- identify the limit
  have hlimit : (∫ t in Ioi (0 : ℝ), ∑' n : ℕ, F n t)
      = mellin (fun t : ℝ => ((∑' n : ℕ, f (((n : ℝ) + 1) * t) : ℝ) : ℂ)) s := by
    rw [mellin]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hsumt : Summable fun n : ℕ => f (((n : ℝ) + 1) * t) := summable_summand hsupp t
    have hofReal : (∑' n : ℕ, ((f (((n : ℝ) + 1) * t) : ℝ) : ℂ))
        = ((∑' n : ℕ, f (((n : ℝ) + 1) * t) : ℝ) : ℂ) :=
      (Complex.ofRealCLM.hasSum hsumt.hasSum).tsum_eq
    simp only [hF, smul_eq_mul]
    rw [tsum_mul_left, hofReal]
  rw [← hlimit, ← hsum.tsum_eq]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  rw [← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [hterm n, smul_eq_mul]
  rw [one_div, ← Complex.cpow_neg]

/-! ## Analytic continuation and vanishing at the zeta zeros -/

/-- The arithmetic sum of the source, the unnormalized summation vector. -/
def arithmeticSum (f : ℝ → ℝ) (t : ℝ) : ℝ := ∑' n : ℕ, f (((n : ℝ) + 1) * t)

theorem summationVector_eq_sqrt_mul (f : ℝ → ℝ) (t : ℝ) :
    summationVector f t = Real.sqrt t * arithmeticSum f t := rfl

theorem measurable_arithmeticSum {f : ℝ → ℝ} (hm : Measurable f) {L : ℝ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) : Measurable (arithmeticSum f) := by
  have hpartial : ∀ N : ℕ, Measurable fun t : ℝ =>
      ∑ i ∈ Finset.range N, f (((i : ℝ) + 1) * t) := by
    intro N
    refine Finset.measurable_sum _ fun i _ => ?_
    exact hm.comp (measurable_id.const_mul _)
  refine measurable_of_tendsto_metrizable' atTop hpartial ?_
  rw [tendsto_pi_nhds]
  intro t
  exact (summable_summand hsupp t).hasSum.tendsto_sum_nat

theorem arithmeticSum_eq_zero_of_lt {f : ℝ → ℝ} {L t : ℝ}
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hLt : L < t) : arithmeticSum f t = 0 := by
  have hzero : ∀ n : ℕ, f (((n : ℝ) + 1) * t) = 0 := by
    intro n
    refine hsupp _ fun hmem => ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hprodpos : (0 : ℝ) < ((n : ℝ) + 1) * t := hmem.1
    have htpos : 0 < t := by
      rcases le_or_gt t 0 with h | h
      · exact absurd hprodpos
          (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (by linarith) h))
      · exact h
    have hge : t ≤ ((n : ℝ) + 1) * t := by nlinarith
    exact absurd hmem.2 (not_le.mpr (lt_of_lt_of_le hLt hge))
  rw [arithmeticSum]
  simp [hzero]

theorem abs_arithmeticSum_le {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ} (hbnd : ∀ x, |f x| ≤ B)
    (hbv : BoundedVariationOn f univ) {L : ℝ} (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0)
    (hint : (∫ x in (0 : ℝ)..L, f x) = 0) (t : ℝ) :
    |arithmeticSum f t| ≤ (eVariationOn f univ).toReal := by
  rcases le_or_gt t 0 with ht | ht
  · have hzero : ∀ n : ℕ, f (((n : ℝ) + 1) * t) = 0 := by
      intro n
      refine hsupp _ fun hmem => ?_
      have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
      have : ((n : ℝ) + 1) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnn ht
      exact absurd hmem.1 (not_lt.mpr this)
    rw [arithmeticSum]
    simp only [hzero, tsum_zero, abs_zero]
    exact ENNReal.toReal_nonneg
  · obtain ⟨N, hN⟩ := exists_index_ge (L := L) ht
    have hfin : arithmeticSum f t = ∑ n ∈ Finset.Icc 1 N, f ((n : ℝ) * t) := by
      have h := summationVector_eq_finset hsupp ht hN
      rw [summationVector_eq_sqrt_mul] at h
      have hsq : (0 : ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht
      exact mul_left_cancel₀ (ne_of_gt hsq) h
    rw [hfin]
    exact abs_sum_le_variation hm hbnd hbv hsupp hint ht hN

/-! ### Local integrability and growth -/

theorem locallyIntegrable_ofReal_of_bound {f : ℝ → ℝ} (hm : Measurable f) {B : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) :
    LocallyIntegrable (fun t : ℝ => ((f t : ℝ) : ℂ)) volume := by
  intro x
  refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := |B|) measure_Icc_lt_top.ne
    (Complex.measurable_ofReal.comp hm).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_ofReal_source]
  exact (hbnd t).trans (le_abs_self B)

theorem isBigO_atTop_of_support {g : ℝ → ℝ} {L : ℝ} (hg : ∀ t, L < t → g t = 0) (a : ℝ) :
    (fun t : ℝ => ((g t : ℝ) : ℂ)) =O[atTop] fun t : ℝ => t ^ (-a) := by
  refine Asymptotics.IsBigO.of_bound 0 ?_
  filter_upwards [eventually_gt_atTop L] with t ht
  rw [norm_ofReal_source, hg t ht]
  simp

theorem isBigO_zero_of_bound {g : ℝ → ℝ} {C : ℝ} (hg : ∀ t, |g t| ≤ C) :
    (fun t : ℝ => ((g t : ℝ) : ℂ)) =O[nhdsWithin 0 (Ioi 0)] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound |C| ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : (0 : ℝ) < t := ht
  rw [norm_ofReal_source, neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact (hg t).trans (le_abs_self C)

theorem differentiableAt_mellin_of_bound_support {g : ℝ → ℝ} (hm : Measurable g) {C L : ℝ}
    (hbnd : ∀ t, |g t| ≤ C) (hsupp : ∀ t, L < t → g t = 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (mellin (fun t : ℝ => ((g t : ℝ) : ℂ))) s := by
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := 0)
    ((locallyIntegrable_ofReal_of_bound hm hbnd).locallyIntegrableOn _)
    (isBigO_atTop_of_support hsupp _) (by linarith) (isBigO_zero_of_bound hbnd) hs

/-! ### The continuation and the spectral vanishing -/

/-- The Muntz identity propagates from the half-plane of absolute convergence to any open convex
region of the right half-plane avoiding the pole of zeta and meeting `Re s > 1`. -/
theorem eqOn_mellin_arithmeticSum_zeta {f : ℝ → ℝ} (hm : Measurable f) {B L : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hbv : BoundedVariationOn f univ)
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hint : (∫ x in (0 : ℝ)..L, f x) = 0)
    {U : Set ℂ} (hUopen : IsOpen U) (hUconv : Convex ℝ U) (hUre : ∀ s ∈ U, 0 < s.re)
    (hUone : (1 : ℂ) ∉ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hz₀re : 1 < z₀.re) :
    EqOn (mellin (fun t : ℝ => ((arithmeticSum f t : ℝ) : ℂ)))
      (fun s => riemannZeta s * mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) s) U := by
  have hAm : Measurable (arithmeticSum f) := measurable_arithmeticSum hm hsupp
  have hAb : ∀ t, |arithmeticSum f t| ≤ (eVariationOn f univ).toReal :=
    abs_arithmeticSum_le hm hbnd hbv hsupp hint
  have hAs : ∀ t, L < t → arithmeticSum f t = 0 := fun t ht =>
    arithmeticSum_eq_zero_of_lt hsupp ht
  have hfs : ∀ t, L < t → f t = 0 := fun t ht =>
    hsupp t fun hmem => absurd hmem.2 (not_le.mpr ht)
  have hleft : DifferentiableOn ℂ
      (mellin (fun t : ℝ => ((arithmeticSum f t : ℝ) : ℂ))) U := fun s hs =>
    (differentiableAt_mellin_of_bound_support hAm hAb hAs (hUre s hs)).differentiableWithinAt
  have hright : DifferentiableOn ℂ
      (fun s => riemannZeta s * mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) s) U := by
    intro s hs
    have hzne : s ≠ 1 := fun h => hUone (h ▸ hs)
    have h1 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hzne
    have h2 : DifferentiableAt ℂ (mellin (fun t : ℝ => ((f t : ℝ) : ℂ))) s :=
      differentiableAt_mellin_of_bound_support hm hbnd hfs (hUre s hs)
    exact (h1.mul h2).differentiableWithinAt
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hleft.analyticOnNhd hUopen) (hright.analyticOnNhd hUopen) hUconv.isPreconnected hz₀ ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hz₀re) fun s hs => ?_
  exact mellin_arithmeticSum_eq_zeta_mul hm hbnd hsupp hs

/-- **Equation (6).**  The Mellin transform of the arithmetic summation vector vanishes at every
nontrivial zeta zero, including any hypothetical off-line zero. -/
theorem mellin_arithmeticSum_eq_zero_of_zeta_eq_zero {f : ℝ → ℝ} (hm : Measurable f) {B L : ℝ}
    (hbnd : ∀ x, |f x| ≤ B) (hbv : BoundedVariationOn f univ)
    (hsupp : ∀ x, x ∉ Ioc (0 : ℝ) L → f x = 0) (hint : (∫ x in (0 : ℝ)..L, f x) = 0)
    {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    mellin (fun t : ℝ => ((arithmeticSum f t : ℝ) : ℂ)) ρ = 0 := by
  have him : ρ.im ≠ 0 := by
    intro h
    have hreal : ρ = ((ρ.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h]
    rw [hreal] at hz
    exact _root_.RHTower.riemannZeta_ne_zero_of_ofReal_mem_Ioo hρ0 hρ1 hz
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hUopen : IsOpen {s : ℂ | 0 < s.re ∧ s.im < 0} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_im continuous_const)
    have hUconv : Convex ℝ {s : ℂ | 0 < s.re ∧ s.im < 0} :=
      (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)
    have hz₀ : (2 - Complex.I) ∈ {s : ℂ | 0 < s.re ∧ s.im < 0} := by
      constructor <;> simp
    have h := eqOn_mellin_arithmeticSum_zeta hm hbnd hbv hsupp hint hUopen hUconv
      (fun s hs => hs.1) (by simp) hz₀ (by simp)
    rw [h ⟨hρ0, hneg⟩]
    show riemannZeta ρ * mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) ρ = 0
    rw [hz, zero_mul]
  · have hUopen : IsOpen {s : ℂ | 0 < s.re ∧ 0 < s.im} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)
    have hUconv : Convex ℝ {s : ℂ | 0 < s.re ∧ 0 < s.im} :=
      (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)
    have hz₀ : (2 + Complex.I) ∈ {s : ℂ | 0 < s.re ∧ 0 < s.im} := by
      constructor <;> simp
    have h := eqOn_mellin_arithmeticSum_zeta hm hbnd hbv hsupp hint hUopen hUconv
      (fun s hs => hs.1) (by simp) hz₀ (by simp)
    rw [h ⟨hρ0, hpos⟩]
    show riemannZeta ρ * mellin (fun t : ℝ => ((f t : ℝ) : ℂ)) ρ = 0
    rw [hz, zero_mul]

end GaloisForLFunctions.RHTower

end
