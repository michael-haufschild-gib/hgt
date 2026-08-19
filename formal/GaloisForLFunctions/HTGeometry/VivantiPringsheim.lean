import Mathlib

/-!
# The Vivanti--Pringsheim theorem

A power series with nonnegative real coefficients and finite positive radius of convergence `R` is
singular at the positive real boundary point `R`: no analytic function on a neighbourhood of `R`
agrees with the series on a disk-side neighbourhood of `R`.

The proof is the classical one, run without any derivative computation.  Shifting the centre to a
real interior point `r` produces the coefficients

```
b_k = ∑_n C(n,k) a_n r^{n-k} ≥ 0,
```

and Tonelli identifies `∑_k b_k s^k` with `∑_n a_n (r+s)^n` for every `s ≥ 0` with `r + s < R`.
If the germ continued across `R`, then for `r` close enough to `R` the continued function would be
analytic on a disk about `r` of radius strictly larger than `R - r`; uniqueness of power series
would force `∑_k b_k s^k` to converge for some `s` with `r + s > R`, and nonnegativity would then
give convergence of `∑_n a_n (r+s)^n` beyond the radius.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `f` continues analytically across `z₀` from the domain `D`: some `g` analytic at `z₀` agrees
with `f` on a `D`-side neighbourhood of `z₀`. -/
def ContinuesAcross (f : ℂ → ℂ) (D : Set ℂ) (z₀ : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ ∀ᶠ w in nhdsWithin z₀ D, g w = f w

/-- The sum of a real-coefficient power series, as a function on `ℂ`. -/
def realSeriesSum (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n : ℕ, (a n : ℂ) * z ^ n

/-- The shifted (Taylor) coefficients at a real interior point. -/
def shiftedCoeff (a : ℕ → ℝ) (r : ℝ) (k : ℕ) : ℝ :=
  ∑' n : ℕ, (n.choose k : ℝ) * a n * r ^ (n - k)

theorem summable_binomial_family {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {r s : ℝ} (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hconv : Summable (fun n => a n * (r + s) ^ n)) :
    Summable (fun p : ℕ × ℕ => (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2) := by
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2 := by
    intro p
    have h1 : (0 : ℝ) ≤ (p.1.choose p.2 : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ a p.1 := ha p.1
    have h3 : (0 : ℝ) ≤ r ^ (p.1 - p.2) := pow_nonneg hr _
    have h4 : (0 : ℝ) ≤ s ^ p.2 := pow_nonneg hs _
    positivity
  rw [summable_prod_of_nonneg hnn]
  constructor
  · intro n
    refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun k hk => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
    simp
  · refine hconv.congr fun n => ?_
    have hfin : ∑' k : ℕ, ((n.choose k : ℝ) * a n * r ^ (n - k) * s ^ k)
        = ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * a n * r ^ (n - k) * s ^ k) := by
      refine tsum_eq_sum fun k hk => ?_
      rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
      simp
    rw [hfin]
    have hbin : (s + r) ^ n = ∑ k ∈ Finset.range (n + 1), s ^ k * r ^ (n - k) * (n.choose k : ℝ) :=
      add_pow s r n
    rw [show r + s = s + r by ring, hbin, Finset.mul_sum]
    exact (Finset.sum_congr rfl fun k _ => by ring).symm

theorem shiftedCoeff_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    0 ≤ shiftedCoeff a r k := by
  refine tsum_nonneg fun n => ?_
  have h1 : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ r ^ (n - k) := pow_nonneg hr _
  have := ha n
  positivity

theorem summable_shiftedCoeff {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {r s : ℝ} (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hconv : Summable (fun n => a n * (r + s) ^ n)) :
    Summable (fun k => shiftedCoeff a r k * s ^ k) := by
  have hfam := summable_binomial_family ha hr hs hconv
  have hswap : Summable (fun p : ℕ × ℕ =>
      (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s ^ p.1) := by
    refine (((Equiv.prodComm ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2)).mpr hfam).congr fun p => rfl
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s ^ p.1 := by
    intro p
    have h1 : (0 : ℝ) ≤ (p.2.choose p.1 : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ r ^ (p.2 - p.1) := pow_nonneg hr _
    have := ha p.2
    positivity
  rw [summable_prod_of_nonneg hnn] at hswap
  refine hswap.2.congr fun k => ?_
  rw [shiftedCoeff, ← tsum_mul_right]

theorem tsum_shiftedCoeff {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {r s : ℝ} (hr : 0 ≤ r)
    (hs : 0 ≤ s) (hconv : Summable (fun n => a n * (r + s) ^ n)) :
    ∑' k : ℕ, shiftedCoeff a r k * s ^ k = ∑' n : ℕ, a n * (r + s) ^ n := by
  have hfam := summable_binomial_family ha hr hs hconv
  have hrow : ∑' p : ℕ × ℕ, ((p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2)
      = ∑' n : ℕ, a n * (r + s) ^ n := by
    rw [hfam.tsum_prod]
    refine tsum_congr fun n => ?_
    have hfin : ∑' k : ℕ, ((n.choose k : ℝ) * a n * r ^ (n - k) * s ^ k)
        = ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * a n * r ^ (n - k) * s ^ k) := by
      refine tsum_eq_sum fun k hk => ?_
      rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
      simp
    rw [hfin]
    have hbin : (s + r) ^ n = ∑ k ∈ Finset.range (n + 1), s ^ k * r ^ (n - k) * (n.choose k : ℝ) :=
      add_pow s r n
    rw [show r + s = s + r by ring, hbin, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hswap : Summable (fun p : ℕ × ℕ =>
      (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s ^ p.1) := by
    refine (((Equiv.prodComm ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2)).mpr hfam).congr fun p => rfl
  have heq : ∑' p : ℕ × ℕ, ((p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2)
      = ∑' p : ℕ × ℕ, ((p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s ^ p.1) := by
    exact ((Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2)).symm
  have hcol : ∑' p : ℕ × ℕ, ((p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2)
      = ∑' k : ℕ, shiftedCoeff a r k * s ^ k := by
    rw [heq, hswap.tsum_prod]
    refine tsum_congr fun k => ?_
    rw [shiftedCoeff, ← tsum_mul_right]
  rw [← hcol, hrow]

/-! ### The complex shifted power series -/

theorem summable_complex_binomial_family {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {R r : ℝ}
    (hr0 : 0 ≤ r)
    (hconv : ∀ s : ℝ, 0 ≤ s → s < R → Summable (fun n => a n * s ^ n))
    {w : ℂ} (hw : ‖w‖ < R - r) :
    Summable (fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℂ) * (a p.1 : ℂ) * ((r : ℂ)) ^ (p.1 - p.2) * w ^ p.2) := by
  have hrw : r + ‖w‖ < R := by linarith
  have hbase := summable_binomial_family ha hr0 (norm_nonneg w)
    (hconv (r + ‖w‖) (by positivity) hrw)
  refine Summable.of_norm (hbase.congr fun p => ?_)
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha p.1), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr0]

theorem tsum_complex_row {a : ℕ → ℝ} {r : ℝ} {w : ℂ} (n : ℕ) :
    ∑' k : ℕ, ((n.choose k : ℂ) * (a n : ℂ) * ((r : ℂ)) ^ (n - k) * w ^ k)
      = (a n : ℂ) * ((r : ℂ) + w) ^ n := by
  have hfin : ∑' k : ℕ, ((n.choose k : ℂ) * (a n : ℂ) * ((r : ℂ)) ^ (n - k) * w ^ k)
      = ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℂ) * (a n : ℂ) * ((r : ℂ)) ^ (n - k) * w ^ k) := by
    refine tsum_eq_sum fun k hk => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
    simp
  rw [hfin]
  have hbin : (w + (r : ℂ)) ^ n
      = ∑ k ∈ Finset.range (n + 1), w ^ k * ((r : ℂ)) ^ (n - k) * (n.choose k : ℂ) :=
    add_pow w (r : ℂ) n
  rw [show ((r : ℂ) + w) = w + (r : ℂ) by ring, hbin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem summable_shiftedCoeff_row {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {R r : ℝ} (hr0 : 0 ≤ r)
    (hrR : r < R)
    (hconv : ∀ s : ℝ, 0 ≤ s → s < R → Summable (fun n => a n * s ^ n)) (k : ℕ) :
    Summable (fun n : ℕ => (n.choose k : ℝ) * a n * r ^ (n - k)) := by
  set s₀ : ℝ := (R - r) / 2 with hs₀
  have hs₀pos : 0 < s₀ := by rw [hs₀]; linarith
  have hrs : r + s₀ < R := by rw [hs₀]; linarith
  have hfam := summable_binomial_family ha hr0 hs₀pos.le (hconv (r + s₀) (by positivity) hrs)
  have hswap : Summable (fun p : ℕ × ℕ =>
      (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s₀ ^ p.1) := by
    refine (((Equiv.prodComm ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s₀ ^ p.2)).mpr hfam).congr fun p => rfl
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s₀ ^ p.1 := by
    intro p
    have h1 : (0 : ℝ) ≤ (p.2.choose p.1 : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ r ^ (p.2 - p.1) := pow_nonneg hr0 _
    have := ha p.2
    positivity
  rw [summable_prod_of_nonneg hnn] at hswap
  have hk := hswap.1 k
  have hsne : (s₀ : ℝ) ^ k ≠ 0 := by positivity
  refine (hk.mul_right ((s₀ : ℝ) ^ k)⁻¹).congr fun n => ?_
  field_simp

theorem tsum_complex_col (a : ℕ → ℝ) (r : ℝ) (w : ℂ) (k : ℕ) :
    ∑' n : ℕ, ((n.choose k : ℂ) * (a n : ℂ) * ((r : ℂ)) ^ (n - k) * w ^ k)
      = (shiftedCoeff a r k : ℂ) * w ^ k := by
  have hcast : ((shiftedCoeff a r k : ℝ) : ℂ)
      = ∑' n : ℕ, (((n.choose k : ℝ) * a n * r ^ (n - k) : ℝ) : ℂ) := by
    rw [shiftedCoeff]
    exact Complex.ofReal_tsum _
  rw [hcast, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  push_cast
  ring

/-- **The shifted power series.**  For a real interior point `r` the series recentred at `r` has the
nonnegative coefficients `shiftedCoeff` and converges on the disk of radius `R - r`. -/
theorem hasSum_shiftedCoeff_complex {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {R r : ℝ} (hr0 : 0 ≤ r)
    (hconv : ∀ s : ℝ, 0 ≤ s → s < R → Summable (fun n => a n * s ^ n))
    {w : ℂ} (hw : ‖w‖ < R - r) :
    HasSum (fun k => (shiftedCoeff a r k : ℂ) * w ^ k) (realSeriesSum a ((r : ℂ) + w)) := by
  have hrw : r + ‖w‖ < R := by linarith
  have hfam := summable_complex_binomial_family ha hr0 hconv hw
  have hksum : Summable (fun k => (shiftedCoeff a r k : ℂ) * w ^ k) := by
    refine Summable.of_norm ((summable_shiftedCoeff ha hr0 (norm_nonneg w)
      (hconv (r + ‖w‖) (by positivity) hrw)).congr fun k => ?_)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (shiftedCoeff_nonneg ha hr0 k)]
  have hrow : ∑' p : ℕ × ℕ,
      ((p.1.choose p.2 : ℂ) * (a p.1 : ℂ) * ((r : ℂ)) ^ (p.1 - p.2) * w ^ p.2)
      = realSeriesSum a ((r : ℂ) + w) := by
    rw [hfam.tsum_prod, realSeriesSum]
    exact tsum_congr fun n => tsum_complex_row n
  have hswapfam : Summable (fun p : ℕ × ℕ =>
      (p.2.choose p.1 : ℂ) * (a p.2 : ℂ) * ((r : ℂ)) ^ (p.2 - p.1) * w ^ p.1) := by
    refine (((Equiv.prodComm ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℂ) * (a p.1 : ℂ) * ((r : ℂ)) ^ (p.1 - p.2) * w ^ p.2)).mpr
      hfam).congr fun p => rfl
  have heq : ∑' p : ℕ × ℕ,
      ((p.1.choose p.2 : ℂ) * (a p.1 : ℂ) * ((r : ℂ)) ^ (p.1 - p.2) * w ^ p.2)
      = ∑' p : ℕ × ℕ,
        ((p.2.choose p.1 : ℂ) * (a p.2 : ℂ) * ((r : ℂ)) ^ (p.2 - p.1) * w ^ p.1) :=
    ((Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℂ) * (a p.1 : ℂ) * ((r : ℂ)) ^ (p.1 - p.2) * w ^ p.2)).symm
  have hcol : ∑' p : ℕ × ℕ,
      ((p.1.choose p.2 : ℂ) * (a p.1 : ℂ) * ((r : ℂ)) ^ (p.1 - p.2) * w ^ p.2)
      = ∑' k : ℕ, (shiftedCoeff a r k : ℂ) * w ^ k := by
    rw [heq, hswapfam.tsum_prod]
    exact tsum_congr fun k => tsum_complex_col a r w k
  have htsum : ∑' k : ℕ, (shiftedCoeff a r k : ℂ) * w ^ k = realSeriesSum a ((r : ℂ) + w) := by
    rw [← hcol, hrow]
  rw [← htsum]
  exact hksum.hasSum

/-- The reverse Tonelli step: convergence of the shifted series forces convergence of the
original series beyond the shift. -/
theorem summable_of_summable_shiftedCoeff {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrow : ∀ k : ℕ, Summable (fun n : ℕ => (n.choose k : ℝ) * a n * r ^ (n - k)))
    (h : Summable (fun k => shiftedCoeff a r k * s ^ k)) :
    Summable (fun n => a n * (r + s) ^ n) := by
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s ^ p.1 := by
    intro p
    have h1 : (0 : ℝ) ≤ (p.2.choose p.1 : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ r ^ (p.2 - p.1) := pow_nonneg hr _
    have := ha p.2
    positivity
  have hswap : Summable (fun p : ℕ × ℕ =>
      (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s ^ p.1) := by
    rw [summable_prod_of_nonneg hnn]
    refine ⟨fun k => ((hrow k).mul_right (s ^ k)).congr fun n => by ring, ?_⟩
    refine h.congr fun k => ?_
    rw [shiftedCoeff, ← tsum_mul_right]
  have hfam : Summable (fun p : ℕ × ℕ =>
      (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2) := by
    refine (((Equiv.prodComm ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ =>
      (p.2.choose p.1 : ℝ) * a p.2 * r ^ (p.2 - p.1) * s ^ p.1)).mpr hswap).congr fun p => rfl
  have hnn' : ∀ p : ℕ × ℕ, 0 ≤ (p.1.choose p.2 : ℝ) * a p.1 * r ^ (p.1 - p.2) * s ^ p.2 := by
    intro p
    have h1 : (0 : ℝ) ≤ (p.1.choose p.2 : ℝ) := by positivity
    have h3 : (0 : ℝ) ≤ r ^ (p.1 - p.2) := pow_nonneg hr _
    have := ha p.1
    positivity
  rw [summable_prod_of_nonneg hnn'] at hfam
  refine hfam.2.congr fun n => ?_
  have hfin : ∑' k : ℕ, ((n.choose k : ℝ) * a n * r ^ (n - k) * s ^ k)
      = ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * a n * r ^ (n - k) * s ^ k) := by
    refine tsum_eq_sum fun k hk => ?_
    rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]
    simp
  rw [hfin]
  have hbin : (s + r) ^ n = ∑ k ∈ Finset.range (n + 1), s ^ k * r ^ (n - k) * (n.choose k : ℝ) :=
    add_pow s r n
  rw [show r + s = s + r by ring, hbin, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-! ### The theorem -/

open scoped ENNReal NNReal

theorem ofReal_le_radius {c : ℕ → ℂ} {T : ℝ}
    (h : ∀ s : ℝ, 0 ≤ s → s < T → Summable (fun n => ‖c n‖ * s ^ n)) :
    ENNReal.ofReal T ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
  have htT : (t : ℝ) < T := by
    have := (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp ht
    simpa using this
  refine FormalMultilinearSeries.le_radius_of_summable_norm _ ?_
  refine (h (t : ℝ) t.coe_nonneg htT).congr fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm]

/-- The sum of a real power series is analytic on its disk of absolute convergence. -/
theorem analyticOnNhd_realSeriesSum {a : ℕ → ℝ} {R : ℝ} (hR : 0 < R)
    (hconv : ∀ s : ℝ, 0 ≤ s → s < R → Summable (fun n => |a n| * s ^ n)) :
    AnalyticOnNhd ℂ (realSeriesSum a) (Metric.ball 0 R) := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ)) with hp
  have hpsum : p.sum = realSeriesSum a := by
    funext z
    rw [FormalMultilinearSeries.sum, realSeriesSum]
    exact tsum_congr fun n => by
      rw [hp, FormalMultilinearSeries.ofScalars_apply_eq]
      simp [smul_eq_mul]
  have hprad : ENNReal.ofReal R ≤ p.radius := by
    refine ofReal_le_radius fun s hs0 hsR => ?_
    refine (hconv s hs0 hsR).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hpradpos : 0 < p.radius := lt_of_lt_of_le (by simpa using hR) hprad
  have h1 := (p.hasFPowerSeriesOnBall hpradpos).analyticOnNhd
  rw [hpsum] at h1
  intro z hz
  refine h1 z ?_
  rw [Metric.mem_eball, edist_zero_right]
  refine lt_of_lt_of_le ?_ hprad
  rw [← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z) |>.mpr (by simpa using hz)

/-- **Vivanti--Pringsheim.**  A power series with nonnegative real coefficients and finite positive
radius of convergence `R` does not continue analytically across its positive real boundary point. -/
theorem not_continuesAcross_of_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {R : ℝ} (hR : 0 < R)
    (hconv : ∀ s : ℝ, 0 ≤ s → s < R → Summable (fun n => a n * s ^ n))
    (hdiv : ∀ s : ℝ, R < s → ¬ Summable (fun n => a n * s ^ n)) :
    ¬ ContinuesAcross (realSeriesSum a) (Metric.ball 0 R) (R : ℂ) := by
  classical
  rintro ⟨g, hg, hagree⟩
  set f : ℂ → ℂ := realSeriesSum a with hf
  set p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ)) with hp
  -- `f` is analytic on the open disk of radius `R`
  have hpsum : p.sum = f := by
    funext z
    rw [FormalMultilinearSeries.sum, hf, realSeriesSum]
    exact tsum_congr fun n => by
      rw [hp, FormalMultilinearSeries.ofScalars_apply_eq]
      simp [smul_eq_mul]
  have hprad : ENNReal.ofReal R ≤ p.radius := by
    refine ofReal_le_radius fun s hs0 hsR => ?_
    refine (hconv s hs0 hsR).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
  have hpradpos : 0 < p.radius :=
    lt_of_lt_of_le (by simpa using hR) hprad
  have hfan : AnalyticOnNhd ℂ f (Metric.ball 0 R) := by
    have h1 := (p.hasFPowerSeriesOnBall hpradpos).analyticOnNhd
    rw [hpsum] at h1
    intro z hz
    refine h1 z ?_
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_of_lt_of_le ?_ hprad
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z) |>.mpr
      (by simpa using hz)
  -- an `ε`-disk of analyticity for the continuation
  obtain ⟨ε₀, hε₀, hgan₀⟩ : ∃ ε > 0, ∀ y ∈ Metric.ball (R : ℂ) ε, AnalyticAt ℂ g y := by
    have h := hg.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hball⟩ := h
    exact ⟨ε, hε, fun y hy => hball (by simpa [dist_eq_norm] using hy)⟩
  set ε : ℝ := min ε₀ R with hεdef
  have hε : 0 < ε := lt_min hε₀ hR
  have hεR : ε ≤ R := min_le_right _ _
  have hgan : ∀ y ∈ Metric.ball (R : ℂ) ε, AnalyticAt ℂ g y := fun y hy =>
    hgan₀ y (Metric.ball_subset_ball (min_le_left _ _) hy)
  set r : ℝ := R - ε / 3 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hrR : r < R := by rw [hrdef]; linarith
  -- the overlap region
  set V : Set ℂ := Metric.ball (0 : ℂ) R ∩ Metric.ball (R : ℂ) ε with hV
  have hVopen : IsOpen V := (Metric.isOpen_ball).inter Metric.isOpen_ball
  have hVconv : Convex ℝ V := (convex_ball _ _).inter (convex_ball _ _)
  have hVconn : IsPreconnected V := hVconv.isPreconnected
  have hrV : (r : ℂ) ∈ V := by
    constructor
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr0]
      rw [hrdef]; linarith
    · rw [Metric.mem_ball, Complex.dist_eq]
      rw [show (r : ℂ) - (R : ℂ) = ((r - R : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, hrdef]
      rw [show R - ε / 3 - R = -(ε / 3) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
  -- `f` and `g` agree on `V`
  have hagree' : ∀ᶠ w in nhds (R : ℂ), w ∈ Metric.ball (0 : ℂ) R → g w = f w := by
    rw [eventually_nhdsWithin_iff] at hagree
    exact hagree
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp hagree'
  set t : ℝ := min (min η ε) (R / 2) / 2 with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    have : 0 < min (min η ε) (R / 2) := lt_min (lt_min hη hε) (by linarith)
    linarith
  have htη : t < η := by
    rw [htdef]
    have h1 : min (min η ε) (R / 2) ≤ η := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have htε : t < ε := by
    rw [htdef]
    have h1 : min (min η ε) (R / 2) ≤ ε := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have htR : t < R := by
    rw [htdef]
    have h1 : min (min η ε) (R / 2) ≤ R / 2 := min_le_right _ _
    linarith
  set z₁ : ℂ := ((R - t : ℝ) : ℂ) with hz₁
  have hz₁V : z₁ ∈ V := by
    constructor
    · rw [Metric.mem_ball, dist_zero_right, hz₁, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
      linarith
    · rw [Metric.mem_ball, Complex.dist_eq, hz₁,
        show ((R - t : ℝ) : ℂ) - (R : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
      exact htε
  have hEq : Set.EqOn f g V := by
    refine (hfan.mono Set.inter_subset_left).eqOn_of_preconnected_of_eventuallyEq
      (fun z hz => hgan z hz.2) hVconn hz₁V ?_
    have hz₁R : dist z₁ (R : ℂ) = t := by
      rw [Complex.dist_eq, hz₁,
        show ((R - t : ℝ) : ℂ) - (R : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
    have hz₁n : ‖z₁‖ = R - t := by
      rw [hz₁, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hmem : ∀ w ∈ Metric.ball z₁ (min (η - t) t), g w = f w := by
      intro w hw
      rw [Metric.mem_ball] at hw
      refine hηball ?_ ?_
      · have hd : dist w (R : ℂ) ≤ dist w z₁ + dist z₁ (R : ℂ) := dist_triangle _ _ _
        have h1 : dist w z₁ < η - t := lt_of_lt_of_le hw (min_le_left _ _)
        linarith
      · rw [Metric.mem_ball, dist_zero_right]
        have hd : ‖w‖ ≤ ‖w - z₁‖ + ‖z₁‖ := by simpa using norm_add_le (w - z₁) z₁
        have h1 : dist w z₁ < t := lt_of_lt_of_le hw (min_le_right _ _)
        rw [Complex.dist_eq] at h1
        linarith
    have hpos : 0 < min (η - t) t := lt_min (by linarith) ht0
    filter_upwards [Metric.ball_mem_nhds z₁ hpos] with w hw
    exact (hmem w hw).symm
  have hfg : f =ᶠ[nhds (r : ℂ)] g := by
    filter_upwards [hVopen.mem_nhds hrV] with w hw
    exact hEq hw
  -- the shifted power series of `f` at `r`
  set b : ℕ → ℝ := fun k => shiftedCoeff a r k with hb
  have hbnn : ∀ k, 0 ≤ b k := fun k => shiftedCoeff_nonneg ha hr0.le k
  set q : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (fun k => (b k : ℂ)) with hq
  have hqrad : ENNReal.ofReal (R - r) ≤ q.radius := by
    refine ofReal_le_radius fun s hs0 hsR => ?_
    have hrs : r + s < R := by linarith
    refine (summable_shiftedCoeff ha hr0.le hs0 (hconv (r + s) (by positivity) hrs)).congr
      fun k => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbnn k)]
  have hfball : HasFPowerSeriesOnBall f q (r : ℂ) (ENNReal.ofReal (R - r)) := by
    refine ⟨hqrad, by simp; linarith, ?_⟩
    intro y hy
    have hynorm : ‖y‖ < R - r := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm_eq_enorm] at hy
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg y)).mp hy
    have heq : (fun n : ℕ => (q n) (fun _ => y))
        = fun k : ℕ => ((shiftedCoeff a r k : ℝ) : ℂ) * y ^ k := by
      funext k
      rw [hq, FormalMultilinearSeries.ofScalars_apply_eq]
      simp [smul_eq_mul, hb]
    rw [heq]
    exact hasSum_shiftedCoeff_complex ha hr0.le hconv hynorm
  -- the continuation's power series at `r`
  have hgdiff : DifferentiableOn ℂ g (Metric.closedBall (r : ℂ) ((ε / 2 : ℝ).toNNReal : ℝ)) := by
    intro z hz
    refine ((hgan z ?_).differentiableAt).differentiableWithinAt
    rw [Metric.mem_closedBall] at hz
    rw [Real.coe_toNNReal _ (by positivity)] at hz
    rw [Metric.mem_ball]
    have hd : dist z (R : ℂ) ≤ dist z (r : ℂ) + dist (r : ℂ) (R : ℂ) := dist_triangle _ _ _
    have hrRd : dist (r : ℂ) (R : ℂ) = ε / 3 := by
      rw [Complex.dist_eq,
        show (r : ℂ) - (R : ℂ) = ((r - R : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, hrdef,
        show R - ε / 3 - R = -(ε / 3) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hgball : HasFPowerSeriesOnBall g (cauchyPowerSeries g (r : ℂ) ((ε / 2 : ℝ).toNNReal))
      (r : ℂ) (((ε / 2 : ℝ).toNNReal : ℝ≥0∞)) :=
    hgdiff.hasFPowerSeriesOnBall (by
      rw [← NNReal.coe_pos, Real.coe_toNNReal _ (by positivity)]
      linarith)
  have hgat : HasFPowerSeriesAt f (cauchyPowerSeries g (r : ℂ) ((ε / 2 : ℝ).toNNReal)) (r : ℂ) :=
    (hgball.hasFPowerSeriesAt).congr hfg.symm
  have hqeq : q = cauchyPowerSeries g (r : ℂ) ((ε / 2 : ℝ).toNNReal) :=
    (hfball.hasFPowerSeriesAt).eq_formalMultilinearSeries hgat
  have hqrad2 : (((ε / 2 : ℝ).toNNReal : ℝ≥0∞)) ≤ q.radius := by
    rw [hqeq]
    exact hgball.r_le
  -- convergence beyond the radius
  set s : ℝ := 5 * ε / 12 with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hslt : (s.toNNReal : ℝ≥0∞) < q.radius := by
    refine lt_of_lt_of_le ?_ hqrad2
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0,
      Real.coe_toNNReal _ (by positivity)]
    rw [hsdef]; linarith
  have hbsum : Summable (fun k => b k * s ^ k) := by
    have h := q.summable_norm_mul_pow hslt
    refine (h.congr fun k => ?_)
    rw [hq, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hbnn k), Real.coe_toNNReal _ hs0]
  have hrow : ∀ k : ℕ, Summable (fun n : ℕ => (n.choose k : ℝ) * a n * r ^ (n - k)) :=
    fun k => summable_shiftedCoeff_row ha hr0.le hrR hconv k
  have hfinal := summable_of_summable_shiftedCoeff ha hr0.le hs0 hrow hbsum
  exact hdiv (r + s) (by rw [hrdef, hsdef]; linarith) hfinal

end

end GaloisForLFunctions.HTGeometry
