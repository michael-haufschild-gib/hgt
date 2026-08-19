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

end

end GaloisForLFunctions.HTGeometry
