import Mathlib

/-!
# Normal convergence and divisor reflection in the relative strip

Two ingredients turn an absolute-convergence abscissa into a divisor bound.

*Normal convergence.*  A generalized Dirichlet series `∑ᵢ aᵢ e^{-μᵢ s}` with nonnegative frequencies
whose absolute series converges at every `v > σ` converges locally uniformly on the open half-plane
`Re s > σ`, defines a holomorphic function there, and its exponential is holomorphic and zero-free.
This is the Weierstrass test applied to the logarithmic Euler discrepancy.

*Divisor reflection.*  A divisor support that avoids the right half-plane `Re s > A` and is stable
under the functional-equation reflection `s ↦ 1 - s` lies in the closed band `1 - A ≤ Re s ≤ A`.
Hence the transverse radius is at most `A - 1/2`; at `A ≤ 1/2` the support is on the critical line,
and at `A < 1/2` it is empty.

## Main results

* `summable_dirichletTerm`, `differentiableAt_dirichletSeries` — normal convergence and holomorphy;
* `exp_dirichletSeries_ne_zero` — the exponential is zero-free on the half-plane;
* `mem_band_of_reflection` — the reflection band;
* `max_re_le_of_reflection` — the form consumed by the outer divisor exponent;
* `re_eq_half_of_reflection`, `eq_empty_of_reflection_lt_half` — the two threshold classes.
-/

noncomputable section

namespace RHTower

/-! ### Normal convergence of a generalized Dirichlet series -/

variable {ι : Type*}

/-- A generalized Dirichlet series with nonnegative frequencies. -/
def dirichletSeries (a : ι → ℂ) (mu : ι → ℝ) (s : ℂ) : ℂ :=
  ∑' i, a i * Complex.exp (-(mu i : ℂ) * s)

theorem norm_dirichletTerm (a : ι → ℂ) (mu : ι → ℝ) (i : ι) (s : ℂ) :
    ‖a i * Complex.exp (-(mu i : ℂ) * s)‖ = ‖a i‖ * Real.exp (-(mu i) * s.re) := by
  rw [norm_mul, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The Weierstrass bound.**  On a right half-plane the terms are dominated by their values at the
boundary abscissa. -/
theorem norm_dirichletTerm_le (a : ι → ℂ) {mu : ι → ℝ} (hmu : ∀ i, 0 ≤ mu i) {v : ℝ}
    (i : ι) {s : ℂ} (hs : v ≤ s.re) :
    ‖a i * Complex.exp (-(mu i : ℂ) * s)‖ ≤ ‖a i‖ * Real.exp (-(mu i) * v) := by
  rw [norm_dirichletTerm]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  nlinarith [hmu i]

theorem summable_dirichletTerm {a : ι → ℂ} {mu : ι → ℝ} (hmu : ∀ i, 0 ≤ mu i) {v : ℝ}
    (hv : Summable (fun i => ‖a i‖ * Real.exp (-(mu i) * v))) {s : ℂ} (hs : v ≤ s.re) :
    Summable (fun i => a i * Complex.exp (-(mu i : ℂ) * s)) :=
  Summable.of_norm_bounded hv (fun i => norm_dirichletTerm_le a hmu i hs)

/-- **Holomorphy on the open half-plane of absolute convergence.** -/
theorem differentiableAt_dirichletSeries {a : ι → ℂ} {mu : ι → ℝ} (hmu : ∀ i, 0 ≤ mu i)
    {sigma : ℝ} (habs : ∀ v : ℝ, sigma < v → Summable (fun i => ‖a i‖ * Real.exp (-(mu i) * v)))
    {s : ℂ} (hs : sigma < s.re) :
    DifferentiableAt ℂ (dirichletSeries a mu) s := by
  obtain ⟨v, hv1, hv2⟩ := exists_between hs
  have hopen : IsOpen {z : ℂ | v < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (dirichletSeries a mu) {z : ℂ | v < z.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun i => ‖a i‖ * Real.exp (-(mu i) * v)) (habs v hv1) (fun i => ?_) hopen
      (fun i z hz => norm_dirichletTerm_le a hmu i (le_of_lt hz))
    refine Differentiable.differentiableOn ?_
    exact (differentiable_const _).mul
      (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  exact (hdiff.differentiableAt (hopen.mem_nhds hv2))

/-- **The exponential of the discrepancy is zero-free.** -/
theorem exp_dirichletSeries_ne_zero (a : ι → ℂ) (mu : ι → ℝ) (s : ℂ) :
    Complex.exp (dirichletSeries a mu s) ≠ 0 := Complex.exp_ne_zero _


/-! ### The sparse-support bound -/

/-- **Sparse support raises the abscissa by at most the parameter bound.**  If the discrepancy
coefficients are dominated by `C e^{θ μ}` on a support whose own exponent is `δ`, the absolute
series converges for every `v > θ + δ`. -/
theorem summable_of_sparse_support {a : ι → ℂ} {mu : ι → ℝ} {C theta delta : ℝ}
    (hbound : ∀ i, ‖a i‖ ≤ C * Real.exp (theta * mu i))
    (hsupp : ∀ u : ℝ, delta < u → Summable (fun i => Real.exp (-(mu i) * u)))
    {v : ℝ} (hv : theta + delta < v) :
    Summable (fun i => ‖a i‖ * Real.exp (-(mu i) * v)) := by
  have hu : delta < v - theta := by linarith
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((hsupp (v - theta) hu).mul_left C)
  calc ‖a i‖ * Real.exp (-(mu i) * v)
      ≤ (C * Real.exp (theta * mu i)) * Real.exp (-(mu i) * v) := by
        exact mul_le_mul_of_nonneg_right (hbound i) (Real.exp_nonneg _)
    _ = C * Real.exp (-(mu i) * (v - theta)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-! ### The accumulated-variation bound -/

/-- **Polynomial growth of the accumulated variation bounds the abscissa.**  If every partial sum of
a nonnegative family over frequencies at most `x` is `O(e^{β x})`, the absolute series converges for
every `v > β`. -/
theorem summable_of_partialSum_bound [DecidableEq ι] {a : ι → ℝ} {mu : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hmu : ∀ i, 0 ≤ mu i) {C beta : ℝ} (hC : 0 ≤ C) (hbeta : 0 ≤ beta)
    (hV : ∀ (x : ℝ) (t : Finset ι), (∀ i ∈ t, mu i ≤ x) → ∑ i ∈ t, a i ≤ C * Real.exp (beta * x))
    {v : ℝ} (hv : beta < v) :
    Summable (fun i => a i * Real.exp (-(mu i) * v)) := by
  classical
  have hr0 : 0 < Real.exp (-(v - beta)) := Real.exp_pos _
  have hr1 : Real.exp (-(v - beta)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hCe : (0 : ℝ) ≤ C * Real.exp beta := by positivity
  refine summable_of_sum_le (c := C * Real.exp beta * (1 - Real.exp (-(v - beta)))⁻¹)
    (fun i => mul_nonneg (ha i) (Real.exp_nonneg _)) (fun t => ?_)
  have hmaps : ∀ i ∈ t, (fun i => ⌊mu i⌋₊) i ∈ Finset.range ((t.image fun i => ⌊mu i⌋₊).sup id + 1) := by
    intro i hi
    show ⌊mu i⌋₊ ∈ Finset.range ((t.image fun i => ⌊mu i⌋₊).sup id + 1)
    refine Finset.mem_range.mpr ?_
    have : (⌊mu i⌋₊) ≤ (t.image fun i => ⌊mu i⌋₊).sup id :=
      Finset.le_sup (f := (id : ℕ → ℕ)) (Finset.mem_image_of_mem _ hi)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun i => a i * Real.exp (-(mu i) * v))]
  have hblock : ∀ n ∈ Finset.range ((t.image fun i => ⌊mu i⌋₊).sup id + 1),
      (∑ i ∈ t.filter (fun i => ⌊mu i⌋₊ = n), a i * Real.exp (-(mu i) * v))
        ≤ C * Real.exp beta * (Real.exp (-(v - beta))) ^ n := by
    intro n _
    have hstep : (∑ i ∈ t.filter (fun i => ⌊mu i⌋₊ = n), a i * Real.exp (-(mu i) * v))
        ≤ (∑ i ∈ t.filter (fun i => ⌊mu i⌋₊ = n), a i) * Real.exp (-(n : ℝ) * v) := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum (fun i hi => ?_)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (ha i)
      have hgi : ⌊mu i⌋₊ = n := (Finset.mem_filter.mp hi).2
      have hn : (n : ℝ) ≤ mu i := by
        rw [← hgi]
        exact Nat.floor_le (hmu i)
      nlinarith [hbeta, hv]
    have hVn : (∑ i ∈ t.filter (fun i => ⌊mu i⌋₊ = n), a i)
        ≤ C * Real.exp (beta * ((n : ℝ) + 1)) := by
      refine hV _ _ (fun i hi => ?_)
      have hgi : ⌊mu i⌋₊ = n := (Finset.mem_filter.mp hi).2
      have hlt : mu i < (n : ℝ) + 1 := by
        rw [← hgi]
        exact Nat.lt_floor_add_one (mu i)
      linarith
    calc (∑ i ∈ t.filter (fun i => ⌊mu i⌋₊ = n), a i * Real.exp (-(mu i) * v))
        ≤ (∑ i ∈ t.filter (fun i => ⌊mu i⌋₊ = n), a i) * Real.exp (-(n : ℝ) * v) := hstep
      _ ≤ (C * Real.exp (beta * ((n : ℝ) + 1))) * Real.exp (-(n : ℝ) * v) :=
          mul_le_mul_of_nonneg_right hVn (Real.exp_nonneg _)
      _ = C * Real.exp beta * (Real.exp (-(v - beta))) ^ n := by
          rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
          congr 2
          ring
  refine le_trans (Finset.sum_le_sum hblock) ?_
  rw [← Finset.mul_sum]
  have hgeom : (∑ n ∈ Finset.range ((t.image fun i => ⌊mu i⌋₊).sup id + 1),
      (Real.exp (-(v - beta))) ^ n) ≤ (1 - Real.exp (-(v - beta)))⁻¹ := by
    have hsum : Summable (fun n : ℕ => (Real.exp (-(v - beta))) ^ n) :=
      summable_geometric_of_lt_one hr0.le hr1
    have hle := hsum.sum_le_tsum (Finset.range ((t.image fun i => ⌊mu i⌋₊).sup id + 1))
      (fun n _ => by positivity)
    rwa [tsum_geometric_of_lt_one hr0.le hr1] at hle
  exact mul_le_mul_of_nonneg_left hgeom hCe

/-! ### Divisor reflection -/

/-- **The reflection band.**  A divisor support avoiding `Re s > A` and stable under `s ↦ 1 - s`
lies in the closed band `1 - A ≤ Re s ≤ A`. -/
theorem mem_band_of_reflection {S : Set ℂ} {A : ℝ}
    (hright : ∀ ρ ∈ S, ρ.re ≤ A) (hrefl : ∀ ρ ∈ S, (1 - ρ) ∈ S) {ρ : ℂ} (hρ : ρ ∈ S) :
    1 - A ≤ ρ.re ∧ ρ.re ≤ A := by
  refine ⟨?_, hright ρ hρ⟩
  have h := hright (1 - ρ) (hrefl ρ hρ)
  simp only [Complex.sub_re, Complex.one_re] at h
  linarith

/-- **The transverse-radius bound.** -/
theorem abs_re_sub_half_le_of_reflection {S : Set ℂ} {A : ℝ}
    (hright : ∀ ρ ∈ S, ρ.re ≤ A) (hrefl : ∀ ρ ∈ S, (1 - ρ) ∈ S) {ρ : ℂ} (hρ : ρ ∈ S) :
    |ρ.re - 1 / 2| ≤ A - 1 / 2 := by
  obtain ⟨h1, h2⟩ := mem_band_of_reflection hright hrefl hρ
  rw [abs_le]
  constructor <;> linarith

/-- **The form consumed by the outer divisor exponent.** -/
theorem max_re_le_of_reflection {S : Set ℂ} {A : ℝ}
    (hright : ∀ ρ ∈ S, ρ.re ≤ A) (hrefl : ∀ ρ ∈ S, (1 - ρ) ∈ S) {ρ : ℂ} (hρ : ρ ∈ S) :
    max ρ.re (1 - ρ.re) ≤ A := by
  obtain ⟨h1, h2⟩ := mem_band_of_reflection hright hrefl hρ
  exact max_le h2 (by linarith)

/-- **The critical class.**  At `A ≤ 1/2` the whole support lies on the critical line. -/
theorem re_eq_half_of_reflection {S : Set ℂ} {A : ℝ} (hA : A ≤ 1 / 2)
    (hright : ∀ ρ ∈ S, ρ.re ≤ A) (hrefl : ∀ ρ ∈ S, (1 - ρ) ∈ S) {ρ : ℂ} (hρ : ρ ∈ S) :
    ρ.re = 1 / 2 := by
  obtain ⟨h1, h2⟩ := mem_band_of_reflection hright hrefl hρ
  linarith

/-- **The subcritical class.**  At `A < 1/2` the support is empty. -/
theorem eq_empty_of_reflection_lt_half {S : Set ℂ} {A : ℝ} (hA : A < 1 / 2)
    (hright : ∀ ρ ∈ S, ρ.re ≤ A) (hrefl : ∀ ρ ∈ S, (1 - ρ) ∈ S) : S = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr (fun ρ hρ => ?_)
  obtain ⟨h1, h2⟩ := mem_band_of_reflection hright hrefl hρ
  linarith

end RHTower
