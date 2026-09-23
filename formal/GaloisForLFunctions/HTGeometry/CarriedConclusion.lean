import GaloisForLFunctions.HTGeometry.CarriedTransfer

/-!
# A compactly carried representative confines every representative

Feeding the transferred power bound into `measure_ge_eq_zero_of_pow_integral_le` kills every set
`{x | t ≤ ((x-c)/r)²}` with `t > 1`.  The region where the square exceeds `1` is the countable union
of those, hence null: the second representative is carried by the same interval.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The region where the normalised square exceeds one is the complement of the interval. -/
theorem sq_gt_one_iff_notMem_Icc {c r x : ℝ} (hr : 0 < r) :
    1 < ((x - c) / r) ^ (2 : ℕ) ↔ x ∉ Set.Icc (c - r) (c + r) := by
  have hmem : x ∈ Set.Icc (c - r) (c + r) ↔ |x - c| ≤ r := by
    rw [Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  rw [hmem, not_le, div_pow, lt_div_iff₀ (by positivity : (0 : ℝ) < r ^ (2 : ℕ))]
  constructor
  · intro hgt
    nlinarith [abs_nonneg (x - c), sq_abs (x - c)]
  · intro hgt
    nlinarith [abs_nonneg (x - c), sq_abs (x - c)]

/-- **The second representative is carried by the same interval.** -/
theorem measure_compl_Icc_eq_zero_of_moments_eq {mu nu : Measure ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] {c r : ℝ} (hr : 0 < r)
    (hmus : mu (Set.Icc (c - r) (c + r))ᶜ = 0)
    (hsmu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hintmu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    (hsnu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂nu)
    (hintnu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu) :
    nu (Set.Icc (c - r) (c + r))ᶜ = 0 := by
  classical
  set f : ℝ → ℝ := fun x => ((x - c) / r) ^ (2 : ℕ) with hfdef
  have hfmeas : Measurable f := by fun_prop
  have hfnn : ∀ x, 0 ≤ f x := fun x => sq_nonneg _
  have hSb : ∀ x ∈ Set.Icc (c - r) (c + r), f x ≤ 1 := by
    intro x hx
    by_contra hc
    exact absurd hx ((sq_gt_one_iff_notMem_Icc hr).mp (not_le.mp hc))
  have hintf : ∀ n : ℕ, Integrable (fun x : ℝ => (f x) ^ n) nu := by
    intro n
    have hp := integrable_eval hintnu
      ((Polynomial.C (1 / r) * (X - Polynomial.C c)) ^ (2 * n))
    simpa only [eval_scaled_sq_pow c r hr.ne' n] using hp
  have hbound : ∀ n : ℕ, ∫ x, (f x) ^ n ∂nu ≤ s 0 := fun n =>
    integral_scaled_sq_pow_le hr.ne' hmus hSb hsmu hintmu hsnu hintnu n
  -- every level above one is null
  have hnull : ∀ k : ℕ, nu {x | 1 + 1 / (k + 1 : ℝ) ≤ f x} = 0 := by
    intro k
    refine measure_ge_eq_zero_of_pow_integral_le hfmeas hfnn hintf hbound ?_
    have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    linarith
  -- and the complement is their union
  have hcover : (Set.Icc (c - r) (c + r))ᶜ ⊆ ⋃ k : ℕ, {x | 1 + 1 / (k + 1 : ℝ) ≤ f x} := by
    intro x hx
    have hgt : 1 < f x := (sq_gt_one_iff_notMem_Icc hr).mpr hx
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < f x - 1)
    exact Set.mem_iUnion.mpr ⟨k, by simp only [Set.mem_setOf_eq]; linarith⟩
  refine measure_mono_null hcover ?_
  exact measure_iUnion_null hnull

/-- **Determinacy from one compactly carried representative.**  If some representing measure is
carried by a compact interval, every representing measure equals it. -/
theorem measure_eq_of_moments_eq_of_one_carried {mu nu : Measure ℝ}
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] {c r : ℝ} (hr : 0 < r)
    (hmus : mu (Set.Icc (c - r) (c + r))ᶜ = 0)
    (hsmu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂mu)
    (hintmu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) mu)
    (hsnu : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂nu)
    (hintnu : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) nu) :
    mu = nu :=
  measure_eq_of_moments_eq_of_carried hmus
    (measure_compl_Icc_eq_zero_of_moments_eq hr hmus hsmu hintmu hsnu hintnu)
    hsmu hintmu hsnu hintnu

end HTGeometry
