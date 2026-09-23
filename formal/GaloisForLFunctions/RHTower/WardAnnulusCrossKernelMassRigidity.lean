import GaloisForLFunctions.HTGeometry.HalfPlanePoissonKernel

/-!
# Mass rigidity of finite Lorentzian cross kernels

A finite signed Laplace mixture `W(u) = ∑ c i * exp (-(b i) * |u|)` produces, after pairing two
Ward responses at common advance `A`, the spatial cross kernel

`K(D) = ∑ 2 (c i) (A + b i) / ((A + b i)^2 + D^2)`.

Each Lorentzian has total real-line mass `2π` independently of its width, so the total mass of `K`
is `2π * ∑ c i`, that is `2π` times the value of the mixture at `u = 0`.  Cancelling the
width-independent baseline is exactly `∑ c i = 0`, and then the cross kernel has zero total mass.
A continuous nonnegative function of zero mass vanishes, so a baseline-cancelling mixture whose
cross kernel is not identically zero must take a negative value.
-/

open MeasureTheory
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Spatial cross kernel of a finite signed Laplace mixture at common advance `A`. -/
def annulusCrossKernel {ι : Type*} (S : Finset ι) (c b : ι → ℝ) (A D : ℝ) : ℝ :=
  ∑ i ∈ S, 2 * c i * (A + b i) / ((A + b i) ^ (2 : ℕ) + D ^ (2 : ℕ))

theorem annulusCrossKernel_eq_sum_poisson {ι : Type*} (S : Finset ι) (c b : ι → ℝ) (A D : ℝ) :
    annulusCrossKernel S c b A D =
      ∑ i ∈ S, (2 * Real.pi * c i) * halfPlanePoisson (A + b i) D := by
  unfold annulusCrossKernel halfPlanePoisson
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

theorem integrable_annulusCrossKernel {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) :
    Integrable (annulusCrossKernel S c b A) := by
  rw [show annulusCrossKernel S c b A = fun D : ℝ =>
      ∑ i ∈ S, (2 * Real.pi * c i) * halfPlanePoisson (A + b i) D from
    funext fun D => annulusCrossKernel_eq_sum_poisson S c b A D]
  exact MeasureTheory.integrable_finsetSum S fun i hi =>
    (integrable_halfPlanePoisson (hb i hi)).const_mul _

theorem continuous_annulusCrossKernel {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) :
    Continuous (annulusCrossKernel S c b A) := by
  rw [show annulusCrossKernel S c b A = fun D : ℝ =>
      ∑ i ∈ S, (2 * Real.pi * c i) * halfPlanePoisson (A + b i) D from
    funext fun D => annulusCrossKernel_eq_sum_poisson S c b A D]
  exact continuous_finsetSum S fun i hi =>
    continuous_const.mul (continuous_halfPlanePoisson (hb i hi))

/-- **Cross-kernel mass law.**  The total real-line mass of the spatial cross kernel is `2π` times
the value of the Laplace mixture at `u = 0`, independently of the advance and of every width. -/
theorem integral_annulusCrossKernel {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) :
    (∫ D : ℝ, annulusCrossKernel S c b A D) = 2 * Real.pi * ∑ i ∈ S, c i := by
  rw [show annulusCrossKernel S c b A = fun D : ℝ =>
      ∑ i ∈ S, (2 * Real.pi * c i) * halfPlanePoisson (A + b i) D from
    funext fun D => annulusCrossKernel_eq_sum_poisson S c b A D]
  rw [MeasureTheory.integral_finsetSum S fun i hi =>
    (integrable_halfPlanePoisson (hb i hi)).const_mul _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [MeasureTheory.integral_const_mul, integral_halfPlanePoisson (hb i hi)]
  ring

/-- A baseline-cancelling mixture has a zero-mass cross kernel, so a nonnegative one vanishes. -/
theorem annulusCrossKernel_eq_zero_of_nonneg {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) (hzero : ∑ i ∈ S, c i = 0)
    (hnn : ∀ D, 0 ≤ annulusCrossKernel S c b A D) :
    ∀ D, annulusCrossKernel S c b A D = 0 := by
  have hint : (∫ D : ℝ, annulusCrossKernel S c b A D) = 0 := by
    rw [integral_annulusCrossKernel S c b hb, hzero, mul_zero]
  have hae : annulusCrossKernel S c b A =ᵐ[volume] 0 := by
    have := (MeasureTheory.integral_eq_zero_iff_of_nonneg hnn
      (integrable_annulusCrossKernel S c b hb)).mp hint
    exact this
  have := (continuous_annulusCrossKernel S c b hb).ae_eq_iff_eq volume continuous_const |>.mp hae
  intro D
  exact congrFun this D

/-- **Negative cross channel is forced.**  A baseline-cancelling finite Laplace mixture whose
spatial cross kernel does not vanish identically takes a strictly negative value. -/
theorem exists_annulusCrossKernel_neg {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) (hzero : ∑ i ∈ S, c i = 0)
    (hne : ∃ D, annulusCrossKernel S c b A D ≠ 0) :
    ∃ D, annulusCrossKernel S c b A D < 0 := by
  by_contra hcon
  rw [not_exists] at hcon
  simp only [not_lt] at hcon
  obtain ⟨D, hD⟩ := hne
  exact hD (annulusCrossKernel_eq_zero_of_nonneg S c b hb hzero hcon D)

/-- **Leak budget.**  A nonnegative cross kernel deposits on every measurable set at most its
total mass, which is `2π` times the baseline leak of the mixture.  No advance and no choice of
widths enlarges that budget. -/
theorem setIntegral_annulusCrossKernel_le {ι : Type*} (S : Finset ι) (c b : ι → ℝ) {A : ℝ}
    (hb : ∀ i ∈ S, 0 < A + b i) (hnn : ∀ D, 0 ≤ annulusCrossKernel S c b A D) (s : Set ℝ) :
    (∫ D in s, annulusCrossKernel S c b A D) ≤ 2 * Real.pi * ∑ i ∈ S, c i := by
  rw [← integral_annulusCrossKernel S c b hb]
  exact MeasureTheory.setIntegral_le_integral (integrable_annulusCrossKernel S c b hb)
    (Filter.Eventually.of_forall hnn)

/-- Candidate route class: a finite baseline-cancelling Laplace weight whose spatial cross kernel
is nonnegative and does not vanish identically. -/
def WardBaselineCancellingNonnegativeCrossKernelRoute : Prop :=
  ∃ (n : ℕ) (c b : Fin n → ℝ) (A : ℝ),
    (∀ i, 0 < A + b i) ∧
    (∑ i, c i = 0) ∧
    (∀ D, 0 ≤ annulusCrossKernel Finset.univ c b A D) ∧
    (∃ D, annulusCrossKernel Finset.univ c b A D ≠ 0)

/-- **Route-class kill.**  No finite Laplace mixture cancels the width-independent baseline and
simultaneously keeps a nontrivial nonnegative spatial cross kernel.  Baseline cancellation and a
sign-definite cross channel are mutually exclusive. -/
theorem wardBaselineCancellingNonnegativeCrossKernelRouteKilled :
    ¬ WardBaselineCancellingNonnegativeCrossKernelRoute := by
  rintro ⟨n, c, b, A, hb, hzero, hnn, D, hD⟩
  exact hD (annulusCrossKernel_eq_zero_of_nonneg Finset.univ c b
    (fun i _ => hb i) hzero hnn D)

/-- The two-width Ward annulus, coefficients `1, -1` at widths `6/5` and `16/5`, has a strictly
negative spatial cross kernel somewhere, at every nonnegative advance. -/
theorem exists_wardTwoWidthAnnulusCrossKernel_neg {A : ℝ} (hA : 0 ≤ A) :
    ∃ D, annulusCrossKernel Finset.univ ![(1 : ℝ), -1] ![(6/5 : ℝ), 16/5] A D < 0 := by
  refine exists_annulusCrossKernel_neg Finset.univ _ _ ?_ ?_ ⟨0, ?_⟩
  · intro i _
    fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_two]
  · have h1 : (0 : ℝ) < A + 6/5 := by linarith
    have h2 : (0 : ℝ) < A + 16/5 := by linarith
    simp only [annulusCrossKernel, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : 2 * (1 : ℝ) * (A + 6/5) / ((A + 6/5) ^ (2 : ℕ) + (0 : ℝ) ^ (2 : ℕ)) +
        2 * (-1 : ℝ) * (A + 16/5) / ((A + 16/5) ^ (2 : ℕ) + (0 : ℝ) ^ (2 : ℕ)) =
        2 / (A + 6/5) - 2 / (A + 16/5) := by
      field_simp
      ring
    rw [this]
    have : 2 / (A + 16/5) < 2 / (A + 6/5) := by
      apply div_lt_div_of_pos_left (by norm_num) h1
      linarith
    linarith

end

end RHTower
