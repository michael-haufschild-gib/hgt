import GaloisForLFunctions.RHTower.ThetaCuspReflectedSquaredBernsteinNoGo
import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare

/-!
# No fixed summable atomic Laplace law for the reflected theta square profile

The positive Bernstein obstruction leaves signed cancellation as a possible escape.  This module
kills its fixed atomic form.  A summable complex exponential pencil with a finite noncancelled
dominant packet cannot vanish after normalization by its dominant radius.  The reflected
completed-theta squared profile does vanish after normalization by every nonnegative exponential
rate.  Hence even equality on integer squared scales is impossible.

For Laplace modes, maximal radius is the lowest frequency.  Repeated lowest frequencies are
combined before the noncancellation hypothesis is imposed, so the result retains every available
same-frequency cancellation.
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- Complex atomic Laplace transform of a coefficient family and real frequency family. -/
def signedAtomicLaplaceTransform {ι : Type*}
    (c : ι → ℂ) (frequency : ι → ℝ) (x : ℝ) : ℂ :=
  ∑' i : ι, c i * (Real.exp (-x * frequency i) : ℂ)

/-- In squared displacement, the reflected completed-theta product decays faster than every
nonnegative exponential rate. -/
theorem tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero
    (u : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun x : ℝ => Real.exp (a * x) *
      thetaCuspReflectedSourceProduct u (Real.sqrt x)) atTop (𝓝 0) := by
  have hsqrt : Tendsto Real.sqrt atTop atTop := Real.tendsto_sqrt_atTop
  have h :=
    (tendsto_exp_sq_mul_thetaCuspReflectedSourceProduct_atTop_zero u ha).comp hsqrt
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply, Real.sq_sqrt hx]

/-- A summable complex exponential pencil with a finite noncancelled dominant packet cannot
represent the reflected theta squared profile even on nonnegative integer samples. -/
theorem not_summableDominantPencil_represents_thetaCuspReflectedSquaredProduct
    {ι : Type*} (c b : ι → ℂ) (hc : Summable c)
    (D : Finset ι) {a : ℝ} (ha : 0 ≤ a)
    (hdom : ∀ i ∈ D, ‖b i‖ = Real.exp (-a))
    (hsub : ∀ i ∉ D, ‖b i‖ < Real.exp (-a))
    (hfiber : ∃ v ∈ D.image (fun i => b i / (Real.exp (-a) : ℂ)),
      finiteExponentialFiberCoefficient D c
        (fun i => b i / (Real.exp (-a) : ℂ)) v ≠ 0)
    (u : ℝ) :
    ¬ ∀ n : ℕ, (thetaCuspReflectedSourceProduct u
        (Real.sqrt (n : ℝ)) : ℂ) = ∑' i : ι, c i * b i ^ n := by
  intro hrep
  let r : ℝ := Real.exp (-a)
  let z : ι → ℂ := fun i => b i / (r : ℂ)
  have hr : 0 < r := by simp only [r]; positivity
  have hscale (n : ℕ) :
      (∑' i : ι, c i * z i ^ n) =
        (Real.exp (a * (n : ℝ)) : ℂ) * ∑' i : ι, c i * b i ^ n := by
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hcancelR : Real.exp (a * (n : ℝ)) * r ^ n = 1 := by
      simp only [r]
      rw [← Real.exp_nat_mul, ← Real.exp_add,
        show a * (n : ℝ) + (n : ℝ) * -a = 0 by ring, Real.exp_zero]
    have hcancelC :
        (Real.exp (a * (n : ℝ)) : ℂ) * (r : ℂ) ^ n = 1 := by
      exact_mod_cast hcancelR
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    calc
      c i * z i ^ n = c i * b i ^ n / (r : ℂ) ^ n := by
        dsimp only [z]
        rw [div_pow]
        ring
      _ = (Real.exp (a * (n : ℝ)) : ℂ) * (c i * b i ^ n) := by
        apply (div_eq_iff (pow_ne_zero n hrC)).2
        calc
          c i * b i ^ n = 1 * (c i * b i ^ n) := by ring
          _ = ((Real.exp (a * (n : ℝ)) : ℂ) * (r : ℂ) ^ n) *
              (c i * b i ^ n) := by rw [hcancelC]
          _ = (Real.exp (a * (n : ℝ)) : ℂ) *
              (c i * b i ^ n) * (r : ℂ) ^ n := by ring
  have hthetaR := tendsto_exp_mul_thetaCuspReflectedSquaredProduct_atTop_zero u ha
  have hthetaNat : Tendsto (fun n : ℕ =>
      Real.exp (a * (n : ℝ)) *
        thetaCuspReflectedSourceProduct u (Real.sqrt (n : ℝ)))
      atTop (𝓝 0) :=
    hthetaR.comp tendsto_natCast_atTop_atTop
  have hthetaC : Tendsto
      (Complex.ofReal ∘ fun n : ℕ => Real.exp (a * (n : ℝ)) *
        thetaCuspReflectedSourceProduct u (Real.sqrt (n : ℝ)))
      atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hthetaNat
  have hnormalized : Tendsto (fun n : ℕ =>
      ∑' i : ι, c i * (b i / (Real.exp (-a) : ℂ)) ^ n)
      atTop (𝓝 0) := by
    apply hthetaC.congr'
    filter_upwards with n
    simp only [Function.comp_apply, Complex.ofReal_mul]
    change (Real.exp (a * (n : ℝ)) : ℂ) *
        (thetaCuspReflectedSourceProduct u (Real.sqrt (n : ℝ)) : ℂ) =
      ∑' i : ι, c i * z i ^ n
    rw [hscale n, ← hrep n]
  exact (not_tendsto_tsum_normalizedExponentialPencil_zero_of_dominantFinset
    c b hc D (r := Real.exp (-a)) (Real.exp_pos _)
    hdom hsub hfiber) hnormalized

/-- No summable atomic Laplace series with a finite noncancelled lowest-frequency shell represents
the reflected theta squared profile, already at integer squared displacements. -/
theorem not_summableAtomicLaplace_represents_thetaCuspReflectedSquaredProduct_at_nat
    {ι : Type*} (c : ι → ℂ) (hc : Summable c)
    (frequency : ι → ℝ) (D : Finset ι) {N : ℝ} (hN : 0 ≤ N)
    (hdom : ∀ i ∈ D, frequency i = N)
    (hsub : ∀ i ∉ D, N < frequency i)
    (hcoeff : ∑ i ∈ D, c i ≠ 0) (u : ℝ) :
    ¬ ∀ n : ℕ, (thetaCuspReflectedSourceProduct u
        (Real.sqrt (n : ℝ)) : ℂ) =
      ∑' i : ι, c i * (Real.exp (-frequency i) : ℂ) ^ n := by
  apply not_summableDominantPencil_represents_thetaCuspReflectedSquaredProduct
    c (fun i => (Real.exp (-frequency i) : ℂ)) hc D hN
  · intro i hi
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), hdom i hi]
  · intro i hi
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_exp.mpr (neg_lt_neg (hsub i hi))
  · have hD : D.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      subst D
      simp at hcoeff
    obtain ⟨i₀, hi₀⟩ := hD
    refine ⟨1, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨i₀, hi₀, ?_⟩
      rw [hdom i₀ hi₀]
      exact div_self (by exact_mod_cast (Real.exp_pos (-N)).ne')
    · unfold finiteExponentialFiberCoefficient
      rw [Finset.filter_eq_self.mpr]
      · exact hcoeff
      · intro i hi
        dsimp only
        rw [hdom i hi]
        exact div_self (by exact_mod_cast (Real.exp_pos (-N)).ne')

/-- No fixed summable complex atomic Laplace representation with a finite noncancelled lowest
frequency shell exists for the reflected completed-theta squared profile on the nonnegative ray. -/
theorem not_summableAtomicLaplace_represents_thetaCuspReflectedSquaredProduct
    {ι : Type*} (c : ι → ℂ) (hc : Summable c)
    (frequency : ι → ℝ) (D : Finset ι) {N : ℝ} (hN : 0 ≤ N)
    (hdom : ∀ i ∈ D, frequency i = N)
    (hsub : ∀ i ∉ D, N < frequency i)
    (hcoeff : ∑ i ∈ D, c i ≠ 0) (u : ℝ) :
    ¬ ∀ x : ℝ, 0 ≤ x →
      (thetaCuspReflectedSourceProduct u (Real.sqrt x) : ℂ) =
        signedAtomicLaplaceTransform c frequency x := by
  intro hrep
  apply (not_summableAtomicLaplace_represents_thetaCuspReflectedSquaredProduct_at_nat
    c hc frequency D hN hdom hsub hcoeff u)
  intro n
  rw [hrep (n : ℝ) (Nat.cast_nonneg n)]
  unfold signedAtomicLaplaceTransform
  apply tsum_congr
  intro i
  congr 1
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  ring

end

end RHTower
