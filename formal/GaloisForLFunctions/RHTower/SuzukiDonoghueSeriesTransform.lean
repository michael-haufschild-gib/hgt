import GaloisForLFunctions.RHTower.SuzukiDonoghueHerglotzTransform

/-!
# The Donoghue transform of a countable atomic spectral measure

The Suzuki lattice is indexed by `ZZ`, so the spectral measure carries countably many atoms and its
Donoghue transform is a series rather than a finite sum.  It converges, and absolutely.

The reason is that the Donoghue kernel is bounded *uniformly in the spectral variable*: above the
real axis its size is controlled by the imaginary height alone.  So the series is dominated
termwise by the masses times one constant, and summable masses give an absolutely summable
transform.  The same bound makes the transform a Herglotz function, since each term has positive
imaginary part and at least one mass is positive.

This removes the finiteness restriction from the Clark reconstruction: the transform exists for the
full countable lattice.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-- The Donoghue transform of a countable atomic spectral measure. -/
noncomputable def donoghueSeriesTransform (p x : ℤ → ℝ) (z : ℂ) : ℂ :=
  ∑' k, (p k : ℂ) * suzukiDonoghueKernel (x k) z

/-- **The Donoghue series converges absolutely.**  The kernel is bounded uniformly in the spectral
variable, so the series is dominated by the masses times one constant. -/
theorem summable_donoghueSeries {p x : ℤ → ℝ} (hp : Summable p) (hp0 : ∀ k, 0 ≤ p k)
    {z : ℂ} (hz : 0 < z.im) :
    Summable (fun k => (p k : ℂ) * suzukiDonoghueKernel (x k) z) := by
  refine Summable.of_norm_bounded (hp.mul_right (‖z‖ + (‖z‖ ^ (2 : ℕ) + 1) / z.im)) ?_
  intro k
  have hpk : ‖((p k : ℝ) : ℂ)‖ = p k := by simp [abs_of_nonneg (hp0 k)]
  rw [norm_mul, hpk]
  exact mul_le_mul_of_nonneg_left (norm_suzukiDonoghueKernel_le hz (x k)) (hp0 k)

theorem im_donoghueSeries_term {p x : ℤ → ℝ} (z : ℂ) (k : ℤ) :
    ((p k : ℂ) * suzukiDonoghueKernel (x k) z).im
      = p k * (suzukiDonoghueKernel (x k) z).im := by
  simp [Complex.mul_im]

/-- **The countable Donoghue transform is a Herglotz function.**  Every term has positive imaginary
part and at least one mass is positive. -/
theorem im_donoghueSeriesTransform_pos {p x : ℤ → ℝ} (hp : Summable p) (hp0 : ∀ k, 0 ≤ p k)
    {k₀ : ℤ} (hk₀ : 0 < p k₀) {z : ℂ} (hz : 0 < z.im) :
    0 < (donoghueSeriesTransform p x z).im := by
  have hsum := summable_donoghueSeries (x := x) hp hp0 hz
  have hsumIm : Summable (fun k => ((p k : ℂ) * suzukiDonoghueKernel (x k) z).im) := by
    obtain ⟨a, ha⟩ := hsum
    exact ⟨a.im, ((Complex.hasSum_iff _ _).mp ha).2⟩
  have hnonneg : ∀ k, 0 ≤ ((p k : ℂ) * suzukiDonoghueKernel (x k) z).im := by
    intro k
    rw [im_donoghueSeries_term]
    exact mul_nonneg (hp0 k) (im_suzukiDonoghueKernel_pos hz _).le
  have hpos : 0 < ((p k₀ : ℂ) * suzukiDonoghueKernel (x k₀) z).im := by
    rw [im_donoghueSeries_term]
    exact mul_pos hk₀ (im_suzukiDonoghueKernel_pos hz _)
  rw [donoghueSeriesTransform, Complex.im_tsum hsum]
  exact lt_of_lt_of_le hpos (hsumIm.le_tsum k₀ fun j _ => hnonneg j)

/-- **The countable transform is Schur after Cayley.**  The inner function of the full lattice
exists. -/
theorem normSq_cayleyOfHerglotz_donoghueSeriesTransform_lt_one {p x : ℤ → ℝ}
    (hp : Summable p) (hp0 : ∀ k, 0 ≤ p k) {k₀ : ℤ} (hk₀ : 0 < p k₀) {z : ℂ} (hz : 0 < z.im) :
    Complex.normSq (cayleyOfHerglotz (donoghueSeriesTransform p x z)) < 1 :=
  normSq_cayleyOfHerglotz_lt_one (im_donoghueSeriesTransform_pos hp hp0 hk₀ hz)

/-- The transform depends on nothing but the jets, so it is a Clark reconstruction for the full
countable lattice. -/
theorem donoghueSeriesTransform_congr {p₁ x₁ p₂ x₂ : ℤ → ℝ}
    (hp : p₁ = p₂) (hx : x₁ = x₂) :
    donoghueSeriesTransform p₁ x₁ = donoghueSeriesTransform p₂ x₂ := by
  rw [hp, hx]

end GaloisForLFunctions.RHTower
