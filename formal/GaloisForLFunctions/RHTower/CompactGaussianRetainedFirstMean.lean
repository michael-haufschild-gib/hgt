import GaloisForLFunctions.RHTower.SteinhausGaussianBandFirstMean
import GaloisForLFunctions.RHTower.SmoothAFEReflectedWindowFirstMean

open Complex Filter Topology Set Finset MeasureTheory
noncomputable section
namespace RHTower
open SteinhausModel

/-- Literal retained Gaussian carrier after removing the common reflected row.
The retained prime set and polynomial cutoff are independent parameters. -/
def compactGaussianRetainedCarrier (s : ℂ) (N : ℝ) (L : ℕ) (S : Finset ℕ) (ω : Omega) : ℂ :=
  (N : ℂ) ^ ((1 / 2 : ℂ) - s) *
    ∑ n ∈ Sieve.smoothUpTo S L,
      (n : ℂ) ^ (s - 1) * smoothAFECutoff ((n : ℝ) / N) * X n ω

/-- The normalized retained carrier is entire in the spectral variable. -/
theorem differentiable_compactGaussianRetainedCarrier {N : ℝ} (hN : 0 < N)
    (L : ℕ) (S : Finset ℕ) (ω : Omega) :
    Differentiable ℂ (fun s => compactGaussianRetainedCarrier s N L S ω) := by
  have hscale : Differentiable ℂ (fun s : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - s)) :=
    ((differentiable_const (1 / 2 : ℂ)).sub differentiable_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
  apply hscale.mul
  apply Differentiable.fun_sum
  intro n hn
  have hnpos : 0 < n := (Sieve.mem_smoothUpTo.mp hn).1.1
  exact (((differentiable_id.sub_const (1 : ℂ)).const_cpow (c := (n : ℂ))
    (Or.inl (by exact_mod_cast hnpos.ne'))).mul_const _).mul_const _

/-- Joint measurability is explicit, before taking any compact envelope. -/
theorem measurable_compactGaussianRetainedCarrier_joint {N : ℝ} (hN : 0 < N)
    (L : ℕ) (S : Finset ℕ) :
    Measurable (fun q : Omega × ℂ => compactGaussianRetainedCarrier q.2 N L S q.1) := by
  have hscale : Continuous (fun s : ℂ => (N : ℂ) ^ ((1 / 2 : ℂ) - s)) :=
    (((differentiable_const (1 / 2 : ℂ)).sub differentiable_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))).continuous
  apply (hscale.measurable.comp measurable_snd).mul
  apply Finset.measurable_sum
  intro n hn
  have hnpos : 0 < n := (Sieve.mem_smoothUpTo.mp hn).1.1
  have hpow : Continuous (fun s : ℂ => (n : ℂ) ^ (s - 1)) :=
    ((differentiable_id.sub_const (1 : ℂ)).const_cpow
      (Or.inl (by exact_mod_cast hnpos.ne'))).continuous
  exact ((hpow.measurable.comp measurable_snd).mul_const _).mul
    ((measurable_X n).comp measurable_fst)

/-- Exact size of the normalization, retaining the original arithmetic sum. -/
theorem norm_compactGaussianRetainedCarrier (s : ℂ) {N : ℝ} (hN : 0 < N)
    (L : ℕ) (S : Finset ℕ) (ω : Omega) :
    ‖compactGaussianRetainedCarrier s N L S ω‖ =
      ‖∑ n ∈ Sieve.smoothUpTo S L,
        (n : ℂ) ^ (s - 1) * smoothAFECutoff ((n : ℝ) / N) * X n ω‖ /
          N ^ (s.re - 1 / 2) := by
  unfold compactGaussianRetainedCarrier
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN]
  have he : ((1 / 2 : ℂ) - s).re = -(s.re - 1 / 2) := by simp
  rw [he, Real.rpow_neg hN.le]
  simp only [div_eq_mul_inv, mul_comm]

/-- Every fixed normalized carrier has a genuine integrable first norm. -/
theorem integrable_norm_compactGaussianRetainedCarrier (s : ℂ) (N : ℝ)
    (L : ℕ) (S : Finset ℕ) :
    Integrable (fun ω => ‖compactGaussianRetainedCarrier s N L S ω‖) steinhausMeasure := by
  simp only [compactGaussianRetainedCarrier, norm_mul]
  exact (integrable_norm_steinhausFiniteSum
    (fun n => (n : ℂ) ^ (s - 1) * smoothAFECutoff ((n : ℝ) / N))
    (Sieve.smoothUpTo S L)).const_mul _

/-- Uniform first-mean decay on every fixed right-strip abscissa band, for all
imaginary parts, retained prime sets and independent polynomial cutoffs. -/
theorem eventually_integral_norm_compactGaussianRetainedCarrier_band_le
    {a b : ℝ} (ha : 1 / 2 < a) (hab : a ≤ b) (hb : b < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ∀ L : ℕ, ∀ S : Finset ℕ,
      (∫ ω, ‖compactGaussianRetainedCarrier s N L S ω‖ ∂steinhausMeasure) ≤ δ := by
  filter_upwards [eventually_integral_norm_steinhausGaussianWeight_band_cutoff_le
    (a := 1 - b) (b := 1 - a) (by linarith) (by linarith) (by linarith) hδ,
    eventually_ge_atTop (1 : ℕ)] with N hmean hN
  intro s hsA hsB L S
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have he : s - 1 = -((1 - s.re : ℝ) : ℂ) - ((-s.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hphase := integral_norm_steinhausGaussianWindow_phase_eq (1 - s.re) 1 (-s.im) N L
  simp only [one_mul, ← he] at hphase
  have hweight (ω : Omega) :
      (∑ n ∈ Finset.Icc 1 L, (steinhausGaussianWeight (1 - s.re) 1 N n : ℂ) * X n ω) =
      ∑ n ∈ Finset.Icc 1 L, (n : ℂ) ^ (-((1 - s.re : ℝ) : ℂ)) *
        smoothAFECutoff ((n : ℝ) / N) * X n ω := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [steinhausGaussianWeight_coe_eq (1 - s.re) one_pos hN (Finset.mem_Icc.mp hn).1, one_mul]
  have hbound := hmean (1 - s.re) ⟨by linarith, by linarith⟩ L
  simp only [hweight, show 1 / 2 - (1 - s.re) = s.re - 1 / 2 by ring] at hbound
  simp only [norm_compactGaussianRetainedCarrier s hNR, integral_div]
  calc
    _ ≤ (∫ ω, ‖∑ n ∈ Finset.Icc 1 L,
        (n : ℂ) ^ (s - 1) * smoothAFECutoff ((n : ℝ) / N) * X n ω‖ ∂steinhausMeasure) /
          (N : ℝ) ^ (s.re - 1 / 2) :=
      div_le_div_of_nonneg_right
        (integral_norm_smoothUpTo_carrier_le
          (fun n => (n : ℂ) ^ (s - 1) * smoothAFECutoff ((n : ℝ) / N)) L S)
        (Real.rpow_nonneg hNR.le _)
    _ ≤ δ := by rw [hphase]; exact hbound

end RHTower
