import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialCriticalPrimeKernelDensity
import GaloisForLFunctions.HTGeometry.BandLimitedPositiveConfiguration

/-!
# Exact total mass of the critical prime kernel weight

The cosine weight is a scaled sinc-square density. The existing band-limited
Fourier identity kills every nonzero integer frequency in a finite pattern,
leaving exactly its coefficient-square mass on the positive half-line.
Singleton harmonic masses agree with the existing scalar harmonic defect.

These normalization identities do not decide the signed arithmetic kernel.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

open HTGeometry.BandLimitedPositiveDensity

/-- Every singleton pattern uses the existing scalar harmonic defect. -/
theorem factorialCriticalPatternHarmonicMass_singleton (j : ℕ) (b : ℕ → ℝ) (m : ℕ) :
    factorialCriticalPatternHarmonicMass {j} b m =
      b j ^ 2 * factorialCriticalHarmonicDefect m := by
  have hQ (t : ℝ) : factorialCriticalPatternDensity {j} b t = b j ^ 2 := by
    simp only [factorialCriticalPatternDensity_eq, Finset.sum_singleton,
      sub_self, mul_zero, zero_mul, Real.cos_zero, mul_one, pow_two]
  unfold factorialCriticalPatternHarmonicMass factorialCriticalHarmonicDefect
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  dsimp only
  rw [hQ, show 2 * Real.pi * (m : ℝ) * v / 12 =
    2 * Real.pi * ((m : ℝ) / 12) * v by ring]
  ring

private def kernelMassSinc (u : ℝ) : ℝ := sincSq ((1 / 12 : ℝ) * u)

private theorem kernel_mass_sinc_integrable : Integrable kernelMassSinc :=
  integrable_sincSq.comp_mul_left' (by norm_num : (1 / 12 : ℝ) ≠ 0)

private theorem kernel_mass_sinc_integral : ∫ u : ℝ, kernelMassSinc u = 12 := by
  change (∫ u : ℝ, sincSq ((1 / 12 : ℝ) * u)) = 12
  rw [Measure.integral_comp_mul_left, integral_sincSq]
  norm_num

/-- The native cosine weight is a scaled existing band-limited sinc-square density. -/
theorem factorialCriticalPrimeKernelWeight_eq_sincSq {u : ℝ} (hu : 0 < u) :
    factorialCriticalPrimeKernelWeight u =
      (Real.pi ^ 2 / 72) * sincSq ((1 / 12 : ℝ) * u) := by
  have hθ : Real.pi * ((1 / 12 : ℝ) * u) ≠ 0 := by positivity
  rw [factorialCriticalPrimeKernelWeight, Real.rpow_neg hu.le, Real.rpow_two,
    sincSq, Real.sinc_of_ne_zero hθ]
  rw [show 2 * Real.pi * u / 12 = 2 * (Real.pi * ((1 / 12 : ℝ) * u)) by ring,
    Real.cos_two_mul, Real.cos_sq']
  field_simp
  ring

private theorem kernel_mass_cos_integrable (i j : ℕ) :
    Integrable (fun u : ℝ => kernelMassSinc u *
      Real.cos (2 * Real.pi * ((i : ℝ) - j) * u)) := by
  apply kernel_mass_sinc_integrable.mul_bdd (c := 1) (by fun_prop)
  filter_upwards [] with u
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * ((i : ℝ) - j) * u)

private theorem kernel_mass_cos_integral (i j : ℕ) :
    (∫ u : ℝ, kernelMassSinc u * Real.cos (2 * Real.pi * ((i : ℝ) - j) * u)) =
      if i = j then 12 else 0 := by
  split_ifs with hij
  · subst j
    simpa only [sub_self, mul_zero, zero_mul, Real.cos_zero, mul_one] using kernel_mass_sinc_integral
  have hgap : (1 : ℝ) ≤ |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : (i : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_neg (by linarith : (i : ℝ) - j < 0)]
      linarith
    · have hle : (j : ℝ) + 1 ≤ i := by exact_mod_cast (Nat.succ_le_iff.mpr h)
      rw [abs_of_pos (by linarith : 0 < (i : ℝ) - j)]
      linarith
  have hε : (0 : ℝ) < Real.pi / 6 := by positivity
  have hs : Real.pi / 6 ≤ |2 * Real.pi * ((i : ℝ) - j)| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    calc
      Real.pi / 6 ≤ 2 * Real.pi := by linarith [Real.pi_pos]
      _ = (2 * Real.pi) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hgap (by positivity)
  have h := HTGeometry.BandLimitedPositiveConfiguration.integral_cexp_mul_sincSq_scaled_eq_zero hε hs
  have hscale : Real.pi / 6 / (2 * Real.pi) = (1 / 12 : ℝ) := by field_simp; norm_num
  rw [hscale] at h
  have hi : Integrable (fun u : ℝ => Complex.exp (((2 * Real.pi * ((i : ℝ) - j) * u : ℝ) : ℂ) * Complex.I) *
      (kernelMassSinc u : ℂ)) := by
    apply kernel_mass_sinc_integrable.ofReal.bdd_mul (c := 1) (by fun_prop)
    filter_upwards [] with u
    rw [Complex.norm_exp_ofReal_mul_I]
  have hr := congrArg (RCLike.re : ℂ → ℝ) h
  change RCLike.re (∫ u : ℝ,
    Complex.exp (((2 * Real.pi * ((i : ℝ) - j) * u : ℝ) : ℂ) * Complex.I) *
      (kernelMassSinc u : ℂ)) = 0 at hr
  rw [← integral_re hi] at hr
  change (∫ u : ℝ,
    (Complex.exp (((2 * Real.pi * ((i : ℝ) - j) * u : ℝ) : ℂ) * Complex.I) *
      (kernelMassSinc u : ℂ)).re) = 0 at hr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.exp_ofReal_mul_I_re] at hr
  simpa only [mul_comm] using hr

private theorem kernel_mass_pattern_integrable (S : Finset ℕ) (b : ℕ → ℝ) :
    Integrable (fun u : ℝ => kernelMassSinc u * factorialCriticalPatternDensity S b u) := by
  apply kernel_mass_sinc_integrable.mul_bdd
    (c := (∑ j ∈ S, |b j|)^2) (continuous_factorialCriticalPatternDensity S b).aestronglyMeasurable
  filter_upwards [] with u
  exact factorialCriticalPatternDensity_le S b u

private theorem kernel_mass_pattern_integral (S : Finset ℕ) (b : ℕ → ℝ) :
    (∫ u : ℝ, kernelMassSinc u * factorialCriticalPatternDensity S b u) =
      12 * ∑ j ∈ S, b j ^ 2 := by
  classical
  have hi (i j : ℕ) : Integrable (fun u : ℝ => kernelMassSinc u *
      (b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * u))) := by
    convert (kernel_mass_cos_integrable i j).const_mul (b i * b j) using 1
    funext u
    ring
  calc
    _ = ∑ i ∈ S, ∑ j ∈ S, b i * b j * (if i = j then 12 else 0) := by
      simp_rw [factorialCriticalPatternDensity_eq, Finset.mul_sum]
      rw [integral_finsetSum S (fun i _ => integrable_finsetSum S (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i hiS
      rw [integral_finsetSum S (fun j _ => hi i j)]
      apply Finset.sum_congr rfl
      intro j hjS
      rw [show (fun u : ℝ => kernelMassSinc u *
          (b i * b j * Real.cos (2 * Real.pi * ((i : ℝ) - j) * u))) =
          (fun u : ℝ => (b i * b j) * (kernelMassSinc u *
            Real.cos (2 * Real.pi * ((i : ℝ) - j) * u))) by funext u; ring,
        integral_const_mul, kernel_mass_cos_integral]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hiS
      rw [Finset.sum_eq_single i]
      · simp only [ite_true]
        ring
      · intro j hjS hji
        rw [if_neg hji.symm]
        ring
      · intro hiN
        exact (hiN hiS).elim

private theorem kernel_mass_pattern_half_integral (S : Finset ℕ) (b : ℕ → ℝ) :
    (∫ u in Ioi (0 : ℝ), kernelMassSinc u * factorialCriticalPatternDensity S b u) =
      6 * ∑ j ∈ S, b j ^ 2 := by
  have hg (u : ℝ) : kernelMassSinc (-u) = kernelMassSinc u := by
    simp only [kernelMassSinc, sincSq, mul_neg, Real.sinc_neg]
  have hQ (u : ℝ) : factorialCriticalPatternDensity S b (-u) =
      factorialCriticalPatternDensity S b u := by
    simp only [factorialCriticalPatternDensity_eq, mul_neg, Real.cos_neg]
  have habs : (fun u : ℝ => kernelMassSinc |u| * factorialCriticalPatternDensity S b |u|) =
      (fun u : ℝ => kernelMassSinc u * factorialCriticalPatternDensity S b u) := by
    funext u
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu]
    · rw [abs_of_nonpos hu, hg, hQ]
  have h := integral_comp_abs (f := fun u : ℝ =>
    kernelMassSinc u * factorialCriticalPatternDensity S b u)
  rw [habs, kernel_mass_pattern_integral] at h
  linarith

/-- The native full half-line pattern mass is an integral of an integrable function. -/
theorem integrableOn_factorialCriticalPrimeKernelWeight_pattern (S : Finset ℕ) (b : ℕ → ℝ) :
    IntegrableOn (fun u : ℝ => factorialCriticalPrimeKernelWeight u *
      factorialCriticalPatternDensity S b u) (Ioi (0 : ℝ)) := by
  apply ((kernel_mass_pattern_integrable S b).const_mul (Real.pi ^ 2 / 72)).integrableOn.congr_fun
    (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi
  intro u hu
  dsimp only
  rw [factorialCriticalPrimeKernelWeight_eq_sincSq hu]
  unfold kernelMassSinc
  ring

/-- The exact full half-line mass of every finite real native coefficient pattern. -/
theorem factorialCriticalPrimeKernelWeight_pattern_mass (S : Finset ℕ) (b : ℕ → ℝ) :
    (∫ u in Ioi (0 : ℝ), factorialCriticalPrimeKernelWeight u *
      factorialCriticalPatternDensity S b u) =
      (Real.pi ^ 2 / 12) * ∑ j ∈ S, b j ^ 2 := by
  calc
    _ = ∫ u in Ioi (0 : ℝ), (Real.pi ^ 2 / 72) *
        (kernelMassSinc u * factorialCriticalPatternDensity S b u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro u hu
      dsimp only
      rw [factorialCriticalPrimeKernelWeight_eq_sincSq hu]
      unfold kernelMassSinc
      ring
    _ = _ := by
      rw [integral_const_mul, kernel_mass_pattern_half_integral]
      ring

end GaloisForLFunctions.ArithmeticPositivityTheory
