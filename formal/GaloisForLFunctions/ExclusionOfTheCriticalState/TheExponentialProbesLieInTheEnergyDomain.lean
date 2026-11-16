import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalHalfLineFormHasItsActualDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.GammaIntegrabilityFromLinearFourierDecay

/-!
# Exponential probes of the half-line energy domain

The probe `e_p(u) = e^{pu}` on `u < 0` (zero on `u ≥ 0`) has Laplace transform
`∫ e_p(u) e^{wu} du = 1/(p + w)` on `Re (p + w) > 0`. For `p > 4` it lies in the actual
finite-energy half-line domain, so the weak equation of the critical state may be tested on it.
Its cosh/sinh moments and confinement pairings are explicit rational functions of `p`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri _root_.RHTower

/-- The exponential probe `e_p(u) = e^{pu}` on `u < 0`, and `0` on `u ≥ 0`. -/
def probe (p : ℝ) : ℝ → ℝ := (Iio (0 : ℝ)).indicator fun u => Real.exp (p * u)

theorem probe_of_neg {p u : ℝ} (hu : u < 0) : probe p u = Real.exp (p * u) :=
  Set.indicator_of_mem (Set.mem_Iio.mpr hu) _

theorem probe_of_nonneg {p u : ℝ} (hu : 0 ≤ u) : probe p u = 0 :=
  Set.indicator_of_notMem (fun h => (not_lt.mpr hu) (Set.mem_Iio.mp h)) _

theorem probe_nonneg (p u : ℝ) : 0 ≤ probe p u :=
  Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) u

theorem measurable_probe (p : ℝ) : Measurable (probe p) :=
  (by fun_prop : Measurable fun u : ℝ => Real.exp (p * u)).indicator measurableSet_Iio

/-- A probe times an exponential is again a probe. -/
theorem probe_mul_exp (p c u : ℝ) : probe p u * Real.exp (c * u) = probe (p + c) u := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [probe_of_neg hu, probe_of_neg hu, ← Real.exp_add]
    ring_nf
  · simp only [probe_of_nonneg hu, zero_mul]

theorem probe_mul_probe (p q u : ℝ) : probe p u * probe q u = probe (p + q) u := by
  rcases lt_or_ge u 0 with hu | hu
  · rw [probe_of_neg hu, probe_of_neg hu, probe_of_neg hu, ← Real.exp_add]
    ring_nf
  · simp only [probe_of_nonneg hu, zero_mul]

theorem integrable_probe {p : ℝ} (hp : 0 < p) : Integrable (probe p) :=
  ((integrableOn_exp_mul_Iic hp 0).mono_set Iio_subset_Iic_self).integrable_indicator
    measurableSet_Iio

/-- The real Laplace transform of a probe. -/
theorem integral_probe {p : ℝ} (hp : 0 < p) : (∫ u, probe p u) = 1 / p := by
  rw [probe, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_Iic hp, mul_zero, Real.exp_zero]

theorem integral_probe_mul_exp {p c : ℝ} (h : 0 < p + c) :
    (∫ u, probe p u * Real.exp (c * u)) = 1 / (p + c) := by
  simp_rw [probe_mul_exp]
  exact integral_probe h

theorem integrable_probe_mul_exp {p c : ℝ} (h : 0 < p + c) :
    Integrable (fun u => probe p u * Real.exp (c * u)) := by
  simp_rw [probe_mul_exp]
  exact integrable_probe h

/-- The complex Laplace transform of a probe: `∫ e_p(u) e^{wu} du = 1/(p + w)`. -/
theorem integral_probe_mul_cexp {p : ℝ} {w : ℂ} (h : 0 < p + w.re) :
    (∫ u, (probe p u : ℂ) * Complex.exp (w * u)) = 1 / (p + w) := by
  have hre : 0 < ((p : ℂ) + w).re := by simpa using h
  have hpt : (fun u : ℝ => (probe p u : ℂ) * Complex.exp (w * u)) =
      (Iio (0 : ℝ)).indicator fun u : ℝ => Complex.exp (((p : ℂ) + w) * u) := by
    funext u
    rcases lt_or_ge u 0 with hu | hu
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr hu), probe_of_neg hu, Complex.ofReal_exp,
        ← Complex.exp_add]
      push_cast
      ring_nf
    · rw [Set.indicator_of_notMem (fun h => (not_lt.mpr hu) (Set.mem_Iio.mp h)),
        probe_of_nonneg hu, Complex.ofReal_zero, zero_mul]
  rw [hpt, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    integral_exp_mul_complex_Iic hre, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- The paper Fourier transform of a probe: `e_p^(z) = 1/(p + i z)` below the line `Im z = p`. -/
theorem paperFT_probe {p : ℝ} {z : ℂ} (h : z.im < p) :
    paperFT (cx (probe p)) z = 1 / (p + Complex.I * z) := by
  have hz : 0 < p + (Complex.I * z).re := by simp; linarith
  rw [← integral_probe_mul_cexp hz]
  rfl

theorem continuous_paperFT_probe {p : ℝ} (hp : 0 < p) :
    Continuous fun r : ℝ => paperFT (cx (probe p)) r := by
  have he : (fun r : ℝ => paperFT (cx (probe p)) r) =
      fun r : ℝ => 1 / ((p : ℂ) + Complex.I * r) := by
    funext r
    exact paperFT_probe (by simpa using hp)
  rw [he]
  refine continuous_const.div (by fun_prop) fun r h => ?_
  have := congrArg Complex.re h
  simp at this
  linarith

/-- The probe's spectrum decays linearly: `(1 + |r|) |e_p^(r)| ≤ 1 + 1/p`. -/
theorem one_add_abs_mul_norm_paperFT_probe_le {p : ℝ} (hp : 0 < p) (r : ℝ) :
    (1 + |r|) * ‖paperFT (cx (probe p)) r‖ ≤ 1 + 1 / p := by
  rw [paperFT_probe (by simpa using hp)]
  set z : ℂ := (p : ℂ) + Complex.I * r with hz
  have hre : z.re = p := by simp [hz]
  have him : z.im = r := by simp [hz]
  have hp' : p ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hre, abs_of_pos hp] at this
    exact this
  have hr' : |r| ≤ ‖z‖ := by
    have := Complex.abs_im_le_norm z
    rwa [him] at this
  have hzpos : 0 < ‖z‖ := hp.trans_le hp'
  rw [norm_div, norm_one, ← div_eq_mul_one_div, div_le_iff₀ hzpos]
  have h1 : 1 ≤ ‖z‖ / p := (one_le_div hp).mpr hp'
  calc 1 + |r| ≤ ‖z‖ / p + ‖z‖ := by linarith
    _ = (1 + 1 / p) * ‖z‖ := by ring

/-- For `p > 4` the probe lies in the actual finite-energy half-line domain. -/
theorem criticalHalfLineEnergyDomain_probe {p : ℝ} (hp : 4 < p) :
    CriticalHalfLineEnergyDomain (probe p) := by
  have hp0 : 0 < p := by linarith
  refine ⟨measurable_probe p, integrable_probe hp0, ?_, ?_, fun u hu => probe_of_nonneg hu, ?_⟩
  · simp_rw [sq, probe_mul_probe]
    exact integrable_probe (by linarith)
  · simp_rw [sq, probe_mul_probe]
    have h := integrable_probe_mul_exp (p := p + p) (c := -8) (by linarith)
    simpa only [neg_mul] using h
  · exact integrable_gammaEnergy_of_linear_decay (continuous_paperFT_probe hp0)
      (one_add_abs_mul_norm_paperFT_probe_le hp0)

/-- The cosh moment of a probe: `C(e_p) = (1/(p+½) + 1/(p-½))/2`. -/
theorem coshHalfMoment_probe {p : ℝ} (hp : 1 / 2 < p) :
    coshHalfMoment (probe p) = (1 / (p + 1 / 2) + 1 / (p - 1 / 2)) / 2 := by
  have h1 := integrable_probe_mul_exp (p := p) (c := 1 / 2) (by linarith)
  have h2 := integrable_probe_mul_exp (p := p) (c := -(1 / 2)) (by linarith)
  have hpt : (fun x => probe p x * Real.cosh (x / 2)) = fun x =>
      (probe p x * Real.exp (1 / 2 * x) + probe p x * Real.exp (-(1 / 2) * x)) / 2 := by
    funext x
    rw [Real.cosh_eq]
    ring_nf
  unfold coshHalfMoment
  rw [hpt, integral_div, integral_add h1 h2, integral_probe_mul_exp (by linarith),
    integral_probe_mul_exp (by linarith)]
  ring

/-- The sinh moment of a probe: `S(e_p) = (1/(p+½) - 1/(p-½))/2`. -/
theorem sinhHalfMoment_probe {p : ℝ} (hp : 1 / 2 < p) :
    sinhHalfMoment (probe p) = (1 / (p + 1 / 2) - 1 / (p - 1 / 2)) / 2 := by
  have h1 := integrable_probe_mul_exp (p := p) (c := 1 / 2) (by linarith)
  have h2 := integrable_probe_mul_exp (p := p) (c := -(1 / 2)) (by linarith)
  have hpt : (fun x => probe p x * Real.sinh (x / 2)) = fun x =>
      (probe p x * Real.exp (1 / 2 * x) - probe p x * Real.exp (-(1 / 2) * x)) / 2 := by
    funext x
    rw [Real.sinh_eq]
    ring_nf
  unfold sinhHalfMoment
  rw [hpt, integral_div, integral_sub h1 h2, integral_probe_mul_exp (by linarith),
    integral_probe_mul_exp (by linarith)]
  ring

/-- The confinement pairing of two probes: `∫_{u<0} e_p e_q e^{-8u} = 1/(p + q - 8)`. -/
theorem confinement_probe_probe {p q : ℝ} (h : 8 < p + q) :
    (∫ u in Iio 0, probe p u * probe q u * Real.exp (-(8 * u))) = 1 / (p + q - 8) := by
  have hpt : (fun u => probe p u * probe q u * Real.exp (-(8 * u))) = probe (p + q - 8) := by
    funext u
    rw [probe_mul_probe, show -(8 * u) = (-8) * u by ring, probe_mul_exp]
    ring_nf
  rw [hpt, setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iio (0 : ℝ))
    (fun u (hu : u ∉ Iio (0 : ℝ)) => probe_of_nonneg (not_lt.mp hu)),
    integral_probe (by linarith)]

/-- Against a profile supported on `u < 0`, the confinement pairing with a probe is a
real Laplace value: `∫_{u<0} F e_p e^{-8u} = ∫ F(u) e^{(p-8)u} du`. -/
theorem confinement_probe_right {F : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0) (p : ℝ) :
    (∫ u in Iio 0, F u * probe p u * Real.exp (-(8 * u))) =
      ∫ u, F u * Real.exp ((p - 8) * u) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Iio (0 : ℝ))
    fun u (hu : u ∉ Iio (0 : ℝ)) => by rw [hF u (not_lt.mp hu), zero_mul, zero_mul]]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  rcases lt_or_ge u 0 with hu | hu
  · simp only [probe_of_neg hu, mul_assoc, ← Real.exp_add]
    ring_nf
  · simp only [hF u hu, zero_mul]

end GaloisForLFunctions.ExclusionOfTheCriticalState
