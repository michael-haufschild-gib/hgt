import GaloisForLFunctions.SelbergClass.Primon.KestenTiltedMoments
import GaloisForLFunctions.SelbergClass.Primon.PhaseSpectralLaw
import GaloisForLFunctions.HTGeometry.CompactMomentWeakConvergence
import Mathlib.Topology.Order.ProjIcc

/-!
# Power-weighted prime laws concentrate at the spectral endpoints

Regard the prime Hecke law as a probability measure on `[-2,2]` and weight
it by `x^(2n)`, normalized by its even moment. Its moments converge to those
of equal masses at `-2` and `2`. Compact moment convergence upgrades this
to weak convergence and convergence of every continuous observable.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The prime spectral law regarded intrinsically on its compact spectral interval. -/
def kestenIntervalLaw (p : Nat.Primes) : ProbabilityMeasure (Icc (-2 : ℝ) 2) :=
  (kestenSpectralLaw p).map
    (continuous_projIcc (a := (-2 : ℝ)) (b := 2) (h := by norm_num)).measurable.aemeasurable

/-- Passing to the compact interval preserves every continuous coordinate observable. -/
theorem integral_kestenIntervalLaw (p : Nat.Primes) (f : C(ℝ, ℝ)) :
    (∫ x : Icc (-2 : ℝ) 2, f x ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) =
      ∫ x : ℝ, f x ∂(kestenSpectralLaw p : Measure ℝ) := by
  have hc : Continuous (fun x : Icc (-2 : ℝ) 2 => f x) :=
    f.continuous.comp continuous_subtype_val
  rw [kestenIntervalLaw, ProbabilityMeasure.toMeasure_map, integral_map
    continuous_projIcc.measurable.aemeasurable hc.aestronglyMeasurable]
  have ha : ∀ᵐ x ∂(kestenSpectralLaw p : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact kestenSpectralLaw_carried p
  apply integral_congr_ae
  filter_upwards [ha] with x hx
  rw [Set.projIcc_of_mem _ hx]

/-- Passing to the compact interval preserves every prime coordinate moment. -/
theorem integral_kestenIntervalLaw_pow (p : Nat.Primes) (k : ℕ) :
    (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ k ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) =
      kestenMoment p k := by
  have h := integral_kestenIntervalLaw p ⟨fun x => x ^ k, by fun_prop⟩
  change (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ k ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) =
    ∫ x : ℝ, x ^ k ∂(kestenSpectralLaw p : Measure ℝ) at h
  exact h.trans (kestenSpectralLaw_hasMoments p k).2

private def powerTiltWeight (p : Nat.Primes) (n : ℕ) (x : Icc (-2 : ℝ) 2) : ℝ :=
  (x : ℝ) ^ (2 * n) / kestenMoment p (2 * n)

private theorem continuous_powerTiltWeight (p : Nat.Primes) (n : ℕ) :
    Continuous (powerTiltWeight p n) := by unfold powerTiltWeight; fun_prop

private theorem powerTiltWeight_nonneg (p : Nat.Primes) (n : ℕ) (x : Icc (-2 : ℝ) 2) :
    0 ≤ powerTiltWeight p n x := by
  unfold powerTiltWeight
  rw [pow_mul]
  exact div_nonneg (pow_nonneg (sq_nonneg _) n) (kestenMoment_even_pos p n).le

private theorem integral_powerTiltWeight (p : Nat.Primes) (n : ℕ) :
    (∫ x, powerTiltWeight p n x ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) = 1 := by
  unfold powerTiltWeight
  rw [integral_div, integral_kestenIntervalLaw_pow, div_self (kestenMoment_even_pos p n).ne']

private theorem powerTilt_probability (p : Nat.Primes) (n : ℕ) :
    IsProbabilityMeasure ((kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2)).withDensity
      (fun x => ENNReal.ofReal (powerTiltWeight p n x))) := by
  have hi := (continuous_powerTiltWeight p n).integrable_of_hasCompactSupport
    (μ := (kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) (HasCompactSupport.of_compactSpace _)
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi
      (Eventually.of_forall (powerTiltWeight_nonneg p n)), integral_powerTiltWeight, ENNReal.ofReal_one]

/-- The normalized law obtained by weighting the prime coordinate by its even power. -/
def kestenPowerTilt (p : Nat.Primes) (n : ℕ) : ProbabilityMeasure (Icc (-2 : ℝ) 2) :=
  ⟨(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (powerTiltWeight p n x)), powerTilt_probability p n⟩

/-- Every tilted observable is an explicit normalized weighted expectation. -/
theorem integral_kestenPowerTilt (p : Nat.Primes) (n : ℕ) (f : C(Icc (-2 : ℝ) 2, ℝ)) :
    (∫ x, f x ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2))) =
      (∫ x, (x : ℝ) ^ (2 * n) * f x ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) /
        kestenMoment p (2 * n) := by
  change (∫ x, f x ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2)).withDensity
    (fun x => ENNReal.ofReal (powerTiltWeight p n x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_powerTiltWeight p n).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (ENNReal.ofReal (powerTiltWeight p n x)).toReal * f x =
      (x : ℝ) ^ (2 * n) * f x / kestenMoment p (2 * n)
    rw [ENNReal.toReal_ofReal (powerTiltWeight_nonneg p n x)]
    simp only [powerTiltWeight]
    ring

/-- The tilted law realizes the exact normalized shifted prime moments. -/
theorem integral_kestenPowerTilt_pow (p : Nat.Primes) (n k : ℕ) :
    (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ k ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2))) =
      kestenMoment p (2 * n + k) / kestenMoment p (2 * n) := by
  have h := integral_kestenPowerTilt p n ⟨fun x => (x : ℝ) ^ k, by fun_prop⟩
  change (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ k ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2))) =
    (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ (2 * n) * (x : ℝ) ^ k
      ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) / kestenMoment p (2 * n) at h
  simp_rw [← pow_add] at h
  rw [integral_kestenIntervalLaw_pow] at h
  exact h

/-- Equal masses at the two endpoints of the normalized Hecke interval. -/
def kestenEndpointLaw : ProbabilityMeasure (Icc (-2 : ℝ) 2) :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac ⟨-2, by constructor <;> norm_num⟩ +
    (1 / 2 : ENNReal) • Measure.dirac ⟨2, by constructor <;> norm_num⟩,
    by constructor; norm_num; exact ENNReal.inv_two_add_inv_two⟩

/-- Endpoint expectation is the arithmetic mean of the two endpoint values. -/
theorem integral_kestenEndpointLaw (f : C(Icc (-2 : ℝ) 2, ℝ)) :
    (∫ x, f x ∂(kestenEndpointLaw : Measure (Icc (-2 : ℝ) 2))) =
      (f ⟨-2, by constructor <;> norm_num⟩ + f ⟨2, by constructor <;> norm_num⟩) / 2 := by
  have hl : Integrable f (Measure.dirac (⟨-2, by constructor <;> norm_num⟩ : Icc (-2 : ℝ) 2)) :=
    integrable_dirac (by finiteness)
  have hr : Integrable f (Measure.dirac (⟨2, by constructor <;> norm_num⟩ : Icc (-2 : ℝ) 2)) :=
    integrable_dirac (by finiteness)
  change (∫ x, f x ∂((1 / 2 : ENNReal) • Measure.dirac _ + (1 / 2 : ENNReal) • Measure.dirac _)) = _
  rw [integral_add_measure (hl.smul_measure (by norm_num)) (hr.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  norm_num
  ring

/-- Every moment of the endpoint law is the mean of the two endpoint powers. -/
theorem integral_kestenEndpointLaw_pow (k : ℕ) :
    (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ k ∂(kestenEndpointLaw : Measure (Icc (-2 : ℝ) 2))) =
      ((-2 : ℝ) ^ k + (2 : ℝ) ^ k) / 2 :=
  integral_kestenEndpointLaw ⟨fun x => (x : ℝ) ^ k, by fun_prop⟩

/-- High even-power weighting converges weakly to equal endpoint masses, for every prime. -/
theorem tendsto_kestenPowerTilt (p : Nat.Primes) :
    Tendsto (kestenPowerTilt p) atTop (𝓝 kestenEndpointLaw) := by
  letI : Nonempty (Icc (-2 : ℝ) 2) := ⟨⟨0, by constructor <;> norm_num⟩⟩
  apply probabilityMeasure_tendsto_of_integral_pow_tendsto
  intro k
  simp_rw [integral_kestenPowerTilt_pow, integral_kestenEndpointLaw_pow]
  exact tendsto_kestenMoment_weighted_ratio p k

/-- Every continuous observable sees equal masses at the two spectral endpoints. -/
theorem tendsto_integral_kestenPowerTilt (p : Nat.Primes) (f : C(Icc (-2 : ℝ) 2, ℝ)) :
    Tendsto (fun n => ∫ x, f x ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2))) atTop
      (𝓝 ((f ⟨-2, by constructor <;> norm_num⟩ + f ⟨2, by constructor <;> norm_num⟩) / 2)) := by
  have h := (continuous_integral_real_continuousMap f).tendsto kestenEndpointLaw |>.comp
    (tendsto_kestenPowerTilt p)
  rwa [integral_kestenEndpointLaw] at h

/-- The tilted compact law, viewed as a probability law on the real line. -/
def kestenPowerTiltReal (p : Nat.Primes) (n : ℕ) : ProbabilityMeasure ℝ :=
  (kestenPowerTilt p n).map continuous_subtype_val.measurable.aemeasurable

/-- Real tilted expectations are normalized weighted expectations of the original prime law. -/
theorem integral_kestenPowerTiltReal (p : Nat.Primes) (n : ℕ) (f : C(ℝ, ℝ)) :
    (∫ x, f x ∂(kestenPowerTiltReal p n : Measure ℝ)) =
      (∫ x, x ^ (2 * n) * f x ∂(kestenSpectralLaw p : Measure ℝ)) /
        kestenMoment p (2 * n) := by
  rw [kestenPowerTiltReal, ProbabilityMeasure.toMeasure_map,
    integral_map continuous_subtype_val.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  have h := integral_kestenPowerTilt p n ⟨fun x => f x, f.continuous.comp continuous_subtype_val⟩
  have hb := integral_kestenIntervalLaw p ⟨fun x => x ^ (2 * n) * f x, by fun_prop⟩
  change (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ (2 * n) * f x
    ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) = _ at hb
  change (∫ x : Icc (-2 : ℝ) 2, f x ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2))) =
    (∫ x : Icc (-2 : ℝ) 2, (x : ℝ) ^ (2 * n) * f x
      ∂(kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2))) / kestenMoment p (2 * n) at h
  rw [hb] at h
  exact h

/-- Every normalized weighted continuous expectation converges to the mean endpoint value. -/
theorem tendsto_weighted_kestenSpectralLaw_integral (p : Nat.Primes) (f : C(ℝ, ℝ)) :
    Tendsto (fun n : ℕ =>
      (∫ x, x ^ (2 * n) * f x ∂(kestenSpectralLaw p : Measure ℝ)) / kestenMoment p (2 * n))
      atTop (𝓝 ((f (-2) + f 2) / 2)) := by
  have h := tendsto_integral_kestenPowerTilt p
    ⟨fun x => f x, f.continuous.comp continuous_subtype_val⟩
  change Tendsto (fun n => ∫ x : Icc (-2 : ℝ) 2, f x
    ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2))) atTop (𝓝 ((f (-2) + f 2) / 2)) at h
  have he (n : ℕ) :
      (∫ x, x ^ (2 * n) * f x ∂(kestenSpectralLaw p : Measure ℝ)) / kestenMoment p (2 * n) =
      ∫ x : Icc (-2 : ℝ) 2, f x ∂(kestenPowerTilt p n : Measure (Icc (-2 : ℝ) 2)) := by
    rw [← integral_kestenPowerTiltReal, kestenPowerTiltReal, ProbabilityMeasure.toMeasure_map,
      integral_map continuous_subtype_val.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  simpa only [he] using h

/-- The equal-endpoint law, viewed as a probability law on the real line. -/
def kestenEndpointRealLaw : ProbabilityMeasure ℝ :=
  kestenEndpointLaw.map continuous_subtype_val.measurable.aemeasurable

/-- The real endpoint law is exactly the equally weighted pair of Dirac masses. -/
theorem kestenEndpointRealLaw_eq :
    (kestenEndpointRealLaw : Measure ℝ) =
      (1 / 2 : ENNReal) • Measure.dirac (-2 : ℝ) + (1 / 2 : ENNReal) • Measure.dirac (2 : ℝ) := by
  rw [kestenEndpointRealLaw, ProbabilityMeasure.toMeasure_map]
  change Measure.map Subtype.val
    ((1 / 2 : ENNReal) • Measure.dirac (⟨-2, _⟩ : Icc (-2 : ℝ) 2) +
      (1 / 2 : ENNReal) • Measure.dirac (⟨2, _⟩ : Icc (-2 : ℝ) 2)) = _
  rw [Measure.map_add _ _ continuous_subtype_val.measurable,
    Measure.map_smul, Measure.map_smul,
    Measure.map_dirac, Measure.map_dirac]

/-- Weak endpoint concentration also holds as a statement about real probability measures. -/
theorem tendsto_kestenPowerTiltReal (p : Nat.Primes) :
    Tendsto (kestenPowerTiltReal p) atTop (𝓝 kestenEndpointRealLaw) :=
  (ProbabilityMeasure.continuous_map continuous_subtype_val).continuousAt.tendsto.comp
    (tendsto_kestenPowerTilt p)

end
end GaloisForLFunctions.SelbergClass.Primon
