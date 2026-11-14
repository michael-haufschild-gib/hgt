import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicClosedDomain
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.SoftLogarithmicCompactTrials
import GaloisForLFunctions.HTGeometry.HardyBoundary.LogarithmicCutoffConvergence

/-!
# Compact physical cutoffs of finite-energy half-line profiles

Choose a real representative with pointwise half-line support. Expanding
Lipschitz cutoffs preserve its reference logarithmic energy and give
literal compact trial profiles with the same L² representatives.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open _root_.RHTower
open scoped FourierTransform
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open HTGeometry CriticalArithmeticCorrelationTheory ArithmeticCastelnuovoSeveri
open CanonicalSystemOfTheWindowTower

/-- Expanding physical cutoffs, reflected onto the negative half-line. -/
def softLogarithmicCutoff (n : ℕ) (u : ℝ) : ℝ :=
  logarithmicEndpointCutoff ((n : ℝ) + 2) (-u)

theorem continuous_softLogarithmicCutoff (n : ℕ) : Continuous (softLogarithmicCutoff n) :=
  (continuous_logarithmicEndpointCutoff _).comp continuous_neg

theorem softLogarithmicCutoff_nonneg (n : ℕ) (u : ℝ) : 0 ≤ softLogarithmicCutoff n u :=
  logarithmicEndpointCutoff_nonneg _ _

theorem softLogarithmicCutoff_abs_le (n : ℕ) (u : ℝ) : |softLogarithmicCutoff n u| ≤ 1 :=
  logarithmicEndpointCutoff_abs_le _ _

theorem softLogarithmicCutoff_lipschitz (n : ℕ) (x y : ℝ) :
    |softLogarithmicCutoff n x - softLogarithmicCutoff n y| ≤ |x - y| := by
  have ha : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hc : (2 : ℝ) / ((n : ℝ) + 2) ≤ 1 :=
    (div_le_one ha).mpr (by linarith only [hn])
  have h := logarithmicEndpointCutoff_lipschitz ha (-x) (-y)
  rw [show -x - -y = -(x - y) by ring, abs_neg] at h
  exact h.trans ((mul_le_mul_of_nonneg_right hc (abs_nonneg (x - y))).trans_eq (one_mul _))

theorem softLogarithmicCutoff_eq_zero (n : ℕ) {u : ℝ}
    (hu : u ≤ -(2 * ((n : ℝ) + 2))) : softLogarithmicCutoff n u = 0 := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  apply logarithmicEndpointCutoff_eq_zero (by positivity : (0 : ℝ) < (n : ℝ) + 2)
  linarith only [hu, hn]

theorem tendsto_softLogarithmicCutoff (u : ℝ) :
    Tendsto (fun n => softLogarithmicCutoff n u) atTop (𝓝 1) := by
  have hlarge : ∀ᶠ n : ℕ in atTop, -u ≤ (n : ℝ) + 2 :=
    (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop).eventually_ge_atTop (-u)
  have he : (fun n => softLogarithmicCutoff n u) =ᶠ[atTop] fun _ => (1 : ℝ) := by
    filter_upwards [hlarge] with n hn
    exact logarithmicEndpointCutoff_eq_one (by positivity : (0 : ℝ) < (n : ℝ) + 2) hn
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem softLogarithmicCutoff_error_abs_le (n : ℕ) (u : ℝ) :
    |1 - softLogarithmicCutoff n u| ≤ 1 := by
  have h0 := softLogarithmicCutoff_nonneg n u
  have h1 := le_of_abs_le (softLogarithmicCutoff_abs_le n u)
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith only [h0]

theorem softLogarithmicCutoff_error_lipschitz (n : ℕ) (x y : ℝ) :
    |(1 - softLogarithmicCutoff n x) - (1 - softLogarithmicCutoff n y)| ≤ |x - y| := by
  rw [show (1 - softLogarithmicCutoff n x) - (1 - softLogarithmicCutoff n y) =
    -(softLogarithmicCutoff n x - softLogarithmicCutoff n y) by ring, abs_neg]
  exact softLogarithmicCutoff_lipschitz n x y

/-- A measurable real representative with pointwise negative-half-line support. -/
def softLogarithmicRealProfile (v : SoninL2) : ℝ → ℝ :=
  (Iio (0 : ℝ)).indicator (fun u => (v u).re)

theorem measurable_softLogarithmicRealProfile (v : SoninL2) :
    Measurable (softLogarithmicRealProfile v) :=
  (Complex.continuous_re.measurable.comp (Lp.stronglyMeasurable v).measurable).indicator
    measurableSet_Iio

theorem ClosedSoftLogarithmicHalfLineDomain.realProfile_ae {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) :
    cx (softLogarithmicRealProfile v) =ᵐ[volume] (v : ℝ → ℂ) := by
  filter_upwards [hv.real, hv.support] with u hu hs
  change (softLogarithmicRealProfile v u : ℂ) = v u
  unfold softLogarithmicRealProfile
  by_cases hn : u ∈ Iio (0 : ℝ)
  · rw [Set.indicator_of_mem hn]
    apply Complex.ext
    · rfl
    · exact hu.symm
  · rw [Set.indicator_of_notMem hn, hs (le_of_not_gt hn), Complex.ofReal_zero]

/-- The literal compact real profile obtained by physical cutoff. -/
def softLogarithmicCutoffProfile (n : ℕ) (v : SoninL2) (u : ℝ) : ℝ :=
  softLogarithmicCutoff n u * softLogarithmicRealProfile v u

/-- The same physical cutoff as a bounded L² multiplier. -/
def softLogarithmicCutoffVector (n : ℕ) (v : SoninL2) : SoninL2 :=
  logarithmicCutoffMultiplier (continuous_softLogarithmicCutoff n).measurable
    zero_le_one (softLogarithmicCutoff_abs_le n) v

theorem ClosedSoftLogarithmicHalfLineDomain.cutoff_representative {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) (n : ℕ) :
    (softLogarithmicCutoffVector n v : ℝ → ℂ) =ᵐ[volume] cx (softLogarithmicCutoffProfile n v) := by
  filter_upwards [logarithmicCutoffMultiplier_coeFn
    (continuous_softLogarithmicCutoff n).measurable zero_le_one
      (softLogarithmicCutoff_abs_le n) v, hv.realProfile_ae] with u hu hr
  change softLogarithmicCutoffVector n v u =
    (softLogarithmicCutoff n u : ℂ) * v u at hu
  rw [hu, ← hr]
  change (softLogarithmicCutoff n u : ℂ) * (softLogarithmicRealProfile v u : ℂ) =
    ((softLogarithmicCutoff n u * softLogarithmicRealProfile v u : ℝ) : ℂ)
  exact (Complex.ofReal_mul _ _).symm

theorem softLogarithmicCutoffProfile_right (n : ℕ) (v : SoninL2) (u : ℝ)
    (hu : 0 ≤ u) : softLogarithmicCutoffProfile n v u = 0 := by
  change softLogarithmicCutoff n u * (Iio (0 : ℝ)).indicator (fun u => (v u).re) u = 0
  rw [Set.indicator_of_notMem (show u ∉ Iio (0 : ℝ) from not_lt_of_ge hu), mul_zero]

theorem softLogarithmicCutoffProfile_left (n : ℕ) (v : SoninL2) (u : ℝ)
    (hu : u ≤ -(2 * ((n : ℝ) + 2))) : softLogarithmicCutoffProfile n v u = 0 := by
  change softLogarithmicCutoff n u * softLogarithmicRealProfile v u = 0
  rw [softLogarithmicCutoff_eq_zero n hu, zero_mul]

/-- Absolute logarithmic energy implies the positive reference jump domain. -/
theorem ClosedSoftLogarithmicHalfLineDomain.hasReferenceEnergy {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) : HasLogarithmicEnergy v := by
  have hc : (1 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  exact (hasLogarithmicEnergy_iff_integrable v).mpr
    ((integrable_logarithmicReference_iff_positiveLog hc (fourierUnitary v)).mpr
      hv.integrable_positiveLogarithm)

/-- Every compact cutoff of a finite-energy half-line profile belongs to the trial domain. -/
theorem ClosedSoftLogarithmicHalfLineDomain.cutoff_trial {v : SoninL2}
    (hv : ClosedSoftLogarithmicHalfLineDomain v) (n : ℕ) :
    SoftLogarithmicHalfLineDomain (softLogarithmicCutoffProfile n v) := by
  have hrep := hv.cutoff_representative n
  have hm : Measurable (softLogarithmicCutoffProfile n v) :=
    (continuous_softLogarithmicCutoff n).measurable.mul (measurable_softLogarithmicRealProfile v)
  have hc2 : MemLp (cx (softLogarithmicCutoffProfile n v)) 2 volume :=
    (memLp_congr_ae hrep).mp (Lp.memLp (softLogarithmicCutoffVector n v))
  have hsq : Integrable (fun u => softLogarithmicCutoffProfile n v u ^ 2) := by
    have hi := hc2.integrable_norm_pow (by norm_num)
    apply hi.congr
    exact Eventually.of_forall fun u => by
      change ‖(softLogarithmicCutoffProfile n v u : ℂ)‖ ^ 2 =
        softLogarithmicCutoffProfile n v u ^ 2
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hf2 : MemLp (softLogarithmicCutoffProfile n v) 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using hsq
  have hs : Function.support (softLogarithmicCutoffProfile n v) ⊆
      Icc (-(2 * ((n : ℝ) + 2))) 0 := by
    intro u hu
    by_contra hn
    by_cases hl : -(2 * ((n : ℝ) + 2)) ≤ u
    · have hp : 0 < u := lt_of_not_ge fun h => hn ⟨hl, h⟩
      exact hu (softLogarithmicCutoffProfile_right n v u hp.le)
    · exact hu (softLogarithmicCutoffProfile_left n v u (lt_of_not_ge hl).le)
  have hf1 : Integrable (softLogarithmicCutoffProfile n v) :=
    (integrableOn_iff_integrable_of_support_subset hs).mp
      ((hf2.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_Icc)
  have hc : (1 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hcut : HasLogarithmicEnergy (softLogarithmicCutoffVector n v) :=
    hasLogarithmicEnergy_cutoff (continuous_softLogarithmicCutoff n).measurable
      zero_le_one (softLogarithmicCutoff_abs_le n) zero_le_one
      (fun x y => by simpa only [one_mul] using softLogarithmicCutoff_lipschitz n x y)
      hv.hasReferenceEnergy
  have hpos := (integrable_logarithmicReference_iff_positiveLog hc
    (fourierUnitary (softLogarithmicCutoffVector n v))).mp
      ((hasLogarithmicEnergy_iff_integrable (softLogarithmicCutoffVector n v)).mp hcut)
  have hV1 : Integrable (softLogarithmicCutoffVector n v : ℝ → ℂ) :=
    (hf1.ofReal (𝕜 := ℂ)).congr hrep.symm
  have hfourier := coeFn_fourierTransform_eq_fourierIntegral (softLogarithmicCutoffVector n v) hV1
  change (fourierUnitary (softLogarithmicCutoffVector n v) : ℝ → ℂ) =ᵐ[volume]
    𝓕 (softLogarithmicCutoffVector n v : ℝ → ℂ) at hfourier
  have he := hfourier.trans (Eventually.of_forall fun ξ => Real.fourier_congr_ae hrep ξ)
  apply softLogarithmicHalfLineDomain_of_compact_positiveLogarithm hm hsq
    (softLogarithmicCutoffProfile_left n v) (softLogarithmicCutoffProfile_right n v)
  apply hpos.congr
  filter_upwards [he] with ξ hξ
  exact congrArg (fun z : ℂ => max (Real.log |ξ|) 0 * ‖z‖ ^ 2) hξ

#print axioms ClosedSoftLogarithmicHalfLineDomain.realProfile_ae
#print axioms ClosedSoftLogarithmicHalfLineDomain.cutoff_representative
#print axioms ClosedSoftLogarithmicHalfLineDomain.cutoff_trial
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

