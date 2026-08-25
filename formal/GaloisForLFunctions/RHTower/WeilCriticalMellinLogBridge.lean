import GaloisForLFunctions.RHTower.XiSimpleCriticalExponentialTypeBound
import GaloisForLFunctions.RHTower.SoninOneSidedPacket
import GaloisForLFunctions.RHTower.PaleyWienerNorms
import Mathlib.Analysis.MellinTransform

noncomputable section

open Complex MeasureTheory Set
open scoped FourierTransform ENNReal

namespace RHTower

/-- Logarithmic half-density profile of a multiplicative Weil test. -/
def weilCriticalLogProfile (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * g (Real.exp x)

theorem continuous_weilCriticalLogProfile {g : ℝ → ℂ} (hg : Continuous g) :
    Continuous (weilCriticalLogProfile g) := by
  unfold weilCriticalLogProfile
  fun_prop

theorem weilCriticalLogProfile_support_subset_Icc
    {a : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a)) :
    Function.support (weilCriticalLogProfile g) ⊆ Icc (-a) a := by
  intro x hx
  have hgx : g (Real.exp x) ≠ 0 := by
    intro hzero
    exact hx (by simp [weilCriticalLogProfile, hzero])
  have hmem := hsupp hgx
  constructor
  · exact (Real.exp_le_exp.mp hmem.1)
  · exact Real.exp_le_exp.mp hmem.2

theorem hasCompactSupport_weilCriticalLogProfile
    {a : ℝ} {g : ℝ → ℂ}
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a)) :
    HasCompactSupport (weilCriticalLogProfile g) := by
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (weilCriticalLogProfile_support_subset_Icc hsupp)

/-- The card's critical-line Mellin transform is exactly the Fourier transform of its logarithmic
half-density profile, with mathlib's frequency normalization. -/
theorem mellin_criticalLine_eq_fourier_weilCriticalLogProfile
    (g : ℝ → ℂ) (t : ℝ) :
    mellin g ((1 / 2 : ℂ) + (t : ℂ) * I) =
      FourierTransform.fourier (weilCriticalLogProfile g) (-t / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hre : (((1 / 2 : ℂ) + (t : ℂ) * I).re) = (1 / 2 : ℝ) := by norm_num
  have him : (((1 / 2 : ℂ) + (t : ℂ) * I).im) = t := by simp
  rw [hre, him]
  have hprofile :
      (fun u : ℝ => Real.exp (-(1 / 2 : ℝ) * u) • g (Real.exp (-u))) =
        fun u : ℝ => weilCriticalLogProfile g (-u) := by
    funext u
    rw [weilCriticalLogProfile]
    simp only [Complex.real_smul]
    congr 1
    push_cast
    congr 1
    ring
  rw [hprofile]
  rw [fourier_comp_neg]
  ring_nf

theorem memLp_two_weilCriticalLogProfile
    {a : ℝ} {g : ℝ → ℂ} (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a)) :
    MemLp (weilCriticalLogProfile g) 2 volume := by
  let φ : ℝ → ℂ := weilCriticalLogProfile g
  have hφcont : Continuous φ := continuous_weilCriticalLogProfile hg
  have hsuppφ : Function.support φ ⊆ Icc (-a) a :=
    weilCriticalLogProfile_support_subset_Icc hsupp
  have hind := GaloisForLFunctions.RHTower.memLp_indicator_of_continuous hφcont a
  have hindicator : Set.indicator (Icc (-a) a) φ = φ := by
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · simp [Set.indicator_of_mem hx]
    · have hzero : φ x = 0 := by
        by_contra hne
        exact hx (hsuppφ hne)
      simp [Set.indicator_of_notMem hx, hzero]
  rwa [hindicator] at hind

/-- Literal global `L²` carrier of the logarithmic Weil profile. -/
def weilCriticalLogProfileL2
    (a : ℝ) (g : ℝ → ℂ) (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a)) : SoninL2 :=
  (memLp_two_weilCriticalLogProfile hg hsupp).toLp (weilCriticalLogProfile g)

theorem weilCriticalLogProfileL2_ae
    (a : ℝ) (g : ℝ → ℂ) (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a)) :
    (weilCriticalLogProfileL2 a g hg hsupp : ℝ → ℂ) =ᵐ[volume]
      weilCriticalLogProfile g := by
  simpa only [weilCriticalLogProfileL2] using
    (memLp_two_weilCriticalLogProfile hg hsupp).coeFn_toLp

theorem suzukiCutoff_weilCriticalLogProfileL2_ae
    {a : ℝ} (g : ℝ → ℂ) (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a)) :
    (suzukiCutoff a (weilCriticalLogProfileL2 a g hg hsupp) : ℝ → ℂ) =ᵐ[volume]
      weilCriticalLogProfile g := by
  filter_upwards [indicatorCutoff_ae (Icc (-a) a) measurableSet_Icc
      (weilCriticalLogProfileL2 a g hg hsupp),
    weilCriticalLogProfileL2_ae a g hg hsupp] with x hcut hrep
  rw [hcut]
  by_cases hx : x ∈ Icc (-a) a
  · rw [Set.indicator_of_mem hx, hrep]
  · have hzero : weilCriticalLogProfile g x = 0 := by
      by_contra hne
      exact hx (weilCriticalLogProfile_support_subset_Icc hsupp hne)
    rw [Set.indicator_of_notMem hx, hzero]

/-- The actual Mellin value equals Suzuki's entire compact Fourier carrier for the canonical
`L²` logarithmic profile. -/
theorem mellin_criticalLine_eq_suzukiCompactL2Fourier
    {a : ℝ} (g : ℝ → ℂ) (hg : Continuous g)
    (hsupp : Function.support g ⊆ Icc (Real.exp (-a)) (Real.exp a)) (t : ℝ) :
    mellin g ((1 / 2 : ℂ) + (t : ℂ) * I) =
      suzukiCompactL2Fourier a (weilCriticalLogProfileL2 a g hg hsupp) t := by
  rw [mellin_criticalLine_eq_fourier_weilCriticalLogProfile]
  have hsuz := suzukiCompactL2Fourier_real_eq_fourier a
    (weilCriticalLogProfileL2 a g hg hsupp) (-t / (2 * Real.pi))
  have harg : -2 * Real.pi * (-t / (2 * Real.pi)) = t := by
    field_simp [Real.pi_ne_zero]
  rw [harg] at hsuz
  rw [hsuz]
  unfold FourierTransform.fourier
  apply MeasureTheory.integral_congr_ae
  filter_upwards [suzukiCutoff_weilCriticalLogProfileL2_ae g hg hsupp] with x hx
  rw [hx]

end RHTower
