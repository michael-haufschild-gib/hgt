import GaloisForLFunctions.RHTower.HeatExteriorForce
import GaloisForLFunctions.RHTower.HeatForwardSimpleZeros
import GaloisForLFunctions.RHTower.HeatZeroSumContinuity
import GaloisForLFunctions.HTGeometry.LocalizedHeatPairForce
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import GaloisForLFunctions.HTGeometry.LogDerivZeroPole

/-!
# Evolution of localized vertical heat-zero energy

The regular part of the logarithmic derivative gives each simple zero's
velocity. Pairwise symmetrization bounds horizontal cutoff flux uniformly
as zero gaps shrink.
-/

open Complex Filter Topology Set Metric MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private theorem second_div_first_eq_twice_regular_part
    {f R : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (hz : f a = 0) (hd : deriv f a ≠ 0) (hR : ContinuousAt R a)
    (heq : ∀ᶠ z in 𝓝[≠] a, logDeriv f z = 1 / (z - a) + R z) :
    deriv (deriv f) a / deriv f a = 2 * R a := by
  obtain ⟨p, hp⟩ := hf
  have hg : AnalyticAt ℂ (dslope f a) a :=
    hp.has_fpower_series_dslope_fslope.analyticAt
  have hgn : dslope f a a ≠ 0 := by rwa [dslope_same]
  have hfac : ∀ᶠ z in 𝓝 a, f z = (z - a) ^ (0 + 1) * dslope f a z := by
    filter_upwards [] with z
    simpa only [pow_one, smul_eq_mul, hz, sub_zero] using (sub_smul_dslope f a z).symm
  have hlog := logDeriv_eventuallyEq_of_factor hg hgn hfac
  have hregular : logDeriv (dslope f a) =ᶠ[𝓝[≠] a] R := by
    filter_upwards [hlog, heq] with z hz₁ hz₂
    simp only [Nat.cast_zero, zero_add] at hz₁
    exact add_left_cancel (hz₁.symm.trans hz₂)
  have hc : ContinuousAt (logDeriv (dslope f a)) a :=
    (hg.deriv.div hg hgn).continuousAt
  have hvalue : logDeriv (dslope f a) a = R a :=
    tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hR.tendsto.mono_left nhdsWithin_le_nhds).congr' hregular.symm)
  have hjet := _root_.HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div
    hp.analyticAt 1
  have hdg : deriv (dslope f a) a = deriv (deriv f) a / 2 := by
    simpa only [iteratedDeriv_succ (n := 1), iteratedDeriv_one, Nat.cast_one,
      one_add_one_eq_two] using hjet
  rw [logDeriv_apply, dslope_same, hdg] at hvalue
  calc
    deriv (deriv f) a / deriv f a = 2 * (deriv (deriv f) a / 2 / deriv f a) := by ring
    _ = 2 * R a := by rw [hvalue]

end

end RHTower.DeBruijn
