import GaloisForLFunctions.RHTower.LiClockThetaReciprocalPoleCancellation
import GaloisForLFunctions.RHTower.LiClockPairedEtaFiniteFilledDeflation
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMoments
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure

/-!
# The paired-eta representation of the reciprocal logarithm beyond Euler convergence

Let `L(s) = ∫_S e^{-st} dt` over the full logarithmic union
`S = ⋃_n (log(2n+1), log(2n+2)]` and `L₁(v) = ∫_0^{log 2} e^{-vt} dt` its first interval.  With
`η(s) = s L(s)` and `1 - 2^{1-s} = (s-1) L₁(s-1)`:

* (A16) `ξ(s) = π s Γ_ℝ(s+2) L(s)/L₁(s-1)` for every real `s > 0`, including the filled point
  `s = 1`, with all four factors positive;
* (A17) `log ξ(s) = log π + log s + log Γ_ℝ(s+2) + log L(s) - log L₁(s-1)` for real `s > 0`; in
  particular along `s(u) = 1/2 + 1/(p-u)` for every `p > 1` and `u` near `0`.
-/

open Set Filter Topology Complex MeasureTheory RiemannGaussian

noncomputable section

namespace RHTower

local notation "L" => pairedEtaLaplacePartition
local notation "L₁" => pairedEtaFiniteLaplacePartition 1

/-- The first interval `L₁(v) = ∫_0^{log 2} e^{-vt} dt` is real and positive at real `v`. -/
theorem pairedEtaFiniteLaplacePartition_one_ofReal (v : ℝ) :
    L₁ (v : ℂ) = ((∫ t in (0 : ℝ)..Real.log 2, Real.exp (-v * t) : ℝ) : ℂ) ∧
      0 < ∫ t in (0 : ℝ)..Real.log 2, Real.exp (-v * t) := by
  refine ⟨?_, intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-v * t)).intervalIntegrable _ _)
    (fun t _ => Real.exp_pos _) (Real.log_pos (by norm_num))⟩
  unfold pairedEtaFiniteLaplacePartition
  rw [Finset.sum_range_one, ← intervalIntegral.integral_ofReal]
  simp only [Nat.cast_zero, mul_zero, zero_add, Real.log_one]
  norm_num

/-- `L(s)` is real and positive at real `s > 0`. -/
theorem pairedEtaLaplacePartition_ofReal {s : ℝ} (hs : 0 < s) :
    L (s : ℂ) = (pairedEtaTiltedCosineMoment s 0 : ℂ) ∧ 0 < pairedEtaTiltedCosineMoment s 0 := by
  have hre := integral_exp_neg_mul_pairedEtaLogMeasure_re s 0 hs
  have him := integral_exp_neg_mul_pairedEtaLogMeasure_im s 0 hs
  have hL := integral_exp_neg_mul_pairedEtaLogMeasure_eq_laplacePartition (s := (s : ℂ))
    (by simpa using hs)
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hre him
  rw [hL] at hre him
  refine ⟨Complex.ext (by simpa using hre) ?_, pairedEtaTiltedCosineMoment_zero_pos s hs⟩
  rw [him]
  simp [pairedEtaTiltedSineMoment]

/-- `Γ_ℝ(s)` is real and positive at real `s > 0`. -/
theorem Gammaℝ_ofReal_pos {s : ℝ} (hs : 0 < s) :
    Complex.Gammaℝ (s : ℂ) = ((Real.pi ^ (-s / 2) * Real.Gamma (s / 2) : ℝ) : ℂ) ∧
      0 < Real.pi ^ (-s / 2) * Real.Gamma (s / 2) := by
  refine ⟨?_, mul_pos (Real.rpow_pos_of_pos Real.pi_pos _) (Real.Gamma_pos_of_pos (by linarith))⟩
  rw [Complex.Gammaℝ_def, Complex.ofReal_mul, Complex.ofReal_cpow Real.pi_pos.le,
    ← Complex.Gamma_ofReal]
  push_cast
  ring_nf

/-- **(A16)** `ξ(s) = π s Γ_ℝ(s+2) L(s)/L₁(s-1)` at every regular point `Re s > 0`, `s ≠ 1`. -/
theorem xi_eq_pairedEta_of_ne_one {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hL1 : L₁ (s - 1) ≠ 0) :
    xi s = Real.pi * s * Complex.Gammaℝ (s + 2) * L s / L₁ (s - 1) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.2 hs1
  have heta := pairedEtaCore_eq_mul_laplacePartition hs
  have hfac := pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1
  have hshift := liClockPairedEtaFactor_eq_shift_mul_firstLaplace s
  have hU : zetaResidueUnit s = (s - 1) * riemannZeta s :=
    (zetaResidueUnit_eventuallyEq hs1).self_of_nhds
  rw [xi_eq_half_mul_Gammaℝ_mul_zetaResidueUnit hs, hU, Complex.Gammaℝ_add_two hs0]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold pairedEtaFactor at hshift
  rw [hshift] at hfac
  rw [eq_div_iff hL1]
  have key : (s - 1) * L₁ (s - 1) * riemannZeta s = s * L s := by rw [← hfac, heta]
  rw [show (Real.pi : ℂ) * s * (Complex.Gammaℝ s * s / 2 / Real.pi) * L s =
    s * s / 2 * Complex.Gammaℝ s * L s by field_simp]
  linear_combination (s / 2 * Complex.Gammaℝ s) * key

/-- **(A16)** `ξ(s) = π s Γ_ℝ(s+2) L(s)/L₁(s-1)` for every real `s > 0`, including the filled
point `s = 1`. -/
theorem xi_ofReal_eq_pairedEta {s : ℝ} (hs : 0 < s) :
    xi (s : ℂ) = Real.pi * s * Complex.Gammaℝ (s + 2) * L s / L₁ (s - 1) := by
  have hL1real : ∀ v : ℝ, L₁ (v : ℂ) ≠ 0 := fun v => by
    rw [(pairedEtaFiniteLaplacePartition_one_ofReal v).1]
    exact_mod_cast (pairedEtaFiniteLaplacePartition_one_ofReal v).2.ne'
  rcases ne_or_eq s 1 with hs1 | rfl
  · refine xi_eq_pairedEta_of_ne_one (by simpa using hs) (by exact_mod_cast hs1) ?_
    rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring]
    exact hL1real _
  · set R : ℂ → ℂ := fun z => Real.pi * z * Complex.Gammaℝ (z + 2) * L z / L₁ (z - 1) with hRdef
    have hL10 : L₁ ((1 : ℂ) - 1) ≠ 0 := by rw [sub_self]; exact_mod_cast hL1real 0
    have hGamma : ContinuousAt (fun z : ℂ => Complex.Gammaℝ (z + 2)) 1 := by
      have hd : DifferentiableAt ℂ Complex.Gamma (((1 : ℂ) + 2) / 2) :=
        Complex.differentiableAt_Gamma _ fun m hm => by
          have := congrArg Complex.re hm
          norm_num at this
          linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
      have hcont : ContinuousAt (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + 2) / 2) *
          Complex.Gamma ((z + 2) / 2)) 1 := by
        refine ContinuousAt.mul ?_ (hd.continuousAt.comp (x := (1 : ℂ))
          (f := fun z : ℂ => (z + 2) / 2) (by fun_prop))
        exact (continuous_const.cpow (by fun_prop) fun _ => Or.inl (by
          exact_mod_cast Real.pi_pos)).continuousAt
      refine hcont.congr (Eventually.of_forall fun z => ?_)
      simp only [Complex.Gammaℝ_def]
    have hRc : ContinuousAt R 1 := by
      refine ((((continuousAt_const.mul continuousAt_id).mul hGamma).mul
        (analyticAt_pairedEtaLaplacePartition (by norm_num)).continuousAt).div
        ((analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 _).continuousAt.comp
          (by fun_prop : ContinuousAt (fun z : ℂ => z - 1) 1)) hL10)
    have hev : xi =ᶠ[𝓝[≠] (1 : ℂ)] R := by
      have hre : ∀ᶠ z in 𝓝 (1 : ℂ), 0 < z.re :=
        continuousAt_const.eventually_lt Complex.continuous_re.continuousAt
          (by norm_num : (0 : ℝ) < (1 : ℂ).re)
      have hL1ev : ∀ᶠ z in 𝓝 (1 : ℂ), L₁ (z - 1) ≠ 0 :=
        ((analyticAt_liClockPairedEtaFiniteLaplacePartition_entire 1 _).continuousAt.comp
          (by fun_prop : ContinuousAt (fun z : ℂ => z - 1) 1)).eventually_ne hL10
      filter_upwards [nhdsWithin_le_nhds hre, nhdsWithin_le_nhds hL1ev, self_mem_nhdsWithin]
        with z hz hz1 hzne
      exact xi_eq_pairedEta_of_ne_one hz hzne hz1
    have h1 := (xi_differentiable.continuous.continuousAt (x := (1 : ℂ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
    have h2 := hRc.tendsto.mono_left (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
    have := tendsto_nhds_unique (h1.congr' hev) h2
    simpa [hRdef] using this

/-- **(A17)** For real `s > 0`,
`log ξ(s) = log π + log s + log Γ_ℝ(s+2) + log L(s) - log L₁(s-1)`, all factors positive. -/
theorem log_xi_ofReal_eq_pairedEta {s : ℝ} (hs : 0 < s) :
    0 < (xi (s : ℂ)).re ∧ (xi (s : ℂ)).im = 0 ∧
      Real.log (xi (s : ℂ)).re = Real.log Real.pi + Real.log s +
        Real.log (Complex.Gammaℝ ((s : ℂ) + 2)).re + Real.log (L (s : ℂ)).re -
          Real.log (L₁ ((s : ℂ) - 1)).re := by
  obtain ⟨hLeq, hLpos⟩ := pairedEtaLaplacePartition_ofReal hs
  obtain ⟨hL1eq, hL1pos⟩ := pairedEtaFiniteLaplacePartition_one_ofReal (s - 1)
  obtain ⟨hGeq, hGpos⟩ := Gammaℝ_ofReal_pos (show 0 < s + 2 by linarith)
  have hG' : Complex.Gammaℝ ((s : ℂ) + 2) = Complex.Gammaℝ ((s + 2 : ℝ) : ℂ) := by push_cast; rfl
  have hL1' : L₁ ((s : ℂ) - 1) = L₁ ((s - 1 : ℝ) : ℂ) := by push_cast; rfl
  have hxi := xi_ofReal_eq_pairedEta hs
  rw [hG', hGeq, hLeq, hL1', hL1eq] at hxi
  set A := Real.pi ^ (-(s + 2) / 2) * Real.Gamma ((s + 2) / 2)
  set B := pairedEtaTiltedCosineMoment s 0
  set C := ∫ t in (0 : ℝ)..Real.log 2, Real.exp (-(s - 1) * t)
  have hreal : xi (s : ℂ) = ((Real.pi * s * A * B / C : ℝ) : ℂ) := by rw [hxi]; push_cast; ring
  have hpos : 0 < Real.pi * s * A * B / C := by
    have := Real.pi_pos; positivity
  rw [hreal, Complex.ofReal_re, Complex.ofReal_im, hG', hGeq, Complex.ofReal_re, hLeq,
    Complex.ofReal_re, hL1', hL1eq, Complex.ofReal_re]
  refine ⟨hpos, rfl, ?_⟩
  rw [Real.log_div (by positivity) hL1pos.ne', Real.log_mul (by positivity) hLpos.ne',
    Real.log_mul (by positivity) hGpos.ne', Real.log_mul Real.pi_pos.ne' hs.ne']

/-- **(A17)** Along `s(u) = 1/2 + 1/(p-u)`, `p > 1`, `|u| < p - 1`, the reciprocal logarithm is the
sum of the five local logarithms, each normalized at `u = 0`. -/
theorem log_xi_liClockReciprocalPoleArgument_eq_pairedEta {p u : ℝ} (hup : u < p) :
    Real.log (xi (liClockReciprocalPoleArgument p u : ℂ)).re =
      Real.log Real.pi + Real.log (liClockReciprocalPoleArgument p u) +
        Real.log (Complex.Gammaℝ ((liClockReciprocalPoleArgument p u : ℂ) + 2)).re +
        Real.log (L (liClockReciprocalPoleArgument p u : ℂ)).re -
        Real.log (L₁ ((liClockReciprocalPoleArgument p u : ℂ) - 1)).re := by
  have hpos : 0 < liClockReciprocalPoleArgument p u := by
    unfold liClockReciprocalPoleArgument
    have : 0 < p - u := by linarith
    positivity
  exact (log_xi_ofReal_eq_pairedEta hpos).2.2

end RHTower
