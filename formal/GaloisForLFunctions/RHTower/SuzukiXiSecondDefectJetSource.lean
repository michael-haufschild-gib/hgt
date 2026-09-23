import GaloisForLFunctions.RHTower.SuzukiFourierLivsicSecondJet
import GaloisForLFunctions.RHTower.SuzukiXiSecondDefectJet

/-!
# Xi target transport for Suzuki's source-only second defect jet

`SuzukiFourierLivsicSecondJet` contains the finite reflected-Fourier identity without any Xi
dependencies. This consumer adds compact-open derivative transport and identifies its limit with
strictly negative prime--Gamma calibration.
-/

open Complex Filter

namespace RHTower

noncomputable section

theorem secondJet_tendsto_of_locallyUniform
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (theta : ι → ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn theta
      (xiHedenmalmLivsicTarget ∘
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)
      l (Metric.ball 0 1))
    (hcont : ∀ᶠ j in l, ContDiffOn ℂ 2 (theta j) (Metric.ball 0 1)) :
    Tendsto (fun j => iteratedDeriv 2 (theta j) 0) l
      (nhds (primeArchSuzukiSecondDefectCalibration : ℂ)) := by
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hdiff : ∀ᶠ j in l,
      DifferentiableOn ℂ (theta j) (Metric.ball 0 1) := by
    filter_upwards [hcont] with j hj
    exact hj.differentiableOn (by norm_num)
  have hconvOne := hconv.deriv hdiff hopen
  have hdiffOne : ∀ᶠ j in l,
      DifferentiableOn ℂ (deriv (theta j)) (Metric.ball 0 1) := by
    filter_upwards [hcont] with j hj
    have hd : ContDiffOn ℂ 1 (deriv (theta j)) (Metric.ball 0 1) :=
      hj.deriv_of_isOpen hopen (m := 1) (by norm_num)
    exact hd.differentiableOn (by norm_num)
  have hconvTwo := hconvOne.deriv hdiffOne hopen
  have hpoint := hconvTwo.tendsto_at
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  simp only [Function.comp_apply] at hpoint
  have hsource :
      (fun j => iteratedDeriv 2 (theta j) 0) =
        fun j => deriv (deriv (theta j)) 0 := by
    funext j
    rw [show iteratedDeriv 2 (theta j) 0 =
      deriv (iteratedDeriv 1 (theta j)) 0 by
        simpa using congrFun
          (iteratedDeriv_succ (n := 1) (f := theta j)) 0,
      iteratedDeriv_one]
  have htarget :
      iteratedDeriv 2
          (xiHedenmalmLivsicTarget ∘
            GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 =
        deriv
          (deriv (xiHedenmalmLivsicTarget ∘
            GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)) 0 := by
    rw [show iteratedDeriv 2
        (xiHedenmalmLivsicTarget ∘
          GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 =
      deriv (iteratedDeriv 1
        (xiHedenmalmLivsicTarget ∘
          GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)) 0 by
        simpa using congrFun
          (iteratedDeriv_succ (n := 1)
            (f := xiHedenmalmLivsicTarget ∘
              GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)) 0,
      iteratedDeriv_one]
  rw [← hsource] at hpoint
  rw [← htarget,
    iteratedDeriv_two_xiHedenmalmLivsicTarget_disk_zero_eq_primeArch] at hpoint
  exact hpoint

/-- Exact second-jet source obligation for every Xi-identifying Suzuki Fourier family. -/
theorem suzukiFourier_endpointSecondDefect_tendsto_primeArch
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (F : ι → ℂ → ℂ)
    (hconv : TendstoLocallyUniformlyOn
      (fun j w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator (F j))
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator (F j))
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w))
      (xiHedenmalmLivsicTarget ∘
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)
      l (Metric.ball 0 1))
    (hcont : ∀ᶠ j in l, ContDiffOn ℂ 2
      (fun w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator (F j))
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator (F j))
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w))
      (Metric.ball 0 1))
    (hsource : ∀ᶠ j in l,
      ContDiffAt ℂ 2 (F j) I ∧ ContDiffAt ℂ 2 (F j) (-I) ∧
        F j (-I) ≠ 0) :
    Tendsto (fun j =>
      4 * I *
        (deriv (F j) I * F j (-I) +
          F j I * deriv (F j) (-I)) /
        F j (-I) ^ (2 : ℕ)) l
      (nhds (primeArchSuzukiSecondDefectCalibration : ℂ)) := by
  have hjet := secondJet_tendsto_of_locallyUniform
    (theta := fun j w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient
        (GaloisForLFunctions.RHTower.suzukiFourierNumerator (F j))
        (GaloisForLFunctions.RHTower.suzukiFourierDenominator (F j))
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w))
    hconv hcont
  refine hjet.congr' ?_
  filter_upwards [hsource] with j hj
  exact iteratedDeriv_two_suzukiFourierLivsic_disk_zero
    hj.1 hj.2.1 hj.2.2

end

end RHTower
