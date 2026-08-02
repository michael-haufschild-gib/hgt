import GaloisForLFunctions.RHTower.SuzukiXiSecondDefectJet

/-!
# Suzuki source equation for the second Xi defect jet

For Suzuki's reflected Fourier pair, disk conjugation removes the universal Cayley factor exactly:

`Theta_F(CayleyInv(w)) = w * F(CayleyInv(w)) / F(-CayleyInv(w))`.

Its second disk jet is therefore the explicit endpoint logarithmic slope

`4 i * (F'(i) F(-i) + F(i) F'(-i)) / F(-i)^2`.

Combined with `SuzukiXiSecondDefectJet`, this turns Xi identification into a source-side equation:
the endpoint logarithmic slope must converge to the strictly negative safe-Euler prime–Gamma
curvature.  First-jet parity matching alone cannot satisfy this stronger identification gate.
-/

open Complex Filter

namespace RHTower

noncomputable section

theorem suzukiFourierLivsic_disk_eq
    {F : ℂ → ℂ} {w : ℂ} (hw : w ≠ 1) :
    GaloisForLFunctions.RHTower.suzukiLivsicQuotient
        (GaloisForLFunctions.RHTower.suzukiFourierNumerator F)
        (GaloisForLFunctions.RHTower.suzukiFourierDenominator F)
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w) =
      w * (F (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w) /
        F (-GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) := by
  let z := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w
  have hzw : (z - I) / (z + I) = w := by
    dsimp only [z]
    rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
    field_simp [sub_ne_zero.mpr (Ne.symm hw), I_ne_zero]
    ring
  rw [GaloisForLFunctions.RHTower.suzukiLivsicQuotient,
    GaloisForLFunctions.RHTower.suzukiFourierNumerator,
    GaloisForLFunctions.RHTower.suzukiFourierDenominator]
  change ((z - I) * F z) / ((z + I) * F (-z)) =
    w * (F z / F (-z))
  rw [mul_div_mul_comm, hzw]

theorem iteratedDeriv_two_suzukiFourierLivsic_disk_zero
    {F : ℂ → ℂ}
    (hFi : ContDiffAt ℂ 2 F I)
    (hFni : ContDiffAt ℂ 2 F (-I))
    (hFni0 : F (-I) ≠ 0) :
    iteratedDeriv 2
      (fun w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator F)
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator F)
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      4 * I *
        (deriv F I * F (-I) + F I * deriv F (-I)) /
          F (-I) ^ 2 := by
  let zfun := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv
  let R : ℂ → ℂ := fun w => F (zfun w) / F (-zfun w)
  have hz0 : zfun 0 = I := by
    simp [zfun, GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
  have hz : ContDiffAt ℂ 2 zfun 0 := by
    change ContDiffAt ℂ 2 (fun w : ℂ => I * ((1 + w) / (1 - w))) 0
    fun_prop (disch := norm_num)
  have hFi' : ContDiffAt ℂ 2 F (zfun 0) := by
    rw [hz0]
    exact hFi
  have hFni' : ContDiffAt ℂ 2 F (-zfun 0) := by
    rw [hz0]
    exact hFni
  have hnum : ContDiffAt ℂ 2 (fun w => F (zfun w)) 0 :=
    hFi'.comp 0 hz
  have hden : ContDiffAt ℂ 2 (fun w => F (-zfun w)) 0 :=
    hFni'.comp 0 hz.neg
  have hden0 : F (-zfun 0) ≠ 0 := by
    rw [hz0]
    exact hFni0
  have hR : ContDiffAt ℂ 2 R 0 := by
    exact hnum.div hden hden0
  have hzDeriv : deriv zfun 0 = 2 * I := by
    dsimp only [zfun]
    convert deriv_suzukiUpperCayleyInv (w := 0) (by norm_num) using 1 <;>
      norm_num
  have hzHas : HasDerivAt zfun (2 * I) 0 := by
    rw [← hzDeriv]
    exact (hz.differentiableAt (by norm_num)).hasDerivAt
  have hnumHas : HasDerivAt (fun w => F (zfun w))
      (deriv F I * (2 * I)) 0 := by
    have houter := hFi'.differentiableAt (by norm_num)
    have hcomp := houter.hasDerivAt.comp 0 hzHas
    rw [hz0] at hcomp
    exact hcomp
  have hdenHas : HasDerivAt (fun w => F (-zfun w))
      (deriv F (-I) * (-(2 * I))) 0 := by
    have houter := hFni'.differentiableAt (by norm_num)
    have hneg := hzHas.neg
    have hcomp := houter.hasDerivAt.comp 0 hneg
    rw [hz0] at hcomp
    exact hcomp
  have hRHas : HasDerivAt R
      ((deriv F I * (2 * I) * F (-I) -
          F I * (deriv F (-I) * (-(2 * I)))) / F (-I) ^ 2) 0 := by
    have hquot := hnumHas.div hdenHas hden0
    rw [hz0] at hquot
    exact hquot
  have hRDeriv :
      deriv R 0 =
        2 * I * (deriv F I * F (-I) + F I * deriv F (-I)) /
          F (-I) ^ 2 := by
    rw [hRHas.deriv]
    ring
  have heq :
      (fun w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator F)
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator F)
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) =ᶠ[nhds 0]
        fun w => w * R w := by
    filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)] with w hw
    exact suzukiFourierLivsic_disk_eq hw
  rw [heq.iteratedDeriv_eq 2]
  have hid : ContDiffAt ℂ 2 (fun w : ℂ => w) 0 := by fun_prop
  have hmul := iteratedDeriv_mul hid hR
  change iteratedDeriv 2 (fun w => w * R w) 0 = _ at hmul
  have hid0 : iteratedDeriv 0 (fun w : ℂ => w) 0 = 0 := rfl
  have hid1 : iteratedDeriv 1 (fun w : ℂ => w) 0 = 1 := by
    rw [iteratedDeriv_one]
    simpa using (hasDerivAt_id (0 : ℂ)).deriv
  have hid2 : iteratedDeriv 2 (fun w : ℂ => w) 0 = 0 := by
    change iteratedDeriv 2 id 0 = 0
    rw [iteratedDeriv_id]
    norm_num
  rw [hmul]
  norm_num [Finset.sum_range_succ, hid0, hid1, hid2,
    iteratedDeriv_one, hRDeriv]
  ring

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
        F j (-I) ^ 2) l
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
