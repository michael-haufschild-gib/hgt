import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality
import GaloisForLFunctions.RHTower.SuzukiDonoghueHerglotzTransform
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Source-only second jet of Suzuki's Fourier--Livšic quotient

This lightweight module isolates the exact second disk jet of a reflected Fourier pair.  It has no
Xi target, prime--Gamma calibration, or convergence dependency: those are consumers of this finite
source identity.
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

theorem deriv_suzukiUpperCayleyInv_source {w : ℂ} (hw : w ≠ 1) :
    deriv GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w =
      2 * I / (1 - w) ^ (2 : ℕ) := by
  have hfun :
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv =
        GaloisForLFunctions.RHTower.herglotzOfCayley := by
    funext z
    rw [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv,
      GaloisForLFunctions.RHTower.herglotzOfCayley]
    ring
  rw [hfun,
    (GaloisForLFunctions.RHTower.hasDerivAt_herglotzOfCayley hw).deriv]

@[simp] theorem deriv_suzukiUpperCayleyInv_zero :
    deriv GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 = 2 * I := by
  rw [deriv_suzukiUpperCayleyInv_source (by norm_num)]
  norm_num

theorem iteratedDeriv_two_suzukiUpperCayleyInv_zero :
    iteratedDeriv 2 GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 = 4 * I := by
  have hbase : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)
  have hden := hbase.pow 2
  have hne : ((1 : ℂ) - 0) ^ (2 : ℕ) ≠ 0 := by norm_num
  have hrhs := (hasDerivAt_const 0 (2 * I)).div hden hne
  have heq : deriv GaloisForLFunctions.RHTower.suzukiUpperCayleyInv =ᶠ[nhds 0]
      fun w : ℂ => 2 * I / (1 - w) ^ (2 : ℕ) := by
    filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1)] with w hw
    exact deriv_suzukiUpperCayleyInv_source hw
  rw [show
    iteratedDeriv 2 GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 =
      deriv (iteratedDeriv 1
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 by
      simpa using congrFun
        (iteratedDeriv_succ
          (n := 1)
          (f := GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)) 0]
  simp only [iteratedDeriv_one]
  have hderiv := (hrhs.congr_of_eventuallyEq heq).deriv
  rw [hderiv]
  norm_num
  ring

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
          F (-I) ^ (2 : ℕ) := by
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
  have hR : ContDiffAt ℂ 2 R 0 := hnum.div hden hden0
  have hzDeriv : deriv zfun 0 = 2 * I := by
    exact deriv_suzukiUpperCayleyInv_zero
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
    have hcomp := houter.hasDerivAt.comp 0 hzHas.neg
    rw [hz0] at hcomp
    exact hcomp
  have hRHas : HasDerivAt R
      ((deriv F I * (2 * I) * F (-I) -
          F I * (deriv F (-I) * (-(2 * I)))) / F (-I) ^ (2 : ℕ)) 0 := by
    have hquot := hnumHas.div hdenHas hden0
    rw [hz0] at hquot
    exact hquot
  have hRDeriv :
      deriv R 0 =
        2 * I * (deriv F I * F (-I) + F I * deriv F (-I)) /
          F (-I) ^ (2 : ℕ) := by
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

end

end RHTower
