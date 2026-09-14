import GaloisForLFunctions.RHTower.SuzukiAllAngleCarrierSchurSecondJet
import GaloisForLFunctions.RHTower.SuzukiTaV2LivsicCharacteristic
import GaloisForLFunctions.RHTower.SuzukiCoalescingHalfPlaneNormality
import GaloisForLFunctions.RHTower.SuzukiFourierLivsicSecondJet

/-!
# Movable Suzuki Schur covariant second jet

Output recentering at every positive imaginary anchor upgrades endpoint-only Suzuki torque control
to an exact Schwarz--Pick two-jet law along symmetric Mellin-shift coordinates.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- Exact norm of the scalar Schur defect inside the open disk. -/
theorem norm_suzukiSchurDefect_eq_of_norm_lt_one
    {alpha : ℂ} (halpha : ‖alpha‖ < 1) :
    ‖1 - (starRingEnd ℂ) alpha * alpha‖ = 1 - ‖alpha‖ ^ 2 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  norm_cast
  rw [Real.norm_eq_abs, abs_of_pos]
  nlinarith [norm_nonneg alpha]

/-- Disk automorphism sending `alpha` to zero. -/
def suzukiDiskOutputRecenter (alpha z : ℂ) : ℂ :=
  (z - alpha) / (1 - (starRingEnd ℂ) alpha * z)

/-- Output-recentered movable disk chart of an upper-half-plane function. -/
def suzukiMovableSchurRecenter (theta : ℂ → ℂ) (c : ℝ) (w : ℂ) : ℂ :=
  let z := suzukiCoalescingCayleyInv c w
  let alpha := theta ((c : ℂ) * I)
  suzukiDiskOutputRecenter alpha (theta z)

theorem deriv_suzukiDiskOutputRecenter
    {alpha z : ℂ} (hden : 1 - (starRingEnd ℂ) alpha * z ≠ 0) :
    deriv (suzukiDiskOutputRecenter alpha) z =
      (1 - (starRingEnd ℂ) alpha * alpha) /
        (1 - (starRingEnd ℂ) alpha * z) ^ 2 := by
  have hnum : HasDerivAt (fun u : ℂ => u - alpha) 1 z := by
    simpa only [id_eq] using (hasDerivAt_id z).sub_const alpha
  have hden' : HasDerivAt
      (fun u : ℂ => 1 - (starRingEnd ℂ) alpha * u)
      (-((starRingEnd ℂ) alpha)) z := by
    simpa only [sub_eq_add_neg, neg_mul] using
      (hasDerivAt_const_mul (x := z) (-((starRingEnd ℂ) alpha))).const_add 1
  change deriv (fun u : ℂ => (u - alpha) /
    (1 - (starRingEnd ℂ) alpha * u)) z = _
  have hd : deriv (fun u : ℂ => (u - alpha) /
      (1 - (starRingEnd ℂ) alpha * u)) z =
      (1 * (1 - (starRingEnd ℂ) alpha * z) -
        (z - alpha) * (-((starRingEnd ℂ) alpha))) /
          (1 - (starRingEnd ℂ) alpha * z) ^ 2 := by
    have h := (hnum.div hden' hden).deriv
    have hfun :
        (fun u : ℂ => (u - alpha) / (1 - (starRingEnd ℂ) alpha * u)) =
          (fun u : ℂ => u - alpha) /
            (fun u : ℂ => 1 - (starRingEnd ℂ) alpha * u) := by
      funext u
      rfl
    rw [hfun]
    exact h
  rw [hd]
  field_simp [hden]
  ring

theorem deriv_suzukiDiskOutputRecenter_self
    {alpha : ℂ} (halpha : ‖alpha‖ < 1) :
    deriv (suzukiDiskOutputRecenter alpha) alpha =
      (1 - (starRingEnd ℂ) alpha * alpha)⁻¹ := by
  have hdelta : 1 - (starRingEnd ℂ) alpha * alpha ≠ 0 := by
    apply sub_ne_zero.mpr
    rw [← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast ne_of_gt (show Complex.normSq alpha < 1 by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg alpha])
  rw [deriv_suzukiDiskOutputRecenter hdelta]
  field_simp [hdelta]

theorem iteratedDeriv_two_suzukiDiskOutputRecenter_self
    {alpha : ℂ} (halpha : ‖alpha‖ < 1) :
    iteratedDeriv 2 (suzukiDiskOutputRecenter alpha) alpha =
      2 * (starRingEnd ℂ) alpha /
        (1 - (starRingEnd ℂ) alpha * alpha) ^ 2 := by
  let delta : ℂ := 1 - (starRingEnd ℂ) alpha * alpha
  let den : ℂ → ℂ := fun z => 1 - (starRingEnd ℂ) alpha * z
  have hdelta : delta ≠ 0 := by
    dsimp only [delta]
    apply sub_ne_zero.mpr
    rw [← Complex.normSq_eq_conj_mul_self]
    exact_mod_cast ne_of_gt (show Complex.normSq alpha < 1 by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg alpha])
  have hdenAt : HasDerivAt den (-((starRingEnd ℂ) alpha)) alpha := by
    dsimp only [den]
    simpa only [sub_eq_add_neg, neg_mul] using
      (hasDerivAt_const_mul (x := alpha) (-((starRingEnd ℂ) alpha))).const_add 1
  have hrhs : HasDerivAt (fun z => delta / den z ^ 2)
      (2 * (starRingEnd ℂ) alpha / delta ^ 2) alpha := by
    have hq := (hasDerivAt_const alpha delta).div (hdenAt.pow 2) (by
      simpa [den, delta] using pow_ne_zero 2 hdelta)
    change HasDerivAt (fun z => delta / den z ^ 2) _ alpha at hq
    norm_num at hq
    change HasDerivAt (fun z => delta / den z ^ 2)
      (delta * (2 * delta * (starRingEnd ℂ) alpha) / (delta ^ 2) ^ 2) alpha at hq
    have hcoeff : delta * (2 * delta * (starRingEnd ℂ) alpha) / (delta ^ 2) ^ 2 =
        2 * (starRingEnd ℂ) alpha / delta ^ 2 := by
      field_simp [hdelta]
    rw [hcoeff] at hq
    exact hq
  have hdenCont : ContinuousAt den alpha := hdenAt.continuousAt
  have heq : deriv (suzukiDiskOutputRecenter alpha) =ᶠ[nhds alpha]
      fun z => delta / den z ^ 2 := by
    filter_upwards [hdenCont.eventually_ne (by simpa [den, delta] using hdelta)] with z hz
    exact deriv_suzukiDiskOutputRecenter hz
  rw [show iteratedDeriv 2 (suzukiDiskOutputRecenter alpha) alpha =
      deriv (iteratedDeriv 1 (suzukiDiskOutputRecenter alpha)) alpha by
        simpa using congrFun
          (iteratedDeriv_succ (n := 1) (f := suzukiDiskOutputRecenter alpha)) alpha]
  simp only [iteratedDeriv_one]
  exact (hrhs.congr_of_eventuallyEq heq).deriv

theorem iteratedDeriv_two_suzukiCoalescingCayleyInv_zero (c : ℝ) :
    iteratedDeriv 2 (suzukiCoalescingCayleyInv c) 0 = 4 * (c : ℂ) * I := by
  change iteratedDeriv 2
    (fun w : ℂ => (c : ℂ) *
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w) 0 = _
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_two_suzukiUpperCayleyInv_zero]
  ring

theorem deriv_suzukiMovableSchurRecenter_zero
    {theta : ℂ → ℂ} {c : ℝ}
    (htheta : DifferentiableAt ℂ theta ((c : ℂ) * I))
    (halpha : ‖theta ((c : ℂ) * I)‖ < 1) :
    deriv (suzukiMovableSchurRecenter theta c) 0 =
      (2 * (c : ℂ) * I * deriv theta ((c : ℂ) * I)) /
        (1 - (starRingEnd ℂ) (theta ((c : ℂ) * I)) *
          theta ((c : ℂ) * I)) := by
  let alpha := theta ((c : ℂ) * I)
  let zfun := suzukiCoalescingCayleyInv c
  have hz : HasDerivAt zfun (2 * (c : ℂ) * I) 0 :=
    hasDerivAt_suzukiCoalescingCayleyInv_zero c
  have hz0 : zfun 0 = (c : ℂ) * I := by
    exact suzukiCoalescingCayleyInv_zero c
  have htheta' : DifferentiableAt ℂ theta (zfun 0) := by
    rw [hz0]
    exact htheta
  have hthetaComp : HasDerivAt (theta ∘ zfun)
      (deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)) 0 := by
    have h := htheta'.hasDerivAt.comp 0 hz
    simpa only [hz0] using h
  have hout : HasDerivAt (suzukiDiskOutputRecenter alpha)
      (1 - (starRingEnd ℂ) alpha * alpha)⁻¹ alpha := by
    rw [← deriv_suzukiDiskOutputRecenter_self halpha]
    have hdelta : 1 - (starRingEnd ℂ) alpha * alpha ≠ 0 := by
      apply sub_ne_zero.mpr
      rw [← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast ne_of_gt (show Complex.normSq alpha < 1 by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg alpha])
    have hdiff : DifferentiableAt ℂ (suzukiDiskOutputRecenter alpha) alpha := by
      change DifferentiableAt ℂ (fun z : ℂ => (z - alpha) /
        (1 - (starRingEnd ℂ) alpha * z)) alpha
      fun_prop
    exact hdiff.hasDerivAt
  have hout' : HasDerivAt (suzukiDiskOutputRecenter alpha)
      (1 - (starRingEnd ℂ) alpha * alpha)⁻¹ (theta (zfun 0)) := by
    rw [hz0]
    exact hout
  have hcomp := hout'.comp 0 hthetaComp
  have hfun : suzukiMovableSchurRecenter theta c =
      (suzukiDiskOutputRecenter alpha) ∘ (theta ∘ zfun) := by
    funext w
    rfl
  rw [hfun, hcomp.deriv]
  dsimp only [alpha]
  ring

theorem iteratedDeriv_two_suzukiMovableSchurRecenter_zero
    {theta : ℂ → ℂ} {c : ℝ}
    (htheta : ContDiffAt ℂ 2 theta ((c : ℂ) * I))
    (halpha : ‖theta ((c : ℂ) * I)‖ < 1) :
    iteratedDeriv 2 (suzukiMovableSchurRecenter theta c) 0 =
      (2 * (starRingEnd ℂ) (theta ((c : ℂ) * I)) /
          (1 - (starRingEnd ℂ) (theta ((c : ℂ) * I)) *
            theta ((c : ℂ) * I)) ^ 2) *
          (deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)) ^ 2 +
        (1 - (starRingEnd ℂ) (theta ((c : ℂ) * I)) *
            theta ((c : ℂ) * I))⁻¹ *
          (iteratedDeriv 2 theta ((c : ℂ) * I) *
              (2 * (c : ℂ) * I) ^ 2 +
            deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)) := by
  let alpha := theta ((c : ℂ) * I)
  let zfun := suzukiCoalescingCayleyInv c
  let inner : ℂ → ℂ := theta ∘ zfun
  have hz0 : zfun 0 = (c : ℂ) * I := suzukiCoalescingCayleyInv_zero c
  have hz : ContDiffAt ℂ 2 zfun 0 := by
    dsimp only [zfun, suzukiCoalescingCayleyInv]
    change ContDiffAt ℂ 2
      (fun w : ℂ => (c : ℂ) * (I * ((1 + w) / (1 - w)))) 0
    fun_prop (disch := norm_num)
  have hinner : ContDiffAt ℂ 2 inner 0 := by
    have htheta' : ContDiffAt ℂ 2 theta (zfun 0) := by
      rw [hz0]
      exact htheta
    exact htheta'.comp 0 hz
  have hout : ContDiffAt ℂ 2 (suzukiDiskOutputRecenter alpha) alpha := by
    change ContDiffAt ℂ 2 (fun z : ℂ => (z - alpha) /
      (1 - (starRingEnd ℂ) alpha * z)) alpha
    have hdelta : 1 - (starRingEnd ℂ) alpha * alpha ≠ 0 := by
      apply sub_ne_zero.mpr
      rw [← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast ne_of_gt (show Complex.normSq alpha < 1 by
        rw [Complex.normSq_eq_norm_sq]
        nlinarith [norm_nonneg alpha])
    fun_prop
  have hinnerZero : inner 0 = alpha := by simp [inner, alpha, hz0]
  have hout' : ContDiffAt ℂ 2 (suzukiDiskOutputRecenter alpha) (inner 0) := by
    rw [hinnerZero]
    exact hout
  have houter := iteratedDeriv_comp_two
    (g := suzukiDiskOutputRecenter alpha) (f := inner) (x := 0) hout' hinner
  have htheta' : ContDiffAt ℂ 2 theta (zfun 0) := by
    rw [hz0]
    exact htheta
  have hinnerTwo := iteratedDeriv_comp_two
    (g := theta) (f := zfun) (x := 0) htheta' hz
  have hinnerOne : deriv inner 0 =
      deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I) := by
    have h := htheta'.differentiableAt (by norm_num) |>.hasDerivAt.comp 0
      (hasDerivAt_suzukiCoalescingCayleyInv_zero c)
    simpa only [inner, hz0] using h.deriv
  have hzTwo : iteratedDeriv 2 zfun 0 = 4 * (c : ℂ) * I := by
    exact iteratedDeriv_two_suzukiCoalescingCayleyInv_zero c
  have hzOne : deriv zfun 0 = 2 * (c : ℂ) * I :=
    (hasDerivAt_suzukiCoalescingCayleyInv_zero c).deriv
  change iteratedDeriv 2
    ((suzukiDiskOutputRecenter alpha) ∘ inner) 0 = _
  rw [houter, hinnerZero,
    iteratedDeriv_two_suzukiDiskOutputRecenter_self halpha,
    deriv_suzukiDiskOutputRecenter_self halpha,
    hinnerOne, hinnerTwo, hz0, hzOne, hzTwo]

theorem norm_suzukiMovableSchurRecenter_secondJet_le_schurSlack
    {theta : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im})
    (hmap : ∀ z : ℂ, 0 < z.im → ‖theta z‖ < 1) :
    ‖iteratedDeriv 2 (suzukiMovableSchurRecenter theta c) 0‖ ≤
      2 * (1 - ‖deriv (suzukiMovableSchurRecenter theta c) 0‖ ^ 2) := by
  let alpha := theta ((c : ℂ) * I)
  let zfun := suzukiCoalescingCayleyInv c
  let f := suzukiMovableSchurRecenter theta c
  have halpha : ‖alpha‖ < 1 := by
    apply hmap
    simp [hc]
  have hf : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    have hzpos : 0 < (zfun w).im := suzukiCoalescingCayleyInv_im_pos hc hwlt
    have hz : DifferentiableAt ℂ zfun w := by
      dsimp only [zfun, suzukiCoalescingCayleyInv]
      change DifferentiableAt ℂ (fun v : ℂ => (c : ℂ) * (I * ((1 + v) / (1 - v)))) w
      have hw1 : w ≠ 1 := by
        intro heq
        rw [heq, norm_one] at hwlt
        exact (lt_irrefl 1) hwlt
      fun_prop (disch := exact sub_ne_zero.mpr (Ne.symm hw1))
    have ht : DifferentiableAt ℂ theta (zfun w) :=
      (htheta (zfun w) hzpos).differentiableAt
        (isOpen_lt continuous_const Complex.continuous_im |>.mem_nhds hzpos)
    have hcomp : DifferentiableAt ℂ (fun v => theta (zfun v)) w := ht.comp w hz
    have hden : 1 - (starRingEnd ℂ) alpha * theta (zfun w) ≠ 0 :=
      Bottcher.one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one
        halpha (hmap (zfun w) hzpos).le
    change DifferentiableWithinAt ℂ
      (fun v => (theta (zfun v) - alpha) /
        (1 - (starRingEnd ℂ) alpha * theta (zfun v))) (ball 0 1) w
    exact ((hcomp.sub_const alpha).div
      ((differentiableAt_const (c := (1 : ℂ))).sub
        (hcomp.const_mul ((starRingEnd ℂ) alpha))) hden).differentiableWithinAt
  have hf0 : f 0 = 0 := by
    simp [f, suzukiMovableSchurRecenter, suzukiDiskOutputRecenter,
      suzukiCoalescingCayleyInv_zero]
  have hfmap : MapsTo f (ball (0 : ℂ) 1) (closedBall 0 1) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hwlt : ‖w‖ < 1 := by simpa [mem_ball_zero_iff] using hw
    have hzpos : 0 < (zfun w).im := suzukiCoalescingCayleyInv_im_pos hc hwlt
    have hden : 1 - (starRingEnd ℂ) alpha * theta (zfun w) ≠ 0 :=
      Bottcher.one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one
        halpha (hmap (zfun w) hzpos).le
    change ‖(theta (zfun w) - alpha) /
      (1 - (starRingEnd ℂ) alpha * theta (zfun w))‖ ≤ 1
    exact GaloisForLFunctions.blaschke_schur alpha (theta (zfun w))
      halpha.le (hmap (zfun w) hzpos).le hden
  exact norm_iteratedDeriv_two_le_schurSlack_closed hf hf0 hfmap

/-- Movable Schwarz--Pick two-jet inequality in literal half-plane derivatives.  Unlike the
anchored endpoint estimate, this controls every positive imaginary height and retains the output
value needed for prime--polar cancellation under symmetric Mellin shifts. -/
theorem norm_suzukiMovableSchurCovariantSecondJet_le
    {theta : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im})
    (hmap : ∀ z : ℂ, 0 < z.im → ‖theta z‖ < 1) :
    ‖(2 * (starRingEnd ℂ) (theta ((c : ℂ) * I)) /
          (1 - (starRingEnd ℂ) (theta ((c : ℂ) * I)) *
            theta ((c : ℂ) * I)) ^ 2) *
          (deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)) ^ 2 +
        (1 - (starRingEnd ℂ) (theta ((c : ℂ) * I)) *
            theta ((c : ℂ) * I))⁻¹ *
          (iteratedDeriv 2 theta ((c : ℂ) * I) *
              (2 * (c : ℂ) * I) ^ 2 +
            deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I))‖ ≤
      2 * (1 -
        ‖(2 * (c : ℂ) * I * deriv theta ((c : ℂ) * I)) /
          (1 - (starRingEnd ℂ) (theta ((c : ℂ) * I)) *
            theta ((c : ℂ) * I))‖ ^ 2) := by
  have him : 0 < (((c : ℂ) * I).im) := by simp [hc]
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hthetaAt : ContDiffAt ℂ 2 theta ((c : ℂ) * I) :=
    (htheta.analyticAt (hopen.mem_nhds him)).contDiffAt
  have halpha : ‖theta ((c : ℂ) * I)‖ < 1 := hmap _ him
  have hbound := norm_suzukiMovableSchurRecenter_secondJet_le_schurSlack
    hc htheta hmap
  rw [iteratedDeriv_two_suzukiMovableSchurRecenter_zero hthetaAt halpha,
    deriv_suzukiMovableSchurRecenter_zero
      (hthetaAt.differentiableAt (by norm_num)) halpha] at hbound
  exact hbound

/-- Suzuki's actual finite-aperture Livšic characteristic is holomorphic throughout the upper
half-plane. -/
theorem differentiableOn_suzukiTaV2Livsic_upperHalfPlane
    (a : SuzukiPositiveAperture) :
    DifferentiableOn ℂ (suzukiTaV2Livsic a) {z : ℂ | 0 < z.im} :=
  GaloisForLFunctions.RHTower.differentiableOn_suzukiLivsicQuotient_upperHalfPlane
    (differentiable_suzukiTaV2CharacteristicA a)
    (differentiable_suzukiTaV2CharacteristicE a)
    (suzukiTaV2CharacteristicA_I a) (suzukiTaV2_allAngleRealZeros a)

theorem norm_suzukiTaV2MovableSchurRecenter_secondJet_le_schurSlack
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    ‖iteratedDeriv 2 (suzukiMovableSchurRecenter (suzukiTaV2Livsic a) c) 0‖ ≤
      2 * (1 - ‖deriv (suzukiMovableSchurRecenter (suzukiTaV2Livsic a) c) 0‖ ^ 2) := by
  apply norm_suzukiMovableSchurRecenter_secondJet_le_schurSlack hc
  · exact differentiableOn_suzukiTaV2Livsic_upperHalfPlane a
  · exact fun z hz => norm_suzukiTaV2Livsic_lt_one a hz

/-- Unconditional movable covariant two-jet bound for Suzuki's actual finite-aperture
prime--polar--Gamma characteristic. -/
theorem norm_suzukiTaV2MovableSchurCovariantSecondJet_le
    (a : SuzukiPositiveAperture) {c : ℝ} (hc : 0 < c) :
    ‖(2 * (starRingEnd ℂ) (suzukiTaV2Livsic a ((c : ℂ) * I)) /
          (1 - (starRingEnd ℂ) (suzukiTaV2Livsic a ((c : ℂ) * I)) *
            suzukiTaV2Livsic a ((c : ℂ) * I)) ^ 2) *
          (deriv (suzukiTaV2Livsic a) ((c : ℂ) * I) *
            (2 * (c : ℂ) * I)) ^ 2 +
        (1 - (starRingEnd ℂ) (suzukiTaV2Livsic a ((c : ℂ) * I)) *
            suzukiTaV2Livsic a ((c : ℂ) * I))⁻¹ *
          (iteratedDeriv 2 (suzukiTaV2Livsic a) ((c : ℂ) * I) *
              (2 * (c : ℂ) * I) ^ 2 +
            deriv (suzukiTaV2Livsic a) ((c : ℂ) * I) *
              (4 * (c : ℂ) * I))‖ ≤
      2 * (1 -
        ‖(2 * (c : ℂ) * I *
            deriv (suzukiTaV2Livsic a) ((c : ℂ) * I)) /
          (1 - (starRingEnd ℂ) (suzukiTaV2Livsic a ((c : ℂ) * I)) *
            suzukiTaV2Livsic a ((c : ℂ) * I))‖ ^ 2) := by
  apply norm_suzukiMovableSchurCovariantSecondJet_le hc
  · exact differentiableOn_suzukiTaV2Livsic_upperHalfPlane a
  · exact fun z hz => norm_suzukiTaV2Livsic_lt_one a hz

/-- Exact defect-faithful clearing of the movable Schwarz--Pick wall.  Unlike the coarse uniform
bound below, the right side retains both powers of the collapsing Schur defect and the negative
first-jet square.  Thus no boundary rate or prime--polar cancellation is discarded. -/
theorem norm_suzukiMovableSchur_defectClearedSecondJet_le
    {theta : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im})
    (hmap : ∀ z : ℂ, 0 < z.im → ‖theta z‖ < 1) :
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ 2 +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q‖ ≤
      2 * (‖D‖ ^ 2 - ‖P‖ ^ 2) := by
  dsimp only
  let alpha := theta ((c : ℂ) * I)
  let D : ℂ := 1 - (starRingEnd ℂ) alpha * alpha
  let P : ℂ := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
  let Q : ℂ := iteratedDeriv 2 theta ((c : ℂ) * I) *
      (2 * (c : ℂ) * I) ^ 2 +
    deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
  change ‖2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q‖ ≤
    2 * (‖D‖ ^ 2 - ‖P‖ ^ 2)
  have him : 0 < (((c : ℂ) * I).im) := by simp [hc]
  have halpha : ‖alpha‖ < 1 := hmap _ him
  have hD0 : D ≠ 0 := by
    dsimp only [D]
    exact Bottcher.one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one halpha halpha.le
  have hraw := norm_suzukiMovableSchurCovariantSecondJet_le hc htheta hmap
  change ‖(2 * (starRingEnd ℂ) alpha / D ^ 2) * P ^ 2 + D⁻¹ * Q‖ ≤
    2 * (1 - ‖(2 * (c : ℂ) * I * deriv theta ((c : ℂ) * I)) / D‖ ^ 2) at hraw
  have hP : 2 * (c : ℂ) * I * deriv theta ((c : ℂ) * I) = P := by
    dsimp only [P]
    ring
  rw [hP] at hraw
  have hclear :
      2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q =
        D ^ 2 * ((2 * (starRingEnd ℂ) alpha / D ^ 2) * P ^ 2 + D⁻¹ * Q) := by
    field_simp [hD0]
  rw [hclear, norm_mul]
  calc
    ‖D ^ 2‖ * ‖(2 * (starRingEnd ℂ) alpha / D ^ 2) * P ^ 2 + D⁻¹ * Q‖ ≤
        ‖D ^ 2‖ * (2 * (1 - ‖P / D‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hraw (norm_nonneg _)
    _ = 2 * (‖D‖ ^ 2 - ‖P‖ ^ 2) := by
      rw [norm_pow, norm_div]
      field_simp [norm_ne_zero_iff.mpr hD0]

/-- Linear-defect normalization of the sharp wall.  Division by the positive Schur defect causes
no singular loss: the normalized second jet and its first-jet penalty share the exact budget
`2 ‖D‖`. -/
theorem norm_suzukiMovableSchur_defectNormalizedSecondJet_budget
    {theta : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im})
    (hmap : ∀ z : ℂ, 0 < z.im → ‖theta z‖ < 1) :
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ 2 +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ +
        2 * ‖P‖ ^ 2 / ‖D‖ ≤ 2 * ‖D‖ := by
  dsimp only
  let alpha := theta ((c : ℂ) * I)
  let D : ℂ := 1 - (starRingEnd ℂ) alpha * alpha
  let P : ℂ := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
  let Q : ℂ := iteratedDeriv 2 theta ((c : ℂ) * I) *
      (2 * (c : ℂ) * I) ^ 2 +
    deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
  change ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ +
      2 * ‖P‖ ^ 2 / ‖D‖ ≤ 2 * ‖D‖
  have him : 0 < (((c : ℂ) * I).im) := by simp [hc]
  have halpha : ‖alpha‖ < 1 := hmap _ him
  have hD0 : D ≠ 0 := by
    dsimp only [D]
    exact Bottcher.one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one halpha halpha.le
  have hDnormPos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  have hsharp := norm_suzukiMovableSchur_defectClearedSecondJet_le hc htheta hmap
  change ‖2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q‖ ≤
    2 * (‖D‖ ^ 2 - ‖P‖ ^ 2) at hsharp
  have hfactor :
      2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q =
        D * (Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2) := by
    field_simp [hD0]
    ring
  rw [hfactor, norm_mul] at hsharp
  have hrearrange :
      ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ +
          2 * ‖P‖ ^ 2 / ‖D‖ =
        (‖D‖ * ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ +
          2 * ‖P‖ ^ 2) / ‖D‖ := by
    field_simp [hDnormPos.ne']
  rw [hrearrange, (div_le_iff₀ hDnormPos)]
  nlinarith

/-- Uniform movable bound after the coefficient-faithful linear-defect normalization.  The exact
budget theorem above is stronger; this corollary records that no inverse-defect singularity
remains. -/
theorem norm_suzukiMovableSchur_defectNormalizedSecondJet_le_two
    {theta : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im})
    (hmap : ∀ z : ℂ, 0 < z.im → ‖theta z‖ < 1) :
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ 2 +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ ≤ 2 := by
  dsimp only
  let alpha := theta ((c : ℂ) * I)
  let D : ℂ := 1 - (starRingEnd ℂ) alpha * alpha
  let P : ℂ := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
  let Q : ℂ := iteratedDeriv 2 theta ((c : ℂ) * I) *
      (2 * (c : ℂ) * I) ^ 2 +
    deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
  change ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ ≤ 2
  have him : 0 < (((c : ℂ) * I).im) := by simp [hc]
  have halpha : ‖alpha‖ < 1 := hmap _ him
  have hDnorm : ‖D‖ = 1 - ‖alpha‖ ^ 2 := by
    simpa only [D] using norm_suzukiSchurDefect_eq_of_norm_lt_one halpha
  have hbudget := norm_suzukiMovableSchur_defectNormalizedSecondJet_budget hc htheta hmap
  change ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ +
      2 * ‖P‖ ^ 2 / ‖D‖ ≤ 2 * ‖D‖ at hbudget
  have hpenalty : 0 ≤ 2 * ‖P‖ ^ 2 / ‖D‖ := by positivity
  calc
    ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ ≤
        ‖Q + (2 * (starRingEnd ℂ) alpha / D) * P ^ 2‖ +
          2 * ‖P‖ ^ 2 / ‖D‖ := le_add_of_nonneg_right hpenalty
    _ ≤ 2 * ‖D‖ := hbudget
    _ ≤ 2 := by rw [hDnorm]; nlinarith [sq_nonneg ‖alpha‖]

/-- Clearing the exact Schur defect denominator leaves a uniformly bounded polynomial jet.  This
coarse compatibility corollary is retained for downstream users; the preceding theorem is the
coefficient-faithful boundary form. -/
theorem norm_suzukiMovableSchur_denominatorClearedSecondJet_le_two
    {theta : ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (htheta : DifferentiableOn ℂ theta {z : ℂ | 0 < z.im})
    (hmap : ∀ z : ℂ, 0 < z.im → ‖theta z‖ < 1) :
    let alpha := theta ((c : ℂ) * I)
    let D := 1 - (starRingEnd ℂ) alpha * alpha
    let P := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
    let Q := iteratedDeriv 2 theta ((c : ℂ) * I) *
        (2 * (c : ℂ) * I) ^ 2 +
      deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
    ‖2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q‖ ≤ 2 := by
  dsimp only
  let alpha := theta ((c : ℂ) * I)
  let D : ℂ := 1 - (starRingEnd ℂ) alpha * alpha
  let P : ℂ := deriv theta ((c : ℂ) * I) * (2 * (c : ℂ) * I)
  let Q : ℂ := iteratedDeriv 2 theta ((c : ℂ) * I) *
      (2 * (c : ℂ) * I) ^ 2 +
    deriv theta ((c : ℂ) * I) * (4 * (c : ℂ) * I)
  change ‖2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q‖ ≤ 2
  have him : 0 < (((c : ℂ) * I).im) := by simp [hc]
  have halpha : ‖alpha‖ < 1 := hmap _ him
  have hDnorm : ‖D‖ = 1 - ‖alpha‖ ^ 2 := by
    simpa only [D] using norm_suzukiSchurDefect_eq_of_norm_lt_one halpha
  have hDnormLe : ‖D ^ 2‖ ≤ 1 := by
    rw [norm_pow, hDnorm]
    have halphaSq : ‖alpha‖ ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg alpha) (by norm_num)).2 halpha
    have h := (sq_le_sq₀
      (sub_nonneg.mpr (le_of_lt (by simpa using halphaSq))) (by norm_num)).2
        (sub_le_self 1 (sq_nonneg ‖alpha‖))
    simpa using h
  have hsharp := norm_suzukiMovableSchur_defectClearedSecondJet_le hc htheta hmap
  change ‖2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q‖ ≤
    2 * (‖D‖ ^ 2 - ‖P‖ ^ 2) at hsharp
  calc
    ‖2 * (starRingEnd ℂ) alpha * P ^ 2 + D * Q‖ ≤
        2 * (‖D‖ ^ 2 - ‖P‖ ^ 2) := hsharp
    _ ≤ 2 * ‖D‖ ^ 2 := by nlinarith [sq_nonneg ‖P‖]
    _ = 2 * ‖D ^ 2‖ := by rw [norm_pow]
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hDnormLe (by norm_num)
    _ = 2 := by norm_num

end
end RHTower
