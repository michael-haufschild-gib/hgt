import GaloisForLFunctions.RHTower.HedenmalmLocalFrameObstruction
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import GaloisForLFunctions.RHTower.XiDerivativeKummerCollision

/-!
# A local Kummer collision on the theta Fourier--Laplace strip

The theta-cusp Fourier--Laplace transform is naturally analytic only on `|im w| < 1`.  The common
Kummer collision with its derivative does not need a global half-plane cover, or even the full
source strip: every possible right-half Xi zero maps into `-1/2 < im w < 0`. Divisibility of the
two consecutive local orders there already forces RH.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- The fixed source-coordinate band containing every possible right-half Xi zero. -/
def thetaCuspFourierLaplaceRightZeroBand : Set ℂ :=
  {w : ℂ | -(1 : ℝ) / 2 < w.im ∧ w.im < 0}

theorem isOpen_thetaCuspFourierLaplaceRightZeroBand :
    IsOpen thetaCuspFourierLaplaceRightZeroBand := by
  rw [thetaCuspFourierLaplaceRightZeroBand]
  change IsOpen ({w : ℂ | -(1 : ℝ) / 2 < w.im} ∩ {w : ℂ | w.im < 0})
  exact (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

/-- Common degree-`d` analytic Kummer covers of the theta source transform and its differentiated
source transform, required only on the fixed right-zero band. -/
def ThetaCuspDerivativeCommonKummerRootRightZeroBand (d : ℕ) : Prop :=
  ∃ g h : ℂ → ℂ,
    AnalyticOnNhd ℂ g thetaCuspFourierLaplaceRightZeroBand ∧
    AnalyticOnNhd ℂ h thetaCuspFourierLaplaceRightZeroBand ∧
    (∀ w ∈ thetaCuspFourierLaplaceRightZeroBand,
      g w ^ d = thetaCuspFourierLaplace w) ∧
    (∀ w ∈ thetaCuspFourierLaplaceRightZeroBand,
      h w ^ d = deriv thetaCuspFourierLaplace w)

/-- The remaining degree-two differentiated-source condition after the first Xi ladder rung
supplies the square root of the undifferentiated theta transform. -/
def ThetaCuspDerivativeSquareRootRightZeroBand : Prop :=
  ∃ h : ℂ → ℂ,
    AnalyticOnNhd ℂ h thetaCuspFourierLaplaceRightZeroBand ∧
      ∀ w ∈ thetaCuspFourierLaplaceRightZeroBand,
        h w ^ 2 = deriv thetaCuspFourierLaplace w

private theorem rightZeroBand_mem_fourierLaplaceStrip
    {w : ℂ} (hw : w ∈ thetaCuspFourierLaplaceRightZeroBand) :
    w ∈ thetaCuspFourierLaplaceStrip := by
  rw [thetaCuspFourierLaplaceRightZeroBand, Set.mem_setOf_eq] at hw
  rw [thetaCuspFourierLaplaceStrip, Set.mem_setOf_eq]
  constructor <;> linarith [hw.1, hw.2]

/-- At a zero inside the right-zero band, the theta Fourier--Laplace transform and its derivative
have consecutive finite analytic orders. -/
theorem analyticOrderAt_thetaCuspFourierLaplace_and_deriv_of_zero
    {w : ℂ} (hw : w ∈ thetaCuspFourierLaplaceRightZeroBand)
    (hzero : thetaCuspFourierLaplace w = 0) :
    ∃ k : ℕ,
      analyticOrderAt thetaCuspFourierLaplace w = (k + 1 : ℕ) ∧
      analyticOrderAt (deriv thetaCuspFourierLaplace) w = (k : ℕ) := by
  have hwStrip := rightZeroBand_mem_fourierLaplaceStrip hw
  have hanalytic : AnalyticAt ℂ thetaCuspFourierLaplace w :=
    analyticOnNhd_thetaCuspFourierLaplace w hwStrip
  have heq : thetaCuspFourierLaplace =ᶠ[𝓝 w] XiC :=
    thetaCuspFourierLaplace_eq_XiC_on_strip.eventuallyEq_of_mem
      (isOpen_thetaCuspFourierLaplaceStrip.mem_nhds hwStrip)
  have hfinite : analyticOrderAt thetaCuspFourierLaplace w ≠ ⊤ := by
    rw [analyticOrderAt_congr heq]
    exact XiC_order_ne_top w
  let m : ℕ := (analyticOrderAt thetaCuspFourierLaplace w).toNat
  have hmne : m ≠ 0 := by
    have hne : analyticOrderAt thetaCuspFourierLaplace w ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hanalytic, hzero⟩
    intro hm
    rcases ENat.toNat_eq_zero.mp hm with horder | htop
    · exact hne horder
    · exact hfinite htop
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmne
  have horder : analyticOrderAt thetaCuspFourierLaplace w = (k + 1 : ℕ) := by
    calc
      analyticOrderAt thetaCuspFourierLaplace w = (m : ℕ∞) :=
        (ENat.coe_toNat hfinite).symm
      _ = (k + 1 : ℕ) := by rw [hk, Nat.succ_eq_add_one]
  refine ⟨k, horder, ?_⟩
  have hderiv := analyticOrderAt_deriv_of_pos hanalytic
    (n := k) (by simpa [Nat.cast_add, Nat.cast_one] using horder)
  simpa using hderiv

/-- **Critical-band Kummer collision.** Common degree-`d` covers of the theta Fourier--Laplace
transform and its derivative on `-1/2 < im w < 0`, for one `d > 1`, force RH. -/
theorem riemannHypothesis_of_thetaCuspDerivativeCommonKummerRootRightZeroBand
    {d : ℕ} (hd : 1 < d)
    (hroot : ThetaCuspDerivativeCommonKummerRootRightZeroBand d) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨g, h, hg, hh, hgpow, hhpow⟩ := hroot
  let w : ℂ := (rho - 1 / 2) * (-I)
  have hcritical := xi_zero_re_mem_open_unit hzero
  have hwBand : w ∈ thetaCuspFourierLaplaceRightZeroBand := by
    rw [thetaCuspFourierLaplaceRightZeroBand, Set.mem_setOf_eq]
    dsimp only [w]
    simp
    constructor <;> linarith [mem_rightHalf.mp hrho]
  have hwStrip := rightZeroBand_mem_fourierLaplaceStrip hwBand
  have hcoord : 1 / 2 + w * I = rho := by
    dsimp only [w]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have hthetaZero : thetaCuspFourierLaplace w = 0 := by
    rw [thetaCuspFourierLaplace_eq_XiC_on_strip hwStrip, XiC, hcoord, hzero]
  obtain ⟨k, hthetaOrder, hderivOrder⟩ :=
    analyticOrderAt_thetaCuspFourierLaplace_and_deriv_of_zero hwBand hthetaZero
  have hdne : d ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd)
  have hdtheta : (d : ℕ∞) ∣ analyticOrderAt thetaCuspFourierLaplace w :=
    root_orders_dvd isOpen_thetaCuspFourierLaplaceRightZeroBand hg hgpow hwBand
  have hdderiv : (d : ℕ∞) ∣ analyticOrderAt (deriv thetaCuspFourierLaplace) w :=
    root_orders_dvd isOpen_thetaCuspFourierLaplaceRightZeroBand hh hhpow hwBand
  rw [hthetaOrder] at hdtheta
  rw [hderivOrder] at hdderiv
  have hdthetaNat : d ∣ k + 1 := natCast_dvd_natCast_of_enat hdne hdtheta
  have hdderivNat : d ∣ k := natCast_dvd_natCast_of_enat hdne hdderiv
  have hdOne : d ∣ 1 := by simpa using Nat.dvd_sub hdthetaNat hdderivNat
  have : d = 1 := Nat.eq_one_of_dvd_one hdOne
  omega

/-- The first Xi multiplicity rung supplies the undifferentiated right-zero-band square root. Thus a
square root of only the differentiated theta source transform closes the local collision. -/
theorem riemannHypothesis_of_rhLadder_one_of_thetaCuspDerivativeSquareRootRightZeroBand
    (hxi : RHLadder 1)
    (hderiv : ThetaCuspDerivativeSquareRootRightZeroBand) :
    RiemannHypothesis := by
  obtain ⟨g, hg, hgpow⟩ := rhLadder_one_iff_sqrt_rightHalf.mp hxi
  obtain ⟨h, hh, hhpow⟩ := hderiv
  let pull : ℂ → ℂ := fun w => 1 / 2 + w * I
  let G : ℂ → ℂ := fun w => g (pull w)
  have hpull_mem : ∀ w ∈ thetaCuspFourierLaplaceRightZeroBand,
      pull w ∈ rightHalf := by
    intro w hw
    rw [thetaCuspFourierLaplaceRightZeroBand, Set.mem_setOf_eq] at hw
    rw [mem_rightHalf]
    dsimp only [pull]
    simp
    linarith
  have hG : AnalyticOnNhd ℂ G thetaCuspFourierLaplaceRightZeroBand := by
    intro w hw
    dsimp only [G]
    exact AnalyticAt.comp (f := pull) (x := w)
      (hg (pull w) (hpull_mem w hw)) (by dsimp only [pull]; fun_prop)
  have hGpow : ∀ w ∈ thetaCuspFourierLaplaceRightZeroBand,
      G w ^ 2 = thetaCuspFourierLaplace w := by
    intro w hw
    have hwStrip := rightZeroBand_mem_fourierLaplaceStrip hw
    calc
      G w ^ 2 = xi (pull w) := hgpow (pull w) (hpull_mem w hw)
      _ = XiC w := by rfl
      _ = thetaCuspFourierLaplace w :=
        (thetaCuspFourierLaplace_eq_XiC_on_strip hwStrip).symm
  apply riemannHypothesis_of_thetaCuspDerivativeCommonKummerRootRightZeroBand
    (d := 2) (by norm_num)
  exact ⟨G, h, hG, hh, hGpow, hhpow⟩

end

end RHTower
