import GaloisForLFunctions.RHTower.SuzukiCharacteristicMeromorphicLimit
import GaloisForLFunctions.RHTower.XiLogDerivPositiveRayAsymptotic
import GaloisForLFunctions.RHTower.SquaredXiRadialJetXiSpecialization
import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import GaloisForLFunctions.RHTower.XiSchurDiscGerm
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam

/-!
# Suzuki v2 characteristic target and its unavoidable pole

Suzuki v2, Corollary 1.6 uses
`xi(1/2-iz) / (xi(1/2-iz) + xi'(1/2-iz))`.  In centered coordinates this is
`XiC z / (XiC z + i XiC' z)`.  This module formalizes the literal compact-open implication
to RH and proves a sharper unconditional correction: the displayed target has a genuine pole on
the negative imaginary axis.  Consequently no entire real-zero characteristics, even after finite
holomorphic exponential gauges, can converge compact-open to that target on all of `C`.

The coherent surviving statement is locally uniform convergence on a preconnected pole-free open
set retaining the whole Xi divisor; that corrected statement still implies RH.
-/

open Complex Metric Set Filter Topology

namespace RHTower

noncomputable section

/-- Suzuki v2's displayed characteristic target in centered Xi coordinates. -/
def suzukiV2CharacteristicTarget (z : ℂ) : ℂ :=
  XiC z / xiHedenmalmDeBrangesE z

/-- The centered target is exactly Suzuki v2's uncentered displayed quotient. -/
theorem suzukiV2CharacteristicTarget_eq_paper (z : ℂ) :
    suzukiV2CharacteristicTarget z =
      xi (1 / 2 - I * z) / (xi (1 / 2 - I * z) + deriv xi (1 / 2 - I * z)) := by
  have harg : (1 : ℂ) / 2 + (-z) * I = 1 / 2 - I * z := by ring
  have hvalue : xi (1 / 2 - I * z) = XiC z := by
    rw [← harg, ← XiC, XiC_even]
  have hchain := deriv_XiC_eq_deriv_xi_mul_I (-z)
  rw [harg, deriv_XiC_neg] at hchain
  have hderiv : deriv xi (1 / 2 - I * z) = I * deriv XiC z := by
    have hmul := congrArg (fun w : ℂ => w * I) hchain
    rw [mul_assoc, I_mul_I] at hmul
    calc
      deriv xi (1 / 2 - I * z) = -(deriv xi (1 / 2 - I * z) * -1) := by ring
      _ = -((-deriv XiC z) * I) := by rw [hmul]
      _ = I * deriv XiC z := by ring
  rw [suzukiV2CharacteristicTarget, xiHedenmalmDeBrangesE, hvalue, hderiv]

/-- The completed logarithmic derivative tends to `+infinity` on the positive real ray. -/
theorem tendsto_xiRayLogDeriv_atTop :
    Tendsto xiRayLogDeriv atTop atTop := by
  have hprod : Tendsto
      (fun x : ℝ => Real.log x * (xiRayLogDeriv x / Real.log x))
      atTop atTop :=
    Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
      Real.tendsto_log_atTop tendsto_xiRayLogDeriv_div_log
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  field_simp [hlog]

/-- The positive-ray completed logarithmic derivative crosses the exact value one. -/
theorem exists_pos_xiRealLogDeriv_eq_one :
    ∃ c : ℝ, 0 < c ∧ xiRealLogDeriv c = 1 := by
  have hev := tendsto_xiRayLogDeriv_atTop.eventually_gt_atTop 1
  obtain ⟨X, hX⟩ := eventually_atTop.1 hev
  let Y := max X 2
  have hY : 1 < xiRayLogDeriv Y := hX Y (le_max_left _ _)
  let c₁ := Y - 1 / 2
  have hc₁ : 0 < c₁ := by
    dsimp only [c₁, Y]
    linarith [le_max_right X 2]
  have hcval : 1 < xiRealLogDeriv c₁ := by
    rw [← xiRayLogDeriv_shift]
    convert hY using 1
    dsimp only [c₁]
    ring
  have hzero : xiRealLogDeriv 0 = 0 := by
    rw [← xiRayLogDeriv_shift]
    simp only [add_zero, xiRayLogDeriv]
    rw [show (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) by norm_num]
    rw [xiLogDeriv, ← logDeriv_apply, logDeriv_xi_one_half]
    rfl
  have hcont : Continuous xiRealLogDeriv := by
    have hbase : Continuous xiRayLogDeriv := (contDiff_xiRayLogDeriv 0).continuous
    have hcomp : Continuous (fun v : ℝ => xiRayLogDeriv (1 / 2 + v)) := by
      fun_prop
    exact hcomp.congr xiRayLogDeriv_shift
  have hmem : (1 : ℝ) ∈ Icc (xiRealLogDeriv 0) (xiRealLogDeriv c₁) := by
    rw [hzero]
    exact ⟨by norm_num, hcval.le⟩
  obtain ⟨c, hc, hval⟩ :=
    intermediate_value_Icc hc₁.le hcont.continuousOn hmem
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, hzero] at hval
    norm_num at hval
  exact ⟨c, lt_of_le_of_ne hc.1 (Ne.symm hc0), hval⟩

/-- There is unconditionally a negative-imaginary zero of `XiC + i XiC'` at which `XiC`
is nonzero. -/
theorem exists_negativeImaginary_xiHedenmalmDeBrangesE_zero :
    ∃ c : ℝ, 0 < c ∧ XiC (-((c : ℂ) * I)) ≠ 0 ∧
      xiHedenmalmDeBrangesE (-((c : ℂ) * I)) = 0 := by
  obtain ⟨c, hc, hL⟩ := exists_pos_xiRealLogDeriv_eq_one
  let z : ℂ := -((c : ℂ) * I)
  have hXi : XiC z ≠ 0 := XiC_neg_imaginaryAxis_ne_zero hc
  have harg : (1 : ℂ) / 2 + z * I = (((1 / 2 + c : ℝ)) : ℂ) := by
    dsimp only [z]
    apply Complex.ext <;> simp
  have hlogReal : logDeriv xi (((1 / 2 + c : ℝ)) : ℂ) = 1 := by
    apply Complex.ext
    · simpa [xiRealLogDeriv] using hL
    · simpa using logDeriv_xi_ofReal_im (1 / 2 + c)
  have hlog : logDeriv XiC z = I := by
    rw [logDeriv_XiC_eq_mul_I_logDeriv_xi, harg, hlogReal, mul_one]
  have hderiv : deriv XiC z = I * XiC z := by
    rw [logDeriv_apply] at hlog
    exact (div_eq_iff hXi).mp hlog
  refine ⟨c, hc, hXi, ?_⟩
  rw [xiHedenmalmDeBrangesE, hderiv]
  change XiC z + I * (I * XiC z) = 0
  rw [← mul_assoc, I_mul_I]
  ring

theorem analyticOrderAt_xiHedenmalmDeBrangesE_ne_top (z : ℂ) :
    analyticOrderAt xiHedenmalmDeBrangesE z ≠ ⊤ := by
  have hglobal : AnalyticOnNhd ℂ xiHedenmalmDeBrangesE Set.univ := by
    intro w _
    change AnalyticAt ℂ (fun q => XiC q + I * deriv XiC q) w
    exact (XiC_analytic w (Set.mem_univ w)).add
      (analyticAt_const.mul (XiC_analytic w (Set.mem_univ w)).deriv)
  have hderiv0 : deriv XiC 0 = 0 := by
    have h := deriv_XiC_neg 0
    simp only [neg_zero] at h
    have htwo : (2 : ℂ) * deriv XiC 0 = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hE0 : xiHedenmalmDeBrangesE 0 ≠ 0 := by
    rw [xiHedenmalmDeBrangesE, hderiv0, mul_zero, add_zero]
    exact XiC_zero_ne
  apply hglobal.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  rw [(hglobal 0 (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hE0]
  exact ENat.zero_ne_top

/-- A zero of the v2 denominator with nonzero numerator is a genuine pole of the v2 target. -/
theorem not_analyticAt_suzukiV2CharacteristicTarget
    {c : ℂ} (hXi : XiC c ≠ 0)
    (hE : xiHedenmalmDeBrangesE c = 0) :
    ¬ AnalyticAt ℂ suzukiV2CharacteristicTarget c := by
  intro htarget
  have hnum : AnalyticAt ℂ XiC c := XiC_analytic c (Set.mem_univ c)
  have hnumOrder : analyticOrderAt XiC c = 0 :=
    hnum.analyticOrderAt_eq_zero.mpr hXi
  have hden : AnalyticAt ℂ xiHedenmalmDeBrangesE c := by
    change AnalyticAt ℂ (fun q => XiC q + I * deriv XiC q) c
    exact hnum.add (analyticAt_const.mul hnum.deriv)
  have hdenOrder0 : analyticOrderAt xiHedenmalmDeBrangesE c ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hden, hE⟩
  have hdenOrderTop := analyticOrderAt_xiHedenmalmDeBrangesE_ne_top c
  let m : ℕ := (analyticOrderAt xiHedenmalmDeBrangesE c).toNat
  have hm : (m : ℕ∞) = analyticOrderAt xiHedenmalmDeBrangesE c :=
    ENat.coe_toNat hdenOrderTop
  have hm0 : m ≠ 0 := by
    intro hmzero
    apply hdenOrder0
    rw [← hm, hmzero]
    rfl
  have htargetOrder : meromorphicOrderAt suzukiV2CharacteristicTarget c < 0 := by
    unfold suzukiV2CharacteristicTarget
    change meromorphicOrderAt (XiC / xiHedenmalmDeBrangesE) c < 0
    rw [meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt,
      hnum.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq,
      hnumOrder, ← hm]
    simp only [ENat.map_zero, ENat.map_coe]
    have hmposZ : (0 : ℤ) < (m : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm0
    change (((0 : ℤ) : WithTop ℤ) - ((m : ℤ) : WithTop ℤ)) <
      ((0 : ℤ) : WithTop ℤ)
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_lt_coe.mpr (sub_neg.mpr hmposZ)
  have htargetNonneg : 0 ≤ meromorphicOrderAt suzukiV2CharacteristicTarget c := by
    rw [htarget.meromorphicOrderAt_eq]
    have enatMap_nonneg (n : ℕ∞) :
        (0 : WithTop ℤ) ≤ ENat.map Nat.cast n := by
      induction n using ENat.recTopCoe with
      | top => simp
      | coe n => simp
    exact enatMap_nonneg _
  exact (not_lt_of_ge htargetNonneg) htargetOrder

/-- Suzuki v2's displayed target is unconditionally not entire. -/
theorem not_analyticOnNhd_suzukiV2CharacteristicTarget :
    ¬ AnalyticOnNhd ℂ suzukiV2CharacteristicTarget Set.univ := by
  intro h
  obtain ⟨c, _, hXi, hE⟩ :=
    exists_negativeImaginary_xiHedenmalmDeBrangesE_zero
  exact not_analyticAt_suzukiV2CharacteristicTarget hXi hE
    (h _ (Set.mem_univ _))

/-- The v2 target is normalized to one at the center. -/
theorem suzukiV2CharacteristicTarget_zero :
    suzukiV2CharacteristicTarget 0 = 1 := by
  have hderiv0 : deriv XiC 0 = 0 := by
    have h := deriv_XiC_neg 0
    simp only [neg_zero] at h
    have htwo : (2 : ℂ) * deriv XiC 0 = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  rw [suzukiV2CharacteristicTarget, xiHedenmalmDeBrangesE,
    hderiv0, mul_zero, add_zero, div_self XiC_zero_ne]

/-- Literal analytic content of Suzuki v2, Corollary 1.6. -/
def SuzukiV2CharacteristicLimitWall : Prop :=
  ∃ W : ℕ → ℂ → ℂ,
    TendstoLocallyUniformly W suzukiV2CharacteristicTarget atTop ∧
    (∀ᶠ n in atTop, Differentiable ℂ (W n)) ∧
    (∀ᶠ n in atTop, ∀ z : ℂ, W n z = 0 → z.im = 0)

/-- Suzuki v2, Corollary 1.6: the literal compact-open characteristic limit implies RH. -/
theorem suzukiV2CharacteristicLimitWall_implies_riemannHypothesis :
    SuzukiV2CharacteristicLimitWall → RiemannHypothesis := by
  rintro ⟨W, hconv, hdiff, hreal⟩
  have htargetDiffOn : DifferentiableOn ℂ suzukiV2CharacteristicTarget Set.univ :=
    hconv.tendstoLocallyUniformlyOn.differentiableOn
      (hdiff.mono fun _ hn => hn.differentiableOn) isOpen_univ
  have htarget : AnalyticOnNhd ℂ suzukiV2CharacteristicTarget Set.univ :=
    htargetDiffOn.analyticOnNhd isOpen_univ
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let z : ℂ := (rho - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = rho := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by
        rw [neg_mul, I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have htargetz : suzukiV2CharacteristicTarget z = 0 := by
    rw [suzukiV2CharacteristicTarget, hXiC, zero_div]
  have him : z.im = 0 := zero_mem_closed_of_tendstoLocallyUniformly
    hconv htarget hdiff
    (isClosed_eq Complex.continuous_im continuous_const)
    hreal (by rw [suzukiV2CharacteristicTarget_zero]; norm_num) htargetz
  have hzIm : z.im = 1 / 2 - rho.re := by
    simp [z]
  have hre : rho.re = 1 / 2 := by
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hre

/-- Stronger correction to Suzuki v2: its literal all-plane compact-open wall is false. -/
theorem not_suzukiV2CharacteristicLimitWall :
    ¬ SuzukiV2CharacteristicLimitWall := by
  rintro ⟨W, hconv, hdiff, _⟩
  have htargetDiffOn : DifferentiableOn ℂ suzukiV2CharacteristicTarget Set.univ :=
    hconv.tendstoLocallyUniformlyOn.differentiableOn
      (hdiff.mono fun _ hn => hn.differentiableOn) isOpen_univ
  exact not_analyticOnNhd_suzukiV2CharacteristicTarget
    (htargetDiffOn.analyticOnNhd isOpen_univ)

/-- Corrected v2 wall: convergence only on a pole-free open set retaining the Xi divisor. -/
def SuzukiV2MeromorphicCharacteristicLimitWall : Prop :=
  ∃ (Omega : Set ℂ) (W : ℕ → ℂ → ℂ),
    IsOpen Omega ∧ IsPreconnected Omega ∧
    {z : ℂ | XiC z = 0} ⊆ Omega ∧
    AnalyticOnNhd ℂ suzukiV2CharacteristicTarget Omega ∧
    TendstoLocallyUniformlyOn W suzukiV2CharacteristicTarget atTop Omega ∧
    (∀ᶠ n in atTop, Differentiable ℂ (W n)) ∧
    (∀ᶠ n in atTop, ∀ z : ℂ, W n z = 0 → z.im = 0) ∧
    0 ∈ Omega

/-- The corrected pole-free v2 convergence statement still implies RH. -/
theorem suzukiV2MeromorphicCharacteristicLimitWall_implies_riemannHypothesis :
    SuzukiV2MeromorphicCharacteristicLimitWall → RiemannHypothesis := by
  rintro ⟨Omega, W, hOpen, hPre, hZeros, hAnalytic, hConv, hDiff, hReal, hZero⟩
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let z : ℂ := (rho - 1 / 2) * (-I)
  have hXiC : XiC z = 0 := by
    rw [XiC]
    have harg : (1 : ℂ) / 2 + z * I = rho := by
      dsimp only [z]
      rw [mul_assoc]
      have hI : (-I) * I = (1 : ℂ) := by
        rw [neg_mul, I_mul_I]
        ring
      rw [hI, mul_one]
      ring
    rw [harg, hzero]
  have hzOmega : z ∈ Omega := hZeros hXiC
  have htargetz : suzukiV2CharacteristicTarget z = 0 := by
    rw [suzukiV2CharacteristicTarget, hXiC, zero_div]
  have hmem := mem_closed_of_tendstoLocallyUniformlyOn
    hOpen hPre hConv hAnalytic hDiff
    (isClosed_eq Complex.continuous_im continuous_const) hReal
    hZero (by rw [suzukiV2CharacteristicTarget_zero]; norm_num)
    hzOmega htargetz
  have him : z.im = 0 := by
    simpa using hmem
  have hzIm : z.im = 1 / 2 - rho.re := by
    simp [z]
  have hre : rho.re = 1 / 2 := by
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hrho)) hre

end

end RHTower
