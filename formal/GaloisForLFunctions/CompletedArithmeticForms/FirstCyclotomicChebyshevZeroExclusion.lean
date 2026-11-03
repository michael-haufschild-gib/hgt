import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicChebyshevMellin
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualODEClosure
import GaloisForLFunctions.RHTower.XiWardGlobalCapRightZeroSum
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCount
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The first mode excludes zeros beyond its growth exponent

The nonvanishing Mellin multiplier turns the arithmetic transform into a
holomorphic first-order ODE for the pole-filled zeta function. Zero propagation
on the upper sector, followed by Schwarz conjugation, bounds the zero abscissa.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Set Topology Asymptotics

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Growth of the actual first-mode packet excludes zeta zeros in the corresponding upper sector. -/
theorem zetaResidueUnit_ne_zero_of_firstCyclotomicContinuous_growth
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : chebyshevFirstCyclotomicContinuous =O[atTop] fun x : ℝ => x ^ b)
    {s : ℂ} (hsre : b < s.re) (hsim : 2 * Real.pi < s.im) :
    _root_.RHTower.zetaResidueUnit (s + 1 / 2) ≠ 0 := by
  let U : Set ℂ := {z | b < z.re ∧ 2 * Real.pi < z.im}
  let F : ℂ → ℂ := fun z => mellin chebyshevFirstCyclotomicContinuous (-z)
  let Z : ℂ → ℂ := fun z => _root_.RHTower.zetaResidueUnit (z + 1 / 2)
  let G : ℂ → ℂ := fun z => (z + 1 / 2) * F z / firstCyclotomicMellin z + 1
  let H : ℂ → ℂ := fun z => deriv Z z + G z * Z z
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hUpre : IsPreconnected U :=
    ((convex_halfSpace_re_gt b).inter (convex_halfSpace_im_gt (2 * Real.pi))).isPreconnected
  have hF : AnalyticOnNhd ℂ F U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (differentiableAt_mellin_chebyshevFirstCyclotomicContinuous hbound hz.1).differentiableWithinAt
  have hJ : AnalyticOnNhd ℂ firstCyclotomicMellin U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    exact (differentiableAt_firstCyclotomicMellin
      (by linarith only [hb, hz.1])).differentiableWithinAt
  have hJne (z : ℂ) (hz : z ∈ U) : firstCyclotomicMellin z ≠ 0 :=
    firstCyclotomicMellin_ne_zero (lt_of_le_of_lt hb hz.1) hz.2
  have hshift (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => w + 1 / 2) z :=
    analyticAt_id.add analyticAt_const
  have hZ : AnalyticOnNhd ℂ Z U := fun z _ =>
    (_root_.RHTower.analyticAt_zetaResidueUnit (z + 1 / 2)).comp
      (f := fun w : ℂ => w + 1 / 2) (x := z) (hshift z)
  have hderivZ (z : ℂ) : deriv Z z = deriv _root_.RHTower.zetaResidueUnit (z + 1 / 2) := by
    have hd := ((_root_.RHTower.analyticAt_zetaResidueUnit (z + 1 / 2)).differentiableAt.hasDerivAt).comp
      z ((hasDerivAt_id z).add_const (1 / 2))
    simpa only [Function.comp_def, id_eq, mul_one, Z] using! hd.deriv
  have hG : AnalyticOnNhd ℂ G U := fun z hz =>
    (((hshift z).mul (hF z hz)).div (hJ z hz) (hJne z hz)).add analyticAt_const
  have hH : AnalyticOnNhd ℂ H U := fun z hz =>
    (hZ z hz).deriv.add ((hG z hz).mul (hZ z hz))
  have hsafe (z : ℂ) (hz : 1 / 2 < z.re) : Z z ≠ 0 := by
    have hu : 1 < (z + 1 / 2).re := by
      have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
      rw [add_re, hhalf]
      linarith only [hz]
    have hu1 : z + 1 / 2 ≠ 1 := by intro he; rw [he] at hu; norm_num at hu
    change _root_.RHTower.zetaResidueUnit (z + 1 / 2) ≠ 0
    rw [_root_.RHTower.zetaResidueUnit, Function.update_of_ne hu1]
    exact mul_ne_zero (sub_ne_zero.mpr hu1) (riemannZeta_ne_zero_of_one_lt_re hu)
  have hHzero (z : ℂ) (hz : z ∈ U) (hfar : 1 / 2 < z.re) : H z = 0 := by
    have hu0 : z + 1 / 2 ≠ 0 := by
      intro he
      have hre := congrArg Complex.re he
      have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
      rw [add_re, hhalf, zero_re] at hre
      linarith only [hre, hfar]
    have hGs : G z = -(deriv _root_.RHTower.zetaResidueUnit (z + 1 / 2) / Z z) := by
      dsimp only [G, F, Z]
      rw [mellin_chebyshevFirstCyclotomicContinuous_eq_logDeriv hfar]
      calc
        _ = -(logDeriv _root_.RHTower.zetaResidueUnit (z + 1 / 2) + 1) *
            ((z + 1 / 2) / (z + 1 / 2)) *
            (firstCyclotomicMellin z / firstCyclotomicMellin z) + 1 := by ring
        _ = _ := by
          rw [div_self hu0, div_self (hJne z hz), mul_one, mul_one, logDeriv_apply]
          ring
    dsimp only [H]
    rw [hderivZ, hGs, neg_mul, div_mul_cancel₀ _ (hsafe z hfar), add_neg_cancel]
  let p : ℂ := ((b + 2 : ℝ) : ℂ) + ((2 * Real.pi + 1 : ℝ) : ℂ) * I
  have hpRe : p.re = b + 2 := by simp [p]
  have hpIm : p.im = 2 * Real.pi + 1 := by simp [p]
  have hpU : p ∈ U := by
    change b < p.re ∧ 2 * Real.pi < p.im
    rw [hpRe, hpIm]
    constructor <;> linarith
  have hpFar : 1 / 2 < p.re := by
    rw [hpRe]
    linarith only [hb]
  have hfreq : ∃ᶠ z in 𝓝[≠] p, H z = 0 := by
    have hnearU : ∀ᶠ z in 𝓝 p, z ∈ U := hUopen.mem_nhds hpU
    have hnearFar : ∀ᶠ z in 𝓝 p, 1 / 2 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpFar
    have hnear : ∀ᶠ z in 𝓝 p, H z = 0 := by
      filter_upwards [hnearU, hnearFar] with z hz hfar
      exact hHzero z hz hfar
    exact (Eventually.filter_mono nhdsWithin_le_nhds hnear).frequently
  have hzero := hH.eqOn_zero_of_preconnected_of_frequently_eq_zero hUpre hpU hfreq
  have hODE : ∀ z ∈ U, deriv Z z = -G z * Z z := by
    intro z hz
    have hh := hzero hz
    change deriv Z z + G z * Z z = 0 at hh
    rw [neg_mul]
    exact eq_neg_of_add_eq_zero_left hh
  intro hszero
  exact _root_.RHTower.false_of_analytic_firstOrderODE_zero_and_nonzero
    hUopen hUpre hZ hG hODE ⟨hsre, hsim⟩ hpU hszero (hsafe p hpFar)

#print axioms zetaResidueUnit_ne_zero_of_firstCyclotomicContinuous_growth

private theorem xiRightCenteredZero_re_le_of_firstCyclotomicContinuous_growth
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : chebyshevFirstCyclotomicContinuous =O[atTop] fun x : ℝ => x ^ b)
    (q : _root_.RHTower.XiRightZeroCopy) : (_root_.RHTower.xiRightCenteredZero q).re ≤ b := by
  have hupper (p : _root_.RHTower.XiRightUpperZeroCopy) :
      (_root_.RHTower.xiRightCenteredZero p.1).re ≤ b := by
    by_contra hnot
    have hre : b < (_root_.RHTower.xiRightCenteredZero p.1).re := lt_of_not_ge hnot
    have hh := _root_.RHTower.xiWard_offlinePair_abs_im_gt_eight p
    rw [abs_of_pos p.2] at hh
    have hne := zetaResidueUnit_ne_zero_of_firstCyclotomicContinuous_growth hb hbound hre
      (by linarith only [hh, Real.pi_lt_four])
    apply hne
    have heq : _root_.RHTower.xiRightCenteredZero p.1 + 1 / 2 = (p.1.1.1 : ℂ) := by
      rw [_root_.RHTower.xiRightCenteredZero, _root_.RHTower.I_mul_xiSpectralPoint]
      ring
    have hp1 : (p.1.1.1 : ℂ) ≠ 1 := by
      intro he
      have h := _root_.RHTower.xiZeroCopy_re_lt_one p.1.1
      rw [he, one_re] at h
      exact (lt_irrefl 1) h
    rw [heq, _root_.RHTower.zetaResidueUnit, Function.update_of_ne hp1,
      _root_.RHTower.riemannZeta_xiZeroCopy_eq_zero, mul_zero]
  by_cases hpos : 0 < (_root_.RHTower.xiRightCenteredZero q).im
  · exact hupper ⟨q, hpos⟩
  · have hneg : (_root_.RHTower.xiRightCenteredZero q).im < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) (_root_.RHTower.xiRightCenteredZero_im_ne_zero q)
    have hconjpos : 0 < (_root_.RHTower.xiRightCenteredZero
        (_root_.RHTower.xiRightZeroCopyConjEquiv q)).im := by
      rw [_root_.RHTower.xiRightCenteredZero_conj, conj_im]
      linarith only [hneg]
    have h := hupper ⟨_root_.RHTower.xiRightZeroCopyConjEquiv q, hconjpos⟩
    rwa [_root_.RHTower.xiRightCenteredZero_conj, conj_re] at h

/-- The actual continuous first mode retains every rightmost zero exponent. -/
theorem zetaZeroAbscissa_le_of_firstCyclotomicContinuous_growth
    {b : ℝ} (hb : 0 ≤ b)
    (hbound : chebyshevFirstCyclotomicContinuous =O[atTop] fun x : ℝ => x ^ b) :
    _root_.RHTower.zetaZeroAbscissa ≤ b + 1 / 2 := by
  apply csSup_le _root_.RHTower.zetaZeroReSet_nonempty
  rintro y ⟨ρ, hρ, rfl⟩
  by_cases hright : 1 / 2 < ρ.re
  · have hρ0 : 0 < ρ.re := by linarith only [hright]
    have hρ1 : ρ ≠ 1 := by intro he; subst ρ; exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hρ
    obtain ⟨c, hc⟩ := _root_.RHTower.exists_xiZeroCopy_of_riemannZeta_eq_zero hρ0 hρ1 hρ
    have hcenter : I * _root_.RHTower.xiSpectralPoint c = ρ - 1 / 2 := by
      rw [_root_.RHTower.I_mul_xiSpectralPoint, hc]
    have hcpos : 0 < (I * _root_.RHTower.xiSpectralPoint c).re := by
      rw [hcenter]
      have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
      rw [sub_re, hhalf]
      linarith only [hright]
    have h := xiRightCenteredZero_re_le_of_firstCyclotomicContinuous_growth hb hbound ⟨c, hcpos⟩
    change (I * _root_.RHTower.xiSpectralPoint c).re ≤ b at h
    rw [hcenter] at h
    have hhalf : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    rw [sub_re, hhalf] at h
    linarith only [h]
  · linarith only [le_of_not_gt hright, hb]

#print axioms zetaZeroAbscissa_le_of_firstCyclotomicContinuous_growth

end GaloisForLFunctions.CompletedArithmeticForms
