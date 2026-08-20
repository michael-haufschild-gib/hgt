/-
# The critical Loewner generator is an exact RH criterion

In centred coordinates `X(W) = ξ(1/2 + W)` the shifted Loewner generator is
`H_ω(W) = (log X)' (W - ω) + (log X)' (W + ω)` and the generator kernel is the Carathéodory kernel
`C_ω(W,V) = (H_ω(W) + conj (H_ω V)) / (W + conj V)`, both taken on the Euler region
`Re W > 1/2 + ω` where `X` has no zeros.

Positivity of the critical generator `C_0` on the Euler region is exactly the Riemann hypothesis,
and no positive shift has a positive generator.  Both directions of the first statement and the
second statement come from the same mechanism: a positive Carathéodory kernel extends, by
Nevanlinna--Pick, to a Carathéodory function on the whole right half plane, and a holomorphic
logarithmic derivative forbids zeros.
-/
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import GaloisForLFunctions.HTGeometry.PSDKernelMatrixBridge
import GaloisForLFunctions.HTGeometry.LogDerivNoZero
import GaloisForLFunctions.RHTower.XiUnitEulerPoleBezoutianSufficiency
import GaloisForLFunctions.RHTower.HardyTheorem

noncomputable section

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ComplexOrder

namespace RHTower

/-- The centred completed function `X(W) = ξ(1/2 + W)`. -/
def xiCent (W : ℂ) : ℂ := xi (1 / 2 + W)

theorem xiCent_eq (W : ℂ) : xiCent W = xiTranslatedCentered 0 W := by
  rw [xiCent, xiTranslatedCentered, sub_zero]

theorem xiCent_analytic : AnalyticOnNhd ℂ xiCent Set.univ := by
  have := analyticOnNhd_xiTranslatedCentered 0
  intro z _
  have h := this z (Set.mem_univ z)
  refine h.congr ?_
  filter_upwards with u
  exact (xiCent_eq u).symm

theorem xiCent_differentiable : Differentiable ℂ xiCent :=
  fun z => (xiCent_analytic z (Set.mem_univ z)).differentiableAt

/-- On the Euler region the centred function has no zeros. -/
theorem xiCent_ne_zero_of_half_lt_re {W : ℂ} (hW : 1 / 2 < W.re) : xiCent W ≠ 0 := by
  intro h
  have hs : (1 : ℝ) < ((1 : ℂ) / 2 + W).re := by
    simp only [Complex.add_re, Complex.div_re, Complex.one_re, Complex.one_im]
    norm_num
    linarith
  have hne1 : (1 : ℂ) / 2 + W ≠ 1 := by
    intro h1
    rw [h1] at hs
    simp at hs
  have hzeta : riemannZeta ((1 : ℂ) / 2 + W) = 0 :=
    (xi_eq_zero_iff (by linarith) hne1).mp h
  exact riemannZeta_ne_zero_of_one_lt_re hs hzeta

/-- **The no-zero transfer.**  A positive Carathéodory kernel for the logarithmic derivative on a
sub-half-plane forbids zeros on the whole right half plane. -/
theorem ne_zero_of_isPSDKernel_caratheodory {Y : ℂ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hY : AnalyticOnNhd ℂ Y Set.univ)
    (hYne : ∀ W : ℂ, a < W.re → Y W ≠ 0)
    (hPSD : IsPSDKernel (fun x y : {W : ℂ // a < W.re} =>
      (logDeriv Y (x : ℂ) + conj (logDeriv Y (y : ℂ))) / ((x : ℂ) + conj (y : ℂ)))) :
    ∀ W : ℂ, 0 < W.re → Y W ≠ 0 := by
  haveI : Nonempty {W : ℂ // a < W.re} := ⟨⟨(a : ℂ) + 1, by simp⟩⟩
  obtain ⟨Gf, hGdiff, hGre, hGval⟩ :=
    exists_caratheodory_interpolant (fun x : {W : ℂ // a < W.re} => (x : ℂ))
      (fun x => logDeriv Y (x : ℂ))
      (fun x => lt_of_le_of_lt ha x.2) hPSD
  set Ω : Set ℂ := {z : ℂ | 0 < z.re} with hΩ
  have hΩopen : IsOpen Ω := isOpen_lt continuous_const Complex.continuous_re
  have hΩconv : Convex ℝ Ω := convex_halfSpace_re_gt 0
  have hΩconn : IsPreconnected Ω := hΩconv.isPreconnected
  have hGan : AnalyticOnNhd ℂ Gf Ω := hGdiff.analyticOnNhd hΩopen
  set h : ℂ → ℂ := fun W => deriv Y W - Gf W * Y W with hh
  have hhan : AnalyticOnNhd ℂ h Ω := by
    intro z hz
    exact ((hY z (Set.mem_univ z)).deriv).sub ((hGan z hz).mul (hY z (Set.mem_univ z)))
  have hzero : ∀ W : ℂ, a < W.re → h W = 0 := by
    intro W hW
    have hval : Gf W = logDeriv Y W := hGval ⟨W, hW⟩
    have hYW : Y W ≠ 0 := hYne W hW
    rw [hh]
    simp only [hval, logDeriv_apply]
    field_simp
    ring
  have hmem : ((a : ℂ) + 1) ∈ Ω := by
    have : a < ((a : ℂ) + 1).re := by simp
    exact lt_of_le_of_lt ha this
  have hev : h =ᶠ[𝓝 ((a : ℂ) + 1)] 0 := by
    have hopen : IsOpen {W : ℂ | a < W.re} := isOpen_lt continuous_const Complex.continuous_re
    have hin : ((a : ℂ) + 1) ∈ {W : ℂ | a < W.re} := by simp
    filter_upwards [hopen.mem_nhds hin] with u hu
    exact hzero u hu
  have hzeroΩ : Set.EqOn h 0 Ω :=
    hhan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hΩconn hmem hev
  have hrel : ∀ z ∈ Ω, deriv Y z = Gf z * Y z := by
    intro z hz
    have := hzeroΩ hz
    rw [hh] at this
    simpa using sub_eq_zero.mp this
  have hYw : Y ((a : ℂ) + 1) ≠ 0 := hYne _ (by simp)
  exact fun W hW => ne_zero_of_deriv_eq_mul hΩopen hΩconn
    (fun z _ => hY z (Set.mem_univ z)) hGan hrel hmem hYw W hW


/-! ## The shifted Loewner generator -/

/-- The shifted Loewner generator `H_ω` in centred coordinates. -/
def xiShiftGen (ω : ℝ) (W : ℂ) : ℂ := logDeriv xiCent (W - ω) + logDeriv xiCent (W + ω)

/-- The Loewner generator kernel `C_ω`, in centred coordinates. -/
def xiShiftGenKernel (ω : ℝ) (W V : ℂ) : ℂ :=
  (xiShiftGen ω W + conj (xiShiftGen ω V)) / (W + conj V)

/-- In the card's upper-half-plane coordinate `z`, with `W = -i z`, the Cauchy factor
`i / (z - conj w)` is exactly `1 / (W + conj V)`, so the generator kernel above is the card's
`C_ω`. -/
theorem xiShiftGenKernel_cardCoordinates (ω : ℝ) (z w : ℂ) :
    (Complex.I / (z - conj w)) *
        (xiShiftGen ω (-Complex.I * z) + conj (xiShiftGen ω (-Complex.I * w)))
      = xiShiftGenKernel ω (-Complex.I * z) (-Complex.I * w) := by
  have hden : -Complex.I * z + conj (-Complex.I * w) = -Complex.I * (z - conj w) := by
    simp only [map_mul, map_neg, Complex.conj_I]
    ring
  rw [xiShiftGenKernel, hden]
  rcases eq_or_ne (z - conj w) 0 with hz | hz
  · rw [hz]
    simp
  · have hIinv : Complex.I / (z - conj w) = (-Complex.I * (z - conj w))⁻¹ := by
      rw [mul_inv, inv_neg, Complex.inv_I, neg_neg, div_eq_mul_inv]
    rw [hIinv, div_eq_mul_inv, mul_comm]

/-- The centred function has nonzero values on the shifted Euler region, so the generator is the
logarithmic derivative of the shifted product. -/
def xiShiftProduct (ω : ℝ) (W : ℂ) : ℂ := xiCent (W - ω) * xiCent (W + ω)

theorem hasDerivAt_xiCent_shift (c : ℂ) (W : ℂ) :
    HasDerivAt (fun z : ℂ => xiCent (z + c)) (deriv xiCent (W + c)) W := by
  have h := (xiCent_differentiable (W + c)).hasDerivAt
  simpa using h.comp_add_const W c

theorem xiShiftProduct_analytic (ω : ℝ) : AnalyticOnNhd ℂ (xiShiftProduct ω) Set.univ := by
  intro z _
  have h1 : AnalyticAt ℂ (fun W : ℂ => xiCent (W - ω)) z :=
    (xiCent_analytic _ (Set.mem_univ _)).comp (by fun_prop)
  have h2 : AnalyticAt ℂ (fun W : ℂ => xiCent (W + ω)) z :=
    (xiCent_analytic _ (Set.mem_univ _)).comp (by fun_prop)
  exact h1.mul h2

theorem logDeriv_xiShiftProduct {ω : ℝ} {W : ℂ}
    (h1 : xiCent (W - ω) ≠ 0) (h2 : xiCent (W + ω) ≠ 0) :
    logDeriv (xiShiftProduct ω) W = xiShiftGen ω W := by
  have hd1 : HasDerivAt (fun z : ℂ => xiCent (z - ω)) (deriv xiCent (W - ω)) W := by
    have := hasDerivAt_xiCent_shift (-(ω : ℂ)) W
    simpa [sub_eq_add_neg] using this
  have hd2 : HasDerivAt (fun z : ℂ => xiCent (z + ω)) (deriv xiCent (W + ω)) W :=
    hasDerivAt_xiCent_shift (ω : ℂ) W
  have hprod : HasDerivAt (xiShiftProduct ω)
      (deriv xiCent (W - ω) * xiCent (W + ω) + xiCent (W - ω) * deriv xiCent (W + ω)) W := by
    have := hd1.mul hd2
    exact this
  rw [logDeriv_apply, hprod.deriv, xiShiftProduct, xiShiftGen, logDeriv_apply, logDeriv_apply]
  field_simp


/-! ## The critical generator criterion -/

theorem xiShiftGenKernel_zero_eq (W V : ℂ) :
    xiShiftGenKernel 0 W V
      = 2 * ((logDeriv xiCent W + conj (logDeriv xiCent V)) / (W + conj V)) := by
  rw [xiShiftGenKernel, xiShiftGen, xiShiftGen]
  simp only [Complex.ofReal_zero, sub_zero, add_zero, map_add]
  ring

theorem xiCent_ne_zero_iff_xi (W : ℂ) : xiCent W = xi (1 / 2 + W) := rfl

/-- **The critical generator is an exact RH criterion.**  Positivity of the critical Loewner
generator kernel on the Euler region is equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_iff_isPSDKernel_criticalGenerator :
    RiemannHypothesis ↔
      IsPSDKernel (fun x y : {W : ℂ // 1 / 2 < W.re} =>
        xiShiftGenKernel 0 (x : ℂ) (y : ℂ)) := by
  constructor
  · intro hRH
    -- from the imaginary-divisor Bezoutian of the centred function
    have hcrit : ∀ s : ℂ, xi s = 0 → s.re = 1 / 2 :=
      riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH
    have hcar : IsPSDKernel (fun x y : {W : ℂ // 1 / 2 < W.re} =>
        (logDeriv xiCent (x : ℂ) + conj (logDeriv xiCent (y : ℂ))) /
          ((x : ℂ) + conj (y : ℂ))) := by
      refine isPSDKernel_of_forall_posSemidef ?_ (fun n w => ?_)
      · intro x y
        rw [map_div₀, map_add, Complex.conj_conj, map_add, Complex.conj_conj]
        ring_nf
      · set W : Fin n → ℂ := fun j => ((w j : ℂ)) with hW
        have hpos : ∀ j, 0 < (W j).re := fun j => lt_trans (by norm_num) (w j).2
        have hne : ∀ j, xiCent (W j) ≠ 0 := fun j => xiCent_ne_zero_of_half_lt_re (w j).2
        have hbez := posSemidef_xiTranslatedBezoutian_of_critical hcrit W hpos
        have hcongr := posSemidef_congr_diagonal hbez (fun j => (xiCent (W j))⁻¹)
        have hEq : (Matrix.of fun j k : Fin n =>
              (logDeriv xiCent (W j) + conj (logDeriv xiCent (W k))) / (W j + conj (W k)))
            = Matrix.of fun j k : Fin n => (xiCent (W j))⁻¹ *
                xiTranslatedBezoutian 0 (W j) (W k) * conj ((xiCent (W k))⁻¹) := by
          ext j k
          rw [Matrix.of_apply, Matrix.of_apply, xiTranslatedBezoutian]
          have h1 : xiTranslatedCentered 0 (W j) = xiCent (W j) := (xiCent_eq _).symm
          have h2 : xiTranslatedCentered 0 (W k) = xiCent (W k) := (xiCent_eq _).symm
          have h3 : deriv (xiTranslatedCentered 0) = deriv xiCent := by
            congr 1
            funext u
            exact (xiCent_eq u).symm
          rw [h1, h2, h3, logDeriv_apply, logDeriv_apply, map_div₀, map_inv₀]
          have hkne : xiCent (W k) ≠ 0 := hne k
          have hjne : xiCent (W j) ≠ 0 := hne j
          have hcj : conj (xiCent (W k)) ≠ 0 := by
            simpa using (map_ne_zero (starRingEnd ℂ)).mpr hkne
          field_simp
        show (Matrix.of fun j k : Fin n =>
          (logDeriv xiCent (W j) + conj (logDeriv xiCent (W k))) / (W j + conj (W k))).PosSemidef
        rw [hEq]
        exact hcongr
    refine (hcar.const_mul (by norm_num : (0:ℝ) ≤ 2)).congr (fun x y => ?_)
    rw [xiShiftGenKernel_zero_eq]
    norm_num
  · intro hPSD
    have hcar : IsPSDKernel (fun x y : {W : ℂ // 1 / 2 < W.re} =>
        (logDeriv xiCent (x : ℂ) + conj (logDeriv xiCent (y : ℂ))) /
          ((x : ℂ) + conj (y : ℂ))) := by
      refine (hPSD.const_mul (by norm_num : (0:ℝ) ≤ 1/2)).congr (fun x y => ?_)
      rw [xiShiftGenKernel_zero_eq]
      push_cast
      ring
    have hno := ne_zero_of_isPSDKernel_caratheodory (by norm_num : (0:ℝ) ≤ 1/2)
      xiCent_analytic (fun W hW => xiCent_ne_zero_of_half_lt_re hW) hcar
    refine rh_iff_xi_ne_zero_right.mpr (fun s hs => ?_)
    have hre : 0 < (s - 1 / 2).re := by
      have := mem_rightHalf.mp hs
      simp only [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.one_im]
      norm_num
      linarith
    have := hno (s - 1 / 2) hre
    rwa [xiCent, show (1 : ℂ) / 2 + (s - 1 / 2) = s by ring] at this

/-- **No positive shift has a positive generator.** -/
theorem not_isPSDKernel_shiftGenerator {ω : ℝ} (hω : 0 < ω) :
    ¬ IsPSDKernel (fun x y : {W : ℂ // 1 / 2 + ω < W.re} =>
        xiShiftGenKernel ω (x : ℂ) (y : ℂ)) := by
  intro hPSD
  have hfac : ∀ W : ℂ, 1 / 2 + ω < W.re →
      xiCent (W - ω) ≠ 0 ∧ xiCent (W + ω) ≠ 0 := by
    intro W hW
    constructor
    · refine xiCent_ne_zero_of_half_lt_re ?_
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    · refine xiCent_ne_zero_of_half_lt_re ?_
      simp only [Complex.add_re, Complex.ofReal_re]
      linarith
  have hcar : IsPSDKernel (fun x y : {W : ℂ // 1 / 2 + ω < W.re} =>
      (logDeriv (xiShiftProduct ω) (x : ℂ) + conj (logDeriv (xiShiftProduct ω) (y : ℂ))) /
        ((x : ℂ) + conj (y : ℂ))) := by
    refine hPSD.congr (fun x y => ?_)
    rw [xiShiftGenKernel, logDeriv_xiShiftProduct (hfac _ x.2).1 (hfac _ x.2).2,
      logDeriv_xiShiftProduct (hfac _ y.2).1 (hfac _ y.2).2]
  have hno := ne_zero_of_isPSDKernel_caratheodory (by linarith : (0:ℝ) ≤ 1 / 2 + ω)
    (xiShiftProduct_analytic ω)
    (fun W hW => mul_ne_zero (hfac W hW).1 (hfac W hW).2) hcar
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ := exists_two_distinct_positive_real_XiC_zeros
  have hzero : xiShiftProduct ω ((ω : ℂ) + (a : ℝ) * Complex.I) = 0 := by
    rw [xiShiftProduct]
    have hleft : xiCent (((ω : ℂ) + (a : ℝ) * Complex.I) - ω) = 0 := by
      rw [show ((ω : ℂ) + (a : ℝ) * Complex.I) - ω = (a : ℝ) * Complex.I by ring]
      rw [xiCent]
      have : XiC ((a : ℝ) : ℂ) = xi (1 / 2 + (a : ℝ) * Complex.I) := rfl
      rw [← this]
      exact hza
    rw [hleft, zero_mul]
  have hre : 0 < ((ω : ℂ) + (a : ℝ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  exact hno _ hre hzero

end RHTower
