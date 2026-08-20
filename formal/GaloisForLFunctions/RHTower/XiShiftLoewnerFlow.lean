/-
# The Loewner flow of the shifted Xi Pick kernel

The shifted quotient `Θ_ω(W) = X(W - ω) / X(W + ω)` of the centred completed function has
logarithmic `ω`-derivative `-H_ω`, so the shifted Pick kernel

`S_ω(W,V) = (1 - Θ_ω(W) conj (Θ_ω V)) / (W + conj V)`

has `ω`-derivative `Θ_ω(W) conj (Θ_ω V) · C_ω(W,V)`.  Integrating from `Θ_0 = 1`, `S_0 = 0`
represents the endpoint kernel as a signed integral of congruences of the generator kernel.
-/
import GaloisForLFunctions.RHTower.XiShiftLoewnerCriticalGenerator
import GaloisForLFunctions.HTGeometry.IntegralMatrixPosSemidef

noncomputable section

open Complex Filter Topology intervalIntegral
open scoped ComplexConjugate ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The shifted quotient `Θ_ω`. -/
def xiShiftTheta (ω : ℝ) (W : ℂ) : ℂ := xiCent (W - ω) / xiCent (W + ω)

/-- The shifted Pick kernel `S_ω`. -/
def xiShiftPick (ω : ℝ) (W V : ℂ) : ℂ :=
  (1 - xiShiftTheta ω W * conj (xiShiftTheta ω V)) / (W + conj V)

@[simp] theorem xiShiftTheta_zero {W : ℂ} (hW : xiCent W ≠ 0) : xiShiftTheta 0 W = 1 := by
  rw [xiShiftTheta]
  simp only [Complex.ofReal_zero, sub_zero, add_zero]
  exact div_self hW

theorem xiShiftPick_zero {W V : ℂ} (hW : xiCent W ≠ 0) (hV : xiCent V ≠ 0) :
    xiShiftPick 0 W V = 0 := by
  rw [xiShiftPick, xiShiftTheta_zero hW, xiShiftTheta_zero hV]
  simp

/-- The real-parameter derivative of a shifted evaluation. -/
theorem hasDerivAt_ofReal_shift (W : ℂ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => W - (t : ℂ)) (-1) ω := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 ω := by
    simpa using (hasDerivAt_id ω).ofReal_comp
  simpa using h0.const_sub W

theorem hasDerivAt_ofReal_shift' (W : ℂ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => W + (t : ℂ)) 1 ω := by
  have h0 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 ω := by
    simpa using (hasDerivAt_id ω).ofReal_comp
  simpa using h0.const_add W

theorem hasDerivAt_xiCent_sub (W : ℂ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => xiCent (W - (t : ℂ))) (-deriv xiCent (W - ω)) ω := by
  have hg : HasDerivAt xiCent (deriv xiCent (W - (ω : ℂ))) (W - (ω : ℂ)) :=
    (xiCent_differentiable _).hasDerivAt
  have h := hg.scomp ω (hasDerivAt_ofReal_shift W ω)
  simpa [Function.comp_def] using h

theorem hasDerivAt_xiCent_add (W : ℂ) (ω : ℝ) :
    HasDerivAt (fun t : ℝ => xiCent (W + (t : ℂ))) (deriv xiCent (W + ω)) ω := by
  have hg : HasDerivAt xiCent (deriv xiCent (W + (ω : ℂ))) (W + (ω : ℂ)) :=
    (xiCent_differentiable _).hasDerivAt
  have h := hg.scomp ω (hasDerivAt_ofReal_shift' W ω)
  simpa [Function.comp_def] using h

/-- **The Loewner generator identity.**  The `ω`-derivative of the shifted quotient is minus the
generator times the quotient. -/
theorem hasDerivAt_xiShiftTheta {ω : ℝ} {W : ℂ}
    (h1 : xiCent (W - ω) ≠ 0) (h2 : xiCent (W + ω) ≠ 0) :
    HasDerivAt (fun t : ℝ => xiShiftTheta t W)
      (-(xiShiftGen ω W) * xiShiftTheta ω W) ω := by
  have hd := (hasDerivAt_xiCent_sub W ω).div (hasDerivAt_xiCent_add W ω) h2
  refine hd.congr_deriv ?_
  rw [xiShiftGen, xiShiftTheta, logDeriv_apply, logDeriv_apply]
  field_simp
  ring


/-- **The Loewner kernel identity.**  The `ω`-derivative of the shifted Pick kernel is the
congruence of the generator kernel by the shifted quotient. -/
theorem hasDerivAt_xiShiftPick {ω : ℝ} {W V : ℂ}
    (h1 : xiCent (W - ω) ≠ 0) (h2 : xiCent (W + ω) ≠ 0)
    (h3 : xiCent (V - ω) ≠ 0) (h4 : xiCent (V + ω) ≠ 0) :
    HasDerivAt (fun t : ℝ => xiShiftPick t W V)
      (xiShiftTheta ω W * conj (xiShiftTheta ω V) * xiShiftGenKernel ω W V) ω := by
  have hW := hasDerivAt_xiShiftTheta h1 h2
  have hV := hasDerivAt_xiShiftTheta h3 h4
  have hVc : HasDerivAt (fun t : ℝ => conj (xiShiftTheta t V))
      (conj (-(xiShiftGen ω V) * xiShiftTheta ω V)) ω := hV.star
  have hprod := hW.mul hVc
  have hnum : HasDerivAt (fun t : ℝ => 1 - xiShiftTheta t W * conj (xiShiftTheta t V))
      (-(-(xiShiftGen ω W) * xiShiftTheta ω W * conj (xiShiftTheta ω V) +
        xiShiftTheta ω W * conj (-(xiShiftGen ω V) * xiShiftTheta ω V))) ω :=
    hprod.const_sub 1
  have hdiv := hnum.div_const (W + conj V)
  refine hdiv.congr_deriv ?_
  rw [xiShiftGenKernel, map_mul, map_neg]
  ring


/-! ## The integral representation -/

theorem continuous_xiCent : Continuous xiCent := xiCent_differentiable.continuous

theorem continuous_deriv_xiCent : Continuous (deriv xiCent) := by
  have han : AnalyticOnNhd ℂ (deriv xiCent) Set.univ := fun z _ =>
    (xiCent_analytic z (Set.mem_univ z)).deriv
  have hdiff : Differentiable ℂ (deriv xiCent) :=
    fun z => (han z (Set.mem_univ z)).differentiableAt
  exact hdiff.continuous

theorem xiCent_ne_zero_shift {ω τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) ω) {W : ℂ}
    (hW : 1 / 2 + ω < W.re) : xiCent (W - τ) ≠ 0 ∧ xiCent (W + τ) ≠ 0 := by
  obtain ⟨hτ0, hτω⟩ := hτ
  constructor
  · refine xiCent_ne_zero_of_half_lt_re ?_
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  · refine xiCent_ne_zero_of_half_lt_re ?_
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith

theorem continuousOn_xiShiftFlowIntegrand {ω : ℝ} (hω : 0 ≤ ω) {W V : ℂ}
    (hW : 1 / 2 + ω < W.re) (hV : 1 / 2 + ω < V.re) :
    ContinuousOn (fun τ : ℝ =>
      xiShiftTheta τ W * conj (xiShiftTheta τ V) * xiShiftGenKernel τ W V) (Set.uIcc 0 ω) := by
  have huIcc : Set.uIcc (0 : ℝ) ω = Set.Icc 0 ω := Set.uIcc_of_le hω
  rw [huIcc]
  have hsub : ∀ U : ℂ, ContinuousOn (fun τ : ℝ => xiCent (U - τ)) (Set.Icc 0 ω) :=
    fun U => (continuous_xiCent.comp (by fun_prop)).continuousOn
  have hadd : ∀ U : ℂ, ContinuousOn (fun τ : ℝ => xiCent (U + τ)) (Set.Icc 0 ω) :=
    fun U => (continuous_xiCent.comp (by fun_prop)).continuousOn
  have hdsub : ∀ U : ℂ, ContinuousOn (fun τ : ℝ => deriv xiCent (U - τ)) (Set.Icc 0 ω) :=
    fun U => (continuous_deriv_xiCent.comp (by fun_prop)).continuousOn
  have hdadd : ∀ U : ℂ, ContinuousOn (fun τ : ℝ => deriv xiCent (U + τ)) (Set.Icc 0 ω) :=
    fun U => (continuous_deriv_xiCent.comp (by fun_prop)).continuousOn
  have hthetaW : ContinuousOn (fun τ : ℝ => xiShiftTheta τ W) (Set.Icc 0 ω) := by
    refine ContinuousOn.div (hsub W) (hadd W) (fun τ hτ => (xiCent_ne_zero_shift hτ hW).2)
  have hthetaV : ContinuousOn (fun τ : ℝ => xiShiftTheta τ V) (Set.Icc 0 ω) := by
    refine ContinuousOn.div (hsub V) (hadd V) (fun τ hτ => (xiCent_ne_zero_shift hτ hV).2)
  have hgenW : ContinuousOn (fun τ : ℝ => xiShiftGen τ W) (Set.Icc 0 ω) := by
    refine ContinuousOn.add ?_ ?_
    · exact ContinuousOn.div (hdsub W) (hsub W) (fun τ hτ => (xiCent_ne_zero_shift hτ hW).1)
    · exact ContinuousOn.div (hdadd W) (hadd W) (fun τ hτ => (xiCent_ne_zero_shift hτ hW).2)
  have hgenV : ContinuousOn (fun τ : ℝ => xiShiftGen τ V) (Set.Icc 0 ω) := by
    refine ContinuousOn.add ?_ ?_
    · exact ContinuousOn.div (hdsub V) (hsub V) (fun τ hτ => (xiCent_ne_zero_shift hτ hV).1)
    · exact ContinuousOn.div (hdadd V) (hadd V) (fun τ hτ => (xiCent_ne_zero_shift hτ hV).2)
  have hden : W + conj V ≠ 0 := by
    refine GaloisForLFunctions.HTGeometry.add_conj_ne_zero ?_ ?_ <;> linarith
  exact ((hthetaW.mul (Complex.continuous_conj.comp_continuousOn hthetaV)).mul
    ((hgenW.add (Complex.continuous_conj.comp_continuousOn hgenV)).div_const _))

set_option maxHeartbeats 1000000 in
/-- **The Loewner integral representation.**  On the Euler region the shifted Pick kernel is the
integral of the congruences of the generator kernel along the shift segment. -/
theorem xiShiftPick_eq_integral {ω : ℝ} (hω : 0 ≤ ω) {W V : ℂ}
    (hW : 1 / 2 + ω < W.re) (hV : 1 / 2 + ω < V.re) :
    xiShiftPick ω W V
      = ∫ τ in (0 : ℝ)..ω, xiShiftTheta τ W * conj (xiShiftTheta τ V) * xiShiftGenKernel τ W V := by
  have huIcc : Set.uIcc (0 : ℝ) ω = Set.Icc 0 ω := Set.uIcc_of_le hω
  have hderiv : ∀ τ ∈ Set.uIcc (0 : ℝ) ω,
      HasDerivAt (fun t : ℝ => xiShiftPick t W V)
        (xiShiftTheta τ W * conj (xiShiftTheta τ V) * xiShiftGenKernel τ W V) τ := by
    intro τ hτ
    rw [huIcc] at hτ
    exact hasDerivAt_xiShiftPick (xiCent_ne_zero_shift hτ hW).1 (xiCent_ne_zero_shift hτ hW).2
      (xiCent_ne_zero_shift hτ hV).1 (xiCent_ne_zero_shift hτ hV).2
  have hint : IntervalIntegrable
      (fun τ : ℝ => xiShiftTheta τ W * conj (xiShiftTheta τ V) * xiShiftGenKernel τ W V)
      MeasureTheory.volume 0 ω :=
    (continuousOn_xiShiftFlowIntegrand hω hW hV).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have h0 : xiShiftPick 0 W V = 0 := by
    refine xiShiftPick_zero ?_ ?_
    · refine xiCent_ne_zero_of_half_lt_re ?_
      linarith
    · refine xiCent_ne_zero_of_half_lt_re ?_
      linarith
  rw [h0, sub_zero]


/-! ## The finite-matrix positive integration law -/

set_option maxHeartbeats 1000000 in
/-- **The positive integration law.**  If the generator kernel is positive semidefinite at every
shift of the segment, then the endpoint Pick kernel is positive semidefinite. -/
theorem posSemidef_xiShiftPickMatrix {ω : ℝ} (hω : 0 ≤ ω) {n : ℕ} (Z : Fin n → ℂ)
    (hZ : ∀ j, 1 / 2 + ω < (Z j).re)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) ω,
      (Matrix.of fun j k => xiShiftGenKernel τ (Z j) (Z k)).PosSemidef) :
    (Matrix.of fun j k => xiShiftPick ω (Z j) (Z k)).PosSemidef := by
  classical
  set D : ℝ → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    Matrix.of fun j k =>
      xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) * xiShiftGenKernel τ (Z j) (Z k) with hD
  set Kf : ℝ → Matrix (Fin n) (Fin n) ℂ :=
    fun τ => if τ ∈ Set.Ioc (0 : ℝ) ω then D τ else 0 with hKf
  have happ : ∀ (τ : ℝ) (j k : Fin n), Kf τ j k
      = if τ ∈ Set.Ioc (0 : ℝ) ω then
          xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) * xiShiftGenKernel τ (Z j) (Z k)
        else 0 := by
    intro τ j k
    show (if τ ∈ Set.Ioc (0 : ℝ) ω then D τ else 0) j k = _
    split_ifs with h
    · rfl
    · rfl
  have hDpsd : ∀ τ ∈ Set.Icc (0 : ℝ) ω, (D τ).PosSemidef := by
    intro τ hτ
    have h := posSemidef_congr_diagonal (hgen τ hτ) (fun j => xiShiftTheta τ (Z j))
    have heq : (Matrix.of fun j k => xiShiftTheta τ (Z j) *
        (Matrix.of fun j k => xiShiftGenKernel τ (Z j) (Z k)) j k *
        conj (xiShiftTheta τ (Z k))) = D τ := by
      ext j k
      simp only [hD, Matrix.of_apply]
      ring
    rw [heq] at h
    exact h
  have hKpsd : ∀ τ : ℝ, (Kf τ).PosSemidef := by
    intro τ
    show (if τ ∈ Set.Ioc (0 : ℝ) ω then D τ else 0).PosSemidef
    split_ifs with hτ
    · exact hDpsd τ ⟨le_of_lt hτ.1, hτ.2⟩
    · exact Matrix.PosSemidef.zero
  have hentryInt : ∀ j k, MeasureTheory.Integrable (fun τ => Kf τ j k) MeasureTheory.volume := by
    intro j k
    have hcont := continuousOn_xiShiftFlowIntegrand hω (hZ j) (hZ k)
    have hii : IntervalIntegrable
        (fun τ : ℝ => xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) *
          xiShiftGenKernel τ (Z j) (Z k)) MeasureTheory.volume 0 ω := hcont.intervalIntegrable
    have hon : MeasureTheory.IntegrableOn
        (fun τ : ℝ => xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) *
          xiShiftGenKernel τ (Z j) (Z k)) (Set.Ioc 0 ω) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hω).mp hii
    have hind := hon.integrable_indicator measurableSet_Ioc
    refine hind.congr (Filter.Eventually.of_forall fun τ => ?_)
    show Set.indicator (Set.Ioc (0 : ℝ) ω)
      (fun τ => xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) *
        xiShiftGenKernel τ (Z j) (Z k)) τ = Kf τ j k
    rw [happ τ j k, Set.indicator]
    congr 1
  have hEntry : ∀ j k, (∫ τ, Kf τ j k) = xiShiftPick ω (Z j) (Z k) := by
    intro j k
    have hrep := xiShiftPick_eq_integral hω (hZ j) (hZ k)
    have hcont := continuousOn_xiShiftFlowIntegrand hω (hZ j) (hZ k)
    have hii : IntervalIntegrable
        (fun τ : ℝ => xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) *
          xiShiftGenKernel τ (Z j) (Z k)) MeasureTheory.volume 0 ω := hcont.intervalIntegrable
    have hon : MeasureTheory.IntegrableOn
        (fun τ : ℝ => xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) *
          xiShiftGenKernel τ (Z j) (Z k)) (Set.Ioc 0 ω) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hω).mp hii
    have hswap : (∫ τ, Kf τ j k) = ∫ τ in Set.Ioc (0 : ℝ) ω,
        xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) * xiShiftGenKernel τ (Z j) (Z k) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
      show Kf τ j k = Set.indicator (Set.Ioc (0 : ℝ) ω)
        (fun τ => xiShiftTheta τ (Z j) * conj (xiShiftTheta τ (Z k)) *
          xiShiftGenKernel τ (Z j) (Z k)) τ
      rw [happ τ j k, Set.indicator]
      congr 1
    rw [hswap, ← intervalIntegral.integral_of_le hω, ← hrep]
  have hpsd := GaloisForLFunctions.HTGeometry.posSemidef_integral_matrix
    MeasureTheory.volume Kf hentryInt hKpsd
  have hfin : (Matrix.of fun j k => ∫ τ, Kf τ j k)
      = Matrix.of fun j k => xiShiftPick ω (Z j) (Z k) := by
    ext j k
    rw [Matrix.of_apply, Matrix.of_apply, hEntry]
  rw [hfin] at hpsd
  exact hpsd

end RHTower
