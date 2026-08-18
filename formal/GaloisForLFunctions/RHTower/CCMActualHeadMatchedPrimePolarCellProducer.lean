import GaloisForLFunctions.RHTower.CCMActualHeadSymmetricTransportRebate
import GaloisForLFunctions.RHTower.CCMActualHeadWallGramSignedProducer
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Mass-matched prime--polar cells on actual Gamma heads

This module converts every critical-Mellin atom into a literal symmetric cell of the outgoing
polar continuum without changing source or coefficient. For atom weight `w_n`, center
`s_n = log n`, and

`rho_n = 2 arsinh (w_n / (4 exp(s_n/2)))`,

the anchor part of the polar cell has mass exactly `w_n`. The coefficient-one transport law then
gives the unconditional atomwise signed producer

`w_n E_f(s_n) - integral_[s_n-rho_n,s_n+rho_n] exp(h/2) E_f(h) dh`
`  = integral_[0,rho_n] (joint rebate - offset debt - reflected sine current) dr`.

Here `E_f` is the translation defect of the same literal actual head. At every prime power, the
sole signed sine term is proved to be Suzuki's existing anti-diagonal wall current, tested by the
offset sine against that head's Fourier mass. Thus prime--polar--Gamma cancellation is preserved;
no surrogate clock, absolute transport, prime-gap estimate, RH premise, or extra logical premise
enters.

Finite assembly still has two hard tasks: control overlap/gaps of these exact cells and pay their
offset/current debts from the higher-Gamma and boundary channels.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace RHTower

def ccmActualHeadTranslationSineCurrent
    (s r : ℝ) (f : SoninL2) : ℝ :=
  ccmActualHeadTranslationDefect (s + r) f -
    ccmActualHeadTranslationDefect (s - r) f

theorem ccmActualHeadTranslationSineCurrent_eq_fourierIntegral
    (s r : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationSineCurrent s r f =
      ∫ xi : ℝ,
        4 * Real.sin (2 * Real.pi * s * xi) *
          Real.sin (2 * Real.pi * r * xi) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  let g : SoninL2 := fourierUnitary f
  have hfg : fourierUnitary.symm g = f := by
    dsimp only [g]
    exact fourierUnitary.symm_apply_apply f
  have hplus := integrable_ccmGammaCosineDefectSpectralDensity (s + r) g
  have hminus := integrable_ccmGammaCosineDefectSpectralDensity (s - r) g
  rw [← hfg]
  unfold ccmActualHeadTranslationSineCurrent
  rw [ccmActualHeadTranslationDefect_fourierUnitary_symm,
    ccmActualHeadTranslationDefect_fourierUnitary_symm,
    ← integral_sub hplus hminus]
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply integral_congr_ae
  filter_upwards with xi
  rw [show 2 * Real.pi * (s + r) * xi =
      2 * Real.pi * s * xi + 2 * Real.pi * r * xi by ring,
    show 2 * Real.pi * (s - r) * xi =
      2 * Real.pi * s * xi - 2 * Real.pi * r * xi by ring,
    Real.cos_add, Real.cos_sub]
  ring

theorem continuous_ccmActualHeadTranslationSineCurrent_right
    (s : ℝ) (f : SoninL2) :
    Continuous fun r : ℝ => ccmActualHeadTranslationSineCurrent s r f := by
  unfold ccmActualHeadTranslationSineCurrent
  have hE : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f := by
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  exact (hE.comp (continuous_const.add continuous_id)).sub
    (hE.comp (continuous_const.sub continuous_id))

theorem ccmActualHeadOutgoingPolar_pair_add_rebate
    (s r : ℝ) (f : SoninL2) :
    Real.exp ((s + r) / 2) * ccmActualHeadTranslationDefect (s + r) f +
        Real.exp ((s - r) / 2) * ccmActualHeadTranslationDefect (s - r) f +
        Real.exp (s / 2) * Real.cosh (r / 2) *
          ccmActualHeadSymmetricTransportRebate s r f =
      2 * Real.exp (s / 2) * Real.cosh (r / 2) *
          (ccmActualHeadTranslationDefect s f +
            ccmActualHeadTranslationDefect r f) +
        Real.exp (s / 2) * Real.sinh (r / 2) *
          ccmActualHeadTranslationSineCurrent s r f := by
  have hsum :=
    ccmActualHeadTranslationDefect_symmetric_pair_add_rebate s r f
  have hplus : Real.exp ((s + r) / 2) =
      Real.exp (s / 2) * (Real.cosh (r / 2) + Real.sinh (r / 2)) := by
    rw [show (s + r) / 2 = s / 2 + r / 2 by ring,
      Real.exp_add, Real.cosh_add_sinh]
  have hminus : Real.exp ((s - r) / 2) =
      Real.exp (s / 2) * (Real.cosh (r / 2) - Real.sinh (r / 2)) := by
    rw [show (s - r) / 2 = s / 2 + -(r / 2) by ring,
      Real.exp_add, Real.cosh_sub_sinh]
  rw [hplus, hminus]
  unfold ccmActualHeadTranslationSineCurrent
  linear_combination
    Real.exp (s / 2) * Real.cosh (r / 2) * hsum

/-- Literal outgoing polar mass on a symmetric log-cell. -/
def ccmActualHeadOutgoingPolarSymmetricCell
    (s ρ : ℝ) (f : SoninL2) : ℝ :=
  ∫ h in (s - ρ)..(s + ρ),
    Real.exp (h / 2) * ccmActualHeadTranslationDefect h f

theorem ccmActualHeadOutgoingPolarSymmetricCell_eq_pairIntegral
    (s ρ : ℝ) (f : SoninL2) :
    ccmActualHeadOutgoingPolarSymmetricCell s ρ f =
      ∫ r in (0 : ℝ)..ρ,
        (Real.exp ((s + r) / 2) *
            ccmActualHeadTranslationDefect (s + r) f +
          Real.exp ((s - r) / 2) *
            ccmActualHeadTranslationDefect (s - r) f) := by
  let F : ℝ → ℝ := fun h =>
    Real.exp (h / 2) * ccmActualHeadTranslationDefect h f
  have hE : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f := by
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  have hF : Continuous F := by
    dsimp only [F]
    fun_prop
  have hplus : IntervalIntegrable (fun r : ℝ => F (s + r)) volume 0 ρ :=
    (hF.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hminus : IntervalIntegrable (fun r : ℝ => F (s - r)) volume 0 ρ :=
    (hF.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  rw [ccmActualHeadOutgoingPolarSymmetricCell]
  change (∫ h in (s - ρ)..(s + ρ), F h) =
    ∫ r in (0 : ℝ)..ρ, F (s + r) + F (s - r)
  rw [intervalIntegral.integral_add hplus hminus,
    intervalIntegral.integral_comp_add_left,
    intervalIntegral.integral_comp_sub_left]
  simp only [add_zero, sub_zero]
  calc
    (∫ h in (s - ρ)..(s + ρ), F h) =
        (∫ h in (s - ρ)..s, F h) + ∫ h in s..(s + ρ), F h :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hF.intervalIntegrable (μ := volume) (s - ρ) s)
        (hF.intervalIntegrable (μ := volume) s (s + ρ))).symm
    _ = (∫ h in s..(s + ρ), F h) + ∫ h in (s - ρ)..s, F h :=
      add_comm _ _

/-- Exact symmetric polar radius carrying one von-Mangoldt atom's full mass. -/
def ccmActualHeadMatchedPrimePolarRadius (n : ℕ) : ℝ :=
  2 * Real.arsinh
    (criticalMellinAtomWeight n /
      (4 * Real.exp (Real.log n / 2)))

theorem ccmActualHeadMatchedPrimePolarRadius_nonneg (n : ℕ) :
    0 ≤ ccmActualHeadMatchedPrimePolarRadius n := by
  unfold ccmActualHeadMatchedPrimePolarRadius
  apply mul_nonneg (by norm_num)
  rw [Real.arsinh_nonneg_iff]
  exact div_nonneg (criticalMellinAtomWeight_nonneg n)
    (mul_nonneg (by norm_num) (Real.exp_pos _).le)

theorem integral_ccmActualHeadMatchedPrimePolar_anchor
    (n : ℕ) (f : SoninL2) :
    (∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
        2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          ccmActualHeadTranslationDefect (Real.log n) f) =
      criticalMellinAtomWeight n *
        ccmActualHeadTranslationDefect (Real.log n) f := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let C : ℝ := 2 * Real.exp (Real.log n / 2) *
    ccmActualHeadTranslationDefect (Real.log n) f
  let P : ℝ → ℝ := fun r =>
    C * (2 * Real.sinh (r / 2))
  have hderiv : ∀ r ∈ uIcc (0 : ℝ) ρ,
      HasDerivAt P
        (2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          ccmActualHeadTranslationDefect (Real.log n) f) r := by
    intro r hr
    have hbase0 := (((Real.hasDerivAt_sinh (r / 2)).comp r
      ((hasDerivAt_id r).div_const 2)).const_mul 2)
    have hbase : HasDerivAt (fun x : ℝ => 2 * Real.sinh (x / 2))
        (Real.cosh (r / 2)) r :=
      hbase0.congr_deriv (by ring)
    change HasDerivAt (fun x : ℝ => C * (2 * Real.sinh (x / 2))) _ r
    apply (hbase.const_mul C).congr_deriv
    dsimp only [C]
    ring
  have hint : IntervalIntegrable
      (fun r : ℝ =>
        2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
          ccmActualHeadTranslationDefect (Real.log n) f)
      volume 0 ρ := by
    exact (by fun_prop : Continuous fun r : ℝ =>
      2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
        ccmActualHeadTranslationDefect (Real.log n) f).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [P, C]
  simp only [zero_div, Real.sinh_zero, mul_zero, sub_zero]
  unfold ρ ccmActualHeadMatchedPrimePolarRadius
  rw [show (2 * Real.arsinh
      (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2)))) / 2 =
      Real.arsinh
        (criticalMellinAtomWeight n / (4 * Real.exp (Real.log n / 2))) by ring,
    Real.sinh_arsinh]
  field_simp [Real.exp_ne_zero]
  ring

/-- Prime-power specialization: the sole signed asymmetric current is Suzuki's literal
anti-diagonal wall current tested by the offset sine on the actual head spectrum. -/
theorem criticalMellinAtomWeight_mul_translationSineCurrent_primePower_eq_suzuki
    (r : ℝ) (f : SoninL2) (p : Nat.Primes) (e : ℕ) :
    criticalMellinAtomWeight (xiGammaEulerValuationNat (p, e)) *
        ccmActualHeadTranslationSineCurrent
          (Real.log (xiGammaEulerValuationNat (p, e))) r f =
      ∫ xi : ℝ,
        4 * (suzukiCriticalWallFieldGramKernel
              (2 * Real.pi * xi) (-(2 * Real.pi * xi)) p e).im *
          Real.sin (2 * Real.pi * r * xi) *
          ‖(fourierUnitary f : ℝ → ℂ) xi‖ ^ 2 := by
  rw [ccmActualHeadTranslationSineCurrent_eq_fourierIntegral,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with xi
  rw [(suzukiCriticalWallFieldGramKernel_antidiagonal_re_im
    (2 * Real.pi * xi) p e).2,
    criticalMellinAtomWeight_primePower_eq_sq_suzukiCriticalEntryWallBareAmplitude,
    sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt]
  have hsin :
      Real.sin (2 * Real.pi * Real.log (xiGammaEulerValuationNat (p, e)) * xi) =
        Real.sin (2 * Real.pi * xi *
          Real.log (xiGammaEulerValuationNat (p, e))) := by
    congr 1
    ring
  rw [hsin]
  ring

/-- Exact atomwise signed producer. Prime mass minus its literal mass-matched polar cell is the
joint same-head rebate, less the Gamma displacement cost and Suzuki reflected sine current. -/
theorem ccmActualHeadPrimeWeight_sub_matchedPolarCell_eq_signedResidual
    (n : ℕ) (f : SoninL2) :
    criticalMellinAtomWeight n *
          ccmActualHeadTranslationDefect (Real.log n) f -
        ccmActualHeadOutgoingPolarSymmetricCell
          (Real.log n) (ccmActualHeadMatchedPrimePolarRadius n) f =
      ∫ r in (0 : ℝ)..ccmActualHeadMatchedPrimePolarRadius n,
        (Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
            ccmActualHeadSymmetricTransportRebate (Real.log n) r f -
          2 * Real.exp (Real.log n / 2) * Real.cosh (r / 2) *
            ccmActualHeadTranslationDefect r f -
          Real.exp (Real.log n / 2) * Real.sinh (r / 2) *
            ccmActualHeadTranslationSineCurrent (Real.log n) r f) := by
  let ρ := ccmActualHeadMatchedPrimePolarRadius n
  let s := Real.log n
  have hE : Continuous fun h : ℝ => ccmActualHeadTranslationDefect h f := by
    unfold ccmActualHeadTranslationDefect
    exact (((continuous_logTranslationCLM f).sub continuous_const).norm).pow 2
  have hanchor : IntervalIntegrable (fun r : ℝ =>
      2 * Real.exp (s / 2) * Real.cosh (r / 2) *
        ccmActualHeadTranslationDefect s f) volume 0 ρ :=
    (by fun_prop : Continuous fun r : ℝ =>
      2 * Real.exp (s / 2) * Real.cosh (r / 2) *
        ccmActualHeadTranslationDefect s f).intervalIntegrable _ _
  have hpair : IntervalIntegrable (fun r : ℝ =>
      Real.exp ((s + r) / 2) * ccmActualHeadTranslationDefect (s + r) f +
        Real.exp ((s - r) / 2) * ccmActualHeadTranslationDefect (s - r) f)
      volume 0 ρ := by
    apply Continuous.intervalIntegrable
    exact ((Real.continuous_exp.comp
      ((continuous_const.add continuous_id).div_const 2)).mul
        (hE.comp (continuous_const.add continuous_id))).add
      ((Real.continuous_exp.comp
        ((continuous_const.sub continuous_id).div_const 2)).mul
          (hE.comp (continuous_const.sub continuous_id)))
  rw [← integral_ccmActualHeadMatchedPrimePolar_anchor n f,
    ccmActualHeadOutgoingPolarSymmetricCell_eq_pairIntegral,
    ← intervalIntegral.integral_sub hanchor hpair]
  apply intervalIntegral.integral_congr
  intro r hr
  have hid := ccmActualHeadOutgoingPolar_pair_add_rebate s r f
  dsimp only [s]
  linarith

end RHTower
