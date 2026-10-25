import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerSourceIntersectionSurface
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerHalfDensityL1Completion

/-!
# Invariant absolute trace majorants force criticality

Two actual point sources recover both components of every Mellin evaluation from
the real mixed trace. Any finite nonnegative invariant majorant of that trace
therefore gives an invariant evaluation gauge. No norm or quotient descent is needed.
-/

noncomputable section
open Complex Zeta23 RHTower ContinuousLinearMap
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

theorem meyerCenteredSourceFlow_mellin (c : ℝ) (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogCenteredFlow c g) s =
      Complex.exp ((c : ℂ) * (s - 1 / 2)) * deningerMeyerStrongLogMellin g s := by
  change deningerMeyerStrongLogMellinLM s
    (Complex.exp (-(c : ℂ) / 2) • deningerMeyerStrongLogFlow c g) = _
  rw [map_smul]
  change Complex.exp (-(c : ℂ) / 2) *
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogFlow c g) s = _
  rw [deningerMeyerStrongLogMellin_flow, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem sharp_sq (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceSharp (deningerMeyerSourceSharp g) = g := by
  simp only [deningerMeyerSourceSharp, deningerMeyerStrongLogConj_J,
    deningerMeyerStrongLogConj_sq, deningerMeyerStrongLogJ_sq]

private theorem point_trace_reading (g : DeningerMeyerStrongLogTarget)
    (rho : XiDivisorSupport) (a : ℂ) :
    meyerSourceTrace g (deningerMeyerSourceSharp (a • meyerPointSource rho)) =
      (a * ((xiSupportMultiplicity rho : ℂ) * deningerMeyerStrongLogMellin g (rho : ℂ))).re := by
  rw [meyerSourceTrace, sharp_sq, meyerPointSource_product_trace]

/-- Two fixed point sources turn an absolute mixed-trace bound into evaluation control. -/
theorem meyerEvaluation_bounded_of_trace_majorant
    (Φ : DeningerMeyerStrongLogTarget → ℝ) (hnn : ∀ g, 0 ≤ Φ g)
    (hbound : ∀ g h, meyerSourceTrace g h ^ 2 ≤ Φ g * Φ h) (rho : XiDivisorSupport) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : DeningerMeyerStrongLogTarget,
      ‖deningerMeyerStrongLogMellin g (rho : ℂ)‖ ≤ C * (Φ g + 1) := by
  let h0 := deningerMeyerSourceSharp ((1 : ℂ) • meyerPointSource rho)
  let h1 := deningerMeyerSourceSharp (I • meyerPointSource rho)
  let K := Φ h0 + Φ h1
  have hK : 0 ≤ K := add_nonneg (hnn h0) (hnn h1)
  refine ⟨K + 1, by linarith only [hK], ?_⟩
  intro g
  let z := deningerMeyerStrongLogMellin g (rho : ℂ)
  let m : ℝ := xiSupportMultiplicity rho
  have hm : 1 ≤ m := by
    exact_mod_cast (show 1 ≤ xiSupportMultiplicity rho from xiSupportMultiplicity_pos rho)
  have hr : meyerSourceTrace g h0 = m * z.re := by
    rw [point_trace_reading]
    simp only [one_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero]
    rfl
  have hi : meyerSourceTrace g h1 = -(m * z.im) := by
    rw [point_trace_reading]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.natCast_re, Complex.natCast_im, zero_mul, one_mul, zero_add, sub_zero, zero_sub]
    rfl
  have h0b := hbound g h0
  have h1b := hbound g h1
  rw [hr] at h0b
  rw [hi] at h1b
  have hz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hsum : m ^ 2 * ‖z‖ ^ 2 ≤ Φ g * K := by
    dsimp only [K]
    rw [hz]
    nlinarith only [h0b, h1b]
  have hm2 : 1 ≤ m ^ 2 := by nlinarith only [hm]
  have hsmall := mul_le_mul_of_nonneg_right hm2 (sq_nonneg ‖z‖)
  have hs : ‖z‖ ^ 2 ≤ Φ g * K := by
    simpa only [one_mul] using hsmall.trans hsum
  have hu : ‖z‖ ≤ ‖z‖ ^ 2 + 1 := by nlinarith only [sq_nonneg (‖z‖ - 1 / 2)]
  have hn := hnn g
  change ‖z‖ ≤ (K + 1) * (Φ g + 1)
  nlinarith only [hs, hu, hn, hK]

/-- Invariance of an absolute majorant forces every Xi point onto the critical line. -/
theorem meyer_trace_majorant_invariant_forces_criticality
    (Φ : DeningerMeyerStrongLogTarget → ℝ) (hnn : ∀ g, 0 ≤ Φ g)
    (hbound : ∀ g h, meyerSourceTrace g h ^ 2 ≤ Φ g * Φ h)
    (hinv : ∀ c g, Φ (deningerMeyerStrongLogCenteredFlow c g) = Φ g) : RiemannHypothesis := by
  have hline (rho : XiDivisorSupport) : (rho : ℂ).re = 1 / 2 := by
    let E := deningerMeyerStrongLogMellinLM (rho : ℂ)
    have hE : E ≠ 0 := by
      intro he
      have hz := congrArg (fun L : DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ =>
        L (meyerPointSource rho)) he
      change deningerMeyerStrongLogMellin (meyerPointSource rho) (rho : ℂ) = 0 at hz
      rw [meyerPointSource_values, if_pos rfl] at hz
      exact one_ne_zero hz
    obtain ⟨C, hC, hb⟩ := meyerEvaluation_bounded_of_trace_majorant Φ hnn hbound rho
    have hz := re_eq_zero_of_invariantGauge_bounded_eigenfunctional
      deningerMeyerStrongLogCenteredFlow E hE (fun g => Φ g + 1)
      (fun g => by linarith only [hnn g])
      (fun c g => by rw [hinv]) ⟨C, hC, hb⟩ ((rho : ℂ) - 1 / 2)
      (fun c g => meyerCenteredSourceFlow_mellin c g (rho : ℂ))
    simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re] at hz
    linarith only [hz]
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  exact (ne_of_gt (mem_rightHalf.mp hz))
    (hline ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩)

/-- Centered flow cancels exactly in the literal mixed arithmetic sharp product. -/
theorem meyerSourceConvolution_centered_flow_sharp
    (c : ℝ) (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceConvolution (deningerMeyerStrongLogCenteredFlow c g)
      (deningerMeyerSourceSharp (deningerMeyerStrongLogCenteredFlow c h)) =
        deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  rw [deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin,
    meyerCenteredSourceFlow_mellin, meyerCenteredSourceFlow_mellin,
    deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin]
  have hh : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have he : (c : ℂ) * (s - 1 / 2) +
      conj ((c : ℂ) * (conj (1 - s) - 1 / 2)) = 0 := by
    simp only [map_mul, map_sub, map_one, Complex.conj_ofReal, Complex.conj_conj, hh]
    ring
  change Complex.exp ((c : ℂ) * (s - 1 / 2)) * deningerMeyerStrongLogMellin g s *
    conj (Complex.exp ((c : ℂ) * (conj (1 - s) - 1 / 2)) *
      deningerMeyerStrongLogMellin h (conj (1 - s))) = _
  rw [map_mul, ← Complex.exp_conj]
  calc
    _ = (Complex.exp ((c : ℂ) * (s - 1 / 2)) *
          Complex.exp (conj ((c : ℂ) * (conj (1 - s) - 1 / 2)))) *
        (deningerMeyerStrongLogMellin g s * conj (deningerMeyerStrongLogMellin h (conj (1 - s)))) := by ring
    _ = _ := by rw [← Complex.exp_add, he, Complex.exp_zero, one_mul]; rfl

/-- Every reading of the literal sharp product is invariant, independently of linearity or descent. -/
theorem meyerSourceProductReading_centered_flow {A : Type*}
    (d : DeningerMeyerStrongLogTarget → A) (c : ℝ) (g h : DeningerMeyerStrongLogTarget) :
    d (deningerMeyerSourceConvolution (deningerMeyerStrongLogCenteredFlow c g)
      (deningerMeyerSourceSharp (deningerMeyerStrongLogCenteredFlow c h))) =
        d (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h)) := by
  rw [meyerSourceConvolution_centered_flow_sharp]

/-- Centered flow preserves the original indefinite trace before any positivity hypothesis. -/
theorem meyerSourceTrace_centered_flow (c : ℝ) (g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace (deningerMeyerStrongLogCenteredFlow c g) (deningerMeyerStrongLogCenteredFlow c h) =
      meyerSourceTrace g h := by
  rw [meyerSourceTrace_eq_degree_product, meyerSourceTrace_eq_degree_product,
    meyerSourceConvolution_centered_flow_sharp]

/-- Invariant absolute trace majorants exist precisely under RH, with no norm or descent axioms. -/
theorem exists_invariant_meyer_trace_majorant_iff :
    (∃ Φ : DeningerMeyerStrongLogTarget → ℝ,
      (∀ g, 0 ≤ Φ g) ∧
      (∀ g h, meyerSourceTrace g h ^ 2 ≤ Φ g * Φ h) ∧
      ∀ c g, Φ (deningerMeyerStrongLogCenteredFlow c g) = Φ g) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨Φ, hnn, hb, hi⟩
    exact meyer_trace_majorant_invariant_forces_criticality Φ hnn hb hi
  · intro hRH
    refine ⟨fun g => meyerSourceTrace g g,
      meyerSourceTrace_nonneg_iff_riemannHypothesis.mpr hRH, ?_,
      fun c g => meyerSourceTrace_centered_flow c g g⟩
    intro g h
    have hb := meyerScalingSurface.defect_sq_le_of_hodgeIndex
      (meyerScalingSurface_hodgeIndex_iff.mpr hRH) (0, 0, g) (0, 0, h)
    simpa only [meyerScalingSurface_defect] using hb

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerEvaluation_bounded_of_trace_majorant
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyer_trace_majorant_invariant_forces_criticality
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSourceConvolution_centered_flow_sharp
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSourceProductReading_centered_flow
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_invariant_meyer_trace_majorant_iff
