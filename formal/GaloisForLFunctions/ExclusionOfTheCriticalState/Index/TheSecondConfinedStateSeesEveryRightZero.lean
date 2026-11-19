import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.EveryConfinedEigenspaceIsSimple
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.EveryConfinedStateHasAnAbsoluteZeroModeExpansion
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CriticalTerminalWallEnergy
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# The second confined state sees every right zero

At a nonreal right Laplace zero the real and imaginary parts of the causal
resolvent give a negative plane at the state's own ratio. The undamped
primitive pairs with its negative derivative by minus four times its
confinement mass. Applying this identity at conjugate coefficients gives
strict negativity on the entire plane. At the second crossing no such plane
exists, independently of the size of the off-line zero set.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23 FourierTransform
open scoped Convolution
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations CriticalArithmeticCorrelationTheory
  ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-! ### The real components of the damped resolvent -/

/-- The real component selected by c from the causal resolvent of a real profile. -/
def resolventComponent (a b : ℝ) (c : ℂ) (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  (c * modulatedCausalConvolution a b (cx F) u).re

private theorem laplace_conjugate_zero {a b : ℝ} {F : ℝ → ℝ}
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) :
    negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a (-b)) = 0 := by
  have h := negativeHalfLineLaplace_real_conj F (modulatedLaplaceRate a b)
  change negativeHalfLineLaplace (fun u => (F u : ℂ)) (modulatedLaplaceRate a b) = 0 at hz
  rw [conj_modulatedLaplaceRate, hz, map_zero] at h
  exact h

private theorem support_cx {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) (u : ℝ) (hu : 0 ≤ u) :
    cx F u = 0 := by
  change (F u : ℂ) = 0
  rw [hF.support u hu, Complex.ofReal_zero]

private theorem two_mul_real (z : ℂ) : 2*(z.re : ℂ) = z + (starRingEnd ℂ) z := by
  apply Complex.ext <;> simp [two_mul]

private theorem laplace_two_components {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0)
    (c : ℂ) {q : ℂ} (hq : |q.re| ≤ 1/2) :
    2 * negativeHalfLineLaplace (cx (resolventComponent a b c F)) q =
      c * negativeHalfLineLaplace (modulatedCausalConvolution a b (cx F)) q +
      (starRingEnd ℂ) c * negativeHalfLineLaplace (modulatedCausalConvolution a (-b) (cx F)) q := by
  let K := fun t => modulatedCausalConvolution a t (cx F)
  have hadm (t : ℝ) (ht : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a t) = 0) :
      Integrable (fun u : ℝ => Complex.exp (q * u) * modulatedCausalConvolution a t (cx F) u) :=
    integrable_complexLaplaceWeighted_of_halfLine_memLp hq
      (memLp_modulatedCausalConvolution ha t hF.memLp_complex)
      (memLp_weighted_modulatedCausalConvolution (add_pos ha (by positivity)) t hF.memLp_weightedComplex)
      (modulatedCausalConvolution_support_of_laplace_zero a t (support_cx hF) ht)
  have hc := conj_modulatedCausalConvolution a b (cx F)
  rw [show (fun u => (starRingEnd ℂ) (cx F u)) = cx F from funext fun u => Complex.conj_ofReal _] at hc
  unfold negativeHalfLineLaplace
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hadm b hz).const_mul c) ((hadm (-b) (laplace_conjugate_zero hz)).const_mul _)]
  apply integral_congr_ae
  refine Eventually.of_forall fun u => ?_
  change 2 * (Complex.exp (q * u) * (((c * K b u).re : ℝ) : ℂ)) =
    c * (Complex.exp (q * u) * K b u) + (starRingEnd ℂ) c * (Complex.exp (q * u) * K (-b) u)
  have hconj : (starRingEnd ℂ) (K b u) = K (-b) u := congrFun hc u
  have hreal : 2 * (((c*K b u).re : ℝ) : ℂ) =
      c*K b u + (starRingEnd ℂ) c * K (-b) u := by rw [two_mul_real, map_mul, hconj]
  linear_combination (Complex.exp (q * u)) * hreal

/-- Multiplication by a Laplace argument takes each real resolvent component
to another component minus the corresponding multiple of the input. -/
theorem laplace_mul_resolventComponent {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0)
    (c : ℂ) {q : ℂ} (hq : |q.re| ≤ 1/2) :
    q * negativeHalfLineLaplace (cx (resolventComponent a b c F)) q =
      negativeHalfLineLaplace (cx (resolventComponent a b (modulatedLaplaceRate a b * c) F)) q -
        (Real.pi : ℂ) * (c.re : ℂ) * negativeHalfLineLaplace (cx F) q := by
  have hmul (t : ℝ) (ht : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a t) = 0) :
      (modulatedLaplaceRate a t - q) * negativeHalfLineLaplace (modulatedCausalConvolution a t (cx F)) q =
        (Real.pi : ℂ) * negativeHalfLineLaplace (cx F) q := by
    rw [modulatedCausalConvolution, modulatedCausalExponential_eq_complexRate]
    apply negativeHalfLineLaplace_causalConvolution_mul
      (by simpa [modulatedLaplaceRate] using mul_pos Real.pi_pos ha)
      (hF.integrable.ofReal (𝕜 := ℂ)) (support_cx hF) ht
    exact integrable_complexLaplaceWeighted_of_halfLine_memLp hq hF.memLp_complex
      hF.memLp_weightedComplex (support_cx hF)
  have h₁ := laplace_two_components ha hF hz c hq
  have h₂ := laplace_two_components ha hF hz (modulatedLaplaceRate a b * c) hq
  rw [map_mul, conj_modulatedLaplaceRate] at h₂
  linear_combination q/2*h₁ - (1/2)*h₂ - c/2*(hmul b hz) -
    (starRingEnd ℂ) c/2*(hmul (-b) (laplace_conjugate_zero hz)) +
    ((Real.pi : ℂ) * negativeHalfLineLaplace (cx F) q/2)*(two_mul_real c)

private theorem resolventComponent_integrable {a : ℝ} (ha : 0 < a) (b : ℝ) (c : ℂ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Integrable (resolventComponent a b c F) :=
  ((integrable_modulatedCausalConvolution ha b (hF.integrable.ofReal (𝕜 := ℂ))).const_mul c).re

private theorem paperFT_at_imaginary_argument (F : ℝ → ℝ) (r : ℝ) :
    paperFT (cx F) r = negativeHalfLineLaplace (cx F) (Complex.I * r) := by
  apply integral_congr_ae
  exact Eventually.of_forall fun u => mul_comm _ _

/-- Every component has one full power of Fourier decay. -/
theorem exists_linear_decay_resolventComponent {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) (c : ℂ) :
    ∃ M : ℝ, ∀ r : ℝ, (1 + |r|) * ‖paperFT (cx (resolventComponent a b c F)) r‖ ≤ M := by
  let U := resolventComponent a b c F
  let V := resolventComponent a b (modulatedLaplaceRate a b * c) F
  refine ⟨(∫ u, |U u|) + (∫ u, |V u|) + (Real.pi * |c.re|) * ∫ u, |F u|, fun r => ?_⟩
  have h := laplace_mul_resolventComponent ha hF hz c (q := Complex.I * r)
    (by simp [Complex.mul_re])
  change Complex.I * (r : ℂ) * negativeHalfLineLaplace (cx U) _ =
    negativeHalfLineLaplace (cx V) _ - _ at h
  simp only [← paperFT_at_imaginary_argument] at h
  have hb := (congrArg norm h).le.trans (norm_sub_le _ _)
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos] at hb
  have ht := mul_le_mul_of_nonneg_left (norm_paperFT_le F r)
    (mul_nonneg Real.pi_pos.le (abs_nonneg c.re))
  change (1+|r|) * ‖paperFT (cx U) r‖ ≤ _
  simp only [Real.norm_eq_abs] at ht
  have hu := norm_paperFT_le U r
  have hv := norm_paperFT_le V r
  simp only [Real.norm_eq_abs] at hu hv
  linarith only [hb, ht, hu, hv]

private theorem integrable_square_component (c : ℂ) {f : ℝ → ℂ} (h : MemLp f 2 volume) :
    Integrable (fun u => (c*f u).re ^ 2) := by
  have hm := h.const_mul c
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  apply hi.mono' ((Complex.continuous_re.comp_aestronglyMeasurable hm.aestronglyMeasurable).pow 2)
  refine Eventually.of_forall fun u => ?_
  change ‖(c*f u).re ^ 2‖ ≤ ‖c*f u‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith only [sq_nonneg (c*f u).im]

/-- Cancellation at a right Laplace zero makes every real component of its
resolvent an admissible half-line test, including its gamma energy. -/
theorem domain_resolventComponent {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0) (c : ℂ) :
    CriticalHalfLineEnergyDomain (resolventComponent a b c F) := by
  let K := modulatedCausalConvolution a b (cx F)
  have hKm : Measurable K := measurable_modulatedCausalConvolution a b
    (Complex.continuous_ofReal.measurable.comp hF.meas)
  have hK := memLp_modulatedCausalConvolution ha b hF.memLp_complex
  have hw := memLp_weighted_modulatedCausalConvolution
    (a := a) (x := 4/Real.pi) (add_pos ha (by positivity)) b hF.memLp_weightedComplex
  have hs := modulatedCausalConvolution_support_of_laplace_zero a b (support_cx hF) hz
  have hU := resolventComponent_integrable ha b c hF
  refine ⟨Complex.continuous_re.measurable.comp (measurable_const.mul hKm), hU,
    integrable_square_component c hK, ?_, ?_, ?_⟩
  · apply (integrable_square_component c hw).congr
    refine Eventually.of_forall fun u => ?_
    have he₁ : Complex.exp (-(Real.pi*(4/Real.pi)*u : ℝ)) = (Real.exp (-(4*u)) : ℂ) := by
      rw [show Real.pi*(4/Real.pi) = 4 by field_simp [Real.pi_ne_zero],
        ← Complex.ofReal_neg, ← Complex.ofReal_exp]
    have he₂ : Real.exp (-(8*u)) = Real.exp (-(4*u))^2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    change (c * causalLaplaceWeighted (4/Real.pi) K u).re^2 = (c*K u).re^2 * Real.exp (-(8*u))
    rw [causalLaplaceWeighted, he₁, he₂, mul_left_comm c]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  · intro u hu
    change (c * modulatedCausalConvolution a b (cx F) u).re = 0
    rw [hs u hu, mul_zero, Complex.zero_re]
  · obtain ⟨M, hM⟩ := exists_linear_decay_resolventComponent ha hF hz c
    exact integrable_gammaEnergy_of_linear_decay (continuous_paperFT_cx hU) hM

#print axioms laplace_mul_resolventComponent
#print axioms domain_resolventComponent

/-! ### A primitive and its confined pairing -/

private theorem zero_resolvent_of_laplace_factor {J U : ℝ → ℝ}
    (hJ : CriticalHalfLineEnergyDomain J) (hU : CriticalHalfLineEnergyDomain U)
    (hJU : ∀ z : ℂ, |z.re| ≤ 1/2 →
      negativeHalfLineLaplace (cx J) z = z * negativeHalfLineLaplace (cx U) z) :
    modulatedCausalConvolution 0 0 (cx J) =ᵐ[volume] fun u => -(Real.pi : ℂ) * cx U u := by
  let K := modulatedCausalConvolution 0 0 (cx J)
  let G := fun u => -(Real.pi : ℂ) * cx U u
  have hrate : modulatedLaplaceRate 0 0 = 0 := by simp [modulatedLaplaceRate]
  have hz : negativeHalfLineLaplace (cx J) (modulatedLaplaceRate 0 0) = 0 := by
    rw [hrate, hJU 0 (by norm_num), zero_mul]
  have hs (u : ℝ) (hu : 0 ≤ u) : cx J u = 0 := by
    change (J u : ℂ) = 0
    rw [hJ.support u hu, Complex.ofReal_zero]
  have hm : Measurable (cx J) := Complex.continuous_ofReal.measurable.comp hJ.meas
  have hK : Integrable K := (undampedCausalConvolution_memLp_and_integrable
    0 hm hJ.memLp_weightedComplex hs hz).2
  have hG : Integrable G := (hU.integrable.ofReal (𝕜 := ℂ)).const_mul _
  have hfi := hJ.integrable.ofReal (𝕜 := ℂ)
  apply _root_.HTGeometry.ae_eq_of_fourierIntegral_eq hK hG
  refine (dense_compl_singleton (0 : ℝ)).induction ?_
    (isClosed_eq (continuous_fourier_of_integrable' hK) (continuous_fourier_of_integrable' hG))
  intro ξ hξ
  change ξ ≠ 0 at hξ
  let q := modulatedLaplaceRate 0 (-ξ)
  have hq : q.re = 0 := by simp [q, modulatedLaplaceRate]
  have hqne : q ≠ 0 := by
    intro he
    have hi := congrArg Complex.im he
    simp [q, modulatedLaplaceRate, Real.pi_ne_zero, hξ] at hi
  have hh := negativeHalfLineLaplace_undampedCausalConvolution_mul (f := cx J) 0 hm hfi
    hJ.memLp_weightedComplex hs hz (q := q) (integrable_negativeHalfLineLaplace hfi hs hq.ge)
  rw [hrate, zero_sub, hJU q (by rw [hq]; norm_num)] at hh
  have he : negativeHalfLineLaplace K q = -(Real.pi : ℂ) * negativeHalfLineLaplace (cx U) q := by
    apply mul_left_cancel₀ hqne
    change q * negativeHalfLineLaplace (modulatedCausalConvolution 0 0 (cx J)) q = _
    linear_combination -hh
  change 𝓕 K ξ = 𝓕 (fun u => -(Real.pi : ℂ) * cx U u) ξ
  rw [fourier_const_mul_apply]
  simpa only [q, negativeHalfLineLaplace_modulated_zero_eq_fourier, neg_neg] using he

private theorem mixed_scaled_left (R s : ℝ) {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) :
    criticalHalfLineMixedEnergy R (fun u => s*F u) G = s*criticalHalfLineMixedEnergy R F G := by
  have h := criticalHalfLineMixedEnergy_add_const_mul_left R hF hF hG (s-1)
  rw [show (fun u => F u+(s-1)*F u) = fun u => s*F u by funext u; ring] at h
  linarith only [h]

private theorem mixed_congr_right {J U V : ℝ → ℝ} (R : ℝ)
    (hJ : CriticalHalfLineEnergyDomain J) (hU : CriticalHalfLineEnergyDomain U)
    (hV : CriticalHalfLineEnergyDomain V) (he : U =ᵐ[volume] V) :
    criticalHalfLineMixedEnergy R J U = criticalHalfLineMixedEnergy R J V := by
  have hs := criticalHalfLineFullEnergy_congr_ae (hJ.add_const_mul hU 1) (hJ.add_const_mul hV 1)
    (he.mono fun u hu => congrArg (fun t => J u + 1*t) hu) R
  rw [criticalHalfLineFullEnergy_add_const_mul R hJ hU 1,
    criticalHalfLineFullEnergy_add_const_mul R hJ hV 1,
    criticalHalfLineFullEnergy_congr_ae hU hV he R] at hs
  linarith only [hs]

/-- A primitive pairs with its negative derivative by minus four times its
confinement mass. The undamped resolvent kills the bare form and recovers
the primitive almost everywhere by Fourier uniqueness. -/
theorem confinedMixedEnergy_laplace_factor {J U : ℝ → ℝ}
    (hJ : CriticalHalfLineEnergyDomain J) (hU : CriticalHalfLineEnergyDomain U)
    (hJU : ∀ z : ℂ, |z.re| ≤ 1/2 →
      negativeHalfLineLaplace (cx J) z = z * negativeHalfLineLaplace (cx U) z) (R : ℝ) :
    criticalHalfLineMixedEnergy R J U = -(4 * criticalAliasCoefficient R) *
      criticalHalfLineExponentialPair U U := by
  have hz : negativeHalfLineLaplace (cx J) (modulatedLaplaceRate 0 0) = 0 := by
    rw [show modulatedLaplaceRate 0 0 = 0 by simp [modulatedLaplaceRate],
      hJU 0 (by norm_num), zero_mul]
  have hk := zero_resolvent_of_laplace_factor hJ hU hJU
  have he : realUndampedCausalConvolution 0 J =ᵐ[volume] fun u => -Real.pi * U u := by
    filter_upwards [hk] with u hu
    change (modulatedCausalConvolution 0 0 (cx J) u).re = _
    rw [hu]
    simp only [cx, neg_mul, Complex.neg_re, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hpair := mixed_congr_right R hJ (hJ.realUndampedCausalConvolution 0 hz) (hU.const_mul _) he
  rw [criticalHalfLineMixedEnergy_comm R J (fun u => -Real.pi * U u),
    mixed_scaled_left R _ hU hJ, criticalHalfLineMixedEnergy_comm R U J] at hpair
  obtain ⟨hg,hp⟩ := arithmetic_mixed_realUndampedCausalConvolution_eq_zero 0 hJ hz
  have hbare : bareMixedEnergy J (realUndampedCausalConvolution 0 J) = 0 := by
    rw [bareMixedEnergy, hg, hp, pole_mixed_realUndampedCausalConvolution_eq_zero 0 hJ hz]
    ring
  rw [criticalHalfLineMixedEnergy_eq_bare_add, hbare, zero_add,
    integral_weighted_realUndampedCausalConvolution_mixed 0 hJ] at hpair
  have hw : (∫ u, ‖causalLaplaceWeighted (4 / Real.pi) (modulatedCausalConvolution 0 0 (cx J)) u‖^2) =
      Real.pi^2 * criticalHalfLineExponentialPair U U := by
    rw [criticalHalfLineExponentialPair_self, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hk] with u hu
    rw [norm_sq_causalLaplaceWeighted, show 2 * Real.pi * (4/Real.pi) = 8 by field_simp; norm_num, hu]
    simp only [cx, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hπ (w : ℝ) : (4/Real.pi) * (Real.pi^2*w) = Real.pi*(4*w) := by
    field_simp [Real.pi_ne_zero]
  rw [hw, hπ] at hpair
  apply mul_left_cancel₀ Real.pi_ne_zero
  linear_combination hpair

#print axioms confinedMixedEnergy_laplace_factor

/-! ### The negative plane and the second crossing -/

private theorem laplace_domain_add_scaled {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G)
    {z : ℂ} (hz : |z.re| ≤ 1/2) (s : ℝ) :
    negativeHalfLineLaplace (cx (fun u => F u + s*G u)) z =
      negativeHalfLineLaplace (cx F) z + (s : ℂ) * negativeHalfLineLaplace (cx G) z := by
  have hi {H : ℝ → ℝ} (h : CriticalHalfLineEnergyDomain H) :
      Integrable (fun u : ℝ => Complex.exp (z * u) * cx H u) :=
    integrable_complexLaplaceWeighted_of_halfLine_memLp hz h.memLp_complex h.memLp_weightedComplex (support_cx h)
  unfold negativeHalfLineLaplace
  rw [← integral_const_mul, ← integral_add (hi hF) ((hi hG).const_mul (s : ℂ))]
  apply integral_congr_ae
  refine Eventually.of_forall fun u => ?_
  simp only [cx, Complex.ofReal_add, Complex.ofReal_mul]
  ring

private theorem component_scaled (a b s : ℝ) (c : ℂ) (F : ℝ → ℝ) :
    resolventComponent a b ((s : ℂ)*c) F = fun u => s * resolventComponent a b c F u := by
  funext u
  simp only [resolventComponent, mul_assoc, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

private theorem component_add (a b : ℝ) (c d : ℂ) (F : ℝ → ℝ) :
    resolventComponent a b (c+d) F = fun u =>
      resolventComponent a b c F u + resolventComponent a b d F u := by
  funext u
  simp only [resolventComponent, add_mul, Complex.add_re]

/-- At a nonreal zero the causal resolvent supplies a strictly negative
direction for every nonzero real combination of its two components. -/
theorem IsConfinedNullVector.negative_resolventComponent {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) {a b : ℝ} (ha : 0 < a) (hb : b ≠ 0)
    (hz : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0)
    {c : ℂ} (hc : c ≠ 0) : criticalHalfLineFullEnergy R (resolventComponent a b c F) < 0 := by
  let α := modulatedLaplaceRate a b
  let U := fun d : ℂ => resolventComponent a b d F
  let M := criticalHalfLineMixedEnergy R
  let W := criticalHalfLineExponentialPair
  let k := criticalAliasCoefficient R
  have hD (d : ℂ) : CriticalHalfLineEnergyDomain (U d) := domain_resolventComponent ha hF.1 hz d
  have hbase (d : ℂ) : M (U (α*d)) (U d) = -(4*k)*W (U d) (U d) := by
    let J := fun u => U (α*d) u + (-(Real.pi*d.re))*F u
    have hJ := (hD (α*d)).add_const_mul hF.1 (-(Real.pi*d.re))
    have hder (z : ℂ) (h : |z.re| ≤ 1/2) :
        negativeHalfLineLaplace (cx J) z = z*negativeHalfLineLaplace (cx (U d)) z := by
      dsimp only [J]
      rw [laplace_domain_add_scaled (hD (α*d)) hF.1 h,
        laplace_mul_resolventComponent ha hF.1 hz d h]
      push_cast
      ring
    have h := confinedMixedEnergy_laplace_factor hJ (hD d) hder R
    rw [criticalHalfLineMixedEnergy_add_const_mul_left R (hD (α*d)) hF.1 (hD d) _,
      hF.2.2 _ (hD d), mul_zero, add_zero] at h
    exact h
  let d := (starRingEnd ℂ) α * c
  let N := Complex.normSq α
  have hA : 0 < α.re := by simpa [α, modulatedLaplaceRate] using mul_pos Real.pi_pos ha
  have hB : α.im ≠ 0 := by simp [α, modulatedLaplaceRate, Real.pi_ne_zero, hb]
  have hN : 0 < N := Complex.normSq_pos.mpr fun he => hA.ne' (by rw [he, Complex.zero_re])
  have had : α*d = (N : ℂ)*c := by
    dsimp only [d, N]
    rw [← mul_assoc, Complex.mul_conj]
  have hsum : α*c+d = ((2*α.re : ℝ) : ℂ)*c := by
    dsimp only [d]
    rw [← add_mul, ← two_mul_real α]
    push_cast
    rfl
  have hadd : M (U (α*c)) (U c) + M (U d) (U c) = (2*α.re)*M (U c) (U c) := by
    have h₁ := criticalHalfLineMixedEnergy_add_const_mul_left R (hD (α*c)) (hD d) (hD c) 1
    simp only [one_mul] at h₁
    dsimp only [U] at h₁
    rw [← component_add, hsum, component_scaled, mixed_scaled_left R _ (hD c) (hD c)] at h₁
    exact h₁.symm
  have hother := hbase d
  rw [had] at hother
  change criticalHalfLineMixedEnergy R (resolventComponent a b ((N : ℂ)*c) F) (U d) = _ at hother
  rw [component_scaled, mixed_scaled_left R _ (hD c) (hD d),
    criticalHalfLineMixedEnergy_comm R (U c) (U d)] at hother
  change N*M (U d) (U c) = _ at hother
  have hidentity : (2*α.re*N)*M (U c) (U c) = -(4*k)*(N*W (U c) (U c)+W (U d) (U d)) := by
    linear_combination N * (hbase c) + hother - N * hadd
  have mass_nonneg (v : ℂ) : 0 ≤ W (U v) (U v) := by
    change 0 ≤ criticalHalfLineExponentialPair (U v) (U v)
    rw [criticalHalfLineExponentialPair_self]
    exact integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hWc := mass_nonneg c
  have hWd := mass_nonneg d
  have hpositive : 0 < N*W (U c) (U c)+W (U d) (U d) := by
    refine lt_of_le_of_ne (add_nonneg (mul_nonneg hN.le hWc) hWd) ?_
    intro he
    have hz₁ : W (U c) (U c) = 0 := by
      by_contra h
      exact (add_pos_of_pos_of_nonneg (mul_pos hN (lt_of_le_of_ne hWc (Ne.symm h))) hWd).ne' he.symm
    have hz₂ : W (U d) (U d) = 0 := by rwa [hz₁, mul_zero, zero_add, eq_comm] at he
    have hK : modulatedCausalConvolution a b (cx F) =ᵐ[volume] 0 := by
      filter_upwards [(criticalHalfLineExponentialPair_self_eq_zero_iff (hD c)).mp hz₁,
        (criticalHalfLineExponentialPair_self_eq_zero_iff (hD d)).mp hz₂] with u hu hv
      let v := c * modulatedCausalConvolution a b (cx F) u
      change v.re = 0 at hu
      change (((starRingEnd ℂ) α*c)*modulatedCausalConvolution a b (cx F) u).re = 0 at hv
      rw [mul_assoc] at hv
      change ((starRingEnd ℂ) α*v).re = 0 at hv
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hu, mul_zero, neg_mul,
        zero_sub, neg_neg] at hv
      have hvi : v.im = 0 := (mul_eq_zero.mp hv).resolve_left hB
      have hv0 : v = 0 := Complex.ext hu hvi
      exact (mul_eq_zero.mp hv0).resolve_left hc
    have hzero := ae_eq_zero_of_modulatedCausalConvolution_ae_zero ha b (hF.1.integrable.ofReal (𝕜 := ℂ)) hK
    apply hF.2.1
    calc (∫ u, F u ^ 2) = ∫ _u : ℝ, (0 : ℝ) := by
          apply integral_congr_ae
          filter_upwards [hzero] with u hu
          change (F u : ℂ) = 0 at hu
          rw [Complex.ofReal_eq_zero.mp hu, zero_pow two_ne_zero]
        _ = 0 := by simp
  have hmneg := hidentity.trans_lt (mul_neg_of_neg_of_pos
    (neg_lt_zero.mpr (mul_pos (by norm_num) (criticalAliasCoefficient_positive hR))) hpositive)
  have hsign : M (U c) (U c) < 0 := by
    by_contra! hn
    exact hmneg.not_ge (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA.le) hN.le) hn)
  simpa only [M, criticalHalfLineMixedEnergy_self R (hD c)] using hsign

/-- A nonreal right Laplace zero of any confined null state produces a real
negative plane at the very same ratio. -/
theorem IsConfinedNullVector.negativePlane_of_nonreal_laplace_zero {R : ℝ} (hR : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) {z : ℂ} (hRe : 0 < z.re) (hIm : z.im ≠ 0)
    (hz : negativeHalfLineLaplace (cx F) z = 0) :
    ∃ X Y : ℝ → ℝ, IsNegativePlane R X Y := by
  let a := z.re / Real.pi
  let b := z.im / (2 * Real.pi)
  have ha : 0 < a := div_pos hRe Real.pi_pos
  have hb : b ≠ 0 := div_ne_zero hIm (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hr : modulatedLaplaceRate a b = z := by
    have hx : Real.pi*a = z.re := by dsimp only [a]; field_simp [Real.pi_ne_zero]
    have hy : 2*Real.pi*b = z.im := by dsimp only [b]; field_simp [Real.pi_ne_zero]
    unfold modulatedLaplaceRate
    rw [hx, hy]
    apply Complex.ext <;> simp
  have hl : negativeHalfLineLaplace (cx F) (modulatedLaplaceRate a b) = 0 := by rwa [hr]
  let U := fun c : ℂ => resolventComponent a b c F
  refine ⟨U 1, U Complex.I, domain_resolventComponent ha hF.1 hl 1,
    domain_resolventComponent ha hF.1 hl Complex.I, ?_⟩
  intro s t hst
  let c := (⟨s,t⟩ : ℂ)
  have hc : c ≠ 0 := fun he => hst (Prod.ext (congrArg Complex.re he) (congrArg Complex.im he))
  have h := hF.negative_resolventComponent hR ha hb hl hc
  have he : U c = fun u => s * U 1 u + t * U Complex.I u := by
    funext u
    simp only [U, c, resolventComponent, Complex.mul_re, Complex.I_re, Complex.I_im,
      one_mul, zero_mul, zero_sub]
    ring
  change criticalHalfLineFullEnergy R (U c) < 0 at h
  rwa [he] at h

/-- On failure of RH the second confined state detects every nonreal Laplace
argument in the right half-plane. Every larger ratio admits a negative plane. -/
theorem riemannHypothesis_or_second_state_sees_nonreal_right_halfPlane :
    RiemannHypothesis ∨ ∃ (R : ℝ) (F : ℝ → ℝ), 0 < R ∧ IsConfinedNullVector R F ∧
      (∫ u, F u^2) = 1 ∧ (∀ X Y, ¬ IsNegativePlane R X Y) ∧
      (∀ r : ℝ, R < r → ∃ X Y, IsNegativePlane r X Y) ∧
      ∀ z : ℂ, 0 < z.re → z.im ≠ 0 → negativeHalfLineLaplace (cx F) z ≠ 0 := by
  rcases riemannHypothesis_or_secondCriticalState with h | ⟨w, r, G, F, hw, _, _, hwr, hF,
    hunit, _, hlow, hhigh⟩
  · exact Or.inl h
  · have hr := hw.trans hwr
    refine Or.inr ⟨r, F, hr, hF, hunit, hlow r hr le_rfl, hhigh, ?_⟩
    intro z hre him hz
    obtain ⟨X, Y, hneg⟩ := hF.negativePlane_of_nonreal_laplace_zero hr hre him hz
    exact hlow r hr le_rfl X Y hneg

/-- On failure of RH one normalized null state at the second crossing has
nonzero Laplace value at every centered right zero of zeta simultaneously. -/
theorem riemannHypothesis_or_second_state_sees_every_right_zero :
    RiemannHypothesis ∨ ∃ (R : ℝ) (F : ℝ → ℝ), 0 < R ∧ IsConfinedNullVector R F ∧
      (∫ u, F u^2) = 1 ∧ (∀ X Y, ¬ IsNegativePlane R X Y) ∧
      (∀ r : ℝ, R < r → ∃ X Y, IsNegativePlane r X Y) ∧
      ∀ ρ ∈ zetaZeroConfig.carrier, 1/2 < ρ.re → negativeHalfLineLaplace (cx F) (ρ-1/2) ≠ 0 := by
  rcases riemannHypothesis_or_second_state_sees_nonreal_right_halfPlane with h | ⟨R,F,hr,hF,hm,hl,hu,hz⟩
  · exact Or.inl h
  · refine Or.inr ⟨R,F,hr,hF,hm,hl,hu,?_⟩
    intro ρ hρ hre
    apply hz
    · have he : (ρ - (1/2 : ℂ)).re = ρ.re - 1/2 := by norm_num [Complex.sub_re]
      rwa [he, sub_pos]
    · simpa using zetaZeroConfig_im_ne_zero' ρ hρ

/-- Every zeta zero on or right of the line gives a nonzero simple-pole
residue of the second state's continued transform, for the same state at all zeros. -/
theorem riemannHypothesis_or_second_state_has_all_right_residues :
    RiemannHypothesis ∨ ∃ (R : ℝ) (F : ℝ → ℝ), 0 < R ∧ IsConfinedNullVector R F ∧
      (∫ u, F u^2) = 1 ∧ (∀ X Y, ¬ IsNegativePlane R X Y) ∧
      (∀ r : ℝ, R < r → ∃ X Y, IsNegativePlane r X Y) ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → 1/2 ≤ ρ.re →
        ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun w => (w - (ρ - 17/2)) * stateMeromorphic R F w)
          (𝓝[≠] (ρ - 17/2)) (𝓝 c) := by
  rcases riemannHypothesis_or_second_state_sees_every_right_zero with h | ⟨R,F,hr,hF,hm,hl,hu,hv⟩
  · exact Or.inl h
  · refine Or.inr ⟨R,F,hr,hF,hm,hl,hu,?_⟩
    intro ρ hζ hre
    have hpos : 0 < ρ.re := lt_of_lt_of_le (by norm_num) hre
    refine ⟨_, (levyResidue_ne_zero_iff hr hζ).mpr ?_, tendsto_stateMeromorphic_residue hF.1 hζ hpos⟩
    rcases hre.eq_or_lt with he | he
    · let z := ρ - 1/2
      have hz : z.re = 0 := by simp [z, Complex.sub_re, ← he]
      have hi : 2*Real.pi*(z.im/(2*Real.pi)) = z.im := by field_simp [Real.pi_ne_zero]
      have e : modulatedLaplaceRate 0 (z.im/(2*Real.pi)) = z := by
        unfold modulatedLaplaceRate
        rw [hi]
        apply Complex.ext <;> simp [hz]
      simpa only [e] using hF.boundary_laplace_ne_zero hr (z.im/(2*Real.pi))
    · exact hv ρ ⟨hζ,hpos,lt_of_not_ge fun h => riemannZeta_ne_zero_of_one_le_re h hζ⟩ he

/-- Every right zeta mode occurs with nonzero coefficient in the same
second state's time profile. Their absolutely convergent sum recovers the
profile up to the decay rate of the critical line. -/
theorem riemannHypothesis_or_second_state_contains_all_right_modes :
    RiemannHypothesis ∨ ∃ (R : ℝ) (F : ℝ → ℝ), 0 < R ∧ IsConfinedNullVector R F ∧
      (∫ u, F u^2) = 1 ∧ (∀ X Y, ¬ IsNegativePlane R X Y) ∧
      (∀ r : ℝ, R < r → ∃ X Y, IsNegativePlane r X Y) ∧
      (∀ q : XiZeroCopy, 0 < (centredZero q).re → zeroModeCoeff R F q ≠ 0) ∧
      ∃ C : ℝ, ∀ t : ℝ, 0 < t →
        ‖(averagedState F t : ℂ) - ∑' q : XiZeroCopy, (if 0 < (centredZero q).re then
          zeroModeCoeff R F q * Complex.exp ((centredZero q-8)*t) else 0)‖ ≤
            C * Real.exp (-(8*t)) := by
  rcases riemannHypothesis_or_second_state_sees_nonreal_right_halfPlane with h | ⟨R,F,hr,hF,hm,hl,hu,hz⟩
  · exact Or.inl h
  · refine Or.inr ⟨R,F,hr,hF,hm,hl,hu,?_,hF.averagedState_sub_rightModes_le hr⟩
    intro q hpos
    have ha : (criticalAliasCoefficient R : ℂ) ≠ 0 := by
      exact_mod_cast (criticalAliasCoefficient_positive hr).ne'
    obtain ⟨h9,h10,h11,h12⟩ := averageSymbol_factors_ne_zero (s := centredZero q-8)
      (by rw [show (centredZero q-8).re = (centredZero q).re-8 by simp]; linarith only [hpos])
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero ha))
      (hz _ hpos (im_centredZero_ne_zero q)))
      (inv_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h9 h10) h11) h12))

#print axioms IsConfinedNullVector.negative_resolventComponent
#print axioms IsConfinedNullVector.negativePlane_of_nonreal_laplace_zero
#print axioms riemannHypothesis_or_second_state_sees_nonreal_right_halfPlane
#print axioms riemannHypothesis_or_second_state_sees_every_right_zero
#print axioms riemannHypothesis_or_second_state_has_all_right_residues
#print axioms riemannHypothesis_or_second_state_contains_all_right_modes

end GaloisForLFunctions.ExclusionOfTheCriticalState
