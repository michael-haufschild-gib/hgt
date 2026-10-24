import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceConeBoundaryRigidity
import GaloisForLFunctions.RHTower.XiCompactPolarWeilRealization
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.WeilPaperPacketRealification
import GaloisForLFunctions.RHTower.XiQuotientRealDecay

/-!
# Numerical equivalence on the scaling surface is equality

Compact polar tests are dense in the absolute Xi evaluation space. They therefore separate
every compact source through the literal Weil pairing, including sources with nonzero pole
moments. Realification transfers this separation to the real Weil form. The hyperbolic pole
plane then makes the full scaling intersection pairing nondegenerate, without Hodge index.

Consequently a translation preserving every intersection reading in the present cycle space
is zero. Divisor movement with nontrivial representatives must precede passage to these classes.
-/

open Complex MeasureTheory Set Zeta23 RHTower
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem xiCopies_tsum_eq_zetaCarrier (F : ℂ → ℂ)
    (hF : Summable (fun q : XiZeroCopy => F (xiSpectralPoint q))) :
    (∑' q : XiZeroCopy, F (xiSpectralPoint q)) =
      ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) * F (gammaOf ρ) := by
  have hγ (q : XiZeroCopy) : xiSpectralPoint q = gammaOf (q.1 : ℂ) := by
    simp only [xiSpectralPoint, gammaOf, div_eq_mul_inv, Complex.inv_I]
  rw [hF.tsum_sigma, ← xiDivisorZetaCarrierEquiv.tsum_eq
    (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) * F (gammaOf ρ))]
  apply tsum_congr
  intro ρ
  simp only [hγ, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, xiDivisorZetaCarrierEquiv_multiplicity]
  rfl

/-- The compact-source polarization retains the complete zeta divisor and its multiplicities. -/
theorem xiWeilPolarization_paperFT_eq_zetaWeil (f g : compactXiTests) :
    xiWeilPolarization (paperFT f) (paperFT g) = zetaZeroConfig.W f g := by
  have hs := xiWeilPairSummable_of_squareSummable'
    (complexXi_squareSummable f (compactXiTests.re_decay f) (compactXiTests.im_decay f))
    (complexXi_squareSummable g (compactXiTests.re_decay g) (compactXiTests.im_decay g))
  change (∑' q : XiZeroCopy,
    paperFT f (xiSpectralPoint q) * xiWeilSharp (paperFT g) (xiSpectralPoint q)) = _
  calc
    _ = ∑' ρ : zetaZeroConfig.carrier, (zetaZeroConfig.mult ρ : ℂ) *
        (paperFT f (gammaOf ρ) * xiWeilSharp (paperFT g) (gammaOf ρ)) :=
      xiCopies_tsum_eq_zetaCarrier
        (fun z : ℂ => paperFT f z * xiWeilSharp (paperFT g) z) hs
    _ = zetaZeroConfig.W f g := by
      apply tsum_congr
      intro ρ
      change (zetaZeroConfig.mult ρ : ℂ) *
        (paperFT f (gammaOf ρ) * conj (paperFT g (conj (gammaOf ρ)))) =
        (zetaZeroConfig.mult ρ : ℂ) * paperFT f (gammaOf ρ) *
          conj (paperFT g (conj (gammaOf ρ)))
      exact (mul_assoc _ _ _).symm

private theorem compactXiEvaluation_eq_evaluationLp (f : compactXiTests) :
    compactXiEvaluation f = xiWeilEvaluationLp (paperFT f)
      (complexXi_squareSummable f (compactXiTests.re_decay f) (compactXiTests.im_decay f)) := by
  apply Subtype.ext
  funext q
  exact compactXiEvaluation_apply f q

theorem zetaWeil_compact_eq_inner (f g : compactXiTests) :
    zetaZeroConfig.W f g =
      inner ℂ (xiWeilLineConjLp (compactXiEvaluation g)) (compactXiEvaluation f) := by
  rw [compactXiEvaluation_eq_evaluationLp f, compactXiEvaluation_eq_evaluationLp g,
    inner_xiWeilLineConjLp_evaluation_eq_polarization, xiWeilPolarization_paperFT_eq_zetaWeil]

private theorem reflected_compactXiEvaluation_mem_core (f : compactXiTests) :
    xiWeilLineConjLp (compactXiEvaluation f) ∈ xiWeilCauchyHilbertSubspace := by
  let F := fun z => paperFT f (conj z)
  have hs : XiWeilSquareSummable F := by
    have h := HilbertSchmidt.summable_coe_sq (xiWeilLineConjLp (compactXiEvaluation f))
    simpa only [XiWeilSquareSummable, F, xiWeilLineConjLp_apply,
      compactXiEvaluation_apply, xiSpectralPoint_lineConj] using h
  have he : xiWeilLineConjLp (compactXiEvaluation f) = xiWeilEvaluationLp F hs := by
    apply Subtype.ext
    funext q
    simp only [xiWeilLineConjLp_apply, compactXiEvaluation_apply,
      xiSpectralPoint_lineConj, xiWeilEvaluationLp_apply, F]
  rw [he]
  exact xiWeilEvaluationLp_mem_xiWeilCauchyHilbertSubspace F hs

/-- Compact polar tests separate every compact source, with no pole constraint on that source. -/
theorem eq_zero_of_zetaWeil_compactPolar_tests (f : compactXiTests)
    (h : ∀ g : compactXiPolarTests, zetaZeroConfig.W (g : compactXiTests) f = 0) : f = 0 := by
  let w := xiWeilLineConjLp (compactXiEvaluation f)
  have hw : w ∈ compactXiPolarEvaluation.range.topologicalClosure := by
    rw [compactXiPolarEvaluation_closure_eq_cauchyHilbertSubspace]
    exact reflected_compactXiEvaluation_mem_core f
  have hz : ∀ v ∈ compactXiPolarEvaluation.range.topologicalClosure, inner ℂ w v = 0 := by
    apply closure_minimal
    · rintro v ⟨g, rfl⟩
      exact (zetaWeil_compact_eq_inner (g : compactXiTests) f).symm.trans (h g)
    · exact isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hzero : w = 0 := inner_self_eq_zero.mp (hz w hw)
  have hn := norm_xiWeilLineConjLp (compactXiEvaluation f)
  change ‖w‖ = ‖compactXiEvaluation f‖ at hn
  rw [hzero, norm_zero] at hn
  apply compactXiEvaluation_injective
  rw [map_zero, ← norm_eq_zero]
  exact hn.symm

private theorem zetaWeil_cx_eq_ofReal (f g : realTests) :
    zetaZeroConfig.W (cx f.1) (cx g.1) = (weilPair f.1 g.1 : ℂ) := by
  rw [zeta_W_eq_weilFullFunctional_mixed (cx_contDiff f.2.1) (cx_hasCompactSupport f.2.2)
    (cx_contDiff g.2.1) (cx_hasCompactSupport g.2.2)]
  apply Complex.ext
  · rfl
  · have hcorr : EF.weilTest (cx f.1) (cx g.1) =
        fun y => ((∫ t : ℝ, f.1 t * g.1 (t - y) : ℝ) : ℂ) := by
      funext y
      rw [WeilSpectral.weilTest_apply, ← integral_complex_ofReal]
      simp only [cx, Complex.conj_ofReal, Complex.ofReal_mul]
    rw [hcorr]
    exact WeilWorkPBAP.weilFullFunctional_ofReal_im _ _

private def compactRealPart (g : compactXiTests) : realTests :=
  ⟨fun u => (g.1 u).re, Complex.reCLM.contDiff.comp g.2.1,
    g.2.2.comp_left Complex.zero_re⟩

private def compactImagPart (g : compactXiTests) : realTests :=
  ⟨fun u => (g.1 u).im, Complex.imCLM.contDiff.comp g.2.1,
    g.2.2.comp_left Complex.zero_im⟩

private theorem compact_split (g : compactXiTests) :
    g.1 = cx (compactRealPart g).1 + I • cx (compactImagPart g).1 := by
  funext u
  change g.1 u = ((g.1 u).re : ℂ) + I * ((g.1 u).im : ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (g.1 u)).symm

private theorem zetaWeil_compact_split (g : compactXiTests) (f : realTests) :
    zetaZeroConfig.W g.1 (cx f.1) =
      zetaZeroConfig.W (cx (compactRealPart g).1) (cx f.1) +
        I * zetaZeroConfig.W (cx (compactImagPart g).1) (cx f.1) := by
  have hr := cx_contDiff (compactRealPart g).2.1
  have hrc := cx_hasCompactSupport (compactRealPart g).2.2
  have hi := (cx_contDiff (compactImagPart g).2.1).const_smul I
  have hic : HasCompactSupport (I • cx (compactImagPart g).1) :=
    (cx_hasCompactSupport (compactImagPart g).2.2).smul_left
  rw [compact_split g]
  rw [W_add_left zetaZeroConfig
    GaloisForLFunctions.SquareRootThreshold.temperedConfig_zetaZeroConfig
    (f₁ := cx (compactRealPart g).1) (f₂ := I • cx (compactImagPart g).1) (g := cx f.1)
    hr hrc hi hic (cx_contDiff f.2.1) (cx_hasCompactSupport f.2.2), W_smul_left]

/-- A real compact source cannot annihilate all real compact tests under the Weil pairing. -/
theorem weilPair_nondegenerate (f : realTests) :
    (∀ g : realTests, weilPair f.1 g.1 = 0) ↔ f = 0 := by
  constructor
  · intro h
    let F : compactXiTests := ⟨cx f.1, cx_contDiff f.2.1, cx_hasCompactSupport f.2.2⟩
    have hreal (g : realTests) : zetaZeroConfig.W (cx g.1) (cx f.1) = 0 := by
      rw [zetaWeil_cx_eq_ofReal, weilPair_comm, h g, Complex.ofReal_zero]
    have hF : F = 0 := by
      apply eq_zero_of_zetaWeil_compactPolar_tests
      intro g
      change zetaZeroConfig.W g.1.1 (cx f.1) = 0
      rw [zetaWeil_compact_split g.1 f, hreal, hreal, mul_zero, add_zero]
    apply Subtype.ext
    funext u
    have hu := congrArg (fun k : compactXiTests => (k.1 u).re) hF
    simpa only [F, cx, Complex.ofReal_re, Submodule.coe_zero, Pi.zero_apply, Complex.zero_re] using hu
  · rintro rfl g
    simpa only [Submodule.coe_zero, zero_smul, zero_mul] using
      (weilPair_smul_left 0 (0 : ℝ → ℝ) g.1)

private theorem scalingPair_eq_degree_products_sub_weilPair (x y : ScalingCycle) :
    scalingSurface.pair x y =
      (x.2.1 + poleB x.2.2) * (y.1 + poleA y.2.2) +
      (x.1 + poleA x.2.2) * (y.2.1 + poleB y.2.2) - weilPair x.2.2 y.2.2 := by
  change scalingPairFun x y = _
  simp only [scalingPairFun, localPair]
  ring

/-- The mixed defect depends only on the two compact sources. -/
theorem scalingSurface_defect_mixed (x y : ScalingCycle) :
    scalingSurface.defect x y = weilPair x.2.2 y.2.2 := by
  rw [PolarSurface.defect, PolarSurface.polar]
  change scalingPairFun x (1, 0, 0) * scalingPairFun y (0, 1, 0) +
    scalingPairFun x (0, 1, 0) * scalingPairFun y (1, 0, 0) - scalingPairFun x y = _
  simp only [scalingPairFun, Submodule.coe_zero, poleB_zero, poleA_zero,
    localPair_zero_right, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
  rw [localPair]
  ring

/-- The defect radical of the full compact scaling surface is exactly the fibre plane. -/
theorem scalingSurface_defect_radical_iff_source_eq_zero (x : ScalingCycle) :
    (∀ y : ScalingCycle, scalingSurface.defect x y = 0) ↔ x.2.2 = 0 := by
  simp only [scalingSurface_defect_mixed]
  constructor
  · intro h
    exact (weilPair_nondegenerate x.2.2).mp fun f => h (0, 0, f)
  · intro hf y
    rw [hf]
    exact (weilPair_nondegenerate 0).mpr rfl y.2.2

/-- The original scaling intersection pairing has zero numerical radical, unconditionally. -/
theorem scalingSurface_pairing_nondegenerate (x : ScalingCycle) :
    (∀ y : ScalingCycle, scalingSurface.pair x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    have hH : x.2.1 + poleB x.2.2 = 0 := by
      have h' := h scalingSurface.H
      change scalingPairFun x (1, 0, 0) = 0 at h'
      simpa only [scalingPairFun, Submodule.coe_zero, poleB_zero, poleA_zero,
        localPair_zero_right, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] using h'
    have hV : x.1 + poleA x.2.2 = 0 := by
      have h' := h scalingSurface.V
      change scalingPairFun x (0, 1, 0) = 0 at h'
      simpa only [scalingPairFun, Submodule.coe_zero, poleB_zero, poleA_zero,
        localPair_zero_right, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] using h'
    have hf : x.2.2 = 0 := (weilPair_nondegenerate x.2.2).mp fun g => by
      have hg := h (0, 0, g)
      rw [scalingPair_eq_degree_products_sub_weilPair, hH, hV, zero_mul, zero_mul,
        zero_add, zero_sub] at hg
      exact neg_eq_zero.mp hg
    have ha : x.1 = 0 := by simpa only [hf, Submodule.coe_zero, poleA_zero, add_zero] using hV
    have hb : x.2.1 = 0 := by simpa only [hf, Submodule.coe_zero, poleB_zero, add_zero] using hH
    exact Prod.ext ha (Prod.ext hb hf)
  · rintro rfl y
    simp only [map_zero, LinearMap.zero_apply]

/-- All intersection readings determine a scaling cycle exactly. -/
theorem scalingSurface_numerical_equivalence_iff_eq (x y : ScalingCycle) :
    (∀ z : ScalingCycle, scalingSurface.pair x z = scalingSurface.pair y z) ↔ x = y := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply (scalingSurface_pairing_nondegenerate (x - y)).mp
    intro z
    rw [map_sub, LinearMap.sub_apply, h z, sub_self]
  · rintro rfl z
    rfl

/-- No nonzero translation of the existing cycle space preserves every intersection. -/
theorem scalingSurface_intersection_preserving_translation_iff (p : ScalingCycle) :
    (∀ x y : ScalingCycle, scalingSurface.pair (x + p) y = scalingSurface.pair x y) ↔ p = 0 := by
  constructor
  · intro h
    apply (scalingSurface_pairing_nondegenerate p).mp
    intro y
    simpa only [zero_add, map_zero, LinearMap.zero_apply] using h 0 y
  · rintro rfl x y
    rw [add_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
