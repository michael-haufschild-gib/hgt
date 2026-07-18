import GaloisForLFunctions.RHTower.XiHurwitzAnchorTransversality
import GaloisForLFunctions.Hurwitz.LadderDeformation
import GaloisForLFunctions.RHTower.XiArakelovHurwitzDependenceCollision
import GaloisForLFunctions.RHTower.XiHedenmalmMomentDeterminacy
import GaloisForLFunctions.RHTower.Reflection

/-!
# Projective Hurwitz anchor-jet reflection forces the critical line

For a zero `rho` of Xi, both frozen-exponent Hurwitz functions with exponents `1-rho` and
`conj rho` vanish simply at the canonical shift `a = 1`.  This module isolates a scale-free
value relation between their complete positive-order anchor jets.  If those jets are proportional
by one scalar, analytic determinacy promotes the relation to a genuine identity in the shift
variable.  The intrinsic continued-Hurwitz differential matroid then forces the two monodromy
characters to agree.  Open-strip rigidity gives `1-rho = conj rho`, hence `Re rho = 1/2`.

This closes the passage

`projective anchor jets -> local germ relation -> global shift relation -> Hurwitz dependence
 -> monodromy collision -> critical line`.

The result is unconditional as an implication.  It does not produce the projective jet relation
from the prime--Gamma source and therefore does not by itself prove RH.
-/

open Complex Set Filter Metric Polynomial
open scoped Topology Differential
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open HurwitzZetaContinuation HurwitzJointLadder HurwitzOrbit HurwitzLadder

namespace RHTower

noncomputable section

/-- Ascending Pochhammer evaluation commutes with complex conjugation. -/
theorem ascPochhammer_eval_conj (r : ℕ) (s : ℂ) :
    (ascPochhammer ℂ r).eval ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) ((ascPochhammer ℂ r).eval s) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]
      simp

/-- Every positive-order canonical Hurwitz anchor jet commutes with Schwarz reflection in the
frozen exponent. -/
theorem continuedHzeta_anchorJet_conj (r : ℕ) {s : ℂ}
    (hs : 0 < s.re) (hr : 0 < r) :
    iteratedDeriv r (continuedHzeta ((starRingEnd ℂ) s)) 1 =
      (starRingEnd ℂ) (iteratedDeriv r (continuedHzeta s) 1) := by
  rw [continuedHzeta_iteratedDeriv_at_one r (by simpa using hs),
    continuedHzeta_iteratedDeriv_at_one r hs]
  rw [ascPochhammer_eval_conj]
  have hz := riemannZeta_conj_of_one_lt (s := s + r) (by
    rw [Complex.add_re, Complex.natCast_re]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith [hs])
  rw [show (starRingEnd ℂ) s + (r : ℂ) =
      (starRingEnd ℂ) (s + r) by simp, hz]
  simp

/-- Local equality at the boundary anchor `1` propagates through the connected upper half-plane.
The proof moves to one interior point in the open equality neighborhood and then invokes the
analytic identity theorem. -/
theorem eventuallyEq_at_one_eqOn_UHP
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f UHP) (hg : AnalyticOnNhd ℂ g UHP)
    (hlocal : f =ᶠ[𝓝 (1 : ℂ)] g) : Set.EqOn f g UHP := by
  have hmem : {z : ℂ | f z = g z} ∈ 𝓝 (1 : ℂ) := hlocal
  obtain ⟨t, htsub, htopen, h1t⟩ := _root_.mem_nhds_iff.mp hmem
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp htopen 1 h1t
  let a : ℂ := 1 + (ε / 2 : ℝ) * Complex.I
  have haU : a ∈ UHP := by
    simp only [a, UHP, Set.mem_setOf_eq, Complex.add_im, Complex.one_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, zero_add]
    positivity
  have haBall : a ∈ Metric.ball (1 : ℂ) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [a, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, mul_one]
    rw [abs_of_pos (by positivity : 0 < ε / 2)]
    linarith
  have hat : a ∈ t := hball haBall
  have haLocal : f =ᶠ[𝓝 a] g := by
    filter_upwards [htopen.mem_nhds hat] with z hzt
    exact htsub hzt
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg isPreconnected_UHP haU haLocal

/-- Scale-free complete anchor-jet compatibility between functional-equation reflection and
Schwarz reflection.  The same scalar must work at every positive differential order. -/
def XiHurwitzAnchorJetProjectiveReflectionCompatible (rho : ℂ) : Prop :=
  ∃ c : ℂ, ∀ r : ℕ, 0 < r →
    iteratedDeriv r (continuedHzeta (1 - rho)) 1 =
      c * (starRingEnd ℂ) (iteratedDeriv r (continuedHzeta rho) 1)

/-- The projective scalar cannot vanish at an open-strip Xi zero: the first anchor jet on the
functional-equation side is unconditionally nonzero. -/
theorem xiHurwitzAnchorJet_projectiveScalar_ne_zero
    {rho c : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hcompat : ∀ r : ℕ, 0 < r →
      iteratedDeriv r (continuedHzeta (1 - rho)) 1 =
        c * (starRingEnd ℂ) (iteratedDeriv r (continuedHzeta rho) 1)) :
    c ≠ 0 := by
  intro hc
  have hfirst := hcompat 1 (by omega)
  rw [hc, zero_mul] at hfirst
  exact continuedHzeta_xiZero_deriv_at_one_ne_zero (rho := 1 - rho) (by
    simp only [Complex.sub_re, Complex.one_re]
    linarith) (by
      simpa [iteratedDeriv_one] using hfirst)

/-- **Pointwise projective reflection rigidity.**  At an open-strip Xi zero, proportionality of
the complete positive-order anchor jets forces the critical-line equation. -/
theorem xi_re_eq_half_of_anchorJetProjectiveReflectionCompatible
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1) (hzero : xi rho = 0)
    (hprojective : XiHurwitzAnchorJetProjectiveReflectionCompatible rho) :
    rho.re = 1 / 2 := by
  obtain ⟨c, hcompat⟩ := hprojective
  have hrefstrip : 0 < (1 - rho).re ∧ (1 - rho).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re]
    constructor <;> linarith
  have hconjstrip : 0 < ((starRingEnd ℂ) rho).re ∧
      ((starRingEnd ℂ) rho).re < 1 := by
    simpa using hstrip
  have hzref : xi (1 - rho) = 0 := by rw [xi_one_sub, hzero]
  have hzconj : xi ((starRingEnd ℂ) rho) = 0 := by
    rw [xi_conj, hzero, map_zero]
  have href1 : 1 - rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hconj1 : (starRingEnd ℂ) rho ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.one_re] at hre
    linarith
  have hder : ∀ r : ℕ,
      iteratedDeriv r (continuedHzeta (1 - rho)) 1 =
        iteratedDeriv r
          (fun a => c * continuedHzeta ((starRingEnd ℂ) rho) a) 1 := by
    intro r
    by_cases hr : r = 0
    · subst r
      simp only [iteratedDeriv_zero]
      rw [continuedHzeta_xiZero_at_one hrefstrip.1 href1 hzref,
        continuedHzeta_xiZero_at_one hconjstrip.1 hconj1 hzconj, mul_zero]
    · rw [GaloisForLFunctions.iteratedDeriv_const_mul_field,
        hcompat r (Nat.pos_of_ne_zero hr)]
      beta_reduce
      rw [continuedHzeta_anchorJet_conj r hstrip.1 (Nat.pos_of_ne_zero hr)]
  have hlocal : continuedHzeta (1 - rho) =ᶠ[𝓝 (1 : ℂ)]
      (fun a => c * continuedHzeta ((starRingEnd ℂ) rho) a) :=
    analyticAt_eventuallyEq_of_all_iteratedDeriv_eq
      (continuedHzeta_analyticAt_one hrefstrip.1)
      ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c) 1).mul
        (continuedHzeta_analyticAt_one hconjstrip.1)) hder
  have heqOn : Set.EqOn (continuedHzeta (1 - rho))
      (fun a => c * continuedHzeta ((starRingEnd ℂ) rho) a) UHP :=
    eventuallyEq_at_one_eqOn_UHP
      (continuedHzeta_analyticOnNhd (1 - rho))
      (analyticOnNhd_const.mul
        (continuedHzeta_analyticOnNhd ((starRingEnd ℂ) rho))) hlocal
  have hanEq : continuedHzetaUpperEndAnalytic (1 - rho) =
      upperEndPolyToAnalytic (Polynomial.C c) *
        continuedHzetaUpperEndAnalytic ((starRingEnd ℂ) rho) := by
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    simp only [Filter.EventuallyEq]
    rw [upperEndFilter_basis.eventually_iff]
    refine ⟨0, trivial, ?_⟩
    intro a ha
    simpa [upperEndPolyToAnalytic] using
      heqOn (by simpa [UHP, upperTail] using ha)
  have hmeroEq : continuedHzetaUpperEndMero (1 - rho) =
      upperEndPolyToMero (Polynomial.C c) *
        continuedHzetaUpperEndMero ((starRingEnd ℂ) rho) := by
    letI := isDomain_upperEndAnalyticSubring
    change algebraMap upperEndAnalyticSubring upperEndMeroField
        (continuedHzetaUpperEndAnalytic (1 - rho)) = _
    rw [hanEq, map_mul]
    rfl
  have hdep : ContinuedHurwitzPairDifferentiallyDependent
      (1 - rho) ((starRingEnd ℂ) rho) := by
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    let cRF : RatFunc ℂ :=
      algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c)
    have hcmap : algebraMap (RatFunc ℂ) upperEndMeroField cRF =
        upperEndPolyToMero (Polynomial.C c) :=
      upperEndRatfuncToMero_algebraMap_polynomial _
    apply not_differentialIndependent_of_jet_eq_base_mul
      (show (false : Bool) ≠ true by simp) 0 cRF
    simpa [continuedHurwitzPairExponent, hcmap] using hmeroEq
  have hmono : monoScalar (1 - rho) = monoScalar ((starRingEnd ℂ) rho) :=
    monoScalar_eq_of_continuedHurwitzPairDifferentiallyDependent
      (fun m => openCriticalStrip_point_ne_int hrefstrip m)
      (fun m => openCriticalStrip_point_ne_int hconjstrip m) hdep
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference _ _).mp hmono
  have heq : 1 - rho = (starRingEnd ℂ) rho :=
    openCriticalStrip_eq_of_sub_eq_int hrefstrip hconjstrip m hm
  have hre := congrArg Complex.re heq
  simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
  linarith

/-- Global source-value hypothesis: every Xi divisor point has projectively reflected complete
positive-order canonical Hurwitz anchor jets. -/
def XiHurwitzAnchorJetProjectiveReflectionLaw : Prop :=
  ∀ rho : XiDivisorSupport,
    XiHurwitzAnchorJetProjectiveReflectionCompatible (rho : ℂ)

/-- **Projective Hurwitz anchor-jet chain to RH.** -/
theorem riemannHypothesis_of_xiHurwitzAnchorJetProjectiveReflectionLaw
    (h : XiHurwitzAnchorJetProjectiveReflectionLaw) : RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hstrip := xi_divisor_support_re_mem_open_unit support
  have hre := xi_re_eq_half_of_anchorJetProjectiveReflectionCompatible
    hstrip hzero (h support)
  exact (not_lt_of_ge hre.le) (mem_rightHalf.mp hrho)

/-- RH supplies the projective Hurwitz anchor-jet reflection law with scalar one. -/
theorem xiHurwitzAnchorJetProjectiveReflectionLaw_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiHurwitzAnchorJetProjectiveReflectionLaw := by
  intro rho
  refine ⟨1, ?_⟩
  intro r hr
  have hhalf : (rho : ℂ).re = 1 / 2 :=
    xi_divisor_support_re_eq_half_of_rh hRH rho
  have href : 1 - (rho : ℂ) = (starRingEnd ℂ) (rho : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    · simp only [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring
  rw [href, one_mul]
  exact continuedHzeta_anchorJet_conj r
    (xi_divisor_support_re_mem_open_unit rho).1 hr

/-- The global projective Hurwitz anchor-jet reflection law is exactly RH. -/
theorem xiHurwitzAnchorJetProjectiveReflectionLaw_iff_riemannHypothesis :
    XiHurwitzAnchorJetProjectiveReflectionLaw ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiHurwitzAnchorJetProjectiveReflectionLaw,
    xiHurwitzAnchorJetProjectiveReflectionLaw_of_riemannHypothesis⟩

end

end RHTower
