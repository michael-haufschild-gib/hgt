import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerNumericalRadicalAndMultiplicity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ExactArithmeticSourceEffectivity

/-!
# The actual Meyer source intersection surface

Ordinary convolution trace defines the intersection pairing on the genuine Poisson
source carrier. The cohomological linear degree supplies graded Riemann–Roch;
Bézout, ampleness, and additive closure retain exactly the RH order condition.
Numerical and principal equivalence agree exactly when the Xi divisor is simple.
-/

noncomputable section
open Complex Zeta23 RHTower ContinuousLinearMap
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Centering the actual Mellin transform identifies the source trace with Weil polarization. -/
theorem meyerProductTrace_eq_xiWeilPolarization (g h : DeningerMeyerStrongLogTarget) :
    opTrace ((deningerMeyerHilbertConvolution g).comp
      (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp h))) =
      xiWeilPolarization (deningerMeyerCenteredMellin g) (deningerMeyerCenteredMellin h) := by
  have hc (s : ℂ) : 1 / 2 + I * ((s - 1 / 2) * (-I)) = s := by
    ring_nf
    rw [I_sq]
    ring
  have hh : conj (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hr (s : ℂ) : 1 / 2 + I * conj ((s - 1 / 2) * (-I)) = star (1 - s) := by
    change 1 / 2 + I * conj ((s - 1 / 2) * (-I)) = conj (1 - s)
    simp only [map_mul, map_sub, map_neg, conj_I, hh, map_one]
    ring_nf
    rw [I_sq]
    ring
  rw [← deningerMeyerHilbertConvolution_mul, deningerMeyerHilbertConvolution_opTrace]
  unfold xiWeilPolarization
  apply tsum_congr
  intro q
  rw [deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin]
  simp only [xiWeilSharp, deningerMeyerCenteredMellin_apply, xiSpectralPoint, hc, hr]
  rfl

/-- The real product trace is symmetric without an order or simplicity assumption. -/
theorem meyerSourceTrace_comm (g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace g h = meyerSourceTrace h g := by
  simp only [meyerSourceTrace, meyerProductTrace_eq_xiWeilPolarization]
  rw [xiWeilPolarization_conj_symm, Complex.conj_re]

private theorem trace_add_left (f g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace (f + g) h = meyerSourceTrace f h + meyerSourceTrace g h := by
  simp only [meyerSourceTrace_eq_degree_product, meyerCohomologyTraceDegree_mk]
  change (meyerSourceTraceDegree
    (deningerMeyerSourceConvolutionLM (f + g) (deningerMeyerSourceSharp h))).re = _
  rw [map_add, LinearMap.add_apply, map_add, Complex.add_re]
  rfl

private theorem trace_smul_left (a : ℝ) (g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace (a • g) h = a * meyerSourceTrace g h := by
  let d : DeningerMeyerStrongLogTarget →ₗ[ℝ] ℝ :=
    Complex.reCLM.toLinearMap.comp (meyerSourceTraceDegree.restrictScalars ℝ)
  have he := congrArg
    (fun L : DeningerMeyerStrongLogTarget →ₗ[ℂ] DeningerMeyerStrongLogTarget =>
      L (deningerMeyerSourceSharp h))
    ((deningerMeyerSourceConvolutionLM.restrictScalars ℝ).map_smul a g)
  change deningerMeyerSourceConvolution (a • g) (deningerMeyerSourceSharp h) =
    a • deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h) at he
  simp only [meyerSourceTrace_eq_degree_product, meyerCohomologyTraceDegree_mk]
  change d (deningerMeyerSourceConvolution (a • g) (deningerMeyerSourceSharp h)) =
    a * d (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h))
  rw [he, map_smul]
  rfl

/-- Reflection across the critical line on the actual Xi-divisor support. -/
def meyerLineReflect (rho : XiDivisorSupport) : XiDivisorSupport :=
  xiZeroReflectEquiv (xiZeroConjEquiv rho)

@[simp] theorem meyerLineReflect_val (rho : XiDivisorSupport) :
    (meyerLineReflect rho : ℂ) = star (1 - (rho : ℂ)) := by
  change 1 - conj (rho : ℂ) = conj (1 - (rho : ℂ))
  rw [map_sub, map_one]

@[simp] theorem meyerLineReflect_sq (rho : XiDivisorSupport) :
    meyerLineReflect (meyerLineReflect rho) = rho := by
  apply Subtype.ext
  change 1 - conj (1 - conj (rho : ℂ)) = (rho : ℂ)
  rw [map_sub, map_one, Complex.conj_conj]
  ring

/-- One actual point source reads the reflected Mellin value, with its full multiplicity. -/
theorem meyerPointSource_trace (rho : XiDivisorSupport) (g : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace (meyerPointSource rho) g =
      ((xiSupportMultiplicity rho : ℂ) *
        star (deningerMeyerStrongLogMellin g (meyerLineReflect rho : ℂ))).re := by
  have hp := meyerPointSource_product_trace (deningerMeyerSourceSharp g) rho 1
  rw [one_smul, one_mul] at hp
  rw [meyerSourceTrace, ← deningerMeyerHilbertConvolution_mul,
    deningerMeyerSourceConvolution_comm, deningerMeyerHilbertConvolution_mul, hp,
    deningerMeyerSourceSharp_mellin, meyerLineReflect_val]

private theorem trace_sub_left (f g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace (f - g) h = meyerSourceTrace f h - meyerSourceTrace g h := by
  have hn := trace_smul_left (-1) g h
  have hneg : (-1 : ℝ) • g = -g := neg_one_smul ℝ g
  rw [hneg, neg_one_mul] at hn
  rw [sub_eq_add_neg, trace_add_left, hn, sub_eq_add_neg]

private theorem trace_sub_right (f g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace f (g - h) = meyerSourceTrace f g - meyerSourceTrace f h := by
  rw [meyerSourceTrace_comm, trace_sub_left, meyerSourceTrace_comm g f, meyerSourceTrace_comm h f]

/-- An off-line two-point packet has an explicit strictly negative ordinary degree. -/
theorem meyerOffLinePacket_trace (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    meyerSourceTrace
      (meyerPointSource rho - meyerPointSource (meyerLineReflect rho))
      (meyerPointSource rho - meyerPointSource (meyerLineReflect rho)) =
        -((xiSupportMultiplicity rho : ℝ) + xiSupportMultiplicity (meyerLineReflect rho)) := by
  have hne : meyerLineReflect rho ≠ rho := by
    intro he
    have hr := congrArg (fun q : XiDivisorSupport => (q : ℂ).re) he
    change 1 - (rho : ℂ).re = (rho : ℂ).re at hr
    exact hoff (by linarith only [hr])
  have hself : meyerSourceTrace (meyerPointSource rho) (meyerPointSource rho) = 0 := by
    rw [meyerPointSource_trace, meyerPointSource_values, if_neg hne]
    simp only [star_zero, mul_zero, Complex.zero_re]
  have hself' : meyerSourceTrace (meyerPointSource (meyerLineReflect rho))
      (meyerPointSource (meyerLineReflect rho)) = 0 := by
    rw [meyerPointSource_trace, meyerPointSource_values, meyerLineReflect_sq, if_neg (Ne.symm hne)]
    simp only [star_zero, mul_zero, Complex.zero_re]
  have hcross : meyerSourceTrace (meyerPointSource rho)
      (meyerPointSource (meyerLineReflect rho)) = xiSupportMultiplicity rho := by
    rw [meyerPointSource_trace, meyerPointSource_values, if_pos rfl]
    simp only [star_one, mul_one, Complex.natCast_re]
  have hcross' : meyerSourceTrace (meyerPointSource (meyerLineReflect rho))
      (meyerPointSource rho) = xiSupportMultiplicity (meyerLineReflect rho) := by
    rw [meyerPointSource_trace, meyerPointSource_values, meyerLineReflect_sq, if_pos rfl]
    simp only [star_one, mul_one, Complex.natCast_re]
  rw [trace_sub_left, trace_sub_right, trace_sub_right, hself, hself', hcross, hcross']
  ring

/-- The negative source packet is constructed directly from the two reflected causal sections. -/
theorem meyerOffLinePacket_trace_neg (rho : XiDivisorSupport)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    meyerSourceTrace
      (meyerPointSource rho - meyerPointSource (meyerLineReflect rho))
      (meyerPointSource rho - meyerPointSource (meyerLineReflect rho)) < 0 := by
  rw [meyerOffLinePacket_trace rho hoff]
  have h1 : (0 : ℝ) < xiSupportMultiplicity rho := by exact_mod_cast xiSupportMultiplicity_pos rho
  have h2 : (0 : ℝ) < xiSupportMultiplicity (meyerLineReflect rho) := by
    exact_mod_cast xiSupportMultiplicity_pos (meyerLineReflect rho)
  linarith only [h1, h2]

private def poleRealLM (s : ℂ) : DeningerMeyerStrongLogTarget →ₗ[ℝ] ℝ :=
  Complex.reCLM.toLinearMap.comp ((deningerMeyerStrongLogMellinLM s).restrictScalars ℝ)

private theorem degreeH_add (x y : MeyerScalingCycle) :
    meyerDegreeH (x + y) = meyerDegreeH x + meyerDegreeH y := by
  change x.2.1 + y.2.1 + poleRealLM 0 (x.2.2 + y.2.2) =
    (x.2.1 + poleRealLM 0 x.2.2) + (y.2.1 + poleRealLM 0 y.2.2)
  rw [map_add]
  ring

private theorem degreeV_add (x y : MeyerScalingCycle) :
    meyerDegreeV (x + y) = meyerDegreeV x + meyerDegreeV y := by
  change x.1 + y.1 + poleRealLM 1 (x.2.2 + y.2.2) =
    (x.1 + poleRealLM 1 x.2.2) + (y.1 + poleRealLM 1 y.2.2)
  rw [map_add]
  ring

private theorem degreeH_smul (a : ℝ) (x : MeyerScalingCycle) :
    meyerDegreeH (a • x) = a * meyerDegreeH x := by
  change a * x.2.1 + poleRealLM 0 (a • x.2.2) = a * (x.2.1 + poleRealLM 0 x.2.2)
  rw [map_smul]
  change a * x.2.1 + a * poleRealLM 0 x.2.2 = _
  ring

private theorem degreeV_smul (a : ℝ) (x : MeyerScalingCycle) :
    meyerDegreeV (a • x) = a * meyerDegreeV x := by
  change a * x.1 + poleRealLM 1 (a • x.2.2) = a * (x.1 + poleRealLM 1 x.2.2)
  rw [map_smul]
  change a * x.1 + a * poleRealLM 1 x.2.2 = _
  ring

theorem meyerScalingPair_comm (x y : MeyerScalingCycle) :
    meyerScalingPair x y = meyerScalingPair y x := by
  simp only [meyerScalingPair, meyerSourceTrace_comm x.2.2 y.2.2]
  ring

private theorem pair_add_left (x y z : MeyerScalingCycle) :
    meyerScalingPair (x + y) z = meyerScalingPair x z + meyerScalingPair y z := by
  simp only [meyerScalingPair, degreeH_add, degreeV_add, Prod.snd_add, trace_add_left]
  ring

private theorem pair_smul_left (a : ℝ) (x y : MeyerScalingCycle) :
    meyerScalingPair (a • x) y = a * meyerScalingPair x y := by
  simp only [meyerScalingPair, degreeH_smul, degreeV_smul, Prod.smul_snd, trace_smul_left]
  ring

/-- The original source product trace defines a real bilinear intersection pairing. -/
def meyerScalingBilinear : MeyerScalingCycle →ₗ[ℝ] MeyerScalingCycle →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ meyerScalingPair pair_add_left pair_smul_left
    (fun x y z => by
      rw [meyerScalingPair_comm, pair_add_left, meyerScalingPair_comm y x,
        meyerScalingPair_comm z x])
    (fun a x y => by
      rw [meyerScalingPair_comm, pair_smul_left, meyerScalingPair_comm y x, smul_eq_mul])

private theorem trace_zero_left (g : DeningerMeyerStrongLogTarget) : meyerSourceTrace 0 g = 0 := by
  simpa only [map_zero] using meyerSourceTrace_boundary_left 0 g

private theorem trace_zero_right (g : DeningerMeyerStrongLogTarget) : meyerSourceTrace g 0 = 0 := by
  simpa only [map_zero] using meyerSourceTrace_boundary_right g 0

/-- The genuine Meyer source extension is a polar surface with the original two pole degrees. -/
def meyerScalingSurface : PolarSurface MeyerScalingCycle where
  pair := meyerScalingBilinear
  pair_comm := meyerScalingPair_comm
  H := (1, 0, 0)
  V := (0, 1, 0)
  pair_H_H := by
    change meyerScalingPair (1, 0, 0) (1, 0, 0) = 0
    simp [meyerScalingPair, meyerDegreeH, meyerDegreeV, meyerPoleA, meyerPoleB, trace_zero_left]
  pair_V_V := by
    change meyerScalingPair (0, 1, 0) (0, 1, 0) = 0
    simp [meyerScalingPair, meyerDegreeH, meyerDegreeV, meyerPoleA, meyerPoleB, trace_zero_left]
  pair_H_V := by
    change meyerScalingPair (1, 0, 0) (0, 1, 0) = 1
    simp [meyerScalingPair, meyerDegreeH, meyerDegreeV, meyerPoleA, meyerPoleB, trace_zero_left]

@[simp] theorem meyerScalingSurface_pair (x y : MeyerScalingCycle) :
    meyerScalingSurface.pair x y = meyerScalingPair x y := rfl

theorem meyerScalingSurface_pair_H (x : MeyerScalingCycle) :
    meyerScalingSurface.pair x meyerScalingSurface.H = meyerDegreeH x := by
  change meyerScalingPair x (1, 0, 0) = _
  simp [meyerScalingPair, meyerDegreeH, meyerDegreeV, meyerPoleA, meyerPoleB, trace_zero_right]

theorem meyerScalingSurface_pair_V (x : MeyerScalingCycle) :
    meyerScalingSurface.pair x meyerScalingSurface.V = meyerDegreeV x := by
  change meyerScalingPair x (0, 1, 0) = _
  simp [meyerScalingPair, meyerDegreeH, meyerDegreeV, meyerPoleA, meyerPoleB, trace_zero_right]

/-- The actual source trace is exactly the surface defect. -/
theorem meyerScalingSurface_defect (x y : MeyerScalingCycle) :
    meyerScalingSurface.defect x y = meyerSourceTrace x.2.2 y.2.2 := by
  rw [PolarSurface.defect, PolarSurface.polar, meyerScalingSurface_pair_H,
    meyerScalingSurface_pair_V, meyerScalingSurface_pair_H, meyerScalingSurface_pair_V,
    meyerScalingSurface_pair, meyerScalingPair]
  ring

/-- The enlarged carrier changes principal representatives, but leaves the exact order obligation. -/
theorem meyerScalingSurface_hodgeIndex_iff : meyerScalingSurface.HodgeIndex ↔ RiemannHypothesis := by
  rw [meyerScalingSurface.hodgeIndex_iff_castelnuovoSeveri,
    meyerScalingSurface.castelnuovoSeveri_iff_defect_nonneg,
    ← meyerSourceTrace_nonneg_iff_riemannHypothesis]
  simp only [meyerScalingSurface_defect]
  constructor
  · intro h g
    exact h (0, 0, g)
  · intro h x
    exact h x.2.2

/-- A source reserve obtained from the genuine cohomological linear degree. -/
def meyerDegreeSourceReserve (x : MeyerScalingCycle) : ℝ :=
  (meyerCohomologyTraceDegree (Submodule.Quotient.mk
    (deningerMeyerSourceConvolution x.2.2 (deningerMeyerSourceSharp x.2.2)))).re

/-- Graded effectivity read from the actual source product degree. -/
def meyerDegreeSourceCone : Set MeyerScalingCycle :=
  meyerScalingSurface.gradedSourceCone meyerDegreeSourceReserve

theorem meyerDegreeSourceCone_eq_positiveCone :
    meyerDegreeSourceCone = meyerScalingSurface.positiveCone := by
  have he : meyerDegreeSourceReserve = fun x => meyerScalingSurface.defect x x := by
    funext x
    rw [meyerScalingSurface_defect, meyerSourceTrace_eq_degree_product]
    rfl
  rw [meyerDegreeSourceCone, he, PolarSurface.gradedSourceCone_defect_eq_positiveCone]

/-- A genuine linear product degree supplies source Riemann–Roch unconditionally. -/
theorem meyerDegreeSourceCone_riemannRoch :
    meyerScalingSurface.RiemannRochAxiom meyerDegreeSourceCone := by
  rw [meyerDegreeSourceCone_eq_positiveCone]
  exact meyerScalingSurface.positiveCone_riemannRoch

/-- Positivity of this same degree cone is exactly RH. -/
theorem meyerDegreeSourceCone_bezout_iff :
    meyerScalingSurface.BezoutAxiom meyerDegreeSourceCone ↔ RiemannHypothesis := by
  rw [meyerDegreeSourceCone_eq_positiveCone,
    ← meyerScalingSurface.hodgeIndex_iff_positiveCone_bezout, meyerScalingSurface_hodgeIndex_iff]

theorem meyerDegreeSourceCone_ample_iff :
    meyerScalingSurface.AmpleAxiom meyerDegreeSourceCone ↔ RiemannHypothesis := by
  rw [meyerDegreeSourceCone_eq_positiveCone, meyerScalingSurface.positiveCone_ample_iff_hodgeIndex,
    meyerScalingSurface_hodgeIndex_iff]

/-- Even additive closure of the exact source degree cone carries the same order condition. -/
theorem meyerDegreeSourceCone_add_closed_iff :
    (∀ x ∈ meyerDegreeSourceCone, ∀ y ∈ meyerDegreeSourceCone, x + y ∈ meyerDegreeSourceCone) ↔
      RiemannHypothesis := by
  rw [meyerDegreeSourceCone_eq_positiveCone,
    meyerScalingSurface.positiveCone_add_closed_iff_hodgeIndex, meyerScalingSurface_hodgeIndex_iff]

/-- Every genuine principal representative lies in the numerical radical. -/
theorem meyerScalingSurface_principal_radical (f : DeningerMeyerCap) (x : MeyerScalingCycle) :
    meyerScalingSurface.pair (meyerPrincipalCycle f) x = 0 :=
  meyerPrincipalCycle_pair_left f x

/-- Equality of principal and numerical equivalence requires simplicity, independently of the order condition. -/
theorem meyerScalingSurface_radical_eq_principal_iff_simple :
    (∀ x : MeyerScalingCycle,
      (∀ y : MeyerScalingCycle, meyerScalingSurface.pair x y = 0) ↔
        ∃ f : DeningerMeyerCap, x = meyerPrincipalCycle f) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 :=
  meyerScalingPair_radical_eq_principal_iff_simple

/-- Ordinary trace is positive and faithful on the full Poisson quotient exactly under RH and simplicity. -/
theorem meyerSourceTrace_positive_faithful_iff :
    (∀ g : DeningerMeyerStrongLogTarget, 0 ≤ meyerSourceTrace g g ∧
      (meyerSourceTrace g g = 0 ↔ g ∈ LinearMap.range deningerMeyerStrongLogSumLM)) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    refine ⟨meyerSourceTrace_nonneg_iff_riemannHypothesis.mp (fun g => (h g).1), ?_⟩
    intro rho
    by_contra hne
    have hm : 1 < xiSupportMultiplicity rho := by
      have hp := xiSupportMultiplicity_pos rho
      omega
    obtain ⟨g, hrad, hnot⟩ := exists_meyer_trace_radical_not_boundary_of_multiple rho hm
    exact hnot ((h g).2.mp (hrad g))
  · rintro ⟨hRH, hs⟩ g
    refine ⟨meyerSourceTrace_nonneg_iff_riemannHypothesis.mpr hRH g, ?_⟩
    constructor
    · intro hz
      apply (meyerSourceTrace_radical_eq_boundary_iff_simple.mpr hs g).mp
      intro h
      have hb := meyerScalingSurface.defect_sq_le_of_hodgeIndex
        (meyerScalingSurface_hodgeIndex_iff.mpr hRH) (0, 0, g) (0, 0, h)
      simp only [meyerScalingSurface_defect] at hb
      rw [hz, zero_mul] at hb
      nlinarith only [hb, sq_nonneg (meyerSourceTrace g h)]
    · rintro ⟨f, rfl⟩
      exact meyerSourceTrace_boundary_left f _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerProductTrace_eq_xiWeilPolarization
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerOffLinePacket_trace_neg
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerScalingSurface_hodgeIndex_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeSourceCone_riemannRoch
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeSourceCone_bezout_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeSourceCone_ample_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerDegreeSourceCone_add_closed_iff
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerScalingSurface_radical_eq_principal_iff_simple
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerSourceTrace_positive_faithful_iff
