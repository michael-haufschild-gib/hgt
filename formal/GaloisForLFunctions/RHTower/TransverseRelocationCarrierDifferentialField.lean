import GaloisForLFunctions.RHTower.TransverseRelocationCarrierAnalyticCompletion
import GaloisForLFunctions.RHTower.NymanMellinGaugeCollapse
import GaloisForLFunctions.HTGeometry.DAGaugeDivisorBlindness
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicAdjoin
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative

/-!
# Differential-translation invariants of the transverse relocation carrier

This leaf realizes the card's concrete base `ℂ(s, exp(2s))` inside the upper-end meromorphic
field. It proves complete translated all-jet field equality, exact rational-base differential
matroid rank equality, and equality of logarithmic source classes for every displacement pair.
-/

open Complex Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NymanUpper

noncomputable section

local instance transverseFieldDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance transverseFieldDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance transverseFieldComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance transverseFieldRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance transverseFieldRatDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance transverseFieldRatDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncDifferentialAlgebra

local instance transverseFieldCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_algebraMap upperEndComplexToMero.injective

def transverseRelocationEnvelope (a : ℝ) (s : ℂ) : ℂ :=
  coshQuartetEnvelope a (s - (1 / 2 : ℂ))

theorem transverseRelocationEnvelope_analyticOnNhd (a : ℝ) :
    AnalyticOnNhd ℂ (transverseRelocationEnvelope a) Set.univ := by
  intro s _
  exact (coshQuartetEnvelope_analyticAt a _).comp
    (analyticAt_id.sub analyticAt_const)

def transverseRelocationEnvelopeUpperEndMero (a : ℝ) : upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  exact upperMeroOf (H := 0) (transverseRelocationEnvelope a)
    ((transverseRelocationEnvelope_analyticOnNhd a).mono (Set.subset_univ _))

theorem expMero_two_mul_neg_two :
    letI := isDomain_upperEndAnalyticSubring
    expMero 2 * expMero (-2) = 1 := by
  letI := isDomain_upperEndAnalyticSubring
  have hplus := analyticOnNhd_expLinear (2 : ℂ) 0
  have hminus := analyticOnNhd_expLinear (-2 : ℂ) 0
  have hprod := upperMeroOf_mul hplus hminus
  have hone : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (upperTail 0) := analyticOnNhd_const
  have hfun : (fun z : ℂ => Complex.exp (2 * z) * Complex.exp (-2 * z)) =
      (fun _ : ℂ => (1 : ℂ)) := by
    funext z
    rw [← Complex.exp_add]
    ring_nf
    simp
  have hcongr := upperMeroOf_congr (hplus.mul hminus) hone hfun
  rw [hcongr, upperMeroOf_const] at hprod
  simpa [expMero] using hprod.symm

theorem expMero_two_ne_zero :
    letI := isDomain_upperEndAnalyticSubring
    expMero 2 ≠ 0 := by
  letI := isDomain_upperEndAnalyticSubring
  intro hzero
  have hprod := expMero_two_mul_neg_two
  rw [hzero, zero_mul] at hprod
  exact zero_ne_one hprod

theorem expMero_neg_two_eq_inv :
    letI := isDomain_upperEndAnalyticSubring
    expMero (-2) = (expMero 2)⁻¹ := by
  letI := isDomain_upperEndAnalyticSubring
  apply (mul_left_cancel₀ expMero_two_ne_zero)
  rw [expMero_two_mul_neg_two, mul_inv_cancel₀ expMero_two_ne_zero]

theorem upperMeroOf_const_mul_expLinear (c lam : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    upperMeroOf (H := 0) (fun z : ℂ => c * Complex.exp (lam * z))
      (by
        exact (analyticOnNhd_const (E := ℂ) (s := upperTail 0)).mul
          (analyticOnNhd_expLinear lam 0)) =
      algebraMap ℂ upperEndMeroField c * expMero lam := by
  letI := isDomain_upperEndAnalyticSubring
  have hc : AnalyticOnNhd ℂ (fun _ : ℂ => c) (upperTail 0) :=
    analyticOnNhd_const
  have hmul := upperMeroOf_mul hc (analyticOnNhd_expLinear lam 0)
  rw [upperMeroOf_const] at hmul
  simpa [expMero] using hmul

theorem transverseRelocationEnvelopeUpperEndMero_eq_expMero
    (a : ℝ) :
    letI := isDomain_upperEndAnalyticSubring
    transverseRelocationEnvelopeUpperEndMero a =
      algebraMap ℂ upperEndMeroField (1 / 4) *
        (algebraMap ℂ upperEndMeroField (Complex.exp (-1)) * expMero 2 +
          algebraMap ℂ upperEndMeroField (Complex.exp 1) * expMero (-2) +
          algebraMap ℂ upperEndMeroField (2 * Complex.cosh (2 * (a : ℂ)))) := by
  letI := isDomain_upperEndAnalyticSubring
  let g : ℂ → ℂ := fun z => (1 / 4 : ℂ) *
    (Complex.exp (-1) * Complex.exp (2 * z) +
      Complex.exp 1 * Complex.exp (-2 * z) +
      2 * Complex.cosh (2 * (a : ℂ)))
  have hg : AnalyticOnNhd ℂ g (upperTail 0) := by
    dsimp [g]
    exact analyticOnNhd_const.mul
      (((analyticOnNhd_const.mul (analyticOnNhd_expLinear 2 0)).add
        (analyticOnNhd_const.mul (analyticOnNhd_expLinear (-2) 0))).add
        analyticOnNhd_const)
  have hfun : transverseRelocationEnvelope a = g := by
    funext z
    have htwo := two_mul_coshQuartetEnvelope a (z - (1 / 2 : ℂ))
    have hp : Complex.exp (2 * (z - (1 / 2 : ℂ))) =
        Complex.exp (-1) * Complex.exp (2 * z) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hm : Complex.exp (-(2 * (z - (1 / 2 : ℂ)))) =
        Complex.exp 1 * Complex.exp (-2 * z) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    change coshQuartetEnvelope a (z - (1 / 2 : ℂ)) = g z
    dsimp [g]
    rw [Complex.cosh] at htwo
    rw [hp, hm] at htwo
    linear_combination (1 / 2 : ℂ) * htwo
  rw [transverseRelocationEnvelopeUpperEndMero]
  have hcongr := upperMeroOf_congr (H := 0) (K := 0)
    ((transverseRelocationEnvelope_analyticOnNhd a).mono
      (Set.subset_univ (upperTail 0))) hg hfun
  have hc0 : AnalyticOnNhd ℂ (fun _ : ℂ => (1 / 4 : ℂ)) (upperTail 0) :=
    analyticOnNhd_const
  have hp : AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.exp (-1) * Complex.exp (2 * z)) (upperTail 0) :=
    analyticOnNhd_const.mul (analyticOnNhd_expLinear 2 0)
  have hm : AnalyticOnNhd ℂ
      (fun z : ℂ => Complex.exp 1 * Complex.exp (-2 * z)) (upperTail 0) :=
    analyticOnNhd_const.mul (analyticOnNhd_expLinear (-2) 0)
  have hc : AnalyticOnNhd ℂ
      (fun _ : ℂ => 2 * Complex.cosh (2 * (a : ℂ))) (upperTail 0) :=
    analyticOnNhd_const
  have hsum : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        Complex.exp (-1) * Complex.exp (2 * z) +
          Complex.exp 1 * Complex.exp (-2 * z)) (upperTail 0) := hp.add hm
  have hinner : AnalyticOnNhd ℂ
      (fun z : ℂ =>
        Complex.exp (-1) * Complex.exp (2 * z) +
          Complex.exp 1 * Complex.exp (-2 * z) +
            2 * Complex.cosh (2 * (a : ℂ))) (upperTail 0) := hsum.add hc
  have houter := upperMeroOf_mul hc0 hinner
  have hinnerEq := upperMeroOf_add hsum hc
  have hsumEq := upperMeroOf_add hp hm
  rw [hcongr]
  rw [show upperMeroOf g hg =
      upperMeroOf (fun _ : ℂ => (1 / 4 : ℂ)) hc0 *
        upperMeroOf (fun z : ℂ =>
          Complex.exp (-1) * Complex.exp (2 * z) +
            Complex.exp 1 * Complex.exp (-2 * z) +
              2 * Complex.cosh (2 * (a : ℂ))) hinner by
        simpa [g] using houter]
  rw [hinnerEq, hsumEq]
  rw [upperMeroOf_const_mul_expLinear, upperMeroOf_const_mul_expLinear]
  rw [upperMeroOf_const, upperMeroOf_const]

def transverseExponentialBase : IntermediateField (RatFunc ℂ) upperEndMeroField := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  exact differentialAdjoin (RatFunc ℂ) ({expMero 2} : Set upperEndMeroField)

theorem expMero_two_mem_transverseExponentialBase :
    letI := isDomain_upperEndAnalyticSubring
    expMero 2 ∈ transverseExponentialBase := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := upperEndMeroFieldDifferential
  letI : DifferentialAlgebra (RatFunc ℂ) upperEndMeroField :=
    upperEndRatfuncDifferentialAlgebra
  exact subset_differentialAdjoin (RatFunc ℂ)
    (s := ({expMero 2} : Set upperEndMeroField)) (Set.mem_singleton _)

theorem expMero_neg_two_mem_transverseExponentialBase :
    letI := isDomain_upperEndAnalyticSubring
    expMero (-2) ∈ transverseExponentialBase := by
  letI := isDomain_upperEndAnalyticSubring
  rw [expMero_neg_two_eq_inv]
  exact (transverseExponentialBase).inv_mem expMero_two_mem_transverseExponentialBase

theorem complexConstant_mem_transverseExponentialBase (c : ℂ) :
    letI := isDomain_upperEndAnalyticSubring
    algebraMap ℂ upperEndMeroField c ∈ transverseExponentialBase := by
  letI := isDomain_upperEndAnalyticSubring
  change upperEndComplexToMero c ∈ transverseExponentialBase
  rw [← upperEnd_ratfunc_algebraMap_complex c]
  exact (transverseExponentialBase).algebraMap_mem (algebraMap ℂ (RatFunc ℂ) c)

theorem transverseRelocationEnvelopeUpperEndMero_mem_base (a : ℝ) :
    letI := isDomain_upperEndAnalyticSubring
    transverseRelocationEnvelopeUpperEndMero a ∈ transverseExponentialBase := by
  letI := isDomain_upperEndAnalyticSubring
  rw [transverseRelocationEnvelopeUpperEndMero_eq_expMero]
  apply (transverseExponentialBase).mul_mem
    (complexConstant_mem_transverseExponentialBase (1 / 4 : ℂ))
  apply (transverseExponentialBase).add_mem
  · apply (transverseExponentialBase).add_mem
    · exact (transverseExponentialBase).mul_mem
        (complexConstant_mem_transverseExponentialBase (Complex.exp (-1)))
        expMero_two_mem_transverseExponentialBase
    · exact (transverseExponentialBase).mul_mem
        (complexConstant_mem_transverseExponentialBase (Complex.exp 1))
        expMero_neg_two_mem_transverseExponentialBase
  · exact complexConstant_mem_transverseExponentialBase
      (2 * Complex.cosh (2 * (a : ℂ)))

theorem upperEndTranslationMeroEquiv_complexConstant (h c : ℂ) :
    upperEndTranslationMeroEquiv h (algebraMap ℂ upperEndMeroField c) =
      algebraMap ℂ upperEndMeroField c := by
  exact (upperEndTranslationMeroDifferentialAlgEquiv h).toAlgEquiv.commutes c

theorem upperEndTranslationMeroEquiv_expMero (lam h : ℂ) :
    upperEndTranslationMeroEquiv h (expMero lam) =
      algebraMap ℂ upperEndMeroField (Complex.exp (lam * h)) * expMero lam := by
  rw [← upperMeroOf_const_mul_expLinear]
  rw [expMero, upperMeroOf, upperMeroOf,
    upperEndTranslationMeroEquiv_algebraMap]
  congr 1
  apply Subtype.ext
  change upperEndTranslateGerm h
      ((fun z : ℂ => Complex.exp (lam * z)) : Filter.Germ upperEndFilter ℂ) =
    ((fun z : ℂ => Complex.exp (lam * h) * Complex.exp (lam * z)) :
      Filter.Germ upperEndFilter ℂ)
  rw [upperEndTranslateGerm_coe]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z => by
    change Complex.exp (lam * (z + h)) =
      Complex.exp (lam * h) * Complex.exp (lam * z)
    rw [← Complex.exp_add]
    congr 1
    ring

theorem upperEndTranslationMeroEquiv_transverseEnvelope_mem_base
    (a : ℝ) (h : ℂ) :
    upperEndTranslationMeroEquiv h (transverseRelocationEnvelopeUpperEndMero a) ∈
      transverseExponentialBase := by
  rw [transverseRelocationEnvelopeUpperEndMero_eq_expMero,
    map_mul, map_add, map_add]
  simp only [map_mul, upperEndTranslationMeroEquiv_complexConstant,
    upperEndTranslationMeroEquiv_expMero]
  apply (transverseExponentialBase).mul_mem
    (complexConstant_mem_transverseExponentialBase (1 / 4 : ℂ))
  apply (transverseExponentialBase).add_mem
  · apply (transverseExponentialBase).add_mem
    · apply (transverseExponentialBase).mul_mem
        (complexConstant_mem_transverseExponentialBase (Complex.exp (-1)))
      exact (transverseExponentialBase).mul_mem
        (complexConstant_mem_transverseExponentialBase (Complex.exp (2 * h)))
        expMero_two_mem_transverseExponentialBase
    · apply (transverseExponentialBase).mul_mem
        (complexConstant_mem_transverseExponentialBase (Complex.exp 1))
      exact (transverseExponentialBase).mul_mem
        (complexConstant_mem_transverseExponentialBase (Complex.exp (-2 * h)))
        expMero_neg_two_mem_transverseExponentialBase
  · exact (transverseExponentialBase).mul_mem
      (complexConstant_mem_transverseExponentialBase 2)
      (complexConstant_mem_transverseExponentialBase
        (Complex.cosh (2 * (a : ℂ))))

theorem transverseRelocationEnvelopeUpperEndMero_ne_zero (a : ℝ) :
    transverseRelocationEnvelopeUpperEndMero a ≠ 0 := by
  intro hzero
  have hanalytic : upperAnalyticOf (transverseRelocationEnvelope a)
      ((transverseRelocationEnvelope_analyticOnNhd a).mono
        (Set.subset_univ (upperTail 0))) = 0 := by
    apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
    simpa [transverseRelocationEnvelopeUpperEndMero, upperMeroOf] using hzero
  have hgerm := congrArg Subtype.val hanalytic
  change ((transverseRelocationEnvelope a : ℂ → ℂ) : Filter.Germ upperEndFilter ℂ) = 0 at hgerm
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at hgerm
  obtain ⟨H, -, hH⟩ := upperEndFilter_basis.mem_iff.mp hgerm
  let z : ℂ := ((|a| + 3 / 2 : ℝ) : ℂ) +
    Complex.I * ((H + 1 : ℝ) : ℂ)
  have hzTail : z ∈ upperTail H := by
    simp [z, upperTail]
  have hz0 := hH hzTail
  have hminusRe : (z - (1 / 2 : ℂ) - (a : ℂ)).re ≠ 0 := by
    simp [z]
    have haAbs : a ≤ |a| := le_abs_self a
    linarith
  have hplusRe : (z - (1 / 2 : ℂ) + (a : ℂ)).re ≠ 0 := by
    simp [z]
    have haAbs : -a ≤ |a| := neg_le_abs a
    linarith
  apply mul_ne_zero (cosh_ne_zero_of_re_ne_zero hminusRe)
    (cosh_ne_zero_of_re_ne_zero hplusRe)
  simpa [transverseRelocationEnvelope, coshQuartetEnvelope] using hz0

theorem upperEndTranslationMeroEquiv_transverseEnvelope_ne_zero
    (a : ℝ) (h : ℂ) :
    upperEndTranslationMeroEquiv h (transverseRelocationEnvelopeUpperEndMero a) ≠ 0 := by
  simpa only [map_zero] using (upperEndTranslationMeroEquiv h).injective.ne
    (transverseRelocationEnvelopeUpperEndMero_ne_zero a)

def transverseGammaUpperEndMero (beta : ℝ) : upperEndMeroField :=
  upperMeroOf (H := 0) (liReflectedGammaCarrier beta)
    ((liReflectedGammaCarrier_analyticOnNhd beta).mono
      (Set.subset_univ (upperTail 0)))

def transverseCarrierUpperEndMero (beta a : ℝ) : upperEndMeroField :=
  upperMeroOf (H := 0) (transverseRelocationCarrier beta a)
    ((transverseRelocationCarrier_analyticOnNhd beta a).mono
      (Set.subset_univ (upperTail 0)))

theorem transverseCarrierUpperEndMero_eq_envelope_mul_gamma (beta a : ℝ) :
    transverseCarrierUpperEndMero beta a =
      transverseRelocationEnvelopeUpperEndMero a * transverseGammaUpperEndMero beta := by
  have henv := (transverseRelocationEnvelope_analyticOnNhd a).mono
    (Set.subset_univ (upperTail 0))
  have hgamma := (liReflectedGammaCarrier_analyticOnNhd beta).mono
    (Set.subset_univ (upperTail 0))
  have hmul := upperMeroOf_mul henv hgamma
  have hfun : transverseRelocationCarrier beta a =
      fun s => transverseRelocationEnvelope a s * liReflectedGammaCarrier beta s := by
    funext s
    simp only [transverseRelocationCarrier, reflectedGammaQuartetCarrier,
      transverseRelocationEnvelope, liReflectedGammaCarrier]
    ring
  have hcongr := upperMeroOf_congr (H := 0) (K := 0)
    ((transverseRelocationCarrier_analyticOnNhd beta a).mono
      (Set.subset_univ (upperTail 0))) (henv.mul hgamma) hfun
  exact hcongr.trans (by simpa [transverseRelocationEnvelopeUpperEndMero,
    transverseGammaUpperEndMero] using hmul)

def transverseGammaTranslateFamily (beta : ℝ) (h : ℂ) : upperEndMeroField :=
  upperEndTranslationMeroEquiv h (transverseGammaUpperEndMero beta)

def transverseCarrierTranslateFamily (beta a : ℝ) (h : ℂ) : upperEndMeroField :=
  upperEndTranslationMeroEquiv h (transverseCarrierUpperEndMero beta a)

theorem transverseCarrierTranslateFamily_eq_gauge_mul
    (beta a : ℝ) (h : ℂ) :
    transverseCarrierTranslateFamily beta a h =
      upperEndTranslationMeroEquiv h (transverseRelocationEnvelopeUpperEndMero a) *
        transverseGammaTranslateFamily beta h := by
  rw [transverseCarrierTranslateFamily, transverseGammaTranslateFamily,
    transverseCarrierUpperEndMero_eq_envelope_mul_gamma, map_mul]

def transverseEnvelopeBaseGauge (a : ℝ) (h : ℂ) : transverseExponentialBase :=
  ⟨upperEndTranslationMeroEquiv h (transverseRelocationEnvelopeUpperEndMero a),
    upperEndTranslationMeroEquiv_transverseEnvelope_mem_base a h⟩

theorem transverseEnvelopeBaseGauge_ne_zero (a : ℝ) (h : ℂ) :
    transverseEnvelopeBaseGauge a h ≠ 0 := by
  intro hzero
  exact upperEndTranslationMeroEquiv_transverseEnvelope_ne_zero a h
    (congrArg Subtype.val hzero)

theorem transverseCarrierTranslateFamily_differentialAdjoin_eq
    (beta a : ℝ) :
    letI : Differential transverseExponentialBase :=
      derivationClosedDifferential transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
      derivationClosed_differentialAlgebra transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    differentialAdjoin transverseExponentialBase
        (Set.range (transverseCarrierTranslateFamily beta a)) =
      differentialAdjoin transverseExponentialBase
        (Set.range (transverseGammaTranslateFamily beta)) := by
  let hclosed : DerivationClosed transverseExponentialBase := by
    rw [transverseExponentialBase]
    exact derivationClosed_differentialAdjoin (RatFunc ℂ)
      ({expMero 2} : Set upperEndMeroField)
  letI : Differential transverseExponentialBase :=
    derivationClosedDifferential transverseExponentialBase hclosed
  letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
    derivationClosed_differentialAlgebra transverseExponentialBase hclosed
  have hfield := differentialAdjoin_gauge_eq
    (transverseGammaTranslateFamily beta) (transverseEnvelopeBaseGauge a)
    (transverseEnvelopeBaseGauge_ne_zero a)
  have hfamily : (fun h => algebraMap transverseExponentialBase upperEndMeroField
      (transverseEnvelopeBaseGauge a h) * transverseGammaTranslateFamily beta h) =
      transverseCarrierTranslateFamily beta a := by
    funext h
    exact (transverseCarrierTranslateFamily_eq_gauge_mul beta a h).symm
  simpa only [hfamily] using hfield

theorem transverseCarrierTranslateFamily_allJets_adjoin_eq
    (beta a : ℝ) :
    letI : Differential transverseExponentialBase :=
      derivationClosedDifferential transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
      derivationClosed_differentialAlgebra transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    IntermediateField.adjoin transverseExponentialBase
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (transverseCarrierTranslateFamily beta a p.1)) =
      IntermediateField.adjoin transverseExponentialBase
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (transverseGammaTranslateFamily beta p.1)) := by
  let hclosed := derivationClosed_differentialAdjoin (RatFunc ℂ)
    ({expMero 2} : Set upperEndMeroField)
  letI : Differential transverseExponentialBase :=
    derivationClosedDifferential transverseExponentialBase hclosed
  letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
    derivationClosed_differentialAlgebra transverseExponentialBase hclosed
  rw [← differentialAdjoin_range_eq_adjoin_jetRange
      transverseExponentialBase (transverseCarrierTranslateFamily beta a),
    ← differentialAdjoin_range_eq_adjoin_jetRange
      transverseExponentialBase (transverseGammaTranslateFamily beta)]
  exact transverseCarrierTranslateFamily_differentialAdjoin_eq beta a

theorem transverseCarrierTranslateFamily_two_displacements_allJets_adjoin_eq
    (beta a b : ℝ) :
    letI : Differential transverseExponentialBase :=
      derivationClosedDifferential transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
      derivationClosed_differentialAlgebra transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    IntermediateField.adjoin transverseExponentialBase
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (transverseCarrierTranslateFamily beta a p.1)) =
      IntermediateField.adjoin transverseExponentialBase
        (Set.range fun p : ℂ × ℕ => differentialJet p.2
          (transverseCarrierTranslateFamily beta b p.1)) := by
  let hclosed := derivationClosed_differentialAdjoin (RatFunc ℂ)
    ({expMero 2} : Set upperEndMeroField)
  letI : Differential transverseExponentialBase :=
    derivationClosedDifferential transverseExponentialBase hclosed
  letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
    derivationClosed_differentialAlgebra transverseExponentialBase hclosed
  rw [transverseCarrierTranslateFamily_allJets_adjoin_eq beta a,
    transverseCarrierTranslateFamily_allJets_adjoin_eq beta b]

theorem expMero_two_differentialAlgebraicOver_ratFunc :
    DifferentialAlgebraicOver (RatFunc ℂ) (expMero 2) := by
  exact differentialAlgebraicOver_expMero 2

theorem transverseCarrierTranslateFamily_differentialMatroid_eRk_eq_base
    (beta a b : ℝ) :
    letI : Differential transverseExponentialBase :=
      derivationClosedDifferential transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
      derivationClosed_differentialAlgebra transverseExponentialBase
        (derivationClosed_differentialAdjoin (RatFunc ℂ)
          ({expMero 2} : Set upperEndMeroField))
    (differentialMatroid transverseExponentialBase upperEndMeroField).eRk
        (Set.range (transverseCarrierTranslateFamily beta a)) =
      (differentialMatroid transverseExponentialBase upperEndMeroField).eRk
        (Set.range (transverseCarrierTranslateFamily beta b)) := by
  let hclosed : DerivationClosed transverseExponentialBase := by
    rw [transverseExponentialBase]
    exact derivationClosed_differentialAdjoin (RatFunc ℂ)
      ({expMero 2} : Set upperEndMeroField)
  letI : Differential transverseExponentialBase :=
    derivationClosedDifferential transverseExponentialBase hclosed
  letI : DifferentialAlgebra transverseExponentialBase upperEndMeroField :=
    derivationClosed_differentialAlgebra transverseExponentialBase hclosed
  rw [← Matroid.eRk_closure_eq,
    ← Matroid.eRk_closure_eq
      (X := Set.range (transverseCarrierTranslateFamily beta b)),
    differentialMatroid_closure_eq_differentialClosure,
    differentialMatroid_closure_eq_differentialClosure]
  unfold differentialClosure
  rw [transverseCarrierTranslateFamily_differentialAdjoin_eq beta a,
    transverseCarrierTranslateFamily_differentialAdjoin_eq beta b]

theorem transverseCarrierTranslateFamily_differentialMatroid_eRk_eq
    (beta a b : ℝ) :
    (differentialMatroid (RatFunc ℂ) upperEndMeroField).eRk
        (Set.range (transverseCarrierTranslateFamily beta a)) =
      (differentialMatroid (RatFunc ℂ) upperEndMeroField).eRk
        (Set.range (transverseCarrierTranslateFamily beta b)) := by
  have hDA : ∀ g ∈ ({expMero 2} : Set upperEndMeroField),
      DifferentialAlgebraicOver (RatFunc ℂ) g := by
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    simpa [hg] using expMero_two_differentialAlgebraicOver_ratFunc
  have hmatroid :=
    differentialMatroidOverDifferentialAdjoin_eq_of_differentialAlgebraicOver
      (F := RatFunc ℂ) (E := upperEndMeroField) hDA
  rw [← hmatroid]
  simpa [differentialMatroidOverDifferentialAdjoin,
    transverseExponentialBase] using
    transverseCarrierTranslateFamily_differentialMatroid_eRk_eq_base beta a b

theorem transverseGammaUpperEndMero_ne_zero (beta : ℝ) :
    transverseGammaUpperEndMero beta ≠ 0 := by
  intro hzero
  have hanalytic : upperAnalyticOf (liReflectedGammaCarrier beta)
      ((liReflectedGammaCarrier_analyticOnNhd beta).mono
        (Set.subset_univ (upperTail 0))) = 0 := by
    apply IsFractionRing.injective upperEndAnalyticSubring upperEndMeroField
    simpa [transverseGammaUpperEndMero, upperMeroOf] using hzero
  have hgerm := congrArg Subtype.val hanalytic
  change ((liReflectedGammaCarrier beta : ℂ → ℂ) :
      Filter.Germ upperEndFilter ℂ) = 0 at hgerm
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq] at hgerm
  obtain ⟨H, -, hH⟩ := upperEndFilter_basis.mem_iff.mp hgerm
  let z : ℂ := (3 / 2 : ℂ) + Complex.I * ((H + 1 : ℝ) : ℂ)
  have hzTail : z ∈ upperTail H := by
    simp [z, upperTail]
  have hz0 := hH hzTail
  have hzRe : z.re ≠ 1 / 2 := by
    norm_num [z]
  exact hzRe (liReflectedGammaCarrier_zero_re_eq_half hz0)

theorem transverseCarrierUpperEndMero_ne_zero (beta a : ℝ) :
    transverseCarrierUpperEndMero beta a ≠ 0 := by
  rw [transverseCarrierUpperEndMero_eq_envelope_mul_gamma]
  exact mul_ne_zero (transverseRelocationEnvelopeUpperEndMero_ne_zero a)
    (transverseGammaUpperEndMero_ne_zero beta)

def transverseUpperEndLogDeriv (x : upperEndMeroField) : upperEndMeroField :=
  x′ / x

theorem transverseUpperEndLogDeriv_mul
    {x y : upperEndMeroField} (hx : x ≠ 0) (hy : y ≠ 0) :
    transverseUpperEndLogDeriv (x * y) =
      transverseUpperEndLogDeriv x + transverseUpperEndLogDeriv y := by
  simp only [transverseUpperEndLogDeriv]
  rw [differential_deriv_mul]
  field_simp

theorem transverseCarrierUpperEndLogDeriv_eq_envelope_add_gamma
    (beta a : ℝ) :
    transverseUpperEndLogDeriv (transverseCarrierUpperEndMero beta a) =
      transverseUpperEndLogDeriv (transverseRelocationEnvelopeUpperEndMero a) +
        transverseUpperEndLogDeriv (transverseGammaUpperEndMero beta) := by
  rw [transverseCarrierUpperEndMero_eq_envelope_mul_gamma]
  exact transverseUpperEndLogDeriv_mul
    (transverseRelocationEnvelopeUpperEndMero_ne_zero a)
    (transverseGammaUpperEndMero_ne_zero beta)

theorem transverseCarrierUpperEndLogDeriv_sub_eq_envelope
    (beta a b : ℝ) :
    transverseUpperEndLogDeriv (transverseCarrierUpperEndMero beta a) -
        transverseUpperEndLogDeriv (transverseCarrierUpperEndMero beta b) =
      transverseUpperEndLogDeriv (transverseRelocationEnvelopeUpperEndMero a) -
        transverseUpperEndLogDeriv (transverseRelocationEnvelopeUpperEndMero b) := by
  rw [transverseCarrierUpperEndLogDeriv_eq_envelope_add_gamma,
    transverseCarrierUpperEndLogDeriv_eq_envelope_add_gamma]
  ring

theorem transverseRelocationEnvelopeUpperEndLogDeriv_mem_base (a : ℝ) :
    transverseUpperEndLogDeriv (transverseRelocationEnvelopeUpperEndMero a) ∈
      transverseExponentialBase := by
  let hclosed : DerivationClosed transverseExponentialBase := by
    rw [transverseExponentialBase]
    exact derivationClosed_differentialAdjoin (RatFunc ℂ)
      ({expMero 2} : Set upperEndMeroField)
  apply transverseExponentialBase.div_mem
  · exact hclosed (transverseRelocationEnvelopeUpperEndMero_mem_base a)
  · exact transverseRelocationEnvelopeUpperEndMero_mem_base a

theorem transverseCarrierUpperEndLogDeriv_sourceClass_eq
    (beta a b : ℝ) :
    transverseUpperEndLogDeriv (transverseCarrierUpperEndMero beta a) -
        transverseUpperEndLogDeriv (transverseCarrierUpperEndMero beta b) ∈
      transverseExponentialBase := by
  rw [transverseCarrierUpperEndLogDeriv_sub_eq_envelope]
  exact transverseExponentialBase.sub_mem
    (transverseRelocationEnvelopeUpperEndLogDeriv_mem_base a)
    (transverseRelocationEnvelopeUpperEndLogDeriv_mem_base b)

end
end RHTower
