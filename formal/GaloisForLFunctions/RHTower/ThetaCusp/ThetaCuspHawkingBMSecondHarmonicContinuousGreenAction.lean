import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicHorizonBasisGreenKrein

/-!
# Continuous source action of the exact BM boundary Green kernel

The actual regular-horizon/normalizable-AdS kernel defines a continuous-source integral action.
Its two derivatives solve the forced reduced BM equation, with the exact source coefficient one.
Supported sources select the prescribed exterior branches, independently of surrounding cutoffs.
The action loses no continuous interior source and applies to every actual Xi fibre.

This is radial inversion. Time-retarded Einstein incidence, membership of the full nonlinear source
in its domain, the left-QNM boundary projection, and Hawking-clock extinction remain separate.
-/

open Complex Real Set Filter Topology MeasureTheory

namespace RHTower
noncomputable section

/-- Canonical source weight for the regular-horizon/normalizable-AdS Green action. The
Wronskian is evaluated at a fixed interior point, independently of source or cutoff. -/
def d4BMPlusPlusContinuousGreenWeight (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusIntegratingWeight n chi z /
    d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (1 / 2)

/-- Continuous source moment against a specified radial mode. -/
def d4BMPlusPlusContinuousGreenMoment
    (n : ℕ) (chi : ℂ) (mode f : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, mode t * d4BMPlusPlusContinuousGreenWeight n chi t * f t

private theorem interiorInterval {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at ht
    exact ⟨lt_of_lt_of_le ha.1 ht.1, lt_of_le_of_lt ht.2 hb.2⟩
  · rw [uIcc_of_ge hba] at ht
    exact ⟨lt_of_lt_of_le hb.1 ht.1, lt_of_le_of_lt ht.2 ha.2⟩

private theorem continuousOn_regular (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ContinuousOn (fun z : ℝ => d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ))
      (Ioo 0 1) := by
  intro z hz
  exact ((hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ)
    hchi (enorm_ofReal_lt_one hz.1 hz.2)).comp_ofReal).continuousAt.continuousWithinAt

private theorem continuousOn_normalizable (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) :
    ContinuousOn (d4BMPlusPlusAdSNormalizableSolution n chi) (Ioo 0 1) := by
  intro z hz
  exact (hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi
    hz.1 hz.2).continuousAt.continuousWithinAt

private theorem continuousOn_greenWeight (n : ℕ) (chi : ℂ) :
    ContinuousOn (d4BMPlusPlusContinuousGreenWeight n chi) (Ioo 0 1) := by
  intro z hz
  have hp := (hasDerivAt_d4BMPlusPlusIntegratingFactor n chi hz.1 hz.2).continuousAt
  have hz0 : (z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz.1)
  have hz1 : (1 - z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hz.2))
  have hq : ContinuousAt (fun t : ℝ => (t : ℂ) * (1 - t : ℂ)) z := by fun_prop
  exact ((hp.div hq (mul_ne_zero hz0 hz1)).div_const
    (d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (1 / 2))).continuousWithinAt

private theorem continuousOn_greenIntegrand (n : ℕ) (chi : ℂ)
    {mode f : ℝ → ℂ} (hm : ContinuousOn mode (Ioo 0 1))
    (hf : ContinuousOn f (Ioo 0 1)) :
    ContinuousOn (fun t => mode t * d4BMPlusPlusContinuousGreenWeight n chi t * f t)
      (Ioo 0 1) :=
  (hm.mul (continuousOn_greenWeight n chi)).mul hf

private theorem hasDerivAt_greenMoment_right (n : ℕ) (chi : ℂ)
    {mode f : ℝ → ℂ} (hm : ContinuousOn mode (Ioo 0 1))
    (hf : ContinuousOn f (Ioo 0 1)) {a z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (d4BMPlusPlusContinuousGreenMoment n chi mode f a)
      (mode z * d4BMPlusPlusContinuousGreenWeight n chi z * f z) z := by
  have hc := continuousOn_greenIntegrand n chi hm hf
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.mono (interiorInterval ha hz)).intervalIntegrable
    (hc.stronglyMeasurableAtFilter isOpen_Ioo z hz)
    (hc.continuousAt (isOpen_Ioo.mem_nhds hz))

private theorem hasDerivAt_greenMoment_left (n : ℕ) (chi : ℂ)
    {mode f : ℝ → ℂ} (hm : ContinuousOn mode (Ioo 0 1))
    (hf : ContinuousOn f (Ioo 0 1)) {b z : ℝ}
    (hb : b ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x => d4BMPlusPlusContinuousGreenMoment n chi mode f x b)
      (-(mode z * d4BMPlusPlusContinuousGreenWeight n chi z * f z)) z := by
  have hc := continuousOn_greenIntegrand n chi hm hf
  exact intervalIntegral.integral_hasDerivAt_left
    (hc.mono (interiorInterval hz hb)).intervalIntegrable
    (hc.stronglyMeasurableAtFilter isOpen_Ioo z hz)
    (hc.continuousAt (isOpen_Ioo.mem_nhds hz))

/-- Actual integral response with regular horizon and normalizable AdS boundary lines. -/
def d4BMPlusPlusContinuousGreenResponse
    (n : ℕ) (chi : ℂ) (f : ℝ → ℂ) (a b z : ℝ) : ℂ :=
  d4BMPlusPlusAdSNormalizableSolution n chi z *
      d4BMPlusPlusContinuousGreenMoment n chi
        (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a z +
    d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
      d4BMPlusPlusContinuousGreenMoment n chi
        (d4BMPlusPlusAdSNormalizableSolution n chi) f z b

/-- First field derivative, after cancellation of moving-endpoint source terms. -/
def d4BMPlusPlusContinuousGreenResponseDerivative
    (n : ℕ) (chi : ℂ) (f : ℝ → ℂ) (a b z : ℝ) : ℂ :=
  d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z *
      d4BMPlusPlusContinuousGreenMoment n chi
        (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a z +
    d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
      d4BMPlusPlusContinuousGreenMoment n chi
        (d4BMPlusPlusAdSNormalizableSolution n chi) f z b

/-- Second field derivative, retaining the exact Wronskian source term. -/
def d4BMPlusPlusContinuousGreenResponseSecondDerivative
    (n : ℕ) (chi : ℂ) (f : ℝ → ℂ) (a b z : ℝ) : ℂ :=
  d4BMPlusPlusAdSNormalizableSolutionSecondDerivative n chi z *
      d4BMPlusPlusContinuousGreenMoment n chi
        (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a z +
    d4BMPlusPlusRegularHypergeometricSolutionSecondDerivative n chi (z : ℂ) *
      d4BMPlusPlusContinuousGreenMoment n chi
        (d4BMPlusPlusAdSNormalizableSolution n chi) f z b +
    (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z *
        d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) -
      d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
        d4BMPlusPlusAdSNormalizableSolution n chi z) *
      d4BMPlusPlusContinuousGreenWeight n chi z * f z

/-- The first jet is the actual real derivative for every continuous interior source. -/
theorem hasDerivAt_d4BMPlusPlusContinuousGreenResponse
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (d4BMPlusPlusContinuousGreenResponse n chi f a b)
      (d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b z) z := by
  have hR := (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ)
    hchi (enorm_ofReal_lt_one hz.1 hz.2)).comp_ofReal
  have hV := hasDerivAt_d4BMPlusPlusAdSNormalizableSolution n chi hchi hz.1 hz.2
  have hA := hasDerivAt_greenMoment_right n chi (continuousOn_regular n chi hchi) hf ha hz
  have hB := hasDerivAt_greenMoment_left n chi (continuousOn_normalizable n chi hchi) hf hb hz
  exact ((hV.mul hA).add (hR.mul hB)).congr_deriv (by
    dsimp [d4BMPlusPlusContinuousGreenResponseDerivative]
    ring)

/-- The second jet is the actual derivative of the first. -/
theorem hasDerivAt_d4BMPlusPlusContinuousGreenResponseDerivative
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b)
      (d4BMPlusPlusContinuousGreenResponseSecondDerivative n chi f a b z) z := by
  have hR := (hasDerivAt_d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ)
    hchi (enorm_ofReal_lt_one hz.1 hz.2)).comp_ofReal
  have hV := hasDerivAt_d4BMPlusPlusAdSNormalizableSolutionDerivative n chi hchi hz.1 hz.2
  have hA := hasDerivAt_greenMoment_right n chi (continuousOn_regular n chi hchi) hf ha hz
  have hB := hasDerivAt_greenMoment_left n chi (continuousOn_normalizable n chi hchi) hf hb hz
  exact ((hV.mul hA).add (hR.mul hB)).congr_deriv (by
    dsimp [d4BMPlusPlusContinuousGreenResponseSecondDerivative]
    ring)

/-- Exact source normalization: the physical Wronskian contributes one copy of the source. -/
theorem d4BMPlusPlusContinuousGreenWeight_sourceNormalization
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    ((z * (1 - z) : ℝ) : ℂ) *
      (d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z *
          d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) -
        d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
          d4BMPlusPlusAdSNormalizableSolution n chi z) *
      d4BMPlusPlusContinuousGreenWeight n chi z = 1 := by
  have hmid0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hmid1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hD := d4BMPlusPlusRegularAdSNormalizableGreenDenominator_ne_zero n chi hchi hmid0 hmid1
  have hW : d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi z =
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (1 / 2) := by
    rw [d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi hz.1 hz.2,
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi hmid0 hmid1]
  change d4BMPlusPlusIntegratingFactor n chi z *
      (d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
          d4BMPlusPlusAdSNormalizableSolutionDerivative n chi z -
        d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (z : ℂ) *
          d4BMPlusPlusAdSNormalizableSolution n chi z) =
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (1 / 2) at hW
  have hz0 : (z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hz.1)
  have hz1 : (1 - z : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (sub_pos.mpr hz.2))
  rw [d4BMPlusPlusContinuousGreenWeight, d4BMPlusPlusIntegratingWeight]
  push_cast
  field_simp [hD, hz0, hz1]
  linear_combination hW

/-- The integral response solves the exact forced BM equation, with no supplied inverse map. -/
theorem d4BMPlusPlusContinuousGreenResponse_forcedJet
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (f : ℝ → ℂ) (a b : ℝ) {z : ℝ}
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusContinuousGreenResponse n chi f a b z)
      (d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b z)
      (d4BMPlusPlusContinuousGreenResponseSecondDerivative n chi f a b z) = f z := by
  have hR := d4BMPlusPlusRegularHypergeometricSolution_real_jet_eq_zero n chi hchi hz.1 hz.2
  have hV := d4BMPlusPlusAdSNormalizableSolution_jet_eq_zero n chi hchi hz.1 hz.2
  have hW := d4BMPlusPlusContinuousGreenWeight_sourceNormalization n chi hchi hz
  rw [d4BMPlusPlusHypergeometricJet] at hR hV
  rw [d4BMPlusPlusHypergeometricJet, d4BMPlusPlusContinuousGreenResponse,
    d4BMPlusPlusContinuousGreenResponseDerivative, d4BMPlusPlusContinuousGreenResponseSecondDerivative]
  linear_combination
    (d4BMPlusPlusContinuousGreenMoment n chi
      (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a z) * hV +
    (d4BMPlusPlusContinuousGreenMoment n chi
      (d4BMPlusPlusAdSNormalizableSolution n chi) f z b) * hR + (f z) * hW

/-- Forced equation expressed using actual first and second real derivatives. -/
theorem d4BMPlusPlusContinuousGreenResponse_forcedEquation
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusContinuousGreenResponse n chi f a b z)
      (deriv (d4BMPlusPlusContinuousGreenResponse n chi f a b) z)
      (deriv (deriv (d4BMPlusPlusContinuousGreenResponse n chi f a b)) z) = f z := by
  have hfirst := hasDerivAt_d4BMPlusPlusContinuousGreenResponse n chi hchi hf ha hb hz
  have hsecond := hasDerivAt_d4BMPlusPlusContinuousGreenResponseDerivative n chi hchi hf ha hb hz
  have heq : deriv (d4BMPlusPlusContinuousGreenResponse n chi f a b) =ᶠ[𝓝 z]
      d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with t ht
    exact (hasDerivAt_d4BMPlusPlusContinuousGreenResponse n chi hchi hf ha hb ht).deriv
  rw [hfirst.deriv, (hsecond.congr_of_eventuallyEq heq).deriv]
  exact d4BMPlusPlusContinuousGreenResponse_forcedJet n chi hchi f a b hz

/-- At the inner cutoff both field and derivative lie on the actual regular horizon line. -/
theorem d4BMPlusPlusContinuousGreenResponse_leftBoundaryJet
    (n : ℕ) (chi : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
    d4BMPlusPlusContinuousGreenResponse n chi f a b a =
        d4BMPlusPlusRegularHypergeometricSolution n chi (a : ℂ) *
          d4BMPlusPlusContinuousGreenMoment n chi
            (d4BMPlusPlusAdSNormalizableSolution n chi) f a b ∧
      d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b a =
        d4BMPlusPlusRegularHypergeometricSolutionDerivative n chi (a : ℂ) *
          d4BMPlusPlusContinuousGreenMoment n chi
            (d4BMPlusPlusAdSNormalizableSolution n chi) f a b := by
  simp [d4BMPlusPlusContinuousGreenResponse, d4BMPlusPlusContinuousGreenResponseDerivative,
    d4BMPlusPlusContinuousGreenMoment]

/-- At the outer cutoff both field and derivative lie on the actual normalizable AdS line. -/
theorem d4BMPlusPlusContinuousGreenResponse_rightBoundaryJet
    (n : ℕ) (chi : ℂ) (f : ℝ → ℂ) (a b : ℝ) :
    d4BMPlusPlusContinuousGreenResponse n chi f a b b =
        d4BMPlusPlusAdSNormalizableSolution n chi b *
          d4BMPlusPlusContinuousGreenMoment n chi
            (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a b ∧
      d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b b =
        d4BMPlusPlusAdSNormalizableSolutionDerivative n chi b *
          d4BMPlusPlusContinuousGreenMoment n chi
            (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a b := by
  simp [d4BMPlusPlusContinuousGreenResponse, d4BMPlusPlusContinuousGreenResponseDerivative,
    d4BMPlusPlusContinuousGreenMoment]

private theorem greenMoment_add_adjacent (n : ℕ) (chi : ℂ)
    {mode f : ℝ → ℂ} (hm : ContinuousOn mode (Ioo 0 1))
    (hf : ContinuousOn f (Ioo 0 1)) {a b c : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusContinuousGreenMoment n chi mode f a b +
        d4BMPlusPlusContinuousGreenMoment n chi mode f b c =
      d4BMPlusPlusContinuousGreenMoment n chi mode f a c := by
  have hcont := continuousOn_greenIntegrand n chi hm hf
  exact intervalIntegral.integral_add_adjacent_intervals
    (hcont.mono (interiorInterval ha hb)).intervalIntegrable
    (hcont.mono (interiorInterval hb hc)).intervalIntegrable

private theorem greenMoment_zeroOnInterval (n : ℕ) (chi : ℂ) (mode f : ℝ → ℂ)
    {a b : ℝ} (hab : a ≤ b) (hf : ∀ t ∈ Ioo a b, f t = 0) :
    d4BMPlusPlusContinuousGreenMoment n chi mode f a b = 0 := by
  rw [d4BMPlusPlusContinuousGreenMoment]
  calc
    _ = ∫ t in a..b, (0 : ℂ) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hab
      intro t ht
      dsimp only
      rw [hf t ht, mul_zero]
    _ = 0 := by simp

/-- For a source supported between the cutoffs, the entire inner exterior is one fixed
multiple of the actual regular horizon mode. -/
theorem d4BMPlusPlusContinuousGreenResponse_horizonBranch
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) (hza : z ≤ a)
    (hsupp : Function.support f ⊆ Icc a b) :
    d4BMPlusPlusContinuousGreenResponse n chi f a b z =
      d4BMPlusPlusRegularHypergeometricSolution n chi (z : ℂ) *
        d4BMPlusPlusContinuousGreenMoment n chi
          (d4BMPlusPlusAdSNormalizableSolution n chi) f a b := by
  have hf0 : ∀ t ∈ Ioo z a, f t = 0 := by
    intro t ht
    by_contra hne
    exact (not_le_of_gt ht.2) (hsupp hne).1
  have hR := greenMoment_zeroOnInterval n chi
    (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f hza hf0
  have hV := greenMoment_zeroOnInterval n chi
    (d4BMPlusPlusAdSNormalizableSolution n chi) f hza hf0
  have hsum := greenMoment_add_adjacent n chi (continuousOn_normalizable n chi hchi) hf hz ha hb
  rw [hV, zero_add] at hsum
  have hRrev : d4BMPlusPlusContinuousGreenMoment n chi
      (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a z = 0 := by
    unfold d4BMPlusPlusContinuousGreenMoment at hR ⊢
    rw [intervalIntegral.integral_symm, hR, neg_zero]
  rw [d4BMPlusPlusContinuousGreenResponse, hRrev, mul_zero, zero_add, ← hsum]

/-- For a source supported between the cutoffs, the entire outer exterior is one fixed
multiple of the actual normalizable AdS mode. -/
theorem d4BMPlusPlusContinuousGreenResponse_adsBranch
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) (hbz : b ≤ z)
    (hsupp : Function.support f ⊆ Icc a b) :
    d4BMPlusPlusContinuousGreenResponse n chi f a b z =
      d4BMPlusPlusAdSNormalizableSolution n chi z *
        d4BMPlusPlusContinuousGreenMoment n chi
          (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f a b := by
  have hf0 : ∀ t ∈ Ioo b z, f t = 0 := by
    intro t ht
    by_contra hne
    exact (not_le_of_gt ht.1) (hsupp hne).2
  have hR := greenMoment_zeroOnInterval n chi
    (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f hbz hf0
  have hV := greenMoment_zeroOnInterval n chi
    (d4BMPlusPlusAdSNormalizableSolution n chi) f hbz hf0
  have hsum := greenMoment_add_adjacent n chi (continuousOn_regular n chi hchi) hf ha hb hz
  rw [hR, add_zero] at hsum
  have hVrev : d4BMPlusPlusContinuousGreenMoment n chi
      (d4BMPlusPlusAdSNormalizableSolution n chi) f z b = 0 := by
    unfold d4BMPlusPlusContinuousGreenMoment at hV ⊢
    rw [intervalIntegral.integral_symm, hV, neg_zero]
  rw [d4BMPlusPlusContinuousGreenResponse, hVrev, mul_zero, add_zero, ← hsum]

/-- Zero source has zero integral response. -/
@[simp] theorem d4BMPlusPlusContinuousGreenResponse_zero
    (n : ℕ) (chi : ℂ) (a b z : ℝ) :
    d4BMPlusPlusContinuousGreenResponse n chi (fun _ => 0) a b z = 0 := by
  simp [d4BMPlusPlusContinuousGreenResponse, d4BMPlusPlusContinuousGreenMoment]

/-- The action loses no continuous source: zero response throughout the radial interior is
exactly zero source there. This is a right-inverse property, not a vanishing theorem. -/
theorem d4BMPlusPlusContinuousGreenResponse_eq_zero_iff
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    (∀ z ∈ Ioo (0 : ℝ) 1, d4BMPlusPlusContinuousGreenResponse n chi f a b z = 0) ↔
      ∀ z ∈ Ioo (0 : ℝ) 1, f z = 0 := by
  constructor
  · intro hzero
    have hD : ∀ z ∈ Ioo (0 : ℝ) 1,
        d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b z = 0 := by
      intro z hz
      have h := hasDerivAt_d4BMPlusPlusContinuousGreenResponse n chi hchi hf ha hb hz
      have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝 z]
          d4BMPlusPlusContinuousGreenResponse n chi f a b := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with t ht
        exact (hzero t ht).symm
      exact (h.congr_of_eventuallyEq heq).unique (hasDerivAt_const z (0 : ℂ))
    have hDD : ∀ z ∈ Ioo (0 : ℝ) 1,
        d4BMPlusPlusContinuousGreenResponseSecondDerivative n chi f a b z = 0 := by
      intro z hz
      have h := hasDerivAt_d4BMPlusPlusContinuousGreenResponseDerivative n chi hchi hf ha hb hz
      have heq : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝 z]
          d4BMPlusPlusContinuousGreenResponseDerivative n chi f a b := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with t ht
        exact (hD t ht).symm
      exact (h.congr_of_eventuallyEq heq).unique (hasDerivAt_const z (0 : ℂ))
    intro z hz
    have heq := d4BMPlusPlusContinuousGreenResponse_forcedJet n chi hchi f a b hz
    rw [hzero z hz, hD z hz, hDD z hz] at heq
    simpa [d4BMPlusPlusHypergeometricJet] using heq.symm
  · intro hfzero z hz
    have hmoment : ∀ (mode : ℝ → ℂ) (c d : ℝ), c ∈ Ioo (0 : ℝ) 1 →
        d ∈ Ioo (0 : ℝ) 1 → d4BMPlusPlusContinuousGreenMoment n chi mode f c d = 0 := by
      intro mode c d hc hd
      rw [d4BMPlusPlusContinuousGreenMoment]
      calc
        _ = ∫ t in c..d, (0 : ℂ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          dsimp only
          rw [hfzero t (interiorInterval hc hd ht), mul_zero]
        _ = 0 := by simp
    rw [d4BMPlusPlusContinuousGreenResponse, hmoment _ a z ha hz,
      hmoment _ z b hz hb, mul_zero, mul_zero, add_zero]

/-- The separated integral action is exactly integration against the corpus's two sewn
Green-kernel pieces, with the physical Sturm weight. -/
theorem d4BMPlusPlusContinuousGreenResponse_eq_kernelIntegrals
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) (f : ℝ → ℂ) {a b z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) :
    d4BMPlusPlusContinuousGreenResponse n chi f a b z =
      (∫ t in a..z, d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernel n chi t z *
        d4BMPlusPlusIntegratingWeight n chi t * f t) +
      (∫ t in z..b, d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernel n chi t z *
        d4BMPlusPlusIntegratingWeight n chi t * f t) := by
  have hden : ∀ t ∈ Ioo (0 : ℝ) 1,
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi t =
        d4BMPlusPlusRegularAdSNormalizableGreenDenominator n chi (1 / 2) := by
    intro t ht
    rw [d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi ht.1 ht.2,
      d4BMPlusPlusRegularAdSNormalizableGreenDenominator_eq_neg_half n chi hchi
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)]
  rw [d4BMPlusPlusContinuousGreenResponse, d4BMPlusPlusContinuousGreenMoment,
    d4BMPlusPlusContinuousGreenMoment]
  congr 1
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [d4BMPlusPlusRegularAdSNormalizableRightEndpointGreenKernel,
      d4BMPlusPlusContinuousGreenWeight, hden t (interiorInterval ha hz ht)]
    ring
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [d4BMPlusPlusRegularAdSNormalizableLeftEndpointGreenKernel,
      d4BMPlusPlusContinuousGreenWeight, hden t (interiorInterval hz hb ht)]
    ring

/-- Exact scalar transport through the constructed operator; scalar normalization does not
change its prescribed radial domain or Green kernel. -/
theorem d4BMPlusPlusContinuousGreenResponse_smul
    (n : ℕ) (chi c : ℂ) (f : ℝ → ℂ) (a b z : ℝ) :
    d4BMPlusPlusContinuousGreenResponse n chi (fun t => c * f t) a b z =
      c * d4BMPlusPlusContinuousGreenResponse n chi f a b z := by
  have hm : ∀ (mode : ℝ → ℂ) (x y : ℝ),
      d4BMPlusPlusContinuousGreenMoment n chi mode (fun t => c * f t) x y =
        c * d4BMPlusPlusContinuousGreenMoment n chi mode f x y := by
    intro mode x y
    rw [d4BMPlusPlusContinuousGreenMoment, d4BMPlusPlusContinuousGreenMoment,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    ring
  rw [d4BMPlusPlusContinuousGreenResponse, hm, hm, d4BMPlusPlusContinuousGreenResponse]
  ring

/-- Enlarging cutoffs around a supported source leaves the entire radial action unchanged. -/
theorem d4BMPlusPlusContinuousGreenResponse_cutoff_independent
    (n : ℕ) (chi : ℂ) (hchi : chi.re ≠ 0) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioo 0 1)) {a b c d z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hc : c ∈ Ioo (0 : ℝ) 1) (hd : d ∈ Ioo (0 : ℝ) 1)
    (hz : z ∈ Ioo (0 : ℝ) 1) (hca : c ≤ a) (hbd : b ≤ d)
    (hsupp : Function.support f ⊆ Icc a b) :
    d4BMPlusPlusContinuousGreenResponse n chi f c d z =
      d4BMPlusPlusContinuousGreenResponse n chi f a b z := by
  have hleft := greenMoment_zeroOnInterval n chi
    (fun t => d4BMPlusPlusRegularHypergeometricSolution n chi (t : ℂ)) f hca
    (by
      intro t ht
      by_contra hne
      exact (not_le_of_gt ht.2) (hsupp hne).1)
  have hright := greenMoment_zeroOnInterval n chi
    (d4BMPlusPlusAdSNormalizableSolution n chi) f hbd
    (by
      intro t ht
      by_contra hne
      exact (not_le_of_gt ht.1) (hsupp hne).2)
  have hA := greenMoment_add_adjacent n chi (continuousOn_regular n chi hchi) hf hc ha hz
  have hB := greenMoment_add_adjacent n chi (continuousOn_normalizable n chi hchi) hf hz hb hd
  rw [hleft, zero_add] at hA
  rw [hright, add_zero] at hB
  rw [d4BMPlusPlusContinuousGreenResponse, ← hA, ← hB, d4BMPlusPlusContinuousGreenResponse]

/-- Every actual Xi fibre has the constructed forced radial action; its nondegenerate
Wronskian is supplied by corpus source geometry, not an extra assumption. -/
theorem d4BMXiPlusPlusContinuousGreenResponse_forcedEquation
    (n : ℕ) (q : XiZeroCopy) {f : ℝ → ℂ} (hf : ContinuousOn f (Ioo 0 1)) {a b z : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) (hz : z ∈ Ioo (0 : ℝ) 1) :
    let chi := d4BMXiMixedHorizonAngularMomentum q
    d4BMPlusPlusHypergeometricJet n chi z
      (d4BMPlusPlusContinuousGreenResponse n chi f a b z)
      (deriv (d4BMPlusPlusContinuousGreenResponse n chi f a b) z)
      (deriv (deriv (d4BMPlusPlusContinuousGreenResponse n chi f a b)) z) = f z :=
  d4BMPlusPlusContinuousGreenResponse_forcedEquation n _
    (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q) hf ha hb hz

end
end RHTower
