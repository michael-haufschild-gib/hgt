import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PoissonPrincipalCyclesOnTheScalingSurface
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFiniteXiCausalSplitting
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarMultiplierCriterion

/-!
# Ordinary numerical trace forgets higher Xi jets

Actual finite causal source sections isolate every Xi value. They show that the ordinary
Weil trace radical consists precisely of sources whose Mellin values vanish on the divisor.
The Poisson boundary is smaller when a multiple zero exists: it requires every lower jet
to vanish. Equality of these two kernels is therefore exactly simplicity of the Xi divisor.
Positivity of ordinary sharp-square degrees has a different exact condition: RH alone.
-/

noncomputable section

open Complex RHTower ContinuousLinearMap
open scoped Classical ComplexConjugate

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private def singleJetPacket (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    DeningerMeyerFiniteXiJetPacket {rho} := fun q => if q.2.val = j.val then 1 else 0

/-- An actual all-weight source for one prescribed jet, with every other divisor block zero. -/
def meyerSingleJetSource (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    DeningerMeyerStrongLogTarget :=
  Classical.choose ((Submodule.Quotient.mk_surjective (LinearMap.range deningerMeyerStrongLogSumLM))
    (deningerMeyerFiniteXiCausalSection {rho} (singleJetPacket rho j)))

private theorem singleJetSource_class (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) :
    (Submodule.Quotient.mk (meyerSingleJetSource rho j) : DeningerMeyerStrongLogCohomology) =
      deningerMeyerFiniteXiCausalSection {rho} (singleJetPacket rho j) :=
  Classical.choose_spec ((Submodule.Quotient.mk_surjective (LinearMap.range deningerMeyerStrongLogSumLM))
    (deningerMeyerFiniteXiCausalSection {rho} (singleJetPacket rho j)))

/-- The source representative realizes the specified jet and no other jet of the divisor. -/
theorem meyerSingleJetSource_jet (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho)
    (sigma : XiDivisorSupport) (i : DeningerArithmeticJetIndex sigma) :
    deningerMeyerStrongLogMellinJetLM i.val (sigma : ℂ) (meyerSingleJetSource rho j) =
      if sigma = rho ∧ i.val = j.val then 1 else 0 := by
  rw [← deningerMeyerXiSupportJetEvaluationLM_mk, singleJetSource_class]
  by_cases h : sigma = rho
  · subst sigma
    let q : DeningerMeyerFiniteXiJetSlot {rho} := ⟨⟨rho, Finset.mem_singleton_self rho⟩, i⟩
    have he := congrFun (deningerMeyerFiniteXiCausalSection_jets {rho} (singleJetPacket rho j)) q
    simpa only [deningerMeyerFiniteXiJetPacketLM_apply, singleJetPacket, q,
      eq_self, true_and, and_true] using he
  · rw [deningerMeyerFiniteXiCausalSection_other_jet_zero {rho} sigma
      (by simpa only [Finset.mem_singleton] using h) i]
    simp only [h, false_and, ↓reduceIte]

/-- The source with value one at one divisor point and zero at every other point. -/
def meyerPointSource (rho : XiDivisorSupport) : DeningerMeyerStrongLogTarget :=
  meyerSingleJetSource rho ⟨0, xiSupportMultiplicity_pos rho⟩

theorem meyerPointSource_values (rho sigma : XiDivisorSupport) :
    deningerMeyerStrongLogMellin (meyerPointSource rho) (sigma : ℂ) =
      if sigma = rho then 1 else 0 := by
  have h := meyerSingleJetSource_jet rho ⟨0, xiSupportMultiplicity_pos rho⟩
    sigma ⟨0, xiSupportMultiplicity_pos sigma⟩
  change deningerMeyerStrongLogMellin (meyerPointSource rho) (sigma : ℂ) =
    (if sigma = rho ∧ (0 : ℕ) = 0 then 1 else 0) at h
  simpa only [and_true] using h

private theorem plain_product_trace (g h : DeningerMeyerStrongLogTarget) :
    opTrace ((deningerMeyerHilbertConvolution g).comp (deningerMeyerHilbertConvolution h)) =
      ∑' rho : XiDivisorSupport, (xiSupportMultiplicity rho : ℂ) *
        deningerMeyerStrongLogMellin g (rho : ℂ) * deningerMeyerStrongLogMellin h (rho : ℂ) := by
  rw [← deningerMeyerHilbertConvolution_mul, deningerMeyerHilbertConvolution_opTrace,
    (deningerMeyerHilbertConvolution_summable_diagonal
      (deningerMeyerSourceConvolution g h)).tsum_sigma]
  apply tsum_congr
  intro rho
  simp only [deningerMeyerSourceConvolution_mellin, tsum_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, xiSupportMultiplicity]
  ring

/-- One actual point source reads its full multiplicity-weighted Mellin value by ordinary trace. -/
theorem meyerPointSource_product_trace (g : DeningerMeyerStrongLogTarget)
    (rho : XiDivisorSupport) (c : ℂ) :
    opTrace ((deningerMeyerHilbertConvolution g).comp
      (deningerMeyerHilbertConvolution (c • meyerPointSource rho))) =
        c * ((xiSupportMultiplicity rho : ℂ) * deningerMeyerStrongLogMellin g (rho : ℂ)) := by
  rw [plain_product_trace]
  have hm (sigma : XiDivisorSupport) :
      deningerMeyerStrongLogMellin (c • meyerPointSource rho : DeningerMeyerStrongLogTarget)
        (sigma : ℂ) =
        c * (if sigma = rho then 1 else 0) := by
    change deningerMeyerStrongLogMellinLM (sigma : ℂ) (c • meyerPointSource rho) = _
    rw [map_smul]
    change c * deningerMeyerStrongLogMellin (meyerPointSource rho) (sigma : ℂ) = _
    rw [meyerPointSource_values]
  simp only [hm]
  rw [tsum_eq_single rho]
  · simp only [↓reduceIte, mul_one]
    ring
  · intro sigma hne
    simp only [hne, ↓reduceIte, mul_zero]

private theorem sourceSharp_sq (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceSharp (deningerMeyerSourceSharp g) = g := by
  simp only [deningerMeyerSourceSharp, deningerMeyerStrongLogConj_J,
    deningerMeyerStrongLogConj_sq, deningerMeyerStrongLogJ_sq]

/-- The ordinary source trace radical is exactly vanishing of every zeroth Mellin value. -/
theorem meyerSourceTrace_radical_iff_values_zero (g : DeningerMeyerStrongLogTarget) :
    (∀ h : DeningerMeyerStrongLogTarget, meyerSourceTrace g h = 0) ↔
      ∀ rho : XiDivisorSupport, deningerMeyerStrongLogMellin g (rho : ℂ) = 0 := by
  constructor
  · intro hz rho
    let z := (xiSupportMultiplicity rho : ℂ) * deningerMeyerStrongLogMellin g (rho : ℂ)
    have h := hz (deningerMeyerSourceSharp (conj z • meyerPointSource rho))
    rw [meyerSourceTrace, sourceSharp_sq, meyerPointSource_product_trace] at h
    change (conj z * z).re = 0 at h
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re] at h
    have hz0 : z = 0 := Complex.normSq_eq_zero.mp h
    have hm : (xiSupportMultiplicity rho : ℂ) ≠ 0 := by
      exact_mod_cast (xiSupportMultiplicity_pos rho).ne'
    exact (mul_eq_zero.mp hz0).resolve_left hm
  · intro hz h
    simp only [meyerSourceTrace, plain_product_trace, hz, mul_zero, zero_mul,
      tsum_zero, Complex.zero_re]

/-- A higher jet at a multiple zero is numerically invisible but not a principal source. -/
theorem exists_meyer_trace_radical_not_boundary_of_multiple
    (rho : XiDivisorSupport) (hm : 1 < xiSupportMultiplicity rho) :
    ∃ g : DeningerMeyerStrongLogTarget,
      (∀ h : DeningerMeyerStrongLogTarget, meyerSourceTrace g h = 0) ∧
        g ∉ LinearMap.range deningerMeyerStrongLogSumLM := by
  let j : DeningerArithmeticJetIndex rho := ⟨1, hm⟩
  let g := meyerSingleJetSource rho j
  refine ⟨g, (meyerSourceTrace_radical_iff_values_zero g).mpr ?_, ?_⟩
  · intro sigma
    have h := meyerSingleJetSource_jet rho j sigma ⟨0, xiSupportMultiplicity_pos sigma⟩
    change deningerMeyerStrongLogMellin g (sigma : ℂ) =
      (if sigma = rho ∧ (0 : ℕ) = 1 then 1 else 0) at h
    simpa only [zero_ne_one, and_false, ↓reduceIte] using h
  · intro hg
    have hclass : (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mpr hg
    have hzero := congrArg (deningerMeyerXiSupportJetEvaluationLM rho j) hclass
    rw [deningerMeyerXiSupportJetEvaluationLM_mk, map_zero] at hzero
    have hone := meyerSingleJetSource_jet rho j rho j
    simp only [and_self, ↓reduceIte] at hone
    rw [hone] at hzero
    exact one_ne_zero hzero

/-- Ordinary trace detects the genuine Poisson class exactly when the Xi divisor is simple. -/
theorem meyerSourceTrace_radical_eq_boundary_iff_simple :
    (∀ g : DeningerMeyerStrongLogTarget,
      (∀ h : DeningerMeyerStrongLogTarget, meyerSourceTrace g h = 0) ↔
        g ∈ LinearMap.range deningerMeyerStrongLogSumLM) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h rho
    by_contra hne
    have hm : 1 < xiSupportMultiplicity rho := by
      have hp := xiSupportMultiplicity_pos rho
      omega
    obtain ⟨g, hg, hnot⟩ := exists_meyer_trace_radical_not_boundary_of_multiple rho hm
    exact hnot ((h g).mp hg)
  · intro hs g
    constructor
    · intro hg
      have hv := (meyerSourceTrace_radical_iff_values_zero g).mp hg
      apply (Submodule.Quotient.mk_eq_zero (LinearMap.range deningerMeyerStrongLogSumLM)).mp
      apply deningerMeyerCohomology_eq_of_XiJets_eq
      intro rho j
      rw [deningerMeyerXiSupportJetEvaluationLM_mk, map_zero]
      have hj : j.val = 0 := by
        have hjlt := j.isLt
        have hm := hs rho
        omega
      change deningerMeyerStrongLogMellinJetLM j.val (rho : ℂ) g = 0
      rw [hj]
      exact hv rho
    · rintro ⟨f, rfl⟩ h
      exact meyerSourceTrace_boundary_left f h

/-- Positivity of the actual ordinary source trace requires RH, but does not require simplicity. -/
theorem meyerSourceTrace_nonneg_iff_riemannHypothesis :
    (∀ g : DeningerMeyerStrongLogTarget, 0 ≤ meyerSourceTrace g g) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_iff_polarMultiplier_nonnegative.mpr
    intro a g
    rw [← ccmRestrictedWeilForm_self_re_eq_source,
      ← deningerWeilConvolutionSource_ccm_trace g.polarMultiplier g.polarMultiplier]
    exact h (deningerWeilConvolutionSource g.polarMultiplier.toSuzukiSmoothCompactTest)
  · intro hRH g
    rw [meyerSourceTrace, ← deningerMeyerHilbertConvolution_mul,
      deningerMeyerHilbertConvolution_opTrace,
      Complex.re_tsum (deningerMeyerHilbertConvolution_summable_diagonal
        (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))]
    apply tsum_nonneg
    intro q
    have href : star (1 - (q.1 : ℂ)) = (q.1 : ℂ) := by
      apply Complex.ext
      · change 1 - (q.1 : ℂ).re = (q.1 : ℂ).re
        rw [xi_divisor_support_re_eq_half_of_rh hRH q.1]
        norm_num
      · change -(0 - (q.1 : ℂ).im) = (q.1 : ℂ).im
        ring
    rw [deningerMeyerSourceConvolution_mellin, deningerMeyerSourceSharp_mellin, href]
    change 0 ≤ (deningerMeyerStrongLogMellin g (q.1 : ℂ) *
      conj (deningerMeyerStrongLogMellin g (q.1 : ℂ))).re
    rw [Complex.mul_conj, Complex.ofReal_re]
    exact Complex.normSq_nonneg _

/-- Linearity of the descended degree leaves precisely this arithmetic order obligation. -/
theorem meyerCohomologyTraceDegree_sharp_squares_nonneg_iff :
    (∀ g : DeningerMeyerStrongLogTarget,
      0 ≤ (meyerCohomologyTraceDegree (Submodule.Quotient.mk
        (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))).re) ↔
      RiemannHypothesis := by
  simp only [← meyerSourceTrace_eq_degree_product]
  exact meyerSourceTrace_nonneg_iff_riemannHypothesis

/-- Failure of RH is witnessed by a negative degree of a literal source sharp square. -/
theorem not_riemannHypothesis_iff_exists_negative_meyerSourceTrace :
    ¬ RiemannHypothesis ↔
      ∃ g : DeningerMeyerStrongLogTarget, meyerSourceTrace g g < 0 := by
  rw [← meyerSourceTrace_nonneg_iff_riemannHypothesis]
  simp only [not_forall, not_le]

/-- Actual Poisson boundaries are exactly the sources with every divisor jet zero. -/
theorem meyerSource_boundary_iff_jets_zero (g : DeningerMeyerStrongLogTarget) :
    g ∈ LinearMap.range deningerMeyerStrongLogSumLM ↔
      ∀ (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho),
        deningerMeyerStrongLogMellinJetLM j.val (rho : ℂ) g = 0 := by
  rw [← Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h rho j
    have he := congrArg (deningerMeyerXiSupportJetEvaluationLM rho j) h
    simpa only [deningerMeyerXiSupportJetEvaluationLM_mk, map_zero] using he
  · intro h
    apply deningerMeyerCohomology_eq_of_XiJets_eq
    intro rho j
    simpa only [deningerMeyerXiSupportJetEvaluationLM_mk, map_zero] using h rho j

/-- Every multiple Xi point supplies a nonprincipal source whose convolution square is principal. -/
theorem exists_meyer_square_zero_nonprincipal_of_multiple
    (rho : XiDivisorSupport) (hm : 1 < xiSupportMultiplicity rho) :
    ∃ g : DeningerMeyerStrongLogTarget,
      g ∉ LinearMap.range deningerMeyerStrongLogSumLM ∧
        deningerMeyerSourceConvolution g g ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  let j : DeningerArithmeticJetIndex rho := ⟨xiSupportMultiplicity rho - 1, by omega⟩
  let g := meyerSingleJetSource rho j
  have hvanish (sigma : XiDivisorSupport) (k : ℕ) (hk : k < xiSupportMultiplicity sigma)
      (hne : ¬ (sigma = rho ∧ k = xiSupportMultiplicity rho - 1)) :
      deningerMeyerStrongLogMellinJetLM k (sigma : ℂ) g = 0 := by
    have h := meyerSingleJetSource_jet rho j sigma ⟨k, hk⟩
    simpa only [j, if_neg hne] using h
  refine ⟨g, ?_, (meyerSource_boundary_iff_jets_zero _).mpr ?_⟩
  · intro hg
    have hz := (meyerSource_boundary_iff_jets_zero g).mp hg rho j
    have ho := meyerSingleJetSource_jet rho j rho j
    simp only [and_self, ↓reduceIte] at ho
    rw [ho] at hz
    exact one_ne_zero hz
  · intro sigma i
    have hz : deningerMeyerHasseMoment (deningerMeyerSourceConvolution g g) i.val
        (sigma : ℂ) = 0 := by
      rw [deningerMeyerHasseMoment_convolution]
      apply Finset.sum_eq_zero
      intro k hk
      have hk' : k ≤ i.val := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hklt : k < xiSupportMultiplicity sigma := lt_of_le_of_lt hk' i.isLt
      have hsub : i.val - k < xiSupportMultiplicity sigma :=
        lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
      by_cases hfirst : sigma = rho ∧ k = xiSupportMultiplicity rho - 1
      · have hsecond : ¬ (sigma = rho ∧ i.val - k = xiSupportMultiplicity rho - 1) := by
          obtain ⟨rfl, hkval⟩ := hfirst
          have hi := i.isLt
          omega
        have hzero := hvanish sigma (i.val - k) hsub hsecond
        simp only [deningerMeyerHasseMoment, hzero, zero_div, mul_zero]
      · have hzero := hvanish sigma k hklt hfirst
        simp only [deningerMeyerHasseMoment, hzero, zero_div, zero_mul]
    have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    change deningerMeyerStrongLogMellinJetLM i.val (sigma : ℂ)
      (deningerMeyerSourceConvolution g g) / (i.val.factorial : ℂ) = 0 at hz
    have he := congrArg (fun z : ℂ => z * (i.val.factorial : ℂ)) hz
    rw [div_mul_cancel₀ _ hf, zero_mul] at he
    exact he

/-- The genuine source quotient has no nonzero square-zero class exactly when Xi is simple. -/
theorem meyerSource_square_root_boundary_iff_simple :
    (∀ g : DeningerMeyerStrongLogTarget,
      deningerMeyerSourceConvolution g g ∈ LinearMap.range deningerMeyerStrongLogSumLM →
        g ∈ LinearMap.range deningerMeyerStrongLogSumLM) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h rho
    by_contra hne
    have hm : 1 < xiSupportMultiplicity rho := by
      have hp := xiSupportMultiplicity_pos rho
      omega
    obtain ⟨g, hnot, hsquare⟩ := exists_meyer_square_zero_nonprincipal_of_multiple rho hm
    exact hnot (h g hsquare)
  · intro hs g hg
    apply (meyerSourceTrace_radical_eq_boundary_iff_simple.mpr hs g).mp
    apply (meyerSourceTrace_radical_iff_values_zero g).mpr
    intro rho
    have hz := (meyerSource_boundary_iff_jets_zero _).mp hg rho
      ⟨0, xiSupportMultiplicity_pos rho⟩
    change deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g g) (rho : ℂ) = 0 at hz
    rw [deningerMeyerSourceConvolution_mellin] at hz
    rcases mul_eq_zero.mp hz with h | h <;> exact h

/-- A source with both pole degrees compensated, whether or not it is principal. -/
def meyerBalancedCycle (g : DeningerMeyerStrongLogTarget) : MeyerScalingCycle :=
  (-meyerPoleA g, -meyerPoleB g, g)

theorem meyerBalancedCycle_principal_iff (g : DeningerMeyerStrongLogTarget) :
    (∃ f : DeningerMeyerCap, meyerBalancedCycle g = meyerPrincipalCycle f) ↔
      g ∈ LinearMap.range deningerMeyerStrongLogSumLM := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (congrArg (fun x : MeyerScalingCycle => x.2.2) hf).symm⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f, rfl⟩

theorem meyerBalancedCycle_radical_iff (g : DeningerMeyerStrongLogTarget) :
    (∀ x : MeyerScalingCycle, meyerScalingPair (meyerBalancedCycle g) x = 0) ↔
      ∀ h : DeningerMeyerStrongLogTarget, meyerSourceTrace g h = 0 := by
  have he (x : MeyerScalingCycle) : meyerScalingPair (meyerBalancedCycle g) x =
      -meyerSourceTrace g x.2.2 := by
    simp only [meyerScalingPair, meyerBalancedCycle, meyerDegreeH, meyerDegreeV,
      neg_add_cancel, zero_mul, zero_add, zero_sub]
  simp only [he, neg_eq_zero]
  constructor
  · intro h g'
    exact h (0, 0, g')
  · intro h x
    exact h x.2.2

/-- Every ordinary numerical reading is determined by the two pole degrees and the Xi values. -/
theorem meyerScalingPair_radical_iff (x : MeyerScalingCycle) :
    (∀ y : MeyerScalingCycle, meyerScalingPair x y = 0) ↔
      meyerDegreeH x = 0 ∧ meyerDegreeV x = 0 ∧
        ∀ rho : XiDivisorSupport, deningerMeyerStrongLogMellin x.2.2 (rho : ℂ) = 0 := by
  have hzero : meyerSourceTrace x.2.2 0 = 0 := by
    simpa only [map_zero] using meyerSourceTrace_boundary_right x.2.2 0
  have hH : meyerScalingPair x (1, 0, 0) = meyerDegreeH x := by
    simp only [meyerScalingPair, meyerDegreeH, meyerDegreeV, meyerPoleA, meyerPoleB,
      map_zero, Complex.zero_re, add_zero, mul_one, mul_zero, sub_zero, hzero]
  have hV : meyerScalingPair x (0, 1, 0) = meyerDegreeV x := by
    simp only [meyerScalingPair, meyerDegreeH, meyerDegreeV, meyerPoleA, meyerPoleB,
      map_zero, Complex.zero_re, zero_add, add_zero, mul_one, mul_zero, sub_zero, hzero]
  constructor
  · intro hx
    have hxH : meyerDegreeH x = 0 := hH.symm.trans (hx (1, 0, 0))
    have hxV : meyerDegreeV x = 0 := hV.symm.trans (hx (0, 1, 0))
    refine ⟨hxH, hxV, (meyerSourceTrace_radical_iff_values_zero x.2.2).mp ?_⟩
    intro g
    have hg := hx (0, 0, g)
    simp only [meyerScalingPair, hxH, hxV, zero_mul, zero_add, zero_sub, neg_eq_zero] at hg
    exact hg
  · rintro ⟨hxH, hxV, hvalues⟩ y
    have htrace := (meyerSourceTrace_radical_iff_values_zero x.2.2).mpr hvalues y.2.2
    simp only [meyerScalingPair, hxH, hxV, zero_mul, zero_add, zero_sub, htrace, neg_zero]

/-- Principal representatives exhaust the ordinary numerical radical precisely when all Xi zeros are simple. -/
theorem meyerScalingPair_radical_eq_principal_iff_simple :
    (∀ x : MeyerScalingCycle,
      (∀ y : MeyerScalingCycle, meyerScalingPair x y = 0) ↔
        ∃ f : DeningerMeyerCap, x = meyerPrincipalCycle f) ↔
      ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    apply meyerSourceTrace_radical_eq_boundary_iff_simple.mp
    intro g
    rw [← meyerBalancedCycle_radical_iff, ← meyerBalancedCycle_principal_iff]
    exact h (meyerBalancedCycle g)
  · intro hs x
    constructor
    · intro hx
      obtain ⟨hH, hV, hvalues⟩ := (meyerScalingPair_radical_iff x).mp hx
      have hg := (meyerSourceTrace_radical_iff_values_zero x.2.2).mpr hvalues
      obtain ⟨f, hf⟩ := (meyerSourceTrace_radical_eq_boundary_iff_simple.mpr hs x.2.2).mp hg
      have hbal : x = meyerBalancedCycle x.2.2 := by
        apply Prod.ext
        · change x.1 = -meyerPoleA x.2.2
          unfold meyerDegreeV at hV
          linarith only [hV]
        · apply Prod.ext
          · change x.2.1 = -meyerPoleB x.2.2
            unfold meyerDegreeH at hH
            linarith only [hH]
          · rfl
      refine ⟨f, hbal.trans ?_⟩
      rw [← hf]
      rfl
    · rintro ⟨f, rfl⟩ y
      exact meyerPrincipalCycle_pair_left f y

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
