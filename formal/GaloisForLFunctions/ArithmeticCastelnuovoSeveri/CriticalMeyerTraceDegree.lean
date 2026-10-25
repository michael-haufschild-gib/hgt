import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PositiveMeyerDegreesCanForgetClasses
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FaithfulPositiveMeyerDegrees
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FlowInvariantMeyerMajorantsForceCriticality

/-!
# The positive critical trace on genuine Meyer cohomology

Actual trace admission permits the sum over every critical Xi multiplicity copy.
This linear degree descends through genuine boundaries and reads a nonnegative
sum of critical Mellin squares. Its kernel forgets all off-line values and higher
jets. Comparison with the original trace and faithfulness have distinct criteria.
-/

noncomputable section
open Complex RHTower ContinuousLinearMap Set
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Critical multiplicity copies of the actual Xi divisor. -/
abbrev MeyerCriticalXiCopy := {q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2}

private theorem critical_values_summable (g : DeningerMeyerStrongLogTarget) :
    Summable (fun q : MeyerCriticalXiCopy => deningerMeyerStrongLogMellin g (q.1.1 : ℂ)) :=
  (deningerMeyerHilbertConvolution_summable_diagonal g).subtype _

/-- The absolutely convergent critical part of the actual source trace. -/
def meyerCriticalSourceTraceDegree : DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ where
  toFun g := ∑' q : MeyerCriticalXiCopy, deningerMeyerStrongLogMellin g (q.1.1 : ℂ)
  map_add' g h := by
    change (∑' q : MeyerCriticalXiCopy,
      deningerMeyerStrongLogMellinLM (q.1.1 : ℂ) (g + h)) = _
    simp only [map_add]
    exact (critical_values_summable g).tsum_add (critical_values_summable h)
  map_smul' c g := by
    change (∑' q : MeyerCriticalXiCopy,
      deningerMeyerStrongLogMellinLM (q.1.1 : ℂ) (c • g)) =
        c * ∑' q : MeyerCriticalXiCopy, deningerMeyerStrongLogMellin g (q.1.1 : ℂ)
    simp only [map_smul, smul_eq_mul, tsum_mul_left]
    rfl

theorem meyerCriticalSourceTraceDegree_boundary (f : DeningerMeyerCap) :
    meyerCriticalSourceTraceDegree (deningerMeyerStrongLogSumLM f) = 0 := by
  have hz := (meyerSource_boundary_iff_jets_zero (deningerMeyerStrongLogSumLM f)).mp ⟨f, rfl⟩
  change (∑' q : MeyerCriticalXiCopy,
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogSumLM f) (q.1.1 : ℂ)) = 0
  calc
    _ = ∑' _ : MeyerCriticalXiCopy, (0 : ℂ) :=
      tsum_congr fun q => hz q.1.1 ⟨0, xiSupportMultiplicity_pos q.1.1⟩
    _ = 0 := tsum_zero

/-- A positive linear degree on the genuine quotient, using every critical value. -/
def meyerCriticalTraceDegree : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  (LinearMap.range deningerMeyerStrongLogSumLM).liftQ meyerCriticalSourceTraceDegree (by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    exact meyerCriticalSourceTraceDegree_boundary f)

@[simp] theorem meyerCriticalTraceDegree_mk (g : DeningerMeyerStrongLogTarget) :
    meyerCriticalTraceDegree (Submodule.Quotient.mk g) = meyerCriticalSourceTraceDegree g := rfl

/-- Square energy read by the critical trace degree. -/
def meyerCriticalSquareEnergy (g : DeningerMeyerStrongLogTarget) : ℝ :=
  (meyerCriticalSourceTraceDegree
    (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))).re

private theorem critical_square_value (g : DeningerMeyerStrongLogTarget)
    (q : MeyerCriticalXiCopy) :
    deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))
      (q.1.1 : ℂ) = (Complex.normSq (deningerMeyerStrongLogMellin g (q.1.1 : ℂ)) : ℂ) :=
  meyerPointDegree_sharp_square q.1.1 q.2 g

/-- Square-energy summability is inherited from the actual sharp-product trace. -/
theorem meyerCriticalSquares_summable (g : DeningerMeyerStrongLogTarget) :
    Summable (fun q : MeyerCriticalXiCopy =>
      Complex.normSq (deningerMeyerStrongLogMellin g (q.1.1 : ℂ))) := by
  have h := Complex.reCLM.summable
    (critical_values_summable (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))
  simpa only [Complex.reCLM_apply, critical_square_value, Complex.ofReal_re] using h

/-- The positive degree reads the complete multiplicity-weighted sum of critical Mellin squares. -/
theorem meyerCriticalSquareEnergy_eq_tsum (g : DeningerMeyerStrongLogTarget) :
    meyerCriticalSquareEnergy g = ∑' q : MeyerCriticalXiCopy,
      Complex.normSq (deningerMeyerStrongLogMellin g (q.1.1 : ℂ)) := by
  change (∑' q : MeyerCriticalXiCopy,
    deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g))
      (q.1.1 : ℂ)).re = _
  rw [Complex.re_tsum
    (critical_values_summable (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp g)))]
  apply tsum_congr
  intro q
  rw [critical_square_value, Complex.ofReal_re]

theorem meyerCriticalSquareEnergy_nonneg (g : DeningerMeyerStrongLogTarget) :
    0 ≤ meyerCriticalSquareEnergy g := by
  rw [meyerCriticalSquareEnergy_eq_tsum]
  exact tsum_nonneg fun _ => Complex.normSq_nonneg _

/-- Critical square energy vanishes precisely on the reduced critical-value kernel. -/
theorem meyerCriticalSquareEnergy_eq_zero_iff (g : DeningerMeyerStrongLogTarget) :
    meyerCriticalSquareEnergy g = 0 ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 →
        deningerMeyerStrongLogMellin g (rho : ℂ) = 0 := by
  rw [meyerCriticalSquareEnergy_eq_tsum]
  constructor
  · intro hz rho hr
    by_contra hne
    let q : MeyerCriticalXiCopy := ⟨⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩, hr⟩
    have hp := (meyerCriticalSquares_summable g).tsum_pos
      (fun _ => Complex.normSq_nonneg _) q (Complex.normSq_pos.mpr hne)
    exact (ne_of_gt hp) hz
  · intro hz
    calc
      _ = ∑' _ : MeyerCriticalXiCopy, (0 : ℝ) := by
        apply tsum_congr
        intro q
        rw [hz q.1.1 q.2, Complex.normSq_zero]
      _ = 0 := tsum_zero

/-- Every mixed critical trace vanishes exactly when all critical source values vanish. -/
theorem meyerCriticalTrace_radical_iff (g : DeningerMeyerStrongLogTarget) :
    (∀ h : DeningerMeyerStrongLogTarget,
      meyerCriticalSourceTraceDegree (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h)) = 0) ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re = 1 / 2 →
        deningerMeyerStrongLogMellin g (rho : ℂ) = 0 := by
  constructor
  · intro h
    apply (meyerCriticalSquareEnergy_eq_zero_iff g).mp
    exact congrArg Complex.re (h g)
  · intro hg h
    change (∑' q : MeyerCriticalXiCopy,
      deningerMeyerStrongLogMellin (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h))
        (q.1.1 : ℂ)) = 0
    calc
      _ = ∑' _ : MeyerCriticalXiCopy, (0 : ℂ) := by
        apply tsum_congr
        intro q
        rw [deningerMeyerSourceConvolution_mellin, hg q.1.1 q.2, zero_mul]
      _ = 0 := tsum_zero

/-- Hardy's theorem makes the full critical degree nontrivial on actual squares. -/
theorem exists_positive_meyerCriticalSquareEnergy :
    ∃ g : DeningerMeyerStrongLogTarget, 0 < meyerCriticalSquareEnergy g := by
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_re_eq_half
  refine ⟨meyerPointSource q.1, ?_⟩
  by_contra hnot
  have hz : meyerCriticalSquareEnergy (meyerPointSource q.1) = 0 :=
    le_antisymm (le_of_not_gt hnot) (meyerCriticalSquareEnergy_nonneg _)
  have hv := (meyerCriticalSquareEnergy_eq_zero_iff _).mp hz q.1 hq
  rw [meyerPointSource_values, if_pos rfl] at hv
  exact one_ne_zero hv

/-- On a critical Xi divisor the restricted trace is the complete original trace. -/
theorem meyerCriticalSourceTraceDegree_eq_trace_of_rh (hRH : RiemannHypothesis)
    (g : DeningerMeyerStrongLogTarget) :
    meyerCriticalSourceTraceDegree g = meyerSourceTraceDegree g := by
  change (∑' q : MeyerCriticalXiCopy, deningerMeyerStrongLogMellin g (q.1.1 : ℂ)) =
    opTrace (deningerMeyerHilbertConvolution g)
  rw [deningerMeyerHilbertConvolution_opTrace]
  calc
    _ = ∑' q : XiZeroCopy, ({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2}).indicator
        (fun q => deningerMeyerStrongLogMellin g (q.1 : ℂ)) q := tsum_subtype _ _
    _ = _ := by
      apply tsum_congr
      intro q
      exact Set.indicator_of_mem
        (show q ∈ {q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2} from
          xi_divisor_support_re_eq_half_of_rh hRH q.1)
        (fun q : XiZeroCopy => deningerMeyerStrongLogMellin g (q.1 : ℂ))

theorem meyerCriticalTraceDegree_eq_trace_of_rh (hRH : RiemannHypothesis) :
    meyerCriticalTraceDegree = meyerCohomologyTraceDegree := by
  apply LinearMap.ext
  intro u
  induction u using Submodule.Quotient.induction_on with
  | H g => exact meyerCriticalSourceTraceDegree_eq_trace_of_rh hRH g

theorem meyerCriticalSquareEnergy_eq_trace_of_rh (hRH : RiemannHypothesis)
    (g : DeningerMeyerStrongLogTarget) :
    meyerCriticalSquareEnergy g = meyerSourceTrace g g := by
  rw [meyerCriticalSquareEnergy, meyerCriticalSourceTraceDegree_eq_trace_of_rh hRH,
    meyerSourceTrace_eq_degree_product, meyerCohomologyTraceDegree_mk]

/-- The entire positive critical energy is invariant under centered source flow. -/
theorem meyerCriticalSquareEnergy_centeredFlow (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    meyerCriticalSquareEnergy (deningerMeyerStrongLogCenteredFlow c g) =
      meyerCriticalSquareEnergy g := by
  rw [meyerCriticalSquareEnergy, meyerSourceConvolution_centered_flow_sharp]
  rfl

/-- Domination of the original mixed trace by this positive degree is precisely RH. -/
theorem meyerCriticalSquareEnergy_trace_majorant_iff :
    (∀ g h : DeningerMeyerStrongLogTarget,
      meyerSourceTrace g h ^ 2 ≤ meyerCriticalSquareEnergy g * meyerCriticalSquareEnergy h) ↔
      RiemannHypothesis := by
  constructor
  · intro hb
    exact meyer_trace_majorant_invariant_forces_criticality meyerCriticalSquareEnergy
      meyerCriticalSquareEnergy_nonneg hb meyerCriticalSquareEnergy_centeredFlow
  · intro hRH g h
    rw [meyerCriticalSquareEnergy_eq_trace_of_rh hRH, meyerCriticalSquareEnergy_eq_trace_of_rh hRH]
    have hb := meyerScalingSurface.defect_sq_le_of_hodgeIndex
      (meyerScalingSurface_hodgeIndex_iff.mpr hRH) (0, 0, g) (0, 0, h)
    simpa only [meyerScalingSurface_defect] using hb

/-- Faithfulness of the positive critical degree has the additional simplicity requirement. -/
theorem meyerCriticalTraceDegree_faithful_iff :
    (∀ g : DeningerMeyerStrongLogTarget,
      g ∉ LinearMap.range deningerMeyerStrongLogSumLM → 0 < meyerCriticalSquareEnergy g) ↔
      RiemannHypothesis ∧ ∀ rho : XiDivisorSupport, xiSupportMultiplicity rho = 1 := by
  constructor
  · intro h
    exact exists_faithful_positive_meyer_degree_iff.mp ⟨meyerCriticalTraceDegree, h⟩
  · intro hs g hnot
    rw [meyerCriticalSquareEnergy_eq_trace_of_rh hs.1]
    have ht := meyerSourceTrace_positive_faithful_iff.mpr hs g
    exact lt_of_le_of_ne ht.1 (fun he => hnot (ht.2.mp he.symm))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
