import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.NumericalEquivalenceOnTheScalingSurface
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionWeilTrace
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerFaithfulConvolution
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerExactXiCapSource

/-!
# Actual Poisson principal representatives for the scaling pairing

The all-weight Meyer source admits genuine Poisson boundaries. Compensating their two Mellin
pole moments produces nonzero cycles invisible to every intersection reading. These principal
representatives use literal source boundaries, not a prescribed entire-function quotient.
Their compact smooth comparison retains the original Weil trace and both pole degrees.
-/

noncomputable section

open Complex MeasureTheory Set Zeta23 RHTower ContinuousLinearMap

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Arithmetic reflection preserves actual Poisson boundaries, with an explicit cap producer. -/
theorem meyerSourceSharp_boundary (f : DeningerMeyerCap) :
    deningerMeyerSourceSharp (deningerMeyerStrongLogSumLM f) =
      deningerMeyerStrongLogSumLM (deningerMeyerCapFourierLM (deningerMeyerCapConj f)) := by
  rw [deningerMeyerSourceSharp, deningerMeyerStrongLogConj_boundary,
    deningerMeyerStrongLogJ_boundary]

private theorem boundary_operator_zero (f : DeningerMeyerCap) :
    deningerMeyerHilbertConvolution (deningerMeyerStrongLogSumLM f) = 0 :=
  (deningerMeyerHilbertConvolution_eq_zero_iff _).mpr ⟨f, rfl⟩

private theorem sharp_boundary_operator_zero (f : DeningerMeyerCap) :
    deningerMeyerHilbertConvolution
      (deningerMeyerSourceSharp (deningerMeyerStrongLogSumLM f)) = 0 := by
  rw [meyerSourceSharp_boundary, boundary_operator_zero]

/-- Ordinary trace is a linear degree on the entire original Meyer source space. -/
def meyerSourceTraceDegree : DeningerMeyerStrongLogTarget →ₗ[ℂ] ℂ where
  toFun g := opTrace (deningerMeyerHilbertConvolution g)
  map_add' g h := by
    simp only [deningerMeyerHilbertConvolution_opTrace]
    change (∑' q : XiZeroCopy, deningerMeyerStrongLogMellinLM (q.1 : ℂ) (g + h)) =
      (∑' q : XiZeroCopy, deningerMeyerStrongLogMellinLM (q.1 : ℂ) g) +
        ∑' q : XiZeroCopy, deningerMeyerStrongLogMellinLM (q.1 : ℂ) h
    simp only [map_add]
    exact (deningerMeyerHilbertConvolution_summable_diagonal g).tsum_add
      (deningerMeyerHilbertConvolution_summable_diagonal h)
  map_smul' c g := by
    simp only [deningerMeyerHilbertConvolution_opTrace]
    change (∑' q : XiZeroCopy, deningerMeyerStrongLogMellinLM (q.1 : ℂ) (c • g)) =
      c * ∑' q : XiZeroCopy, deningerMeyerStrongLogMellinLM (q.1 : ℂ) g
    simp only [map_smul, smul_eq_mul, tsum_mul_left]

theorem meyerSourceTraceDegree_boundary (f : DeningerMeyerCap) :
    meyerSourceTraceDegree (deningerMeyerStrongLogSumLM f) = 0 := by
  change opTrace (deningerMeyerHilbertConvolution (deningerMeyerStrongLogSumLM f)) = 0
  rw [boundary_operator_zero, RHTower.opTrace_zero]

/-- The linear degree descends through genuine Poisson boundaries to actual source cohomology. -/
def meyerCohomologyTraceDegree : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  (LinearMap.range deningerMeyerStrongLogSumLM).liftQ meyerSourceTraceDegree (by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    exact meyerSourceTraceDegree_boundary f)

@[simp] theorem meyerCohomologyTraceDegree_mk (g : DeningerMeyerStrongLogTarget) :
    meyerCohomologyTraceDegree (Submodule.Quotient.mk g) = meyerSourceTraceDegree g := rfl

/-- The source trace representing the Weil pairing on compact smooth inputs. -/
def meyerSourceTrace (g h : DeningerMeyerStrongLogTarget) : ℝ :=
  (opTrace ((deningerMeyerHilbertConvolution g).comp
    (deningerMeyerHilbertConvolution (deningerMeyerSourceSharp h)))).re

/-- The Weil trace is a linear degree of the literal source product; linearity supplies no sign. -/
theorem meyerSourceTrace_eq_degree_product (g h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace g h =
      (meyerCohomologyTraceDegree (Submodule.Quotient.mk
        (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h)))).re := by
  rw [meyerCohomologyTraceDegree_mk]
  change _ = (opTrace (deningerMeyerHilbertConvolution
    (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h)))).re
  rw [deningerMeyerHilbertConvolution_mul]
  rfl

theorem meyerSourceTrace_boundary_left (f : DeningerMeyerCap)
    (g : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace (deningerMeyerStrongLogSumLM f) g = 0 := by
  simp only [meyerSourceTrace, boundary_operator_zero, zero_comp, RHTower.opTrace_zero,
    Complex.zero_re]

theorem meyerSourceTrace_boundary_right (g : DeningerMeyerStrongLogTarget)
    (f : DeningerMeyerCap) :
    meyerSourceTrace g (deningerMeyerStrongLogSumLM f) = 0 := by
  simp only [meyerSourceTrace, sharp_boundary_operator_zero, comp_zero, RHTower.opTrace_zero,
    Complex.zero_re]

/-- The first pole moment on the original all-weight source space. -/
def meyerPoleA (g : DeningerMeyerStrongLogTarget) : ℝ :=
  (deningerMeyerStrongLogMellinLM 1 g).re

/-- The second pole moment on the original all-weight source space. -/
def meyerPoleB (g : DeningerMeyerStrongLogTarget) : ℝ :=
  (deningerMeyerStrongLogMellinLM 0 g).re

/-- A larger representative carrier retaining the two original fibre coordinates. -/
abbrev MeyerScalingCycle := ℝ × ℝ × DeningerMeyerStrongLogTarget

def meyerDegreeH (x : MeyerScalingCycle) : ℝ := x.2.1 + meyerPoleB x.2.2

def meyerDegreeV (x : MeyerScalingCycle) : ℝ := x.1 + meyerPoleA x.2.2

/-- Polar degree products minus the literal source convolution trace. -/
def meyerScalingPair (x y : MeyerScalingCycle) : ℝ :=
  meyerDegreeH x * meyerDegreeV y + meyerDegreeV x * meyerDegreeH y -
    meyerSourceTrace x.2.2 y.2.2

/-- A Poisson boundary with its two polar coordinates exactly compensated. -/
def meyerPrincipalCycle (f : DeningerMeyerCap) : MeyerScalingCycle :=
  (-meyerPoleA (deningerMeyerStrongLogSumLM f),
    -meyerPoleB (deningerMeyerStrongLogSumLM f), deningerMeyerStrongLogSumLM f)

@[simp] theorem meyerPrincipalCycle_degreeH (f : DeningerMeyerCap) :
    meyerDegreeH (meyerPrincipalCycle f) = 0 := by
  simp only [meyerDegreeH, meyerPrincipalCycle, neg_add_cancel]

@[simp] theorem meyerPrincipalCycle_degreeV (f : DeningerMeyerCap) :
    meyerDegreeV (meyerPrincipalCycle f) = 0 := by
  simp only [meyerDegreeV, meyerPrincipalCycle, neg_add_cancel]

theorem meyerPrincipalCycle_pair_left (f : DeningerMeyerCap) (x : MeyerScalingCycle) :
    meyerScalingPair (meyerPrincipalCycle f) x = 0 := by
  rw [meyerScalingPair, meyerPrincipalCycle_degreeH, meyerPrincipalCycle_degreeV]
  simp only [zero_mul, add_zero, zero_sub, meyerPrincipalCycle,
    meyerSourceTrace_boundary_left, neg_zero]

theorem meyerPrincipalCycle_pair_right (x : MeyerScalingCycle) (f : DeningerMeyerCap) :
    meyerScalingPair x (meyerPrincipalCycle f) = 0 := by
  rw [meyerScalingPair, meyerPrincipalCycle_degreeH, meyerPrincipalCycle_degreeV]
  simp only [mul_zero, add_zero, zero_sub, meyerPrincipalCycle,
    meyerSourceTrace_boundary_right, neg_zero]

private theorem sourceSharp_add (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceSharp (g + h) = deningerMeyerSourceSharp g + deningerMeyerSourceSharp h := by
  simp only [deningerMeyerSourceSharp, deningerMeyerStrongLogConj_add, map_add]

private theorem degreeH_add_principal (x : MeyerScalingCycle) (f : DeningerMeyerCap) :
    meyerDegreeH (x + meyerPrincipalCycle f) = meyerDegreeH x := by
  simp only [meyerDegreeH, meyerPrincipalCycle, meyerPoleB,
    Prod.fst_add, Prod.snd_add, map_add, Complex.add_re]
  ring

private theorem degreeV_add_principal (x : MeyerScalingCycle) (f : DeningerMeyerCap) :
    meyerDegreeV (x + meyerPrincipalCycle f) = meyerDegreeV x := by
  simp only [meyerDegreeV, meyerPrincipalCycle, meyerPoleA,
    Prod.fst_add, Prod.snd_add, map_add, Complex.add_re]
  ring

/-- Adding a genuine Poisson principal representative preserves every left intersection reading. -/
theorem meyerScalingPair_add_principal_left (x y : MeyerScalingCycle) (f : DeningerMeyerCap) :
    meyerScalingPair (x + meyerPrincipalCycle f) y = meyerScalingPair x y := by
  simp only [meyerScalingPair]
  rw [degreeH_add_principal, degreeV_add_principal]
  simp only [meyerSourceTrace, Prod.snd_add, meyerPrincipalCycle,
    deningerMeyerHilbertConvolution_add, boundary_operator_zero, add_zero]

/-- The same principal move preserves every right intersection reading. -/
theorem meyerScalingPair_add_principal_right (x y : MeyerScalingCycle) (f : DeningerMeyerCap) :
    meyerScalingPair x (y + meyerPrincipalCycle f) = meyerScalingPair x y := by
  simp only [meyerScalingPair]
  rw [degreeH_add_principal, degreeV_add_principal]
  simp only [meyerSourceTrace, Prod.snd_add, meyerPrincipalCycle, sourceSharp_add,
    deningerMeyerHilbertConvolution_add, sharp_boundary_operator_zero, add_zero]

/-- The explicit polynomial-Gaussian cap gives a nonzero principal representative. -/
theorem meyerPrincipalCycle_xi_ne_zero : meyerPrincipalCycle deningerMeyerXiCapSource ≠ 0 := by
  intro h
  have hg : deningerMeyerStrongLogSumLM deningerMeyerXiCapSource = 0 :=
    congrArg (fun x : MeyerScalingCycle => x.2.2) h
  have hM := deningerMeyerXiCapSource_mellin 1
  change deningerMeyerStrongLogMellinLM 1
    (deningerMeyerStrongLogSumLM deningerMeyerXiCapSource) = xi 1 at hM
  rw [hg, map_zero, xi_one] at hM
  norm_num at hM

/-- The original Poisson source supplies nontrivial principal cycles with both degrees zero. -/
theorem exists_nonzero_meyer_principal_cycle :
    ∃ p : MeyerScalingCycle, p ≠ 0 ∧ meyerDegreeH p = 0 ∧ meyerDegreeV p = 0 ∧
      ∀ x : MeyerScalingCycle, meyerScalingPair p x = 0 ∧ meyerScalingPair x p = 0 := by
  refine ⟨meyerPrincipalCycle deningerMeyerXiCapSource, meyerPrincipalCycle_xi_ne_zero,
    meyerPrincipalCycle_degreeH _, meyerPrincipalCycle_degreeV _, ?_⟩
  intro x
  exact ⟨meyerPrincipalCycle_pair_left _ x, meyerPrincipalCycle_pair_right x _⟩

/-- A compact smooth source that is a genuine Poisson boundary must vanish. -/
theorem compact_source_eq_zero_of_meyer_boundary {r : ℝ} (k : SuzukiSmoothCompactTest r)
    (hk : deningerWeilConvolutionSource k ∈ LinearMap.range deningerMeyerStrongLogSumLM) :
    (k : ℝ → ℂ) = 0 := by
  obtain ⟨f, hf⟩ := hk
  obtain ⟨H, -, hH⟩ := deningerMeyerBoundary_entireQuotient f
  let K : compactXiTests :=
    ⟨k, k.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)),
      k.hasCompactSupport⟩
  have hK : compactXiEvaluation K = 0 := by
    apply Subtype.ext
    funext q
    change compactXiEvaluation K q = 0
    rw [compactXiEvaluation_apply]
    have h := hH (q.1 : ℂ)
    rw [hf, deningerWeilConvolutionSource_mellin,
      xi_eq_zero_of_mem_divisor_support q.1, zero_mul] at h
    change paperFT k (((q.1 : ℂ) - 1 / 2) * (-I)) = 0
    rw [mul_comm _ (-I)]
    exact h
  have hzero := (compactXiEvaluation_eq_zero_iff K).mp hK
  exact congrArg (fun g : compactXiTests => g.1) hzero

private theorem compact_real_source_mellin {r : ℝ} (k : SuzukiSmoothCompactTest r)
    (f : ℝ → ℝ) (hk : (k : ℝ → ℂ) = cx f) (s : ℝ) :
    deningerMeyerStrongLogMellin (deningerWeilConvolutionSource k) (s : ℂ) =
      ((∫ t : ℝ, f t * Real.exp ((s - 1 / 2) * t) : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  change (t : ℂ) ^ 0 * Complex.exp ((s : ℂ) * t) *
    (Complex.exp (-(t : ℂ) / 2) * k t) =
      ((f t * Real.exp ((s - 1 / 2) * t) : ℝ) : ℂ)
  rw [pow_zero, one_mul, show k t = (f t : ℂ) from congrFun hk t]
  calc
    _ = (f t : ℂ) * Complex.exp ((s : ℂ) * t - (t : ℂ) / 2) := by
      rw [sub_eq_add_neg, Complex.exp_add, neg_div]
      ring
    _ = _ := by
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      congr 2
      push_cast
      ring

/-- The enlarged source's first pole moment agrees with the original compact-source coordinate. -/
theorem meyerPoleA_compact_real {r : ℝ} (k : SuzukiSmoothCompactTest r)
    (f : ℝ → ℝ) (hk : (k : ℝ → ℂ) = cx f) :
    meyerPoleA (deningerWeilConvolutionSource k) = poleA f := by
  change (deningerMeyerStrongLogMellin (deningerWeilConvolutionSource k) (1 : ℂ)).re = _
  have h := compact_real_source_mellin k f hk 1
  rw [Complex.ofReal_one] at h
  rw [h, Complex.ofReal_re]
  unfold poleA
  congr 1
  funext t
  congr 2
  ring

/-- The second pole moment also agrees; neither polar term is discarded. -/
theorem meyerPoleB_compact_real {r : ℝ} (k : SuzukiSmoothCompactTest r)
    (f : ℝ → ℝ) (hk : (k : ℝ → ℂ) = cx f) :
    meyerPoleB (deningerWeilConvolutionSource k) = poleB f := by
  change (deningerMeyerStrongLogMellin (deningerWeilConvolutionSource k) (0 : ℂ)).re = _
  have h := compact_real_source_mellin k f hk 0
  rw [Complex.ofReal_zero] at h
  rw [h, Complex.ofReal_re]
  unfold poleB
  congr 1
  funext t
  congr 2
  ring

/-- On real compact smooth sources, the larger representative pairing is exactly the original scaling pairing. -/
theorem meyerScalingPair_compact_real {r : ℝ} (k h : SuzukiSmoothCompactTest r)
    (f g : realTests) (hk : (k : ℝ → ℂ) = cx f.1) (hh : (h : ℝ → ℂ) = cx g.1)
    (a b c d : ℝ) :
    meyerScalingPair (a, b, deningerWeilConvolutionSource k)
      (c, d, deningerWeilConvolutionSource h) =
        scalingSurface.pair (a, b, f) (c, d, g) := by
  have hW : meyerSourceTrace (deningerWeilConvolutionSource k)
      (deningerWeilConvolutionSource h) = weilPair f.1 g.1 := by
    rw [meyerSourceTrace, deningerWeilConvolutionSource_pair_trace, hk, hh,
      zeta_W_eq_weilFullFunctional_mixed (cx_contDiff f.2.1) (cx_hasCompactSupport f.2.2)
        (cx_contDiff g.2.1) (cx_hasCompactSupport g.2.2)]
    rfl
  change meyerScalingPair _ _ = scalingPairFun _ _
  simp only [meyerScalingPair, meyerDegreeH, meyerDegreeV,
    meyerPoleA_compact_real k f.1 hk, meyerPoleB_compact_real k f.1 hk,
    meyerPoleA_compact_real h g.1 hh, meyerPoleB_compact_real h g.1 hh,
    hW, scalingPairFun, localPair]
  ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerScalingPair_add_principal_left
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerScalingPair_add_principal_right
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_nonzero_meyer_principal_cycle
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.compact_source_eq_zero_of_meyer_boundary
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerScalingPair_compact_real
