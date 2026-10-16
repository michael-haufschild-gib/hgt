import GaloisForLFunctions.RHTower.MobiusDivisorCompactClockSource
import GaloisForLFunctions.RHTower.MobiusDivisorCompactClockTailSeparation
import GaloisForLFunctions.RHTower.FiniteDirichletMellinContinuationObstruction

/-!
# Cofinal separation of complete source clock profiles

Every nonzero continuous functional on a compact clock interval has an
uncancelled critical pole in its literal source transform. Finite
exponential type and the superlinear simple-critical-zero census prevent
annihilation of that divisor. Landau tail separation therefore produces a
strictly negative actual source pairing beyond every depth threshold.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex
open scoped NNReal
open GaloisForLFunctions.HTGeometry
namespace RHTower

private def unitDirichletCoefficient : ℕ →₀ ℂ := Finsupp.single 1 1

private lemma unitDirichletCoefficient_zero : unitDirichletCoefficient 0 = 0 := by
  simp [unitDirichletCoefficient]

private lemma unitDirichletPolynomial (s : ℂ) :
    finiteDirichletPolynomial unitDirichletCoefficient s = 1 := by
  simp [finiteDirichletPolynomial, unitDirichletCoefficient]

private def criticalClockUnitMellin : ℂ → ℂ :=
  finiteDirichletDivisorMellin unitDirichletCoefficient ∅ (2 * Real.eulerMascheroniConstant)

private lemma criticalAbelProfileLaplace_eq_unitMellin {s : ℂ} (hs : 0 < s.re) :
    criticalAbelProfileLaplace s = criticalClockUnitMellin (s + 3 / 2) := by
  rw [criticalAbelProfileLaplace_eq_continuation hs,
    criticalAbelLaplaceContinuation_eq_step hs,
    criticalStepSourceMellin_eq_centeredCurrentGap (by simp; linarith),
    ← criticalSourceMellinNumerator_eq_centeredCurrentGap (by simp; linarith)]
  unfold criticalClockUnitMellin finiteDirichletDivisorMellin finiteDirichletDivisorSource
  rw [unitDirichletPolynomial]
  simp only [finitePrimeEulerDenominator, Finset.prod_empty, one_mul]
  rw [show s + 3 / 2 - 1 / 2 + 1 / 2 = s + 3 / 2 by ring,
    simplePrimeDivisorContinuedSource_eq_zetaLogDeriv (by simp; linarith),
    show s + 3 / 2 - 1 / 2 = 1 + s by ring, div_div]
  congr 1
  ring

def criticalClockDualContinuation (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (s : ℂ) : ℂ :=
  criticalClockFourierBorel a L (s - 1) * criticalClockUnitMellin (s + 1 / 2)

lemma meromorphicAt_criticalClockDualContinuation (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (s : ℂ) :
    MeromorphicAt (criticalClockDualContinuation a L) s := by
  have hf := ((differentiable_criticalClockFourierBorel a L).analyticAt (s - 1)).comp (f := fun z : ℂ => z - 1) (x := s)
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) s)
  have hg := (meromorphicAt_finiteDirichletDivisorMellin unitDirichletCoefficient
    unitDirichletCoefficient_zero ∅ (2 * Real.eulerMascheroniConstant) (s + 1 / 2)).comp_analyticAt (g := fun z : ℂ => z + 1 / 2) (x := s)
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s)
  exact hf.meromorphicAt.mul hg

lemma analyticAt_criticalClockDualContinuation_real (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) {x : ℝ} (hx : 1 / 4 < x) :
    AnalyticAt ℂ (criticalClockDualContinuation a L) (x : ℂ) := by
  have hf := ((differentiable_criticalClockFourierBorel a L).analyticAt ((x : ℂ) - 1)).comp (f := fun z : ℂ => z - 1) (x := (x : ℂ))
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - 1) (x : ℂ))
  have hg := (analyticAt_finiteDirichletDivisorMellin_of_small_im unitDirichletCoefficient
    unitDirichletCoefficient_zero ∅ (2 * Real.eulerMascheroniConstant)
    (s := (x : ℂ) + 1 / 2) (by simp; linarith) (by norm_num)).comp
      (f := fun z : ℂ => z + 1 / 2) (x := (x : ℂ))
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) (x : ℂ))
  exact hf.mul hg

lemma exists_criticalClockDualContinuation_pole (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) :
    ∃ p : ℂ, 1 / 4 < p.re ∧ meromorphicOrderAt (criticalClockDualContinuation a L) p < 0 := by
  have hF : Differentiable ℂ (fun z : ℂ =>
      criticalClockFourierBorel a L (-1 / 2 + z * I)) :=
    (differentiable_criticalClockFourierBorel a L).comp
      ((differentiable_const (-1 / 2)).add (differentiable_id.mul_const I))
  obtain ⟨C, hC, hg⟩ := criticalClockFourierBorel_criticalLine_exponentialType a L
  obtain ⟨t, _, ht, hz, _, hne⟩ := exists_simpleCritical_nonzero_of_exponentialType hF
    (criticalClockFourierBorel_criticalLine_nonzero a L hL) a.property hC hg ∅
  have hval : criticalClockFourierBorel a L (linePt t - 1) ≠ 0 := by
    convert hne using 1
    congr 1
    simp only [linePt, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hreg : regularizedRiemannZeta (linePt t) = 0 := by
    have hp1 : linePt t ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      rw [linePt_re] at hr
      norm_num at hr
    have hzeta := (xi_eq_zero_iff (by rw [linePt_re]; norm_num) hp1).mp hz
    rw [regularizedRiemannZeta_of_ne_one hp1, hzeta, mul_zero]
  have hbase : meromorphicOrderAt criticalClockUnitMellin (linePt t + 1 / 2) =
      ((-1 : ℤ) : WithTop ℤ) := by
    apply meromorphicOrderAt_finiteDirichletDivisorMellin_eq_neg_one
      unitDirichletCoefficient unitDirichletCoefficient_zero ∅ (2 * Real.eulerMascheroniConstant)
    · simp [linePt_re]
    · simpa using hreg
    · rw [unitDirichletPolynomial]
      norm_num
  have hshift : meromorphicOrderAt (fun s : ℂ => criticalClockUnitMellin (s + 1 / 2))
      (linePt t) = ((-1 : ℤ) : WithTop ℤ) := by
    rw [show (fun s : ℂ => criticalClockUnitMellin (s + 1 / 2)) =
      criticalClockUnitMellin ∘ (fun s : ℂ => s + 1 / 2) from rfl,
      meromorphicOrderAt_comp_of_deriv_ne_zero
        (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s + 1 / 2) (linePt t))
        (by simp), hbase]
  have hf := ((differentiable_criticalClockFourierBorel a L).analyticAt (linePt t - 1)).comp (f := fun z : ℂ => z - 1) (x := linePt t)
    (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s - 1) (linePt t))
  change AnalyticAt ℂ (fun s : ℂ => criticalClockFourierBorel a L (s - 1)) (linePt t) at hf
  have hfo : meromorphicOrderAt (fun s : ℂ => criticalClockFourierBorel a L (s - 1))
      (linePt t) = 0 := by
    rw [hf.meromorphicOrderAt_eq, hf.analyticOrderAt_eq_zero.mpr hval]
    simp
  have hm := (meromorphicAt_finiteDirichletDivisorMellin unitDirichletCoefficient
    unitDirichletCoefficient_zero ∅ (2 * Real.eulerMascheroniConstant) (linePt t + 1 / 2)).comp_analyticAt (g := fun z : ℂ => z + 1 / 2) (x := linePt t)
      (by fun_prop : AnalyticAt ℂ (fun s : ℂ => s + 1 / 2) (linePt t))
  change MeromorphicAt (fun s : ℂ => criticalClockUnitMellin (s + 1 / 2)) (linePt t) at hm
  refine ⟨linePt t, by rw [linePt_re]; norm_num, ?_⟩
  change meromorphicOrderAt ((fun s : ℂ => criticalClockFourierBorel a L (s - 1)) *
    (fun s : ℂ => criticalClockUnitMellin (s + 1 / 2))) (linePt t) < 0
  rw [meromorphicOrderAt_mul hf.meromorphicAt hm, hfo, hshift, zero_add]
  exact_mod_cast (show (-1 : ℤ) < 0 by omega)

private lemma criticalClockWeightedKernel (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (σ t : ℝ) :
    ((Real.exp t * L (criticalClockProfile a t) * Real.exp (-σ * t) : ℝ) : ℂ) =
      criticalClockDualComplex a L
        (expRay ((σ : ℂ) - 1) t • criticalClockProfileC a t) := by
  rw [map_smul]
  change _ = expRay ((σ : ℂ) - 1) t * criticalClockDualComplex a L
    (Complex.ofRealCLM.compLeftContinuous ℝ _ (criticalClockProfile a t))
  rw [criticalClockDualComplex_ofReal]
  simp only [Complex.ofReal_mul, Complex.ofReal_exp]
  rw [mul_right_comm, ← Complex.exp_add]
  unfold expRay
  congr 2
  push_cast
  ring

private lemma integrable_criticalClockWeightedDual (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) {σ : ℝ} (hσ : 3 / 2 < σ) :
    IntegrableOn (fun t : ℝ => Real.exp t * L (criticalClockProfile a t) *
      Real.exp (-σ * t)) (Ioi 0) := by
  have hi := (criticalClockDualComplex a L).integrable_comp
    (integrable_criticalClockProfileC_ray a (s := (σ : ℂ) - 1) (by simp; linarith))
  apply hi.re.congr
  filter_upwards with t
  rw [← criticalClockWeightedKernel]
  rfl

private lemma laplace_criticalClockWeightedDual (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) {σ : ℝ} (hσ : 3 / 2 < σ) :
    ((∫ t in Ioi (0 : ℝ), Real.exp t * L (criticalClockProfile a t) *
      Real.exp (-σ * t) : ℝ) : ℂ) = criticalClockDualContinuation a L (σ : ℂ) := by
  have hs : 0 < ((σ : ℂ) - 1).re := by simp; linarith
  rw [← integral_complex_ofReal]
  simp_rw [criticalClockWeightedKernel]
  rw [(criticalClockDualComplex a L).integral_comp_comm
    (integrable_criticalClockProfileC_ray a hs), integral_criticalClockProfileC a hs, map_smul]
  rw [criticalAbelProfileLaplace_eq_unitMellin hs]
  change criticalClockUnitMellin ((σ : ℂ) - 1 + 3 / 2) *
    criticalClockFourierBorel a L ((σ : ℂ) - 1) = _
  rw [show (σ : ℂ) - 1 + 3 / 2 = (σ : ℂ) + 1 / 2 by ring]
  exact mul_comm _ _

/-- Every nonzero continuous functional has strictly negative literal clock-source values
beyond every prescribed source depth. -/
theorem exists_negative_criticalClockProfile_pairing (a : ℝ≥0)
    (L : C(CriticalClockWindow a, ℝ) →L[ℝ] ℝ) (hL : L ≠ 0) (T : ℝ) :
    ∃ t : ℝ, T < t ∧ L (criticalClockProfile a t) < 0 := by
  by_contra hn
  push Not at hn
  let g : ℝ → ℝ := fun t => Real.exp t * L (criticalClockProfile a t)
  have hgc : Continuous g :=
    Real.continuous_exp.mul (L.continuous.comp (continuous_criticalClockProfile a))
  obtain ⟨p, hp, hpo⟩ := exists_criticalClockDualContinuation_pole a L hL
  apply no_oneSign_tail_of_meromorphic_pole hgc
    (fun σ hσ => integrable_criticalClockWeightedDual a L hσ)
    (fun σ hσ => laplace_criticalClockWeightedDual a L hσ)
    (fun σ hσ => analyticAt_criticalClockDualContinuation_real a L hσ)
    (fun z _ => meromorphicAt_criticalClockDualContinuation a L z) hp hpo
  refine ⟨max 0 T, le_max_left _ _, fun t ht => ?_⟩
  exact mul_nonneg (Real.exp_pos t).le (hn t ((le_max_right _ _).trans_lt ht))

end RHTower
