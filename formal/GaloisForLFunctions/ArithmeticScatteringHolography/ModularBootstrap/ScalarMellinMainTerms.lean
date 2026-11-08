import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic

/-!
# Logarithmic main terms in scalar Mellin transforms

Differentiating the Mellin transform of the unit interval gives the double
pole of its logarithmic weight. Shifting the Mellin parameter handles the
scalar main term `(a log y + b)/y`.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics

noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The unit interval cutoff, excluding zero. -/
def scalarMellinUnitCutoff : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator fun _ => 1

/-- Logarithmic weighting differentiates the simple Mellin pole. -/
theorem hasMellin_logarithmicCutoff {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun y : ℝ => Real.log y • scalarMellinUnitCutoff y) s (-(1 / s ^ 2)) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hi : LocallyIntegrableOn scalarMellinUnitCutoff (Ioi 0) := by
    have h := (hasMellin_one_Ioc (s := 1) (by norm_num)).1
    have h' : IntegrableOn scalarMellinUnitCutoff (Ioi 0) := by
      simpa only [MellinConvergent, sub_self, cpow_zero, one_smul, scalarMellinUnitCutoff] using h
    exact h'.locallyIntegrableOn
  have htop : scalarMellinUnitCutoff =O[atTop] (fun y : ℝ => y ^ (-(s.re + 1))) := by
    refine IsBigO.of_bound 0 ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    simp [scalarMellinUnitCutoff, not_le.mpr hy]
  have hbot : scalarMellinUnitCutoff =O[𝓝[>] (0 : ℝ)] (fun y : ℝ => y ^ (-(0 : ℝ))) := by
    refine IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ Ioc (0 : ℝ) 1 <;> simp [scalarMellinUnitCutoff, hy]
  have hd := mellin_hasDerivAt_of_isBigO_rpow hi htop (by linarith) hbot hs
  have heq : mellin scalarMellinUnitCutoff =ᶠ[𝓝 s] fun z : ℂ => 1 / z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact (hasMellin_one_Ioc hz).2
  have hd' := hd.2.congr_of_eventuallyEq heq.symm
  have hi' : HasDerivAt (fun z : ℂ => 1 / z) (-(1 / s ^ 2)) s := by
    simpa only [one_div] using (hasDerivAt_inv hs0)
  exact ⟨hd.1, hd'.unique hi'⟩

/-- The logarithmic and constant scalar main terms, cut off at height one. -/
def scalarMellinMainTerm (a b : ℂ) : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator fun y => (a * (Real.log y : ℂ) + b) / (y : ℂ)

/-- The cutoff main terms contribute only a double and a simple pole at one. -/
theorem hasMellin_scalarMellinMainTerm (a b : ℂ) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (scalarMellinMainTerm a b) s (-a / (s - 1) ^ 2 + b / (s - 1)) := by
  have hw : 0 < (s - 1).re := by simp; linarith only [hs]
  have hlog := hasMellin_logarithmicCutoff hw
  have hone : HasMellin scalarMellinUnitCutoff (s - 1) (1 / (s - 1)) := hasMellin_one_Ioc hw
  have hab := hasMellin_add (hlog.1.const_smul a) (hone.1.const_smul b)
  have hp : scalarMellinMainTerm a b = fun y : ℝ => (y : ℂ) ^ (-1 : ℂ) •
      (a • (Real.log y • scalarMellinUnitCutoff y) + b • scalarMellinUnitCutoff y) := by
    funext y
    by_cases hy : y ∈ Ioc (0 : ℝ) 1
    · simp [scalarMellinMainTerm, scalarMellinUnitCutoff, hy, cpow_neg_one, smul_eq_mul, Complex.real_smul]
      ring
    · simp [scalarMellinMainTerm, scalarMellinUnitCutoff, hy]
  rw [hp]
  refine ⟨MellinConvergent.cpow_smul.mpr ?_, ?_⟩
  · simpa only [sub_eq_add_neg, scalarMellinUnitCutoff] using hab.1
  · rw [mellin_cpow_smul]
    change mellin (fun y => a • (Real.log y • scalarMellinUnitCutoff y) + b • scalarMellinUnitCutoff y) (s - 1) = _
    rw [hab.2, mellin_const_smul, mellin_const_smul, hlog.2, hone.2]
    simp only [smul_eq_mul]
    ring

theorem locallyIntegrableOn_scalarMellinMainTerm (a b : ℂ) :
    LocallyIntegrableOn (scalarMellinMainTerm a b) (Ioi 0) := by
  intro t ht
  have ht0 : 0 < t := ht
  refine ⟨Ioo (t / 2) (t + 1),
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)), ?_⟩
  rw [scalarMellinMainTerm, integrableOn_indicator_iff measurableSet_Ioc]
  have hpos : ∀ y ∈ Icc (t / 2) (t + 1), (0 : ℝ) < y :=
    fun y hy => lt_of_lt_of_le (half_pos ht0) hy.1
  have hl : ContinuousOn (fun y : ℝ => (Real.log y : ℂ)) (Icc (t / 2) (t + 1)) :=
    Complex.continuous_ofReal.comp_continuousOn
      (Real.continuousOn_log.mono fun y hy => (hpos y hy).ne')
  have hc : ContinuousOn (fun y : ℝ => (a * (Real.log y : ℂ) + b) / (y : ℂ))
      (Icc (t / 2) (t + 1)) :=
    ((continuousOn_const.mul hl).add continuousOn_const).div
      Complex.continuous_ofReal.continuousOn
      (fun y hy => Complex.ofReal_ne_zero.mpr (hpos y hy).ne')
  exact hc.integrableOn_Icc.mono_set (fun y hy => ⟨hy.2.1.le, hy.2.2.le⟩)

#print axioms hasMellin_logarithmicCutoff
#print axioms hasMellin_scalarMellinMainTerm
#print axioms locallyIntegrableOn_scalarMellinMainTerm

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
