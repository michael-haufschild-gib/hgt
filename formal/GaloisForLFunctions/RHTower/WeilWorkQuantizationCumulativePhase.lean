import GaloisForLFunctions.RHTower.WeilWorkQuantizationResidualPhase

/-!
# The actual cumulative residual phase

Finite-interval integer counts identify the reflected radial phase even when
total residual mass is infinite. Monotonicity and mass growth are derived
from the same canonical residual measure. Boundary zeros are retained.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open HamburgerStability IntegerMassRigidity FractionalMassRigidity PhaseLockRigidity

def quantizationResidualCumulative {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (x : ℝ) : ℝ :=
  (quantizationResidualMeasure hW).real (Ioc 0 (2 * x))

def quantizationOriginPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : ℂ :=
  Complex.exp (((Real.pi * (boundaryMeasure hW).real {0} : ℝ) : ℂ) * I)

theorem quantizationResidualMeasure_Ioc_ne_top {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (a b : ℝ) : quantizationResidualMeasure hW (Ioc a b) ≠ ∞ :=
  ne_top_of_le_ne_top (quantization_boundaryMeasure_Icc_ne_top hW a b)
    ((quantizationResidualMeasure_le hW _).trans (measure_mono Ioc_subset_Icc_self))

theorem monotone_quantizationResidualCumulative {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Monotone (quantizationResidualCumulative hW) := by
  intro a b hab
  exact ENNReal.toReal_mono (quantizationResidualMeasure_Ioc_ne_top hW 0 (2 * b))
    (measure_mono (by intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩))

theorem norm_quantizationOriginPhase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ‖quantizationOriginPhase hW‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- Actual interval mass controls the cumulative phase, including singular mass. -/
theorem quantizationResidualCumulative_power_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {α K : ℝ} (hgrowth : ∀ T : ℝ, 1 ≤ T →
      (quantizationResidualMeasure hW).real (Icc (-T) T) ≤ K * T ^ α)
    {x : ℝ} (hx : 1 ≤ x) : quantizationResidualCumulative hW x ≤ (K * 2 ^ α) * x ^ α := by
  have hfin : quantizationResidualMeasure hW (Icc (-(2 * x)) (2 * x)) ≠ ∞ :=
    ne_top_of_le_ne_top (quantization_boundaryMeasure_Icc_ne_top hW (-(2 * x)) (2 * x))
      (quantizationResidualMeasure_le hW _)
  have hsub : Ioc 0 (2 * x) ⊆ Icc (-(2 * x)) (2 * x) := by
    intro r hr; exact ⟨by linarith [hr.1], hr.2⟩
  calc quantizationResidualCumulative hW x ≤
        (quantizationResidualMeasure hW).real (Icc (-(2 * x)) (2 * x)) :=
          ENNReal.toReal_mono hfin (measure_mono hsub)
    _ ≤ K * (2 * x) ^ α := hgrowth _ (by linarith)
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ x)]; ring

/-- The cumulative phase uses only finite intervals, even if total residual mass is infinite. -/
theorem quantizationReflectedTraceF_cumulative_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {t : ℝ} (ht : t < 0) (hno : boundaryMeasure hW {-(2 * t)} = 0) :
    quantizationReflectedTraceF hW (2 * t) = quantizationOriginPhase hW *
      Complex.exp (((2 * Real.pi * quantizationResidualCumulative hW (-t) : ℝ) : ℂ) * I) *
        quantizationTraceF hW (2 * t) := by
  let ν := quantizationResidualMeasure hW
  let y : ℝ := -(2 * t)
  have hy : 0 < y := by dsimp [y]; linarith
  have hμfin := boundaryMeasure_Ioo_ne_top hW 0 y
  obtain ⟨n, hn⟩ := quantizationIntegerMeasure_nat hW measurableSet_Ioo hμfin
  have hdec := quantization_real_mass_decomposition hW measurableSet_Ioo hμfin
  have hn' : (quantizationIntegerMeasure hW).real (Ioo 0 y) = n := by
    simp only [Measure.real, hn, ENNReal.toReal_natCast]
  rw [hn'] at hdec
  have hνy : ν {y} = 0 := le_antisymm ((quantizationResidualMeasure_le hW {y}).trans_eq hno) bot_le
  have hu : Ioo 0 y ∪ {y} = Ioc 0 y := by
    ext r
    simp only [mem_union, mem_Ioo, mem_singleton_iff, mem_Ioc]
    constructor
    · rintro (h | rfl)
      · exact ⟨h.1, h.2.le⟩
      · exact ⟨hy, le_rfl⟩
    · intro h
      rcases lt_or_eq_of_le h.2 with h' | h'
      · exact Or.inl ⟨h.1, h'⟩
      · exact Or.inr h'
  have hd : Disjoint (Ioo 0 y) {y} := by
    apply Set.disjoint_left.mpr
    intro r hr hr'
    have : r = y := hr'
    subst r
    exact lt_irrefl y hr.2
  have hmass : ν.real (Ioo 0 y) = ν.real (Ioc 0 y) := by
    unfold Measure.real
    rw [← hu, measure_union hd (measurableSet_singleton y), hνy, add_zero]
  have hcum : quantizationResidualCumulative hW (-t) = ν.real (Ioo 0 y) := by
    rw [hmass]
    unfold quantizationResidualCumulative
    congr 2
    dsimp [y]
    ring
  have hphase : Complex.exp (((Real.pi * (boundaryMeasure hW).real {0} +
      2 * Real.pi * (boundaryMeasure hW).real (Ioo 0 y) : ℝ) : ℂ) * I) =
      quantizationOriginPhase hW *
        Complex.exp (((2 * Real.pi * quantizationResidualCumulative hW (-t) : ℝ) : ℂ) * I) := by
    have he : (((Real.pi * (boundaryMeasure hW).real {0} +
        2 * Real.pi * (boundaryMeasure hW).real (Ioo 0 y) : ℝ) : ℂ) * I) =
        (((Real.pi * (boundaryMeasure hW).real {0} : ℝ) : ℂ) * I) +
        (((2 * Real.pi * quantizationResidualCumulative hW (-t) : ℝ) : ℂ) * I) +
        (n : ℂ) * (2 * Real.pi * I) := by
      rw [hcum, hdec]
      push_cast
      ring
    rw [he, Complex.exp_add, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
    rfl
  have htrace := quantizationCompletedTrace_phase hW hy hno
  rw [hphase] at htrace
  have hneg : -y = 2 * t := by dsimp [y]; ring
  rw [hneg] at htrace
  simp only [quantizationReflectedTraceF, quantizationTraceF]
  rw [htrace]
  ring

theorem ae_quantizationReflectedTraceF_cumulative_phase {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∀ᵐ t : ℝ, t < 0 → quantizationReflectedTraceF hW (2 * t) = quantizationOriginPhase hW *
      Complex.exp (((2 * Real.pi * quantizationResidualCumulative hW (-t) : ℝ) : ℂ) * I) *
        quantizationTraceF hW (2 * t) := by
  filter_upwards [ae_quantization_boundary_nonatom hW] with t ht
  exact fun ht0 => quantizationReflectedTraceF_cumulative_phase hW ht0 ht

end RHTower.WeilSpectral
