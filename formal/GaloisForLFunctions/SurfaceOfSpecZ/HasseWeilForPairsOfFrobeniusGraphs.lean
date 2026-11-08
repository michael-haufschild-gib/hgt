import GaloisForLFunctions.SurfaceOfSpecZ.TheTorsionEnergyAgainstTheJets
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.DifferenceTwoBumpTestsDecideTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.WindowedWeilFormSliceTransfer

/-!
# Hasse–Weil for every pair of smoothed Frobenius graphs is RH

`ThePointCountOfSpecZ` shows that atomic Frobenius graphs of `Spec ℤ` fail the Hasse–Weil test for
every finite genus. Smooth the graphs by the cubic spline `B` (`splineCycle`): the smoothed graph of
degree `n` is the translate `ψ_{log n} B`, and the Castelnuovo–Severi defect of two of them depends only
on the ratio of the degrees, `δ(ψ_{log m} B, ψ_{log n} B) = c_B(log m − log n)`
(`defect_frobeniusPair`), with the orbit correlation `c_B` of `B`. So on the plane spanned by two smoothed
graphs the defect is the genus form `[[c_B(0), c], [c, c_B(0)]]`, nonnegative exactly at Hasse–Weil
`|c| ≤ c_B(0)` (`frobeniusPair_defect_nonneg_iff`), with genus `c_B(0)/2`.

**Theorem** (`riemannHypothesis_iff_forall_frobeniusPair_hasseWeil`). RH holds iff every pair of
smoothed Frobenius graphs of integer degrees passes the Hasse–Weil test. The log-ratios
`log m − log n` are dense (`dense_logRatios`), the orbit correlation is continuous, so the test on
integer pairs is the test at every real scale, which is RH because the spline sees every off-line zero
(`ArithmeticOrientationGeometry.riemannHypothesis_iff_splineOrbit_hasseWeil`).

Atomic graphs have infinite genus; smoothed graphs are a curve of genus `c_B(0)/2` exactly under RH.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri

/-- The log-ratios of positive integers are dense in `ℝ`. -/
theorem dense_logRatios :
    Dense {t : ℝ | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ t = Real.log m - Real.log n} := by
  rw [Metric.dense_iff]
  intro v ε hε
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (Real.exp_lt_exp.mpr (lt_add_of_pos_right v hε))
  have hq0 : (0 : ℝ) < q := (Real.exp_pos v).trans hq1
  have hq : (0 : ℚ) < q := by exact_mod_cast hq0
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  have hlogq : Real.log ((q.num.toNat : ℕ) : ℝ) - Real.log (q.den : ℝ) = Real.log (q : ℝ) := by
    have hn : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum.le
    rw [hn, ← Real.log_div (by exact_mod_cast hnum.ne') (by exact_mod_cast q.den_pos.ne')]
    congr 1
    exact_mod_cast (Rat.num_div_den q)
  refine ⟨Real.log (q : ℝ), ?_, ⟨q.num.toNat, q.den, by omega, q.den_pos, hlogq.symm⟩⟩
  rw [Metric.mem_ball, Real.dist_eq]
  have h1 : v < Real.log (q : ℝ) := (Real.lt_log_iff_exp_lt hq0).mpr hq1
  have h2 : Real.log (q : ℝ) < v + ε := (Real.log_lt_iff_lt_exp hq0).mpr hq2
  rw [abs_lt]; constructor <;> linarith

/-- The orbit correlation of a cycle is continuous in the scale. -/
theorem continuous_zetaOrbitCorr' (x : ScalingCycle) :
    Continuous (zetaScalingDatum.orbitCorr x) := by
  have hf : (x.2.2 : ℝ → ℝ) ∈ realTests := x.2.2.2
  obtain ⟨w, -, hw⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hf.2)
  have hbs : ∀ u, cx x.2.2 u ≠ 0 → |u| ≤ w := fun u hu => by
    by_contra h
    exact hu (hw u (not_le.mp h))
  have hlag := SquareRootThreshold.continuous_lagStructure Zeta23.zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig (cx_contDiff hf.1) hbs
  have heq : zetaScalingDatum.orbitCorr x =
      fun v => (SquareRootThreshold.lagStructure Zeta23.zetaZeroConfig (cx x.2.2) v).re := by
    funext v
    rw [← configScalingDatum_zeta_orbitCorr, configScalingDatum_orbitCorr_eq,
      lagStructure_eq Zeta23.zetaZeroConfig hf]
  rw [heq]
  exact Complex.continuous_re.comp hlag

/-- **The defect of two smoothed Frobenius graphs depends only on the ratio of their degrees.** -/
theorem defect_frobeniusPair (x : ScalingCycle) (m n : ℕ) :
    zetaScalingDatum.defect (zetaScalingDatum.act (Real.log m) x) (zetaScalingDatum.act (Real.log n) x) =
      zetaScalingDatum.orbitCorr x (Real.log m - Real.log n) := by
  rw [ScalingDatum.defect_act_act, ScalingDatum.orbitCorr]

/-- On the plane of two smoothed graphs the defect is the genus form; it is nonnegative exactly at
Hasse–Weil. -/
theorem frobeniusPair_defect_nonneg_iff (x : ScalingCycle) (t : ℝ) :
    (∀ u v : ℝ, 0 ≤ zetaScalingDatum.orbitCorr x 0 * u ^ 2 + 2 * zetaScalingDatum.orbitCorr x t * u * v +
      zetaScalingDatum.orbitCorr x 0 * v ^ 2) ↔ zetaScalingDatum.HasseWeilAt x t := by
  rw [ScalingDatum.HasseWeilAt]
  set c0 := zetaScalingDatum.orbitCorr x 0
  set c := zetaScalingDatum.orbitCorr x t
  constructor
  · intro h
    have h1 := h 1 (-1)
    have h2 := h 1 1
    rw [abs_le]
    constructor <;> nlinarith
  · intro h u v
    rw [abs_le] at h
    have hc0 : 0 ≤ c0 := by linarith [h.1, h.2]
    nlinarith [sq_nonneg (u + v), sq_nonneg (u - v), mul_nonneg (by linarith [h.2] : 0 ≤ c0 - c)
      (sq_nonneg (u - v)), mul_nonneg (by linarith [h.1] : 0 ≤ c0 + c) (sq_nonneg (u + v))]

/-- **Hasse–Weil for every pair of smoothed Frobenius graphs of integer degrees is RH.** -/
theorem riemannHypothesis_iff_forall_frobeniusPair_hasseWeil :
    RiemannHypothesis ↔ ∀ m n : ℕ, 0 < m → 0 < n →
      zetaScalingDatum.HasseWeilAt splineCycle (Real.log m - Real.log n) := by
  rw [riemannHypothesis_iff_splineOrbit_hasseWeil]
  constructor
  · intro h m n _ _; exact h _
  · intro h
    have hcont := continuous_zetaOrbitCorr' splineCycle
    have hclosed : IsClosed {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by
      simp only [ScalingDatum.HasseWeilAt]
      exact isClosed_le (continuous_abs.comp hcont) continuous_const
    have hsub : {t : ℝ | ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ t = Real.log m - Real.log n} ⊆
        {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by
      rintro _ ⟨m, n, hm, hn, rfl⟩
      exact h m n hm hn
    have huniv := (dense_logRatios.mono hsub).closure_eq
    rw [hclosed.closure_eq] at huniv
    intro t
    have : t ∈ {t : ℝ | zetaScalingDatum.HasseWeilAt splineCycle t} := by rw [huniv]; trivial
    exact this

end GaloisForLFunctions.SurfaceOfSpecZ
