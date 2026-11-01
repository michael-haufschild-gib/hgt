import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeOfTheCompleteWeilFamily
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileWithoutRealFourierZerosIsUniformlyPositiveOnBoundedOverlap

/-!
# A smooth profile carries both edge regimes

The universal regime of the detection edge (`edge → ∞` unconditionally) was known for the tilted
spline, which is only `C²`, while the receivers at every power of `log N` on the pole hyperplane
need a `C^∞` nonnegative profile. This module puts both on one profile.

* **The universal regime needs only real Fourier nonvanishing** (`tendsto_edge_of_noRealZero`):
  for every `C²` profile on `[0, 1]` whose Fourier transform has no real zero, the edge tends to
  `∞` unconditionally, by uniform positivity on every bounded overlap interval.
* **Smooth profiles without real Fourier zeros exist** (`exists_smooth_profile_noRealZero`): the
  tilt `e^{λu}·b(u)` of a smooth bump `b` has transform `b̂(r − iλ)`; the zeros of the entire
  nonzero function `b̂` are countable, so all but countably many tilts avoid the real line.
* **Both regimes on one profile** (`exists_smooth_profile_with_both_edge_regimes`): there is a
  `C^∞` nonnegative profile on `[0, 1]` whose edge tends to `∞` unconditionally and for which RH is
  equivalent to positivity on `v₁^⊥` at overlap `2(log N)^α`, for every `α > 0`. Without RH its
  hyperplane edge tends to `∞` and is at most `2(log N)^β` infinitely often for every `β > 0`.
-/

noncomputable section

open Filter Topology Finset MeasureTheory Zeta23
open scoped RealInnerProductSpace ENNReal ContDiff

namespace GaloisForLFunctions.EdgeHodgeTheory

open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
  ArithmeticCastelnuovoSeveri

/-- **Universal regime from real Fourier nonvanishing.** For a `C²` profile on `[0, 1]` without
real Fourier zeros the edge tends to `∞`: below any bound `K` the complete Weil matrices are
eventually positive definite for all overlaps in `[1, K]` at once. -/
theorem tendsto_edge_of_noRealZero {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0) :
    Tendsto (edge φ) atTop (𝓝 ⊤) := by
  refine ENNReal.tendsto_nhds_top_iff_nat.mpr fun n => ?_
  have hK : (1 : ℝ) ≤ n + 1 := by linarith only [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  filter_upwards [CriticalArithmeticCorrelationTheory.eventually_noRealZero_completeWeilMatrix_posDef_uniform_overlap
    hφ hsupp hFT hK] with N hN
  have hle : ENNReal.ofReal ((n : ℝ) + 1) ≤ edge φ N :=
    ofReal_le_firstFailure_iff.mpr fun c hc hcK x =>
      RenormalizedIntersectionTheory.energy_nonneg_of_posDef (completeWeilMatrix_isHermitian _ _ _)
        (hN c hc hcK.le) x
  refine lt_of_lt_of_le ?_ hle
  rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  exact_mod_cast Nat.lt_succ_self n

/-- The hyperplane edge is at least the edge, so it tends to `∞` as well. -/
theorem tendsto_hyperplaneEdge_of_noRealZero {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hFT : ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0) :
    Tendsto (hyperplaneEdge φ) atTop (𝓝 ⊤) :=
  tendsto_nhds_top_mono (tendsto_edge_of_noRealZero hφ hsupp hFT)
    (Eventually.of_forall fun N => edge_le_hyperplaneEdge φ N)

/-! ### Smooth profiles without real Fourier zeros -/

/-- A nonzero entire function misses some horizontal line: its zeros are countable. -/
theorem exists_horizontal_line_free_of_zeros {G : ℂ → ℂ} (hG : Differentiable ℂ G) {z₀ : ℂ}
    (hz₀ : G z₀ ≠ 0) : ∃ μ : ℝ, ∀ r : ℝ, G ((r : ℂ) + μ * Complex.I) ≠ 0 := by
  have hcod : G ⁻¹' {0}ᶜ ∈ codiscrete ℂ :=
    AnalyticOnNhd.preimage_zero_mem_codiscrete (fun z _ => hG.analyticAt z) hz₀
  have hfin : ∀ n : ℕ, (Metric.closedBall (0 : ℂ) n ∩ G ⁻¹' {0}).Finite := by
    intro n
    have h := (isCompact_closedBall (0 : ℂ) n).finite_sdiff_of_mem_codiscreteWithin
      (codiscreteWithin_mono (Set.subset_univ _) hcod)
    simpa only [Set.sdiff_eq, Set.preimage_compl, compl_compl] using h
  have hZ : (G ⁻¹' {0}).Countable := by
    have hcover : G ⁻¹' {0} ⊆ ⋃ n : ℕ, Metric.closedBall (0 : ℂ) n ∩ G ⁻¹' {0} := by
      intro z hz
      obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
      exact Set.mem_iUnion.mpr ⟨n, mem_closedBall_zero_iff.mpr hn, hz⟩
    exact (Set.countable_iUnion fun n => (hfin n).countable).mono hcover
  by_contra h
  push Not at h
  refine Cardinal.not_countable_real ((hZ.image Complex.im).mono fun μ _ => ?_)
  obtain ⟨r, hr⟩ := h μ
  exact ⟨_, hr, by simp⟩

/-- An exponential tilt shifts the Fourier variable off the real axis. -/
theorem paperFT_exp_tilt (b : ℝ → ℝ) (lam : ℝ) (z : ℂ) :
    paperFT (cx fun u => Real.exp (lam * u) * b u) z =
      paperFT (cx b) (z - lam * Complex.I) := by
  unfold paperFT cx
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  push_cast
  rw [mul_comm (Complex.exp _) ((b u : ℂ)), mul_assoc, ← Complex.exp_add]
  congr 2
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **A smooth nonnegative profile on `[0, 1]` without real Fourier zeros.** -/
theorem exists_smooth_profile_noRealZero :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) ∧ (∀ u, 0 ≤ φ u) ∧
      0 < (∫ u, φ u) ∧ ∀ r : ℝ, paperFT (cx φ) (r : ℂ) ≠ 0 := by
  let b : ℝ → ℝ := RenormalizedIntersectionTheory.unitBump
  have hbc : Continuous b := RenormalizedIntersectionTheory.unitBump.continuous
  have hbs : HasCompactSupport b := RenormalizedIntersectionTheory.unitBump.hasCompactSupport
  have hG : Differentiable ℂ (paperFT (cx b)) :=
    RHTower.EvenSector.differentiable_paperFT_of_compact (Complex.continuous_ofReal.comp hbc)
      (hbs.comp_left Complex.ofReal_zero)
  have hG0 : paperFT (cx b) 0 ≠ 0 := by
    have h : paperFT (cx b) 0 = ((∫ u, b u : ℝ) : ℂ) := by
      unfold paperFT cx
      simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
      exact integral_ofReal
    rw [h]
    exact Complex.ofReal_ne_zero.mpr RenormalizedIntersectionTheory.unitBump.integral_pos.ne'
  obtain ⟨μ, hμ⟩ := exists_horizontal_line_free_of_zeros hG hG0
  let φ : ℝ → ℝ := fun u => Real.exp (-μ * u) * b u
  have hφ : ContDiff ℝ ∞ φ :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).mul
      RenormalizedIntersectionTheory.unitBump.contDiff
  have hnn : ∀ u, 0 ≤ φ u := fun u =>
    mul_nonneg (Real.exp_pos _).le RenormalizedIntersectionTheory.unitBump.nonneg
  refine ⟨φ, hφ, fun u hu => ?_, hnn, ?_, fun r => ?_⟩
  · simp only [φ, b, RenormalizedIntersectionTheory.unitBump_eq_zero u hu, mul_zero]
  · have hpos : φ (1 / 2) ≠ 0 :=
      (mul_pos (Real.exp_pos _) (RenormalizedIntersectionTheory.unitBump.pos_of_mem_ball
        (Metric.mem_ball_self RenormalizedIntersectionTheory.unitBump.rOut_pos))).ne'
    exact (hφ.continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hbs.mul_left) (fun u => hnn u) hpos
  · rw [paperFT_exp_tilt, show (r : ℂ) - ((-μ : ℝ) : ℂ) * Complex.I = (r : ℂ) + μ * Complex.I by
      push_cast; ring]
    exact hμ r

/-! ### Both regimes on one smooth profile -/

/-- **Both edge regimes on one smooth profile.** There is a `C^∞` nonnegative profile `φ` on
`[0, 1]` with positive mass such that
* unconditionally, its edge tends to `∞` (the universal regime);
* for every `α > 0`, RH holds iff its complete Weil matrices are eventually positive on `v₁^⊥` at
  overlap `2(log N)^α` (receivers at every power of the logarithm);
* without RH, its hyperplane edge tends to `∞` and is at most `2(log N)^β` infinitely often, for
  every `β > 0`. -/
theorem exists_smooth_profile_with_both_edge_regimes :
    ∃ φ : ℝ → ℝ, ContDiff ℝ ∞ φ ∧ (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) ∧ (∀ u, 0 ≤ φ u) ∧
      0 < (∫ u, φ u) ∧ Tendsto (edge φ) atTop (𝓝 ⊤) ∧
      (∀ α : ℝ, 0 < α → (RiemannHypothesis ↔
        ∀ᶠ N : ℕ in atTop, HyperplanePositiveAt φ (2 * Real.log N ^ α) N)) ∧
      (¬ RiemannHypothesis → Tendsto (hyperplaneEdge φ) atTop (𝓝 ⊤) ∧
        ∀ β : ℝ, 0 < β →
          ∃ᶠ N : ℕ in atTop, hyperplaneEdge φ N ≤ ENNReal.ofReal (2 * Real.log N ^ β)) := by
  obtain ⟨φ, hφ, hsupp, hnn, hint, hFT⟩ := exists_smooth_profile_noRealZero
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  have hM : 0 < ∫ u, φ u ^ 2 := integral_sq_pos_of_noRealZero hφ2 hsupp hFT
  refine ⟨φ, hφ, hsupp, hnn, hint, tendsto_edge_of_noRealZero hφ2 hsupp hFT,
    fun α hα => RenormalizedIntersectionTheory.riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log
      hφ hsupp hnn hint hM hα, fun hRH => ⟨tendsto_hyperplaneEdge_of_noRealZero hφ2 hsupp hFT,
        fun β hβ => frequently_hyperplaneEdge_le_of_smooth hφ hsupp hnn hint hM hRH hβ⟩⟩

end GaloisForLFunctions.EdgeHodgeTheory

#print axioms GaloisForLFunctions.EdgeHodgeTheory.tendsto_edge_of_noRealZero
#print axioms GaloisForLFunctions.EdgeHodgeTheory.exists_smooth_profile_with_both_edge_regimes
