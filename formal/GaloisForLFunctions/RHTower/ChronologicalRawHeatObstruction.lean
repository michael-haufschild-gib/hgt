import GaloisForLFunctions.RHTower.ChronologicalPositiveAbelTransfer
import GaloisForLFunctions.RHTower.BaezDuarteMobiusCriticalTailObstruction
import GaloisForLFunctions.RHTower.HardyDyadicWindowTheorem
import GaloisForLFunctions.RHTower.ChronologicalDampingRigidity
import GaloisForLFunctions.RHTower.ChronologicalHeatMellin

/-!
# The raw chronological heat obstruction and its positive survivor

Raw Möbius heat errors do not converge to zero in the genuine L²(0,∞) norm.
Positive Abel transfer would otherwise kill the canonical critical Laplace
profile, which a closed Hardy zero theorem forbids. Existing damping rigidity
then rules out every vanishing geometric-response damping schedule.

A fixed positive raw error recurs cofinally. Consequently every successful
arithmetic array must add a correction of nonvanishing L² size cofinally.
These results do not rule out general bounded arrays and do not prove RH.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RHTower

/-- The finite positive-Abel estimate passes to the genuine, absolutely
convergent Möbius--Laplace series. -/
theorem chronologicalRaw_to_laplace_bound (M : ℕ) {δ t : ℝ}
    (hδ : 0 ≤ δ) (ht : 0 < t)
    (hE : ∀ n, M ≤ n → chronologicalL2Norm (chronologicalRawHeatError n) ≤ δ) :
    ‖mobiusDiscreteLaplaceTransform t‖ ≤ 6*δ / Real.sqrt t + 6 + (M:ℝ) := by
  have hlim := (mobiusDiscreteLaplaceTerm_hasSum ht).tendsto_sum_nat.norm
  apply le_of_tendsto hlim
  filter_upwards with N
  have he (k : ℕ) : mobiusDiscreteLaplaceTerm t k =
      (((ArithmeticFunction.moebius k : ℝ) * Real.exp (-((k:ℝ)*t))) : ℂ) := by
    simp [mobiusDiscreteLaplaceTerm, Complex.ofReal_exp]
  simp_rw [he]
  simp_rw [← Complex.ofReal_mul]
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  exact chronologicalRaw_to_finite_laplace_bound M hδ ht hE N

/-- A vanishing raw heat norm would force the forbidden critical Laplace limit.
This implication is proved from the actual source and positive Abel weights. -/
theorem chronologicalRaw_convergence_forces_critical_profile
    (hE : Tendsto (fun N => chronologicalL2Norm (chronologicalRawHeatError N))
      atTop (𝓝 0)) :
    Tendsto mobiusLaplaceCriticalProfile atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε/12 := by positivity
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hE) (ε/12) hδ
  have htail : ∀ n, M ≤ n → chronologicalL2Norm (chronologicalRawHeatError n) ≤ ε/12 := by
    intro n hn
    have h := hM n hn
    simpa [Real.dist_eq, abs_of_nonneg (chronologicalL2Norm_nonneg _)] using h.le
  have hhalf : Tendsto (fun y : ℝ => y/2) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (by positivity : (0:ℝ) < 1/2)).mpr
      (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)
    simpa only [one_div, div_eq_mul_inv, mul_comm, id_eq, one_mul] using h
  have hexp : Tendsto (fun y : ℝ => Real.exp (-y/2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hhalf
  have hsmall : Tendsto (fun y : ℝ => (6+(M:ℝ))*Real.exp (-y/2)) atTop (𝓝 0) := by
    simpa using hexp.const_mul (6+(M:ℝ))
  obtain ⟨Y, hY⟩ := (Metric.tendsto_atTop.mp hsmall) (ε/2) (by positivity)
  refine ⟨Y, ?_⟩
  intro y hy
  have hL := chronologicalRaw_to_laplace_bound M hδ.le (Real.exp_pos (-y)) htail
  have hs : Real.sqrt (Real.exp (-y)) = Real.exp (-y/2) := by
    have he : Real.exp (-y) = Real.exp (-y/2)^2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he, Real.sqrt_sq (Real.exp_pos _).le]
  rw [hs] at hL
  have hP : ‖mobiusLaplaceCriticalProfile y‖ ≤ ε/2 + (6+(M:ℝ))*Real.exp (-y/2) := by
    rw [mobiusLaplaceCriticalProfile, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le).trans_eq
    field_simp
    ring
  have hsmallY := hY y hy
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hsmallY
  rw [dist_zero_right]
  linarith

/-- Raw Möbius chronological heat repair fails unconditionally in the actual
full L² norm. A closed Hardy theorem supplies the critical zero. -/
theorem chronologicalRawHeat_not_convergent :
    ¬ Tendsto (fun N => chronologicalL2Norm (chronologicalRawHeatError N)) atTop (𝓝 0) := by
  intro hE
  obtain ⟨T₀, _hT₀, hzero⟩ := exists_riemannZeta_line_zero_dyadic
  obtain ⟨τ, _hτ, hτzero⟩ := hzero T₀ le_rfl
  exact not_tendsto_mobiusLaplaceCriticalProfile_zero_of_critical_zeta_zero
    (linePt_re τ) hτzero (chronologicalRaw_convergence_forces_critical_profile hE)

/-- Positive survivor: one nonzero raw error floor recurs at arbitrarily large
cutoffs; no numerical value or simplicity assumption is required. -/
theorem chronologicalRawHeat_frequent_floor :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
      c ≤ chronologicalL2Norm (chronologicalRawHeatError N) := by
  by_contra hfloor
  push Not at hfloor
  apply chronologicalRawHeat_not_convergent
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := hfloor ε hε
  refine ⟨M, ?_⟩
  intro N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (chronologicalL2Norm_nonneg _)]
  exact hM N hN

/-- Geometric response damping tending to zero cannot repair the raw sequence.
The statement rules out the complete schedule, not just a selected numerical fit. -/
theorem chronologicalDampedHeat_no_vanishing_schedule :
    ¬ ∃ ε : ℕ → ℝ, (∀ N, 0 ≤ ε N) ∧ (∀ N, ε N ≤ 1/2) ∧
      Tendsto ε atTop (𝓝 0) ∧
      Tendsto (fun N => chronologicalL2Norm (chronologicalDampedHeatError (ε N) N))
        atTop (𝓝 0) := by
  rintro ⟨ε, hε0, hεh, hε, hD⟩
  exact chronologicalRawHeat_not_convergent
    ((chronologicalDampedHeat_converges_iff_raw hε0 hεh hε).mp hD)

/-- Every successful arithmetic repair must supply a correction of nonvanishing
L² size cofinally often. This holds for all arrays, independently of their
coefficient budget, and does not deny the original bounded-array target. -/
theorem chronologicalSuccessfulRepair_requires_persistent_correction :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ → ℕ → ℝ,
      Tendsto (fun N => chronologicalL2Norm (chronologicalHeatError (a N) N)) atTop (𝓝 0) →
      ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧ c ≤ chronologicalL2Norm
        (fun t => chronologicalHeatError (a N) N t - chronologicalRawHeatError N t) := by
  obtain ⟨c, hc, hfloor⟩ := chronologicalRawHeat_frequent_floor
  refine ⟨c/2, by positivity, ?_⟩
  intro a ha M
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp ha) (c/2) (by positivity)
  obtain ⟨N, hN, hlow⟩ := hfloor (max M K)
  refine ⟨N, (le_max_left _ _).trans hN, ?_⟩
  have hsmall := hK N ((le_max_right _ _).trans hN)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (chronologicalL2Norm_nonneg _)] at hsmall
  have htri := lpNorm_le_lpNorm_add_lpNorm_sub'
    (chronologicalHeatError_memLp (a N) N) (by simp : (1:ENNReal) ≤ 2)
    (f := chronologicalRawHeatError N)
  rw [lpNorm_sub_comm] at htri
  change chronologicalL2Norm (chronologicalRawHeatError N) ≤
    chronologicalL2Norm (chronologicalHeatError (a N) N) + chronologicalL2Norm
      (fun t => chronologicalHeatError (a N) N t - chronologicalRawHeatError N t) at htri
  linarith

end RHTower
