import GaloisForLFunctions.BiScaleUncertainty.NyquistResidualOperator

/-! # Exact polar production by cell averages, with a stable all-tail residual -/

open MeasureTheory Set Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistPolarCellAverage (H : ℝ →ᵇ ℝ) (k : ℕ) : ℝ :=
  nyquistPolarConstant (k + 1) * ∫ x in nyquistResidualCell k, H x

def nyquistPolarProducer (N : ℕ) (H : ℝ →ᵇ ℝ) : ℝ :=
  ∑' k : ℕ, nyquistPolarCellAverage H (N + k)

def nyquistPolarTail (N : ℕ) (H : ℝ →ᵇ ℝ) : ℝ :=
  ∫ x in Ioi (nyquistResidualNode N), H x * Real.cosh (x / 2)

theorem integral_polar_nyquistResidualCell (H : ℝ →ᵇ ℝ) (k : ℕ) :
    (∫ x in nyquistResidualCell k, H x * Real.cosh (x / 2)) =
      nyquistPolarCellAverage H k + nyquistCellResidual H k := by
  have hh : (fun x => H x * Real.cosh (x / 2)) =
      fun x => nyquistPolarConstant (k + 1) * H x + H x * nyquistResidualDensity k x := by
    funext x
    dsimp [nyquistResidualDensity]
    ring
  rw [hh, integral_add]
  · rw [integral_const_mul]
    rfl
  · exact (H.continuous.const_mul _).integrableOn_Ioc
  · exact (H.continuous.mul (continuous_nyquistResidualDensity k)).integrableOn_Ioc

theorem nyquistPolarCellAverage_eventually_zero (H : ℝ →ᵇ ℝ)
    (hH : HasCompactSupport (⇑H)) :
    ∃ M : ℕ, ∀ k : ℕ, M ≤ k →
      nyquistPolarCellAverage H k = 0 ∧ nyquistCellResidual H k = 0 := by
  obtain ⟨R, hR, hz⟩ := hH.exists_pos_le_norm
  obtain ⟨M, hM⟩ := (tendsto_nyquistResidualNode.eventually (eventually_ge_atTop R)).exists
  refine ⟨M, ?_⟩
  intro k hk
  have hzero (x : ℝ) (hx : x ∈ nyquistResidualCell k) : H x = 0 := by
    apply hz
    rw [Real.norm_eq_abs]
    exact (hM.trans (strictMono_nyquistResidualNode.monotone hk)).trans
      (hx.1.le.trans (le_abs_self x))
  have hI : (∫ x in nyquistResidualCell k, H x) = 0 := by
    calc
      _ = ∫ _x in nyquistResidualCell k, (0 : ℝ) :=
        setIntegral_congr_fun (measurableSet_nyquistResidualCell k) hzero
      _ = 0 := by simp
  constructor
  · simp only [nyquistPolarCellAverage, hI, mul_zero]
  · change (∫ x in nyquistResidualCell k, H x * nyquistResidualDensity k x) = 0
    calc
      _ = ∫ _x in nyquistResidualCell k, (0 : ℝ) := by
        apply setIntegral_congr_fun (measurableSet_nyquistResidualCell k)
        intro x hx
        change H x * nyquistResidualDensity k x = 0
        rw [hzero x hx, zero_mul]
      _ = 0 := by simp

theorem hasSum_nyquistPolarCellAverage (N : ℕ) (H : ℝ →ᵇ ℝ)
    (hH : HasCompactSupport (⇑H)) :
    HasSum (fun k => nyquistPolarCellAverage H (N + k))
      (nyquistPolarTail N H - nyquistResidualOperator N H) := by
  have hi : Integrable (fun x => H x * Real.cosh (x / 2)) :=
    (H.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hH.mul_right
  have hs := hasSum_integral_iUnion
    (fun k : ℕ => measurableSet_nyquistResidualCell (N + k))
    (fun i j hij => pairwise_disjoint_nyquistResidualCell (by omega : N + i ≠ N + j))
    hi.integrableOn
  rw [iUnion_nyquistResidualCell] at hs
  have hh := hs.sub (summable_nyquistCellResidual H N).hasSum
  simpa only [integral_polar_nyquistResidualCell, add_sub_cancel_right,
    ← nyquistResidualOperator_eq_tsum, nyquistPolarTail] using hh

theorem summable_nyquistPolarCellAverage (N : ℕ) (H : ℝ →ᵇ ℝ)
    (hH : HasCompactSupport (⇑H)) :
    Summable (fun k => nyquistPolarCellAverage H (N + k)) :=
  (hasSum_nyquistPolarCellAverage N H hH).summable

theorem nyquistPolarProducer_eq_sub (N : ℕ) (H : ℝ →ᵇ ℝ)
    (hH : HasCompactSupport (⇑H)) :
    nyquistPolarProducer N H = nyquistPolarTail N H - nyquistResidualOperator N H :=
  (hasSum_nyquistPolarCellAverage N H hH).tsum_eq

theorem nyquistPolarTail_decomposition (N : ℕ) (H : ℝ →ᵇ ℝ)
    (hH : HasCompactSupport (⇑H)) :
    nyquistPolarTail N H = nyquistPolarProducer N H + nyquistResidualOperator N H := by
  rw [nyquistPolarProducer_eq_sub N H hH]
  ring

theorem nyquistPolarProducer_error_le (N : ℕ) (H : ℝ →ᵇ ℝ)
    (hH : HasCompactSupport (⇑H)) :
    |nyquistPolarTail N H - nyquistPolarProducer N H| ≤ nyquistResidualTailScale N * ‖H‖ := by
  rw [nyquistPolarTail_decomposition N H hH, add_sub_cancel_left]
  exact nyquistResidualOperator_abs_le_scale N H

theorem nyquistPolar_convergence_iff_producer {H : ℝ →ᵇ ℝ} {F : ℕ → ℝ →ᵇ ℝ}
    (hH : HasCompactSupport (⇑H)) (hF : ∀ n, HasCompactSupport (⇑(F n)))
    (hu : TendstoUniformly (fun n => ⇑(F n)) (⇑H) atTop) (N : ℕ) :
    Tendsto (fun n => nyquistPolarTail N (F n)) atTop (𝓝 (nyquistPolarTail N H)) ↔
      Tendsto (fun n => nyquistPolarProducer N (F n)) atTop (𝓝 (nyquistPolarProducer N H)) := by
  have hr := tendsto_nyquistResidualOperator_of_uniform hu N
  constructor
  · intro hp
    simpa only [nyquistPolarTail_decomposition N H hH,
      nyquistPolarTail_decomposition N (F _) (hF _), add_sub_cancel_right] using hp.sub hr
  · intro hq
    simpa only [← nyquistPolarTail_decomposition N H hH,
      ← nyquistPolarTail_decomposition N (F _) (hF _)] using hq.add hr

end
end GaloisForLFunctions.BiScaleUncertainty
