import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.RelativeTolerance.MaximumLoss
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.MaximumIntervals.PrescribedTolerance
import Mathlib.Analysis.PSeries

/-! # Relative stability of the orbit maximum at polynomial accuracy margins -/
open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator ENNReal
namespace GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
open MaximumIntervals
noncomputable section

/-- Summing the logarithmic losses at tolerance increments N⁻³ costs a
convergent p-series, even with an exponential synthesis cap. -/
private theorem summable_margins :
    Summable fun k : ℕ => (1/((k+3:ℕ):ℝ)^3)*log (((2^(6*(k+3)):ℕ):ℝ)+1) := by
  have hs := (summable_nat_add_iff (f:=fun n : ℕ => 1/(n:ℝ)^2) 3).mpr
    (summable_one_div_nat_pow.mpr (by decide : 1<2))
  apply (hs.mul_left (7*log 2)).of_nonneg_of_le (fun k => mul_nonneg (by positivity) (log_nonneg (by
    linarith only [Nat.cast_nonneg (α:=ℝ) (2^(6*(k+3)))])))
  intro k
  let N := k+3
  have hN : 1 ≤ (N:ℝ) := by exact_mod_cast (by dsimp only [N]; omega : 1 ≤ N)
  have hB : (1:ℝ) ≤ 2^(6*N) := one_le_pow₀ (by norm_num)
  have hlog : log ((2:ℝ)^(6*N)+1) ≤ ((6*N+1:ℕ):ℝ)*log 2 := by
    rw [←log_pow]
    exact log_le_log (by positivity) (by rw [pow_succ]; linarith only [hB])
  have hh : ((6*N+1:ℕ):ℝ)*log 2 ≤ 7*(N:ℝ)*log 2 := by
    apply mul_le_mul_of_nonneg_right _ (log_nonneg (by norm_num))
    push_cast
    linarith only [hN]
  change (1/(N:ℝ)^3)*log (((2^(6*N):ℕ):ℝ)+1) ≤ 7*log 2*(1/(N:ℝ)^2)
  push_cast
  calc
    _ ≤ (1/(N:ℝ)^3)*(7*(N:ℝ)*log 2) := mul_le_mul_of_nonneg_left (hlog.trans hh) (by positivity)
    _ = _ := by field_simp [show (N:ℝ)≠0 by linarith only [hN]] <;> ring

private def marginLoss (ω : PathPauliDisorder) (k : ℕ) (e : ℝ) :=
  thresholdLoss (2^(6*(k+3))) (criticalHeight (chainGenerator ω k)) (1/((k+3:ℕ):ℝ)^3) e

private theorem measurable_marginLoss (k : ℕ) :
    Measurable (fun p : PathPauliDisorder × ℝ => marginLoss p.1 k p.2) := by
  let h (j : ℕ) (p : PathPauliDisorder × ℝ) := criticalHeight (chainGenerator p.1 k) j
  have hh (j : ℕ) : Measurable (h j) := (measurable_threshold k j).comp measurable_fst
  unfold marginLoss thresholdLoss
  apply Finset.measurable_fun_sum
  intro j _
  let A := {p : PathPauliDisorder × ℝ | h j p-1/((k+3:ℕ):ℝ)^3 ≤ p.2 ∧ p.2 < h j p}
  have hA : MeasurableSet A :=
    (measurableSet_le ((hh j).sub_const _) measurable_snd).inter (measurableSet_lt measurable_snd (hh j))
  exact measurable_const.indicator hA

private theorem ae_prescribed_loss :
    ∀ᵐ e : ℝ ∂volume, ∀ᵐ ω ∂pathPauliDisorderLaw, Summable (fun k => marginLoss ω k e) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  let f (k : ℕ) (p : PathPauliDisorder × ℝ) := ENNReal.ofReal (marginLoss p.1 k p.2)
  let A := {p : PathPauliDisorder × ℝ | ∑' k, f k p < ⊤}
  have hm : MeasurableSet A := measurableSet_lt
    (Measurable.tsum fun k => (measurable_marginLoss k).ennreal_ofReal) measurable_const
  have h₁ : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᵐ e : ℝ ∂volume, (ω,e) ∈ A := by
    apply Eventually.of_forall
    intro ω
    filter_upwards [ae_summable_thresholdLoss (fun k => 2^(6*(k+3)))
      (fun k => criticalHeight (chainGenerator ω k)) (fun k => 1/((k+3:ℕ):ℝ)^3)
      (fun _ => by positivity) summable_margins] with e hs
    change ∑' k, ENNReal.ofReal (marginLoss ω k e) < ⊤
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun k => thresholdLoss_nonneg _ _ _ _) hs]
    exact ENNReal.ofReal_lt_top
  filter_upwards [(Measure.ae_ae_comm hm).mp h₁] with e he
  filter_upwards [he] with ω hw
  exact (ENNReal.summable_toReal hw.ne).congr fun k =>
    ENNReal.toReal_ofReal (thresholdLoss_nonneg _ _ _ _)

/-- On the same frozen draw the maxima at e and e+N⁻³ have asymptotic
ratio one, for almost every positive prescribed error. -/
theorem gaussian_prescribed_relative_maximum :
    ∀ᵐ e : ℝ ∂volume, 0 < e → ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ r > (1:ℝ),
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let H := chainGenerator ω k
        ∃ m n : ℕ, IsRecurrentOrbitCircuitMaximumAt H e m ∧
          IsRecurrentOrbitCircuitMaximumAt H (e+1/(N:ℝ)^3) n ∧ n ≤ m ∧
          (m:ℝ)+1 ≤ r*((n:ℝ)+1) := by
  filter_upwards [ae_prescribed_loss] with e he hepos
  filter_upwards [he] with ω hw
  intro r hr
  filter_upwards [hw.tendsto_atTop_zero.eventually_lt_const (log_pos hr)] with k hk
  intro N H
  have hN : 2 ≤ N := by dsimp only [N]; omega
  have hδ : 0 ≤ 1/(N:ℝ)^3 := by positivity
  have hloc := hasPauliWeightAtMost_pathHamiltonian (pathPauliDisorderShell ω (k+1))
    (isSelfAdjoint_pathHamiltonian _)
  obtain ⟨m,hm⟩ := twoLocal_exists_recurrent_maximum_at hN H hloc e hepos
  obtain ⟨n,hn⟩ := twoLocal_exists_recurrent_maximum_at hN H hloc _ (add_pos_of_pos_of_nonneg hepos hδ)
  have hnm : n ≤ m := by
    obtain ⟨u,hu⟩ := required_at_some_date hn
    obtain ⟨z,hz,C,hC,hfit⟩ := hm.1 u
    exact hu m ⟨z,hz,C,hC,hfit.trans (le_add_of_nonneg_right hδ)⟩
  have hl := log_maximum_drop H hδ hm hn (max_cap hN H hepos.le hm)
  change thresholdLoss _ _ _ _ < log r at hk
  rw [hl] at hk
  refine ⟨m,n,hm,hn,hnm,le_of_lt ((log_lt_log_iff (by positivity) (by positivity)).mp ?_)⟩
  rw [log_mul (zero_lt_one.trans hr).ne' (by positivity)]
  linarith only [hk]

#print axioms gaussian_prescribed_relative_maximum
end
end GaloisForLFunctions.HTGeometry.AccuracyScales.RelativeTolerance
