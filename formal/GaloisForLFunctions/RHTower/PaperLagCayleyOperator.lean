import GaloisForLFunctions.RHTower.PaperLagCayleyChannels
import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator

/-! # Unitary source encoding and all continuous phase observations

Uniform continuity on the circle transports the literal source discrepancy to
every continuous observable. Finite coordinate prefixes approximate the original
source/model operator difference with the native reciprocal error bound.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHTower.PaperLagCayley

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

abbrev Space := lp (fun _ : ℕ => ℂ) 2

def observable (f : C(Circle, ℂ)) : Space →L[ℂ] Space :=
  lpDiagonalCLM (fun n => f (phase n)) (norm_nonneg f) (fun _ => f.norm_coe_le_norm _)

def modelObservable (f : C(Circle, ℂ)) : Space →L[ℂ] Space :=
  lpDiagonalCLM (fun n => f (arithmeticPhase n)) (norm_nonneg f) (fun _ => f.norm_coe_le_norm _)

theorem observable_apply (f : C(Circle, ℂ)) (x : Space) (n : ℕ) :
    observable f x n = f (phase n) * x n := rfl

theorem modelObservable_apply (f : C(Circle, ℂ)) (x : Space) (n : ℕ) :
    modelObservable f x n = f (arithmeticPhase n) * x n := rfl

theorem norm_observable_le (f : C(Circle, ℂ)) : ‖observable f‖ ≤ ‖f‖ :=
  norm_lpDiagonalCLM_le _ _ _

theorem norm_modelObservable_le (f : C(Circle, ℂ)) : ‖modelObservable f‖ ≤ ‖f‖ :=
  norm_lpDiagonalCLM_le _ _ _

theorem observable_discrepancy_tendsto (f : C(Circle, ℂ)) :
    Tendsto (fun n => ‖f (phase n) - f (arithmeticPhase n)‖) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hf⟩ := Metric.uniformContinuous_iff.1
    (CompactSpace.uniformContinuous_of_continuous f.continuous) ε hε
  filter_upwards [Metric.tendsto_nhds.1 phase_discrepancy_tendsto δ hδ] with n hn
  have hd : dist (phase n) (arithmeticPhase n) < δ := by
    change dist (phase n : ℂ) (arithmeticPhase n : ℂ) < δ
    simpa only [dist_eq_norm, sub_zero, norm_norm] using hn
  simpa only [dist_eq_norm, sub_zero, norm_norm] using hf hd

theorem observable_sub_model_compact (f : C(Circle, ℂ)) :
    IsCompactOperator (observable f - modelObservable f) :=
  paperBoundedDiagonal_sub_compact _ _ (norm_nonneg f) (fun _ => f.norm_coe_le_norm _)
    (norm_nonneg f) (fun _ => f.norm_coe_le_norm _) (observable_discrepancy_tendsto f)

def circleCoordinate : C(Circle, ℂ) := ⟨fun z => (z : ℂ), continuous_subtype_val⟩

def sourceOperator : Space →L[ℂ] Space := observable circleCoordinate

def arithmeticOperator : Space →L[ℂ] Space := modelObservable circleCoordinate

theorem sourceOperator_apply (x : Space) (n : ℕ) :
    sourceOperator x n = (phase n : ℂ) * x n := rfl

theorem arithmeticOperator_apply (x : Space) (n : ℕ) :
    arithmeticOperator x n = (arithmeticPhase n : ℂ) * x n := rfl

theorem sourceOperator_unitary : sourceOperator ∈ unitary (Space →L[ℂ] Space) :=
  paperBoundedDiagonal_unitary _ _ _ (fun n => Circle.norm_coe (phase n))

theorem arithmeticOperator_unitary : arithmeticOperator ∈ unitary (Space →L[ℂ] Space) :=
  paperBoundedDiagonal_unitary _ _ _ (fun n => Circle.norm_coe (arithmeticPhase n))

theorem sourceOperator_sub_arithmetic_compact :
    IsCompactOperator (sourceOperator - arithmeticOperator) := observable_sub_model_compact _

theorem norm_phase_discrepancy_le_two (n : ℕ) :
    ‖(phase n : ℂ) - arithmeticPhase n‖ ≤ 2 := by
  simpa only [Circle.norm_coe, one_add_one_eq_two] using
    norm_sub_le (phase n : ℂ) (arithmeticPhase n : ℂ)

def differencePrefix (N : ℕ) : Space →L[ℂ] Space :=
  diagonalOperator (truncMultiplier (fun n => (phase n : ℂ) - arithmeticPhase n) N)
    (norm_truncMultiplier_le norm_phase_discrepancy_le_two N)

theorem hasRankLE_differencePrefix (N : ℕ) : HasRankLE (differencePrefix N) N :=
  hasRankLE_diagonalOperator_trunc _ norm_phase_discrepancy_le_two N

theorem norm_difference_sub_prefix_le (N : ℕ) :
    ‖(sourceOperator - arithmeticOperator) - differencePrefix N‖ ≤ 18 / (N + 2 : ℝ) := by
  let tail : ℕ → ℂ := fun n => if n < N then 0 else (phase n : ℂ) - arithmeticPhase n
  have hb : ∀ n, ‖tail n‖ ≤ 18 / (N + 2 : ℝ) := by
    intro n
    dsimp [tail]
    split_ifs with hn
    · simp only [norm_zero]
      positivity
    · have hN : (N : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hn
      exact (phase_discrepancy_pointwise n).trans
        (div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith))
  have heq : (sourceOperator - arithmeticOperator) - differencePrefix N =
      diagonalOperator tail hb := by
    ext x n
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, sourceOperator_apply,
      arithmeticOperator_apply, differencePrefix, diagonalOperator_apply, truncMultiplier, tail]
    split_ifs <;> ring
  rw [heq]
  exact norm_diagonalOperator_le _ _

end RHTower.PaperLagCayley
