import GaloisForLFunctions.RHTower.PaperLagCayleyQuotient

/-! # Exact Green reconstruction and the boundary charge lost by the quotient

Inverse Cayley recovers the entire native lag with its original affine charges.
A single changed normalized-curvature coordinate leaves every continuous phase
observation unchanged modulo finite rank, but changes the reconstructed lag at
square-root scale. The compensating affine charge is identified exactly.
-/

noncomputable section

open Filter
open scoped Topology

namespace RHTower.PaperLagCayley

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerLagCurvature

def affineBase : ℝ := Real.sqrt 3 * integerLag 3

def affineSlope : ℝ := Real.sqrt 3 * integerLag 3 - Real.sqrt 2 * integerLag 2

def greenFromPhases (q : ℕ → Circle) (N : ℕ) : ℝ :=
  affineBase + N * affineSlope + ∑ n ∈ Finset.range N,
    ((N : ℝ) - n) * (paperRealCayleyInverse (q n) / (n + 3 : ℝ))

def lagFromPhases (q : ℕ → Circle) (N : ℕ) : ℝ :=
  greenFromPhases q N / Real.sqrt (N + 3 : ℝ)

theorem greenFromPhases_source (N : ℕ) :
    greenFromPhases phase N = Real.sqrt (N + 3 : ℝ) * integerLag (N + 3) := by
  have h := scaledCurvature_green_eq N
  simp only [Nat.cast_add, Nat.cast_ofNat] at h
  simp only [greenFromPhases, curvature_from_phase, affineBase, affineSlope]
  linarith

theorem lagFromPhases_source (N : ℕ) : lagFromPhases phase N = integerLag (N + 3) := by
  rw [lagFromPhases, greenFromPhases_source]
  have hs : Real.sqrt (N + 3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  field_simp

def perturbedSource (δ : ℝ) (n : ℕ) : ℝ := source n + if n = 0 then δ else 0

def perturbedPhase (δ : ℝ) (n : ℕ) : Circle := circleCayley (perturbedSource δ n)

theorem perturbedPhase_inverse (δ : ℝ) (n : ℕ) :
    paperRealCayleyInverse (perturbedPhase δ n) = perturbedSource δ n :=
  paperRealCayleyInverse_apply _

theorem perturbedPhase_ne_zero_index (δ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    perturbedPhase δ n = phase n := by
  simp only [perturbedPhase, perturbedSource, if_neg hn, add_zero, phase]

def perturbedObservable (δ : ℝ) (f : C(Circle, ℂ)) : Space →L[ℂ] Space :=
  lpDiagonalCLM (fun n => f (perturbedPhase δ n)) (norm_nonneg f)
    (fun _ => f.norm_coe_le_norm _)

theorem hasRankLE_perturbedObservable_sub (δ : ℝ) (f : C(Circle, ℂ)) :
    HasRankLE (perturbedObservable δ f - observable f) 1 := by
  let v : ℕ → ℂ := fun n => f (perturbedPhase δ n) - f (phase n)
  have hb : ∀ n, ‖v n‖ ≤ 2 * ‖f‖ := by
    intro n
    have h₁ := f.norm_coe_le_norm (perturbedPhase δ n)
    have h₂ := f.norm_coe_le_norm (phase n)
    exact (norm_sub_le _ _).trans (by linarith)
  have heq : perturbedObservable δ f - observable f =
      diagonalOperator (truncMultiplier v 1) (norm_truncMultiplier_le hb 1) := by
    ext x n
    change f (perturbedPhase δ n) * x n - f (phase n) * x n =
      (if n < 1 then v n else 0) * x n
    by_cases hn : n = 0
    · subst n
      simp only [Nat.zero_lt_one, if_pos, v]
      ring
    · rw [if_neg (by omega), perturbedPhase_ne_zero_index δ hn]
      ring
  rw [heq]
  exact hasRankLE_diagonalOperator_trunc _ hb 1

theorem perturbedObservable_sub_compact (δ : ℝ) (f : C(Circle, ℂ)) :
    IsCompactOperator (perturbedObservable δ f - observable f) :=
  isCompactOperator_of_hasRankLE (hasRankLE_perturbedObservable_sub δ f)

theorem perturbedObservable_compactIdealDistance (δ : ℝ) (f : C(Circle, ℂ)) :
    compactIdealDistance (perturbedObservable δ f) = ‖modelObservable f‖ := by
  calc
    _ = compactIdealDistance (observable f + (perturbedObservable δ f - observable f)) := by
      congr 1
      abel
    _ = compactIdealDistance (observable f) :=
      paperCompactIdealDistance_add_compact _ ⟨_, perturbedObservable_sub_compact δ f⟩
    _ = _ := observable_compactIdealDistance f

theorem perturbedObservable_ideal_cost (δ : ℝ) (f : C(Circle, ℂ)) :
    compactOperatorTraceCost Space (perturbedObservable δ f) =
      compactOperatorTraceCost Space (observable f) := by
  calc
    _ = compactOperatorTraceCost Space
        (observable f + (perturbedObservable δ f - observable f)) := by
      congr 1
      abel
    _ = _ := compactOperatorTraceCost_add_compact _ ⟨_, perturbedObservable_sub_compact δ f⟩

theorem perturbedSourceOperator_unitary (δ : ℝ) :
    perturbedObservable δ circleCoordinate ∈ unitary (Space →L[ℂ] Space) :=
  paperBoundedDiagonal_unitary _ _ _ (fun n => Circle.norm_coe (perturbedPhase δ n))

theorem green_zero_coordinate (δ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((N : ℝ) - n) *
      ((if n = 0 then δ else 0) / (n + 3 : ℝ))) = δ * N / 3 := by
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.cast_zero, sub_zero, ite_true, zero_add]
    ring
  · intro n _ hn
    simp only [if_neg hn, zero_div, mul_zero]
  · intro h
    have hN : N = 0 := by simpa using h
    subst N
    simp

theorem greenFromPhases_perturbed (δ : ℝ) (N : ℕ) :
    greenFromPhases (perturbedPhase δ) N = greenFromPhases phase N + δ * N / 3 := by
  have heq : (∑ n ∈ Finset.range N, ((N : ℝ) - n) *
      (paperRealCayleyInverse (perturbedPhase δ n) / (n + 3 : ℝ))) =
      (∑ n ∈ Finset.range N, ((N : ℝ) - n) *
        (paperRealCayleyInverse (phase n) / (n + 3 : ℝ))) + δ * N / 3 := by
    simp only [perturbedPhase_inverse, perturbedSource, source_from_phase,
      add_div, mul_add, Finset.sum_add_distrib, green_zero_coordinate]
  simp only [greenFromPhases]
  rw [heq]
  ring

theorem lagFromPhases_perturbed (δ : ℝ) (N : ℕ) :
    lagFromPhases (perturbedPhase δ) N - integerLag (N + 3) =
      δ * N / (3 * Real.sqrt (N + 3 : ℝ)) := by
  rw [lagFromPhases, greenFromPhases_perturbed, add_div]
  change lagFromPhases phase N + _ - _ = _
  rw [lagFromPhases_source]
  ring

/-- Exact positive survivor: changing the affine slope by `-δ/3` repairs the entire lag. -/
theorem greenFromPhases_affine_compensation (δ : ℝ) (N : ℕ) :
    greenFromPhases (perturbedPhase δ) N - N * (δ / 3) =
      Real.sqrt (N + 3 : ℝ) * integerLag (N + 3) := by
  rw [greenFromPhases_perturbed, greenFromPhases_source]
  ring

theorem lag_perturbation_sqrt_ratio (δ : ℝ) (N : ℕ) :
    (lagFromPhases (perturbedPhase δ) N - integerLag (N + 3)) /
      Real.sqrt (N + 3 : ℝ) = δ / 3 * (1 - 3 / (N + 3 : ℝ)) := by
  rw [lagFromPhases_perturbed, div_div, mul_assoc, Real.mul_self_sqrt (by positivity)]
  field_simp
  ring

/-- The lag change has the sharp square-root-scale leading coefficient `δ/3`. -/
theorem tendsto_lag_perturbation_sqrt_ratio (δ : ℝ) :
    Tendsto (fun N => (lagFromPhases (perturbedPhase δ) N - integerLag (N + 3)) /
      Real.sqrt (N + 3 : ℝ)) atTop (𝓝 (δ / 3)) := by
  simp_rw [lag_perturbation_sqrt_ratio]
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 3) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  simpa using (tendsto_const_nhds.mul (tendsto_const_nhds.sub (hN.const_div_atTop 3)) :
    Tendsto (fun N : ℕ => δ / 3 * (1 - 3 / (N + 3 : ℝ))) atTop (𝓝 (δ / 3 * (1 - 0))))

theorem lag_perturbation_abs_lower (δ : ℝ) (N : ℕ) (hN : 3 ≤ N) :
    |δ| / 6 * Real.sqrt (N + 3 : ℝ) ≤
      |lagFromPhases (perturbedPhase δ) N - integerLag (N + 3)| := by
  rw [lagFromPhases_perturbed]
  simp only [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N),
    abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (le_div_iff₀ (by positivity)).2
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ N + 3)
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have heq : (|δ| / 6 * Real.sqrt (N + 3 : ℝ)) * (3 * Real.sqrt (N + 3 : ℝ)) =
      |δ| * (N + 3 : ℝ) / 2 := by
    calc
      _ = |δ| * (Real.sqrt (N + 3 : ℝ)) ^ 2 / 2 := by ring
      _ = _ := by rw [hs]
  rw [heq]
  nlinarith [mul_nonneg (abs_nonneg δ) (sub_nonneg.2 hn)]

/-- Every nonzero one-coordinate change gives an unbounded reconstructed-lag change. -/
theorem tendsto_abs_lag_perturbation (δ : ℝ) :
    Tendsto (fun N => |lagFromPhases (perturbedPhase δ) N - integerLag (N + 3)|)
      atTop (if δ = 0 then 𝓝 0 else atTop) := by
  by_cases hδ : δ = 0
  · subst δ
    simp only [lagFromPhases_perturbed, zero_mul, zero_div, abs_zero]
    exact tendsto_const_nhds
  · rw [if_neg hδ]
    have hN : Tendsto (fun N : ℕ => (N : ℝ) + 3) atTop atTop :=
      tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
    have hg := (Real.tendsto_sqrt_atTop.comp hN).const_mul_atTop
      (show 0 < |δ| / 6 by exact div_pos (abs_pos.2 hδ) (by norm_num))
    apply tendsto_atTop.2
    intro b
    filter_upwards [hg.eventually (eventually_ge_atTop b), eventually_ge_atTop (3 : ℕ)] with N hb hN
    exact hb.trans (lag_perturbation_abs_lower δ N hN)

end RHTower.PaperLagCayley
