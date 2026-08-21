/-
# Continuous majorants of upper semicontinuous functions

The Lipschitz regularization from above, `g_n(x) = sup_y (f(y) - n·d(x,y))`, is `n`-Lipschitz, lies
above `f`, and decreases to `f` at every point at which `f` is upper semicontinuous: near `x` the
values of `f` are already below `f(x)+ε`, and far from `x` the penalty `n·d(x,y)` eventually beats
the global ceiling.  Dominated convergence then makes the integral of the majorant as close to the
integral of `f` as desired.

Main results:
* `lipMajorant`, `lipschitzWith_lipMajorant` — the regularization and its Lipschitz constant.
* `tendsto_lipMajorant` — it converges pointwise to an upper semicontinuous function.
* `exists_continuous_majorant` — **a continuous majorant with almost the same integral**.
-/
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open Filter MeasureTheory Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section Majorant

variable {X : Type*} [MetricSpace X] [Nonempty X] {f : X → ℝ} {M : ℝ}

/-- The Lipschitz regularization of a function from above. -/
def lipMajorant (f : X → ℝ) (n : ℕ) (x : X) : ℝ := ⨆ y : X, (f y - n * dist x y)

theorem bddAbove_lipMajorant_family (hM : ∀ y, f y ≤ M) (n : ℕ) (x : X) :
    BddAbove (Set.range fun y : X => f y - n * dist x y) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨y, rfl⟩
  have hnn : (0 : ℝ) ≤ (n : ℝ) * dist x y := by positivity
  linarith [hM y]

theorem le_lipMajorant (hM : ∀ y, f y ≤ M) (n : ℕ) (x : X) : f x ≤ lipMajorant f n x := by
  show f x ≤ ⨆ y : X, (f y - (n : ℝ) * dist x y)
  have h := le_ciSup (bddAbove_lipMajorant_family hM n x) x
  rw [dist_self, mul_zero, sub_zero] at h
  exact h

theorem lipMajorant_le (hM : ∀ y, f y ≤ M) (n : ℕ) (x : X) : lipMajorant f n x ≤ M := by
  show (⨆ y : X, (f y - (n : ℝ) * dist x y)) ≤ M
  refine ciSup_le fun y => ?_
  have hnn : (0 : ℝ) ≤ (n : ℝ) * dist x y := by positivity
  linarith [hM y]

theorem lipMajorant_le_add (hM : ∀ y, f y ≤ M) (n : ℕ) (x x' : X) :
    lipMajorant f n x ≤ lipMajorant f n x' + (n : ℝ) * dist x x' := by
  show (⨆ y : X, (f y - (n : ℝ) * dist x y)) ≤ _
  refine ciSup_le fun y => ?_
  have hbase : f y - (n : ℝ) * dist x' y ≤ lipMajorant f n x' :=
    le_ciSup (bddAbove_lipMajorant_family hM n x') y
  have htri : dist x' y ≤ dist x' x + dist x y := dist_triangle x' x y
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcomm : dist x' x = dist x x' := dist_comm x' x
  nlinarith [hbase, htri, hnn, hcomm]

theorem lipschitzWith_lipMajorant (hM : ∀ y, f y ≤ M) (n : ℕ) :
    LipschitzWith (n : NNReal) (lipMajorant f n) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  have h1 := lipMajorant_le_add hM n x x'
  have h2 := lipMajorant_le_add hM n x' x
  have hcomm : dist x' x = dist x x' := dist_comm x' x
  rw [Real.dist_eq, abs_le]
  constructor
  · have : (n : NNReal) = (n : ℝ) := by simp
    rw [this]
    nlinarith [h2, hcomm]
  · have : (n : NNReal) = (n : ℝ) := by simp
    rw [this]
    linarith [h1]

theorem continuous_lipMajorant (hM : ∀ y, f y ≤ M) (n : ℕ) :
    Continuous (lipMajorant f n) := (lipschitzWith_lipMajorant hM n).continuous

/-- **The regularization converges to an upper semicontinuous function.** -/
theorem tendsto_lipMajorant (hf : UpperSemicontinuous f) (hM : ∀ y, f y ≤ M) (x : X) :
    Tendsto (fun n : ℕ => lipMajorant f n x) atTop (𝓝 (f x)) := by
  refine Metric.tendsto_atTop.mpr fun eps heps => ?_
  obtain ⟨delta, hdelta, hball⟩ : ∃ delta > 0, ∀ y, dist x y < delta → f y < f x + eps / 2 := by
    have hev := hf x (f x + eps / 2) (by linarith)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨d, hd, hdd⟩ := hev
    exact ⟨d, hd, fun y hy => hdd (by rwa [dist_comm] at hy)⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (M - f x) / delta ≤ (N : ℝ) := exists_nat_ge _
  refine ⟨N, fun n hn => ?_⟩
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hupper : lipMajorant f n x ≤ f x + eps / 2 := by
    show (⨆ y : X, (f y - (n : ℝ) * dist x y)) ≤ _
    refine ciSup_le fun y => ?_
    by_cases hy : dist x y < delta
    · have hnn : (0 : ℝ) ≤ (n : ℝ) * dist x y := by positivity
      linarith [hball y hy]
    · have hyd : delta ≤ dist x y := le_of_not_gt hy
      have hnnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hpen : (M - f x) ≤ (n : ℝ) * dist x y := by
        have h1 : (M - f x) / delta * delta ≤ (n : ℝ) * dist x y := by
          refine mul_le_mul (le_trans hN hnN) hyd (le_of_lt hdelta) hnnn
        rwa [div_mul_cancel₀ _ (ne_of_gt hdelta)] at h1
      linarith [hM y]
  have hlower : f x ≤ lipMajorant f n x := le_lipMajorant hM n x
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-- **A continuous majorant with almost the same integral.** -/
theorem exists_continuous_majorant [MeasurableSpace X] [BorelSpace X]
    (hf : UpperSemicontinuous f) (h0 : ∀ x, 0 ≤ f x) (hM : ∀ x, f x ≤ M)
    (mu : Measure X) [IsFiniteMeasure mu] {eps : ℝ} (heps : 0 < eps) :
    ∃ g : X → ℝ, Continuous g ∧ (∀ x, f x ≤ g x) ∧ (∀ x, g x ≤ M) ∧
      ∫ x, g x ∂mu ≤ ∫ x, f x ∂mu + eps := by
  classical
  have hMnn : (0 : ℝ) ≤ M := le_trans (h0 (Classical.arbitrary X)) (hM _)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (lipMajorant f n) mu :=
    fun n => (continuous_lipMajorant hM n).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂mu, ‖lipMajorant f n x‖ ≤ M := by
    intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (h0 x) (le_lipMajorant hM n x))]
    exact lipMajorant_le hM n x
  have hptw : ∀ᵐ x ∂mu, Tendsto (fun n : ℕ => lipMajorant f n x) atTop (𝓝 (f x)) :=
    Filter.Eventually.of_forall (tendsto_lipMajorant hf hM)
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (bound := fun _ : X => M) hmeas (MeasureTheory.integrable_const M) hbound hptw
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hdct) eps heps
  refine ⟨lipMajorant f N, continuous_lipMajorant hM N, fun x => le_lipMajorant hM N x,
    fun x => lipMajorant_le hM N x, ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq] at h
  have habs := abs_lt.mp h
  linarith [habs.2]

end Majorant

end GaloisForLFunctions.HTGeometry

end
