import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Volume packing forces a close pair

Finitely many points of a ball whose mutual distances are all at least `δ` carry disjoint open
balls of radius `δ/2` inside a slightly larger ball, so their number is bounded by the ratio of
volumes.  Reading the bound backwards, a set of `N` points of the ball of radius `ρ` always has two
distinct points at distance at most `2ρ/(N^{1/d}-1)`, where `d` is the dimension.

This is the deterministic observer-compression mechanism: exponentially many observed vectors in a
bounded region of a low-dimensional observer space must crowd.
-/

open MeasureTheory Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]

/-- **Volume packing bound.**  A `δ`-separated finite subset of the ball of radius `ρ` has at most
`((ρ + δ/2)/(δ/2))^d` elements. -/
theorem card_mul_pow_le_of_separated (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Finset E) (ρ δ : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hball : ∀ x ∈ S, ‖x‖ ≤ ρ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ ‖x - y‖) :
    (S.card : ℝ) * (δ / 2) ^ (Module.finrank ℝ E) ≤ (ρ + δ / 2) ^ (Module.finrank ℝ E) := by
  classical
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hdisj : (↑S : Set E).PairwiseDisjoint fun x => ball x (δ / 2) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    have h1 : dist x z < δ / 2 := by
      rw [dist_comm]
      exact mem_ball.mp hz
    have h2 : dist z y < δ / 2 := mem_ball.mp hz'
    have h3 : dist x y < δ := by
      have := dist_triangle x z y
      linarith
    have h4 := hsep x hx y hy hxy
    rw [← dist_eq_norm] at h4
    linarith
  have hsub : (⋃ x ∈ S, ball x (δ / 2)) ⊆ ball 0 (ρ + δ / 2) := by
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨x, hx, hzx⟩ := hz
    rw [mem_ball, dist_zero_right]
    have h1 : ‖z - x‖ < δ / 2 := by
      rw [← dist_eq_norm]
      exact mem_ball.mp hzx
    have h2 : ‖x‖ ≤ ρ := hball x hx
    calc ‖z‖ = ‖(z - x) + x‖ := by ring_nf
      _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
      _ < δ / 2 + ρ := by linarith
      _ = ρ + δ / 2 := by ring
  have hmeas := measure_biUnion_finset (μ := μ) hdisj
    (fun b _ => measurableSet_ball)
  have hle : ∑ x ∈ S, μ (ball x (δ / 2)) ≤ μ (ball 0 (ρ + δ / 2)) := by
    rw [← hmeas]
    exact measure_mono hsub
  have hballval : ∀ x : E, μ (ball x (δ / 2)) =
      ENNReal.ofReal ((δ / 2) ^ (Module.finrank ℝ E)) * μ (ball 0 1) :=
    fun x => Measure.addHaar_ball μ x hhalf.le
  rw [Finset.sum_congr rfl fun x _ => hballval x, Finset.sum_const, nsmul_eq_mul,
    Measure.addHaar_ball μ (0 : E) (by linarith : (0:ℝ) ≤ ρ + δ / 2), ← mul_assoc] at hle
  have hpos : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hfin : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hcancel := (ENNReal.mul_le_mul_right hpos hfin).mp hle
  have hcast : ((S.card : ℝ≥0∞)) * ENNReal.ofReal ((δ / 2) ^ (Module.finrank ℝ E)) =
      ENNReal.ofReal ((S.card : ℝ) * (δ / 2) ^ (Module.finrank ℝ E)) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp
  rw [hcast] at hcancel
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcancel

/-- **Deterministic observer compression.**  Any finite set of more than one point inside the ball
of radius `ρ` has two distinct points whose distance is at most `2ρ/(N^{1/d}-1)`, in the
division-free form. -/
theorem exists_pair_norm_sub_mul_le (μ : Measure E) [μ.IsAddHaarMeasure]
    (S : Finset E) (ρ : ℝ) (hρ : 0 ≤ ρ) (hcard : 1 < S.card)
    (hball : ∀ x ∈ S, ‖x‖ ≤ ρ) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧
      ((S.card : ℝ) ^ ((Module.finrank ℝ E : ℝ)⁻¹) - 1) * ‖x - y‖ ≤ 2 * ρ := by
  classical
  set d := Module.finrank ℝ E with hd
  have hdpos : 0 < d := Module.finrank_pos
  set T := (S ×ˢ S).filter fun z : E × E => z.1 ≠ z.2 with hT
  have hTne : T.Nonempty := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard
    exact ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩⟩
  obtain ⟨z, hzT, hzmin⟩ := T.exists_min_image (fun w : E × E => ‖w.1 - w.2‖) hTne
  rw [hT, Finset.mem_filter, Finset.mem_product] at hzT
  set δ := ‖z.1 - z.2‖ with hδ
  have hδpos : 0 < δ := by
    rw [hδ, norm_pos_iff, sub_ne_zero]
    exact hzT.2
  have hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ ‖x - y‖ := by
    intro x hx y hy hxy
    exact hzmin (x, y) (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩)
  have hpack := card_mul_pow_le_of_separated μ S ρ δ hρ hδpos hball hsep
  have hroot : ((S.card : ℝ) ^ ((d : ℝ)⁻¹)) ^ d = (S.card : ℝ) := by
    rw [← Real.rpow_natCast ((S.card : ℝ) ^ ((d : ℝ)⁻¹)) d, ← Real.rpow_mul (by positivity),
      inv_mul_cancel₀ (by exact_mod_cast hdpos.ne'), Real.rpow_one]
  have hkey : (((S.card : ℝ) ^ ((d : ℝ)⁻¹)) * (δ / 2)) ^ d ≤ (ρ + δ / 2) ^ d := by
    rw [mul_pow, hroot]
    exact hpack
  have hrootpos : (0 : ℝ) ≤ (S.card : ℝ) ^ ((d : ℝ)⁻¹) := Real.rpow_nonneg (by positivity) _
  have hlin : ((S.card : ℝ) ^ ((d : ℝ)⁻¹)) * (δ / 2) ≤ ρ + δ / 2 := by
    refine le_of_pow_le_pow_left₀ hdpos.ne' (by linarith) hkey
  exact ⟨z.1, hzT.1.1, z.2, hzT.1.2, hzT.2, by nlinarith [hlin]⟩

end GaloisForLFunctions.HTGeometry
