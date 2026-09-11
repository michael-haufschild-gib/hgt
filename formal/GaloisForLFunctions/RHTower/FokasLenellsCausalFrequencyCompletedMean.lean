import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyHilbertAmplitude
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyHilbertMean
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAbsoluteSynthesis
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Module
open Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

private theorem norm_square_gap_bound
    {H : Type*} [NormedAddCommGroup H] (x y : H) :
    |‖x‖ ^ 2 - ‖y‖ ^ 2| ≤ (‖x‖ + ‖y‖) * ‖x - y‖ := by
  have he : ‖x‖ ^ 2 - ‖y‖ ^ 2 = (‖x‖ + ‖y‖) * (‖x‖ - ‖y‖) := by ring
  rw [he, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem absolute_real_cesaro_bound (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ n, |f n| ≤ C) (N : ℕ) :
    |(N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f n| ≤ C := by
  by_cases hN : N = 0
  · subst N
    simpa using hC
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hi : 0 ≤ (N : ℝ)⁻¹ := by positivity
  calc
    _ = (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, f n‖ := by
      rw [abs_mul, abs_of_nonneg hi, Real.norm_eq_abs]
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖f n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hi
    _ ≤ (N : ℝ)⁻¹ * ∑ _n ∈ Finset.range N, C := by
      apply mul_le_mul_of_nonneg_left _ hi
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Real.norm_eq_abs] using hf n
    _ = C := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hn, one_mul]

section QuadraticObservation
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

private def quadraticCesaro (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H) (N : ℕ) (u : E) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖J ((T ^ n) u)‖ ^ 2

private theorem observed_square_gap_bound (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H)
    (n : ℕ) (u v : E) :
    |‖J ((T ^ n) u)‖ ^ 2 - ‖J ((T ^ n) v)‖ ^ 2| ≤
      ‖J‖ ^ 2 * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hb (w : E) : ‖J ((T ^ n) w)‖ ≤ ‖J‖ * ‖w‖ := by
    simpa only [(T ^ n).norm_map] using J.le_opNorm ((T ^ n) w)
  have hd : ‖J ((T ^ n) u) - J ((T ^ n) v)‖ ≤ ‖J‖ * ‖u - v‖ := by
    rw [← map_sub, ← map_sub]
    exact hb (u - v)
  calc
    _ ≤ (‖J ((T ^ n) u)‖ + ‖J ((T ^ n) v)‖) *
        ‖J ((T ^ n) u) - J ((T ^ n) v)‖ := norm_square_gap_bound _ _
    _ ≤ (‖J‖ * ‖u‖ + ‖J‖ * ‖v‖) * (‖J‖ * ‖u - v‖) :=
      mul_le_mul (add_le_add (hb u) (hb v)) hd (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem quadraticCesaro_gap_bound (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H)
    (N : ℕ) (u v : E) :
    |quadraticCesaro T J N u - quadraticCesaro T J N v| ≤
      ‖J‖ ^ 2 * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have he : quadraticCesaro T J N u - quadraticCesaro T J N v =
      (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        (‖J ((T ^ n) u)‖ ^ 2 - ‖J ((T ^ n) v)‖ ^ 2) := by
    simp only [quadraticCesaro, Finset.sum_sub_distrib, mul_sub]
  rw [he]
  exact absolute_real_cesaro_bound _ _ (by positivity)
    (fun n => observed_square_gap_bound T J n u v) N
end QuadraticObservation

private theorem finite_synthesis_dense
    {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (v : I → E) (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hS : DenseRange S) (hsum : ∀ c, HasSum (fun i => c i • v i) (S c)) :
    DenseRange (Finsupp.linearCombination ℂ v) := by
  classical
  let D : Set E := Set.range (Finsupp.linearCombination ℂ v)
  have hsub : Set.range S ⊆ closure D := by
    rintro _ ⟨c, rfl⟩
    apply mem_closure_of_tendsto (hsum c)
    apply Filter.Eventually.of_forall
    intro s
    refine ⟨∑ i ∈ s, Finsupp.single i (c i), ?_⟩
    simp only [map_sum, Finsupp.linearCombination_single]
  have hclosure := closure_minimal hsub isClosed_closure
  rw [hS.closure_range] at hclosure
  intro u
  exact hclosure (Set.mem_univ u)

private theorem quadratic_limit_from_dense
    {D E : Type*} [NormedAddCommGroup E]
    (e : D → E) (he : DenseRange e) (F : ℕ → E → ℝ) (G : E → ℝ)
    (hG : Continuous G) (K : ℝ) (hK : 0 ≤ K)
    (hF : ∀ N u v, |F N u - F N v| ≤ K * (‖u‖ + ‖v‖) * dist u v)
    (hc : ∀ d, Tendsto (fun N => F N (e d)) atTop (𝓝 (G (e d))))
    (u : E) : Tendsto (fun N => F N u) atTop (𝓝 (G u)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he3 : 0 < ε / 3 := by positivity
  obtain ⟨δ, hδ, hGδ⟩ := Metric.continuousAt_iff.1 hG.continuousAt (ε / 3) he3
  let R : ℝ := K * (2 * ‖u‖ + 1)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let η : ℝ := min 1 (min δ (ε / (3 * (R + 1))))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨d, hd⟩ := he.exists_dist_lt u hη
  have hv1 : dist u (e d) < 1 := hd.trans_le (min_le_left _ _)
  have hvδ : dist u (e d) < δ :=
    hd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hvε : dist u (e d) < ε / (3 * (R + 1)) :=
    hd.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hvnorm : ‖e d‖ ≤ ‖u‖ + 1 := by
    have ht := dist_triangle (e d) u 0
    rw [dist_zero_right, dist_zero_right, dist_comm (e d) u] at ht
    linarith
  have hFsmall (N : ℕ) : |F N u - F N (e d)| < ε / 3 := by
    have hb : |F N u - F N (e d)| ≤ R * dist u (e d) := by
      apply (hF N u (e d)).trans
      apply mul_le_mul_of_nonneg_right _ dist_nonneg
      exact mul_le_mul_of_nonneg_left (by linarith : ‖u‖ + ‖e d‖ ≤ 2 * ‖u‖ + 1) hK
    have hp := (lt_div_iff₀ (by positivity : 0 < 3 * (R + 1))).1 hvε
    have hl : R * dist u (e d) < ε / 3 := by nlinarith [(dist_nonneg : 0 ≤ dist u (e d))]
    exact hb.trans_lt hl
  have hGsmall : dist (G (e d)) (G u) < ε / 3 := by
    apply hGδ
    rw [dist_comm]
    exact hvδ
  have hevent := Metric.tendsto_nhds.1 (hc d) (ε / 3) he3
  filter_upwards [hevent] with N hN
  have hFN : dist (F N u) (F N (e d)) < ε / 3 := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using hFsmall N
  have ht := dist_triangle (F N u) (F N (e d)) (G u)
  have ht' := dist_triangle (F N (e d)) (G (e d)) (G u)
  linarith

private theorem completed_quadratic_mean
    {I E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : E ≃ₗᵢ[ℂ] E) (J : E →L[ℂ] H)
    (v : I → E) (S : lp (fun _ : I => ℂ) 1 →L[ℂ] E)
    (hS : DenseRange S) (hsum : ∀ c, HasSum (fun i => c i • v i) (S c))
    (W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hW : ∀ (s : Finset I) (c : I → ℂ),
      ‖W (∑ i ∈ s, c i • v i)‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 * ‖J (v i)‖ ^ 2)
    (hm : ∀ (s : Finset I) (c : I → ℂ),
      Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
        ‖J ((T ^ n) (∑ i ∈ s, c i • v i))‖ ^ 2) atTop
        (𝓝 (∑ i ∈ s, ‖c i‖ ^ 2 * ‖J (v i)‖ ^ 2)))
    (u : E) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J ((T ^ n) u)‖ ^ 2) atTop (𝓝 (‖W u‖ ^ 2)) := by
  classical
  apply quadratic_limit_from_dense (Finsupp.linearCombination ℂ v)
    (finite_synthesis_dense v S hS hsum) (quadraticCesaro T J) (fun w => ‖W w‖ ^ 2)
    (by fun_prop) (‖J‖ ^ 2) (sq_nonneg ‖J‖)
  · intro N x y
    simpa only [dist_eq_norm] using quadraticCesaro_gap_bound T J N x y
  · intro c
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, hW, quadraticCesaro] using
      hm c.support c

/-- Finite actual mode combinations are dense in the full frequency space. -/
theorem causalFrequencyMode_finite_synthesis_dense (b : ℝ) :
    DenseRange (Finsupp.linearCombination ℂ (causalFrequencyMode b)) :=
  finite_synthesis_dense (causalFrequencyMode b) (causalFrequencyAbsoluteSynthesis b)
    (causalFrequencyAbsoluteSynthesis_denseRange b) (causalFrequencyAbsoluteSynthesis_hasSum b)

/-- The Hilbert-valued mean-square law extends from finite packets to every
vector in the actual completed frequency space. Its limit is the weighted
amplitude norm, with no absolute-summability or regularity premise. -/
theorem causalFrequencyShift_completed_hilbert_square_mean
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J (((causalFrequencyShift b) ^ n) u)‖ ^ 2) atTop
      (𝓝 (‖causalFrequencyObservedAmplitude b J u‖ ^ 2)) :=
  completed_quadratic_mean (causalFrequencyShift b) J (causalFrequencyMode b)
    (causalFrequencyAbsoluteSynthesis b) (causalFrequencyAbsoluteSynthesis_denseRange b)
    (causalFrequencyAbsoluteSynthesis_hasSum b) (causalFrequencyObservedAmplitude b J)
    (causalFrequencyObservedAmplitude_packet_square_norm b J)
    (causalFrequencyShift_hilbert_square_mean b J) u

/-- Every bounded Hilbert observation has an exact convergent spectral formula
for its time-averaged energy on the completed frequency space. -/
theorem causalFrequencyShift_completed_hilbert_parseval
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : ℝ) (J : causalFrequencySpace b →L[ℂ] H) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖J (((causalFrequencyShift b) ^ n) u)‖ ^ 2) atTop
      (𝓝 (∑' ω : ℝ, ‖causalFrequencyCoefficient b ω u‖ ^ 2 *
        ‖J (causalFrequencyMode b ω)‖ ^ 2)) := by
  simpa only [causalFrequencyObservedAmplitude_square_norm] using
    causalFrequencyShift_completed_hilbert_square_mean b J u

private theorem observed_map_eq_of_unit_weights
    {I E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (v : I → E) (J : E →L[ℂ] H) (A W : E →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hW : ∀ u i, W u i = (‖J (v i)‖ : ℂ) * A u i)
    (hJ : ∀ i, ‖J (v i)‖ = 1) : W = A := by
  apply ContinuousLinearMap.ext
  intro u
  apply lp.ext
  funext i
  rw [hW, hJ, Complex.ofReal_one, one_mul]

/-- Every derivative-coordinate observer assigns unit weight to each actual
mode, so its observed amplitude map is the canonical amplitude map. -/
theorem causalFrequencyObservedAmplitude_coordinate (b : ℝ) (j : ℕ) :
    causalFrequencyObservedAmplitude b
      ((causalBoundedChainCoordinate j).comp (causalFrequencySpace b).subtypeL) =
      causalFrequencyAmplitudeMap b :=
  observed_map_eq_of_unit_weights (causalFrequencyMode b)
    ((causalBoundedChainCoordinate j).comp (causalFrequencySpace b).subtypeL)
    (causalFrequencyAmplitudeMap b)
    (causalFrequencyObservedAmplitude b
      ((causalBoundedChainCoordinate j).comp (causalFrequencySpace b).subtypeL))
    (causalFrequencyObservedAmplitude_apply b _)
    (fun ω => causalBoundedUnitEigenchain_coordinate_norm b ω j)

/-- Every derivative-coordinate observation has the same long-run energy:
the square of the canonical amplitude norm. This holds throughout completion. -/
theorem causalFrequencyShift_completed_coordinate_square_mean
    (b : ℝ) (j : ℕ) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖causalBoundedChainCoordinate j ((((causalFrequencyShift b) ^ n) u).val)‖ ^ 2)
      atTop (𝓝 (‖causalFrequencyAmplitudeMap b u‖ ^ 2)) := by
  have hm := causalFrequencyShift_completed_hilbert_square_mean b
    ((causalBoundedChainCoordinate j).comp (causalFrequencySpace b).subtypeL) u
  simpa only [causalFrequencyObservedAmplitude_coordinate, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] using hm

/-- A completed vector has zero mean energy in any derivative coordinate
exactly when the vector itself vanishes. -/
theorem causalFrequencyShift_completed_coordinate_mean_zero_iff
    (b : ℝ) (j : ℕ) (u : causalFrequencySpace b) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
      ‖causalBoundedChainCoordinate j ((((causalFrequencyShift b) ^ n) u).val)‖ ^ 2)
      atTop (𝓝 0) ↔ u = 0 := by
  constructor
  · intro h
    have he := tendsto_nhds_unique
      (causalFrequencyShift_completed_coordinate_square_mean b j u) h
    have hz : causalFrequencyAmplitudeMap b u = 0 := by
      have hn : ‖causalFrequencyAmplitudeMap b u‖ = 0 := by nlinarith [norm_nonneg (causalFrequencyAmplitudeMap b u)]
      exact norm_eq_zero.1 hn
    apply causalFrequencyAmplitudeMap_injective b
    simpa only [map_zero] using hz
  · rintro rfl
    simpa only [map_zero, ZeroMemClass.coe_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end RHTower.FokasLenells
