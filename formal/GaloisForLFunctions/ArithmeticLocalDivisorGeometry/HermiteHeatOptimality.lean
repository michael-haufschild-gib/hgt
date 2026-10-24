import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteExtremizers
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteEdgeAsymptotics
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedPairHeatThreshold

/-!
# Optimal heat at fixed degree and root depth

The scaled Hermite family attains the least heat time among nonnegative polynomials of
fixed even degree with a prescribed positive root. Its edge limit makes four optimal in
the uniform root bound, and central masking costs asymptotically twice this least heat.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- Least possible heat time for degree `2m+4` and positive root depth `δ`. -/
def optimalRootHeat (m : ℕ) (δ : ℝ) : ℝ :=
  δ ^ 2 / (2 * hermiteEdge (2 * m + 2) ^ 2)

/-- Every admissible heat time pays the sharp root-depth cost, without a parity premise. -/
theorem optimalRootHeat_le_of_heat_cone {p : ℝ[X]} (m : ℕ) {δ s : ℝ}
    (hδ : 0 < δ) (hdeg : p.natDegree = 2 * m + 4)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) (hr : p.eval δ = 0)
    (hc : CoeffNonneg (forwardPolyHeat s p)) : optimalRootHeat m δ ≤ s := by
  have hpne : p ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at hdeg
    omega
  have hs : 0 < s := by
    by_contra hn
    have h0 := coeffNonneg_forwardPolyHeat_mono p (le_of_not_gt hn) hc
    rw [forwardPolyHeat_zero] at h0
    exact (eval_pos_of_coeffNonneg hpne h0 hδ).ne' hr
  have he : 0 < hermiteEdge (2 * m + 2) := hermiteEdge_pos (by omega)
  have hb := nonnegative_root_le_sqrt_mul_hermiteEdge (by positivity : 0 < 2 * s)
    hdeg hp (by simpa only [show 2 * s / 2 = s by ring] using hc) hr
  have hsq := mul_self_le_mul_self hδ.le hb
  simp only [← pow_two, mul_pow, Real.sq_sqrt (show 0 ≤ 2 * s by positivity)] at hsq
  rw [optimalRootHeat, div_le_iff₀ (by positivity : 0 < 2 * hermiteEdge (2 * m + 2) ^ 2)]
  nlinarith only [hsq]

/-- The optimum is attained by an even nonnegative polynomial with the prescribed root. -/
theorem optimalRootHeat_attained (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : ℝ[X], p.natDegree = 2 * m + 4 ∧
      (∀ x : ℝ, 0 ≤ p.eval x) ∧ (∀ x : ℝ, p.eval (-x) = p.eval x) ∧
      p.eval δ = 0 ∧
      ∀ s : ℝ, CoeffNonneg (forwardPolyHeat s p) ↔ optimalRootHeat m δ ≤ s := by
  have he : 0 < hermiteEdge (2 * m + 2) := hermiteEdge_pos (by omega)
  have hr : 0 < δ / hermiteEdge (2 * m + 2) := div_pos hδ he
  have hscale : δ / hermiteEdge (2 * m + 2) * hermiteEdge (2 * m + 2) = δ := by
    field_simp
  refine ⟨scaledHermiteExtremizer (δ / hermiteEdge (2 * m + 2)) m,
    scaledHermiteExtremizer_degree hr m, scaledHermiteExtremizer_nonneg hr m, ?_, ?_, ?_⟩
  · intro x
    simp only [scaledHermiteExtremizer, eval_mul, eval_C, eval_comp, eval_X, mul_neg,
      hermiteExtremizer_eval_neg]
  · apply (scaledHermiteExtremizer_eval_eq_zero_iff hr m δ).mpr
    exact Or.inl hscale.symm
  · intro s
    rw [coeffNonneg_heat_scaledHermiteExtremizer_iff hr, optimalRootHeat]
    congr 1
    ring

/-- The fixed-degree, fixed-root optimization has an attained minimum. -/
theorem isLeast_optimalRootHeat (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    IsLeast {s : ℝ | ∃ p : ℝ[X], p.natDegree = 2 * m + 4 ∧
      (∀ x : ℝ, 0 ≤ p.eval x) ∧ (∀ x : ℝ, p.eval (-x) = p.eval x) ∧
      p.eval δ = 0 ∧ CoeffNonneg (forwardPolyHeat s p)} (optimalRootHeat m δ) := by
  obtain ⟨p, hd, hp, he, hr, hc⟩ := optimalRootHeat_attained m hδ
  refine ⟨⟨p, hd, hp, he, hr, (hc _).mpr le_rfl⟩, ?_⟩
  rintro s ⟨q, hqd, hqp, _, hqr, hqc⟩
  exact optimalRootHeat_le_of_heat_cone m hδ hqd hqp hqr hqc

/-- No smaller constant than four bounds squared roots divided by Gaussian variance and degree. -/
theorem exists_hermiteExtremizer_violating_smaller_constant {C : ℝ} (hC : C < 4) :
    ∃ (p : ℝ[X]) (x : ℝ), 0 < x ∧
      (∀ y : ℝ, 0 ≤ p.eval y) ∧ (∀ y : ℝ, p.eval (-y) = p.eval y) ∧
      CoeffNonneg (forwardPolyHeat (1 / 2) p) ∧ p.eval x = 0 ∧
      C * p.natDegree < x ^ 2 := by
  obtain ⟨m, hm⟩ := (tendsto_even_hermiteEdge_sq_div_degree.eventually_const_lt hC).exists
  refine ⟨hermiteExtremizer m, hermiteEdge (2 * m + 2), hermiteEdge_pos (by omega),
    hermiteExtremizer_nonneg m, hermiteExtremizer_eval_neg m,
    coeffNonneg_heat_hermiteExtremizer m, hermiteExtremizer_eval_edge m, ?_⟩
  rw [hermiteExtremizer_degree]
  have h := (lt_div_iff₀ (by positivity : 0 < (2 * m + 4 : ℝ))).mp hm
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

/-- The centrally masked model costs twice the optimal heat budget asymptotically. -/
theorem tendsto_maskedPairHeatThreshold_over_optimal :
    Tendsto (fun m : ℕ => 2 * hermiteEdge (2 * m + 2) ^ 2 * maskedPairHeatThreshold m)
      atTop (𝓝 2) := by
  have hbase := tendsto_natCast_div_add_atTop (2 : ℝ)
  have h := (tendsto_even_hermiteEdge_sq_div_degree.mul
    (tendsto_maskedPairHeatThreshold.div hbase (by norm_num))).div_const 2
  norm_num only [one_div_one, mul_one, show (4 : ℝ) / 2 = 2 by norm_num] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hplus : (m : ℝ) + 2 ≠ 0 := by positivity
  have hdeg : (2 * m + 4 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- At every fixed positive depth the ratio of the two exact first heat times tends to two. -/
theorem tendsto_centralMasking_heat_ratio {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun m : ℕ => (δ ^ 2 * maskedPairHeatThreshold m) / optimalRootHeat m δ)
      atTop (𝓝 2) := by
  apply tendsto_maskedPairHeatThreshold_over_optimal.congr
  intro m
  have he : hermiteEdge (2 * m + 2) ≠ 0 := (hermiteEdge_pos (by omega)).ne'
  unfold optimalRootHeat
  field_simp

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
