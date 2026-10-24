import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteExtremizers
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HermiteEdgeAsymptotics
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.EvenPolynomialHeatCone
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.MaskedPairHeatThreshold

/-!
# Optimal heat at fixed degree and root depth

Scaled Hermite extremizers minimize the first heat time among even nonnegative polynomials
of fixed degree and positive root. The sharp degree constant is four; central masking costs
asymptotically twice the optimal heat.
-/

open Polynomial Filter Topology Set
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- The exact lower heat budget depends on the largest derivative zero, not merely degree. -/
theorem hermite_heat_time_lower_bound {p : ℝ[X]} (m : ℕ) {a s : ℝ} (ha : 0 < a)
    (hdeg : p.natDegree = 2 * m + 4) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hz : p.eval (Real.sqrt a) = 0) (hc : CoeffNonneg (forwardPolyHeat s p)) :
    a / (2 * hermiteEdge (2 * m + 2) ^ 2) ≤ s := by
  have hp0 : p ≠ 0 := by intro he; rw [he, natDegree_zero] at hdeg; omega
  have hs := heat_time_pos_of_positive_root hp0 (Real.sqrt_pos.mpr ha) hz hc
  have htime : 2 * s / 2 = s := by ring
  have hb := nonnegative_root_le_sqrt_mul_hermiteEdge (n := 2 * m + 2)
    (by positivity : 0 < 2 * s) hdeg hp (by simpa only [htime] using hc) hz
  have he : 0 < hermiteEdge (2 * m + 2) := hermiteEdge_pos (by omega)
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg a) hb
  have hsq' : a ≤ (2 * s) * hermiteEdge (2 * m + 2) ^ 2 := by
    simpa only [← pow_two, mul_pow, Real.sq_sqrt ha.le,
      Real.sq_sqrt (show 0 ≤ 2 * s by positivity)] using hsq
  apply (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos he))).mpr
  nlinarith only [hsq']

/-- Each polynomial in the fixed-depth even class has an attained positive first heat time. -/
theorem fixed_depth_first_heat_time {p : ℝ[X]} (m : ℕ) {a : ℝ} (ha : 0 < a)
    (hdeg : p.natDegree = 2 * m + 4) (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (heven : ∀ x : ℝ, p.eval (-x) = p.eval x) (hz : p.eval (Real.sqrt a) = 0) :
    ∃ tau : ℝ, 0 < tau ∧
      a / (2 * hermiteEdge (2 * m + 2) ^ 2) ≤ tau ∧
      ∀ s : ℝ, CoeffNonneg (forwardPolyHeat s p) ↔ tau ≤ s := by
  have hp0 : p ≠ 0 := by intro he; rw [he, natDegree_zero] at hdeg; omega
  obtain ⟨tau, htau, hcone⟩ := exists_first_heat_time_of_even_nonnegative_root hp0
    (show p.natDegree = 2 * (m + 2) by omega) hp heven (Real.sqrt_pos.mpr ha) hz
  exact ⟨tau, htau, hermite_heat_time_lower_bound m ha hdeg hp hz ((hcone tau).mpr le_rfl), hcone⟩

/-- The lower bound is attained by an explicit monic scaled Hermite polynomial. -/
theorem isLeast_fixed_depth_heat (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IsLeast {s : ℝ | ∃ p : ℝ[X], p.natDegree = 2 * m + 4 ∧
      (∀ x : ℝ, 0 ≤ p.eval x) ∧ (∀ x : ℝ, p.eval (-x) = p.eval x) ∧
      p.eval (Real.sqrt a) = 0 ∧ CoeffNonneg (forwardPolyHeat s p)}
      (a / (2 * hermiteEdge (2 * m + 2) ^ 2)) := by
  have he : 0 < hermiteEdge (2 * m + 2) := hermiteEdge_pos (by omega)
  let r := Real.sqrt a / hermiteEdge (2 * m + 2)
  have hr : 0 < r := div_pos (Real.sqrt_pos.mpr ha) he
  have hroot : r * hermiteEdge (2 * m + 2) = Real.sqrt a := by
    dsimp only [r]
    field_simp
  have htime : r ^ 2 / 2 = a / (2 * hermiteEdge (2 * m + 2) ^ 2) := by
    dsimp only [r]
    rw [div_pow, Real.sq_sqrt ha.le]
    ring
  constructor
  · refine ⟨scaledHermiteExtremizer r m, scaledHermiteExtremizer_degree hr m,
      scaledHermiteExtremizer_nonneg hr m, scaledHermiteExtremizer_even r m, ?_, ?_⟩
    · exact (scaledHermiteExtremizer_eval_eq_zero_iff hr m _).mpr (Or.inl hroot.symm)
    · exact (coeffNonneg_heat_scaledHermiteExtremizer_iff hr m _).mpr htime.le
  · rintro s ⟨p, hd, hp, _, hz, hc⟩
    exact hermite_heat_time_lower_bound m ha hd hp hz hc

/-- No constant smaller than four can uniformly replace the squared-root/degree bound. -/
theorem hermite_degree_constant_optimal {c : ℝ} (hc : c < 4) :
    ∃ m : ℕ, ∃ p : ℝ[X], p.Monic ∧ p.natDegree = 2 * m + 4 ∧
      (∀ x : ℝ, 0 ≤ p.eval x) ∧ (∀ x : ℝ, p.eval (-x) = p.eval x) ∧
      CoeffNonneg (forwardPolyHeat (1 / 2) p) ∧
      p.eval (hermiteEdge (2 * m + 2)) = 0 ∧
      c * (2 * m + 4 : ℝ) < hermiteEdge (2 * m + 2) ^ 2 := by
  obtain ⟨m, hm⟩ := (tendsto_even_hermiteEdge_sq_div_degree.eventually_const_lt hc).exists
  refine ⟨m, hermiteExtremizer m, hermiteExtremizer_monic m, hermiteExtremizer_degree m,
    hermiteExtremizer_nonneg m, hermiteExtremizer_eval_neg m,
    coeffNonneg_heat_hermiteExtremizer m, hermiteExtremizer_eval_edge m, ?_⟩
  exact (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * m + 4)).mp hm

/-- Central masking uses asymptotically twice the least possible heat at the same degree. -/
theorem tendsto_central_to_optimal_heat_ratio :
    Tendsto (fun m : ℕ => 2 * hermiteEdge (2 * m + 2) ^ 2 * maskedPairHeatThreshold m)
      atTop (𝓝 2) := by
  have hi := (tendsto_natCast_div_add_atTop (2 : ℝ)).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hr : Tendsto (fun m : ℕ => (2 * m + 4 : ℝ) / (8 * m)) atTop (𝓝 (1 / 4)) := by
    have hh := hi.const_mul (1 / 4 : ℝ)
    norm_num only [inv_one, mul_one] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    <;> ring
  have hlim := (((tendsto_even_hermiteEdge_sq_div_degree.const_mul 2).mul
    tendsto_maskedPairHeatThreshold).mul hr)
  norm_num only at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hd : (2 * m + 4 : ℝ) ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Positive root depth cancels from the comparison of the two exact heat thresholds. -/
theorem central_to_optimal_heat_ratio (m : ℕ) {a : ℝ} (ha : 0 < a) :
    (a * maskedPairHeatThreshold m) / (a / (2 * hermiteEdge (2 * m + 2) ^ 2)) =
      2 * hermiteEdge (2 * m + 2) ^ 2 * maskedPairHeatThreshold m := by
  have he : 0 < hermiteEdge (2 * m + 2) := hermiteEdge_pos (by omega)
  field_simp
  <;> ring

/-- The same factor-two limit holds for every fixed positive squared depth. -/
theorem tendsto_central_to_optimal_heat_times {a : ℝ} (ha : 0 < a) :
    Tendsto (fun m : ℕ => (a * maskedPairHeatThreshold m) /
      (a / (2 * hermiteEdge (2 * m + 2) ^ 2))) atTop (𝓝 2) := by
  simpa only [central_to_optimal_heat_ratio _ ha] using tendsto_central_to_optimal_heat_ratio

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
