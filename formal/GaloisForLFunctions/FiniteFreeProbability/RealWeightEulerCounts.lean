import GaloisForLFunctions.FiniteFreeProbability.RealWeightEulerGeometry
import GaloisForLFunctions.FiniteFreeProbability.JensenCountsOffLineZeros

/-!
# Real-root gain for arbitrary nonnegative Euler weights

For a positive rational weight, Rolle's theorem applies to a product of
powers of the input and the coordinate. Removing its known factors leaves
the original real-root count as a lower bound. Positive rational weights
approximate every nonnegative real weight, and nonreal zeros persist in
the limit by Hurwitz's theorem.
-/

open Polynomial Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry

namespace FiniteFreeProbability

noncomputable section

private theorem degree_le (a : ℝ) (p : ℝ[X]) : (weightedEuler a p).natDegree ≤ p.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [weightedEuler_coeff, coeff_eq_zero_of_natDegree_lt hj, mul_zero]

private theorem leading_ne {a : ℝ} (ha : 0 < a) {p : ℝ[X]} (hp : p ≠ 0) :
    (weightedEuler a p).coeff p.natDegree ≠ 0 := by
  rw [weightedEuler_coeff]
  exact mul_ne_zero (by positivity) (leadingCoeff_ne_zero.mpr hp)

private theorem filter_nonzero {a : ℝ} (ha : 0 < a) {p : ℝ[X]} (hp : p ≠ 0) :
    weightedEuler a p ≠ 0 := by
  intro hz
  exact leading_ne ha hp (by rw [hz, coeff_zero])

private theorem rat_lift (m n : ℕ) (p : ℝ[X]) :
    derivative ((X : ℝ[X])^(m+1) * p^(n+1)) =
      X^m * p^n * C ((n : ℝ)+1) * weightedEuler (((m : ℝ)+1)/((n : ℝ)+1)) p := by
  rw [derivative_mul, derivative_X_pow_succ, derivative_pow_succ, weightedEuler]
  have hc : C ((n : ℝ)+1) * C (((m : ℝ)+1)/((n : ℝ)+1)) = C ((m : ℝ)+1) := by
    rw [← map_mul, mul_comm, div_mul_cancel₀ _ (by positivity)]
  simp only [pow_succ]
  linear_combination (X^m * p^n * p) * (-hc)

private theorem rat_gain (m n : ℕ) (p : ℝ[X]) :
    p.roots.card ≤ (weightedEuler (((m : ℝ)+1)/((n : ℝ)+1)) p).roots.card := by
  by_cases hp : p = 0
  · simp [hp]
  let q := weightedEuler (((m : ℝ)+1)/((n : ℝ)+1)) p
  have hq : q ≠ 0 := filter_nonzero (by positivity) hp
  have hn : C ((n : ℝ)+1) ≠ 0 := C_ne_zero.mpr (by positivity)
  have hlo : (X : ℝ[X])^(m+1) * p^(n+1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hp)
  have hmid : (X : ℝ[X])^m * p^n ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hp)
  have h := card_roots_le_derivative ((X : ℝ[X])^(m+1) * p^(n+1))
  rw [rat_lift, roots_mul hlo, roots_mul (mul_ne_zero (mul_ne_zero hmid hn) hq),
    roots_mul (mul_ne_zero hmid hn), roots_mul hmid, roots_C, roots_X_pow, roots_X_pow,
    roots_pow, roots_pow] at h
  simp only [Multiset.card_add, Multiset.card_nsmul, Multiset.card_singleton, Multiset.card_zero,
    mul_one, add_zero, Nat.add_mul, one_mul] at h
  omega

private def numerator (a : ℝ) (n : ℕ) : ℕ := ⌊a*((n : ℝ)+1)⌋₊
private def approx (a : ℝ) (n : ℕ) : ℝ := ((numerator a n : ℝ)+1)/((n : ℝ)+1)

private theorem approx_tendsto {a : ℝ} (ha : 0 ≤ a) : Tendsto (approx a) atTop (𝓝 a) := by
  have hb : Tendsto (fun n : ℕ => a+1/((n : ℝ)+1)) atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
  · intro n
    apply (le_div_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
    exact (Nat.lt_floor_add_one (a*((n : ℝ)+1))).le
  · intro n
    unfold approx numerator
    rw [div_le_iff₀ (by positivity : 0 < (n : ℝ)+1), add_mul, div_mul_cancel₀ _ (by positivity)]
    exact add_le_add_right (Nat.floor_le (mul_nonneg ha (by positivity))) _

/-- Every nonnegative real Euler weight decreases or preserves the total nonreal
multiplicity. The zero weight is included, even for a constant input. -/
theorem weightedEuler_nonreal_le (a : ℝ≥0) (p : ℝ[X]) :
    nonrealRootCount (weightedEuler (a : ℝ) p) ≤ nonrealRootCount p := by
  by_cases hz : weightedEuler (a : ℝ) p = 0
  · simp [hz, nonrealRootCount]
  have hp : p ≠ 0 := fun he => hz (by simp [weightedEuler, he])
  let S := fun n => weightedEuler (approx a n) p
  have hap (n : ℕ) : 0 < approx a n := by unfold approx; positivity
  refine nonrealRootCount_le_of_tendsto hz (fun n => filter_nonzero (hap n) hp)
    (S := S) (fun n => ?_) ?_
  · unfold nonrealRootCount
    exact Nat.sub_le_sub (degree_le _ p) (rat_gain (numerator a n) n p)
  · apply tendstoLocallyUniformly_eval_of_coeff (D := p.natDegree)
    · intro n
      exact natDegree_map_le.trans (degree_le _ p)
    · exact natDegree_map_le.trans (degree_le _ p)
    · intro j
      simp only [S, coeff_map, weightedEuler_coeff, Complex.ofRealHom_eq_coe]
      exact (Complex.continuous_ofReal.tendsto _).comp (((approx_tendsto a.2).add_const
        (j : ℝ)).mul_const (p.coeff j))

/-- At strictly positive real weights the degree stays fixed, hence every real
input retains at least as many real zeros, counted with multiplicity. -/
theorem weightedEuler_real_root_gain {a : ℝ} (ha : 0 < a) (p : ℝ[X]) :
    p.roots.card ≤ (weightedEuler a p).roots.card := by
  by_cases hp : p = 0
  · simp [hp]
  have hd := natDegree_eq_of_le_of_coeff_ne_zero (degree_le a p) (leading_ne ha hp)
  have h := weightedEuler_nonreal_le ⟨a,ha.le⟩ p
  change (weightedEuler a p).natDegree - (weightedEuler a p).roots.card ≤
    p.natDegree - p.roots.card at h
  rw [hd] at h
  have h₀ := card_roots' p
  omega


end

end FiniteFreeProbability
