import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.HeatConeEvolution
import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.DivisorTransitions
import GaloisForLFunctions.HTGeometry.PolynomialHeatNonrealCount
import Mathlib.Analysis.Polynomial.Order

/-!
# First heat time for even nonnegative polynomials

Each even coefficient is a polynomial in heat with positive leading coefficient. Their finite
intersection eventually enters the full cone. Closedness and heat preservation then give an
attained first time, strictly positive whenever the original polynomial has a positive root.
-/

open Polynomial Filter Topology
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry
noncomputable section

/-- A fixed heated coefficient is itself a polynomial in the heat time. -/
def heatCoefficientPolynomial (p : ℝ[X]) (j : ℕ) : ℝ[X] :=
  ∑ i ∈ Finset.range (p.natDegree + 1),
    C (((derivative^[2 * i] p).coeff j) / (i.factorial : ℝ)) * X ^ i

theorem heatCoefficientPolynomial_coeff (p : ℝ[X]) (j i : ℕ) :
    (heatCoefficientPolynomial p j).coeff i = (derivative^[2 * i] p).coeff j / (i.factorial : ℝ) := by
  classical
  rw [heatCoefficientPolynomial, finsetSum_coeff]
  by_cases hi : i ∈ Finset.range (p.natDegree + 1)
  · rw [Finset.sum_eq_single i]
    · simp only [coeff_C_mul, coeff_X_pow, ite_true, mul_one]
    · intro k hk hki
      simp only [coeff_C_mul, coeff_X_pow, if_neg hki, mul_zero]
    · exact fun h => (h hi).elim
  · have hd : derivative^[2 * i] p = 0 := by
      apply iterate_derivative_eq_zero
      have := Finset.not_mem_range.mp hi
      omega
    rw [hd, coeff_zero, zero_div]
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k ≠ i := by intro h; subst k; exact hi hk
    simp only [coeff_C_mul, coeff_X_pow, if_neg hki, mul_zero]

/-- Evaluation in the heat variable is the exact finite derivative series coefficient. -/
theorem heatCoefficientPolynomial_eval (p : ℝ[X]) (j : ℕ) (s : ℝ) :
    (heatCoefficientPolynomial p j).eval s = (forwardPolyHeat s p).coeff j := by
  rw [heatCoefficientPolynomial, eval_finsetSum, forwardPolyHeat, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  simp only [eval_mul, eval_C, eval_pow, eval_X, coeff_C_mul]
  ring

/-- The leading even coefficient controls each lower even coefficient at large heat. -/
theorem heatCoefficientPolynomial_even_degree {p : ℝ[X]} {d j : ℕ}
    (hdeg : p.natDegree = 2 * d) (hp : 0 < p.leadingCoeff) (hj : j ≤ d) :
    (heatCoefficientPolynomial p (2 * j)).natDegree = d - j ∧
      0 < (heatCoefficientPolynomial p (2 * j)).leadingCoeff := by
  have hle : (heatCoefficientPolynomial p (2 * j)).natDegree ≤ d - j := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [heatCoefficientPolynomial_coeff, coeff_iterate_derivative]
    have hlt : p.natDegree < 2 * j + 2 * i := by rw [hdeg]; omega
    rw [coeff_eq_zero_of_natDegree_lt hlt, smul_zero, zero_div]
  have htop : 0 < (heatCoefficientPolynomial p (2 * j)).coeff (d - j) := by
    have hdf : 0 < ((2 * d).descFactorial (2 * (d - j)) : ℝ) := by
      apply Nat.cast_pos.mpr
      apply Nat.pos_of_ne_zero
      intro hz
      have hlt := Nat.descFactorial_eq_zero_iff_lt.mp hz
      omega
    have hc : 0 < p.coeff (2 * d) := by rw [← hdeg, coeff_natDegree]; exact hp
    rw [heatCoefficientPolynomial_coeff, coeff_iterate_derivative,
      show 2 * j + 2 * (d - j) = 2 * d by omega, nsmul_eq_mul]
    exact div_pos (mul_pos hdf hc) (by positivity)
  have he := natDegree_eq_of_le_of_coeff_ne_zero hle htop.ne'
  refine ⟨he, ?_⟩
  rw [← coeff_natDegree, he]
  exact htop

private theorem eventually_eval_pos_of_leadingCoeff_pos {q : ℝ[X]} (hq : 0 < q.leadingCoeff) :
    ∀ᶠ s : ℝ in atTop, 0 < q.eval s := by
  obtain ⟨a, ha⟩ := Polynomial.exists_max_root q (leadingCoeff_ne_zero.mp hq.ne')
  filter_upwards [eventually_ge_atTop (a + 1)] with s hs
  apply zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg _ hq.le
  intro y hy
  exact (ha y hy).trans_lt (by linarith only [hs])

/-- Every even coefficient through the degree eventually becomes strictly positive. -/
theorem eventually_pos_even_heat_coeff {p : ℝ[X]} {d j : ℕ}
    (hdeg : p.natDegree = 2 * d) (hp : 0 < p.leadingCoeff) (hj : j ≤ d) :
    ∀ᶠ s : ℝ in atTop, 0 < (forwardPolyHeat s p).coeff (2 * j) := by
  have h := eventually_eval_pos_of_leadingCoeff_pos
    (heatCoefficientPolynomial_even_degree hdeg hp hj).2
  simpa only [heatCoefficientPolynomial_eval] using h

/-- Functional evenness is exactly what eliminates the odd heat coefficients here. -/
theorem odd_coeff_eq_zero_of_even {p : ℝ[X]}
    (hp : ∀ x : ℝ, p.eval (-x) = p.eval x) (j : ℕ) : p.coeff (2 * j + 1) = 0 := by
  have he : p.comp (C (-1) * X) = p := by
    apply Polynomial.funext
    intro x
    simpa only [eval_comp, eval_mul, eval_C, eval_X, neg_one_mul] using hp x
  have hc := congrArg (fun q : ℝ[X] => q.coeff (2 * j + 1)) he
  rw [comp_C_mul_X_coeff] at hc
  have hpow : (-1 : ℝ) ^ (2 * j + 1) = -1 := by simp [pow_add, pow_mul]
  rw [hpow] at hc
  linarith only [hc]

theorem odd_heat_coeff_eq_zero {p : ℝ[X]}
    (hp : ∀ j, p.coeff (2 * j + 1) = 0) (s : ℝ) (j : ℕ) :
    (forwardPolyHeat s p).coeff (2 * j + 1) = 0 := by
  rw [forwardPolyHeat, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  rw [coeff_C_mul, coeff_iterate_derivative,
    show 2 * j + 1 + 2 * i = 2 * (j + i) + 1 by omega, hp, smul_zero, mul_zero]

private theorem eventually_all_nat_le {α : Type*} {F : Filter α} {P : ℕ → α → Prop}
    (d : ℕ) (h : ∀ j ≤ d, ∀ᶠ x in F, P j x) : ∀ᶠ x in F, ∀ j ≤ d, P j x := by
  have hall : ∀ᶠ x in F, ∀ j ∈ Finset.range (d + 1), P j x :=
    (Finset.eventually_all _).mpr (fun j hj => h j (by have := Finset.mem_range.mp hj; omega))
  filter_upwards [hall] with x hx
  intro j hj
  exact hx j (Finset.mem_range.mpr (by omega))

/-- Even polynomials with positive leading coefficient eventually enter the entire heat cone. -/
theorem eventually_coeffNonneg_heat_of_even {p : ℝ[X]} {d : ℕ}
    (hdeg : p.natDegree = 2 * d) (hp : 0 < p.leadingCoeff)
    (heven : ∀ x : ℝ, p.eval (-x) = p.eval x) :
    ∀ᶠ s : ℝ in atTop, CoeffNonneg (forwardPolyHeat s p) := by
  have hne : p ≠ 0 := leadingCoeff_ne_zero.mp hp.ne'
  have h := eventually_all_nat_le d (fun j hj => eventually_pos_even_heat_coeff hdeg hp hj)
  filter_upwards [h] with s hs
  intro n
  by_cases hn : n ≤ 2 * d
  · by_cases he : n % 2 = 0
    · rw [show n = 2 * (n / 2) by omega]
      exact (hs (n / 2) (by omega)).le
    · rw [show n = 2 * (n / 2) + 1 by omega,
        odd_heat_coeff_eq_zero (odd_coeff_eq_zero_of_even heven)]
  · have hd : (forwardPolyHeat s p).natDegree < n := by
      rw [forwardPolyHeat_eq_polyHeat, (natDegree_polyHeat _ hne).1, hdeg]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hd]

/-- A nonzero polynomial nonnegative on the real line has strictly positive leading coefficient. -/
theorem leadingCoeff_pos_of_nonnegative {p : ℝ[X]} (hp0 : p ≠ 0)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) : 0 < p.leadingCoeff := by
  have hn := leadingCoeff_ne_zero.mpr hp0
  by_contra hnot
  have hneg : p.leadingCoeff < 0 := lt_of_le_of_ne (le_of_not_gt hnot) hn
  obtain ⟨a, ha⟩ := Polynomial.exists_max_root p hp0
  have hval : 0 < (-p).eval (a + 1) := by
    apply zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    · intro y hy
      have hr : p.IsRoot y := by simpa only [IsRoot, eval_neg, neg_eq_zero] using hy
      exact (ha y hr).trans_lt (by linarith)
    · rw [leadingCoeff_neg]
      linarith only [hneg]
  rw [eval_neg] at hval
  linarith only [hval, hp (a + 1)]

/-- A positive real root excludes every nonpositive admissible heat time. -/
theorem heat_time_pos_of_positive_root {p : ℝ[X]} (hp : p ≠ 0) {x : ℝ}
    (hx : 0 < x) (hz : p.eval x = 0) {s : ℝ}
    (hs : CoeffNonneg (forwardPolyHeat s p)) : 0 < s := by
  by_contra hn
  have h0 := coeffNonneg_forwardPolyHeat_mono p (le_of_not_gt hn) hs
  rw [forwardPolyHeat_zero] at h0
  have hv := eval_pos_of_coeffNonneg hp h0 hx
  rw [hz] at hv
  exact (lt_irrefl (0 : ℝ)) hv

/-- Every even nonnegative polynomial with a positive root has a strictly positive attained
first heat time, and its full admissible set is the corresponding closed ray. -/
theorem exists_first_heat_time_of_even_nonnegative_root {p : ℝ[X]} {d : ℕ}
    (hp0 : p ≠ 0) (hdeg : p.natDegree = 2 * d)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) (heven : ∀ x : ℝ, p.eval (-x) = p.eval x)
    {x : ℝ} (hx : 0 < x) (hz : p.eval x = 0) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ s : ℝ,
      CoeffNonneg (forwardPolyHeat s p) ↔ tau ≤ s := by
  have hne : {s : ℝ | CoeffNonneg (forwardPolyHeat s p)}.Nonempty :=
    (eventually_coeffNonneg_heat_of_even hdeg (leadingCoeff_pos_of_nonnegative hp0 hp) heven).exists
  have hbd : BddBelow {s : ℝ | CoeffNonneg (forwardPolyHeat s p)} :=
    ⟨0, fun s hs => (heat_time_pos_of_positive_root hp0 hx hz hs).le⟩
  have hmem := (isClosed_forwardPolyHeat_cone p).csInf_mem hne hbd
  refine ⟨sInf {s : ℝ | CoeffNonneg (forwardPolyHeat s p)},
    heat_time_pos_of_positive_root hp0 hx hz hmem, ?_⟩
  intro s
  constructor
  · exact fun hs => csInf_le hbd hs
  · exact fun hs => coeffNonneg_forwardPolyHeat_mono p hs hmem

end
end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
