import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.RationalRefinementCompletesTheCyclotomicGram
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Real overlap curvature and its positive centered kernel

The periodic quadratic is continuous because its endpoint values agree.
Approximating all points on one common rational grid transports the positive
conductor-completion identity to every finite family of nonnegative real
points. Consequently the centered kernel is positive and the original
distance kernel is conditionally negative.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

private theorem continuous_fract_quadratic :
    Continuous (fun x : ℝ => Int.fract x * (1 - Int.fract x)) := by
  have hpoly : Continuous (fun x : ℝ => x * (1 - x)) := by fun_prop
  have h := (AddCircle.liftIco_zero_continuous
    (p := (1 : ℝ)) (f := fun x : ℝ => x * (1 - x))
    (by norm_num) hpoly.continuousOn).comp (AddCircle.continuous_mk' (1 : ℝ))
  convert h using 1
  funext x
  rw [← AddCircle.coe_fract x,
    AddCircle.liftIco_zero_coe_apply ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩]

/-- The jumps of the fractional part cancel in the quadratic curvature. -/
theorem continuous_arithmeticOverlapCurvature (m : ℕ) :
    Continuous (arithmeticOverlapCurvature m) := by
  unfold arithmeticOverlapCurvature
  apply continuous_finset_sum
  intro d _
  have h := (continuous_fract_quadratic.comp (continuous_id.div_const (d : ℝ))).const_mul
    ((ArithmeticFunction.moebius (m / d) : ℝ) * (d : ℝ) ^ 2)
  simpa only [mul_assoc] using h

/-- The centered arithmetic kernel is jointly continuous. -/
theorem continuous_arithmeticOverlapGram (m : ℕ) :
    Continuous (fun p : ℝ × ℝ => arithmeticOverlapGram m p.1 p.2) := by
  unfold arithmeticOverlapGram
  exact ((((continuous_arithmeticOverlapCurvature m).comp continuous_fst).add
    ((continuous_arithmeticOverlapCurvature m).comp continuous_snd)).sub
      ((continuous_arithmeticOverlapCurvature m).comp
        ((continuous_fst.sub continuous_snd).abs))).div_const 2

/-- The signed divisor curvature has a positive centered Gram form on the
whole nonnegative real axis, for arbitrary finite real coefficients. -/
theorem arithmeticOverlapGram_quadratic_nonneg {ι : Type*} (s : Finset ι)
    {m : ℕ} (hm : 1 < m) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j * arithmeticOverlapGram m (x i) (x j) := by
  have ht (i : ι) (hi : i ∈ s) :
      Tendsto (fun N : ℕ => (⌊x i * (N : ℝ)⌋₊ : ℝ) / N) atTop (𝓝 (x i)) :=
    (tendsto_nat_floor_mul_div_atTop (hx i hi)).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => ∑ i ∈ s, ∑ j ∈ s, a i * a j *
      arithmeticOverlapGram m ((⌊x i * (N : ℝ)⌋₊ : ℝ) / N)
        ((⌊x j * (N : ℝ)⌋₊ : ℝ) / N)) atTop
      (𝓝 (∑ i ∈ s, ∑ j ∈ s, a i * a j * arithmeticOverlapGram m (x i) (x j))) := by
    apply tendsto_finsetSum s
    intro i hi
    apply tendsto_finsetSum s
    intro j hj
    exact ((continuous_arithmeticOverlapGram m).continuousAt.tendsto.comp
      ((ht i hi).prodMk_nhds (ht j hj))).const_mul (a i * a j)
  apply neg_nonpos.mp
  apply le_of_tendsto hlim.neg
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact neg_nonpos.mpr (arithmeticOverlapGram_rational_quadratic_nonneg s hm (by omega) a
    (fun i => ⌊x i * (N : ℝ)⌋₊))

/-- On zero-total-mass coefficients, the raw distance form is minus twice
its centered Gram form. -/
theorem arithmeticOverlapCurvature_conditional_quadratic_eq {ι : Type*}
    (s : Finset ι) (m : ℕ) (a : ι → ℝ) (x : ι → ℝ)
    (ha : ∑ i ∈ s, a i = 0) :
    (∑ i ∈ s, ∑ j ∈ s,
      a i * a j * arithmeticOverlapCurvature m |x i - x j|) =
      -2 * ∑ i ∈ s, ∑ j ∈ s, a i * a j * arithmeticOverlapGram m (x i) (x j) := by
  have he : ∀ i j, a i * a j * arithmeticOverlapCurvature m |x i - x j| =
      a i * arithmeticOverlapCurvature m (x i) * a j +
        a i * (a j * arithmeticOverlapCurvature m (x j)) -
          2 * (a i * a j * arithmeticOverlapGram m (x i) (x j)) := by
    intro i j
    unfold arithmeticOverlapGram
    ring
  simp_rw [he, sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul, ha,
    mul_zero, zero_mul, sum_const_zero]
  ring

/-- The real arithmetic distance kernel is conditionally negative. -/
theorem arithmeticOverlapCurvature_conditional_quadratic_nonpos {ι : Type*}
    (s : Finset ι) {m : ℕ} (hm : 1 < m) (a : ι → ℝ) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (ha : ∑ i ∈ s, a i = 0) :
    (∑ i ∈ s, ∑ j ∈ s,
      a i * a j * arithmeticOverlapCurvature m |x i - x j|) ≤ 0 := by
  rw [arithmeticOverlapCurvature_conditional_quadratic_eq s m a x ha]
  exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
    (arithmeticOverlapGram_quadratic_nonneg s hm a x hx)

/-- On the first unit cell the curvature is exactly linear, with slope
equal to the number of primitive roots. -/
theorem arithmeticOverlapCurvature_unit_cell {m : ℕ} (hm : 1 < m)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    arithmeticOverlapCurvature m t = (m.totient : ℝ) * t := by
  have hcard : (Polynomial.primitiveRoots m ℂ).card = m.totient :=
    (Complex.isPrimitiveRoot_exp m (zero_lt_one.trans hm).ne').card_primitiveRoots
  have h0 : primitiveRootPrefixEnergy m 0 = 0 := by simp [primitiveRootPrefixEnergy]
  have h1 : primitiveRootPrefixEnergy m 1 = (m.totient : ℝ) := by
    simp [primitiveRootPrefixEnergy, hcard]
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · have h := arithmeticOverlapCurvature_eq_interpolation hm 0 ht.1 hlt
    simpa only [Nat.cast_zero, zero_add, Nat.zero_add, h0, h1, mul_zero,
      zero_add, mul_comm] using h
  · simpa only [Nat.cast_one, h1, mul_one] using arithmeticOverlapCurvature_natCast hm 1

/-- After totient normalization, every conductor has the same full Gram
kernel on the unit cell: the minimum kernel. -/
theorem arithmeticOverlapGram_unit_cell {m : ℕ} (hm : 1 < m)
    {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    arithmeticOverlapGram m x y = (m.totient : ℝ) * min x y := by
  have hd : |x - y| ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨abs_nonneg _, abs_le.mpr ⟨by linarith [hx.1, hy.2], by linarith [hy.1, hx.2]⟩⟩
  rw [arithmeticOverlapGram, arithmeticOverlapCurvature_unit_cell hm hx,
    arithmeticOverlapCurvature_unit_cell hm hy, arithmeticOverlapCurvature_unit_cell hm hd]
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · rw [min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]
    ring

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.arithmeticOverlapGram_quadratic_nonneg
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.arithmeticOverlapCurvature_conditional_quadratic_nonpos
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.arithmeticOverlapGram_unit_cell
