import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CyclotomicNormGivesAConductorUniformCurvatureFloor
import GaloisForLFunctions.HTGeometry.FiniteHilbertDispersion
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Nat.Dist

/-!
# The exact Gram completion of arithmetic curvature

Primitive-root prefix differences are unit rotations of shorter prefixes.
Consequently integer arithmetic curvature is a squared Hilbert distance.
Its centered kernel is positive, whereas the uncentered kernel is
conditionally negative. The identities retain every mixed coefficient.
-/

noncomputable section

open Finset Polynomial
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

/-- The geometric prefix at one primitive embedding. -/
def primitivePrefixValue (ζ : ℂ) (k : ℕ) : ℂ :=
  ∑ j ∈ range k, ζ ^ j

private theorem primitivePrefixValue_add (ζ : ℂ) (i j : ℕ) :
    primitivePrefixValue ζ (i + j) =
      primitivePrefixValue ζ i + ζ ^ i * primitivePrefixValue ζ j := by
  simp only [primitivePrefixValue, sum_range_add, pow_add, mul_sum]

private theorem norm_primitivePrefixValue_sub_of_le {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    {i j : ℕ} (hji : j ≤ i) :
    ‖primitivePrefixValue ζ i - primitivePrefixValue ζ j‖ =
      ‖primitivePrefixValue ζ (i - j)‖ := by
  have hij : j + (i - j) = i := by omega
  have hp := primitivePrefixValue_add ζ j (i - j)
  rw [hij] at hp
  rw [hp, add_sub_cancel_left, norm_mul, norm_pow, hζ, one_pow, one_mul]

/-- Prefix distance depends only on the difference of the two lengths. -/
theorem norm_primitivePrefixValue_sub {ζ : ℂ} (hζ : ‖ζ‖ = 1) (i j : ℕ) :
    ‖primitivePrefixValue ζ i - primitivePrefixValue ζ j‖ =
      ‖primitivePrefixValue ζ (Nat.dist i j)‖ := by
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij, norm_sub_rev]
    exact norm_primitivePrefixValue_sub_of_le hζ hij
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hji]
    exact norm_primitivePrefixValue_sub_of_le hζ hji

/-- The signed divisor curvature at integer differences is an actual
squared distance, before any scalar or matrix inequality is applied. -/
theorem primitiveRootPrefixEnergy_dist_eq {m : ℕ} (hm : 0 < m) (i j : ℕ) :
    primitiveRootPrefixEnergy m (Nat.dist i j) =
      ∑ ζ ∈ primitiveRoots m ℂ,
        ‖primitivePrefixValue ζ i - primitivePrefixValue ζ j‖ ^ 2 := by
  unfold primitiveRootPrefixEnergy
  refine sum_congr rfl fun ζ hζ => ?_
  have hroot := (mem_primitiveRoots hm).mp hζ
  have hnorm : ‖ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hroot.pow_eq_one hm.ne'
  rw [norm_primitivePrefixValue_sub hnorm, Complex.sq_norm]
  rfl

/-- The centered arithmetic curvature kernel. -/
def primitivePrefixGram (m i j : ℕ) : ℝ :=
  (primitiveRootPrefixEnergy m i + primitiveRootPrefixEnergy m j -
    primitiveRootPrefixEnergy m (Nat.dist i j)) / 2

/-- Centering gives the literal real Gram matrix of primitive prefixes. -/
theorem primitivePrefixGram_eq_sum_inner {m : ℕ} (hm : 0 < m) (i j : ℕ) :
    primitivePrefixGram m i j =
      ∑ ζ ∈ primitiveRoots m ℂ,
        inner ℝ (primitivePrefixValue ζ i) (primitivePrefixValue ζ j) := by
  rw [primitivePrefixGram, primitiveRootPrefixEnergy_dist_eq hm]
  simp only [primitiveRootPrefixEnergy, ← Complex.sq_norm]
  rw [← sum_add_distrib, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun ζ _ => ?_
  rw [norm_sub_sq_real]
  change (‖primitivePrefixValue ζ i‖ ^ 2 + ‖primitivePrefixValue ζ j‖ ^ 2 -
    (‖primitivePrefixValue ζ i‖ ^ 2 -
      2 * inner ℝ (primitivePrefixValue ζ i) (primitivePrefixValue ζ j) +
      ‖primitivePrefixValue ζ j‖ ^ 2)) / 2 = _
  ring

/-- The full centered quadratic form is a sum of actual primitive-root
squares, for arbitrary finite real coefficients and prefix lengths. -/
theorem primitivePrefixGram_quadratic_eq {ι : Type*} (s : Finset ι)
    {m : ℕ} (hm : 0 < m) (a : ι → ℝ) (k : ι → ℕ) :
    (∑ i ∈ s, ∑ j ∈ s, a i * a j * primitivePrefixGram m (k i) (k j)) =
      ∑ ζ ∈ primitiveRoots m ℂ,
        ‖∑ i ∈ s, a i • primitivePrefixValue ζ (k i)‖ ^ 2 := by
  simp_rw [primitivePrefixGram_eq_sum_inner hm, mul_sum]
  calc
    _ = ∑ i ∈ s, ∑ ζ ∈ primitiveRoots m ℂ, ∑ j ∈ s,
        a i * a j * inner ℝ (primitivePrefixValue ζ (k i))
          (primitivePrefixValue ζ (k j)) :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ ζ ∈ primitiveRoots m ℂ, ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * inner ℝ (primitivePrefixValue ζ (k i))
          (primitivePrefixValue ζ (k j)) := sum_comm
    _ = _ := by
      refine sum_congr rfl fun ζ _ => ?_
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- Every finite compression of the completed kernel is nonnegative. -/
theorem primitivePrefixGram_quadratic_nonneg {ι : Type*} (s : Finset ι)
    {m : ℕ} (hm : 0 < m) (a : ι → ℝ) (k : ι → ℕ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, a i * a j * primitivePrefixGram m (k i) (k j) := by
  rw [primitivePrefixGram_quadratic_eq s hm]
  exact sum_nonneg fun ζ _ => sq_nonneg _

/-- On zero-total-mass coefficients the uncentered curvature has the
opposite sign, with its entire negative part given by one square energy. -/
theorem primitiveRootPrefixEnergy_conditional_quadratic_eq {ι : Type*} (s : Finset ι)
    {m : ℕ} (hm : 0 < m) (a : ι → ℝ) (k : ι → ℕ) (ha : ∑ i ∈ s, a i = 0) :
    (∑ i ∈ s, ∑ j ∈ s,
      a i * a j * primitiveRootPrefixEnergy m (Nat.dist (k i) (k j))) =
      -2 * ∑ ζ ∈ primitiveRoots m ℂ,
        ‖∑ i ∈ s, a i • primitivePrefixValue ζ (k i)‖ ^ 2 := by
  simp_rw [primitiveRootPrefixEnergy_dist_eq hm, mul_sum]
  calc
    _ = ∑ i ∈ s, ∑ ζ ∈ primitiveRoots m ℂ, ∑ j ∈ s,
        a i * a j * ‖primitivePrefixValue ζ (k i) - primitivePrefixValue ζ (k j)‖ ^ 2 :=
      sum_congr rfl fun _ _ => sum_comm
    _ = ∑ ζ ∈ primitiveRoots m ℂ, ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * ‖primitivePrefixValue ζ (k i) - primitivePrefixValue ζ (k j)‖ ^ 2 :=
      sum_comm
    _ = ∑ ζ ∈ primitiveRoots m ℂ,
        -2 * ‖∑ i ∈ s, a i • primitivePrefixValue ζ (k i)‖ ^ 2 :=
      sum_congr rfl fun ζ _ =>
        HTGeometry.finite_pairwise_hilbert_dispersion_of_sum_eq_zero
          s a (fun i => primitivePrefixValue ζ (k i)) ha

/-- Conditional negative type is an exact consequence of the primitive
prefix realization, without a spectral assumption. -/
theorem primitiveRootPrefixEnergy_conditional_quadratic_nonpos {ι : Type*} (s : Finset ι)
    {m : ℕ} (hm : 0 < m) (a : ι → ℝ) (k : ι → ℕ) (ha : ∑ i ∈ s, a i = 0) :
    (∑ i ∈ s, ∑ j ∈ s,
      a i * a j * primitiveRootPrefixEnergy m (Nat.dist (k i) (k j))) ≤ 0 := by
  rw [primitiveRootPrefixEnergy_conditional_quadratic_eq s hm a k ha]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sum_nonneg fun ζ _ => sq_nonneg _)

/-- Integer samples of the real curvature are precisely the prefix energies. -/
theorem arithmeticOverlapCurvature_natCast {m : ℕ} (hm : 1 < m) (k : ℕ) :
    arithmeticOverlapCurvature m (k : ℝ) = primitiveRootPrefixEnergy m k := by
  have h := arithmeticOverlapCurvature_eq_interpolation hm k
    (u := 0) le_rfl zero_lt_one
  simpa only [add_zero, sub_zero, one_mul, zero_mul] using h

/-- The cyclotomic norm gives a conductor-uniform separation quantum for
distinct prefix classes. This is a distance bound, not a full Gram floor. -/
theorem totient_le_primitive_prefix_distance {m : ℕ} (hm : 1 < m) (i j : ℕ)
    (hij : ¬ m ∣ Nat.dist i j) :
    (m.totient : ℝ) ≤ ∑ ζ ∈ primitiveRoots m ℂ,
      ‖primitivePrefixValue ζ i - primitivePrefixValue ζ j‖ ^ 2 := by
  rw [← primitiveRootPrefixEnergy_dist_eq (zero_lt_one.trans hm)]
  exact totient_le_primitiveRootPrefixEnergy hm hij

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitivePrefixGram_quadratic_eq
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.primitiveRootPrefixEnergy_conditional_quadratic_eq
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.totient_le_primitive_prefix_distance
