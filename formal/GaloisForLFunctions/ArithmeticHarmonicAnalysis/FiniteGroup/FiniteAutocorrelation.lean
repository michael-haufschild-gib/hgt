import Mathlib.Analysis.Complex.Circle
import Mathlib.Data.NNReal.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Finite autocorrelation, positivity, and difference support

Autocorrelation of real weights has character transform equal to a squared modulus.
For nonnegative weights, its positive support is exactly the quotient set of the
positive support of the weights. The identities hold for every finite group; no
commutativity or probability normalization is required.
-/

open Finset
open scoped Classical Pointwise

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

noncomputable section

variable {G : Type*} [Group G] [Fintype G]

/-- The mass of ordered pairs whose quotient is the specified group element. -/
def finiteAutocorrelation (f : G → ℝ) (g : G) : ℝ :=
  ∑ x, f x * f (g⁻¹ * x)

/-- Total autocorrelation mass is the square of the original total mass. -/
theorem sum_finiteAutocorrelation (f : G → ℝ) :
    ∑ g, finiteAutocorrelation f g = (∑ x, f x) ^ 2 := by
  unfold finiteAutocorrelation
  rw [sum_comm]
  calc
    _ = ∑ x, f x * ∑ y, f y := by
      apply sum_congr rfl
      intro x _
      rw [← mul_sum]
      congr 1
      exact Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulRight x)) f
    _ = _ := by rw [← sum_mul, pow_two]

/-- The identity coefficient is the exact squared energy of the weights. -/
theorem finiteAutocorrelation_one (f : G → ℝ) :
    finiteAutocorrelation f 1 = ∑ x, (f x) ^ 2 := by
  simp [finiteAutocorrelation, pow_two]

private theorem circle_inv_eq_conj (z : Circle) :
    (z : ℂ)⁻¹ = (starRingEnd ℂ) (z : ℂ) := by
  rw [Complex.inv_def, Circle.normSq_coe]
  simp

/-- Autocorrelation has squared-modulus Fourier transform for every one-dimensional character. -/
theorem finiteAutocorrelation_character (f : G → ℝ) (χ : G →* Circle) :
    ∑ g, (finiteAutocorrelation f g : ℂ) * (χ g : ℂ) =
      (Complex.normSq (∑ x, (f x : ℂ) * (χ x : ℂ)) : ℂ) := by
  have hshift (x : G) :
      (∑ g, (f (g⁻¹ * x) : ℂ) * (χ g : ℂ)) =
        (χ x : ℂ) * (starRingEnd ℂ) (∑ y, (f y : ℂ) * (χ y : ℂ)) := by
    calc
      _ = ∑ y, (f ((x * y⁻¹)⁻¹ * x) : ℂ) * (χ (x * y⁻¹) : ℂ) :=
        (Equiv.sum_comp ((Equiv.inv G).trans (Equiv.mulLeft x))
          (fun g => (f (g⁻¹ * x) : ℂ) * (χ g : ℂ))).symm
      _ = _ := by
        rw [map_sum, mul_sum]
        apply sum_congr rfl
        intro y _
        have hcancel : (x * y⁻¹)⁻¹ * x = y := by group
        simp only [hcancel, map_mul, map_inv, Circle.coe_mul, Circle.coe_inv,
          circle_inv_eq_conj, Complex.conj_ofReal]
        ring
  simp only [finiteAutocorrelation, Complex.ofReal_sum, Complex.ofReal_mul, sum_mul]
  rw [sum_comm]
  calc
    _ = ∑ x, (f x : ℂ) * ∑ g, (f (g⁻¹ * x) : ℂ) * (χ g : ℂ) := by
      apply sum_congr rfl
      intro x _
      rw [mul_sum]
      apply sum_congr rfl
      intro g _
      ring
    _ = (∑ x, (f x : ℂ) * (χ x : ℂ)) *
        (starRingEnd ℂ) (∑ x, (f x : ℂ) * (χ x : ℂ)) := by
      simp_rw [hshift]
      rw [sum_mul]
      apply sum_congr rfl
      intro x _
      ring
    _ = _ := Complex.mul_conj _

/-- Every character coefficient of a real autocorrelation is real and nonnegative. -/
theorem finiteAutocorrelation_spectral_nonneg (f : G → ℝ) (χ : G →* Circle) :
    0 ≤ (∑ g, (finiteAutocorrelation f g : ℂ) * (χ g : ℂ)).re ∧
      (∑ g, (finiteAutocorrelation f g : ℂ) * (χ g : ℂ)).im = 0 := by
  rw [finiteAutocorrelation_character]
  exact ⟨Complex.normSq_nonneg _, rfl⟩

/-- Nonnegative input weights have nonnegative autocorrelation coefficients. -/
theorem finiteAutocorrelation_nonneg (w : G → NNReal) (g : G) :
    0 ≤ finiteAutocorrelation (fun x => (w x : ℝ)) g :=
  sum_nonneg (fun x _ => mul_nonneg (w x).property (w (g⁻¹ * x)).property)

variable [DecidableEq G]

/-- The positive support of a nonnegative weight family. -/
def positiveWeightSupport (w : G → NNReal) : Finset G :=
  univ.filter fun x => 0 < (w x : ℝ)

/-- A quotient has positive autocorrelation mass exactly when it is represented by two
positive-weight elements. This includes the zero weight family without an exception. -/
theorem finiteAutocorrelation_pos_iff (w : G → NNReal) (g : G) :
    0 < finiteAutocorrelation (fun x => (w x : ℝ)) g ↔
      g ∈ positiveWeightSupport w * (positiveWeightSupport w)⁻¹ := by
  have hpositive : (0 < ∑ x, (w x : ℝ) * (w (g⁻¹ * x) : ℝ)) ↔
      ∃ x ∈ (univ : Finset G), 0 < (w x : ℝ) * (w (g⁻¹ * x) : ℝ) :=
    sum_pos_iff_of_nonneg (fun x _ => mul_nonneg (w x).property (w (g⁻¹ * x)).property)
  constructor
  · intro h
    obtain ⟨x, _, hp⟩ := hpositive.mp h
    have hpos := (mul_pos_iff.mp hp).resolve_right
      (fun hn => (not_lt_of_ge (w x).property) hn.1)
    refine mem_mul.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hpos.1⟩,
      (g⁻¹ * x)⁻¹, mem_inv.mpr ⟨g⁻¹ * x, mem_filter.mpr ⟨mem_univ _, hpos.2⟩, rfl⟩, ?_⟩
    group
  · intro hg
    apply hpositive.mpr
    obtain ⟨x, hx, z, hz, rfl⟩ := mem_mul.mp hg
    obtain ⟨y, hy, rfl⟩ := mem_inv.mp hz
    refine ⟨x, mem_univ _, ?_⟩
    have hcancel : (x * y⁻¹)⁻¹ * x = y := by group
    rw [hcancel]
    exact mul_pos (mem_filter.mp hx).2 (mem_filter.mp hy).2

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.sum_finiteAutocorrelation
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.finiteAutocorrelation_one
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.finiteAutocorrelation_character
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.finiteAutocorrelation_spectral_nonneg
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.finiteAutocorrelation_nonneg
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.finiteAutocorrelation_pos_iff
