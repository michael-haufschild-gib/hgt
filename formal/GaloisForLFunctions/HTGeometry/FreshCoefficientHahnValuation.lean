import GaloisForLFunctions.HTGeometry.FreshCoefficientNoncancellation
import Mathlib.RingTheory.HahnSeries.Addition

/-!
# Fresh tags force exact Hahn-series order

Coefficientwise algebraic independence upgrades the ultrametric lower bound for a finite sum to an
equality.  At a common lowest exponent, partial differentiation by one fresh tag extracts a
nonzero coefficient, so cancellation is impossible.  This is the Hahn-series form of the fresh
coefficient mechanism in the k-server paper.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators
open MvPolynomial

variable {ι σ Γ R : Type*} [Fintype ι] [DecidableEq ι]
  [DecidableEq σ] [LinearOrder Γ] [CommRing R]

/-- **Exact fresh-tag order.** Suppose every series has order at least `m`, one has order exactly
`m`, and every coefficient is independent of every fresh tag.  Multiplying each series by its own
tag and summing preserves the exact lowest exponent `m`. -/
theorem orderTop_sum_fresh_smul_eq
    (eta : ι → σ) (heta : Function.Injective eta)
    (x : ι → HahnSeries Γ (MvPolynomial σ R))
    (hfresh : ∀ i j exponent,
      degreeOf (eta i) ((x j).coeff exponent) = 0)
    (m : Γ) (hmin : ∀ i, (m : WithTop Γ) ≤ (x i).orderTop)
    (i₀ : ι) (hi₀ : (x i₀).orderTop = m) :
    (∑ i, (X (eta i) : MvPolynomial σ R) • x i).orderTop = m := by
  apply HahnSeries.orderTop_eq_of_le
  · rw [HahnSeries.mem_support, HahnSeries.coeff_sum]
    simpa only [HahnSeries.coeff_smul, smul_eq_mul] using
      sum_fresh_X_mul_ne_zero eta heta (fun i => (x i).coeff m)
        (fun i j => hfresh i j m) (HahnSeries.coeff_orderTop_ne hi₀)
  · intro exponent hexponent
    by_contra hle
    have hlt : exponent < m := lt_of_not_ge hle
    rw [HahnSeries.mem_support, HahnSeries.coeff_sum] at hexponent
    apply hexponent
    apply Finset.sum_eq_zero
    intro i _
    rw [HahnSeries.coeff_smul,
      HahnSeries.coeff_eq_zero_of_lt_orderTop
        (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hlt) (hmin i)), smul_zero]

/-- A concrete finite-monomial specialization: fresh tags force the order of a sum of tagged
monomials to equal the smallest assigned exponent, even when several exponents tie. -/
theorem orderTop_sum_single_fresh_X_mul_eq_min
    (weight : ι → Γ) (eta : ι → σ) (heta : Function.Injective eta)
    (f : ι → MvPolynomial σ R)
    (hfresh : ∀ i j, degreeOf (eta i) (f j) = 0)
    (m : Γ) (hmin : ∀ i, m ≤ weight i)
    (i₀ : ι) (hi₀weight : weight i₀ = m) (hi₀ : f i₀ ≠ 0) :
    (∑ i, HahnSeries.single (weight i) (X (eta i) * f i)).orderTop = m := by
  apply HahnSeries.orderTop_eq_of_le
  · rw [HahnSeries.mem_support, HahnSeries.coeff_sum]
    let g : ι → MvPolynomial σ R := fun i => if m = weight i then f i else 0
    have hgFresh : ∀ i j, degreeOf (eta i) (g j) = 0 := by
      intro i j
      by_cases h : m = weight j
      · simp [g, h, hfresh i j]
      · simp [g, h]
    have hg₀ : g i₀ ≠ 0 := by
      simpa [g, hi₀weight] using hi₀
    have hne := sum_fresh_X_mul_ne_zero eta heta g hgFresh hg₀
    convert hne using 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [HahnSeries.coeff_single]
    by_cases h : m = weight i
    · simp [g, h]
    · simp [g, h]
  · intro exponent hexponent
    by_contra hle
    have hlt : exponent < m := lt_of_not_ge hle
    rw [HahnSeries.mem_support, HahnSeries.coeff_sum] at hexponent
    apply hexponent
    apply Finset.sum_eq_zero
    intro i _
    rw [HahnSeries.coeff_single_of_ne]
    exact ne_of_lt (lt_of_lt_of_le hlt (hmin i))

end GaloisForLFunctions.HTGeometry
