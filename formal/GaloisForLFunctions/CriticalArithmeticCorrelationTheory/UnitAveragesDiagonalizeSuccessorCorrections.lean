import GaloisForLFunctions.ArithmeticEffectivityTheory.TheFourierCoefficientsOfTheTorsionMeasure
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPoleProfilesArePrimeQuasimodes

/-!
# Ramanujan modes diagonalize affine unit averages

For each primitive root, reduced-residue powers permute the primitive roots.
Interchanging these finite sums diagonalizes the average of `a(r n+h)` over
unit residues `r`. The eigenvalue is the actual Ramanujan coefficient at the
successor shift, divided by the totient.
-/

noncomputable section

open Finset Polynomial
open scoped Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticEffectivityTheory RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

private theorem primitiveRoots_eq_coprime_powers {q : ℕ} (hq : 0 < q)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) :
    primitiveRoots q ℂ = ((range q).filter (·.Coprime q)).image (ζ ^ ·) := by
  ext μ
  simp only [mem_image, mem_filter, mem_range, mem_primitiveRoots hq]
  constructor
  · intro hμ
    haveI : NeZero q := ⟨hq.ne'⟩
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    exact ⟨i, ⟨hi, (hζ.pow_iff_coprime hq i).mp hμ⟩, rfl⟩
  · rintro ⟨i, ⟨_, hi⟩, rfl⟩
    exact hζ.pow_of_coprime i hi

private theorem sum_coprime_primitiveRoot_pow_mul {q : ℕ} (hq : 0 < q)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ q) (n : ℕ) :
    (∑ r ∈ (range q).filter (·.Coprime q), ζ ^ (r * n)) = ramanujanSum q n := by
  rw [ramanujanSum, primitiveRoots_eq_coprime_powers hq hζ,
    sum_image (fun a ha b hb hab =>
      hζ.pow_inj (mem_range.mp (mem_filter.mp ha).1)
        (mem_range.mp (mem_filter.mp hb).1) hab)]
  exact sum_congr rfl fun r _ => pow_mul ζ r n

/-- The actual primitive-root sums obey the affine reduced-residue product law. -/
theorem sum_coprime_ramanujanSum_affine {q : ℕ} (hq : 0 < q) (n h : ℕ) :
    (∑ r ∈ (range q).filter (·.Coprime q), ramanujanSum q (r * n + h)) =
      ramanujanSum q n * ramanujanSum q h := by
  have he (r : ℕ) : ramanujanSum q (r * n + h) =
      ∑ ζ ∈ primitiveRoots q ℂ, ζ ^ (r * n) * ζ ^ h := by
    simp only [ramanujanSum, pow_add]
  simp_rw [he]
  rw [sum_comm]
  calc
    _ = ∑ ζ ∈ primitiveRoots q ℂ, ramanujanSum q n * ζ ^ h := by
      apply sum_congr rfl
      intro ζ hζ
      rw [← sum_mul, sum_coprime_primitiveRoot_pow_mul hq ((mem_primitiveRoots hq).mp hζ)]
    _ = _ := by rw [← mul_sum]; rfl

/-- The finite affine unit law holds for the literal real arithmetic coefficients. -/
theorem sum_coprime_ramanujanLagCoefficient_affine {q : ℕ} (hq : 0 < q) (n h : ℕ) :
    (∑ r ∈ (range q).filter (·.Coprime q), ramanujanLagCoefficient q (r * n + h)) =
      ramanujanLagCoefficient q n * ramanujanLagCoefficient q h := by
  have he := sum_coprime_ramanujanSum_affine hq n h
  simp_rw [TransThresholdPairCorrelation.ramanujanSum_eq_ramanujanLagCoefficient hq] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re] using hr

/-- Every normalized conductor is an eigenfunction of each affine unit average;
the eigenvalue retains the exact successor shift. -/
theorem normalizedRamanujanMode_affine_unit_average {q : ℕ} (hq : 0 < q) (n h : ℕ) :
    (∑ r ∈ (range q).filter (·.Coprime q), normalizedRamanujanMode q (r * n + h)) /
        (q.totient : ℝ) =
      (ramanujanLagCoefficient q h / (q.totient : ℝ)) * normalizedRamanujanMode q n := by
  simp_rw [normalizedRamanujanMode_eq_coefficient hq]
  rw [← sum_div, sum_coprime_ramanujanLagCoefficient_affine hq]
  ring

/-- The exact arithmetic eigenvalue of a successor unit average lies in `[-1,1]`. -/
theorem abs_successor_unit_eigenvalue_le_one {q : ℕ} (hq : 0 < q) (h : ℕ) :
    |ramanujanLagCoefficient q h / (q.totient : ℝ)| ≤ 1 := by
  have ht : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  rw [abs_div, abs_of_pos ht, div_le_one ht]
  exact BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient q h

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.sum_coprime_ramanujanSum_affine
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.normalizedRamanujanMode_affine_unit_average
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_successor_unit_eigenvalue_le_one
