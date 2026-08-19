import GaloisForLFunctions.RHTower.Sieve.LadderHarmonicSplit

/-!
# The size of a ladder step against its harmonic mass

Every estimate of the §4 assembly is stated per short block and then weighted by the reciprocal of
that block's harmonic mass, so the two have to be compared.  On a step of ratio `1 + η` the
comparison is exact up to that ratio:

```text
   stepMass_j · (Q(1+η)^j)  ≤  #B_j  ≤  stepMass_j · (Q(1+η)^{j+1}) ,
```

because every prime of the step lies in `(Q(1+η)^j, Q(1+η)^{j+1}]`.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **A ladder step is no larger than its harmonic mass times its right endpoint.** -/
theorem card_geomBlock_le_stepMass {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    ((geomBlock P Q (1 + η) j).card : ℝ) ≤ stepMass P Q η j * (Q * (1 + η) ^ (j + 1)) := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hpow : (0 : ℝ) < (1 + η) ^ (j + 1) := by positivity
  have hR : (0 : ℝ) < Q * (1 + η) ^ (j + 1) := by positivity
  have hterm : ∀ p ∈ geomBlock P Q (1 + η) j,
      (1 : ℝ) / (Q * (1 + η) ^ (j + 1)) ≤ 1 / (p : ℝ) := by
    intro p hp
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    have hp0 : (0 : ℝ) < (p : ℝ) := by
      have hQj : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
      linarith
    exact one_div_le_one_div_of_le hp0 hhi
  have hsum : ((geomBlock P Q (1 + η) j).card : ℝ) * (1 / (Q * (1 + η) ^ (j + 1)))
      ≤ stepMass P Q η j := by
    rw [stepMass]
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  calc ((geomBlock P Q (1 + η) j).card : ℝ)
      = ((geomBlock P Q (1 + η) j).card : ℝ) * (1 / (Q * (1 + η) ^ (j + 1)))
          * (Q * (1 + η) ^ (j + 1)) := by field_simp
    _ ≤ stepMass P Q η j * (Q * (1 + η) ^ (j + 1)) :=
        mul_le_mul_of_nonneg_right hsum hR.le

/-- **A ladder step is no smaller than its harmonic mass times its left endpoint.** -/
theorem stepMass_mul_le_card {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) (j : ℕ) :
    stepMass P Q η j * (Q * (1 + η) ^ j) ≤ ((geomBlock P Q (1 + η) j).card : ℝ) := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj : (0 : ℝ) < Q * (1 + η) ^ j := by positivity
  have hterm : ∀ p ∈ geomBlock P Q (1 + η) j,
      (1 : ℝ) / (p : ℝ) ≤ 1 / (Q * (1 + η) ^ j) := by
    intro p hp
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, -⟩ := hp
    exact one_div_le_one_div_of_le hQj hlo.le
  have hsum : stepMass P Q η j
      ≤ ((geomBlock P Q (1 + η) j).card : ℝ) * (1 / (Q * (1 + η) ^ j)) := by
    rw [stepMass]
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hmul := mul_le_mul_of_nonneg_right hsum hQj.le
  refine hmul.trans (le_of_eq ?_)
  field_simp

end

end RHTower.Sieve
