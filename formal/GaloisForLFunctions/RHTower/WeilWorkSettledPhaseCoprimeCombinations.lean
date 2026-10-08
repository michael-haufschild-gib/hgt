import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeMasks

/-!
# Finite affine combinations of coprime masks

All algebra is literal coefficient algebra. Products of masks use the product
modulus, including repeated prime factors. No source multiplicativity is used.
-/

open Complex Finset
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem coprimeMask_product (Q R n : ℕ) :
    coprimeMask Q n * coprimeMask R n = coprimeMask (Q * R) n := by
  unfold coprimeMask
  by_cases hQ : n.Coprime Q
  · by_cases hR : n.Coprime R
    · rw [if_pos hQ, if_pos hR, if_pos (Nat.coprime_mul_iff_right.mpr ⟨hQ, hR⟩),
        one_mul]
    · rw [if_pos hQ, if_neg hR,
        if_neg (fun h => hR (Nat.coprime_mul_iff_right.mp h).2), mul_zero]
  · rw [if_neg hQ, if_neg (fun h => hQ (Nat.coprime_mul_iff_right.mp h).1), zero_mul]

def coprimeAffineMask {ι : Type*} (S : Finset ι) (Q : ι → ℕ) (c : ι → ℝ)
    (b : ℝ) (n : ℕ) : ℝ :=
  b + ∑ i ∈ S, c i * coprimeMask (Q i) n

theorem coprimeAffineMask_mul {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) (f : ℕ → ℂ) :
    (fun n => f n * (coprimeAffineMask S Q c b n : ℂ)) =
      (b : ℂ) • f + ∑ i ∈ S, (c i : ℂ) • coprimePart (Q i) f := by
  funext n
  simp only [coprimeAffineMask, Complex.ofReal_add, Complex.ofReal_sum,
    Complex.ofReal_mul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    coprimePart, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

theorem summable_coprimeAffineMask_mul {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeriesSummable (fun n => f n * (coprimeAffineMask S Q c b n : ℂ)) s := by
  rw [coprimeAffineMask_mul]
  exact (hf.smul (b : ℂ)).add
    (LSeriesSummable.sum fun i _ => (summable_coprimePart (Q i) hf).smul (c i : ℂ))

theorem LSeries_coprimeAffineMask_mul {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) {f : ℕ → ℂ} {s : ℂ} (hf : LSeriesSummable f s) :
    LSeries (fun n => f n * (coprimeAffineMask S Q c b n : ℂ)) s =
      (b : ℂ) * LSeries f s +
        ∑ i ∈ S, (c i : ℂ) * LSeries (coprimePart (Q i) f) s := by
  rw [coprimeAffineMask_mul, LSeries_add (hf.smul (b : ℂ))
    (LSeriesSummable.sum fun i _ => (summable_coprimePart (Q i) hf).smul (c i : ℂ)),
    LSeries_sum (fun i _ => (summable_coprimePart (Q i) hf).smul (c i : ℂ))]
  simp only [LSeries_smul]

/-- Exact affine square expansion, retaining all cross terms. -/
theorem coprimeAffineMask_sq {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) (n : ℕ) :
    coprimeAffineMask S Q c b n ^ 2 = b ^ 2 +
      ∑ i ∈ S, (2 * b * c i) * coprimeMask (Q i) n +
      ∑ i ∈ S, ∑ j ∈ S, (c i * c j) * coprimeMask (Q i * Q j) n := by
  have hsq : (∑ i ∈ S, c i * coprimeMask (Q i) n) ^ 2 =
      ∑ i ∈ S, ∑ j ∈ S, (c i * c j) * coprimeMask (Q i * Q j) n := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← coprimeMask_product]
    ring
  have hlin : (∑ i ∈ S, (2 * b * c i) * coprimeMask (Q i) n) =
      2 * b * ∑ i ∈ S, c i * coprimeMask (Q i) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hsq, hlin]
  unfold coprimeAffineMask
  ring

private theorem coprimeAffineMask_sq_coeff {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) :
    (fun n => ((coprimeAffineMask S Q c b n ^ 2 : ℝ) : ℂ)) =
      ((b ^ 2 : ℝ) : ℂ) • (1 : ℕ → ℂ) +
        (∑ i ∈ S, ((2 * b * c i : ℝ) : ℂ) • coprimePart (Q i) 1) +
        ∑ i ∈ S, ∑ j ∈ S, ((c i * c j : ℝ) : ℂ) • coprimePart (Q i * Q j) 1 := by
  funext n
  simp only [coprimeAffineMask_sq, Complex.ofReal_add, Complex.ofReal_sum,
    Complex.ofReal_mul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    coprimePart, Pi.one_apply, mul_one]

theorem summable_coprimeAffineMask_sq {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => ((coprimeAffineMask S Q c b n ^ 2 : ℝ) : ℂ)) s := by
  have h1 := LSeriesSummable_one_iff.mpr hs
  rw [coprimeAffineMask_sq_coeff]
  exact ((h1.smul _).add (LSeriesSummable.sum fun i _ =>
    (summable_coprimePart (Q i) h1).smul _)).add
      (LSeriesSummable.sum fun i _ => LSeriesSummable.sum fun j _ =>
        (summable_coprimePart (Q i * Q j) h1).smul _)

theorem LSeries_coprimeAffineMask_sq {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((coprimeAffineMask S Q c b n ^ 2 : ℝ) : ℂ)) s =
      ((b ^ 2 : ℝ) : ℂ) * LSeries 1 s +
        (∑ i ∈ S, ((2 * b * c i : ℝ) : ℂ) * LSeries (coprimePart (Q i) 1) s) +
        ∑ i ∈ S, ∑ j ∈ S, ((c i * c j : ℝ) : ℂ) *
          LSeries (coprimePart (Q i * Q j) 1) s := by
  have h1 := LSeriesSummable_one_iff.mpr hs
  have hi := fun i => (summable_coprimePart (Q i) h1).smul ((2 * b * c i : ℝ) : ℂ)
  have hij := fun i j => (summable_coprimePart (Q i * Q j) h1).smul ((c i * c j : ℝ) : ℂ)
  rw [coprimeAffineMask_sq_coeff,
    LSeries_add ((h1.smul _).add (LSeriesSummable.sum fun i _ => hi i))
      (LSeriesSummable.sum fun i _ => LSeriesSummable.sum fun j _ => hij i j),
    LSeries_add (h1.smul _) (LSeriesSummable.sum fun i _ => hi i),
    LSeries_sum (fun i _ => hi i),
    LSeries_sum (fun i _ => LSeriesSummable.sum fun j _ => hij i j)]
  simp only [LSeries_smul, LSeries_sum (fun j _ => hij _ j)]

end RHTower.WeilSingularArithmetic
