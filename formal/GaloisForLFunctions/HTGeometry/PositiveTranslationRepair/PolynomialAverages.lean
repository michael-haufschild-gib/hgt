import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.PositiveMultipliers

/-! Positive polynomial translation averages preserve order. A polynomial pulse below a
source supplies a finite positive average making that source nonnegative. -/

open Polynomial
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section
namespace GaloisForLFunctions.HTGeometry.PositiveTranslationRepair

/-- Translation by one mesh step, as a linear endomorphism. -/
def translationEnd (h : ℝ) : Module.End ℝ (ℝ → ℝ) where
  toFun f x := f (x - h)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem translationEnd_pow_apply (h : ℝ) (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (translationEnd h ^ n) f x = f (x - n * h) := by
  induction n generalizing f x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    change f ((x - n * h) - h) = _
    congr 1
    push_cast
    ring

/-- Apply a polynomial to the translation endomorphism. -/
def polynomialAverage (p : ℝ[X]) (h : ℝ) : Module.End ℝ (ℝ → ℝ) :=
  aeval (translationEnd h) p

theorem polynomialAverage_apply (p : ℝ[X]) (h : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    polynomialAverage p h f x =
      ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * f (x - i * h) := by
  rw [polynomialAverage, aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, translationEnd_pow_apply]

theorem polynomialAverage_mul (p q : ℝ[X]) (h : ℝ) (f : ℝ → ℝ) :
    polynomialAverage (p * q) h f = polynomialAverage p h (polynomialAverage q h f) := by
  rw [polynomialAverage, map_mul, Module.End.mul_apply]
  rfl

theorem polynomialAverage_mono {p : ℝ[X]} (hp : CoeffNonneg p) (h : ℝ)
    {f g : ℝ → ℝ} (hfg : ∀ x, f x ≤ g x) (x : ℝ) :
    polynomialAverage p h f x ≤ polynomialAverage p h g x := by
  simp only [polynomialAverage_apply]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfg _) (hp i)

theorem polynomialAverage_nonneg {p : ℝ[X]} (hp : CoeffNonneg p) (h : ℝ)
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℝ) :
    0 ≤ polynomialAverage p h f x := by
  rw [polynomialAverage_apply]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hf _)

/-- A coefficient-positive multiple repairs every function above the corresponding polynomial pulse. -/
theorem exists_positive_average_of_polynomial_lower_bound
    (p : ℝ[X]) (hp : ∀ x : ℝ, 0 ≤ x → 0 < p.eval x) (h : ℝ)
    {f b : ℝ → ℝ} (hb : ∀ x, 0 ≤ b x)
    (hlower : ∀ x, polynomialAverage p h b x ≤ f x) :
    ∃ L : List ℝ, (∀ r ∈ L, 0 < r) ∧
      ∀ x, 0 ≤ polynomialAverage (negativeRootMultiplier L) h f x := by
  obtain ⟨L, hL, hrepair⟩ := exists_negativeRootMultiplier_repair p hp
  refine ⟨L, hL, fun x => ?_⟩
  have hmono := polynomialAverage_mono (negativeRootMultiplier_coeffNonneg hL) h hlower x
  have hnonneg := polynomialAverage_nonneg hrepair h hb x
  rw [mul_comm, polynomialAverage_mul] at hnonneg
  exact hnonneg.trans hmono

#print axioms exists_positive_average_of_polynomial_lower_bound

end GaloisForLFunctions.HTGeometry.PositiveTranslationRepair
