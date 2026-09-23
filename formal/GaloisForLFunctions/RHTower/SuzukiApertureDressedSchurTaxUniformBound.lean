import GaloisForLFunctions.RHTower.SuzukiApertureDressedMarkedHalfGapUniformBound
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaSchurCoherence

/-!
# Uniform cofinal bound for aperture-dressed scalar Schur tax

The Suzuki Krein weld pays a projective holonomy tax `b² / A` when its completed positive block
has scalar weight `A > 0` and its cross-channel coupling has weight `b`.  A common determinant-line
density `q` scales both blocks as `qA` and `qb`, so the dressed tax is not quadratic in source mass:

`(qb)² / (qA) = q * b² / A`.

For the actual aperture-dressed wall atom, `q` is strictly positive and its complete
prime--valuation sum has an explicit ceiling independent of observer aperture and spectral height.
Consequently every fixed scalar Schur tax is absolutely summable and uniformly bounded after actual
source dressing.  Thus all-prime wall mass cannot itself make this holonomy tax diverge.  Remaining
RH-bearing work is uniform control of the undressed Schur ratio and occurrence of this block in the
actual Robin--Gamma--holonomy carrier.

No RH premise, Xi-zero hypothesis, computation, or asymptotic interchange is used.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Scalar Schur tax carried by one actual aperture-dressed prime--valuation atom. -/
def suzukiCriticalApertureDressedScalarSchurTax
    (h a t positiveBlock coupling : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  Complex.normSq
      (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) *
    (coupling ^ (2 : ℕ) / positiveBlock)

/-- Every actual dressed determinant-line density is strictly positive. -/
theorem normSq_suzukiCriticalApertureBoundaryAtom_pos
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ)
    (pe : Nat.Primes × ℕ) :
    0 < Complex.normSq
      (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) := by
  rw [normSq_suzukiCriticalApertureBoundaryAtom_eq_causalDepthGammaWeight_sq]
  exact sq_pos_of_pos (suzukiCausalDepthGammaWeight_pos hh ha pe)

/-- **Schur-tax homogeneity.** Scaling positive block and coupling by same actual source density
makes the tax linear in that density. -/
theorem suzukiCriticalApertureDressedScalarSchurTax_eq_scaledBlocks
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ)
    {positiveBlock coupling : ℝ} (hpositive : 0 < positiveBlock)
    (pe : Nat.Primes × ℕ) :
    let q := Complex.normSq
      (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2)
    (q * coupling) ^ (2 : ℕ) / (q * positiveBlock) =
      suzukiCriticalApertureDressedScalarSchurTax
        h a t positiveBlock coupling pe := by
  dsimp only
  rw [suzukiCriticalApertureDressedScalarSchurTax]
  have hq := normSq_suzukiCriticalApertureBoundaryAtom_pos hh ha t pe
  field_simp [hq.ne', hpositive.ne']

/-- Positive-block coercivity makes every dressed scalar tax nonnegative. -/
theorem suzukiCriticalApertureDressedScalarSchurTax_nonneg
    (h a t : ℝ) {positiveBlock : ℝ} (hpositive : 0 < positiveBlock)
    (coupling : ℝ) (pe : Nat.Primes × ℕ) :
    0 ≤ suzukiCriticalApertureDressedScalarSchurTax
      h a t positiveBlock coupling pe := by
  rw [suzukiCriticalApertureDressedScalarSchurTax]
  exact mul_nonneg (Complex.normSq_nonneg _)
    (div_nonneg (sq_nonneg _) hpositive.le)

/-- Complete dressed scalar Schur tax is absolutely summable over primes and valuation depth. -/
theorem summable_suzukiCriticalApertureDressedScalarSchurTax_allPrime
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t positiveBlock coupling : ℝ) :
    Summable (suzukiCriticalApertureDressedScalarSchurTax
      h a t positiveBlock coupling) := by
  have hs := summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  refine (hs.mul_right (coupling ^ (2 : ℕ) / positiveBlock)).congr ?_
  intro pe
  rfl

/-- Exact total-tax law: dressed wall mass times one undressed scalar Schur ratio. -/
theorem tsum_suzukiCriticalApertureDressedScalarSchurTax_eq
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t positiveBlock coupling : ℝ) :
    (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedScalarSchurTax
        h a t positiveBlock coupling pe) =
      (∑' pe : Nat.Primes × ℕ,
        Complex.normSq
          (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2)) *
        (coupling ^ (2 : ℕ) / positiveBlock) := by
  have hs := summable_normSq_suzukiCriticalApertureBoundaryAtom_allPrime hh ha t
  rw [show (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedScalarSchurTax
        h a t positiveBlock coupling pe) =
      ∑' pe : Nat.Primes × ℕ,
        Complex.normSq
          (suzukiCriticalApertureBoundaryAtom h a t pe.1 pe.2) *
          (coupling ^ (2 : ℕ) / positiveBlock) by
      apply tsum_congr
      intro pe
      rfl]
  exact hs.tsum_mul_right (coupling ^ (2 : ℕ) / positiveBlock)

/-- **Uniform cofinal Schur-tax ceiling.** Right side is independent of observer aperture `a` and
spectral height `t`. -/
theorem tsum_suzukiCriticalApertureDressedScalarSchurTax_le
    {h a : ℝ} (hh : 0 < h) (ha : 0 < a) (t : ℝ)
    {positiveBlock : ℝ} (hpositive : 0 < positiveBlock) (coupling : ℝ) :
    (∑' pe : Nat.Primes × ℕ,
      suzukiCriticalApertureDressedScalarSchurTax
        h a t positiveBlock coupling pe) ≤
      (2 * ((h * Real.sqrt h)⁻¹) ^ (2 : ℕ) *
        (∑' p : Nat.Primes,
          Real.log (p : ℝ) * ((p : ℝ) ^ (2 : ℕ))⁻¹)) *
        (coupling ^ (2 : ℕ) / positiveBlock) := by
  rw [tsum_suzukiCriticalApertureDressedScalarSchurTax_eq
    hh ha t positiveBlock coupling]
  exact mul_le_mul_of_nonneg_right
    (tsum_normSq_suzukiCriticalApertureBoundaryAtom_allPrime_le hh ha t)
    (div_nonneg (sq_nonneg _) hpositive.le)

end

end RHTower
