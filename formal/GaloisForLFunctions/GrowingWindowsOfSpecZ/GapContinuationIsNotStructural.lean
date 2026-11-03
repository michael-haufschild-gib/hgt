import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeCanonicalSystem
import Mathlib.Tactic.FinCases

/-!
# Continuation across interior gaps is not structural

Zero modes of a first critical window continue uniquely from either end collar
(`zeroMode_eq_of_eq_on_collar`). Across an interior gap they need not: the window structure alone —
an even positive-semidefinite Toeplitz sequence at its first critical length — allows zero modes with
interior gaps.

* **The three-angle curve** (`curveThree`): `κ(d) = 1` if `3 ∣ d` and `0` otherwise, the power sums
  `(1 + ω^d + ω^{−d})/3` of the three cube roots of unity, i.e. the Toeplitz data of a curve with three
  Frobenius angles `0, ±2π/3`.
* **Its first critical window has a gap** (`curveThree_first_critical`): the window of size `3` is
  positive definite (`T_3(x) = Σx_i²`), the window of size `4` is nonnegative,
  `T_4(x) = (x₀ + x₃)² + x₁² + x₂²`, and its zero modes are exactly the multiples of
  `(1, 0, 0, −1)`: the unique zero mode vanishes on both interior sites. Its polynomial `1 − z³` has the
  three angles as simple roots, as the degeneration theory requires (`zeroMode_roots`).

So a unique-continuation principle across interior gaps is not a consequence of positivity,
translation invariance and the reflection: it holds for no class containing curves with three
angles. For Spec ℤ it must come from arithmetic; under RH there are no zero modes at all, and
forbidding them is RH (`riemannHypothesis_iff_no_degenerate_lattice`). The structural survivor is
continuation from an end collar.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

/-- The Toeplitz data of the curve with the three cube roots of unity as Frobenius angles. -/
def curveThree (d : ℤ) : ℝ := if (3 : ℤ) ∣ d then 1 else 0

theorem curveThree_isEven : IsEvenSeq curveThree := fun d => by
  simp only [curveThree, Int.dvd_neg]

theorem toeplitzForm_curveThree_three (x : Fin 3 → ℝ) :
    toeplitzForm curveThree 3 x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  simp only [toeplitzForm, Fin.sum_univ_three, curveThree, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  norm_num
  ring

theorem toeplitzForm_curveThree_four (x : Fin 4 → ℝ) :
    toeplitzForm curveThree 4 x = (x 0 + x 3) ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  simp only [toeplitzForm, Fin.sum_univ_four, curveThree]
  norm_num
  ring

/-- **The first critical window of the three-angle curve has an interior gap.** The window of size `3`
is positive definite, the window of size `4` is nonnegative, and its zero modes are exactly the
multiples of `(1, 0, 0, −1)`. -/
theorem curveThree_first_critical :
    ToeplitzPosDef curveThree 3 ∧ (∀ x : Fin 4 → ℝ, 0 ≤ toeplitzForm curveThree 4 x) ∧
      ∀ x : Fin 4 → ℝ, toeplitzForm curveThree 4 x = 0 ↔
        x = fun k => x 0 * ![1, 0, 0, -1] k := by
  refine ⟨fun x hx => ?_, fun x => ?_, fun x => ?_⟩
  · rw [toeplitzForm_curveThree_three]
    by_contra hle
    push Not at hle
    apply hx
    funext k
    fin_cases k <;> simp <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]
  · rw [toeplitzForm_curveThree_four]; positivity
  · rw [toeplitzForm_curveThree_four]
    constructor
    · intro h0
      have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0 + x 3), sq_nonneg (x 1), sq_nonneg (x 2)]
      have h2 : x 2 = 0 := by nlinarith [sq_nonneg (x 0 + x 3), sq_nonneg (x 1), sq_nonneg (x 2)]
      have h3 : x 3 = -x 0 := by nlinarith [sq_nonneg (x 0 + x 3), sq_nonneg (x 1), sq_nonneg (x 2)]
      funext k
      fin_cases k <;> simp [h1, h2, h3]
    · intro hx
      have e0 := congrFun hx 1
      have e1 := congrFun hx 2
      have e2 := congrFun hx 3
      simp at e0 e1 e2
      rw [e0, e1, e2]
      ring

end GaloisForLFunctions.GrowingWindowsOfSpecZ
