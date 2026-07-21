import GaloisForLFunctions.HilbertMetric.PositiveHessianSquare
import GaloisForLFunctions.HilbertMetric.FourthJetCoalescedCusp

/-!
# A uniform coalesced square for three-point correlation determinants

For a `C⁶` radial profile, negative center curvature and a strict fourth Hankel jet open a full
two-dimensional positive determinant neighbourhood at the doubly coalesced corner.  The proof
uses the three entrywise-positive Hessian jets of `∂y²∂x² D`; unlike a ray expansion, it remains
uniform when either aspect ratio tends to zero.
-/

open Set

namespace HilbertMetric

noncomputable section

private def mixedSecondSum0 (f f₁ f₂ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₂ y * f (x + y) + 2 * f₁ y * f₁ (x + y) + f y * f₂ (x + y)

private def mixedSecondSum1 (f f₁ f₂ f₃ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₂ y * f₁ (x + y) + 2 * f₁ y * f₂ (x + y) + f y * f₃ (x + y)

private def mixedSecondSum2 (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₂ y * f₂ (x + y) + 2 * f₁ y * f₃ (x + y) + f y * f₄ (x + y)

private def mixedSecondSum3 (f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₂ y * f₃ (x + y) + 2 * f₁ y * f₄ (x + y) + f y * f₅ (x + y)

private def mixedSecondSum4 (f f₁ f₂ _f₃ f₄ f₅ f₆ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₂ y * f₄ (x + y) + 2 * f₁ y * f₅ (x + y) + f y * f₆ (x + y)

private def mixedThirdSum0 (f f₁ f₂ f₃ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₃ y * f (x + y) + 3 * f₂ y * f₁ (x + y) +
    3 * f₁ y * f₂ (x + y) + f y * f₃ (x + y)

private def mixedThirdSum1 (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₃ y * f₁ (x + y) + 3 * f₂ y * f₂ (x + y) +
    3 * f₁ y * f₃ (x + y) + f y * f₄ (x + y)

private def mixedThirdSum2 (f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₃ y * f₂ (x + y) + 3 * f₂ y * f₃ (x + y) +
    3 * f₁ y * f₄ (x + y) + f y * f₅ (x + y)

private def mixedThirdSum3 (f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  f₃ y * f₃ (x + y) + 3 * f₂ y * f₄ (x + y) +
    3 * f₁ y * f₅ (x + y) + f y * f₆ (x + y)

private def diagonalFourthSum (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (z : ℝ) : ℝ :=
  3 * f₂ z ^ 2 + 4 * f₁ z * f₃ z + f z * f₄ z

private def diagonalFifthSum (f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ) (z : ℝ) : ℝ :=
  10 * f₂ z * f₃ z + 5 * f₁ z * f₄ z + f z * f₅ z

private def diagonalSixthSum (f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ) (z : ℝ) : ℝ :=
  10 * f₃ z ^ 2 + 15 * f₂ z * f₄ z + 6 * f₁ z * f₅ z + f z * f₆ z

/-- The mixed fourth jet `∂y²∂x² D(y,x)` of the three-point determinant path. -/
def threePointCorrelationDeterminantPathMixedFourthJet
    (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  2 * (f₂ x * mixedSecondSum0 f f₁ f₂ y x +
    2 * f₁ x * mixedSecondSum1 f f₁ f₂ f₃ y x +
      f x * mixedSecondSum2 f f₁ f₂ f₃ f₄ y x) -
    2 * f 0 * diagonalFourthSum f f₁ f₂ f₃ f₄ (x + y)

/-- The `x` derivative of the mixed fourth jet. -/
def threePointCorrelationDeterminantPathMixedFourthJetX
    (f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  2 * (f₃ x * mixedSecondSum0 f f₁ f₂ y x +
    3 * f₂ x * mixedSecondSum1 f f₁ f₂ f₃ y x +
      3 * f₁ x * mixedSecondSum2 f f₁ f₂ f₃ f₄ y x +
        f x * mixedSecondSum3 f f₁ f₂ f₃ f₄ f₅ y x) -
    2 * f 0 * diagonalFifthSum f f₁ f₂ f₃ f₄ f₅ (x + y)

/-- The `x,x` derivative of the mixed fourth jet. -/
def threePointCorrelationDeterminantPathMixedFourthJetXX
    (f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  2 * (f₄ x * mixedSecondSum0 f f₁ f₂ y x +
    4 * f₃ x * mixedSecondSum1 f f₁ f₂ f₃ y x +
      6 * f₂ x * mixedSecondSum2 f f₁ f₂ f₃ f₄ y x +
        4 * f₁ x * mixedSecondSum3 f f₁ f₂ f₃ f₄ f₅ y x +
          f x * mixedSecondSum4 f f₁ f₂ f₃ f₄ f₅ f₆ y x) -
    2 * f 0 * diagonalSixthSum f f₁ f₂ f₃ f₄ f₅ f₆ (x + y)

/-- The `y,x` derivative of the mixed fourth jet. -/
def threePointCorrelationDeterminantPathMixedFourthJetYX
    (f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  2 * (f₃ x * mixedThirdSum0 f f₁ f₂ f₃ y x +
    3 * f₂ x * mixedThirdSum1 f f₁ f₂ f₃ f₄ y x +
      3 * f₁ x * mixedThirdSum2 f f₁ f₂ f₃ f₄ f₅ y x +
        f x * mixedThirdSum3 f f₁ f₂ f₃ f₄ f₅ f₆ y x) -
    2 * f 0 * diagonalSixthSum f f₁ f₂ f₃ f₄ f₅ f₆ (x + y)

/-- The first `y` derivative of `∂x²D`. -/
def threePointCorrelationDeterminantPathSecondJetY
    (f f₁ f₂ f₃ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  2 * (f₂ x * (f₁ y * f (x + y) + f y * f₁ (x + y)) +
    2 * f₁ x * (f₁ y * f₁ (x + y) + f y * f₂ (x + y)) +
      f x * (f₁ y * f₂ (x + y) + f y * f₃ (x + y))) -
    2 * f 0 * (3 * f₁ (x + y) * f₂ (x + y) + f (x + y) * f₃ (x + y))

private theorem hasDerivAt_add_y
    {g g' : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (g' z) z) (x y : ℝ) :
    HasDerivAt (fun z => g (x + z)) (g' (x + y)) y := by
  convert (hg (x + y)).comp y ((hasDerivAt_const y x).add (hasDerivAt_id y)) using 1
  all_goals (dsimp; ring)

private theorem hasDerivAt_add_x
    {g g' : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (g' z) z) (x y : ℝ) :
    HasDerivAt (fun z => g (z + y)) (g' (x + y)) x := by
  simpa only [Function.comp_def, id_eq, mul_one] using
    (hg (x + y)).comp x ((hasDerivAt_id x).add_const y)

private theorem hasDerivAt_mixedSecondSum0_x
    {f f₁ f₂ f₃ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z) (y x : ℝ) :
    HasDerivAt (mixedSecondSum0 f f₁ f₂ y)
      (mixedSecondSum1 f f₁ f₂ f₃ y x) x := by
  unfold mixedSecondSum0 mixedSecondSum1
  convert (((hasDerivAt_add_x hf x y).mul_const (f₂ y)).add
    ((hasDerivAt_add_x hf₁ x y).mul_const (2 * f₁ y))).add
      ((hasDerivAt_add_x hf₂ x y).mul_const (f y)) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_mixedSecondSum1_x
    {f f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z) (y x : ℝ) :
    HasDerivAt (mixedSecondSum1 f f₁ f₂ f₃ y)
      (mixedSecondSum2 f f₁ f₂ f₃ f₄ y x) x := by
  unfold mixedSecondSum1 mixedSecondSum2
  convert (((hasDerivAt_add_x hf₁ x y).mul_const (f₂ y)).add
    ((hasDerivAt_add_x hf₂ x y).mul_const (2 * f₁ y))).add
      ((hasDerivAt_add_x hf₃ x y).mul_const (f y)) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_mixedSecondSum2_x
    {f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ}
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z) (y x : ℝ) :
    HasDerivAt (mixedSecondSum2 f f₁ f₂ f₃ f₄ y)
      (mixedSecondSum3 f f₁ f₂ f₃ f₄ f₅ y x) x := by
  unfold mixedSecondSum2 mixedSecondSum3
  convert (((hasDerivAt_add_x hf₂ x y).mul_const (f₂ y)).add
    ((hasDerivAt_add_x hf₃ x y).mul_const (2 * f₁ y))).add
      ((hasDerivAt_add_x hf₄ x y).mul_const (f y)) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_mixedSecondSum3_x
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z)
    (hf₅ : ∀ z, HasDerivAt f₅ (f₆ z) z) (y x : ℝ) :
    HasDerivAt (mixedSecondSum3 f f₁ f₂ f₃ f₄ f₅ y)
      (mixedSecondSum4 f f₁ f₂ f₃ f₄ f₅ f₆ y x) x := by
  unfold mixedSecondSum3 mixedSecondSum4
  convert (((hasDerivAt_add_x hf₃ x y).mul_const (f₂ y)).add
    ((hasDerivAt_add_x hf₄ x y).mul_const (2 * f₁ y))).add
      ((hasDerivAt_add_x hf₅ x y).mul_const (f y)) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_mixedSecondSum0_y
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (_hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (_hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z)
    (_hf₅ : ∀ z, HasDerivAt f₅ (f₆ z) z) (y x : ℝ) :
    HasDerivAt (fun z => mixedSecondSum0 f f₁ f₂ z x)
      (mixedThirdSum0 f f₁ f₂ f₃ y x) y := by
  unfold mixedSecondSum0 mixedThirdSum0
  convert ((((hf₂ y).mul (hasDerivAt_add_y hf x y)).add
    (((hf₁ y).mul (hasDerivAt_add_y hf₁ x y)).const_mul 2)).add
      ((hf y).mul (hasDerivAt_add_y hf₂ x y))) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_mixedSecondSum1_y
    {f f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z) (y x : ℝ) :
    HasDerivAt (fun z => mixedSecondSum1 f f₁ f₂ f₃ z x)
      (mixedThirdSum1 f f₁ f₂ f₃ f₄ y x) y := by
  unfold mixedSecondSum1 mixedThirdSum1
  convert ((((hf₂ y).mul (hasDerivAt_add_y hf₁ x y)).add
    (((hf₁ y).mul (hasDerivAt_add_y hf₂ x y)).const_mul 2)).add
      ((hf y).mul (hasDerivAt_add_y hf₃ x y))) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_mixedSecondSum2_y
    {f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z) (y x : ℝ) :
    HasDerivAt (fun z => mixedSecondSum2 f f₁ f₂ f₃ f₄ z x)
      (mixedThirdSum2 f f₁ f₂ f₃ f₄ f₅ y x) y := by
  unfold mixedSecondSum2 mixedThirdSum2
  convert ((((hf₂ y).mul (hasDerivAt_add_y hf₂ x y)).add
    (((hf₁ y).mul (hasDerivAt_add_y hf₃ x y)).const_mul 2)).add
      ((hf y).mul (hasDerivAt_add_y hf₄ x y))) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_mixedSecondSum3_y
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z)
    (hf₅ : ∀ z, HasDerivAt f₅ (f₆ z) z) (y x : ℝ) :
    HasDerivAt (fun z => mixedSecondSum3 f f₁ f₂ f₃ f₄ f₅ z x)
      (mixedThirdSum3 f f₁ f₂ f₃ f₄ f₅ f₆ y x) y := by
  unfold mixedSecondSum3 mixedThirdSum3
  convert ((((hf₂ y).mul (hasDerivAt_add_y hf₃ x y)).add
    (((hf₁ y).mul (hasDerivAt_add_y hf₄ x y)).const_mul 2)).add
      ((hf y).mul (hasDerivAt_add_y hf₅ x y))) using 1 <;>
    (try funext z) <;> dsimp <;> ring

private theorem hasDerivAt_diagonalFourthSum
    {f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z) (z : ℝ) :
    HasDerivAt (diagonalFourthSum f f₁ f₂ f₃ f₄)
      (diagonalFifthSum f f₁ f₂ f₃ f₄ f₅ z) z := by
  unfold diagonalFourthSum diagonalFifthSum
  convert (((((hf₂ z).mul (hf₂ z)).const_mul 3).add
    (((hf₁ z).mul (hf₃ z)).const_mul 4)).add ((hf z).mul (hf₄ z))) using 1 <;>
    (try funext w) <;> dsimp <;> ring

private theorem hasDerivAt_diagonalFifthSum
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z)
    (hf₅ : ∀ z, HasDerivAt f₅ (f₆ z) z) (z : ℝ) :
    HasDerivAt (diagonalFifthSum f f₁ f₂ f₃ f₄ f₅)
      (diagonalSixthSum f f₁ f₂ f₃ f₄ f₅ f₆ z) z := by
  unfold diagonalFifthSum diagonalSixthSum
  convert (((((hf₂ z).mul (hf₃ z)).const_mul 10).add
    (((hf₁ z).mul (hf₄ z)).const_mul 5)).add ((hf z).mul (hf₅ z))) using 1 <;>
    (try funext w) <;> dsimp <;> ring

theorem hasDerivAt_threePointCorrelationDeterminantPathMixedFourthJet_x
    {f f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z) (y x : ℝ) :
    HasDerivAt (threePointCorrelationDeterminantPathMixedFourthJet f f₁ f₂ f₃ f₄ y)
      (threePointCorrelationDeterminantPathMixedFourthJetX f f₁ f₂ f₃ f₄ f₅ y x) x := by
  unfold threePointCorrelationDeterminantPathMixedFourthJet
    threePointCorrelationDeterminantPathMixedFourthJetX
  have hS0 := hasDerivAt_mixedSecondSum0_x hf hf₁ hf₂ y x
  have hS1 := hasDerivAt_mixedSecondSum1_x (f := f) hf₁ hf₂ hf₃ y x
  have hS2 := hasDerivAt_mixedSecondSum2_x (f := f) (f₁ := f₁) hf₂ hf₃ hf₄ y x
  have hB := (hasDerivAt_diagonalFourthSum hf hf₁ hf₂ hf₃ hf₄ (x + y)).comp x
    ((hasDerivAt_id x).add_const y)
  convert (((((hf₂ x).mul hS0).add (((hf₁ x).mul hS1).const_mul 2)).add
    ((hf x).mul hS2)).const_mul 2).sub (hB.const_mul (2 * f 0)) using 1 <;>
    (try funext z) <;> dsimp <;> ring

theorem hasDerivAt_threePointCorrelationDeterminantPathMixedFourthJetX_x
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z)
    (hf₅ : ∀ z, HasDerivAt f₅ (f₆ z) z) (y x : ℝ) :
    HasDerivAt (threePointCorrelationDeterminantPathMixedFourthJetX f f₁ f₂ f₃ f₄ f₅ y)
      (threePointCorrelationDeterminantPathMixedFourthJetXX f f₁ f₂ f₃ f₄ f₅ f₆ y x) x := by
  unfold threePointCorrelationDeterminantPathMixedFourthJetX
    threePointCorrelationDeterminantPathMixedFourthJetXX
  have hS0 := hasDerivAt_mixedSecondSum0_x hf hf₁ hf₂ y x
  have hS1 := hasDerivAt_mixedSecondSum1_x (f := f) hf₁ hf₂ hf₃ y x
  have hS2 := hasDerivAt_mixedSecondSum2_x (f := f) (f₁ := f₁) hf₂ hf₃ hf₄ y x
  have hS3 := hasDerivAt_mixedSecondSum3_x (f := f) (f₁ := f₁) (f₂ := f₂)
    hf₃ hf₄ hf₅ y x
  have hB := (hasDerivAt_diagonalFifthSum hf hf₁ hf₂ hf₃ hf₄ hf₅ (x + y)).comp x
    ((hasDerivAt_id x).add_const y)
  convert ((((((hf₃ x).mul hS0).add (((hf₂ x).mul hS1).const_mul 3)).add
    (((hf₁ x).mul hS2).const_mul 3)).add ((hf x).mul hS3)).const_mul 2).sub
      (hB.const_mul (2 * f 0)) using 1 <;> (try funext z) <;> dsimp <;> ring

theorem hasDerivAt_threePointCorrelationDeterminantPathMixedFourthJetX_y
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z)
    (hf₅ : ∀ z, HasDerivAt f₅ (f₆ z) z) (y x : ℝ) :
    HasDerivAt (fun z => threePointCorrelationDeterminantPathMixedFourthJetX
      f f₁ f₂ f₃ f₄ f₅ z x)
      (threePointCorrelationDeterminantPathMixedFourthJetYX
        f f₁ f₂ f₃ f₄ f₅ f₆ y x) y := by
  unfold threePointCorrelationDeterminantPathMixedFourthJetX
    threePointCorrelationDeterminantPathMixedFourthJetYX
  have hS0 := hasDerivAt_mixedSecondSum0_y hf hf₁ hf₂ hf₃ hf₄ hf₅ y x
  have hS1 := hasDerivAt_mixedSecondSum1_y hf hf₁ hf₂ hf₃ y x
  have hS2 := hasDerivAt_mixedSecondSum2_y hf hf₁ hf₂ hf₃ hf₄ y x
  have hS3 := hasDerivAt_mixedSecondSum3_y hf hf₁ hf₂ hf₃ hf₄ hf₅ y x
  have hB := (hasDerivAt_diagonalFifthSum hf hf₁ hf₂ hf₃ hf₄ hf₅ (x + y)).comp y
    ((hasDerivAt_const y x).add (hasDerivAt_id y))
  have hmain := ((((hasDerivAt_const y (f₃ x)).mul hS0).add
    ((hasDerivAt_const y (3 * f₂ x)).mul hS1)).add
      ((hasDerivAt_const y (3 * f₁ x)).mul hS2)).add
        ((hasDerivAt_const y (f x)).mul hS3)
  convert (hmain.const_mul 2).sub (hB.const_mul (2 * f 0)) using 1
  all_goals (dsimp; ring)

theorem threePointCorrelationDeterminantPathMixedFourthJet_comm
    (f f₁ f₂ f₃ f₄ : ℝ → ℝ) (y x : ℝ) :
    threePointCorrelationDeterminantPathMixedFourthJet f f₁ f₂ f₃ f₄ y x =
      threePointCorrelationDeterminantPathMixedFourthJet f f₁ f₂ f₃ f₄ x y := by
  unfold threePointCorrelationDeterminantPathMixedFourthJet mixedSecondSum0 mixedSecondSum1
    mixedSecondSum2 diagonalFourthSum
  ring

theorem hasDerivAt_threePointCorrelationDeterminantPathSecondJet_y
    {f f₁ f₂ f₃ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z) (y x : ℝ) :
    HasDerivAt (fun z => threePointCorrelationDeterminantPathSecondJet f f₁ f₂ z x)
      (threePointCorrelationDeterminantPathSecondJetY f f₁ f₂ f₃ y x) y := by
  unfold threePointCorrelationDeterminantPathSecondJet
    threePointCorrelationDeterminantPathSecondJetY
  have hc0 := hasDerivAt_add_y hf x y
  have hc1 := hasDerivAt_add_y hf₁ x y
  have hc2 := hasDerivAt_add_y hf₂ x y
  have hA := ((hf y).mul hc0).mul_const (f₂ x)
  have hB := ((hf y).mul hc1).mul_const (2 * f₁ x)
  have hC := ((hf y).mul hc2).mul_const (f x)
  have hR := ((hc1.mul hc1).add (hc0.mul hc2)).const_mul (2 * f 0)
  have hmain := ((((hA.add hB).add hC).const_mul 2).sub hR).add_const
    (-2 * f 0 * (f₁ x ^ 2 + f x * f₂ x))
  convert hmain using 1 <;>
    (try funext z) <;> dsimp <;> ring

theorem hasDerivAt_threePointCorrelationDeterminantPathSecondJetY_y
    {f f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z) (y x : ℝ) :
    HasDerivAt (threePointCorrelationDeterminantPathSecondJetY f f₁ f₂ f₃ · x)
      (threePointCorrelationDeterminantPathMixedFourthJet f f₁ f₂ f₃ f₄ y x) y := by
  unfold threePointCorrelationDeterminantPathSecondJetY
    threePointCorrelationDeterminantPathMixedFourthJet mixedSecondSum0 mixedSecondSum1
    mixedSecondSum2 diagonalFourthSum
  have hc0 := hasDerivAt_add_y hf x y
  have hc1 := hasDerivAt_add_y hf₁ x y
  have hc2 := hasDerivAt_add_y hf₂ x y
  have hc3 := hasDerivAt_add_y hf₃ x y
  have hA := (((hf₁ y).mul hc0).add ((hf y).mul hc1)).mul_const (f₂ x)
  have hB := (((hf₁ y).mul hc1).add ((hf y).mul hc2)).mul_const (2 * f₁ x)
  have hC := (((hf₁ y).mul hc2).add ((hf y).mul hc3)).mul_const (f x)
  have hR := (((hc1.mul hc2).const_mul 3).add (hc0.mul hc3)).const_mul (2 * f 0)
  convert (((hA.add hB).add hC).const_mul 2).sub hR using 1 <;>
    (try funext z) <;> dsimp <;> ring

/-- The `(2,4)` and `(4,2)` sixth mixed determinant jets at the doubly coalesced corner.  The
sixth source jet cancels identically. -/
theorem threePointCorrelationDeterminantPathMixedFourthJetXX_zero
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (h₁ : f₁ 0 = 0) (h₃ : f₃ 0 = 0) :
    threePointCorrelationDeterminantPathMixedFourthJetXX
        f f₁ f₂ f₃ f₄ f₅ f₆ 0 0 =
      -12 * f₂ 0 * (f 0 * f₄ 0 - f₂ 0 ^ 2) := by
  simp [threePointCorrelationDeterminantPathMixedFourthJetXX, mixedSecondSum0,
    mixedSecondSum1, mixedSecondSum2, mixedSecondSum3, mixedSecondSum4,
    diagonalSixthSum, h₁, h₃]
  ring

/-- The central `(3,3)` sixth mixed determinant jet at the doubly coalesced corner. -/
theorem threePointCorrelationDeterminantPathMixedFourthJetYX_zero
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (h₁ : f₁ 0 = 0) (h₃ : f₃ 0 = 0) :
    threePointCorrelationDeterminantPathMixedFourthJetYX
        f f₁ f₂ f₃ f₄ f₅ f₆ 0 0 =
      -18 * f₂ 0 * (f 0 * f₄ 0 - f₂ 0 ^ 2) := by
  simp [threePointCorrelationDeterminantPathMixedFourthJetYX, mixedThirdSum0,
    mixedThirdSum1, mixedThirdSum2, mixedThirdSum3, diagonalSixthSum, h₁, h₃]
  ring

/-- A negative center second jet and strict fourth Hankel gap open one common positive determinant
square for both adjacent gaps. -/
theorem exists_threePointCorrelationDeterminantPath_pos_uniform_square
    {f f₁ f₂ f₃ f₄ f₅ f₆ : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (f₁ z) z)
    (hf₁ : ∀ z, HasDerivAt f₁ (f₂ z) z)
    (hf₂ : ∀ z, HasDerivAt f₂ (f₃ z) z)
    (hf₃ : ∀ z, HasDerivAt f₃ (f₄ z) z)
    (hf₄ : ∀ z, HasDerivAt f₄ (f₅ z) z)
    (hf₅ : ∀ z, HasDerivAt f₅ (f₆ z) z)
    (hf₆ : Continuous f₆)
    (h₁ : f₁ 0 = 0) (h₃ : f₃ 0 = 0)
    (h₂ : f₂ 0 < 0) (h₄ : 0 < f 0 * f₄ 0 - f₂ 0 ^ 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : ℝ, 0 < x → x < δ → 0 < y → y < δ →
      0 < threePointCorrelationDeterminantPath f y x := by
  let C := threePointCorrelationDeterminantPathMixedFourthJet f f₁ f₂ f₃ f₄
  let Cx := threePointCorrelationDeterminantPathMixedFourthJetX f f₁ f₂ f₃ f₄ f₅
  let Cxx := threePointCorrelationDeterminantPathMixedFourthJetXX f f₁ f₂ f₃ f₄ f₅ f₆
  let Cyx := threePointCorrelationDeterminantPathMixedFourthJetYX f f₁ f₂ f₃ f₄ f₅ f₆
  have hC_x : ∀ y x, HasDerivAt (C y) (Cx y x) x := fun y x =>
    hasDerivAt_threePointCorrelationDeterminantPathMixedFourthJet_x hf hf₁ hf₂ hf₃ hf₄ y x
  have hCx_x : ∀ y x, HasDerivAt (Cx y) (Cxx y x) x := fun y x =>
    hasDerivAt_threePointCorrelationDeterminantPathMixedFourthJetX_x
      hf hf₁ hf₂ hf₃ hf₄ hf₅ y x
  have hCx_y : ∀ y x, HasDerivAt (fun z => Cx z x) (Cyx y x) y := fun y x =>
    hasDerivAt_threePointCorrelationDeterminantPathMixedFourthJetX_y
      hf hf₁ hf₂ hf₃ hf₄ hf₅ y x
  have hC_y : ∀ y x, HasDerivAt (fun z => C z x) (Cx x y) y := by
    intro y x
    convert hC_x x y using 1
    · funext z
      exact threePointCorrelationDeterminantPathMixedFourthJet_comm f f₁ f₂ f₃ f₄ z x
  have hcont (g g' : ℝ → ℝ) (hg : ∀ z, HasDerivAt g (g' z) z) : Continuous g :=
    continuous_iff_continuousAt.mpr fun z => (hg z).continuousAt
  have hc0 := hcont f f₁ hf
  have hc1 := hcont f₁ f₂ hf₁
  have hc2 := hcont f₂ f₃ hf₂
  have hc3 := hcont f₃ f₄ hf₃
  have hc4 := hcont f₄ f₅ hf₄
  have hc5 := hcont f₅ f₆ hf₅
  have hCxxcont : Continuous (fun p : ℝ × ℝ => Cxx p.1 p.2) := by
    dsimp [Cxx]
    unfold threePointCorrelationDeterminantPathMixedFourthJetXX mixedSecondSum0
      mixedSecondSum1 mixedSecondSum2 mixedSecondSum3 mixedSecondSum4 diagonalSixthSum
    fun_prop
  have hCyxcont : Continuous (fun p : ℝ × ℝ => Cyx p.1 p.2) := by
    dsimp [Cyx]
    unfold threePointCorrelationDeterminantPathMixedFourthJetYX mixedThirdSum0
      mixedThirdSum1 mixedThirdSum2 mixedThirdSum3 diagonalSixthSum
    fun_prop
  have hCzero : C 0 0 = 0 := by
    simp [C, threePointCorrelationDeterminantPathMixedFourthJet, mixedSecondSum0,
      mixedSecondSum1, mixedSecondSum2, diagonalFourthSum, h₁]
    ring
  have hCxzero : Cx 0 0 = 0 := by
    simp [Cx, threePointCorrelationDeterminantPathMixedFourthJetX, mixedSecondSum0,
      mixedSecondSum1, mixedSecondSum2, mixedSecondSum3, diagonalFifthSum, h₁, h₃]
    ring
  have hCxxzero : Cxx 0 0 = -12 * f₂ 0 * (f 0 * f₄ 0 - f₂ 0 ^ 2) := by
    exact threePointCorrelationDeterminantPathMixedFourthJetXX_zero h₁ h₃
  have hCyxzero : Cyx 0 0 = -18 * f₂ 0 * (f 0 * f₄ 0 - f₂ 0 ^ 2) := by
    exact threePointCorrelationDeterminantPathMixedFourthJetYX_zero h₁ h₃
  have hCxxpos : 0 < Cxx 0 0 := by
    rw [hCxxzero]
    exact mul_pos (mul_pos_of_neg_of_neg (by norm_num) h₂) h₄
  have hCyxpos : 0 < Cyx 0 0 := by
    rw [hCyxzero]
    exact mul_pos (mul_pos_of_neg_of_neg (by norm_num) h₂) h₄
  rcases exists_pos_square_of_coordinateHessian_pos
      hC_y hC_x (fun y x => hCx_x x y) hCx_y hCx_x
      (hCxxcont.comp continuous_swap) hCyxcont hCxxcont
      hCzero hCxzero hCxzero hCxxpos hCyxpos hCxxpos with
    ⟨δ, hδ, hCpos⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hxδ hy hyδ
  let K := threePointCorrelationDeterminantPathSecondJet f f₁ f₂
  let Ky := threePointCorrelationDeterminantPathSecondJetY f f₁ f₂ f₃
  have hK : ∀ z, HasDerivAt (fun w => K w x) (Ky z x) z := fun z =>
    hasDerivAt_threePointCorrelationDeterminantPathSecondJet_y hf hf₁ hf₂ z x
  have hKy : ∀ z, HasDerivAt (fun w => Ky w x) (C z x) z := fun z =>
    hasDerivAt_threePointCorrelationDeterminantPathSecondJetY_y hf hf₁ hf₂ hf₃ z x
  have hKzero : K 0 x = 0 := by
    simp [K, threePointCorrelationDeterminantPathSecondJet]
    ring
  have hKyzero : Ky 0 x = 0 := by
    simp [Ky, threePointCorrelationDeterminantPathSecondJetY, h₁]
    ring
  have hKpos : 0 < K y x := by
    exact pos_right_of_secondJet_posOn hK hKy hKzero hKyzero hδ
      (fun z hz => by
        have hz' : 0 < z ∧ z < δ := by
          simpa [interior_Icc, hδ.ne'] using hz
        exact hCpos z x hz'.1 hz'.2 hx hxδ) y hy hyδ
  let D := threePointCorrelationDeterminantPath f y
  let Dx := threePointCorrelationDeterminantPathFirstJet f f₁ y
  have hD : ∀ z, HasDerivAt D (Dx z) z := fun z =>
    hasDerivAt_threePointCorrelationDeterminantPath hf y z
  have hDx : ∀ z, HasDerivAt Dx (K y z) z := fun z =>
    hasDerivAt_threePointCorrelationDeterminantPathFirstJet hf hf₁ y z
  have hDzero : D 0 = 0 := by
    simp [D, threePointCorrelationDeterminantPath, threePointCorrelationDeterminant]
    ring
  have hDxzero : Dx 0 = 0 := by
    simp [Dx, threePointCorrelationDeterminantPathFirstJet, h₁]
    ring
  exact pos_right_of_secondJet_posOn hD hDx hDzero hDxzero hδ
    (fun z hz => by
      have hz' : 0 < z ∧ z < δ := by
        simpa [interior_Icc, hδ.ne'] using hz
      exact pos_right_of_secondJet_posOn
        (fun w => hasDerivAt_threePointCorrelationDeterminantPathSecondJet_y hf hf₁ hf₂ w z)
        (fun w => hasDerivAt_threePointCorrelationDeterminantPathSecondJetY_y
          hf hf₁ hf₂ hf₃ w z)
        (by simp [threePointCorrelationDeterminantPathSecondJet]; ring)
        (by simp [threePointCorrelationDeterminantPathSecondJetY, h₁]; ring)
        hδ (fun w hw => by
          have hw' : 0 < w ∧ w < δ := by
            simpa [interior_Icc, hδ.ne'] using hw
          exact hCpos w z hw'.1 hw'.2 hz'.1 hz'.2) y hy hyδ) x hx hxδ

end

end HilbertMetric
