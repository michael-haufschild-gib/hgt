import GaloisForLFunctions.RHTower.Sieve.MaynardComplementaryMontgomeryFiniteSet
import GaloisForLFunctions.RHTower.Sieve.MaynardOverweightCountExponents

/-!
# Scalar geometry of complementary Montgomery

After taking the square root of one height-dominated and one length-dominated mean square, the
count exponent in the local-height base is

`(1 + r + mu * (1 - 2 * alpha)) / 2`,

where `r` is the logarithmic length of the long side.  This module classifies that mixed term
exactly.  Through amplitude `997/1000`, every failure of Route T's first two receivers is a genuine
single-giant geometry: the long side is above height and its complement is below height.  Thus the
entire low-ordinate obstruction is not a diffuse moment problem; it is one explicit crossing seam.
-/

noncomputable section
namespace RHTower.Sieve

/-- Mixed complementary-Montgomery count exponent, in the height base. -/
def maynardComplementaryMixedCountExponent (mu alpha r : ℝ) : ℝ :=
  (1 + r + mu * (1 - 2 * alpha)) / 2

/-- If the long side leaves at least one full height in its complement, the mixed term is already
Route T's first alternative. -/
theorem complementaryMixed_le_first_of_complement_ge_height
    {mu alpha r : ℝ} (hr : r ≤ mu - 1) :
    maynardComplementaryMixedCountExponent mu alpha r ≤ mu * (1 - alpha) := by
  dsimp only [maynardComplementaryMixedCountExponent]
  linarith

/-- If the long side is below the exact second-receiver threshold, the mixed term is Route T's
second alternative. -/
theorem complementaryMixed_le_second_of_long_le
    {mu alpha r : ℝ}
    (hr : r ≤ 1 + mu * (1 + 2 * routeTGapMomentNu - 2 * alpha)) :
    maynardComplementaryMixedCountExponent mu alpha r ≤
      1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  dsimp only [maynardComplementaryMixedCountExponent]
  linarith

/-- Exact three-way scalar classification, with no range hypotheses. -/
theorem complementaryMixed_first_or_second_or_crossing
    (mu alpha r : ℝ) :
    maynardComplementaryMixedCountExponent mu alpha r ≤ mu * (1 - alpha) ∨
      maynardComplementaryMixedCountExponent mu alpha r ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) ∨
      (mu - 1 < r ∧
        1 + mu * (1 + 2 * routeTGapMomentNu - 2 * alpha) < r) := by
  by_cases hfirst : r ≤ mu - 1
  · exact Or.inl (complementaryMixed_le_first_of_complement_ge_height hfirst)
  by_cases hsecond : r ≤ 1 + mu * (1 + 2 * routeTGapMomentNu - 2 * alpha)
  · exact Or.inr (Or.inl (complementaryMixed_le_second_of_long_le hsecond))
  · exact Or.inr (Or.inr ⟨lt_of_not_ge hfirst, lt_of_not_ge hsecond⟩)

/-- In the complete middle-amplitude band, a residual mixed term has an over-height long side and
a sub-height complement.  No upper bound on `mu` is used. -/
theorem complementaryMixed_first_or_second_or_giant_middle
    {mu alpha r : ℝ}
    (hmu : 4 / 3 ≤ mu) (halpha : alpha ≤ 997 / 1000) :
    maynardComplementaryMixedCountExponent mu alpha r ≤ mu * (1 - alpha) ∨
      maynardComplementaryMixedCountExponent mu alpha r ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) ∨
      (1 < r ∧ mu - r < 1) := by
  rcases complementaryMixed_first_or_second_or_crossing mu alpha r with
    hfirst | hsecond | ⟨hcomplement, hlong⟩
  · exact Or.inl hfirst
  · exact Or.inr (Or.inl hsecond)
  · right
    right
    have hd : maynardLongGlobalAmplitudeDeficit < (1 / 1000000 : ℝ) :=
      maynardLongGlobalAmplitudeDeficit_lt_one_millionth
    have hcoef : 0 < 1 + 2 * routeTGapMomentNu - 2 * alpha := by
      dsimp only [routeTGapMomentNu]
      linarith
    have hmu0 : 0 < mu := lt_of_lt_of_le (by norm_num) hmu
    have hpositive : 0 < mu * (1 + 2 * routeTGapMomentNu - 2 * alpha) :=
      mul_pos hmu0 hcoef
    exact ⟨by linarith, by linarith⟩

/-- A residual mixed term is impossible whenever both complementary sides lie on the same side of
height.  This is the receiver-facing no-diffuse-obstruction statement. -/
theorem complementaryMixed_first_or_second_of_not_giant_middle
    {mu alpha r : ℝ}
    (hmu : 4 / 3 ≤ mu) (halpha : alpha ≤ 997 / 1000)
    (hnotGiant : r ≤ 1 ∨ 1 ≤ mu - r) :
    maynardComplementaryMixedCountExponent mu alpha r ≤ mu * (1 - alpha) ∨
      maynardComplementaryMixedCountExponent mu alpha r ≤
        1 + mu * (1 + routeTGapMomentNu - 2 * alpha) := by
  rcases complementaryMixed_first_or_second_or_giant_middle hmu halpha with
    hfirst | hsecond | hgiant
  · exact Or.inl hfirst
  · exact Or.inr hsecond
  · rcases hnotGiant with hlong | hcomplement
    · exact (not_lt_of_ge hlong hgiant.1).elim
    · exact (not_lt_of_ge hcomplement hgiant.2).elim

end RHTower.Sieve
