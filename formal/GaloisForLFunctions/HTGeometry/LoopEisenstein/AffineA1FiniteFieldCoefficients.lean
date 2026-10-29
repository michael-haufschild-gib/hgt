import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticZetaContinuation
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1XiCoefficients

/-!
# Finite-field zeta coefficients for affine A₁

The base is the proved genus-one curve over `𝔽₃`. Its arithmetic zeta ratio
replaces the rational-field completed-zeta ratio in the finite product over
affine inversion roots. The two simple-reflection coefficients have genuine
poles inherited from the curve's Frobenius zeros, with their full multiplicities.
The volume scalar `3^(length(w)(1−g))` is one because the geometric genus is one.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1

open ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- The genus-one finite-field Gindikin–Karpelevich coefficient formula. -/
def finiteFieldCoefficient (lam : ℂ × ℂ) (w : Weyl) : ℂ :=
  ∏ β ∈ inversions w, arithmeticZetaRatio (rootArgument lam β)

theorem finiteFieldCoefficient_one (lam : ℂ × ℂ) : finiteFieldCoefficient lam 1 = 1 := by
  simp only [finiteFieldCoefficient, inversions_one, Finset.prod_empty]

theorem finiteFieldCoefficient_finiteReflection (lam : ℂ × ℂ) :
    finiteFieldCoefficient lam finiteReflection = arithmeticZetaRatio lam.2 := by
  simp [finiteFieldCoefficient, rootArgument, Root.corootZero, Root.corootOne]

theorem finiteFieldCoefficient_affineReflection (lam : ℂ × ℂ) :
    finiteFieldCoefficient lam affineReflection = arithmeticZetaRatio lam.1 := by
  simp [finiteFieldCoefficient, rootArgument, Root.corootZero, Root.corootOne]

/-- In either simple-coroot direction, the denominator zeros survive with exact order. -/
theorem simpleCoefficient_orders (a s : ℂ)
    (hs : numerator.eval (zetaCoordinate (s + 1)) = 0) :
    meromorphicOrderAt (fun t => finiteFieldCoefficient (a, t) finiteReflection) s =
        -((numerator.rootMultiplicity (zetaCoordinate (s + 1)) : ℤ) : WithTop ℤ) ∧
      meromorphicOrderAt (fun t => finiteFieldCoefficient (t, a) affineReflection) s =
        -((numerator.rootMultiplicity (zetaCoordinate (s + 1)) : ℤ) : WithTop ℤ) := by
  simp only [finiteFieldCoefficient_finiteReflection, finiteFieldCoefficient_affineReflection]
  exact ⟨arithmeticZetaRatio_order_at_zero s hs, arithmeticZetaRatio_order_at_zero s hs⟩

/-- Actual Frobenius roots supply poles; no noncancellation hypothesis is assumed. -/
theorem simpleCoefficient_poles (a : ℂ) (i : FrobeniusIndex) :
    (arithmeticPoleParameter i).re = -(1 / 2 : ℝ) ∧
      meromorphicOrderAt
        (fun t => finiteFieldCoefficient (a, t) finiteReflection) (arithmeticPoleParameter i) < 0 ∧
      meromorphicOrderAt
        (fun t => finiteFieldCoefficient (t, a) affineReflection) (arithmeticPoleParameter i) < 0 := by
  simp only [finiteFieldCoefficient_finiteReflection, finiteFieldCoefficient_affineReflection]
  exact ⟨(arithmeticPoleParameter_spec i).1,
    (arithmeticPoleParameter_spec i).2, (arithmeticPoleParameter_spec i).2⟩

/-- Both simple coefficient formulas have arithmetic poles for every fixed other coordinate. -/
theorem simpleCoefficient_has_poles (a : ℂ) :
    ∃ s : ℂ, s.re = -(1 / 2 : ℝ) ∧
      meromorphicOrderAt (fun t => finiteFieldCoefficient (a, t) finiteReflection) s < 0 ∧
      meromorphicOrderAt (fun t => finiteFieldCoefficient (t, a) affineReflection) s < 0 := by
  have hn : Nonempty FrobeniusIndex := Fintype.card_pos_iff.mp (by
    rw [card_frobeniusIndex]
    norm_num)
  obtain ⟨i⟩ := hn
  exact ⟨arithmeticPoleParameter i, simpleCoefficient_poles a i⟩

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineA1
