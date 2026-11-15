import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerDifferentialKernel

/-!
# Frobenius power bases in a separating coordinate

Any function with nonzero differential generates the field over its
Frobenius subfield. Its first `p` powers are consequently a basis.
In particular the original rational coordinate gives unique Frobenius
coefficients without choosing a valuation or a local uniformizer.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- Adjoining any non-Frobenius function recovers the actual Kummer field. -/
def squareKummerSeparatingAdjoinEquiv
    (x : SquareKummerField p s c b R) (hx : x ∉ SquareKummerFrobeniusField p s c b R) :
    (SquareKummerFrobeniusField p s c b R)⟮x⟯ ≃ₐ[SquareKummerFrobeniusField p s c b R]
      SquareKummerField p s c b R := by
  refine AlgEquiv.ofBijective
    (IntermediateField.val ((SquareKummerFrobeniusField p s c b R)⟮x⟯)) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext h
  · intro a
    refine ⟨⟨a, ?_⟩, rfl⟩
    rw [squareKummer_frobenius_adjoin_of_notMem p s c b R x hx]
    trivial

/-- The first `p` powers of a separating function form a basis over actual `p`th powers. -/
def squareKummerSeparatingBasis
    (x : SquareKummerField p s c b R) (hx : x ∉ SquareKummerFrobeniusField p s c b R) :
    Module.Basis (Fin p) (SquareKummerFrobeniusField p s c b R) (SquareKummerField p s c b R) := by
  let K := SquareConstantField p s
  let L := SquareKummerField p s c b R
  let P := SquareKummerFrobeniusField p s c b R
  have hint : IsIntegral P x := GaloisForLFunctions.HTGeometry.isIntegral_of_pow_mem (Fact.out : p.Prime).pos
    (show x ^ p = algebraMap P L (frobeniusPowerElement K L p x) from rfl)
  let pb := IntermediateField.adjoin.powerBasis hint
  have hd : pb.dim = p := pb.finrank.symm.trans (frobeniusPowerField_adjoin_finrank K L p x hx)
  exact (pb.basis.map (squareKummerSeparatingAdjoinEquiv p s c b R x hx).toLinearEquiv).reindex
    (finCongr hd)

/-- The separating basis consists of the literal powers of its chosen function. -/
theorem squareKummerSeparatingBasis_apply
    (x : SquareKummerField p s c b R) (hx : x ∉ SquareKummerFrobeniusField p s c b R)
    (i : Fin p) : squareKummerSeparatingBasis p s c b R x hx i = x ^ i.val := by
  dsimp only [squareKummerSeparatingBasis]
  simp only [Module.Basis.reindex_apply, Module.Basis.map_apply,
    PowerBasis.basis_eq_pow, AlgEquiv.toLinearEquiv_apply, map_pow,
    IntermediateField.adjoin.powerBasis_gen, finCongr_symm, finCongr_apply, Fin.val_cast]; rfl

/-- The original rational coordinate has nonzero differential and is outside the Frobenius subfield. -/
theorem squareKummer_coordinate_notMem_frobenius :
    algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X ∉
      SquareKummerFrobeniusField p s c b R := by
  intro h
  have hz := (squareKummerCoordinateDerivation_eq_zero_iff p s c b R _).mpr h
  rw [squareKummerCoordinateDerivation_polynomial, derivative_X, map_one] at hz
  exact one_ne_zero hz

/-- The original rational coordinate gives a Frobenius basis independent of any local parameter choice. -/
def squareKummerCoordinatePowerBasis :
    Module.Basis (Fin p) (SquareKummerFrobeniusField p s c b R) (SquareKummerField p s c b R) :=
  squareKummerSeparatingBasis p s c b R
    (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X)
    (squareKummer_coordinate_notMem_frobenius p s c b R)

/-- The coordinate basis is the sequence `1,y,…,y^(p-1)`. -/
theorem squareKummerCoordinatePowerBasis_apply (i : Fin p) :
    squareKummerCoordinatePowerBasis p s c b R i =
      (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) ^ i.val :=
  squareKummerSeparatingBasis_apply p s c b R _ _ i

/-- Every function has an expansion in coordinate powers with actual Frobenius roots as coefficients. -/
theorem squareKummer_coordinate_power_expansion (x : SquareKummerField p s c b R) :
    ∃ a : Fin p → SquareKummerField p s c b R,
      x = ∑ i : Fin p, a i ^ p *
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X) ^ i.val := by
  classical
  let B := squareKummerCoordinatePowerBasis p s c b R
  have hc : ∀ i : Fin p, ∃ a : SquareKummerField p s c b R,
      a ^ p = (B.repr x i : SquareKummerField p s c b R) := fun i => (B.repr x i).property
  choose a ha using hc
  refine ⟨a, ?_⟩
  calc
    x = ∑ i : Fin p, B.repr x i • B i := (B.sum_repr x).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [squareKummerCoordinatePowerBasis_apply, Algebra.smul_def]
      change (B.repr x i : SquareKummerField p s c b R) * _ = a i ^ p * _
      rw [ha i]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
