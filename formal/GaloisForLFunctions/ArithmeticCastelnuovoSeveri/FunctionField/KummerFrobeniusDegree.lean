import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerCharacteristic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusPowerField
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFieldGenerators
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginFunctionOrders
import Mathlib.LinearAlgebra.FiniteDimensional.Basic


/-!
# Frobenius degree of the Kummer function field

The origin order `Q+1` excludes the coordinate from the `p`th-power field.
Since `Q+1 = p·p^s+1`, the radical is recovered from the coordinate by
`z = f(y)/(z^(p^s))^p`. Hence the coordinate generates the whole function
field over its Frobenius subfield, and that extension has degree `p`.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped IntermediateField
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)

/-- The Frobenius subfield of the actual Kummer function field. -/
abbrev SquareKummerFrobeniusField :=
  frobeniusPowerField (SquareConstantField p s) (SquareKummerField p s c b R) p

/-- The coordinate is not a `p`th power, since its origin order is prime to `p`. -/
theorem squareKummer_coordinate_not_frobenius :
    algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X ∉
      SquareKummerFrobeniusField p s c b R := by
  rintro ⟨x, hx⟩
  change x ^ p = algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X at hx
  have h := congrArg (fun x => WithZero.log (squareKummerOriginValuation p s c b R x)) hx
  rw [map_pow, WithZero.log_pow, squareKummerOriginValuation_coordinate,
    WithZero.log_exp, nsmul_eq_mul] at h
  have hd : (p : ℤ) ∣ -((p ^ (s + 1) + 1 : ℕ) : ℤ) :=
    ⟨WithZero.log (squareKummerOriginValuation p s c b R x), h.symm⟩
  have hd' : p ∣ p ^ (s + 1) + 1 := Int.natCast_dvd_natCast.mp (dvd_neg.mp hd)
  obtain ⟨k, hk⟩ := hd'
  have hz : ((p ^ (s + 1) + 1 : ℕ) : SquareConstantField p s) = 0 := by
    rw [hk, Nat.cast_mul, CharP.cast_eq_zero (SquareConstantField p s) p, zero_mul]
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, CharP.cast_eq_zero (SquareConstantField p s) p,
    zero_pow (Nat.succ_ne_zero s), zero_add] at hz
  exact one_ne_zero hz

/-- The coordinate generates the Kummer field over its Frobenius subfield. -/
theorem squareKummer_frobenius_adjoin_coordinate :
    (SquareKummerFrobeniusField p s c b R)⟮algebraMap (SquareConstantField p s)[X]
      (SquareKummerField p s c b R) X⟯ = ⊤ := by
  let K := SquareConstantField p s
  let F := FractionRing K[X]
  let L := SquareKummerField p s c b R
  let P := SquareKummerFrobeniusField p s c b R
  let y := algebraMap K[X] L X
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1)))
  let S := P⟮y⟯
  let S' := S.restrictScalars K
  have hy : y ∈ S' := IntermediateField.mem_adjoin_simple_self P y
  have hnum : algebraMap K[X] L (kummerBranch c b R) ∈ S' := by
    rw [IsScalarTower.algebraMap_apply K[X] F L]
    exact kummerBranchField_base_mem_of_coordinate_mem c b R (p ^ (s + 1)) S' hy _
  have hden : (z ^ (p ^ s)) ^ p ∈ S' :=
    S.algebraMap_mem (frobeniusPowerElement K L p (z ^ (p ^ s)))
  have hz0 : z ≠ 0 := kummerBranchField_root_ne_zero c b R (p ^ (s + 1))
  have hrecover : z = algebraMap K[X] L (kummerBranch c b R) / (z ^ (p ^ s)) ^ p := by
    apply (eq_div_iff (pow_ne_zero _ (pow_ne_zero _ hz0))).mpr
    rw [← pow_mul, ← pow_succ', ← pow_succ p s]
    exact (kummerBranchField_root_pow c b R (p ^ (s + 1))).trans
      (IsScalarTower.algebraMap_apply K[X] F L _).symm
  have hz : z ∈ S' := by
    rw [hrecover]
    exact S'.div_mem hnum hden
  have htop := kummerBranchField_eq_top_of_coordinate_root_mem c b R (p ^ (s + 1)) S' hy hz
  apply top_unique
  intro x _
  have hx : x ∈ S' := by rw [htop]; trivial
  exact hx

/-- The actual Kummer field has Frobenius degree exactly the characteristic. -/
theorem squareKummer_frobenius_finrank :
    Module.finrank (SquareKummerFrobeniusField p s c b R) (SquareKummerField p s c b R) = p := by
  let K := SquareConstantField p s
  let L := SquareKummerField p s c b R
  let P := SquareKummerFrobeniusField p s c b R
  let y := algebraMap K[X] L X
  have h := frobeniusPowerField_adjoin_finrank K L p y
    (squareKummer_coordinate_not_frobenius p s c b R)
  rw [squareKummer_frobenius_adjoin_coordinate] at h
  exact (IntermediateField.topEquiv.toLinearEquiv.finrank_eq).symm.trans h

/-- The Kummer field is finite-dimensional over its Frobenius subfield. -/
instance squareKummer_frobenius_finiteDimensional :
    FiniteDimensional (SquareKummerFrobeniusField p s c b R) (SquareKummerField p s c b R) :=
  FiniteDimensional.of_finrank_pos (by
    rw [squareKummer_frobenius_finrank]
    exact (Fact.out : p.Prime).pos)

/-- Every uniformizer generates the actual Kummer field over its Frobenius subfield. -/
theorem squareKummer_frobenius_adjoin_uniformizer
    (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ)) :
    (SquareKummerFrobeniusField p s c b R)⟮π⟯ = ⊤ := by
  let K := SquareConstantField p s
  let L := SquareKummerField p s c b R
  let P := SquareKummerFrobeniusField p s c b R
  have hd : Module.finrank P P⟮π⟯ = p :=
    frobeniusPowerField_adjoin_finrank K L p π
      (frobeniusPowerField_uniformizer_notMem K L p v π hπ)
  letI : FiniteDimensional P L := squareKummer_frobenius_finiteDimensional p s c b R
  have hdim : Module.finrank P P⟮π⟯ = Module.finrank P L :=
    hd.trans (squareKummer_frobenius_finrank p s c b R).symm
  have htop : P⟮π⟯.toSubalgebra.toSubmodule = ⊤ :=
    Submodule.eq_top_of_finrank_eq hdim
  apply top_unique
  intro x _
  have hx : x ∈ P⟮π⟯.toSubalgebra.toSubmodule := by rw [htop]; trivial
  exact hx

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
