import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalSubcover

/-!
# The three-point coordinate

Passing from `y` to `t=y^m` gives a radical equation with branch support
at zero, one and infinity. The original coordinate is recovered from
`t` and the radical, and the new coordinate is transcendental.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable {K : Type*} [Field K] (c : Kˣ) (b R n : ℕ)

/-- Raising the original coordinate to the degree of its nonlinear branch factor. -/
def kummerMonomialCoordinate : KummerBranchField c b R n :=
  algebraMap K[X] (KummerBranchField c b R n) X ^ (b + 1)

private theorem coordinate_equation :
    AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ^ (n + 1) =
      algebraMap K (KummerBranchField c b R n) c *
        algebraMap K[X] (KummerBranchField c b R n) X *
          (1 - kummerMonomialCoordinate c b R n) ^ R := by
  have h := kummerBranchField_root_pow c b R n
  rw [← IsScalarTower.algebraMap_apply, kummerBranch, map_mul, map_mul,
    map_pow, map_sub, map_one, map_pow] at h
  have hc : algebraMap K[X] (KummerBranchField c b R n) (C (c : K)) =
      algebraMap K (KummerBranchField c b R n) c :=
    (IsScalarTower.algebraMap_apply K K[X] (KummerBranchField c b R n) c).symm
  rw [hc] at h
  exact h

/-- The same radical satisfies a three-point equation of degree `N(b+1)` over the power coordinate. -/
theorem kummerBranchField_threePoint_equation :
    AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ^ ((n + 1) * (b + 1)) =
      algebraMap K (KummerBranchField c b R n) ((c : K) ^ (b + 1)) *
        kummerMonomialCoordinate c b R n *
          (1 - kummerMonomialCoordinate c b R n) ^ (R * (b + 1)) := by
  simpa only [pow_mul, mul_pow, map_pow, kummerMonomialCoordinate] using
    congrArg (fun x : KummerBranchField c b R n => x ^ (b + 1)) (coordinate_equation c b R n)

/-- The original coordinate is recovered rationally from the power coordinate and the radical. -/
theorem kummerBranchField_coordinate_recover :
    algebraMap K[X] (KummerBranchField c b R n) X =
      AdjoinRoot.root (kummerBranchFieldPolynomial c b R n) ^ (n + 1) /
        (algebraMap K (KummerBranchField c b R n) c *
          (1 - kummerMonomialCoordinate c b R n) ^ R) := by
  let L := KummerBranchField c b R n
  let y := algebraMap K[X] L X
  let z := AdjoinRoot.root (kummerBranchFieldPolynomial c b R n)
  let u := algebraMap K L c * (1 - kummerMonomialCoordinate c b R n) ^ R
  have hz : z ^ (n + 1) = y * u := by
    rw [coordinate_equation]
    dsimp only [y, u]
    ring
  have hu : u ≠ 0 := by
    intro h
    rw [h, mul_zero] at hz
    exact (pow_ne_zero _ (kummerBranchField_root_ne_zero c b R n)) hz
  exact (eq_div_iff hu).mpr hz.symm

/-- The power coordinate is a genuine transcendental rational parameter. -/
theorem kummerMonomialCoordinate_transcendental :
    Transcendental K (kummerMonomialCoordinate c b R n) := by
  intro h
  apply kummerBranchField_coordinate_transcendental c b R n
  exact (IsIntegral.of_pow (Nat.succ_pos b) h.isIntegral).isAlgebraic

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
