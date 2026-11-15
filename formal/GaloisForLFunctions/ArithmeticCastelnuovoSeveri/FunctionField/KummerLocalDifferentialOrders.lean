import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerLocalDerivation
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.TameValuationDerivatives
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerOriginFunctionOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerPlaceClassification

/-!
# Differential orders at the Kummer origin and infinity

Frobenius expansions make differentiation in a local parameter integral.
The tame order rule then gives order `Q` for `dy` at the origin and
pole order `Q+2` at infinity. Both statements use normalized valuations
of the actual function field and its Kähler-derived local derivation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis

private theorem coveringDegree_cast_ne_zero
    (p : ℕ) [Fact p.Prime] (s : ℕ) :
    ((p ^ (s + 1) + 1 : ℕ) : SquareConstantField p s) ≠ 0 := by
  rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow, CharP.cast_eq_zero (SquareConstantField p s) p,
    zero_pow (Nat.succ_ne_zero s), zero_add]
  exact one_ne_zero

/-- The normalized local derivation lowers positive orders prime to the characteristic by one. -/
theorem squareKummerUniformizerDerivation_order
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
    (v : Valuation (SquareKummerField p s c b R) (WithZero (Multiplicative ℤ)))
    (hK : ∀ a : SquareConstantField p s,
      v (algebraMap (SquareConstantField p s) (SquareKummerField p s c b R) a) ≤ 1)
    (π : SquareKummerField p s c b R) (hπ : v π = WithZero.exp (-1 : ℤ))
    (x : SquareKummerField p s c b R) (e : ℕ) (he : 0 < e)
    (hx : v x = WithZero.exp (-(e : ℤ))) (heK : (e : SquareConstantField p s) ≠ 0) :
    v (squareKummerUniformizerDerivation p s c b R π x) = WithZero.exp (-((e - 1 : ℕ) : ℤ)) := by
  apply valuation_derivation_of_tame_order v _ π hπ
    (squareKummerUniformizerDerivation_self p s c b R v π hπ)
    (squareKummerUniformizerDerivation_integral p s c b R v π hπ) x e he hx
  simpa only [map_natCast] using valuation_constant_eq_one_of_constants_mem v hK
    (e : SquareConstantField p s) heK

/-- At the origin, `dy` has order `Q` in the radical uniformizer. -/
theorem squareKummerOrigin_derivative_coordinate
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ) :
    squareKummerOriginValuation p s c b R
      (squareKummerUniformizerDerivation p s c b R
        (AdjoinRoot.root (kummerBranchFieldPolynomial c b R (p ^ (s + 1))))
        (algebraMap (SquareConstantField p s)[X] (SquareKummerField p s c b R) X)) =
          WithZero.exp (-((p ^ (s + 1) : ℕ) : ℤ)) := by
  have h := squareKummerUniformizerDerivation_order p s c b R (squareKummerOriginValuation p s c b R)
    (heightOne_constants_mem (squareKummerOriginPlace p s c b R))
    _ (squareKummerOriginValuation_root p s c b R) _ (p ^ (s + 1) + 1) (Nat.succ_pos _)
    (squareKummerOriginValuation_coordinate p s c b R) (coveringDegree_cast_ne_zero p s)
  simpa only [Nat.add_sub_cancel] using h

/-- Transport the existing Dedekind uniformizer from the infinity normalization chart. -/
def squareKummerInfinityUniformizer
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ) :
    SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) :=
  (kummerInfinityFieldEquiv c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))).symm
    (GaloisForLFunctions.HTGeometry.placeUniformizer
      (KummerInfinityField c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1)))
      (squareKummerInfinityPlace p s c d r))

/-- The transported infinity parameter has normalized order one. -/
theorem squareKummerInfinityUniformizer_value
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ) :
    squareKummerInfinityValuation p s c d r (squareKummerInfinityUniformizer p s c d r) =
      WithZero.exp (-1 : ℤ) := by
  let e := kummerInfinityFieldEquiv c (p ^ (d + 1) - 2)
    (kummerExponent (p ^ (d + 1)) r) (p ^ (s + 1))
  change (squareKummerInfinityPlace p s c d r).valuation _ (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  exact GaloisForLFunctions.HTGeometry.placeUniformizer_valuation _ _

/-- At infinity, `dy` has pole order `Q+2`. -/
theorem squareKummerInfinity_derivative_coordinate
    (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (d r : ℕ) :
    squareKummerInfinityValuation p s c d r
      (squareKummerUniformizerDerivation p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)
        (squareKummerInfinityUniformizer p s c d r)
        (algebraMap (SquareConstantField p s)[X]
          (SquareKummerField p s c (p ^ (d + 1) - 2) (kummerExponent (p ^ (d + 1)) r)) X)) =
            WithZero.exp (((p ^ (s + 1) + 2 : ℕ) : ℤ)) := by
  let K := SquareConstantField p s
  let b := p ^ (d + 1) - 2
  let R := kummerExponent (p ^ (d + 1)) r
  let L := SquareKummerField p s c b R
  let N := p ^ (s + 1) + 1
  let v := squareKummerInfinityValuation p s c d r
  let π := squareKummerInfinityUniformizer p s c d r
  let y := algebraMap K[X] L X
  let D := squareKummerUniformizerDerivation p s c b R π
  have hy : v y = WithZero.exp (N : ℤ) := squareKummerInfinityValuation_coordinate p s c d r
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have hinv : v y⁻¹ = WithZero.exp (-(N : ℤ)) := by
    rw [map_inv₀, hy, ← WithZero.exp_neg]
  have hDinv : v (D y⁻¹) = WithZero.exp (-((N - 1 : ℕ) : ℤ)) :=
    squareKummerUniformizerDerivation_order p s c b R v
      (squareKummerInfinityConstantPlace p s c d r).property.2 π
      (squareKummerInfinityUniformizer_value p s c d r) y⁻¹ N (Nat.succ_pos _) hinv
      (coveringDegree_cast_ne_zero p s)
  have hchain : D y⁻¹ = -(y⁻¹) ^ 2 * D y := by
    simpa only [smul_eq_mul] using D.leibniz_of_mul_eq_one (inv_mul_cancel₀ hy0)
  have hv := congrArg v hchain
  rw [hDinv, map_mul, v.map_neg, map_pow, hinv, ← WithZero.exp_nsmul] at hv
  have hfinal : v (D y) = WithZero.exp ((N : ℤ) + 1) := by
    apply mul_left_cancel₀ (show WithZero.exp (2 • (-(N : ℤ))) ≠ 0 from WithZero.exp_ne_zero)
    rw [← hv, ← WithZero.exp_add]
    congr 1
    have hsub : ((N - 1 : ℕ) : ℤ) + 1 = N := by
      exact_mod_cast Nat.sub_add_cancel (Nat.succ_pos (p ^ (s + 1)))
    simp only [nsmul_eq_mul]
    omega
  simpa only [N, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, add_assoc, one_add_one_eq_two] using hfinal

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
