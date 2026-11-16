import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianLocalValuations
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerPrescribedResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SquareKummerExtensionOrders

/-!
# Normalized valuations at every geometric Hermitian point

At a nonzero radical coordinate, a root-of-unity automorphism selects the
prescribed residue and unramifiedness gives the coordinate order. At zero,
the simple branch equation makes the radical a uniformizer directly.
Thus every geometric point has an actual normalized valuation with first
coordinate difference of order one and both coordinate residues prescribed.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "B" => HermitianGeometricNormalization p s
local notation "η" => hermitianExtensionTraceConstant p s E
local notation "u" => hermitianExtensionAdditiveCoordinate p s E
local notation "z" => hermitianExtensionRadicalCoordinate p s E

private theorem transported_constant (w : HeightOneSpectrum B)
    (V : Valuation H (WithZero (Multiplicative ℤ)))
    (hbase : ∀ f : E[X], V (algebraMap E[X] H f) = w.valuation H (algebraMap E[X] H f))
    (c : E) (hc : c ≠ 0) : V (algebraMap E H c) = 1 := by
  rw [IsScalarTower.algebraMap_apply E E[X] H, hbase,
    ← IsScalarTower.algebraMap_apply E E[X] H]
  exact heightOne_valuation_constant w c hc

private theorem additive_shift (b : E) :
    u - algebraMap E H b = algebraMap E H ((η : E)⁻¹) *
      algebraMap E[X] H (X - C ((η : E) * b)) := by
  rw [hermitianExtensionAdditiveCoordinate, map_sub, mul_sub,
    ← IsScalarTower.algebraMap_apply E E[X] H, ← map_mul]
  congr 1
  rw [← mul_assoc, inv_mul_cancel₀ (hermitianExtensionTraceConstant p s E).ne_zero, one_mul]

private theorem transported_additive (P : HermitianAffinePoint p s E)
    (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver (Ideal.span {X - C (hermitianGeometricBaseCoordinate p s P)})]
    (V : Valuation H (WithZero (Multiplicative ℤ)))
    (hbase : ∀ f : E[X], V (algebraMap E[X] H f) = w.valuation H (algebraMap E[X] H f)) :
    V (u - algebraMap E H P.val.2) =
      WithZero.exp (-((Ideal.span {X - C (hermitianGeometricBaseCoordinate p s P)}).ramificationIdx'
        w.asIdeal : ℤ)) := by
  rw [additive_shift, map_mul,
    transported_constant p s w V hbase _ (inv_ne_zero (hermitianExtensionTraceConstant p s E).ne_zero),
    one_mul, hbase]
  exact squareKummerExtension_valuation_linear p s E η⁻¹ (Q - 2) 1
    (hermitianGeometricBaseCoordinate p s P) w

/-- Every geometric point admits a normalized valuation with the stated residues and uniformizer. -/
theorem hermitianGeometricPoint_exists_valuation (P : HermitianAffinePoint p s E) :
    ∃ V : Valuation H (WithZero (Multiplicative ℤ)),
      Function.Surjective V ∧
      (∀ c : E, c ≠ 0 → V (algebraMap E H c) = 1) ∧
      V (z - algebraMap E H P.val.1) = WithZero.exp (-1 : ℤ) ∧
      V (u - algebraMap E H P.val.2) < 1 := by
  by_cases hP : P.val.1 = 0
  · obtain ⟨w, hw⟩ := squareKummerExtension_exists_primeAbove p s E η⁻¹ (Q - 2) 1
      (GaloisForLFunctions.HTGeometry.polyPlace
        (irreducible_X_sub_C (hermitianGeometricBaseCoordinate p s P)))
    change w.asIdeal.LiesOver (Ideal.span {X - C (hermitianGeometricBaseCoordinate p s P)}) at hw
    letI := hw
    refine ⟨w.valuation H, w.valuation_surjective H,
      fun c hc => heightOne_valuation_constant w c hc, ?_, ?_⟩
    · rw [hP, map_zero, sub_zero]
      exact squareKummerExtension_valuation_root_simple p s E η⁻¹ (Q - 2) 1
        (hermitianGeometricBaseCoordinate p s P)
        (hermitianGeometricPoint_branchMultiplicity p s P hP) w
    · rw [transported_additive p s P w (w.valuation H) (fun _ => rfl),
        hermitianGeometricPoint_totallyRamified p s P hP w,
        ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
  · obtain ⟨w, V, hw, hsurj, hbase, hz⟩ :=
      squareKummerExtension_exists_prescribed_valuation p s E η⁻¹ (Q - 2) 1
        (hermitianGeometricBaseCoordinate p s P) P.val.1 hP
        (hermitianGeometricPoint_branch p s P).symm
    letI := hw
    have hc := transported_constant p s w V hbase
    have hu : V (u - algebraMap E H P.val.2) = WithZero.exp (-1 : ℤ) := by
      rw [transported_additive p s P w V hbase,
        hermitianGeometricPoint_unramified p s P hP w, Nat.cast_one]
    have husmall : V (u - algebraMap E H P.val.2) < 1 := by
      rw [hu, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    refine ⟨V, hsurj, hc, ?_, husmall⟩
    exact (hermitianPoint_coordinate_valuation_eq p s H V
      (hermitianGeometricConstantPoint p s P) (hermitianExtensionGenericPoint p s E)
      (hc P.val.1 hP) hz husmall).trans hu

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
