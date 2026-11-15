import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerSeparatingPowerBasis
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.FrobeniusPowerFieldEquiv

/-!
# Frobenius coefficient extraction on Kummer differentials

The coordinate power basis expands a differential uniquely as
`Σ aᵢ^p y^i dy`. Extracting `a_(p-1) dy` is additive and satisfies
Frobenius inverse semilinearity. The construction uses the actual
Kähler module and the actual Frobenius subfield of the Kummer field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
variable (p : ℕ) [Fact p.Prime] (s : ℕ) (c : (SquareConstantField p s)ˣ) (b R : ℕ)
local notation "K" => SquareConstantField p s
local notation "L" => SquareKummerField p s c b R
local notation "Ω" => KaehlerDifferential K L
local notation "P" => SquareKummerFrobeniusField p s c b R
local notation "dy" => KaehlerDifferential.D K L (algebraMap K[X] L X)

private def topFrobeniusIndex : Fin p :=
  ⟨p - 1, Nat.sub_lt (Fact.out : p.Prime).pos Nat.zero_lt_one⟩

/-- The highest Frobenius coordinate of a differential, with its unique Frobenius root extracted. -/
def squareKummerCoordinateCartier : Ω →+ Ω where
  toFun ω := (show L ≃+* P from frobeniusPowerFieldEquiv K L p).symm
    ((squareKummerCoordinatePowerBasis p s c b R).repr
      (squareKummerDifferentialEquiv p s c b R ω) (topFrobeniusIndex p)) • dy
  map_zero' := by
    let E : Ω ≃ₗ[L] L := squareKummerDifferentialEquiv p s c b R
    let B : Module.Basis (Fin p) P L := squareKummerCoordinatePowerBasis p s c b R
    let F : L ≃+* P := frobeniusPowerFieldEquiv K L p
    let j := topFrobeniusIndex p
    change F.symm (B.repr (E 0) j) • dy = 0
    have hc : B.repr (E 0) j = 0 :=
      (congrArg (fun x : L => B.repr x j) E.map_zero).trans
        (congrArg (fun a : Fin p →₀ P => a j) B.repr.map_zero)
    rw [hc, F.symm.map_zero, zero_smul]
  map_add' ω η := by
    let E : Ω ≃ₗ[L] L := squareKummerDifferentialEquiv p s c b R
    let B : Module.Basis (Fin p) P L := squareKummerCoordinatePowerBasis p s c b R
    let F : L ≃+* P := frobeniusPowerFieldEquiv K L p
    let j := topFrobeniusIndex p
    change F.symm (B.repr (E (ω + η)) j) • dy =
      F.symm (B.repr (E ω) j) • dy + F.symm (B.repr (E η) j) • dy
    have hc : B.repr (E (ω + η)) j = B.repr (E ω) j + B.repr (E η) j :=
      (congrArg (fun x : L => B.repr x j) (E.map_add ω η)).trans
        (congrArg (fun a : Fin p →₀ P => a j) (B.repr.map_add (E ω) (E η)))
    exact (congrArg (fun a : P => F.symm a • dy) hc).trans
      ((congrArg (fun a : L => a • dy) (F.symm.map_add _ _)).trans (add_smul _ _ dy))

/-- Frobenius coefficient extraction turns multiplication by a `p`th power into multiplication by its root. -/
theorem squareKummerCoordinateCartier_frobenius_smul (a : L) (ω : Ω) :
    squareKummerCoordinateCartier p s c b R (a ^ p • ω) =
      a • squareKummerCoordinateCartier p s c b R ω := by
  let E : Ω ≃ₗ[L] L := squareKummerDifferentialEquiv p s c b R
  let B : Module.Basis (Fin p) P L := squareKummerCoordinatePowerBasis p s c b R
  let F : L ≃+* P := frobeniusPowerFieldEquiv K L p
  let j := topFrobeniusIndex p
  let aP : P := frobeniusPowerElement K L p a
  have hE : E (a ^ p • ω) = aP • E ω := E.map_smul (a ^ p) ω
  have hc : B.repr (E (a ^ p • ω)) j = aP * B.repr (E ω) j :=
    (congrArg (fun x : L => B.repr x j) hE).trans
      (congrArg (fun u : Fin p →₀ P => u j) (B.repr.map_smul aP (E ω)))
  change F.symm (B.repr (E (a ^ p • ω)) j) • dy =
    a • (F.symm (B.repr (E ω) j) • dy)
  rw [hc, F.symm.map_mul]
  have hroot : F.symm aP = a := frobeniusPowerFieldEquiv_symm_element K L p a
  rw [hroot, mul_smul]

/-- Frobenius coefficient extraction selects exactly the highest coordinate power. -/
theorem squareKummerCoordinateCartier_power (i : Fin p) :
    squareKummerCoordinateCartier p s c b R
      ((algebraMap K[X] L X) ^ i.val • dy) =
        if i.val = p - 1 then dy else 0 := by
  classical
  let E : Ω ≃ₗ[L] L := squareKummerDifferentialEquiv p s c b R
  let B : Module.Basis (Fin p) P L := squareKummerCoordinatePowerBasis p s c b R
  let F : L ≃+* P := frobeniusPowerFieldEquiv K L p
  let j := topFrobeniusIndex p
  have he : E ((algebraMap K[X] L X) ^ i.val • dy) = B i := by
    rw [map_smul, squareKummerDifferentialEquiv_D_polynomial, derivative_X,
      map_one, smul_eq_mul, mul_one, squareKummerCoordinatePowerBasis_apply]
  change F.symm (B.repr (E ((algebraMap K[X] L X) ^ i.val • dy)) j) • dy = _
  rw [he, Module.Basis.repr_self, Finsupp.single_apply]
  by_cases h : j = i
  · have hi : i.val = p - 1 := (congrArg Fin.val h).symm
    simp only [if_pos h.symm, if_pos hi, map_one, one_smul]
  · have hi : i.val ≠ p - 1 := fun hi => h (Fin.ext hi.symm)
    simp only [if_neg (Ne.symm h), if_neg hi, map_zero, zero_smul]

/-- Every exact Kähler differential has zero highest Frobenius coefficient. -/
theorem squareKummerCoordinateCartier_D (f : L) :
    squareKummerCoordinateCartier p s c b R (KaehlerDifferential.D K L f) = 0 := by
  classical
  let D := KaehlerDifferential.D K L
  obtain ⟨a, ha⟩ := squareKummer_coordinate_power_expansion p s c b R f
  rw [ha, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change squareKummerCoordinateCartier p s c b R
    (D (a i ^ p * (algebraMap K[X] L X) ^ i.val)) = 0
  rw [D.leibniz, derivation_frobenius_power_eq_zero p D (a i),
    smul_zero, add_zero, D.leibniz_pow, squareKummerCoordinateCartier_frobenius_smul,
    map_nsmul]
  by_cases hi : i.val = 0
  · rw [hi, zero_nsmul, smul_zero]
  · let j : Fin p := ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
    have hj : j.val ≠ p - 1 := by dsimp only [j]; omega
    change a i • (i.val • squareKummerCoordinateCartier p s c b R
      ((algebraMap K[X] L X) ^ j.val • dy)) = 0
    rw [squareKummerCoordinateCartier_power, if_neg hj, nsmul_zero, smul_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
