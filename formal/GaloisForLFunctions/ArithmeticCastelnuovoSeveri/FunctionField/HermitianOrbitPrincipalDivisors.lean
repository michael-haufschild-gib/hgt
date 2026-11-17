import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianFrobeniusReturnTimes
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricDivisorDegree

/-!
# Principal functions along periodic Hermitian orbits

With square-field Frobenius denoted by F, the tangent at a divisor D
represents FD + QD after subtracting degrees at infinity. Iterating along
the finite orbits in the support gives an explicit principal multiple of
every degree-zero point divisor, including those with nonrational support.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Function
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "Q" => p ^ (s + 1)
local notation "H" => HermitianGeometricField p s
local notation "Pts" => HermitianGeometricPoint p s
local notation "Fr" => hermitianGeometricPointFrobenius p s
local notation "F" => hermitianGeometricFrobeniusDivisor p s
local notation "D₀" => hermitianGeometricDegreeZeroPart p s
local notation "divH" => hermitianGeometricPrincipalDivisorHom p s

/-- Infinity has period one. Affine points have their joint coordinate degree as period. -/
def hermitianPointOrbitDegree : Pts → ℕ
  | none => 1
  | some P => hermitianOrbitDegree p s P

private theorem point_degree_period (P : Pts) :
    IsPeriodicPt Fr (hermitianPointOrbitDegree p s P) P := by
  cases P with
  | none => exact (show IsFixedPt Fr none from rfl).isPeriodicPt _
  | some P =>
    exact ((hermitianFrobenius_return_iff p s P _).2 dvd_rfl).map
      (show Semiconj some _ Fr from fun _ => rfl)

private theorem point_degree_pos (P : Pts) : 0 < hermitianPointOrbitDegree p s P := by
  cases P with
  | none => exact Nat.one_pos
  | some P => exact hermitianOrbitDegree_pos p s P

/-- A common return time for the entire signed support, independent of its multiplicities. -/
def hermitianSupportPeriod (D : Pts →₀ ℤ) : ℕ :=
  D.support.lcm (hermitianPointOrbitDegree p s)

/-- Iterating the divisor map transports every coefficient by the corresponding point iterate. -/
theorem hermitianFrobeniusDivisor_iterate (D : Pts →₀ ℤ) (n : ℕ) :
    F^[n] D = Finsupp.mapDomain (Fr^[n]) D := by
  induction n with
  | zero => exact Finsupp.mapDomain_id.symm
  | succ n ih =>
    rw [iterate_succ_apply', ih, hermitianGeometricFrobeniusDivisor,
      ← Finsupp.mapDomain_comp, iterate_succ']

theorem hermitianSupportPeriod_pos (D : Pts →₀ ℤ) : 0 < hermitianSupportPeriod p s D := by
  classical
  unfold hermitianSupportPeriod
  exact Nat.pos_of_ne_zero fun hz => by
    obtain ⟨i, _, hi⟩ := Finset.lcm_eq_zero_iff.mp hz
    exact (point_degree_pos p s i).ne' hi

/-- Every signed divisor returns, with a period bounded by the lcm of its closed point degrees. -/
theorem hermitianFrobeniusDivisor_support_period (D : Pts →₀ ℤ) :
    IsPeriodicPt F (hermitianSupportPeriod p s D) D := by
  change F^[_] D = D
  rw [hermitianFrobeniusDivisor_iterate]
  refine Eq.trans ?_ (Finsupp.mapDomain_id (v := D))
  exact Finsupp.mapDomain_congr fun P hP =>
    (point_degree_period p s P).trans_dvd (Finset.dvd_lcm hP)

/-- Alternating powers of tangents telescope along the orbit of a signed divisor. -/
def hermitianOrbitTangent (D : Pts →₀ ℤ) : ℕ → Additive Hˣ
  | 0 => 0
  | n + 1 => Additive.ofMul (hermitianGeometricTangentProduct p s (F^[n] D)) +
      (-((Q : ℕ) : ℤ)) • hermitianOrbitTangent D n

/-- The orbit product realizes the difference of the iterated divisor and its scalar prediction. -/
theorem hermitianOrbitTangent_divisor (D : Pts →₀ ℤ) (n : ℕ) :
    divH (hermitianOrbitTangent p s D n) =
      D₀ (F^[n] D) - (-((Q : ℕ) : ℤ)) ^ n • D₀ D := by
  induction n with
  | zero => simp [hermitianOrbitTangent]
  | succ n ih =>
    let T := F^[n] D
    have hT : divH (Additive.ofMul (hermitianGeometricTangentProduct p s T)) =
      ((Q : ℕ) : ℤ) • D₀ T + D₀ (F T) := hermitianGeometricTangentProduct_divisor p s T
    rw [hermitianOrbitTangent, map_add, map_zsmul, hT, ih, smul_sub, smul_smul,
      ← pow_succ', iterate_succ_apply', neg_smul]
    change _ + _ + (-(((Q : ℕ) : ℤ) • D₀ T) - _) = _
    abel

/-- A single return of length d gives the sharper signed annihilator 1 - (-Q)^d. -/
theorem hermitianOrbitTangent_support_divisor (D : Pts →₀ ℤ) :
    divH (hermitianOrbitTangent p s D (hermitianSupportPeriod p s D)) =
      (1 - (-((Q : ℕ) : ℤ)) ^ hermitianSupportPeriod p s D) • D₀ D := by
  rw [hermitianOrbitTangent_divisor, (hermitianFrobeniusDivisor_support_period p s D).isFixedPt.eq,
    sub_smul, one_smul]

/-- Over the even return field a positive multiple Q^(2d)-1 is principal with an explicit witness. -/
theorem hermitianEvenOrbit_principal (D : Pts →₀ ℤ) :
    divH (-hermitianOrbitTangent p s D (2 * hermitianSupportPeriod p s D)) =
      (((Q : ℕ) : ℤ) ^ (2 * hermitianSupportPeriod p s D) - 1) • D₀ D := by
  rw [map_neg, hermitianOrbitTangent_divisor,
    ((hermitianFrobeniusDivisor_support_period p s D).const_mul 2).isFixedPt.eq,
    Even.neg_pow (even_two_mul _), sub_smul, one_smul, neg_sub]

#print axioms hermitianFrobeniusDivisor_iterate
#print axioms hermitianSupportPeriod_pos
#print axioms hermitianFrobeniusDivisor_support_period
#print axioms hermitianOrbitTangent_divisor
#print axioms hermitianOrbitTangent_support_divisor
#print axioms hermitianEvenOrbit_principal

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
