import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeSteinbergObstruction
import GaloisForLFunctions.HTGeometry.CommonFactorKoszulHomology

/-!
# The scalar Kummer regulator in prime coordinates

The actual rational-scaling regulator is the logarithm-weighted sum of prime
moments. Its prime-coordinate kernel has a complete complex basis indexed by
primes other than two: `e_p - (log p / log 2) e_2`. The weighted Finsupp splitting
gives an explicit linear equivalence from arbitrary finite combinations of these
relations to the whole kernel.
-/

open scoped TensorProduct
noncomputable section
namespace RHTower
open GaloisForLFunctions.RHTower GaloisForLFunctions.HTGeometry

def deningerLogLinear : Additive CCMRationalAdelicScaling →ₗ[ℤ] ℂ :=
  AddMonoidHom.toIntLinearMap {
    toFun g := ccmRationalAdelicKummerLogWeight g.toMul
    map_zero' := by
      change ccmRationalAdelicKummerLogWeight 1 = 0
      simp [ccmRationalAdelicKummerLogWeight]
    map_add' g h := ccmRationalAdelicKummerLogWeight_mul g.toMul h.toMul }

def deningerLogMoment : DeningerMomentSpace →ₗ[ℂ] ℂ :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton ℂ _ deningerLogLinear)

theorem deningerLogMoment_tmul (z : ℂ) (g : Additive CCMRationalAdelicScaling) :
    deningerLogMoment (z ⊗ₜ[ℤ] g) = z * ccmRationalAdelicKummerLogWeight g.toMul := rfl

def deningerPrimeLogUnit (p : Nat.Primes) : ℂˣ :=
  Units.mk0 (Real.log (p : ℝ) : ℂ) (by
    rw [Ne, Complex.ofReal_eq_zero]
    exact Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.ne_one))

def deningerPrimeLog : (Nat.Primes →₀ ℂ) →ₗ[ℂ] ℂ :=
  unitWeightedFinsuppAugmentation deningerPrimeLogUnit

@[simp] theorem deningerPrimeLog_single (p : Nat.Primes) (z : ℂ) :
    deningerPrimeLog (Finsupp.single p z) = (Real.log (p : ℝ) : ℂ) * z :=
  unitWeightedFinsuppAugmentation_single _ _ _

theorem deningerPrimeMomentEquiv_prime (p : Nat.Primes) :
    deningerPrimeMomentEquiv ((1 : ℂ) ⊗ₜ[ℤ]
      Additive.ofMul (⟨deningerPrimeUnit p⟩ : CCMRationalAdelicScaling)) = Finsupp.single p 1 := by
  classical
  ext q
  rw [deningerPrimeMomentEquiv_label]
  change (padicValRat (q : ℕ) (deningerPrimeUnit p : ℚ) : ℂ) = _
  rw [deningerPadicValRat_primeUnit]
  by_cases h : p = q <;> simp [h, eq_comm]

/-- Prime generators determine the logarithmic functional on the scaling moment space. -/
theorem deningerPrimeLog_eq_logMoment :
    deningerPrimeLog = deningerLogMoment.comp deningerPrimeMomentEquiv.symm.toLinearMap := by
  apply (Finsupp.basisSingleOne : Module.Basis Nat.Primes ℂ (Nat.Primes →₀ ℂ)).ext
  intro p
  change deningerPrimeLog (Finsupp.single p 1) =
    deningerLogMoment (deningerPrimeMomentEquiv.symm (Finsupp.single p 1))
  rw [deningerPrimeLog_single, mul_one, ← deningerPrimeMomentEquiv_prime,
    LinearEquiv.symm_apply_apply, deningerLogMoment_tmul, one_mul]
  simp [ccmRationalAdelicKummerLogWeight, deningerPrimeUnit_val]

/-- The native regulator retains the logarithm-weighted sum of ordinary prime moments. -/
theorem deningerKummerRegulator_eq_primeLog :
    deningerKummerRegulator = deningerPrimeLog.comp deningerPrimeMoment := by
  apply (MonoidAlgebra.basis CCMRationalAdelicScaling ℂ).ext
  intro g
  change deningerKummerRegulator (deningerSteinbergBasis g) =
    deningerPrimeLog (deningerPrimeMoment (deningerSteinbergBasis g))
  rw [deningerKummerRegulator_basis, deningerPrimeLog_eq_logMoment]
  change ccmRationalAdelicKummerLogWeight g = deningerLogMoment
    (deningerPrimeMomentEquiv.symm (deningerPrimeMomentEquiv
      (GroupAlgebraFirstJet.jet ℂ CCMRationalAdelicScaling (MonoidAlgebra.of ℂ _ g)).snd))
  rw [LinearEquiv.symm_apply_apply, GroupAlgebraFirstJet.jet_of]
  change ccmRationalAdelicKummerLogWeight g =
    deningerLogMoment ((1 : ℂ) ⊗ₜ[ℤ] Additive.ofMul g)
  rw [deningerLogMoment_tmul, one_mul]
  rfl

def deningerPrimeLogPivot : Nat.Primes := ⟨2, Nat.prime_two⟩
abbrev DeningerPrimeLogAway := unitWeightedFinsuppAway deningerPrimeLogPivot

def deningerPrimeLogKernelEquiv :
    (DeningerPrimeLogAway →₀ ℂ) ≃ₗ[ℂ] deningerPrimeLog.ker :=
  unitWeightedFinsuppAwayEquivRelations deningerPrimeLogUnit deningerPrimeLogPivot

/-- The prime relations normalized at two form a complete complex basis. -/
def deningerPrimeLogKernelBasis : Module.Basis DeningerPrimeLogAway ℂ deningerPrimeLog.ker :=
  unitWeightedFinsuppRelationsBasis deningerPrimeLogUnit deningerPrimeLogPivot

theorem deningerPrimeLogKernelBasis_apply (p : DeningerPrimeLogAway) :
    (deningerPrimeLogKernelBasis p).val = Finsupp.single p.val 1 -
      Finsupp.single deningerPrimeLogPivot
        ((Real.log (p.val : ℝ) : ℂ) / (Real.log (2 : ℝ) : ℂ)) := by
  refine (unitWeightedFinsuppRelationsBasis_apply deningerPrimeLogUnit deningerPrimeLogPivot p).trans ?_
  simp only [unitWeightedFinsuppRelationVector, deningerPrimeLogUnit,
    deningerPrimeLogPivot, Units.val_mk0, Units.val_inv_eq_inv_val, div_eq_mul_inv, Nat.cast_ofNat]

#print axioms deningerKummerRegulator_eq_primeLog
#print axioms deningerPrimeLogKernelEquiv
#print axioms deningerPrimeLogKernelBasis_apply
end RHTower
