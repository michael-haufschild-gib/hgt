/-
Exact unitary transport of the even Sonin Euler corner to a Hardy--Titchmarsh boundary model.

Grade: BRIDGE.  The source Hilbert realization is universally quantified by a unitary `u`; no
intertwining hypothesis is left to the caller.  The boundary carrier is the actual image of the
even Sonin carrier, and its cutoff is its actual orthogonal projection.  The one-prime source
factor is the unitary push of `I - p⁻¹ᐟ² U_p*`; its Gram operator is the positive Euler weight.
-/
import GaloisForLFunctions.RHTower.SoninEvenCarrier

noncomputable section

open scoped InnerProduct InnerProductSpace

namespace RHTower

section UnitaryTransport

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Push an endomorphism through a unitary equivalence. -/
def unitaryPush (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) : K →L[ℂ] K :=
  (u : H →L[ℂ] K) ∘L T ∘L (u.symm : K →L[ℂ] H)

@[simp] theorem unitaryPush_apply (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) (x : K) :
    unitaryPush u T x = u (T (u.symm x)) := rfl

@[simp] theorem unitaryPush_one (u : H ≃ₗᵢ[ℂ] K) :
    unitaryPush u (1 : H →L[ℂ] H) = 1 := by
  ext x
  simp [unitaryPush]

@[simp] theorem unitaryPush_add (u : H ≃ₗᵢ[ℂ] K) (A B : H →L[ℂ] H) :
    unitaryPush u (A + B) = unitaryPush u A + unitaryPush u B := by
  ext x
  simp [unitaryPush]

@[simp] theorem unitaryPush_sub (u : H ≃ₗᵢ[ℂ] K) (A B : H →L[ℂ] H) :
    unitaryPush u (A - B) = unitaryPush u A - unitaryPush u B := by
  ext x
  simp [unitaryPush]

@[simp] theorem unitaryPush_smul (u : H ≃ₗᵢ[ℂ] K) (c : ℂ) (A : H →L[ℂ] H) :
    unitaryPush u (c • A) = c • unitaryPush u A := by
  ext x
  simp [unitaryPush]

@[simp] theorem unitaryPush_mul (u : H ≃ₗᵢ[ℂ] K) (A B : H →L[ℂ] H) :
    unitaryPush u (A * B) = unitaryPush u A * unitaryPush u B := by
  ext x
  simp [unitaryPush, ContinuousLinearMap.mul_apply]

@[simp] theorem adjoint_unitaryPush [CompleteSpace H] [CompleteSpace K]
    (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    (unitaryPush u T)† = unitaryPush u (T†) := by
  simp only [unitaryPush, ContinuousLinearMap.adjoint_comp]
  rw [LinearIsometryEquiv.adjoint_eq_symm u,
    LinearIsometryEquiv.adjoint_eq_symm u.symm]
  rw [LinearIsometryEquiv.symm_symm]
  rw [ContinuousLinearMap.comp_assoc]

theorem adjoint_one_sub_real_smul_unitary_symm [CompleteSpace H]
    (u : H ≃ₗᵢ[ℂ] H) (c : ℝ) :
    (1 - (c : ℂ) • (u.symm : H →L[ℂ] H))† =
      1 - (c : ℂ) • (u : H →L[ℂ] H) := by
  let adj : (H →L[ℂ] H) ≃ₗᵢ⋆[ℂ] (H →L[ℂ] H) :=
    ContinuousLinearMap.adjoint
  change adj (1 - (c : ℂ) • (u.symm : H →L[ℂ] H)) = _
  rw [map_sub adj, adj.map_smulₛₗ, ContinuousLinearMap.adjoint_one,
    LinearIsometryEquiv.adjoint_eq_symm]
  simp

@[simp] theorem conjugateOperator_unitaryPush
    (u : H ≃ₗᵢ[ℂ] K) (T : H →L[ℂ] H) :
    conjugateOperator u.toContinuousLinearEquiv (unitaryPush u T) = T := by
  ext x
  simp [conjugateOperator, unitaryPush]

theorem unitaryPush_crossBoundary
    (u : H ≃ₗᵢ[ℂ] K) (Q T : H →L[ℂ] H) :
    unitaryPush u (crossBoundary Q T) =
      crossBoundary (unitaryPush u Q) (unitaryPush u T) := by
  simp [crossBoundary]

end UnitaryTransport

/-! The physical one-prime factor and its Gram operator on the even Sonin model. -/

/-- `U_p + U_p^*` on the even physical model. -/
def evenDilationUnitarySum (p : ℝ) (hp : 1 < p) :
    evenSubspace →L[ℂ] evenSubspace :=
  (evenDilationUnitary p (zero_lt_one.trans hp) : evenSubspace →L[ℂ] evenSubspace) +
    ((evenDilationUnitary p (zero_lt_one.trans hp)).symm :
      evenSubspace →L[ℂ] evenSubspace)

theorem evenDilationUnitarySum_eq_evenDilationSum (p : ℝ) (hp : 1 < p) :
    evenDilationUnitarySum p hp = evenDilationSum p hp := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  simp [evenDilationUnitarySum, evenDilationSum, dilationSum_apply]

/-- The local factor `1 - p^{-1/2-is}` in the physical model:
`I - p^{-1/2} U_p^*`. -/
def evenPrimeLocalFactor (p : ℝ) (hp : 1 < p) :
    evenSubspace →L[ℂ] evenSubspace :=
  (1 : evenSubspace →L[ℂ] evenSubspace) -
    ((Real.sqrt p : ℂ)⁻¹) •
      ((evenDilationUnitary p (zero_lt_one.trans hp)).symm :
        evenSubspace →L[ℂ] evenSubspace)

/-- The positive Euler weight `|1-p^{-1/2-is}|²` in the physical model. -/
def evenPositiveEulerOperator (p : ℝ) (hp : 1 < p) :
    evenSubspace →L[ℂ] evenSubspace :=
  ((1 + p⁻¹ : ℝ) : ℂ) • (1 : evenSubspace →L[ℂ] evenSubspace) +
    (-((Real.sqrt p : ℂ)⁻¹)) • evenDilationSum p hp

theorem evenPrimeLocalFactor_adjoint_comp_self (p : ℝ) (hp : 1 < p) :
    (evenPrimeLocalFactor p hp)† * evenPrimeLocalFactor p hp =
      evenPositiveEulerOperator p hp := by
  let U : evenSubspace ≃ₗᵢ[ℂ] evenSubspace :=
    evenDilationUnitary p (zero_lt_one.trans hp)
  have hcoeff :
      (Real.sqrt p : ℂ)⁻¹ = (((Real.sqrt p)⁻¹ : ℝ) : ℂ) := by
    norm_cast
  have hsqrt_sq :
      ((((Real.sqrt p)⁻¹ : ℝ) : ℂ)) * ((((Real.sqrt p)⁻¹ : ℝ) : ℂ)) =
      ((p⁻¹ : ℝ) : ℂ) := by
    norm_cast
    rw [← mul_inv]
    rw [Real.mul_self_sqrt (le_of_lt (zero_lt_one.trans hp))]
  have hpinv : (p : ℂ)⁻¹ = ((p⁻¹ : ℝ) : ℂ) := by
    norm_cast
  rw [evenPrimeLocalFactor, evenPositiveEulerOperator, hcoeff]
  change
    ((1 - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) •
        (U.symm : evenSubspace →L[ℂ] evenSubspace))†) *
      (1 - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) •
        (U.symm : evenSubspace →L[ℂ] evenSubspace)) = _
  have hadj :
      (1 - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) •
          (U.symm : evenSubspace →L[ℂ] evenSubspace))† =
        1 - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) •
          (U : evenSubspace →L[ℂ] evenSubspace) := by
    exact adjoint_one_sub_real_smul_unitary_symm U (Real.sqrt p)⁻¹
  rw [hadj, ← evenDilationUnitarySum_eq_evenDilationSum p hp]
  change
    (1 - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) •
        (U : evenSubspace →L[ℂ] evenSubspace)) *
      (1 - (((Real.sqrt p)⁻¹ : ℝ) : ℂ) •
        (U.symm : evenSubspace →L[ℂ] evenSubspace)) =
    ((1 + p⁻¹ : ℝ) : ℂ) • (1 : evenSubspace →L[ℂ] evenSubspace) +
      (-((((Real.sqrt p)⁻¹ : ℝ) : ℂ))) •
        ((U : evenSubspace →L[ℂ] evenSubspace) +
          (U.symm : evenSubspace →L[ℂ] evenSubspace))
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, map_sub, map_smul]
  have hU :
      (U : evenSubspace →L[ℂ] evenSubspace)
        ((U.symm : evenSubspace →L[ℂ] evenSubspace) f) = f :=
    U.apply_symm_apply f
  rw [hU]
  push_cast
  rw [hcoeff, hpinv, ← hsqrt_sq]
  module

/-- The intrinsic even Euler corner is the corner of the Gram operator of the local factor. -/
theorem evenCentralPositiveEulerCorner_eq_gramCorner
    (a p : ℝ) (hp : 1 < p) :
    evenCentralPositiveEulerCorner a p hp =
      crossBoundary (evenCentralSoninProjection a)
        ((evenPrimeLocalFactor p hp)† * evenPrimeLocalFactor p hp) := by
  rw [evenPrimeLocalFactor_adjoint_comp_self]
  rw [evenPositiveEulerOperator]
  have hQ : IsIdempotentElem (evenCentralSoninProjection a) := by
    rw [evenCentralSoninProjection_eq_starProjection]
    exact (evenCentralSoninCarrier a).isIdempotentElem_starProjection
  rw [crossBoundary_affine _ hQ]
  rw [evenCentralPositiveEulerCorner_eq_smul]
  rw [evenCentralSoninDilationCorner_eq_crossBoundary]

theorem evenCentralPositiveEulerCorner_eq_operatorCorner
    (a p : ℝ) (hp : 1 < p) :
    evenCentralPositiveEulerCorner a p hp =
      crossBoundary (evenCentralSoninProjection a)
        (evenPositiveEulerOperator p hp) := by
  rw [evenCentralPositiveEulerCorner_eq_gramCorner,
    evenPrimeLocalFactor_adjoint_comp_self]

/-! Source-side Hardy--Titchmarsh names. -/

section Source

variable {K : Type*}
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The dual Hardy--Titchmarsh unitary, supplied by a concrete source realization. -/
abbrev DualHardyTitchmarshUnitary (K : Type*)
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] :=
  evenSubspace ≃ₗᵢ[ℂ] K

/-- The boundary realization of the common carrier `B_a` in the archimedean source norm. -/
def hardyTitchmarshBoundaryCarrier
    (u : DualHardyTitchmarshUnitary K) (a : ℝ) : Submodule ℂ K :=
  (evenCentralSoninCarrier a).map
    (u.toLinearEquiv.toLinearMap : evenSubspace →ₗ[ℂ] K)

instance hardyTitchmarshBoundaryCarrier_hasOrthogonalProjection
    (u : DualHardyTitchmarshUnitary K) (a : ℝ) :
    (hardyTitchmarshBoundaryCarrier u a).HasOrthogonalProjection := by
  rw [hardyTitchmarshBoundaryCarrier]
  infer_instance

/-- `Π^B_{a,∞}`: the actual orthogonal projection onto the boundary realization of `B_a`
for the archimedean source norm. -/
def hardyTitchmarshCarrierProjection
    (u : DualHardyTitchmarshUnitary K) (a : ℝ) : K →L[ℂ] K :=
  (hardyTitchmarshBoundaryCarrier u a).starProjection

omit [CompleteSpace K] in
/-- The actual source projection is the unitary push of the actual even Sonin projection. -/
theorem hardyTitchmarshCarrierProjection_eq_unitaryPush
    (u : DualHardyTitchmarshUnitary K) (a : ℝ) :
    hardyTitchmarshCarrierProjection u a =
      unitaryPush u (evenCentralSoninProjection a) := by
  apply ContinuousLinearMap.ext
  intro x
  change ((evenCentralSoninCarrier a).map
      (u.toLinearEquiv.toLinearMap : evenSubspace →ₗ[ℂ] K)).starProjection x =
    u (evenCentralSoninProjection a (u.symm x))
  rw [Submodule.starProjection_map_apply,
    evenCentralSoninProjection_eq_starProjection]

/-- The source local-factor multiplier `T_p = M_{1-p^{-1/2-is}}`. -/
def hardyTitchmarshLocalFactor
    (u : DualHardyTitchmarshUnitary K) (p : ℝ) (hp : 1 < p) : K →L[ℂ] K :=
  unitaryPush u (evenPrimeLocalFactor p hp)

/-- The source positive Euler Gram `T_p† T_p = M_{|1-p^{-1/2-is}|²}`. -/
def hardyTitchmarshEulerGram
    (u : DualHardyTitchmarshUnitary K) (p : ℝ) (hp : 1 < p) : K →L[ℂ] K :=
  (hardyTitchmarshLocalFactor u p hp)† * hardyTitchmarshLocalFactor u p hp

/-- The source Euler corner across the archimedean-norm entire carrier. -/
def hardyTitchmarshEulerCorner
    (u : DualHardyTitchmarshUnitary K) (a p : ℝ) (hp : 1 < p) : K →L[ℂ] K :=
  crossBoundary (hardyTitchmarshCarrierProjection u a)
    (hardyTitchmarshEulerGram u p hp)

theorem hardyTitchmarshLocalFactor_adjoint_comp_self
    (u : DualHardyTitchmarshUnitary K) (p : ℝ) (hp : 1 < p) :
    hardyTitchmarshEulerGram u p hp =
      unitaryPush u (evenPositiveEulerOperator p hp) := by
  rw [hardyTitchmarshEulerGram, hardyTitchmarshLocalFactor]
  have hAdj :
      (unitaryPush u (evenPrimeLocalFactor p hp))† =
        unitaryPush u ((evenPrimeLocalFactor p hp)†) :=
    adjoint_unitaryPush u (evenPrimeLocalFactor p hp)
  rw [hAdj]
  rw [← unitaryPush_mul]
  rw [evenPrimeLocalFactor_adjoint_comp_self]

theorem hardyTitchmarshEulerCorner_eq_unitaryPush
    (u : DualHardyTitchmarshUnitary K) (a p : ℝ) (hp : 1 < p) :
    hardyTitchmarshEulerCorner u a p hp =
      unitaryPush u (evenCentralPositiveEulerCorner a p hp) := by
  rw [hardyTitchmarshEulerCorner,
    hardyTitchmarshCarrierProjection_eq_unitaryPush,
    hardyTitchmarshLocalFactor_adjoint_comp_self,
    ← unitaryPush_crossBoundary,
    ← evenCentralPositiveEulerCorner_eq_operatorCorner]

theorem hardyTitchmarshEulerCorner_pullback
    (u : DualHardyTitchmarshUnitary K) (a p : ℝ) (hp : 1 < p) :
    conjugateOperator u.toContinuousLinearEquiv
      (hardyTitchmarshEulerCorner u a p hp) =
        evenCentralPositiveEulerCorner a p hp := by
  rw [hardyTitchmarshEulerCorner_eq_unitaryPush]
  exact conjugateOperator_unitaryPush u
    (evenCentralPositiveEulerCorner a p hp)

theorem hardyTitchmarshEulerCorner_not_isCompactOperator
    (u : DualHardyTitchmarshUnitary K) (a p : ℝ) (ha : 0 < a) (hp : 1 < p) :
    ¬ IsCompactOperator (hardyTitchmarshEulerCorner u a p hp) := by
  intro hcompact
  have hpull : IsCompactOperator
      (conjugateOperator u.toContinuousLinearEquiv
        (hardyTitchmarshEulerCorner u a p hp)) :=
    (isCompactOperator_conjugateOperator_iff u.toContinuousLinearEquiv _).mpr hcompact
  rw [hardyTitchmarshEulerCorner_pullback] at hpull
  exact evenCentralPositiveEulerCorner_not_isCompactOperator a p ha hp hpull

theorem hardyTitchmarshPrimeEulerCorner_not_isCompactOperator
    (u : DualHardyTitchmarshUnitary K) (a : ℝ) (p : ℕ)
    (ha : 0 < a) (hp : p.Prime) :
    ¬ IsCompactOperator
      (hardyTitchmarshEulerCorner u a (p : ℝ) (by exact_mod_cast hp.one_lt)) :=
  hardyTitchmarshEulerCorner_not_isCompactOperator u a (p : ℝ) ha (by
    exact_mod_cast hp.one_lt)

end Source

end RHTower
