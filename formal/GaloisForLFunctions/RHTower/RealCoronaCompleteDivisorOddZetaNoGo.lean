import GaloisForLFunctions.RHTower.RealCoronaCrossedProductSmoothnessFracture
import GaloisForLFunctions.RHTower.XiDivisorTraceTowerWitness

/-!
# The odd complete-divisor zeta operator misses the spectral-triple Lipschitz axiom

The absolute complete-divisor diagonal commutes with functional-equation reflection.  Composing
the two gives the canonical odd realization of the divisor relative to the Real-corona
orientation.  This file proves, on the maximal domain, that the resulting operator is
self-adjoint, genuinely unbounded, and has a compact two-sided inverse.  Thus it has all of the
basic zeta/Fredholm features one wants from the complete divisor.

The obstruction is exact: the commutator with the projector `(1 + m) / 2` has pointwise norm
equal to the odd Dirac norm.  It is therefore genuinely unbounded.  Hence an algebra containing
the Real-corona idempotent cannot form a spectral triple with this odd complete-divisor operator,
before regularity or dimension-spectrum questions even arise.
-/

noncomputable section

open Filter HilbertSchmidt
open scoped LinearPMap
open GaloisForLFunctions.RHTower ContinuousLinearMap

namespace RHTower

/-- The complete-divisor odd Dirac: absolute divisor energy followed by functional-equation
reflection.  Its maximal domain is the same as that of the absolute diagonal because reflection
preserves the energy. -/
def xiCompleteDivisorOddDirac : XiDivisorL2 →ₗ.[ℂ] XiDivisorL2 where
  domain := xiCompleteDivisorDirac.domain
  toFun :=
    { toFun := fun x =>
        ⟨fun q => (xiCompleteDivisorEnergy q : ℂ) *
            (x : XiDivisorL2) (xiZeroCopyReflectEquiv q),
          by
            change Memℓp (fun q : XiZeroCopy =>
              (xiCompleteDivisorEnergy q : ℂ) *
                (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)) 2
            apply HilbertSchmidt.memℓp_of_sq
            have hx : Summable (fun q : XiZeroCopy =>
                ‖(xiCompleteDivisorEnergy q : ℂ) * (x : XiDivisorL2) q‖ ^ (2 : ℕ)) := by
              simpa using x.property.summable (by norm_num)
            exact (xiZeroCopyReflectEquiv.summable_iff.mpr hx).congr fun q => by
              simp only [Function.comp_apply, xiCompleteDivisorEnergy,
                xiSpectralPoint_reflect, norm_neg]⟩
      map_add' := by
        intro x y
        ext q
        change (xiCompleteDivisorEnergy q : ℂ) *
            ((x : XiDivisorL2) (xiZeroCopyReflectEquiv q) +
              (y : XiDivisorL2) (xiZeroCopyReflectEquiv q)) =
          (xiCompleteDivisorEnergy q : ℂ) *
              (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) +
            (xiCompleteDivisorEnergy q : ℂ) *
              (y : XiDivisorL2) (xiZeroCopyReflectEquiv q)
        ring
      map_smul' := by
        intro c x
        ext q
        change (xiCompleteDivisorEnergy q : ℂ) *
            (c * (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)) =
          c * ((xiCompleteDivisorEnergy q : ℂ) *
            (x : XiDivisorL2) (xiZeroCopyReflectEquiv q))
        ring }

@[simp] theorem xiCompleteDivisorOddDirac_apply
    (x : xiCompleteDivisorOddDirac.domain) (q : XiZeroCopy) :
    xiCompleteDivisorOddDirac x q =
      (xiCompleteDivisorEnergy q : ℂ) *
        (x : XiDivisorL2) (xiZeroCopyReflectEquiv q) := rfl

theorem xiCompleteDivisorEnergy_reflect (q : XiZeroCopy) :
    xiCompleteDivisorEnergy (xiZeroCopyReflectEquiv q) =
      xiCompleteDivisorEnergy q := by
  simp [xiCompleteDivisorEnergy, xiSpectralPoint_reflect]

/-- The coupled odd divisor is formally self-adjoint. -/
theorem xiCompleteDivisorOddDirac_formalSelfAdjoint :
    xiCompleteDivisorOddDirac.IsFormalAdjoint xiCompleteDivisorOddDirac := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  let f : XiZeroCopy → ℂ := fun q =>
    inner ℂ (xiCompleteDivisorOddDirac x q) ((y : XiDivisorL2) q)
  have hreindex : (∑' q, f q) = ∑' q, f (xiZeroCopyReflectEquiv q) :=
    (xiZeroCopyReflectEquiv.tsum_eq f).symm
  rw [show (∑' q, inner ℂ (xiCompleteDivisorOddDirac x q)
      ((y : XiDivisorL2) q)) = ∑' q, f q by rfl, hreindex]
  apply tsum_congr
  intro q
  simp only [f, xiCompleteDivisorOddDirac_apply,
    xiZeroCopyReflectEquiv_apply_apply, xiCompleteDivisorEnergy_reflect,
    RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

theorem xiCompleteDivisorOddDirac_dense :
    Dense (xiCompleteDivisorOddDirac.domain : Set XiDivisorL2) :=
  maximalRealDiagonal_dense xiCompleteDivisorEnergy

/-- The adjoint of the odd divisor has the same reflected coordinate formula on its entire
domain. -/
theorem xiCompleteDivisorOddDirac_adjoint_apply
    (y : xiCompleteDivisorOddDirac†.domain) (q : XiZeroCopy) :
    xiCompleteDivisorOddDirac† y q =
      (xiCompleteDivisorEnergy q : ℂ) *
        (y : XiDivisorL2) (xiZeroCopyReflectEquiv q) := by
  let e : xiCompleteDivisorOddDirac.domain :=
    ⟨lpBasis XiZeroCopy q,
      lpBasis_mem_maximalRealDiagonalDomain xiCompleteDivisorEnergy q⟩
  have hformal :=
    (LinearPMap.adjoint_isFormalAdjoint xiCompleteDivisorOddDirac_dense).symm e y
  have heval :
      xiCompleteDivisorOddDirac e =
        (xiCompleteDivisorEnergy q : ℂ) •
          lpBasis XiZeroCopy (xiZeroCopyReflectEquiv q) := by
    ext r
    classical
    change (xiCompleteDivisorEnergy r : ℂ) *
        (lpBasis XiZeroCopy q) (xiZeroCopyReflectEquiv r) =
      (xiCompleteDivisorEnergy q : ℂ) *
        (lpBasis XiZeroCopy (xiZeroCopyReflectEquiv q)) r
    by_cases hr : r = xiZeroCopyReflectEquiv q
    · subst r
      simp [lpBasis_apply, xiCompleteDivisorEnergy_reflect]
    · have hne : xiZeroCopyReflectEquiv r ≠ q := by
        intro h
        apply hr
        rw [← h, xiZeroCopyReflectEquiv_apply_apply]
      rw [lpBasis_apply, lp.single_apply_ne _ _ _ hne,
        lpBasis_apply, lp.single_apply_ne _ _ _ hr]
      simp
  change inner ℂ (xiCompleteDivisorOddDirac e) (y : XiDivisorL2) =
      inner ℂ (lpBasis XiZeroCopy q) (xiCompleteDivisorOddDirac† y) at hformal
  rw [heval, inner_smul_left, Complex.conj_ofReal,
    lpBasis_apply, lp.inner_single_left, lpBasis_apply,
    lp.inner_single_left] at hformal
  simpa [RCLike.inner_apply] using hformal.symm

/-- The complete-divisor odd operator is self-adjoint on its maximal domain. -/
theorem xiCompleteDivisorOddDirac_isSelfAdjoint :
    IsSelfAdjoint xiCompleteDivisorOddDirac := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      let y' : xiCompleteDivisorOddDirac†.domain := ⟨y, hy⟩
      let z : XiDivisorL2 := xiCompleteDivisorOddDirac† y'
      change Memℓp (fun q : XiZeroCopy =>
        (xiCompleteDivisorEnergy q : ℂ) * y q) 2
      apply HilbertSchmidt.memℓp_of_sq
      have hz : Summable (fun q : XiZeroCopy => ‖z q‖ ^ (2 : ℕ)) :=
        HilbertSchmidt.summable_coe_sq z
      exact (xiZeroCopyReflectEquiv.summable_iff.mpr hz).congr fun q => by
        simp only [Function.comp_apply]
        rw [xiCompleteDivisorOddDirac_adjoint_apply,
          xiCompleteDivisorEnergy_reflect,
          xiZeroCopyReflectEquiv_apply_apply]
    · intro x y hxy
      apply lp.ext
      funext q
      rw [xiCompleteDivisorOddDirac_adjoint_apply,
        xiCompleteDivisorOddDirac_apply]
      exact congrArg (fun z : XiDivisorL2 =>
        (xiCompleteDivisorEnergy q : ℂ) *
          z (xiZeroCopyReflectEquiv q)) hxy
  · exact xiCompleteDivisorOddDirac_formalSelfAdjoint.le_adjoint
      xiCompleteDivisorOddDirac_dense

/-- The Real-corona orientation preserves the odd complete-divisor maximal domain. -/
theorem xiCompleteDivisorOrientation_mem_oddDomain
    (x : xiCompleteDivisorOddDirac.domain) :
    xiCompleteDivisorOrientation (x : XiDivisorL2) ∈
      xiCompleteDivisorOddDirac.domain :=
  xiCompleteDivisorOrientation_mem_domain x

/-- The coupled complete-divisor Dirac is odd for the Real-corona orientation. -/
theorem xiCompleteDivisorOddDirac_orientation_odd
    (x : xiCompleteDivisorOddDirac.domain) :
    xiCompleteDivisorOddDirac
        ⟨xiCompleteDivisorOrientation (x : XiDivisorL2),
          xiCompleteDivisorOrientation_mem_oddDomain x⟩ =
      -xiCompleteDivisorOrientation (xiCompleteDivisorOddDirac x) := by
  ext q
  change (xiCompleteDivisorEnergy q : ℂ) *
      (deningerArithmeticFEOrientation (xiZeroCopyReflectEquiv q) *
        (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)) =
    -(deningerArithmeticFEOrientation q *
      ((xiCompleteDivisorEnergy q : ℂ) *
        (x : XiDivisorL2) (xiZeroCopyReflectEquiv q)))
  rw [deningerArithmeticFEOrientation_reflect]
  ring

/-- Canonical basis vectors belong to the odd maximal domain. -/
def xiCompleteDivisorOddEigenpacket (q : XiZeroCopy) :
    xiCompleteDivisorOddDirac.domain :=
  ⟨lpBasis XiZeroCopy q,
    lpBasis_mem_maximalRealDiagonalDomain xiCompleteDivisorEnergy q⟩

theorem norm_xiCompleteDivisorOddDirac_eigenpacket (q : XiZeroCopy) :
    ‖xiCompleteDivisorOddDirac (xiCompleteDivisorOddEigenpacket q)‖ =
      xiCompleteDivisorEnergy q := by
  have hvec : xiCompleteDivisorOddDirac (xiCompleteDivisorOddEigenpacket q) =
      (xiCompleteDivisorEnergy q : ℂ) •
        lpBasis XiZeroCopy (xiZeroCopyReflectEquiv q) := by
    ext r
    classical
    change (xiCompleteDivisorEnergy r : ℂ) *
        (lpBasis XiZeroCopy q) (xiZeroCopyReflectEquiv r) =
      (xiCompleteDivisorEnergy q : ℂ) *
        (lpBasis XiZeroCopy (xiZeroCopyReflectEquiv q)) r
    by_cases hr : r = xiZeroCopyReflectEquiv q
    · subst r
      simp [lpBasis_apply, xiCompleteDivisorEnergy_reflect]
    · have hne : xiZeroCopyReflectEquiv r ≠ q := by
        intro h
        apply hr
        rw [← h, xiZeroCopyReflectEquiv_apply_apply]
      rw [lpBasis_apply, lp.single_apply_ne _ _ _ hne,
        lpBasis_apply, lp.single_apply_ne _ _ _ hr]
      simp
  rw [hvec, norm_smul, (lpBasis XiZeroCopy).orthonormal.norm_eq_one,
    mul_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (norm_nonneg _)

theorem xiCompleteDivisorOddDirac_genuinelyUnbounded :
    IsGenuinelyUnboundedLinearPMap xiCompleteDivisorOddDirac := by
  rintro ⟨C, hC, hbound⟩
  have hev : ∀ᶠ q : XiZeroCopy in cofinite,
      C < xiCompleteDivisorEnergy q :=
    tendsto_norm_xiSpectralPoint_cofinite.eventually
      (eventually_gt_atTop C)
  rcases hev.exists with ⟨q, hq⟩
  have hb := hbound (xiCompleteDivisorOddEigenpacket q)
  have hnorm : ‖(xiCompleteDivisorOddEigenpacket q : XiDivisorL2)‖ = 1 := by
    simpa [xiCompleteDivisorOddEigenpacket] using
      (lpBasis XiZeroCopy).orthonormal.norm_eq_one q
  rw [norm_xiCompleteDivisorOddDirac_eigenpacket, hnorm, mul_one] at hb
  exact (not_lt_of_ge hb) hq

/-- Functional-equation reflection as a bounded unitary operator. -/
def xiCompleteDivisorReflectionCLM : XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  xiCompleteDivisorReflection.mkContinuous 1 fun x => by
    rw [norm_xiCompleteDivisorReflection, one_mul]

@[simp] theorem xiCompleteDivisorReflectionCLM_apply
    (x : XiDivisorL2) :
    xiCompleteDivisorReflectionCLM x = xiCompleteDivisorReflection x := rfl

/-- Positive inverse-energy weight of the absolute complete divisor. -/
def xiCompleteDivisorInverseWeight (q : XiZeroCopy) : ℂ :=
  (xiCompleteDivisorEnergy q : ℂ)⁻¹

theorem norm_xiCompleteDivisorInverseWeight_le (q : XiZeroCopy) :
    ‖xiCompleteDivisorInverseWeight q‖ ≤ xiDivisorSpectralGap⁻¹ := by
  have henergy : 0 ≤ xiCompleteDivisorEnergy q := norm_nonneg _
  rw [xiCompleteDivisorInverseWeight, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg henergy,
    inv_eq_one_div, inv_eq_one_div]
  exact div_le_div_of_nonneg_left (by norm_num) xiDivisorSpectralGap_pos
    (xiDivisorSpectralGap_le q)

theorem summable_norm_xiCompleteDivisorInverseWeight_sq :
    Summable fun q : XiZeroCopy => ‖xiCompleteDivisorInverseWeight q‖ ^ (2 : ℕ) := by
  simpa [xiCompleteDivisorInverseWeight, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg, inv_pow, one_div,
    xiCompleteDivisorEnergy] using xiSpectralPoint_inv_sq_summable

/-- Bounded inverse of the odd complete-divisor operator: inverse-energy multiplication followed
by reflection. -/
def xiCompleteDivisorOddInverse : XiDivisorL2 →L[ℂ] XiDivisorL2 :=
  (xiDivisorDiagonal xiCompleteDivisorInverseWeight
      xiDivisorSpectralGap_inv_nonneg norm_xiCompleteDivisorInverseWeight_le).comp
    xiCompleteDivisorReflectionCLM

@[simp] theorem xiCompleteDivisorOddInverse_apply
    (x : XiDivisorL2) (q : XiZeroCopy) :
    xiCompleteDivisorOddInverse x q =
      (xiCompleteDivisorEnergy q : ℂ)⁻¹ *
        x (xiZeroCopyReflectEquiv q) := rfl

theorem xiCompleteDivisorOddInverse_mem_domain (x : XiDivisorL2) :
    xiCompleteDivisorOddInverse x ∈ xiCompleteDivisorOddDirac.domain := by
  change Memℓp (fun q : XiZeroCopy =>
    (xiCompleteDivisorEnergy q : ℂ) * xiCompleteDivisorOddInverse x q) 2
  have hfun : (fun q : XiZeroCopy =>
      (xiCompleteDivisorEnergy q : ℂ) * xiCompleteDivisorOddInverse x q) =
      fun q => x (xiZeroCopyReflectEquiv q) := by
    funext q
    rw [xiCompleteDivisorOddInverse_apply]
    field_simp [show (xiCompleteDivisorEnergy q : ℂ) ≠ 0 by
      exact_mod_cast (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)).ne']
  rw [hfun]
  apply HilbertSchmidt.memℓp_of_sq
  exact xiZeroCopyReflectEquiv.summable_iff.mpr
    (HilbertSchmidt.summable_coe_sq x)

theorem xiCompleteDivisorOddDirac_inverse_left (x : XiDivisorL2) :
    xiCompleteDivisorOddDirac
        ⟨xiCompleteDivisorOddInverse x,
          xiCompleteDivisorOddInverse_mem_domain x⟩ = x := by
  ext q
  rw [xiCompleteDivisorOddDirac_apply,
    xiCompleteDivisorOddInverse_apply,
    xiCompleteDivisorEnergy_reflect,
    xiZeroCopyReflectEquiv_apply_apply]
  field_simp [show (xiCompleteDivisorEnergy q : ℂ) ≠ 0 by
    exact_mod_cast (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)).ne']

theorem xiCompleteDivisorOddDirac_inverse_right
    (x : xiCompleteDivisorOddDirac.domain) :
    xiCompleteDivisorOddInverse (xiCompleteDivisorOddDirac x) =
      (x : XiDivisorL2) := by
  ext q
  rw [xiCompleteDivisorOddInverse_apply,
    xiCompleteDivisorOddDirac_apply,
    xiCompleteDivisorEnergy_reflect,
    xiZeroCopyReflectEquiv_apply_apply]
  field_simp [show (xiCompleteDivisorEnergy q : ℂ) ≠ 0 by
    exact_mod_cast (norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)).ne']

theorem xiCompleteDivisorOddInverse_isHilbertSchmidt :
    IsHilbertSchmidt xiCompleteDivisorOddInverse := by
  have hdiag : IsHilbertSchmidt
      (xiDivisorDiagonal xiCompleteDivisorInverseWeight
        xiDivisorSpectralGap_inv_nonneg norm_xiCompleteDivisorInverseWeight_le) :=
    xiDivisorDiagonal_isHilbertSchmidt _ _ _
      summable_norm_xiCompleteDivisorInverseWeight_sq
  exact hdiag.comp_right xiCompleteDivisorReflectionCLM

/-- The two-sided inverse of the complete-divisor odd Dirac is compact (indeed
Hilbert--Schmidt). -/
theorem xiCompleteDivisorOddInverse_isCompact :
    IsCompactOperator xiCompleteDivisorOddInverse :=
  xiCompleteDivisorOddInverse_isHilbertSchmidt.isCompactOperator

/-- The exact Real-corona idempotent cut out by the orientation. -/
def xiCompleteDivisorRealCoronaProjector : Module.End ℂ XiDivisorL2 :=
  cliffordExchangeProjector xiCompleteDivisorOrientation

theorem xiCompleteDivisorRealCoronaProjector_isIdempotent :
    IsIdempotentElem xiCompleteDivisorRealCoronaProjector :=
  cliffordExchangeProjector_isIdempotent xiCompleteDivisorOrientation_sq

theorem norm_xiCompleteDivisorOdd_projectorCommutator
    (x : xiCompleteDivisorOddDirac.domain) :
    ‖linearPMapExchangeCommutator xiCompleteDivisorOddDirac
        xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_oddDomain x‖ =
      ‖xiCompleteDivisorOddDirac x‖ :=
  norm_linearPMapExchangeCommutator xiCompleteDivisorOddDirac
    xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_oddDomain
    xiCompleteDivisorOddDirac_orientation_odd norm_xiCompleteDivisorOrientation x

/-- **P1, exact first-order no-go.**  The canonical odd, self-adjoint, compactly invertible
complete-divisor zeta operator has genuinely unbounded commutator with the Real-corona
idempotent.  Therefore that idempotent cannot lie in the represented Lipschitz algebra of a
spectral triple using this operator, so no Connes--Moscovici local index formula for its class can
start from this complete-divisor realization. -/
theorem xiCompleteDivisorOdd_not_realCoronaProjector_lipschitz :
    ¬HasLinearPMapBoundOnDomain
      (linearPMapExchangeCommutator xiCompleteDivisorOddDirac
        xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_oddDomain) := by
  exact (genuinelyUnboundedLinearPMap_exchangeCommutator_iff
    xiCompleteDivisorOddDirac xiCompleteDivisorOrientation
      xiCompleteDivisorOrientation_mem_oddDomain
      xiCompleteDivisorOddDirac_orientation_odd
      norm_xiCompleteDivisorOrientation).mpr
    xiCompleteDivisorOddDirac_genuinelyUnbounded

/-- Bundled non-vacuity certificate: the odd complete-divisor realization is self-adjoint,
genuinely unbounded, and has a compact two-sided inverse, but its Real-corona projector
commutator is unbounded. -/
theorem xiCompleteDivisorOdd_zetaNoGo_certificate :
    IsSelfAdjoint xiCompleteDivisorOddDirac ∧
      IsGenuinelyUnboundedLinearPMap xiCompleteDivisorOddDirac ∧
      IsCompactOperator xiCompleteDivisorOddInverse ∧
      (∀ x : XiDivisorL2,
        xiCompleteDivisorOddDirac
          ⟨xiCompleteDivisorOddInverse x,
            xiCompleteDivisorOddInverse_mem_domain x⟩ = x) ∧
      (∀ x : xiCompleteDivisorOddDirac.domain,
        xiCompleteDivisorOddInverse (xiCompleteDivisorOddDirac x) =
          (x : XiDivisorL2)) ∧
      ¬HasLinearPMapBoundOnDomain
        (linearPMapExchangeCommutator xiCompleteDivisorOddDirac
          xiCompleteDivisorOrientation xiCompleteDivisorOrientation_mem_oddDomain) :=
  ⟨xiCompleteDivisorOddDirac_isSelfAdjoint,
    xiCompleteDivisorOddDirac_genuinelyUnbounded,
    xiCompleteDivisorOddInverse_isCompact,
    xiCompleteDivisorOddDirac_inverse_left,
    xiCompleteDivisorOddDirac_inverse_right,
    xiCompleteDivisorOdd_not_realCoronaProjector_lipschitz⟩

end RHTower
