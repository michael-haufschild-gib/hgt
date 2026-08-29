import GaloisForLFunctions.RHTower.JointAncestryPrimeCoordinateGammaThetaNilpotentLandingNoGo
import GaloisForLFunctions.HTGeometry.CircleSingularWitness

/-!
# JAS prime-coordinate/toggle dense-range no-go

The canonical Boolean toggle cannot be the reversible target image of both inverse prime
coordinates in a nonzero closed source-linear landing.

The source difference has a rigid analytic form. Multiplication by

`I * (chi_p - chi_p⁻¹)`

is self-adjoint and has dense range on every positive-aperture prime-Poisson `L²`. Its symbol
vanishes only when the fixed circle coordinate is `+1` or `-1`; each such fibre is null because a
local circle-Poisson law has a density against atomless circle Haar measure.

The relation theorem is stronger than the toggle application. If a closed, densely defined,
single-valued Hilbert relation sends two bounded source actions to the same bounded target action,
and a nonzero scalar multiple of their difference has dense range, every relation output is zero.
The target action need not be unitary, involutive, injective, or have dense range.

Thus a reversible JAS dilation must distinguish the target images of `p` and `p⁻¹`. A single
Boolean toggle, even before compression to the literal Gamma--theta creator, cannot provide the
coefficient-faithful prime-Poisson landing needed for Xi reflection sewing.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

local instance : MeasurableSpace Circle :=
  GaloisForLFunctions.HTGeometry.instMeasurableSpaceCircle_galoisForLFunctions

/-- The additive-circle point whose multiplicative image is `+1`. -/
def jasUnitAddCirclePlus : UnitAddCircle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm 1

/-- The additive-circle point whose multiplicative image is `-1`. -/
def jasUnitAddCircleMinus : UnitAddCircle :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (-1)

/-- The first Fourier character is the multiplicative-circle coordinate. -/
theorem fourier_one_eq_circle (x : UnitAddCircle) :
    fourier 1 x =
      (((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero) x : Circle) : ℂ) := by
  rw [fourier_apply, one_zsmul, AddCircle.homeomorphCircle_apply one_ne_zero]

/-- Self-adjoint local difference of the positive and negative coordinate characters. -/
def jasLocalOddCharacter (x : UnitAddCircle) : ℂ :=
  I * (fourier 1 x - fourier (-1) x)

/-- The local odd character can vanish only at the two real circle points. -/
theorem jasLocalOddCharacter_eq_zero_imp (x : UnitAddCircle)
    (hx : jasLocalOddCharacter x = 0) :
    x = jasUnitAddCirclePlus ∨ x = jasUnitAddCircleMinus := by
  have hdiff : fourier 1 x - fourier (-1) x = 0 :=
    (mul_eq_zero.mp hx).resolve_left I_ne_zero
  have heq : fourier 1 x = (starRingEnd ℂ) (fourier 1 x) := by
    have hneg : fourier (-1) x = (starRingEnd ℂ) (fourier 1 x) := by
      simpa using (fourier_neg (n := (1 : ℤ)) (x := x))
    rw [← hneg]
    exact sub_eq_zero.mp hdiff
  let e : UnitAddCircle ≃ₜ Circle :=
    AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hnorm : ‖fourier 1 x‖ = 1 := by
    rw [fourier_one_eq_circle]
    exact Circle.norm_coe (e x)
  have hu0 : fourier 1 x ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at hnorm
    norm_num at hnorm
  have huinv : (fourier 1 x)⁻¹ = (starRingEnd ℂ) (fourier 1 x) :=
    Complex.inv_eq_conj hnorm
  have husq : fourier 1 x * fourier 1 x = 1 := by
    calc
      fourier 1 x * fourier 1 x = (fourier 1 x)⁻¹ * fourier 1 x := by
        rw [huinv, ← heq]
      _ = 1 := inv_mul_cancel₀ hu0
  rcases mul_self_eq_one_iff.mp husq with hu | hu
  · left
    apply e.injective
    rw [jasUnitAddCirclePlus, e.apply_symm_apply]
    apply Subtype.ext
    change ↑(e x) = (1 : ℂ)
    rw [AddCircle.homeomorphCircle_apply one_ne_zero]
    simpa [fourier_one_eq_circle] using hu
  · right
    apply e.injective
    rw [jasUnitAddCircleMinus, e.apply_symm_apply]
    apply Subtype.ext
    change ↑(e x) = (-1 : ℂ)
    rw [AddCircle.homeomorphCircle_apply one_ne_zero]
    simpa [fourier_one_eq_circle] using hu

/-- A local circle-Poisson law is atomless at every singleton. -/
theorem jasCirclePoissonMeasure_singleton_eq_zero
    (a : CirclePoissonParameter) (z : Circle) :
    circlePoissonMeasure a {z} = 0 := by
  unfold circlePoissonMeasure
  calc
    (circleLebesgue.withDensity (circlePoissonDensity a)) {z} =
        ∫⁻ w in {z}, circlePoissonDensity a w ∂circleLebesgue :=
      withDensity_apply _ (measurableSet_singleton z)
    _ = 0 := by simp

/-- The transported local Poisson law on the additive circle is atomless. -/
theorem jasAddCirclePoissonMeasure_singleton_eq_zero
    (a : CirclePoissonParameter) (x : UnitAddCircle) :
    (addCirclePoissonProbabilityMeasure a : Measure UnitAddCircle) {x} = 0 := by
  let e : UnitAddCircle ≃ₜ Circle :=
    AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  rw [addCirclePoissonProbabilityMeasure, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply e.symm.continuous.measurable
    (measurableSet_singleton x)]
  have hpre : e.symm ⁻¹' {x} = {e x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      calc
        z = e (e.symm z) := (e.apply_symm_apply z).symm
        _ = e x := congrArg e hz
    · intro hz
      rw [hz]
      exact e.symm_apply_apply x
  rw [hpre]
  change circlePoissonMeasure a {e x} = 0
  exact jasCirclePoissonMeasure_singleton_eq_zero a (e x)

/-- Every singleton fibre of a fixed prime coordinate is null for every positive-aperture
prime-Poisson product law. -/
theorem primePoissonMeasure_coordinate_singleton_eq_zero
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes)
    (x : UnitAddCircle) :
    primePoissonMeasure sigma t hsigma {z | z p = x} = 0 := by
  change (Measure.infinitePi fun q : Nat.Primes =>
      (addCirclePoissonProbabilityMeasure
        (primePoissonParameter sigma t hsigma q) : Measure UnitAddCircle))
      ((Function.eval p) ⁻¹' {x}) = 0
  rw [(measurePreserving_eval_infinitePi
    (fun q : Nat.Primes =>
      (addCirclePoissonProbabilityMeasure
        (primePoissonParameter sigma t hsigma q) : Measure UnitAddCircle)) p).measure_preimage
      (measurableSet_singleton x).nullMeasurableSet]
  exact jasAddCirclePoissonMeasure_singleton_eq_zero
    (primePoissonParameter sigma t hsigma p) x

/-- Global self-adjoint odd prime-coordinate symbol `I * (chi_p - chi_p⁻¹)`. -/
def jasPrimeCoordinateOddSymbol (p : Nat.Primes) : C(PrimeTorus, ℂ) :=
  I • (torusCharacter (Finsupp.single p (1 : ℤ)) -
    torusCharacter (Finsupp.single p (-1 : ℤ)))

theorem jasPrimeCoordinateOddSymbol_apply
    (p : Nat.Primes) (z : PrimeTorus) :
    jasPrimeCoordinateOddSymbol p z = jasLocalOddCharacter (z p) := by
  classical
  unfold jasPrimeCoordinateOddSymbol jasLocalOddCharacter
  simp only [ContinuousMap.smul_apply, smul_eq_mul, ContinuousMap.sub_apply]
  have hplus : torusCharacter (Finsupp.single p (1 : ℤ)) z =
      fourier 1 (z p) := by
    rw [torusCharacter_apply,
      Finsupp.support_single p (by norm_num : (1 : ℤ) ≠ 0)]
    simp only [Finset.prod_singleton, Finsupp.single_eq_same]
  have hminus : torusCharacter (Finsupp.single p (-1 : ℤ)) z =
      fourier (-1) (z p) := by
    rw [torusCharacter_apply,
      Finsupp.support_single p (by norm_num : (-1 : ℤ) ≠ 0)]
    simp only [Finset.prod_singleton, Finsupp.single_eq_same]
  rw [hplus, hminus]

/-- The global odd prime-coordinate symbol is nonzero almost everywhere for every positive
prime-Poisson aperture, including the critical wall and the mutually singular regime. -/
theorem jasPrimeCoordinateOddSymbol_ne_zero_ae
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    ∀ᵐ z ∂primePoissonMeasure sigma t hsigma,
      jasPrimeCoordinateOddSymbol p z ≠ 0 := by
  rw [ae_iff]
  have hsubset :
      {z : PrimeTorus | ¬ jasPrimeCoordinateOddSymbol p z ≠ 0} ⊆
        {z : PrimeTorus | z p = jasUnitAddCirclePlus} ∪
          {z : PrimeTorus | z p = jasUnitAddCircleMinus} := by
    intro z hz
    have hzero : jasPrimeCoordinateOddSymbol p z = 0 := not_ne_iff.mp hz
    rw [jasPrimeCoordinateOddSymbol_apply] at hzero
    rcases jasLocalOddCharacter_eq_zero_imp (z p) hzero with hp | hp
    · exact Or.inl hp
    · exact Or.inr hp
  exact measure_mono_null hsubset
    (measure_union_null
      (primePoissonMeasure_coordinate_singleton_eq_zero sigma t hsigma p
        jasUnitAddCirclePlus)
      (primePoissonMeasure_coordinate_singleton_eq_zero sigma t hsigma p
        jasUnitAddCircleMinus))

/-- Pointwise self-adjointness of the global odd source symbol. -/
theorem jasPrimeCoordinateOddSymbol_star
    (p : Nat.Primes) (z : PrimeTorus) :
    (starRingEnd ℂ) (jasPrimeCoordinateOddSymbol p z) =
      jasPrimeCoordinateOddSymbol p z := by
  rw [jasPrimeCoordinateOddSymbol_apply]
  unfold jasLocalOddCharacter
  have hneg : fourier (-1) (z p) =
      (starRingEnd ℂ) (fourier 1 (z p)) := by
    simpa using (fourier_neg (n := (1 : ℤ)) (x := z p))
  have hI : (starRingEnd ℂ) I = -I := by
    apply Complex.ext <;> norm_num
  have hstar : (starRingEnd ℂ) ((starRingEnd ℂ) (fourier 1 (z p))) =
      fourier 1 (z p) := star_star _
  rw [hneg]
  rw [map_mul, map_sub, hI, hstar]
  ring

/-- Actual odd difference multiplier on prime-Poisson `L²`. -/
def jasPrimeCoordinateOddMul
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    PrimePoissonL2 sigma t hsigma →L[ℂ] PrimePoissonL2 sigma t hsigma :=
  continuousL2Mul (primePoissonMeasure sigma t hsigma)
    (jasPrimeCoordinateOddSymbol p)

/-- The actual odd difference multiplier has dense range at every positive aperture. -/
theorem jasPrimeCoordinateOddMul_denseRange
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) :
    DenseRange (jasPrimeCoordinateOddMul sigma t hsigma p) := by
  exact denseRange_lpBoundedMulCLM_of_ae_ne_zero
    (jasPrimeCoordinateOddSymbol p).continuous.measurable
    (norm_nonneg (jasPrimeCoordinateOddSymbol p))
    (jasPrimeCoordinateOddSymbol p).norm_coe_le_norm
    (jasPrimeCoordinateOddSymbol_star p)
    (jasPrimeCoordinateOddSymbol_ne_zero_ae sigma t hsigma p)

/-- The odd multiplier is exactly `I` times the difference of the actual positive and negative
prime-coordinate multiplication actions. -/
theorem jasPrimeCoordinateOddMul_apply
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes)
    (u : PrimePoissonL2 sigma t hsigma) :
    jasPrimeCoordinateOddMul sigma t hsigma p u =
      I • (jasPrimeCoordinateMul sigma t hsigma p 1 u -
        jasPrimeCoordinateMul sigma t hsigma p (-1) u) := by
  let up : C(PrimeTorus, ℂ) :=
    torusCharacter (Finsupp.single p (1 : ℤ))
  let um : C(PrimeTorus, ℂ) :=
    torusCharacter (Finsupp.single p (-1 : ℤ))
  apply Lp.ext
  filter_upwards [
    continuousL2Mul_coeFn (primePoissonMeasure sigma t hsigma)
      (jasPrimeCoordinateOddSymbol p) u,
    continuousL2Mul_coeFn (primePoissonMeasure sigma t hsigma) up u,
    continuousL2Mul_coeFn (primePoissonMeasure sigma t hsigma) um u,
    Lp.coeFn_sub
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) up u)
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) um u),
    Lp.coeFn_smul I
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) up u -
        continuousL2Mul (primePoissonMeasure sigma t hsigma) um u)]
      with z hodd hplus hminus hsub hsmul
  simp only [Pi.sub_apply] at hsub
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  change ((continuousL2Mul (primePoissonMeasure sigma t hsigma)
      (jasPrimeCoordinateOddSymbol p) u :
        PrimePoissonL2 sigma t hsigma) : PrimeTorus → ℂ) z =
    ((I • (continuousL2Mul (primePoissonMeasure sigma t hsigma) up u -
      continuousL2Mul (primePoissonMeasure sigma t hsigma) um u) :
        PrimePoissonL2 sigma t hsigma) : PrimeTorus → ℂ) z
  rw [hodd, hsmul, hsub, hplus, hminus]
  change jasPrimeCoordinateOddSymbol p z * (u : PrimeTorus → ℂ) z =
    I * (up z * (u : PrimeTorus → ℂ) z -
      um z * (u : PrimeTorus → ℂ) z)
  unfold jasPrimeCoordinateOddSymbol
  change (I * (up z - um z)) * (u : PrimeTorus → ℂ) z = _
  ring

section GenericRelation

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- A closed single-valued relation with dense domain has zero output if it contains zero-output
pairs produced by a dense-range source action on its domain. -/
theorem hilbertRelation_output_eq_zero_of_closed_denseDomain_denseZeroAction
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (hclosed : IsClosed (R : Set (HilbertSum H₁ H₂)))
    (hdomain : Dense (hilbertRelationDomain R : Set H₁))
    (hsingle : HilbertRelationSingleValued R)
    (T : H₁ →L[ℂ] H₁) (hT : DenseRange T)
    (hzero : ∀ d : hilbertRelationDomain R,
      hilbertSumInl (T (d : H₁)) ∈ R)
    {z : HilbertSum H₁ H₂} (hz : z ∈ R) :
    hilbertSumSnd z = 0 := by
  let D : Submodule ℂ H₁ := hilbertRelationDomain R
  have hinc : DenseRange (fun d : D => (d : H₁)) := by
    change Dense (Set.range fun d : D => (d : H₁))
    have hrange : Set.range (fun d : D => (d : H₁)) = (D : Set H₁) := by
      ext x
      simp
    rw [hrange]
    exact hdomain
  have hcomp : DenseRange (fun d : D => T (d : H₁)) :=
    hT.comp hinc T.continuous
  let Z : Submodule ℂ H₁ := R.comap hilbertSumInl.toLinearMap
  have hZclosed : IsClosed (Z : Set H₁) := by
    change IsClosed ((fun x : H₁ => hilbertSumInl x) ⁻¹'
      (R : Set (HilbertSum H₁ H₂)))
    exact hclosed.preimage hilbertSumInl.continuous
  have hsubset : Set.range (fun d : D => T (d : H₁)) ⊆ (Z : Set H₁) := by
    intro x hx
    rcases hx with ⟨d, rfl⟩
    exact hzero d
  have hZtop : Z = ⊤ := by
    apply top_unique
    intro x _
    apply closure_minimal hsubset hZclosed
    rw [hcomp.closure_range]
    exact Set.mem_univ x
  have hallzero (x : H₁) : hilbertSumInl x ∈ R := by
    have hx : x ∈ Z := by
      rw [hZtop]
      exact Submodule.mem_top
    exact hx
  have hvertical : hilbertSumInr (hilbertSumSnd z) ∈ R := by
    have hsub := R.sub_mem hz (hallzero (hilbertSumFst z))
    have heq : z - hilbertSumInl (hilbertSumFst z) =
        hilbertSumInr (hilbertSumSnd z) := by
      apply hilbertSum_ext
      · rw [map_sub, hilbertSumFst_inl, hilbertSumFst_inr, sub_self]
      · rw [map_sub, hilbertSumSnd_inl, hilbertSumSnd_inr, sub_zero]
    rw [heq] at hsub
    exact hsub
  exact hsingle _ hvertical

/-- Same-target dense-difference rigidity. If two source actions are sent to one target action,
a dense-range scalar difference makes every output of a closed densely defined single-valued
relation vanish. No property of the target action beyond bounded linearity is used. -/
theorem hilbertRelation_output_eq_zero_of_closed_denseDomain_sameTarget
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (hclosed : IsClosed (R : Set (HilbertSum H₁ H₂)))
    (hdomain : Dense (hilbertRelationDomain R : Set H₁))
    (hsingle : HilbertRelationSingleValued R)
    (Aplus Aminus T : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂)
    (c : ℂ) (hT : DenseRange T)
    (hTapply : ∀ x : H₁, T x = c • (Aplus x - Aminus x))
    (hplus : ∀ z, z ∈ R → hilbertBlockDiagonal Aplus B z ∈ R)
    (hminus : ∀ z, z ∈ R → hilbertBlockDiagonal Aminus B z ∈ R)
    {z : HilbertSum H₁ H₂} (hz : z ∈ R) :
    hilbertSumSnd z = 0 := by
  apply hilbertRelation_output_eq_zero_of_closed_denseDomain_denseZeroAction
    R hclosed hdomain hsingle T hT
  · intro d
    have hd : (d : H₁) ∈ hilbertRelationDomain R := d.property
    rcases hd with ⟨w, hw, hwd⟩
    have hp := hplus w hw
    have hm := hminus w hw
    have hscaled := R.smul_mem c (R.sub_mem hp hm)
    have heq : c • (hilbertBlockDiagonal Aplus B w -
        hilbertBlockDiagonal Aminus B w) =
        hilbertSumInl (T (d : H₁)) := by
      apply hilbertSum_ext
      · rw [map_smul, map_sub, hilbertBlockDiagonal_fst,
          hilbertBlockDiagonal_fst, hilbertSumFst_inl, hTapply]
        exact congrArg (fun x : H₁ => c • (Aplus x - Aminus x)) hwd
      · rw [map_smul, map_sub, hilbertBlockDiagonal_snd,
          hilbertBlockDiagonal_snd, hilbertSumSnd_inl, sub_self, smul_zero]
    rw [heq] at hscaled
    exact hscaled
  · exact hz

end GenericRelation

/-- Bounded target action underlying the canonical Gamma--theta Boolean toggle. -/
def jasGammaThetaToggleCLM (p : Nat.Primes) :
    JASGammaThetaL2 →L[ℂ] JASGammaThetaL2 :=
  (jasGammaThetaToggleUnitary p).toLinearIsometry.toContinuousLinearMap

/-- Every output vanishes when both inverse actual prime coordinates are assigned to the same
canonical Gamma--theta Boolean toggle in a closed densely defined single-valued relation. -/
theorem jasPrimeCoordinateToggle_relation_output_eq_zero
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes)
    (R : Submodule ℂ
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASGammaThetaL2))
    (hclosed : IsClosed
      (R : Set (HilbertSum (PrimePoissonL2 sigma t hsigma) JASGammaThetaL2)))
    (hdomain : Dense
      (hilbertRelationDomain R : Set (PrimePoissonL2 sigma t hsigma)))
    (hsingle : HilbertRelationSingleValued R)
    (hplus : ∀ z, z ∈ R →
      hilbertBlockDiagonal
        (jasPrimeCoordinateMul sigma t hsigma p 1)
        (jasGammaThetaToggleCLM p) z ∈ R)
    (hminus : ∀ z, z ∈ R →
      hilbertBlockDiagonal
        (jasPrimeCoordinateMul sigma t hsigma p (-1))
        (jasGammaThetaToggleCLM p) z ∈ R)
    {z : HilbertSum (PrimePoissonL2 sigma t hsigma) JASGammaThetaL2}
    (hz : z ∈ R) :
    hilbertSumSnd z = 0 := by
  exact hilbertRelation_output_eq_zero_of_closed_denseDomain_sameTarget
    R hclosed hdomain hsingle
    (jasPrimeCoordinateMul sigma t hsigma p 1)
    (jasPrimeCoordinateMul sigma t hsigma p (-1))
    (jasPrimeCoordinateOddMul sigma t hsigma p)
    (jasGammaThetaToggleCLM p) I
    (jasPrimeCoordinateOddMul_denseRange sigma t hsigma p)
    (jasPrimeCoordinateOddMul_apply sigma t hsigma p)
    hplus hminus hz

/-- Proposed reversible one-toggle JAS landing: both inverse source characters act by the same
canonical Boolean toggle and a nonzero target output survives. -/
def JASPrimeCoordinateGammaThetaToggleClosedLanding : Prop :=
  ∃ (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes)
    (R : Submodule ℂ
      (HilbertSum (PrimePoissonL2 sigma t hsigma) JASGammaThetaL2)),
    IsClosed
      (R : Set (HilbertSum (PrimePoissonL2 sigma t hsigma) JASGammaThetaL2)) ∧
    Dense (hilbertRelationDomain R : Set (PrimePoissonL2 sigma t hsigma)) ∧
    HilbertRelationSingleValued R ∧
    (∀ z, z ∈ R →
      hilbertBlockDiagonal
        (jasPrimeCoordinateMul sigma t hsigma p 1)
        (jasGammaThetaToggleCLM p) z ∈ R) ∧
    (∀ z, z ∈ R →
      hilbertBlockDiagonal
        (jasPrimeCoordinateMul sigma t hsigma p (-1))
        (jasGammaThetaToggleCLM p) z ∈ R) ∧
    ∃ z ∈ R, hilbertSumSnd z ≠ 0

/-- The canonical one-toggle reversible JAS landing is impossible at every positive aperture. -/
theorem not_JASPrimeCoordinateGammaThetaToggleClosedLanding :
    ¬ JASPrimeCoordinateGammaThetaToggleClosedLanding := by
  rintro ⟨sigma, t, hsigma, p, R, hclosed, hdense, hsingle,
    hplus, hminus, z, hz, hnonzero⟩
  exact hnonzero
    (jasPrimeCoordinateToggle_relation_output_eq_zero
      sigma t hsigma p R hclosed hdense hsingle hplus hminus hz)

end

end RHTower
