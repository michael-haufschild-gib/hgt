import GaloisForLFunctions.RHTower.JointAncestryGammaThetaBooleanClosedCreation
import GaloisForLFunctions.HTGeometry.PrimePoissonSourceLinearSuperselection

/-!
# JAS prime-coordinate/Gamma--theta nilpotent landing no-go

The actual Gamma--theta creator is globally square-zero on its full natural domain: every output
automatically lies in the same unbounded-operator domain, and applying the creator again gives
zero. This upgrades the previously known two-step packet identity to every domain vector.

That global fact closes the strongest direct source-linear landing attempt. Positive and negative
prime-torus coordinate multipliers are mutual inverses. If a single-valued linear relation sends
the positive source action to a square-zero partial target action and remains invariant under the
negative source action with any partial target partner, then every relation output vanishes. No
closedness, density, boundedness, target representation law, or target inverse law is required.

Consequently the actual Boolean Gamma--theta creator cannot itself be a prime-coordinate action
in a nonzero JAS source landing. A surviving construction must retain a reversible target action;
literal creation may occur only after compression, in a corner, or through a bilateral dilation.
-/

open Complex Real MeasureTheory Set
open scoped ENNReal LinearPMap

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

private abbrev jasGammaThetaMeasure : Measure (JASGammaThetaSupport × ℝ) :=
  (Measure.count : Measure JASGammaThetaSupport).prod (volume : Measure ℝ)

/-- Creation energy on complementary support sectors has zero pointwise product. -/
theorem jasGammaThetaCreationEnergy_mul_toggle_eq_zero
    (x : ℝ) (p : Nat.Primes) (z : JASGammaThetaSupport × ℝ) :
    (jasGammaThetaCreationEnergy x p z : ℂ) *
        (jasGammaThetaCreationEnergy x p
          (jasGammaSupportToggle p z.1, z.2) : ℂ) = 0 := by
  by_cases hp : p ∈ z.1
  · simp [jasGammaThetaCreationEnergy, jasGammaSupportToggle_apply, hp]
  · simp [jasGammaThetaCreationEnergy, jasGammaSupportToggle_apply, hp]

/-- Pointwise almost-everywhere formula for the actual unbounded Gamma--theta creator. -/
theorem jasGammaThetaCreation_apply_ae
    (x : ℝ) (p : Nat.Primes) (f : (jasGammaThetaCreation x p).domain) :
    ((jasGammaThetaCreation x p f : JASGammaThetaL2) :
        JASGammaThetaSupport × ℝ → ℂ) =ᵐ[jasGammaThetaMeasure]
      fun z =>
        (jasGammaThetaCreationEnergy x p
          (jasGammaSupportToggle p z.1, z.2) : ℂ) *
          (f : JASGammaThetaSupport × ℝ → ℂ)
            (jasGammaSupportToggle p z.1, z.2) := by
  let g : (maximalRealL2Mul jasGammaThetaMeasure
      (jasGammaThetaCreationEnergy x p)).domain :=
    ⟨f, f.property⟩
  change ((Lp.compMeasurePreserving
      (jasGammaThetaToggleMeasurableEquiv p)
      (jasGammaThetaToggle_measurePreserving p)
      (maximalRealL2Mul jasGammaThetaMeasure
        (jasGammaThetaCreationEnergy x p) g) : JASGammaThetaL2) :
      JASGammaThetaSupport × ℝ → ℂ) =ᵐ[jasGammaThetaMeasure] _
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (maximalRealL2Mul jasGammaThetaMeasure
        (jasGammaThetaCreationEnergy x p) g)
      (jasGammaThetaToggle_measurePreserving p),
    (maximalRealL2Mul_apply_ae jasGammaThetaMeasure
      (jasGammaThetaCreationEnergy x p) g).comp_tendsto
        (jasGammaThetaToggle_measurePreserving p).quasiMeasurePreserving.tendsto_ae]
      with z hcomp hmul
  rw [hcomp, hmul]
  rfl

/-- Every actual creator output lies in the creator's own natural domain. -/
theorem jasGammaThetaCreation_apply_mem_domain
    (x : ℝ) (p : Nat.Primes) (f : (jasGammaThetaCreation x p).domain) :
    jasGammaThetaCreation x p f ∈ (jasGammaThetaCreation x p).domain := by
  change MemLp (fun z => (jasGammaThetaCreationEnergy x p z : ℂ) *
    ((jasGammaThetaCreation x p f : JASGammaThetaL2) :
      JASGammaThetaSupport × ℝ → ℂ) z) 2 jasGammaThetaMeasure
  refine (memLp_congr_ae ?_).mpr MemLp.zero
  filter_upwards [jasGammaThetaCreation_apply_ae x p f] with z hz
  rw [hz]
  calc
    (jasGammaThetaCreationEnergy x p z : ℂ) *
          ((jasGammaThetaCreationEnergy x p
            (jasGammaSupportToggle p z.1, z.2) : ℂ) *
            (f : JASGammaThetaSupport × ℝ → ℂ)
              (jasGammaSupportToggle p z.1, z.2)) =
        ((jasGammaThetaCreationEnergy x p z : ℂ) *
          (jasGammaThetaCreationEnergy x p
            (jasGammaSupportToggle p z.1, z.2) : ℂ)) *
          (f : JASGammaThetaSupport × ℝ → ℂ)
            (jasGammaSupportToggle p z.1, z.2) := by ring
    _ = 0 := by rw [jasGammaThetaCreationEnergy_mul_toggle_eq_zero]; simp

/-- Natural second-application domain point for the actual creator. -/
def jasGammaThetaCreationSecondDomain
    (x : ℝ) (p : Nat.Primes) (f : (jasGammaThetaCreation x p).domain) :
    (jasGammaThetaCreation x p).domain :=
  ⟨jasGammaThetaCreation x p f, jasGammaThetaCreation_apply_mem_domain x p f⟩

/-- Global Boolean nilpotence: the actual closed unbounded creator squares to zero on its full
natural domain. -/
theorem jasGammaThetaCreation_sq_apply
    (x : ℝ) (p : Nat.Primes) (f : (jasGammaThetaCreation x p).domain) :
    jasGammaThetaCreation x p (jasGammaThetaCreationSecondDomain x p f) = 0 := by
  apply Lp.ext
  filter_upwards [
    jasGammaThetaCreation_apply_ae x p (jasGammaThetaCreationSecondDomain x p f),
    (jasGammaThetaCreation_apply_ae x p f).comp_tendsto
      (jasGammaThetaToggle_measurePreserving p).quasiMeasurePreserving.tendsto_ae,
    Lp.coeFn_zero ℂ 2 jasGammaThetaMeasure] with z hsecond hfirst hzero
  rw [hsecond, hzero]
  change (jasGammaThetaCreationEnergy x p
      (jasGammaSupportToggle p z.1, z.2) : ℂ) *
      ((jasGammaThetaCreation x p f : JASGammaThetaL2) :
        JASGammaThetaSupport × ℝ → ℂ)
          (jasGammaSupportToggle p z.1, z.2) = 0
  change ((jasGammaThetaCreation x p f : JASGammaThetaL2) :
      JASGammaThetaSupport × ℝ → ℂ)
        (jasGammaSupportToggle p z.1, z.2) =
      (jasGammaThetaCreationEnergy x p
        (jasGammaSupportToggle p (jasGammaSupportToggle p z.1), z.2) : ℂ) *
        (f : JASGammaThetaSupport × ℝ → ℂ)
          (jasGammaSupportToggle p (jasGammaSupportToggle p z.1), z.2) at hfirst
  have htoggle :
      jasGammaSupportToggle p (jasGammaSupportToggle p z.1) = z.1 :=
    jasGammaSupportToggleFun_involutive p z.1
  rw [htoggle] at hfirst
  rw [hfirst]
  change (jasGammaThetaCreationEnergy x p
      (jasGammaSupportToggle p z.1, z.2) : ℂ) *
      ((jasGammaThetaCreationEnergy x p z : ℂ) *
        (f : JASGammaThetaSupport × ℝ → ℂ) z) = 0
  calc
    (jasGammaThetaCreationEnergy x p
          (jasGammaSupportToggle p z.1, z.2) : ℂ) *
        ((jasGammaThetaCreationEnergy x p z : ℂ) *
          (f : JASGammaThetaSupport × ℝ → ℂ) z) =
      ((jasGammaThetaCreationEnergy x p z : ℂ) *
        (jasGammaThetaCreationEnergy x p
          (jasGammaSupportToggle p z.1, z.2) : ℂ)) *
        (f : JASGammaThetaSupport × ℝ → ℂ) z := by ring
    _ = 0 := by rw [jasGammaThetaCreationEnergy_mul_toggle_eq_zero]; simp

section RelationRigidity

variable {H₁ H₂ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

/-- Block action with a bounded source operator and a partially defined target operator. -/
def partialTargetRelationAction
    (A : H₁ →L[ℂ] H₁) (B : H₂ →ₗ.[ℂ] H₂)
    (z : HilbertSum H₁ H₂) (hB : hilbertSumSnd z ∈ B.domain) :
    HilbertSum H₁ H₂ :=
  hilbertSumInl (A (hilbertSumFst z)) +
    hilbertSumInr (B ⟨hilbertSumSnd z, hB⟩)

@[simp] theorem partialTargetRelationAction_fst
    (A : H₁ →L[ℂ] H₁) (B : H₂ →ₗ.[ℂ] H₂)
    (z : HilbertSum H₁ H₂) (hB : hilbertSumSnd z ∈ B.domain) :
    hilbertSumFst (partialTargetRelationAction A B z hB) =
      A (hilbertSumFst z) := by
  rw [partialTargetRelationAction, map_add, hilbertSumFst_inl,
    hilbertSumFst_inr, add_zero]

@[simp] theorem partialTargetRelationAction_snd
    (A : H₁ →L[ℂ] H₁) (B : H₂ →ₗ.[ℂ] H₂)
    (z : HilbertSum H₁ H₂) (hB : hilbertSumSnd z ∈ B.domain) :
    hilbertSumSnd (partialTargetRelationAction A B z hB) =
      B ⟨hilbertSumSnd z, hB⟩ := by
  rw [partialTargetRelationAction, map_add, hilbertSumSnd_inl,
    hilbertSumSnd_inr, zero_add]

/-- Relation invariance under a bounded source action and a partial target action, including the
target-domain obligation at every relation point. -/
def PartialTargetRelationInvariant
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (A : H₁ →L[ℂ] H₁) (B : H₂ →ₗ.[ℂ] H₂) : Prop :=
  ∀ z, z ∈ R →
    ∃ hB : hilbertSumSnd z ∈ B.domain,
      partialTargetRelationAction A B z hB ∈ R

/-- A partial linear operator is square-zero when every domain vector maps back into the domain
and its second application vanishes. -/
def LinearPMapSquareZero (B : H₂ →ₗ.[ℂ] H₂) : Prop :=
  ∀ y (hy : y ∈ B.domain),
    ∃ hBy : B ⟨y, hy⟩ ∈ B.domain,
      B ⟨B ⟨y, hy⟩, hBy⟩ = 0

/-- Single-valuedness makes relation outputs equal whenever source coordinates agree. -/
theorem hilbertRelation_snd_eq_of_fst_eq
    {R : Submodule ℂ (HilbertSum H₁ H₂)}
    (hsingle : HilbertRelationSingleValued R)
    {z w : HilbertSum H₁ H₂} (hz : z ∈ R) (hw : w ∈ R)
    (hfst : hilbertSumFst z = hilbertSumFst w) :
    hilbertSumSnd z = hilbertSumSnd w := by
  have hdiff : z - w ∈ R := R.sub_mem hz hw
  have hfstDiff : hilbertSumFst (z - w) = 0 := by
    rw [map_sub, hfst, sub_self]
  have hdecomp := hilbertSum_inl_add_inr (z - w)
  rw [hfstDiff, map_zero, zero_add] at hdecomp
  have hmem : hilbertSumInr (hilbertSumSnd (z - w)) ∈ R := by
    rw [hdecomp]
    exact hdiff
  have hout := hsingle _ hmem
  rw [map_sub] at hout
  exact sub_eq_zero.mp hout

/-- Inverse source actions cannot land nontrivially in a square-zero target action. The target
partner for the inverse source action is completely arbitrary and only partially defined. -/
theorem hilbertRelation_output_eq_zero_of_inverse_source_squareZero_target
    (R : Submodule ℂ (HilbertSum H₁ H₂))
    (Aplus Aminus : H₁ →L[ℂ] H₁)
    (C D : H₂ →ₗ.[ℂ] H₂)
    (hsingle : HilbertRelationSingleValued R)
    (hleft : ∀ u, Aminus (Aplus u) = u)
    (hright : ∀ u, Aplus (Aminus u) = u)
    (hplus : PartialTargetRelationInvariant R Aplus C)
    (hminus : PartialTargetRelationInvariant R Aminus D)
    (hsq : LinearPMapSquareZero C)
    (z : HilbertSum H₁ H₂) (hz : z ∈ R) :
    hilbertSumSnd z = 0 := by
  obtain ⟨hyC, hzC⟩ := hplus z hz
  obtain ⟨hCyD, hzDC⟩ := hminus _ hzC
  have hDC :
      D ⟨hilbertSumSnd (partialTargetRelationAction Aplus C z hyC), hCyD⟩ =
        hilbertSumSnd z := by
    have hfstBack :
        hilbertSumFst
            (partialTargetRelationAction Aminus D
              (partialTargetRelationAction Aplus C z hyC) hCyD) =
          hilbertSumFst z := by
      rw [partialTargetRelationAction_fst,
        partialTargetRelationAction_fst, hleft]
    have hout := hilbertRelation_snd_eq_of_fst_eq hsingle hzDC hz hfstBack
    rw [partialTargetRelationAction_snd] at hout
    exact hout
  obtain ⟨hyD, hzD⟩ := hminus z hz
  obtain ⟨hDyC, hzCD⟩ := hplus _ hzD
  have hCD :
      C ⟨hilbertSumSnd (partialTargetRelationAction Aminus D z hyD), hDyC⟩ =
        hilbertSumSnd z := by
    have hfstBack :
        hilbertSumFst
            (partialTargetRelationAction Aplus C
              (partialTargetRelationAction Aminus D z hyD) hDyC) =
          hilbertSumFst z := by
      rw [partialTargetRelationAction_fst,
        partialTargetRelationAction_fst, hright]
    have hout := hilbertRelation_snd_eq_of_fst_eq hsingle hzCD hz hfstBack
    rw [partialTargetRelationAction_snd] at hout
    exact hout
  obtain ⟨hCDyC, hCCDy⟩ :=
    hsq (hilbertSumSnd (partialTargetRelationAction Aminus D z hyD)) hDyC
  have hCyZero : C ⟨hilbertSumSnd z, hyC⟩ = 0 := by
    have harg :
        (⟨C ⟨hilbertSumSnd
          (partialTargetRelationAction Aminus D z hyD), hDyC⟩, hCDyC⟩ : C.domain) =
          ⟨hilbertSumSnd z, hyC⟩ := by
      ext
      exact hCD
    rw [harg] at hCCDy
    exact hCCDy
  have hargD :
      (⟨hilbertSumSnd (partialTargetRelationAction Aplus C z hyC), hCyD⟩ :
        D.domain) = 0 := by
    ext
    exact (partialTargetRelationAction_snd Aplus C z hyC).trans hCyZero
  have hDzero := congrArg D.toFun hargD
  change D ⟨hilbertSumSnd
    (partialTargetRelationAction Aplus C z hyC), hCyD⟩ = D 0 at hDzero
  rw [hDC] at hDzero
  simpa using hDzero

end RelationRigidity

/-- Actual prime-Poisson multiplication by one integral prime-coordinate character. -/
def jasPrimeCoordinateMul
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes) (k : ℤ) :
    PrimePoissonL2 sigma t hsigma →L[ℂ] PrimePoissonL2 sigma t hsigma :=
  continuousL2Mul (primePoissonMeasure sigma t hsigma)
    (torusCharacter (Finsupp.single p k))

/-- Negative then positive prime-coordinate multiplication is the identity. -/
theorem jasPrimeCoordinateMul_neg_pos
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes)
    (u : PrimePoissonL2 sigma t hsigma) :
    jasPrimeCoordinateMul sigma t hsigma p (-1)
        (jasPrimeCoordinateMul sigma t hsigma p 1 u) = u := by
  let up : C(PrimeTorus, ℂ) := torusCharacter (Finsupp.single p (1 : ℤ))
  let um : C(PrimeTorus, ℂ) := torusCharacter (Finsupp.single p (-1 : ℤ))
  have hprod : um * up = 1 := by
    ext z
    rw [show (um * up) z = um z * up z by rfl,
      ← torusCharacter_add_index]
    simp [torusCharacter_zero]
  apply Lp.ext
  filter_upwards [
    continuousL2Mul_coeFn (primePoissonMeasure sigma t hsigma) um
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) up u),
    continuousL2Mul_coeFn (primePoissonMeasure sigma t hsigma) up u]
      with z hm hp
  change ((continuousL2Mul (primePoissonMeasure sigma t hsigma) um
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) up u) :
        PrimePoissonL2 sigma t hsigma) : PrimeTorus → ℂ) z =
    (u : PrimeTorus → ℂ) z
  rw [hm, hp, ← mul_assoc]
  have hz := DFunLike.congr_fun hprod z
  change um z * up z = 1 at hz
  rw [hz, one_mul]

/-- Positive then negative prime-coordinate multiplication is the identity. -/
theorem jasPrimeCoordinateMul_pos_neg
    (sigma t : ℝ) (hsigma : 0 < sigma) (p : Nat.Primes)
    (u : PrimePoissonL2 sigma t hsigma) :
    jasPrimeCoordinateMul sigma t hsigma p 1
        (jasPrimeCoordinateMul sigma t hsigma p (-1) u) = u := by
  let up : C(PrimeTorus, ℂ) := torusCharacter (Finsupp.single p (1 : ℤ))
  let um : C(PrimeTorus, ℂ) := torusCharacter (Finsupp.single p (-1 : ℤ))
  have hprod : up * um = 1 := by
    ext z
    rw [show (up * um) z = up z * um z by rfl,
      ← torusCharacter_add_index]
    simp [torusCharacter_zero]
  apply Lp.ext
  filter_upwards [
    continuousL2Mul_coeFn (primePoissonMeasure sigma t hsigma) up
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) um u),
    continuousL2Mul_coeFn (primePoissonMeasure sigma t hsigma) um u]
      with z hp hm
  change ((continuousL2Mul (primePoissonMeasure sigma t hsigma) up
      (continuousL2Mul (primePoissonMeasure sigma t hsigma) um u) :
        PrimePoissonL2 sigma t hsigma) : PrimeTorus → ℂ) z =
    (u : PrimeTorus → ℂ) z
  rw [hp, hm, ← mul_assoc]
  have hz := DFunLike.congr_fun hprod z
  change up z * um z = 1 at hz
  rw [hz, one_mul]

/-- Direct partial JAS source landing: positive prime-coordinate multiplication acts by the
actual Gamma--theta creator, negative multiplication has an arbitrary partial target partner, and
the single-valued relation has nonzero output. -/
def JASPrimeCoordinateGammaThetaPartialLanding : Prop :=
  ∃ (sigma t : ℝ) (hsigma : 0 < sigma) (x : ℝ) (p : Nat.Primes)
      (R : Submodule ℂ
        (HilbertSum (PrimePoissonL2 sigma t hsigma) JASGammaThetaL2))
      (D : JASGammaThetaL2 →ₗ.[ℂ] JASGammaThetaL2),
    HilbertRelationSingleValued R ∧
    PartialTargetRelationInvariant R
      (jasPrimeCoordinateMul sigma t hsigma p 1)
      (jasGammaThetaCreation x p) ∧
    PartialTargetRelationInvariant R
      (jasPrimeCoordinateMul sigma t hsigma p (-1)) D ∧
    ∃ z ∈ R, hilbertSumSnd z ≠ 0

/-- Closed route-class no-go: no nonzero single-valued partial source relation can identify a
prime coordinate with the actual Gamma--theta Boolean creator. -/
theorem not_JASPrimeCoordinateGammaThetaPartialLanding :
    ¬ JASPrimeCoordinateGammaThetaPartialLanding := by
  rintro ⟨sigma, t, hsigma, x, p, R, D,
    hsingle, hplus, hminus, z, hz, hout⟩
  apply hout
  apply hilbertRelation_output_eq_zero_of_inverse_source_squareZero_target
    R
    (jasPrimeCoordinateMul sigma t hsigma p 1)
    (jasPrimeCoordinateMul sigma t hsigma p (-1))
    (jasGammaThetaCreation x p) D hsingle
  · exact jasPrimeCoordinateMul_neg_pos sigma t hsigma p
  · exact jasPrimeCoordinateMul_pos_neg sigma t hsigma p
  · exact hplus
  · exact hminus
  · intro y hy
    let f : (jasGammaThetaCreation x p).domain := ⟨y, hy⟩
    refine ⟨jasGammaThetaCreation_apply_mem_domain x p f, ?_⟩
    simpa [f, jasGammaThetaCreationSecondDomain] using
      jasGammaThetaCreation_sq_apply x p f
  · exact hz

end

end RHTower
