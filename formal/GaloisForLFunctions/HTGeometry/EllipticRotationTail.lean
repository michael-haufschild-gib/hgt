import GaloisForLFunctions.HTGeometry.PlaneScaleSimilarity
import GaloisForLFunctions.HTGeometry.TwistedReparametrizationAutomorphism
import GaloisForLFunctions.HTGeometry.RootOfUnityScalingFixedField
import GaloisForLFunctions.HTGeometry.DifferentialSubfieldTransfer
import GaloisForLFunctions.HTGeometry.FreeDifferentialLinearAction
import GaloisForLFunctions.HTGeometry.NonautonomousProjectiveTimeLaw
import GaloisForLFunctions.HTGeometry.FreeDifferentialScalingAutomorphism
import GaloisForLFunctions.HTGeometry.TranslationRotationDeckFixedField

/-!
# The rotation layer of a compact parabolic signature

An orbifold rotation of the cover by a root of unity of exact order `n` acts on the generic
reparametrisation of the meromorphic plane field as a similarity: it rescales the variable, hence
rescales every jet by the same root of unity.  Its invariants inside the velocity field are exactly
the differential rational functions of the `n`-th power of the velocity.

Together with the translation layer this is the complete deck fixed field of a compact parabolic
signature on a carrier where the coordinate is a differential-generic point.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

local instance rotComplexDifferential : Differential ℂ where
  deriv := 0

local instance rotComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ (ReparamField MeromorphicPlane) :=
  ⟨fun c => by
    have htower : algebraMap ℂ (ReparamField MeromorphicPlane) c
        = algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) (constPlane c) := by
      rw [IsScalarTower.algebraMap_apply ℂ MeromorphicPlane (ReparamField MeromorphicPlane)]
      rfl
    rw [htower]
    show ReparamField.fieldDerivation MeromorphicPlane _ = _
    rw [← ReparamField.deriv_eq, ReparamField.deriv_algebraMap, deriv_constPlane]
    show algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) 0 * _ = _
    rw [map_zero, zero_mul]
    show (0 : ReparamField MeromorphicPlane) = algebraMap ℂ (ReparamField MeromorphicPlane) 0
    rw [map_zero]⟩

theorem constPlane_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) : constPlane ζ ≠ 0 := by
  intro h
  exact hζ (constPlane_injective (by rw [h, map_zero]))

theorem planeScaleEquiv_constPlane_self {ζ : ℂ} (hζ : ζ ≠ 0) :
    planeScaleEquiv ζ hζ (constPlane ζ) = constPlane ζ := by
  show planeScale ζ hζ (constPlane ζ) = constPlane ζ
  exact planeScale_constPlane ζ hζ ζ

/-- The rotation of the cover by a nonzero scalar, on the generic reparametrisation. -/
noncomputable def rotationEquiv {ζ : ℂ} (hζ : ζ ≠ 0) :
    ReparamField MeromorphicPlane ≃+* ReparamField MeromorphicPlane :=
  ReparamField.twistFieldEquiv (constPlane_ne_zero hζ) (planeScaleEquiv_constPlane_self hζ)

theorem rotationEquiv_base {ζ : ℂ} (hζ : ζ ≠ 0) (a : MeromorphicPlane) :
    rotationEquiv hζ (algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) a)
      = algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) (planeScale ζ hζ a) :=
  ReparamField.twistFieldEquiv_base _ _ a

theorem rotationEquiv_jet {ζ : ℂ} (hζ : ζ ≠ 0) (i : ℕ) :
    rotationEquiv hζ (ReparamField.jet i : ReparamField MeromorphicPlane)
      = algebraMap ℂ (ReparamField MeromorphicPlane) ζ * ReparamField.jet i := by
  rw [rotationEquiv, ReparamField.twistFieldEquiv_jet,
    IsScalarTower.algebraMap_apply ℂ MeromorphicPlane (ReparamField MeromorphicPlane)]
  rfl

theorem rotationEquiv_deriv {ζ : ℂ} (hζ : ζ ≠ 0) (x : ReparamField MeromorphicPlane) :
    rotationEquiv hζ (x′) = (rotationEquiv hζ x)′ :=
  ReparamField.twistFieldEquiv_deriv _ _ (deriv_constPlane ζ)
    (fun a => planeScale_deriv ζ hζ a) x

/-- The rotation, as an automorphism over the constants. -/
noncomputable def rotationAlgEquiv {ζ : ℂ} (hζ : ζ ≠ 0) :
    ReparamField MeromorphicPlane ≃ₐ[ℂ] ReparamField MeromorphicPlane :=
  { rotationEquiv hζ with
    commutes' := by
      intro c
      have htower : algebraMap ℂ (ReparamField MeromorphicPlane) c
          = algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) (constPlane c) := by
        rw [IsScalarTower.algebraMap_apply ℂ MeromorphicPlane (ReparamField MeromorphicPlane)]
        rfl
      show rotationEquiv hζ (algebraMap ℂ (ReparamField MeromorphicPlane) c) = _
      rw [htower, rotationEquiv_base, planeScale_constPlane] }

@[simp] theorem rotationAlgEquiv_apply {ζ : ℂ} (hζ : ζ ≠ 0) (x : ReparamField MeromorphicPlane) :
    rotationAlgEquiv hζ x = rotationEquiv hζ x := rfl

/-- **The rotation fixes the power current.**  A root of unity of order `n` fixes every differential
rational function of the `n`-th power of the velocity. -/
theorem rotation_fixes_jetPow {ζ : ℂ} (hζ : ζ ≠ 0) {n : ℕ} (hpow : ζ ^ n = 1)
    {x : ReparamField MeromorphicPlane}
    (hx : x ∈ differentialAdjoin ℂ
      ({(ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n} : Set _)) :
    rotationEquiv hζ x = x := by
  have hfix : rotationEquiv hζ ((ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n)
      = (ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n := by
    rw [map_pow, rotationEquiv_jet, mul_pow, ← map_pow, hpow, map_one, one_mul]
  have hrange : ({(ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n} : Set _)
      = Set.range (fun _ : Unit => (ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n) :=
    (Set.range_const).symm
  rw [hrange] at hx
  exact DifferentialAlgEquiv.fixed_on_differentialAdjoin
    (⟨rotationAlgEquiv hζ, fun w => rotationEquiv_deriv hζ w⟩ :
      DifferentialAlgEquiv ℂ (ReparamField MeromorphicPlane))
    (fun _ : Unit => (ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n)
    (fun _ => hfix) hx

/-- The power current lies in the velocity field. -/
theorem jetPow_mem_velocityField (n : ℕ) :
    (ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n ∈ velocityField :=
  pow_mem (jet_mem_velocityField 0) n

/-- **The power current field lies in the velocity field.** -/
theorem differentialAdjoin_jetPow_le_velocityField (n : ℕ) :
    differentialAdjoin ℂ ({(ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n} : Set _)
      ≤ velocityField := by
  refine differentialAdjoin_le ℂ ?_ ?_
  · intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact jetPow_mem_velocityField n
  · rw [velocityField]
    exact derivationClosed_differentialAdjoin ℂ _

instance charZeroMeromorphicPlane : CharZero MeromorphicPlane :=
  charZero_of_injective_algebraMap constPlane_injective

set_option maxHeartbeats 1000000 in
/-- **The rotation-invariant part of the velocity field is the power current field.**  An element of
the velocity field fixed by a rotation of exact order `n` is a differential rational function of the
`n`-th power of the velocity. -/
theorem mem_differentialAdjoin_jetPow_of_rotation_invariant
    {ζ : ℂˣ} {n : ℕ} (hn : 0 < n) (hord : orderOf ζ = n)
    {x : ReparamField MeromorphicPlane} (hxV : x ∈ velocityField)
    (hxρ : rotationEquiv (Units.ne_zero ζ) x = x) :
    x ∈ differentialAdjoin ℂ
      ({(ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n} : Set _) := by
  classical
  set ρ := rotationAlgEquiv (Units.ne_zero ζ) with hρdef
  have hρderiv : ∀ z : ReparamField MeromorphicPlane, ρ z′ = (ρ z)′ := fun z =>
    rotationEquiv_deriv (Units.ne_zero ζ) z
  have hρjet : ρ (ReparamField.jet 0 : ReparamField MeromorphicPlane)
      = algebraMap ℂ (ReparamField MeromorphicPlane) (ζ : ℂ) * ReparamField.jet 0 :=
    rotationEquiv_jet (Units.ne_zero ζ) 0
  set L : IntermediateField ℂ (ReparamField MeromorphicPlane) :=
    differentialAdjoin ℂ (Set.range (fun _ : Fin 1 =>
      (ReparamField.jet 0 : ReparamField MeromorphicPlane))) with hLdef
  have hLset : Set.range (fun _ : Fin 1 => (ReparamField.jet 0 : ReparamField MeromorphicPlane))
      = ({ReparamField.jet 0} : Set (ReparamField MeromorphicPlane)) := Set.range_const
  have hLeq : L = velocityField := by rw [hLdef, hLset]; rfl
  have hLclosed : DerivationClosed L :=
    derivationClosed_differentialAdjoin ℂ (Set.range (fun _ : Fin 1 =>
      (ReparamField.jet 0 : ReparamField MeromorphicPlane)))
  letI : Differential ↥L := derivationClosedDifferential L hLclosed
  letI : DifferentialAlgebra ℂ ↥L := by
    refine ⟨fun a ↦ ?_⟩
    apply Subtype.ext
    show (((algebraMap ℂ ↥L a)′ : ↥L) : ReparamField MeromorphicPlane)
      = ((algebraMap ℂ ↥L (a′) : ↥L) : ReparamField MeromorphicPlane)
    have h1 : (((algebraMap ℂ ↥L a)′ : ↥L) : ReparamField MeromorphicPlane)
        = ((algebraMap ℂ ↥L a : ↥L) : ReparamField MeromorphicPlane)′ :=
      derivationClosedDifferential_apply L hLclosed _
    have h2 : ((algebraMap ℂ ↥L a : ↥L) : ReparamField MeromorphicPlane)
        = algebraMap ℂ (ReparamField MeromorphicPlane) a :=
      (IsScalarTower.algebraMap_apply ℂ ↥L (ReparamField MeromorphicPlane) a).symm
    have h3 : ((algebraMap ℂ ↥L (a′) : ↥L) : ReparamField MeromorphicPlane)
        = algebraMap ℂ (ReparamField MeromorphicPlane) (a′) :=
      (IsScalarTower.algebraMap_apply ℂ ↥L (ReparamField MeromorphicPlane) (a′)).symm
    rw [h1, h2, h3]
    exact DifferentialAlgebra.deriv_algebraMap a
  haveI : CharZero ↥L := by
    refine ⟨fun m k h ↦ ?_⟩
    have hcoe : ((m : ↥L) : ReparamField MeromorphicPlane)
        = ((k : ↥L) : ReparamField MeromorphicPlane) := congrArg Subtype.val h
    have hm : ((m : ↥L) : ReparamField MeromorphicPlane)
        = (m : ReparamField MeromorphicPlane) := by push_cast; rfl
    have hk : ((k : ↥L) : ReparamField MeromorphicPlane)
        = (k : ReparamField MeromorphicPlane) := by push_cast; rfl
    rw [hm, hk] at hcoe
    exact Nat.cast_injective hcoe
  set v₀ : ↥L := ⟨ReparamField.jet 0, by
    rw [hLdef, hLset]
    exact subset_differentialAdjoin ℂ
      ({(ReparamField.jet 0 : ReparamField MeromorphicPlane)} : Set _) rfl⟩ with hv₀def
  have hv₀coe : ((v₀ : ↥L) : ReparamField MeromorphicPlane) = ReparamField.jet 0 := rfl
  have hindT : DifferentialIndependent ℂ
      (fun _ : Fin 1 => (ReparamField.jet 0 : ReparamField MeromorphicPlane)) := by
    have hU : AlgebraicIndependent ℂ (fun p : Unit × ℕ =>
        differentialJet p.2 (ReparamField.jet 0 : ReparamField MeromorphicPlane)) :=
      differentialIndependent_reparamJet_zero
    exact hU.comp (fun p : Fin 1 × ℕ => (((), p.2) : Unit × ℕ)) (by
      rintro ⟨i, m⟩ ⟨j, m'⟩ hp
      have hm : m = m' := congrArg Prod.snd hp
      have hij : i = j := Subsingleton.elim i j
      rw [hm, hij])
  have hv : DifferentialIndependent ℂ (fun _ : Fin 1 => v₀) :=
    differentialIndependent_subfield L hLclosed (fun _ : Fin 1 => v₀) hindT
  have hgenv : differentialAdjoin ℂ (Set.range (fun _ : Fin 1 => v₀)) = ⊤ := by
    have h := differentialAdjoin_adjoinLift_eq_top (F := ℂ)
      (fun _ : Fin 1 => (ReparamField.jet 0 : ReparamField MeromorphicPlane))
    have hr : Set.range (adjoinLift ℂ
        (fun _ : Fin 1 => (ReparamField.jet 0 : ReparamField MeromorphicPlane)))
        = Set.range (fun _ : Fin 1 => v₀) := by
      ext w
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨0, Subtype.ext rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨0, Subtype.ext rfl⟩
    rw [hr] at h
    exact h
  have hv0 : v₀ ≠ 0 := by
    intro h0
    have hc := congrArg Subtype.val h0
    rw [hv₀coe] at hc
    have hjet0 : (ReparamField.jet 0 : ReparamField MeromorphicPlane) ≠ 0 := by
      intro hz
      have hX : (MvPolynomial.X 0 : ReparamPoly MeromorphicPlane) = 0 :=
        IsFractionRing.injective (ReparamPoly MeromorphicPlane) (ReparamField MeromorphicPlane)
          (by rw [map_zero]; exact hz)
      exact MvPolynomial.X_ne_zero 0 hX
    exact hjet0 hc
  have hmapadj : ∀ (σ : ReparamField MeromorphicPlane ≃ₐ[ℂ] ReparamField MeromorphicPlane),
      (∀ z : ReparamField MeromorphicPlane, σ z′ = (σ z)′) →
      ∀ w ∈ L, σ w ∈ differentialAdjoin ℂ
        ({σ (ReparamField.jet 0 : ReparamField MeromorphicPlane)} : Set _) := by
    intro σ hσd w hw
    have hmap := map_differentialAdjoin (σ : ReparamField MeromorphicPlane →ₐ[ℂ]
      ReparamField MeromorphicPlane) (fun z ↦ hσd z)
      (Set.range (fun _ : Fin 1 => (ReparamField.jet 0 : ReparamField MeromorphicPlane)))
    have hwmem : σ w ∈ IntermediateField.map (σ : ReparamField MeromorphicPlane →ₐ[ℂ]
      ReparamField MeromorphicPlane) L := ⟨w, hw, rfl⟩
    rw [hLdef] at hwmem
    rw [hmap] at hwmem
    have himg : (σ : ReparamField MeromorphicPlane →ₐ[ℂ] ReparamField MeromorphicPlane) ''
        Set.range (fun _ : Fin 1 => (ReparamField.jet 0 : ReparamField MeromorphicPlane))
        = ({σ (ReparamField.jet 0 : ReparamField MeromorphicPlane)} : Set _) := by
      rw [hLset]
      simp
    rwa [himg] at hwmem
  have hρmem : ∀ w ∈ L, ρ w ∈ L := by
    intro w hw
    have h1 := hmapadj ρ hρderiv w hw
    rw [hρjet] at h1
    have h2 : differentialAdjoin ℂ ({algebraMap ℂ (ReparamField MeromorphicPlane) (ζ : ℂ)
          * ReparamField.jet 0} : Set _)
        = differentialAdjoin ℂ ({(ReparamField.jet 0 : ReparamField MeromorphicPlane)} : Set _) :=
      differentialAdjoin_const_mul (Units.ne_zero ζ) _
    rw [h2] at h1
    rw [hLdef, hLset]
    exact h1
  have hρsymmderiv : ∀ z : ReparamField MeromorphicPlane, ρ.symm z′ = (ρ.symm z)′ := by
    intro z
    have h1 : ρ ((ρ.symm z)′) = z′ := by
      have h0 := hρderiv (ρ.symm z)
      rw [ρ.apply_symm_apply] at h0
      exact h0
    calc ρ.symm z′ = ρ.symm (ρ ((ρ.symm z)′)) := by rw [h1]
      _ = (ρ.symm z)′ := ρ.symm_apply_apply _
  have hζζ : ((ζ⁻¹ : ℂˣ) : ℂ) * ((ζ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel ζ, Units.val_one]
  have hρsymjet : ρ.symm (ReparamField.jet 0 : ReparamField MeromorphicPlane)
      = algebraMap ℂ (ReparamField MeromorphicPlane) ((ζ⁻¹ : ℂˣ) : ℂ) * ReparamField.jet 0 := by
    apply ρ.injective
    rw [ρ.apply_symm_apply, map_mul, AlgEquiv.commutes, hρjet, ← mul_assoc, ← map_mul, hζζ,
      map_one, one_mul]
  have hρsymmem : ∀ w ∈ L, ρ.symm w ∈ L := by
    intro w hw
    have h1 := hmapadj ρ.symm hρsymmderiv w hw
    rw [hρsymjet] at h1
    have h2 : differentialAdjoin ℂ ({algebraMap ℂ (ReparamField MeromorphicPlane)
          ((ζ⁻¹ : ℂˣ) : ℂ) * ReparamField.jet 0} : Set _)
        = differentialAdjoin ℂ ({(ReparamField.jet 0 : ReparamField MeromorphicPlane)} : Set _) :=
      differentialAdjoin_const_mul (Units.ne_zero ζ⁻¹) _
    rw [h2] at h1
    rw [hLdef, hLset]
    exact h1
  set ρL : ↥L ≃ₐ[ℂ] ↥L :=
    { toFun := fun w ↦ ⟨ρ w, hρmem w w.2⟩
      invFun := fun w ↦ ⟨ρ.symm w, hρsymmem w w.2⟩
      left_inv := fun w ↦ Subtype.ext (ρ.symm_apply_apply w)
      right_inv := fun w ↦ Subtype.ext (ρ.apply_symm_apply w)
      map_mul' := fun a b ↦ Subtype.ext (map_mul ρ (a : ReparamField MeromorphicPlane)
        (b : ReparamField MeromorphicPlane))
      map_add' := fun a b ↦ Subtype.ext (map_add ρ (a : ReparamField MeromorphicPlane)
        (b : ReparamField MeromorphicPlane))
      commutes' := fun a ↦ Subtype.ext (ρ.commutes a) } with hρLdef
  have hρLderiv : ∀ z : ↥L, ρL z′ = (ρL z)′ := by
    intro z
    apply Subtype.ext
    have h1 : ((ρL z′ : ↥L) : ReparamField MeromorphicPlane)
        = ρ ((z′ : ↥L) : ReparamField MeromorphicPlane) := rfl
    have h2 : ((z′ : ↥L) : ReparamField MeromorphicPlane)
        = ((z : ↥L) : ReparamField MeromorphicPlane)′ :=
      derivationClosedDifferential_apply L hLclosed z
    have h3 : (((ρL z)′ : ↥L) : ReparamField MeromorphicPlane)
        = ((ρL z : ↥L) : ReparamField MeromorphicPlane)′ :=
      derivationClosedDifferential_apply L hLclosed (ρL z)
    rw [h1, h2, h3]
    exact hρderiv _
  have hρLpalette : ρL v₀ = algebraMap ℂ ↥L ((ζ : ℂˣ) : ℂ) * v₀ := by
    apply Subtype.ext
    have h1 : ((ρL v₀ : ↥L) : ReparamField MeromorphicPlane)
        = ρ (ReparamField.jet 0 : ReparamField MeromorphicPlane) := rfl
    have h2 : ((algebraMap ℂ ↥L ((ζ : ℂˣ) : ℂ) * v₀ : ↥L) : ReparamField MeromorphicPlane)
        = algebraMap ℂ (ReparamField MeromorphicPlane) ((ζ : ℂˣ) : ℂ) * ReparamField.jet 0 := by
      rw [MulMemClass.coe_mul, hv₀coe]
      rfl
    rw [h1, h2, hρjet]
  have hρLeq : ρL = torusScaleEquiv hv hgenv (fun _ ↦ ζ) := by
    refine tailEquiv_ext (fun _ : Fin 1 ↦ v₀) hgenv hρLderiv
      (fun z ↦ torusScaleEquiv_deriv hv hgenv (fun _ ↦ ζ) z) ?_
    intro i
    rw [hρLpalette, torusScaleEquiv_apply hv hgenv (fun _ ↦ ζ) i]
  have hconstL : ∀ c : ℂ, (c′ : ℂ) = 0 := fun _ => rfl
  have hxL : x ∈ L := by rw [hLeq]; exact hxV
  have hxρL : torusScaleEquiv hv hgenv (fun _ ↦ ζ) ⟨x, hxL⟩ = ⟨x, hxL⟩ := by
    rw [← hρLeq]
    exact Subtype.ext hxρ
  have hmemL := mem_differentialAdjoin_pow_of_rootOfUnity_invariant (C := ℂ) (E := ↥L)
    (v := v₀) (ζ := ζ) hconstL hv hgenv hv0 hn hord hxρL
  have hdown := coe_mem_differentialAdjoin_of_subfield L hLclosed (v₀ ^ n) hmemL
  have hcoepow : (((v₀ ^ n : ↥L)) : ReparamField MeromorphicPlane)
      = (ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n := by
    rw [SubmonoidClass.coe_pow]
  rwa [hcoepow] at hdown

/-- **The deck fixed field of a compact parabolic signature.**  On the generic reparametrisation,
the elements fixed by every deck translation of every depth of a degree-expanding elliptic protocol
and by the rotation of exact order `n` are exactly the differential rational functions of the
`n`-th power of the Maurer–Cartan velocity. -/
theorem setOf_deck_rotation_invariant_eq_differentialAdjoin_jetPow
    (Λ : PeriodPair) (M : ℕ → ℂ) (hM : ∀ k, M k ≠ 0)
    (hMinf : Tendsto (fun k => ‖M k‖) atTop atTop)
    {ζ : ℂˣ} {n : ℕ} (hn : 0 < n) (hord : orderOf ζ = n) :
    {x : ReparamField MeromorphicPlane |
        (∀ k : ℕ, ∀ t : ℂ, M k * t ∈ Λ.lattice →
          ReparamField.fieldEquiv (planeTranslateEquiv t) x = x)
        ∧ rotationEquiv (Units.ne_zero ζ) x = x}
      = (differentialAdjoin ℂ ({(ReparamField.jet 0 : ReparamField MeromorphicPlane) ^ n} : Set _)
          : Set _) := by
  have hpow : ((ζ : ℂˣ) : ℂ) ^ n = 1 := by
    have h1 := pow_orderOf_eq_one ζ
    rw [hord] at h1
    calc ((ζ : ℂˣ) : ℂ) ^ n = ((ζ ^ n : ℂˣ) : ℂ) := (Units.val_pow_eq_pow_val ζ n).symm
      _ = ((1 : ℂˣ) : ℂ) := by rw [h1]
      _ = 1 := Units.val_one
  ext x
  constructor
  · rintro ⟨hxt, hxρ⟩
    have hxV : x ∈ velocityField := by
      rw [← deckInvariantField_eq_velocityField Λ M hM hMinf]
      exact hxt
    exact mem_differentialAdjoin_jetPow_of_rotation_invariant hn hord hxV hxρ
  · intro hx
    have hxV : x ∈ velocityField := differentialAdjoin_jetPow_le_velocityField n hx
    refine ⟨?_, rotation_fixes_jetPow (Units.ne_zero ζ) hpow hx⟩
    have hmem : x ∈ deckInvariantField Λ M := by
      rw [deckInvariantField_eq_velocityField Λ M hM hMinf]
      exact hxV
    exact hmem

end GaloisForLFunctions.HTGeometry
