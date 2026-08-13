import GaloisForLFunctions.HTGeometry.RootOfUnityScalingFixedField
import GaloisForLFunctions.HTGeometry.ScalarAdditiveDifferentialTorsor
import GaloisForLFunctions.HTGeometry.FreeDifferentialScalingAutomorphism
import GaloisForLFunctions.HTGeometry.DifferentialSubfieldTransfer
import GaloisForLFunctions.HTGeometry.FreeDifferentialLinearAction
import GaloisForLFunctions.HTGeometry.NonautonomousProjectiveTimeLaw
import GaloisForLFunctions.HTGeometry.LogarithmicDerivativeFixedField

/-!
# The deck fixed field of a compact parabolic signature: translation and rotation

On a freely differentially generated field with one hypertranscendental generator `q`, the deck
group of a compact parabolic orbifold acts through the unit translation `q ↦ q + 1` and the
rotation `q ↦ ζ·q` by a root of unity of exact order `n`.  The invariants of the translation are
the derivative field `F⟨q′⟩`, on which the rotation acts as the scaling of the free generator
`q′`; the invariants of that scaling are the differential rational functions of `(q′)^n`.  The
common fixed field is therefore exactly `F⟨(q′)^n⟩` — the transported Maurer–Cartan current of
the signature, the `n`-th power of the cover velocity.

* `mem_derivativeField_of_translation_invariant`;
* `mem_differentialAdjoin_derivPow_of_translation_rotation_invariant`;
* `setOf_translation_rotation_invariant_eq_differentialAdjoin_derivPow`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped Differential

noncomputable section

variable {F T : Type u} [Field F] [Field T] [Differential F] [Differential T] [Algebra F T]
  [DifferentialAlgebra F T] [CharZero F] [CharZero T]

/-! ### Fixed points of powers of an automorphism -/

omit [Differential F] [Differential T] [DifferentialAlgebra F T] [CharZero F] [CharZero T] in
/-- A fixed point of an automorphism is fixed by all its integer powers. -/
theorem algEquiv_zpow_apply_eq_of_apply_eq {L : Type*} [Field L] [Algebra L T]
    {σ : T ≃ₐ[L] T} {x : T} (hx : σ x = x) (k : ℤ) : (σ ^ k) x = x := by
  have hpow : ∀ m : ℕ, (σ ^ m) x = x := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  cases k with
  | ofNat m => simpa using hpow m
  | negSucc m =>
      have hsymm : σ.symm x = x := by
        conv_lhs => rw [← hx]
        exact σ.symm_apply_apply x
      have hpowsymm : ∀ j : ℕ, (σ.symm ^ j) x = x := by
        intro j
        induction j with
        | zero => rfl
        | succ j ih =>
            rw [pow_succ, AlgEquiv.mul_apply, hsymm, ih]
      rw [zpow_negSucc, ← inv_pow]
      exact hpowsymm (m + 1)

/-! ### The translation layer -/

omit [CharZero F] in
/-- **A translation-invariant element lies in the derivative field.** -/
theorem mem_derivativeField_of_translation_invariant
    (hconst : ∀ c : F, c′ = 0)
    {q : T} (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    {x : T} (hx : scalarDifferentialTranslationEquiv q hq hgen 1 x = x) :
    x ∈ scalarDerivativeField F q := by
  have hx' : scalarDifferentialTranslationEquivDerivative q hq hgen hconst 1 x = x := hx
  have hfixmem : x ∈ IntermediateField.fixedField
      (Subgroup.zpowers (scalarDifferentialTranslationEquivDerivative q hq hgen hconst 1)) := by
    rw [IntermediateField.mem_fixedField_iff]
    rintro σ hσ
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσ
    exact algEquiv_zpow_apply_eq_of_apply_eq hx' k
  rw [fixedField_zpowers_scalarDifferentialTranslation_one q hq hgen hconst] at hfixmem
  rw [IntermediateField.mem_bot] at hfixmem
  obtain ⟨l, rfl⟩ := hfixmem
  exact l.2

/-! ### Transfer of adjoin membership from a derivation-closed subfield -/

omit [Differential F] [DifferentialAlgebra F T] [CharZero F] [CharZero T] in
/-- Membership in a differential adjunction computed inside a derivation-closed subfield descends
to the ambient field. -/
theorem coe_mem_differentialAdjoin_of_subfield
    (L : IntermediateField F T) (hL : DerivationClosed L) (w : L) {z : L}
    (hz : letI := derivationClosedDifferential L hL
      z ∈ differentialAdjoin F ({w} : Set L)) :
    (z : T) ∈ differentialAdjoin F ({(w : T)} : Set T) := by
  letI := derivationClosedDifferential L hL
  set N : IntermediateField F T := differentialAdjoin F ({(w : T)} : Set T) with hN
  have hjet : ∀ y ∈ differentialJetSet ({w} : Set L), ((y : T)) ∈ N := by
    rintro y ⟨u, hu, m, rfl⟩
    rw [Set.mem_singleton_iff] at hu
    rw [hu, differentialJet_coe L hL w m]
    exact IntermediateField.subset_adjoin F (differentialJetSet ({(w : T)} : Set T))
      ⟨(w : T), rfl, m, rfl⟩
  refine IntermediateField.adjoin_induction F (s := differentialJetSet ({w} : Set L))
    (p := fun y _ ↦ ((y : T)) ∈ N) ?_ ?_ ?_ ?_ ?_ hz
  · intro y hy
    exact hjet y hy
  · intro a
    have hcoe : ((algebraMap F L a : L) : T) = algebraMap F T a :=
      (IsScalarTower.algebraMap_apply F L T a).symm
    rw [hcoe]
    exact N.algebraMap_mem a
  · intro a b _ _ ha hb
    rw [AddMemClass.coe_add]
    exact N.add_mem ha hb
  · intro a _ ha
    rw [IntermediateField.coe_inv]
    exact N.inv_mem ha
  · intro a b _ _ ha hb
    rw [MulMemClass.coe_mul]
    exact N.mul_mem ha hb

/-! ### The composite deck fixed field -/

set_option maxHeartbeats 1000000 in
/-- **Invariance under the translation and the rotation forces membership in the current field.**
An element fixed by the unit translation `q ↦ q + 1` and by the scaling `q ↦ ζ·q` of a root of
unity of exact order `n` is a differential rational function of `(q′)^n`. -/
theorem mem_differentialAdjoin_derivPow_of_translation_rotation_invariant
    (hconst : ∀ c : F, c′ = 0) (hF : ∀ a : F, (algebraMap F T a)′ = 0)
    {q : T} (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    {ζ : Fˣ} {n : ℕ} (hn : 0 < n) (hord : orderOf ζ = n)
    {x : T} (hxt : scalarDifferentialTranslationEquiv q hq hgen 1 x = x)
    (hxρ : scalingAutomorphism hF (Units.ne_zero ζ)
      ((hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq) hgen x = x) :
    x ∈ differentialAdjoin F ({q′ ^ n} : Set T) := by
  classical
  set hyq := (hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq with hyqdef
  set ρ := scalingAutomorphism hF (Units.ne_zero ζ) hyq hgen with hρdef
  -- the derivative is hypertranscendental and nonzero
  have hq' : HypertranscendentalOver F q′ := hypertranscendentalOver_deriv hq
  have hq'0 : q′ ≠ 0 := by
    intro h0
    exact hq' (differentialAlgebraicOver_of_isAlgebraic (h0 ▸ isAlgebraic_zero))
  -- the rotation scales the derivative
  have hρq : ρ q = algebraMap F T (ζ : F) * q :=
    scalingAutomorphism_generator hF (Units.ne_zero ζ) hyq hgen
  have hρderiv : ∀ z : T, ρ z′ = (ρ z)′ := fun z ↦
    scalingAutomorphism_deriv hF (Units.ne_zero ζ) hyq hgen z
  have hρq' : ρ q′ = algebraMap F T (ζ : F) * q′ := by
    rw [hρderiv q, hρq]
    have hleib := Differential.deriv.leibniz (algebraMap F T (ζ : F)) q
    simp only [smul_eq_mul] at hleib
    rw [hleib, hF (ζ : F), mul_zero, add_zero]
  -- the subfield carrier
  set L : IntermediateField F T :=
    differentialAdjoin F (Set.range (fun _ : Fin 1 ↦ q′)) with hLdef
  have hLset : Set.range (fun _ : Fin 1 ↦ q′) = ({q′} : Set T) := Set.range_const
  have hLeq : L = scalarDerivativeField F q := by
    rw [hLdef, hLset]
    rfl
  have hLclosed : DerivationClosed L :=
    derivationClosed_differentialAdjoin F (Set.range (fun _ : Fin 1 ↦ q′))
  letI : Differential ↥L := derivationClosedDifferential L hLclosed
  letI : DifferentialAlgebra F ↥L := by
    refine ⟨fun a ↦ ?_⟩
    apply Subtype.ext
    show (((algebraMap F ↥L a)′ : ↥L) : T) = ((algebraMap F ↥L (a′) : ↥L) : T)
    have h1 : (((algebraMap F ↥L a)′ : ↥L) : T) = ((algebraMap F ↥L a : ↥L) : T)′ :=
      derivationClosedDifferential_apply L hLclosed _
    have h2 : ((algebraMap F ↥L a : ↥L) : T) = algebraMap F T a :=
      (IsScalarTower.algebraMap_apply F ↥L T a).symm
    have h3 : ((algebraMap F ↥L (a′) : ↥L) : T) = algebraMap F T (a′) :=
      (IsScalarTower.algebraMap_apply F ↥L T (a′)).symm
    rw [h1, h2, h3]
    exact DifferentialAlgebra.deriv_algebraMap a
  haveI : CharZero ↥L := by
    refine ⟨fun m k h ↦ ?_⟩
    have hcoe : ((m : ↥L) : T) = ((k : ↥L) : T) := congrArg Subtype.val h
    have hm : ((m : ↥L) : T) = (m : T) := by push_cast; rfl
    have hk : ((k : ↥L) : T) = (k : T) := by push_cast; rfl
    rw [hm, hk] at hcoe
    exact Nat.cast_injective hcoe
  -- the lifted palette
  set v₀ : ↥L := ⟨q′, by
    rw [hLdef, hLset]
    exact subset_differentialAdjoin F ({q′} : Set T) rfl⟩ with hv₀def
  have hv₀coe : ((v₀ : ↥L) : T) = q′ := rfl
  have hindT : DifferentialIndependent F (fun _ : Fin 1 ↦ q′) := by
    have hU : DifferentialIndependent F (fun _ : Unit ↦ q′) :=
      (hypertranscendentalOver_iff_differentialIndependent_singleton F q′).mp hq'
    have hU' : AlgebraicIndependent F
        (fun p : Unit × ℕ ↦ differentialJet p.2 q′) := hU
    have hcomp := hU'.comp (fun p : Fin 1 × ℕ ↦ (((), p.2) : Unit × ℕ)) (by
      rintro ⟨i, m⟩ ⟨j, m'⟩ hp
      have hm : m = m' := congrArg Prod.snd hp
      have hij : i = j := Subsingleton.elim i j
      rw [hm, hij])
    exact hcomp
  have hv : DifferentialIndependent F (fun _ : Fin 1 ↦ v₀) := by
    refine differentialIndependent_subfield L hLclosed (fun _ : Fin 1 ↦ v₀) ?_
    exact hindT
  have hgenv : differentialAdjoin F (Set.range (fun _ : Fin 1 ↦ v₀)) = ⊤ := by
    have h := differentialAdjoin_adjoinLift_eq_top (F := F) (fun _ : Fin 1 ↦ q′)
    have hr : Set.range (adjoinLift F (fun _ : Fin 1 ↦ q′))
        = Set.range (fun _ : Fin 1 ↦ v₀) := by
      ext w
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨0, Subtype.ext rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨0, Subtype.ext rfl⟩
    rw [hr] at h
    exact h
  -- the rotation preserves the subfield
  have hmapadj : ∀ (σ : T ≃ₐ[F] T), (∀ z : T, σ z′ = (σ z)′) →
      ∀ w ∈ L, σ w ∈ differentialAdjoin F ({σ q′} : Set T) := by
    intro σ hσd w hw
    have hmap := map_differentialAdjoin (σ : T →ₐ[F] T) (fun z ↦ hσd z)
      (Set.range (fun _ : Fin 1 ↦ q′))
    have hwmem : σ w ∈ IntermediateField.map (σ : T →ₐ[F] T) L := ⟨w, hw, rfl⟩
    rw [hLdef] at hwmem
    rw [hmap] at hwmem
    have himg : (σ : T →ₐ[F] T) '' Set.range (fun _ : Fin 1 ↦ q′) = ({σ q′} : Set T) := by
      rw [hLset]
      simp
    rwa [himg] at hwmem
  have hρmem : ∀ w ∈ L, ρ w ∈ L := by
    intro w hw
    have h1 := hmapadj ρ hρderiv w hw
    rw [hρq'] at h1
    have h2 : differentialAdjoin F ({algebraMap F T (ζ : F) * q′} : Set T)
        = differentialAdjoin F ({q′} : Set T) :=
      differentialAdjoin_const_mul (Units.ne_zero ζ) q′
    rw [h2] at h1
    rw [hLdef, hLset]
    exact h1
  have hρsymmderiv : ∀ z : T, ρ.symm z′ = (ρ.symm z)′ := by
    intro z
    have h1 : ρ ((ρ.symm z)′) = z′ := by
      have h0 := hρderiv (ρ.symm z)
      rw [ρ.apply_symm_apply] at h0
      exact h0
    calc ρ.symm z′ = ρ.symm (ρ ((ρ.symm z)′)) := by rw [h1]
      _ = (ρ.symm z)′ := ρ.symm_apply_apply _
  have hζζ : ((ζ⁻¹ : Fˣ) : F) * ((ζ : Fˣ) : F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel ζ, Units.val_one]
  have hρsymq' : ρ.symm q′ = algebraMap F T ((ζ⁻¹ : Fˣ) : F) * q′ := by
    apply ρ.injective
    rw [ρ.apply_symm_apply, map_mul, AlgEquiv.commutes, hρq', ← mul_assoc, ← map_mul, hζζ,
      map_one, one_mul]
  have hρsymmem : ∀ w ∈ L, ρ.symm w ∈ L := by
    intro w hw
    have h1 := hmapadj ρ.symm hρsymmderiv w hw
    rw [hρsymq'] at h1
    have h2 : differentialAdjoin F ({algebraMap F T ((ζ⁻¹ : Fˣ) : F) * q′} : Set T)
        = differentialAdjoin F ({q′} : Set T) :=
      differentialAdjoin_const_mul (Units.ne_zero ζ⁻¹) q′
    rw [h2] at h1
    rw [hLdef, hLset]
    exact h1
  -- the rotation restricted to the subfield
  set ρL : ↥L ≃ₐ[F] ↥L :=
    { toFun := fun w ↦ ⟨ρ w, hρmem w w.2⟩
      invFun := fun w ↦ ⟨ρ.symm w, hρsymmem w w.2⟩
      left_inv := fun w ↦ Subtype.ext (ρ.symm_apply_apply w)
      right_inv := fun w ↦ Subtype.ext (ρ.apply_symm_apply w)
      map_mul' := fun a b ↦ Subtype.ext (map_mul ρ (a : T) (b : T))
      map_add' := fun a b ↦ Subtype.ext (map_add ρ (a : T) (b : T))
      commutes' := fun a ↦ Subtype.ext (ρ.commutes a) } with hρLdef
  have hρLderiv : ∀ z : ↥L, ρL z′ = (ρL z)′ := by
    intro z
    apply Subtype.ext
    have h1 : ((ρL z′ : ↥L) : T) = ρ ((z′ : ↥L) : T) := rfl
    have h2 : ((z′ : ↥L) : T) = ((z : ↥L) : T)′ :=
      derivationClosedDifferential_apply L hLclosed z
    have h3 : (((ρL z)′ : ↥L) : T) = ((ρL z : ↥L) : T)′ :=
      derivationClosedDifferential_apply L hLclosed (ρL z)
    rw [h1, h2, h3]
    exact hρderiv _
  have hρLpalette : ρL v₀ = algebraMap F ↥L ((ζ : Fˣ) : F) * v₀ := by
    apply Subtype.ext
    have h1 : ((ρL v₀ : ↥L) : T) = ρ q′ := rfl
    have h2 : ((algebraMap F ↥L ((ζ : Fˣ) : F) * v₀ : ↥L) : T)
        = algebraMap F T ((ζ : Fˣ) : F) * q′ := by
      rw [MulMemClass.coe_mul, hv₀coe]
      rfl
    rw [h1, h2, hρq']
  have hρLeq : ρL = torusScaleEquiv hv hgenv (fun _ ↦ ζ) := by
    refine tailEquiv_ext (fun _ : Fin 1 ↦ v₀) hgenv hρLderiv
      (fun z ↦ torusScaleEquiv_deriv hv hgenv (fun _ ↦ ζ) z) ?_
    intro i
    rw [hρLpalette, torusScaleEquiv_apply hv hgenv (fun _ ↦ ζ) i]
  -- the constants of the base stay constants
  have hconstL : ∀ c : F, (c′ : F) = 0 := hconst
  -- membership of the invariant in the subfield
  have hxL : x ∈ L := by
    rw [hLeq]
    exact mem_derivativeField_of_translation_invariant hconst hq hgen hxt
  -- the restricted invariance
  have hxρL : torusScaleEquiv hv hgenv (fun _ ↦ ζ) ⟨x, hxL⟩ = ⟨x, hxL⟩ := by
    rw [← hρLeq]
    exact Subtype.ext hxρ
  -- the rotation layer
  have hv0 : v₀ ≠ 0 := by
    intro h0
    exact hq'0 (by
      have hc := congrArg Subtype.val h0
      simpa [hv₀coe] using hc)
  have hmemL := mem_differentialAdjoin_pow_of_rootOfUnity_invariant (C := F) (E := ↥L)
    (v := v₀) (ζ := ζ) hconstL hv hgenv hv0 hn hord hxρL
  -- descend to the ambient field
  have hdown := coe_mem_differentialAdjoin_of_subfield L hLclosed (v₀ ^ n) hmemL
  have hcoepow : (((v₀ ^ n : ↥L)) : T) = q′ ^ n := by
    rw [SubmonoidClass.coe_pow]
  rwa [hcoepow] at hdown

set_option maxHeartbeats 800000 in
/-- **The deck fixed field of a compact parabolic signature.**  The elements fixed by the unit
translation and by the rotation of exact order `n` are exactly the differential rational functions
of the `n`-th power of the cover velocity. -/
theorem setOf_translation_rotation_invariant_eq_differentialAdjoin_derivPow
    (hconst : ∀ c : F, c′ = 0) (hF : ∀ a : F, (algebraMap F T a)′ = 0)
    {q : T} (hq : HypertranscendentalOver F q)
    (hgen : differentialAdjoin F ({q} : Set T) = ⊤)
    {ζ : Fˣ} {n : ℕ} (hn : 0 < n) (hord : orderOf ζ = n) :
    {x : T | scalarDifferentialTranslationEquiv q hq hgen 1 x = x ∧
        scalingAutomorphism hF (Units.ne_zero ζ)
          ((hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq) hgen x = x}
      = (differentialAdjoin F ({q′ ^ n} : Set T) : Set T) := by
  ext x
  constructor
  · rintro ⟨hxt, hxρ⟩
    exact mem_differentialAdjoin_derivPow_of_translation_rotation_invariant hconst hF hq hgen
      hn hord hxt hxρ
  · intro hx
    have hsub : differentialAdjoin F ({q′ ^ n} : Set T) ≤ scalarDerivativeField F q := by
      refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact pow_mem (subset_differentialAdjoin F ({q′} : Set T) rfl) n
    constructor
    · exact scalarDifferentialTranslationEquiv_fixed_on_derivativeField q hq hgen hconst 1
        ⟨x, hsub hx⟩
    · set hyq := (hypertranscendentalOver_iff_differentialIndependent_singleton F q).mp hq
      set ρ := scalingAutomorphism hF (Units.ne_zero ζ) hyq hgen with hρdef
      have hρq : ρ q = algebraMap F T ((ζ : Fˣ) : F) * q :=
        scalingAutomorphism_generator hF (Units.ne_zero ζ) hyq hgen
      have hρq' : ρ q′ = algebraMap F T ((ζ : Fˣ) : F) * q′ := by
        rw [scalingAutomorphism_deriv hF (Units.ne_zero ζ) hyq hgen q, hρq]
        have hleib := Differential.deriv.leibniz (algebraMap F T ((ζ : Fˣ) : F)) q
        simp only [smul_eq_mul] at hleib
        rw [hleib, hF ((ζ : Fˣ) : F), mul_zero, add_zero]
      have hfix : ρ (q′ ^ n) = q′ ^ n := by
        rw [map_pow, hρq', mul_pow, ← map_pow]
        have hpow : ((ζ : Fˣ) : F) ^ n = 1 := by
          have h1 := pow_orderOf_eq_one ζ
          rw [hord] at h1
          calc ((ζ : Fˣ) : F) ^ n = ((ζ ^ n : Fˣ) : F) := (Units.val_pow_eq_pow_val ζ n).symm
            _ = ((1 : Fˣ) : F) := by rw [h1]
            _ = 1 := Units.val_one
        rw [hpow, map_one, one_mul]
      exact scalingAutomorphism_fixes_differentialAdjoin hF (Units.ne_zero ζ) hyq hgen hfix hx

end

end GaloisForLFunctions.HTGeometry
