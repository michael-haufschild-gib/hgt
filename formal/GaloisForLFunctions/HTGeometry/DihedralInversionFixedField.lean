import GaloisForLFunctions.HTGeometry.TranslationRotationDeckFixedField
import GaloisForLFunctions.HTGeometry.DifferentialIndependentTopEquiv
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction

/-!
# The deck fixed field of the dihedral parabolic signature: scalings and inversion

On a freely differentially generated field with one hypertranscendental generator `w`, the deck
group of the `(2,2,∞)` orbifold acts through the scalings `w ↦ a·w` and the inversion `w ↦ w⁻¹`.
The invariants of the scalings are the field of the Maurer–Cartan current `ℓ = w′/w`; the
inversion negates the current, so on the current field it acts as the scaling of the free
generator `ℓ` by `-1`, whose invariants are the differential rational functions of `ℓ²`.  The
common fixed field is therefore exactly `F⟨ℓ²⟩` — the transported Chebyshev quadratic current.

* `inversionAutomorphism`, `inversionAutomorphism_generator`, `inversionAutomorphism_logDeriv`;
* `mem_differentialAdjoin_sqCurrent_of_scaling_inversion_invariant`;
* `setOf_scaling_inversion_invariant_eq_differentialAdjoin_sqCurrent`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

open scoped Differential

noncomputable section

variable {F E : Type u} [Field F] [Field E] [Differential F] [Differential E] [Algebra F E]
  [DifferentialAlgebra F E] [CharZero F] [CharZero E]

/-! ### The inversion automorphism -/

omit [CharZero F] in
/-- The inverse of a differentially independent generator is differentially independent. -/
theorem differentialIndependent_inv
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w)) :
    DifferentialIndependent F (fun _ : Unit ↦ w⁻¹) := by
  rw [← hypertranscendentalOver_iff_differentialIndependent_singleton]
  intro hDA
  have hDAw : DifferentialAlgebraicOver F w := by
    have h := differentialAlgebraicOver_inv hDA
    rwa [inv_inv] at h
  exact (hypertranscendentalOver_iff_differentialIndependent_singleton F w).mpr hw hDAw

omit [CharZero F] [CharZero E] in
/-- The inverse of a generator generates the same differential field. -/
theorem differentialAdjoin_inv_eq_top
    {w : E} (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) :
    differentialAdjoin F ({w⁻¹} : Set E) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← hwtop]
  refine differentialAdjoin_le F ?_ (derivationClosed_differentialAdjoin F _)
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  have hmem : w⁻¹ ∈ differentialAdjoin F ({w⁻¹} : Set E) :=
    subset_differentialAdjoin F _ rfl
  have hinv := (differentialAdjoin F ({w⁻¹} : Set E)).inv_mem hmem
  rwa [inv_inv] at hinv

omit [CharZero F] in
/-- **The inversion automorphism** `w ↦ w⁻¹` of a freely differentially generated field. -/
def inversionAutomorphism
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w))
    (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) : E ≃ₐ[F] E :=
  differentialIndependentTopAlgEquiv (fun _ : Unit ↦ w) (fun _ : Unit ↦ w⁻¹)
    hw (differentialIndependent_inv hw)
    (by rwa [Set.range_const]) (by rw [Set.range_const]; exact differentialAdjoin_inv_eq_top hwtop)

omit [CharZero F] in
theorem inversionAutomorphism_generator
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w))
    (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) :
    inversionAutomorphism hw hwtop w = w⁻¹ :=
  differentialIndependentTopAlgEquiv_apply (fun _ : Unit ↦ w) (fun _ : Unit ↦ w⁻¹)
    hw (differentialIndependent_inv hw) _ _ ()

omit [CharZero F] in
theorem inversionAutomorphism_deriv
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w))
    (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) (z : E) :
    inversionAutomorphism hw hwtop z′ = (inversionAutomorphism hw hwtop z)′ :=
  differentialIndependentTopAlgEquiv_deriv (fun _ : Unit ↦ w) (fun _ : Unit ↦ w⁻¹)
    hw (differentialIndependent_inv hw) _ _ z

omit [CharZero F] in
/-- **The inversion negates the Maurer–Cartan current.** -/
theorem inversionAutomorphism_logDeriv
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w))
    (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) (hw0 : w ≠ 0) :
    inversionAutomorphism hw hwtop (w′ / w) = -(w′ / w) := by
  set ι := inversionAutomorphism hw hwtop with hι
  have hgen : ι w = w⁻¹ := inversionAutomorphism_generator hw hwtop
  have hderiv : ι w′ = (w⁻¹)′ := by
    rw [inversionAutomorphism_deriv hw hwtop w, hgen]
  have hinvderiv : (w⁻¹)′ = -(w′ / w ^ 2) := by
    have h := Differential.deriv.leibniz_inv w
    simp only [smul_eq_mul] at h
    rw [h]
    field_simp
  rw [map_div₀, hgen, hderiv, hinvderiv]
  field_simp

/-! ### The dihedral fixed field -/

set_option maxHeartbeats 1000000 in
/-- **Invariance under every scaling and the inversion forces membership in the square-current
field.**  An element fixed by all scalings `w ↦ a·w` and by the inversion `w ↦ w⁻¹` is a
differential rational function of `(w′/w)²`. -/
theorem mem_differentialAdjoin_sqCurrent_of_scaling_inversion_invariant
    (hconst : ∀ c : F, c′ = 0) (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w))
    (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) (hw0 : w ≠ 0)
    {x : E}
    (hxs : ∀ (a : F) (ha : a ≠ 0), scalingAutomorphism hF ha hw hwtop x = x)
    (hxι : inversionAutomorphism hw hwtop x = x) :
    x ∈ differentialAdjoin F ({(w′ / w) ^ 2} : Set E) := by
  classical
  set ι := inversionAutomorphism hw hwtop with hιdef
  set ℓ : E := w′ / w with hℓdef
  have hιderiv : ∀ z : E, ι z′ = (ι z)′ := fun z ↦
    inversionAutomorphism_deriv hw hwtop z
  have hιℓ : ι ℓ = algebraMap F E (-1 : F) * ℓ := by
    rw [hℓdef, inversionAutomorphism_logDeriv hw hwtop hw0, map_neg, map_one]
    ring
  -- the current is hypertranscendental and nonzero
  have hwHT : HypertranscendentalOver F w :=
    (hypertranscendentalOver_iff_differentialIndependent_singleton F w).mpr hw
  have hℓHT : HypertranscendentalOver F ℓ := by
    have h := logDeriv_hypertranscendentalOver hwHT hw0
    rwa [Differential.logDeriv] at h
  have hℓ0 : ℓ ≠ 0 := by
    intro h0
    exact hℓHT (differentialAlgebraicOver_of_isAlgebraic (h0 ▸ isAlgebraic_zero))
  -- the subfield carrier
  set L : IntermediateField F E :=
    differentialAdjoin F (Set.range (fun _ : Fin 1 ↦ ℓ)) with hLdef
  have hLset : Set.range (fun _ : Fin 1 ↦ ℓ) = ({ℓ} : Set E) := Set.range_const
  have hLclosed : DerivationClosed L :=
    derivationClosed_differentialAdjoin F (Set.range (fun _ : Fin 1 ↦ ℓ))
  letI : Differential ↥L := derivationClosedDifferential L hLclosed
  letI : DifferentialAlgebra F ↥L := by
    refine ⟨fun a ↦ ?_⟩
    apply Subtype.ext
    show (((algebraMap F ↥L a)′ : ↥L) : E) = ((algebraMap F ↥L (a′) : ↥L) : E)
    have h1 : (((algebraMap F ↥L a)′ : ↥L) : E) = ((algebraMap F ↥L a : ↥L) : E)′ :=
      derivationClosedDifferential_apply L hLclosed _
    have h2 : ((algebraMap F ↥L a : ↥L) : E) = algebraMap F E a :=
      (IsScalarTower.algebraMap_apply F ↥L E a).symm
    have h3 : ((algebraMap F ↥L (a′) : ↥L) : E) = algebraMap F E (a′) :=
      (IsScalarTower.algebraMap_apply F ↥L E (a′)).symm
    rw [h1, h2, h3]
    exact DifferentialAlgebra.deriv_algebraMap a
  haveI : CharZero ↥L := by
    refine ⟨fun m k h ↦ ?_⟩
    have hcoe : ((m : ↥L) : E) = ((k : ↥L) : E) := congrArg Subtype.val h
    have hm : ((m : ↥L) : E) = (m : E) := by push_cast; rfl
    have hk : ((k : ↥L) : E) = (k : E) := by push_cast; rfl
    rw [hm, hk] at hcoe
    exact Nat.cast_injective hcoe
  -- the lifted palette
  set v₀ : ↥L := ⟨ℓ, by
    rw [hLdef, hLset]
    exact subset_differentialAdjoin F ({ℓ} : Set E) rfl⟩ with hv₀def
  have hv₀coe : ((v₀ : ↥L) : E) = ℓ := rfl
  have hindE : DifferentialIndependent F (fun _ : Fin 1 ↦ ℓ) := by
    have hU : DifferentialIndependent F (fun _ : Unit ↦ ℓ) :=
      (hypertranscendentalOver_iff_differentialIndependent_singleton F ℓ).mp hℓHT
    have hU' : AlgebraicIndependent F
        (fun p : Unit × ℕ ↦ differentialJet p.2 ℓ) := hU
    have hcomp := hU'.comp (fun p : Fin 1 × ℕ ↦ (((), p.2) : Unit × ℕ)) (by
      rintro ⟨i, m⟩ ⟨j, m'⟩ hp
      have hm : m = m' := congrArg Prod.snd hp
      have hij : i = j := Subsingleton.elim i j
      rw [hm, hij])
    exact hcomp
  have hv : DifferentialIndependent F (fun _ : Fin 1 ↦ v₀) := by
    refine differentialIndependent_subfield L hLclosed (fun _ : Fin 1 ↦ v₀) ?_
    exact hindE
  have hgenv : differentialAdjoin F (Set.range (fun _ : Fin 1 ↦ v₀)) = ⊤ := by
    have h := differentialAdjoin_adjoinLift_eq_top (F := F) (fun _ : Fin 1 ↦ ℓ)
    have hr : Set.range (adjoinLift F (fun _ : Fin 1 ↦ ℓ))
        = Set.range (fun _ : Fin 1 ↦ v₀) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨0, Subtype.ext rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨0, Subtype.ext rfl⟩
    rw [hr] at h
    exact h
  -- the inversion preserves the current field
  have hmapadj : ∀ (σ : E ≃ₐ[F] E), (∀ z : E, σ z′ = (σ z)′) →
      ∀ y ∈ L, σ y ∈ differentialAdjoin F ({σ ℓ} : Set E) := by
    intro σ hσd y hy
    have hmap := map_differentialAdjoin (σ : E →ₐ[F] E) (fun z ↦ hσd z)
      (Set.range (fun _ : Fin 1 ↦ ℓ))
    have hymem : σ y ∈ IntermediateField.map (σ : E →ₐ[F] E) L := ⟨y, hy, rfl⟩
    rw [hLdef] at hymem
    rw [hmap] at hymem
    have himg : (σ : E →ₐ[F] E) '' Set.range (fun _ : Fin 1 ↦ ℓ) = ({σ ℓ} : Set E) := by
      rw [hLset]
      simp
    rwa [himg] at hymem
  have hneg0 : (-1 : F) ≠ 0 := by norm_num
  have hιmem : ∀ y ∈ L, ι y ∈ L := by
    intro y hy
    have h1 := hmapadj ι hιderiv y hy
    rw [hιℓ] at h1
    have h2 : differentialAdjoin F ({algebraMap F E (-1 : F) * ℓ} : Set E)
        = differentialAdjoin F ({ℓ} : Set E) :=
      differentialAdjoin_const_mul hneg0 ℓ
    rw [h2] at h1
    rw [hLdef, hLset]
    exact h1
  have hιsymm : ∀ z : E, ι.symm z′ = (ι.symm z)′ := by
    intro z
    have h1 : ι ((ι.symm z)′) = z′ := by
      have h0 := hιderiv (ι.symm z)
      rw [ι.apply_symm_apply] at h0
      exact h0
    calc ι.symm z′ = ι.symm (ι ((ι.symm z)′)) := by rw [h1]
      _ = (ι.symm z)′ := ι.symm_apply_apply _
  have hιsymℓ : ι.symm ℓ = algebraMap F E (-1 : F) * ℓ := by
    apply ι.injective
    rw [ι.apply_symm_apply, map_mul, AlgEquiv.commutes, hιℓ, ← mul_assoc, ← map_mul]
    norm_num
  have hιsymmem : ∀ y ∈ L, ι.symm y ∈ L := by
    intro y hy
    have h1 := hmapadj ι.symm hιsymm y hy
    rw [hιsymℓ] at h1
    have h2 : differentialAdjoin F ({algebraMap F E (-1 : F) * ℓ} : Set E)
        = differentialAdjoin F ({ℓ} : Set E) :=
      differentialAdjoin_const_mul hneg0 ℓ
    rw [h2] at h1
    rw [hLdef, hLset]
    exact h1
  -- the inversion restricted to the current field
  set ιL : ↥L ≃ₐ[F] ↥L :=
    { toFun := fun y ↦ ⟨ι y, hιmem y y.2⟩
      invFun := fun y ↦ ⟨ι.symm y, hιsymmem y y.2⟩
      left_inv := fun y ↦ Subtype.ext (ι.symm_apply_apply y)
      right_inv := fun y ↦ Subtype.ext (ι.apply_symm_apply y)
      map_mul' := fun a b ↦ Subtype.ext (map_mul ι (a : E) (b : E))
      map_add' := fun a b ↦ Subtype.ext (map_add ι (a : E) (b : E))
      commutes' := fun a ↦ Subtype.ext (ι.commutes a) } with hιLdef
  have hιLderiv : ∀ z : ↥L, ιL z′ = (ιL z)′ := by
    intro z
    apply Subtype.ext
    have h1 : ((ιL z′ : ↥L) : E) = ι ((z′ : ↥L) : E) := rfl
    have h2 : ((z′ : ↥L) : E) = ((z : ↥L) : E)′ :=
      derivationClosedDifferential_apply L hLclosed z
    have h3 : (((ιL z)′ : ↥L) : E) = ((ιL z : ↥L) : E)′ :=
      derivationClosedDifferential_apply L hLclosed (ιL z)
    rw [h1, h2, h3]
    exact hιderiv _
  set ζ : Fˣ := -1 with hζdef
  have hζcoe : ((ζ : Fˣ) : F) = (-1 : F) := rfl
  have hord : orderOf ζ = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · ext
      simp [hζdef]
    · intro h1
      rw [hζdef] at h1
      have hval : ((-1 : Fˣ) : F) = ((1 : Fˣ) : F) := by rw [h1]
      rw [Units.val_neg, Units.val_one] at hval
      have hne : (-1 : F) ≠ 1 := by
        intro hcon
        have h2 : (2 : F) = 0 := by linear_combination -hcon
        exact two_ne_zero h2
      exact hne hval
  have hιLpalette : ιL v₀ = algebraMap F ↥L ((ζ : Fˣ) : F) * v₀ := by
    apply Subtype.ext
    have h1 : ((ιL v₀ : ↥L) : E) = ι ℓ := rfl
    have h2 : ((algebraMap F ↥L ((ζ : Fˣ) : F) * v₀ : ↥L) : E)
        = algebraMap F E ((ζ : Fˣ) : F) * ℓ := by
      rw [MulMemClass.coe_mul, hv₀coe]
      rfl
    rw [h1, h2, hιℓ, hζcoe]
  have hιLeq : ιL = torusScaleEquiv hv hgenv (fun _ ↦ ζ) := by
    refine tailEquiv_ext (fun _ : Fin 1 ↦ v₀) hgenv hιLderiv
      (fun z ↦ torusScaleEquiv_deriv hv hgenv (fun _ ↦ ζ) z) ?_
    intro i
    rw [hιLpalette, torusScaleEquiv_apply hv hgenv (fun _ ↦ ζ) i]
  -- membership of the invariant in the current field
  have hxL : x ∈ L := by
    rw [hLdef, hLset]
    have hset := fixedField_scaling_eq_logDerivField hF hw hwtop hw0
    have hxmem : x ∈ {y : E | ∀ (a : F) (ha : a ≠ 0), scalingAutomorphism hF ha hw hwtop y = y} :=
      hxs
    rw [hset] at hxmem
    exact hxmem
  -- the restricted invariance
  have hxιL : torusScaleEquiv hv hgenv (fun _ ↦ ζ) ⟨x, hxL⟩ = ⟨x, hxL⟩ := by
    rw [← hιLeq]
    exact Subtype.ext hxι
  have hv0 : v₀ ≠ 0 := by
    intro h0
    exact hℓ0 (by
      have hc := congrArg Subtype.val h0
      simpa [hv₀coe] using hc)
  have hconstL : ∀ c : F, (c′ : F) = 0 := hconst
  have hmemL := mem_differentialAdjoin_pow_of_rootOfUnity_invariant (C := F) (E := ↥L)
    (v := v₀) (ζ := ζ) hconstL hv hgenv hv0 (by norm_num) hord hxιL
  -- descend to the ambient field
  have hdown := coe_mem_differentialAdjoin_of_subfield L hLclosed (v₀ ^ 2) hmemL
  have hcoepow : (((v₀ ^ 2 : ↥L)) : E) = ℓ ^ 2 := by
    rw [SubmonoidClass.coe_pow]
  rwa [hcoepow] at hdown

/-- **The dihedral deck fixed field.**  The elements fixed by every scaling and by the inversion
are exactly the differential rational functions of the square of the Maurer–Cartan current. -/
theorem setOf_scaling_inversion_invariant_eq_differentialAdjoin_sqCurrent
    (hconst : ∀ c : F, c′ = 0) (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w))
    (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) (hw0 : w ≠ 0) :
    {x : E | (∀ (a : F) (ha : a ≠ 0), scalingAutomorphism hF ha hw hwtop x = x) ∧
        inversionAutomorphism hw hwtop x = x}
      = (differentialAdjoin F ({(w′ / w) ^ 2} : Set E) : Set E) := by
  ext x
  constructor
  · rintro ⟨hxs, hxι⟩
    exact mem_differentialAdjoin_sqCurrent_of_scaling_inversion_invariant hconst hF hw hwtop hw0
      hxs hxι
  · intro hx
    constructor
    · intro a ha
      have hfix : scalingAutomorphism hF ha hw hwtop ((w′ / w) ^ 2) = (w′ / w) ^ 2 := by
        rw [map_pow, scalingAutomorphism_logDeriv hF ha hw hwtop]
      exact scalingAutomorphism_fixes_differentialAdjoin hF ha hw hwtop hfix hx
    · have hfix : inversionAutomorphism hw hwtop ((w′ / w) ^ 2) = (w′ / w) ^ 2 := by
        rw [map_pow, inversionAutomorphism_logDeriv hw hwtop hw0]
        ring
      exact DifferentialAlgEquiv.fixed_on_differentialAdjoin
        (⟨inversionAutomorphism hw hwtop,
          fun z ↦ inversionAutomorphism_deriv hw hwtop z⟩ : DifferentialAlgEquiv F E)
        (fun _ : Unit ↦ (w′ / w) ^ 2) (fun _ ↦ hfix) (by
          rwa [show Set.range (fun _ : Unit ↦ (w′ / w) ^ 2) = ({(w′ / w) ^ 2} : Set E) from
            Set.range_const] )

/-- **The complete tail of any dihedral deck tower.**  For a family of deck transformations that
contains every scaling and the inversion and whose members all fix the square-current field
pointwise, the common invariants are exactly the differential rational functions of `(w′/w)²`. -/
theorem setOf_forall_fixed_eq_differentialAdjoin_sqCurrent
    (hconst : ∀ c : F, c′ = 0) (hF : ∀ a : F, (algebraMap F E a)′ = 0)
    {w : E} (hw : DifferentialIndependent F (fun _ : Unit ↦ w))
    (hwtop : differentialAdjoin F ({w} : Set E) = ⊤) (hw0 : w ≠ 0)
    {ι : Type v} (σs : ι → (E ≃ₐ[F] E)) (iscale : ∀ (a : F), a ≠ 0 → ι) (iinv : ι)
    (hscale : ∀ (a : F) (ha : a ≠ 0), σs (iscale a ha) = scalingAutomorphism hF ha hw hwtop)
    (hinv : σs iinv = inversionAutomorphism hw hwtop)
    (hfix : ∀ i : ι, ∀ z ∈ differentialAdjoin F ({(w′ / w) ^ 2} : Set E), σs i z = z) :
    {x : E | ∀ i : ι, σs i x = x}
      = (differentialAdjoin F ({(w′ / w) ^ 2} : Set E) : Set E) := by
  ext x
  constructor
  · intro hx
    refine mem_differentialAdjoin_sqCurrent_of_scaling_inversion_invariant hconst hF hw hwtop hw0
      (fun a ha ↦ ?_) ?_
    · rw [← hscale a ha]
      exact hx (iscale a ha)
    · rw [← hinv]
      exact hx iinv
  · intro hx i
    exact hfix i x hx

end

end GaloisForLFunctions.HTGeometry
