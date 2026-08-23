import GaloisForLFunctions.RHTower.DeningerDynSysOmegaDomainRing
import GaloisForLFunctions.RHTower.DeningerDynSysValuedCharEquiv

/-!
# The `𝒪`-valued points of `W_rat (X)` as Witt-vector homomorphisms

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.1
(`t41`) and the identification (145).

Proposition 13.1 describes an `𝒪`-valued point of `W_rat (X)` by a pair of points `y ∈ closure {x}`
together with the commuting diagram of ring homomorphisms

`W_rat (κ (y)) → k`, `W_rat (𝒪_{X,y}) → 𝒪`, `W_rat (𝒪_{X,x}) → C`, `W_rat (κ (x)) → C` .

Over a scheme whose residue fields are algebraically closed and whose local rings are integrally
closed domains with algebraically closed fraction field — Deninger's `X`, the integral closure of an
integral normal scheme in an algebraic closure of its function field — the Teichmüller comparison
`ω` turns every one of these ring homomorphisms into a pointed multiplicative map, and the diagram
becomes exactly Deninger's Definition 13.2.  This is his identification (145).
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry

noncomputable section

universe u

/-! ### Fields -/

theorem deningerIsAlgClosed_fractionRing (K : Type*) [Field K] [IsAlgClosed K] :
    IsAlgClosed (FractionRing K) :=
  IsAlgClosed.of_ringEquiv K (FractionRing K)
    (FractionRing.algEquiv K K).symm.toRingEquiv

open Classical in
/-- Pointed multiplicative maps of a field are the characters of its group of units. -/
def deningerFieldPointedEquivChar (k C : Type*) [Field k] [Field C] :
    (k →*₀ C) ≃ (kˣ →* Cˣ) where
  toFun P :=
    { toFun := fun u => Units.mk0 (P (u : k)) (by
        intro hc
        have h1 : P ((u : k) * ((u⁻¹ : kˣ) : k)) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
        rw [map_mul, hc, zero_mul] at h1
        exact zero_ne_one h1)
      map_one' := by
        refine Units.ext ?_
        show P ((1 : kˣ) : k) = 1
        rw [Units.val_one, map_one]
      map_mul' := by
        intro a b
        refine Units.ext ?_
        show P ((a * b : kˣ) : k) = P (a : k) * P (b : k)
        rw [Units.val_mul, map_mul] }
  invFun χ := deningerCharExtendByZero χ
  left_inv P := by
    refine MonoidWithZeroHom.ext fun a => ?_
    by_cases ha : a = 0
    · subst ha
      rw [map_zero, map_zero]
    · rw [deningerCharExtendByZero_apply_ne_zero _ ha]
      rfl
  right_inv χ := by
    refine MonoidHom.ext fun u => Units.ext ?_
    have hu : (u : k) ≠ 0 := u.ne_zero
    show deningerCharExtendByZero χ (u : k) = ((χ u : Cˣ) : C)
    rw [deningerCharExtendByZero_apply_ne_zero _ hu,
      show Units.mk0 (u : k) hu = u from Units.ext rfl]

/-- Ring homomorphisms out of `W_rat (κ)` for an algebraically closed field are the pointed
multiplicative maps of `κ`. -/
def deningerWittFieldHomEquivPointed (K : Type*) [Field K] [IsAlgClosed K]
    (R : Type*) [CommRing R] :
    (DeningerCanonicalRationalWittRing K →+* R) ≃ (K →*₀ R) :=
  letI := deningerIsAlgClosed_fractionRing K
  deningerWittRingHomEquivPointed K R

@[simp] theorem deningerWittFieldHomEquivPointed_apply (K : Type*) [Field K] [IsAlgClosed K]
    (R : Type*) [CommRing R] (φ : DeningerCanonicalRationalWittRing K →+* R) (a : K) :
    deningerWittFieldHomEquivPointed K R φ a
      = φ (deningerCanonicalRationalWittTeichmuller a) := by
  letI := deningerIsAlgClosed_fractionRing K
  exact deningerWittRingHomEquivPointed_apply R φ a

/-! ### The Witt-vector description of the valued points -/

variable {X : Scheme.{u}} {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]

/-- **Deninger, Proposition 13.1 (`t41`).**  An `𝒪`-valued point of `W_rat (X)` in the description
by ring homomorphisms out of rational Witt rings: a specialisation `y` of `x` together with
Deninger's commuting diagram of homomorphisms `f_η^♯`, `f_s^♯`, `f̃_s^♯`. -/
structure DeningerWittValuedPoint (X : Scheme.{u}) (O : Type u) [CommRing O] [IsDomain O]
    [IsLocalRing O] where
  /-- The generic point. -/
  gen : X
  /-- The specialisation. -/
  spec : X
  /-- `spec` lies in the closure of `gen`. -/
  specializes : gen ⤳ spec
  /-- Deninger's `f̃_η^♯ : W_rat (κ (x)) → C`. -/
  charHom : DeningerCanonicalRationalWittRing (X.residueField gen) →+* FractionRing O
  /-- Deninger's `f_s^♯ : W_rat (𝒪_{X,y}) → 𝒪`. -/
  localHom : DeningerCanonicalRationalWittRing (X.presheaf.stalk spec) →+* O
  /-- Deninger's `f̃_s^♯ : W_rat (κ (y)) → k`. -/
  residueHom :
    DeningerCanonicalRationalWittRing (X.residueField spec) →+* IsLocalRing.ResidueField O
  /-- The lower square of (140): the character recovers the local homomorphism after inverting. -/
  comm_gen : ∀ w : DeningerCanonicalRationalWittRing (X.presheaf.stalk spec),
    algebraMap O (FractionRing O) (localHom w)
      = charHom (deningerCanonicalRationalWittMap (stalkValueHom specializes) w)
  /-- The upper square of (140): the local homomorphism reduces to the residue homomorphism. -/
  comm_spec : ∀ w : DeningerCanonicalRationalWittRing (X.presheaf.stalk spec),
    IsLocalRing.residue O (localHom w)
      = residueHom (deningerCanonicalRationalWittMap (X.residue spec).hom w)

theorem DeningerWittValuedPoint.ext' {T U : DeningerWittValuedPoint X O} (hg : T.gen = U.gen)
    (hs : T.spec = U.spec) (hc : HEq T.charHom U.charHom) (hl : HEq T.localHom U.localHom)
    (hr : HEq T.residueHom U.residueHom) : T = U := by
  obtain ⟨g, s, hsp, c, l, r, c1, c2⟩ := T
  obtain ⟨g', s', hsp', c', l', r', c1', c2'⟩ := U
  cases hg
  cases hs
  cases hc
  cases hl
  cases hr
  rfl

variable [∀ x : X, IsAlgClosed (X.residueField x)]
variable [∀ x : X, IsDomain (X.presheaf.stalk x)]
variable [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
variable [∀ x : X, IsAlgClosed (FractionRing (X.presheaf.stalk x))]

/-- **Deninger, (145).**  The Witt-vector description of an `𝒪`-valued point gives the character
description of Definition 13.2. -/
def DeningerWittValuedPoint.toCharTriple (T : DeningerWittValuedPoint X O) :
    DeningerValuedCharTriple X O where
  gen := T.gen
  spec := T.spec
  specializes := T.specializes
  chr := deningerFieldPointedEquivChar _ _
    (deningerWittFieldHomEquivPointed (X.residueField T.gen) (FractionRing O) T.charHom)
  localMap := deningerWittRingHomEquivPointed (X.presheaf.stalk T.spec) O T.localHom
  residueMap := deningerWittFieldHomEquivPointed (X.residueField T.spec)
    (IsLocalRing.ResidueField O) T.residueHom
  comm_gen := by
    intro a
    have hchr : deningerCharExtendByZero (deningerFieldPointedEquivChar _ _
        (deningerWittFieldHomEquivPointed (X.residueField T.gen) (FractionRing O) T.charHom))
        = deningerWittFieldHomEquivPointed (X.residueField T.gen) (FractionRing O) T.charHom :=
      (deningerFieldPointedEquivChar _ _).symm_apply_apply _
    have hval : (X.residue T.gen).hom
        ((X.presheaf.stalkSpecializes T.specializes).hom a)
        = stalkValueHom T.specializes a := rfl
    rw [hchr, deningerWittRingHomEquivPointed_apply, hval,
      deningerWittFieldHomEquivPointed_apply,
      ← deningerCanonicalRationalWittMap_teichmuller (stalkValueHom T.specializes) a]
    exact T.comm_gen (deningerCanonicalRationalWittTeichmuller a)
  comm_spec := by
    intro a
    rw [deningerWittRingHomEquivPointed_apply, deningerWittFieldHomEquivPointed_apply,
      ← deningerCanonicalRationalWittMap_teichmuller (X.residue T.spec).hom a]
    exact T.comm_spec (deningerCanonicalRationalWittTeichmuller a)

/-- **Deninger, (145).**  The character description of an `𝒪`-valued point gives the Witt-vector
description of Proposition 13.1. -/
def DeningerValuedCharTriple.toWittValuedPoint (P : DeningerValuedCharTriple X O) :
    DeningerWittValuedPoint X O where
  gen := P.gen
  spec := P.spec
  specializes := P.specializes
  charHom := (deningerWittFieldHomEquivPointed (X.residueField P.gen) (FractionRing O)).symm
    ((deningerFieldPointedEquivChar _ _).symm P.chr)
  localHom := (deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).symm P.localMap
  residueHom := (deningerWittFieldHomEquivPointed (X.residueField P.spec)
    (IsLocalRing.ResidueField O)).symm P.residueMap
  comm_gen := by
    have hloc : ∀ a : X.presheaf.stalk P.spec,
        ((deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).symm P.localMap)
            (deningerCanonicalRationalWittTeichmuller a) = P.localMap a := by
      intro a
      have h := deningerWittRingHomEquivPointed_apply (A := X.presheaf.stalk P.spec) O
        ((deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).symm P.localMap) a
      rw [(deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).apply_symm_apply] at h
      exact h.symm
    have hchr : ∀ t : X.residueField P.gen,
        ((deningerWittFieldHomEquivPointed (X.residueField P.gen) (FractionRing O)).symm
            ((deningerFieldPointedEquivChar _ _).symm P.chr))
            (deningerCanonicalRationalWittTeichmuller t)
          = deningerCharExtendByZero P.chr t := by
      intro t
      have h := deningerWittFieldHomEquivPointed_apply (X.residueField P.gen) (FractionRing O)
        ((deningerWittFieldHomEquivPointed (X.residueField P.gen) (FractionRing O)).symm
          ((deningerFieldPointedEquivChar _ _).symm P.chr)) t
      rw [(deningerWittFieldHomEquivPointed (X.residueField P.gen)
        (FractionRing O)).apply_symm_apply] at h
      exact h.symm
    have key : ((algebraMap O (FractionRing O)).comp
          ((deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).symm P.localMap))
        = (((deningerWittFieldHomEquivPointed (X.residueField P.gen) (FractionRing O)).symm
            ((deningerFieldPointedEquivChar _ _).symm P.chr)).comp
          (deningerCanonicalRationalWittMap (stalkValueHom P.specializes))) := by
      refine (deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec)
        (FractionRing O)).injective ?_
      refine MonoidWithZeroHom.ext fun a => ?_
      rw [deningerWittRingHomEquivPointed_apply, deningerWittRingHomEquivPointed_apply,
        RingHom.comp_apply, RingHom.comp_apply, hloc a,
        deningerCanonicalRationalWittMap_teichmuller, hchr]
      exact P.comm_gen a
    intro w
    exact congrArg (fun ψ : DeningerCanonicalRationalWittRing (X.presheaf.stalk P.spec) →+*
      FractionRing O => ψ w) key
  comm_spec := by
    have hloc : ∀ a : X.presheaf.stalk P.spec,
        ((deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).symm P.localMap)
            (deningerCanonicalRationalWittTeichmuller a) = P.localMap a := by
      intro a
      have h := deningerWittRingHomEquivPointed_apply (A := X.presheaf.stalk P.spec) O
        ((deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).symm P.localMap) a
      rw [(deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).apply_symm_apply] at h
      exact h.symm
    have hres : ∀ t : X.residueField P.spec,
        ((deningerWittFieldHomEquivPointed (X.residueField P.spec)
            (IsLocalRing.ResidueField O)).symm P.residueMap)
            (deningerCanonicalRationalWittTeichmuller t) = P.residueMap t := by
      intro t
      have h := deningerWittFieldHomEquivPointed_apply (X.residueField P.spec)
        (IsLocalRing.ResidueField O)
        ((deningerWittFieldHomEquivPointed (X.residueField P.spec)
          (IsLocalRing.ResidueField O)).symm P.residueMap) t
      rw [(deningerWittFieldHomEquivPointed (X.residueField P.spec)
        (IsLocalRing.ResidueField O)).apply_symm_apply] at h
      exact h.symm
    have key : ((IsLocalRing.residue O).comp
          ((deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).symm P.localMap))
        = (((deningerWittFieldHomEquivPointed (X.residueField P.spec)
            (IsLocalRing.ResidueField O)).symm P.residueMap).comp
          (deningerCanonicalRationalWittMap (X.residue P.spec).hom)) := by
      refine (deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec)
        (IsLocalRing.ResidueField O)).injective ?_
      refine MonoidWithZeroHom.ext fun a => ?_
      rw [deningerWittRingHomEquivPointed_apply, deningerWittRingHomEquivPointed_apply,
        RingHom.comp_apply, RingHom.comp_apply, hloc a,
        deningerCanonicalRationalWittMap_teichmuller, hres]
      exact P.comm_spec a
    intro w
    exact congrArg (fun ψ : DeningerCanonicalRationalWittRing (X.presheaf.stalk P.spec) →+*
      IsLocalRing.ResidueField O => ψ w) key

/-- **Deninger, (145).**  For a scheme with algebraically closed residue fields whose local rings
are integrally closed domains with algebraically closed fraction field, the `𝒪`-valued points of
`W_rat (X)` in the sense of Proposition 13.1 are exactly the character triples of
Definition 13.2. -/
def deningerWittValuedPointEquiv :
    DeningerWittValuedPoint X O ≃ DeningerValuedCharTriple X O where
  toFun := DeningerWittValuedPoint.toCharTriple
  invFun := DeningerValuedCharTriple.toWittValuedPoint
  left_inv T := by
    refine DeningerWittValuedPoint.ext' rfl rfl (heq_of_eq ?_) (heq_of_eq ?_) (heq_of_eq ?_)
    · show (deningerWittFieldHomEquivPointed (X.residueField T.gen) (FractionRing O)).symm
        ((deningerFieldPointedEquivChar _ _).symm (deningerFieldPointedEquivChar _ _
          (deningerWittFieldHomEquivPointed (X.residueField T.gen)
            (FractionRing O) T.charHom))) = T.charHom
      rw [(deningerFieldPointedEquivChar _ _).symm_apply_apply,
        (deningerWittFieldHomEquivPointed (X.residueField T.gen)
          (FractionRing O)).symm_apply_apply]
    · exact (deningerWittRingHomEquivPointed (X.presheaf.stalk T.spec) O).symm_apply_apply _
    · exact (deningerWittFieldHomEquivPointed (X.residueField T.spec)
        (IsLocalRing.ResidueField O)).symm_apply_apply _
  right_inv P := by
    refine DeningerValuedCharTriple.ext' rfl rfl (heq_of_eq ?_) (heq_of_eq ?_) (heq_of_eq ?_)
    · show deningerFieldPointedEquivChar _ _
        (deningerWittFieldHomEquivPointed (X.residueField P.gen) (FractionRing O)
          ((deningerWittFieldHomEquivPointed (X.residueField P.gen) (FractionRing O)).symm
            ((deningerFieldPointedEquivChar _ _).symm P.chr))) = P.chr
      rw [(deningerWittFieldHomEquivPointed (X.residueField P.gen)
          (FractionRing O)).apply_symm_apply,
        (deningerFieldPointedEquivChar _ _).apply_symm_apply]
    · exact (deningerWittRingHomEquivPointed (X.presheaf.stalk P.spec) O).apply_symm_apply _
    · exact (deningerWittFieldHomEquivPointed (X.residueField P.spec)
        (IsLocalRing.ResidueField O)).apply_symm_apply _

/-- **Deninger, (145) and Proposition 13.4.**  The `𝒪`-valued points of `W_rat (X)` are the
triples `(x , y , P'_y)`. -/
def deningerWittValuedPointTripleEquiv :
    DeningerWittValuedPoint X O ≃ DeningerValuedTriple X O :=
  deningerWittValuedPointEquiv.trans deningerValuedCharTripleEquiv

end

end RHTower
