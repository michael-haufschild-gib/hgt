import GaloisForLFunctions.RHTower.DeningerDynSysValuedLocalTriple
import GaloisForLFunctions.HTGeometry.FractionFieldMultiplicativeExtension

/-!
# The character description of the `𝒪`-valued points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 13.4
(`t44`), the equivalence of Definition 13.2 with the description by `P_y`.

A character triple `(x , y , P^×)` gives the pointed multiplicative map `P_y` on `𝒪_{X,y}`, and the
three conditions of Deninger's Proposition 13.4 are read off the two commuting squares: the lower
one forces the value to be determined by, and to vanish only with, the value at `x`, and the upper
one forces the residue of the value to be determined by the value at `y`.

Conversely `P^×` is recovered from `P'_y` as the extension of `P'_y` to the fraction fields:
`κ (x)` is the fraction field of `𝒪_{closure {x} , y}` and `P'_y` is nonzero off `0`, so
`P^× (a / b) = P'_y (a) / P'_y (b)` is well defined, and it is the only pointed multiplicative map
restricting to `P'_y`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry

noncomputable section

universe u

variable {X : Scheme.{u}} {x y : X}

theorem deningerClosureResidue_surjective (h : x ⤳ y) :
    Function.Surjective (deningerClosureResidue h) := by
  intro t
  obtain ⟨a, rfl⟩ := X.residue_surjective y t
  exact ⟨DeningerClosureLocalRing.mk h a, rfl⟩

variable {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O]

theorem DeningerValuedCharTriple.ext' {P Q : DeningerValuedCharTriple X O} (hg : P.gen = Q.gen)
    (hs : P.spec = Q.spec) (hc : HEq P.chr Q.chr) (hl : HEq P.localMap Q.localMap)
    (hr : HEq P.residueMap Q.residueMap) : P = Q := by
  obtain ⟨g, s, hsp, c, l, r, c1, c2⟩ := P
  obtain ⟨g', s', hsp', c', l', r', c1', c2'⟩ := Q
  cases hg
  cases hs
  cases hc
  cases hl
  cases hr
  rfl

/-! ### From a character triple to the description by `P_y` -/

/-- **Deninger, Proposition 13.4 (`t44`).**  A character triple gives a pointed multiplicative map
on the local ring at the specialisation satisfying Deninger's conditions 1), 2), 3). -/
@[reducible] def DeningerValuedCharTriple.toLocalTriple (P : DeningerValuedCharTriple X O) :
    DeningerValuedLocalTriple X O where
  gen := P.gen
  spec := P.spec
  specializes := P.specializes
  map := P.localMap
  map_ne_zero := by
    intro f hf hzero
    have h := P.comm_gen f
    rw [hzero, map_zero] at h
    exact hf ((deningerCharExtendByZero_eq_zero_iff P.chr _).1 h.symm)
  map_congr := by
    intro f g hfg
    have h1 := P.comm_gen f
    have h2 := P.comm_gen g
    have h3 : algebraMap O (FractionRing O) (P.localMap f)
        = algebraMap O (FractionRing O) (P.localMap g) := by
      rw [h1, h2]
      exact congrArg _ hfg
    exact IsFractionRing.injective O (FractionRing O) h3
  map_residue := by
    intro f g hfg
    have h1 := P.comm_spec f
    have h2 := P.comm_spec g
    have h3 : IsLocalRing.residue O (P.localMap f) = IsLocalRing.residue O (P.localMap g) := by
      rw [h1, h2, hfg]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h3

/-- **Deninger, Proposition 13.4 (`t44`).**  A character triple gives an `𝒪`-valued triple. -/
@[reducible] def DeningerValuedCharTriple.toValuedTriple (P : DeningerValuedCharTriple X O) :
    DeningerValuedTriple X O :=
  P.toLocalTriple.toValuedTriple

/-! ### From an `𝒪`-valued triple to a character triple -/

/-- The map induced on the residue field at the specialisation. -/
def DeningerValuedTriple.residueFun (T : DeningerValuedTriple X O)
    (t : X.residueField T.spec) : IsLocalRing.ResidueField O :=
  IsLocalRing.residue O
    (T.map (Function.surjInv (deningerClosureResidue_surjective T.specializes) t))

omit [IsDomain O] in
theorem DeningerValuedTriple.residueFun_apply (T : DeningerValuedTriple X O)
    (d : DeningerClosureLocalRing T.specializes) :
    T.residueFun (deningerClosureResidue T.specializes d) = IsLocalRing.residue O (T.map d) := by
  have hs := Function.surjInv_eq (deningerClosureResidue_surjective T.specializes)
    (deningerClosureResidue T.specializes d)
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (T.map_residue _ _ hs)

/-- The pointed multiplicative map induced on the residue field at the specialisation. -/
def DeningerValuedTriple.residueMap (T : DeningerValuedTriple X O) :
    X.residueField T.spec →*₀ IsLocalRing.ResidueField O where
  toFun := T.residueFun
  map_zero' := by
    have h : (0 : X.residueField T.spec) = deningerClosureResidue T.specializes 0 :=
      (map_zero _).symm
    rw [h, T.residueFun_apply, map_zero, map_zero]
  map_one' := by
    have h : (1 : X.residueField T.spec) = deningerClosureResidue T.specializes 1 :=
      (map_one _).symm
    rw [h, T.residueFun_apply, map_one, map_one]
  map_mul' s t := by
    obtain ⟨a, rfl⟩ := deningerClosureResidue_surjective T.specializes s
    obtain ⟨b, rfl⟩ := deningerClosureResidue_surjective T.specializes t
    rw [← map_mul, T.residueFun_apply, T.residueFun_apply, T.residueFun_apply, map_mul, map_mul]

/-- **Deninger, Proposition 13.4 (`t44`).**  An `𝒪`-valued triple gives a character triple: the
character is the extension of the pointed multiplicative map to the fraction fields. -/
def DeningerValuedTriple.charTriple (T : DeningerValuedTriple X O) :
    DeningerValuedCharTriple X O :=
  letI := deningerClosureAlgebra T.specializes
  haveI := deningerClosure_isFractionRing T.specializes
  { gen := T.gen
    spec := T.spec
    specializes := T.specializes
    chr := fractionMulExtendUnits (K := X.residueField T.gen) (L := FractionRing O)
      T.map T.map_ne_zero
    localMap := T.map.comp
      (DeningerClosureLocalRing.mk T.specializes : _ →+* _).toMonoidWithZeroHom
    residueMap := T.residueMap
    comm_gen := by
      intro a
      set d := DeningerClosureLocalRing.mk T.specializes a with hd
      show algebraMap O (FractionRing O) (T.map d) = _
      have hval : (X.residue T.gen).hom ((X.presheaf.stalkSpecializes T.specializes).hom a)
          = deningerClosureToResidue T.specializes d := rfl
      rw [hval]
      by_cases hz : d = 0
      · rw [hz]
        simp
      · have hne : deningerClosureToResidue T.specializes d ≠ 0 := fun hc =>
          hz ((injective_iff_map_eq_zero _).1 (deningerClosureToResidue_injective _) _ hc)
        rw [deningerCharExtendByZero_apply_ne_zero _ hne]
        have hu : ((fractionMulExtendUnits (K := X.residueField T.gen) (L := FractionRing O)
            T.map T.map_ne_zero (Units.mk0 _ hne) : (FractionRing O)ˣ) : FractionRing O)
            = fractionMulExtend (L := FractionRing O) T.map T.map_ne_zero
              (deningerClosureToResidue T.specializes d) := rfl
        rw [hu]
        have : (algebraMap (DeningerClosureLocalRing T.specializes) (X.residueField T.gen)) d
            = deningerClosureToResidue T.specializes d := rfl
        rw [← this, fractionMulExtend_algebraMap]
    comm_spec := by
      intro a
      show IsLocalRing.residue O (T.map (DeningerClosureLocalRing.mk T.specializes a)) = _
      exact (T.residueFun_apply (DeningerClosureLocalRing.mk T.specializes a)).symm }

/-! ### The bijection -/

/-- **Deninger, Proposition 13.4 (`t44`).**  The description of the `𝒪`-valued points of
`W_rat (X)` by a character of `κ (x)ˣ` and the description by a pointed multiplicative map on
`𝒪_{closure {x} , y}` are the same. -/
def deningerValuedCharTripleEquiv :
    DeningerValuedCharTriple X O ≃ DeningerValuedTriple X O where
  toFun := DeningerValuedCharTriple.toValuedTriple
  invFun := DeningerValuedTriple.charTriple
  left_inv P := by
    letI := deningerClosureAlgebra P.specializes
    haveI := deningerClosure_isFractionRing P.specializes
    have hloc : ∀ a : X.presheaf.stalk P.spec,
        P.toValuedTriple.map (DeningerClosureLocalRing.mk P.specializes a) = P.localMap a :=
      fun a => P.toLocalTriple.closureMap_mk a
    have halgmap : ∀ d : DeningerClosureLocalRing P.specializes,
        (algebraMap (DeningerClosureLocalRing P.specializes) (X.residueField P.gen)) d
          = deningerClosureToResidue P.specializes d := fun _ => rfl
    have hext : (deningerCharExtendByZero P.chr : X.residueField P.gen →*₀ FractionRing O)
        = fractionMulExtend (K := X.residueField P.gen) (L := FractionRing O)
            P.toValuedTriple.map P.toValuedTriple.map_ne_zero := by
      refine eq_fractionMulExtend _ _ _ fun d => ?_
      obtain ⟨a, rfl⟩ := DeningerClosureLocalRing.mk_surjective P.specializes d
      rw [halgmap, hloc]
      exact (P.comm_gen a).symm
    have hchr : (fractionMulExtendUnits (K := X.residueField P.gen) (L := FractionRing O)
        P.toValuedTriple.map P.toValuedTriple.map_ne_zero) = P.chr := by
      refine MonoidHom.ext fun u => Units.ext ?_
      have hu : (u : X.residueField P.gen) ≠ 0 := u.ne_zero
      have h1 : ((fractionMulExtendUnits (K := X.residueField P.gen) (L := FractionRing O)
          P.toValuedTriple.map P.toValuedTriple.map_ne_zero u : (FractionRing O)ˣ)
            : FractionRing O)
          = fractionMulExtend (K := X.residueField P.gen) (L := FractionRing O)
              P.toValuedTriple.map P.toValuedTriple.map_ne_zero (u : X.residueField P.gen) := rfl
      have hmk : Units.mk0 (u : X.residueField P.gen) hu = u := Units.ext rfl
      rw [h1, ← hext, deningerCharExtendByZero_apply_ne_zero P.chr hu, hmk]
    have hlm : (P.toValuedTriple.map.comp
        (DeningerClosureLocalRing.mk P.specializes : _ →+* _).toMonoidWithZeroHom)
          = P.localMap := MonoidWithZeroHom.ext hloc
    have hrm : P.toValuedTriple.residueMap = P.residueMap := by
      refine MonoidWithZeroHom.ext fun t => ?_
      obtain ⟨a, rfl⟩ := X.residue_surjective P.spec t
      have h3 := P.toValuedTriple.residueFun_apply (DeningerClosureLocalRing.mk P.specializes a)
      rw [hloc] at h3
      exact h3.trans (P.comm_spec a)
    exact DeningerValuedCharTriple.ext' rfl rfl (heq_of_eq hchr) (heq_of_eq hlm) (heq_of_eq hrm)
  right_inv T := by
    refine DeningerValuedTriple.ext' rfl rfl (heq_of_eq ?_)
    refine MonoidWithZeroHom.ext fun d => ?_
    obtain ⟨a, rfl⟩ := DeningerClosureLocalRing.mk_surjective T.specializes d
    exact T.charTriple.toLocalTriple.closureMap_mk a

/-- **Deninger, Proposition 13.4 (`t44`).**  All three descriptions of the `𝒪`-valued points of
`W_rat (X)` agree. -/
def deningerValuedCharLocalTripleEquiv :
    DeningerValuedCharTriple X O ≃ DeningerValuedLocalTriple X O :=
  deningerValuedCharTripleEquiv.trans deningerValuedLocalTripleEquiv.symm

end

end RHTower
