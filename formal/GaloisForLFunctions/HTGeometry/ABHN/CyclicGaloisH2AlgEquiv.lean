/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisH2NormQuotient

/-!
# Cyclic degree-two cohomology under extension equivalence

A base-preserving equivalence between two finite extensions preserves field norms. Consequently it
identifies their base-unit norm subgroups, norm quotients, and cyclic degree-two cohomology groups.
This makes the finite local invariant independent of a chosen concrete unramified root-lift model.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

/-- A `K`-algebra equivalence between finite extensions preserves the subgroup of base units that
occur as field norms. -/
theorem cyclicGaloisH2BaseNormImage_eq_of_algEquiv
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L] [FiniteDimensional K M]
    (e : L ≃ₐ[K] M) :
    cyclicGaloisH2BaseNormImage K L = cyclicGaloisH2BaseNormImage K M := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨Additive.ofMul
      (Units.map e.toRingEquiv.toMonoidHom (Additive.toMul x)), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    change Algebra.norm K (e ((Additive.toMul x : Lˣ) : L)) =
      Algebra.norm K ((Additive.toMul x : Lˣ) : L)
    exact Algebra.norm_eq_of_algEquiv e _
  · rintro ⟨x, rfl⟩
    refine ⟨Additive.ofMul
      (Units.map e.symm.toRingEquiv.toMonoidHom (Additive.toMul x)), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    change Algebra.norm K (e.symm ((Additive.toMul x : Mˣ) : M)) =
      Algebra.norm K ((Additive.toMul x : Mˣ) : M)
    exact Algebra.norm_eq_of_algEquiv e.symm _

/-- A `K`-algebra equivalence of extensions identifies their base-unit norm quotients. -/
noncomputable def cyclicGaloisH2BaseNormQuotientAddEquivOfAlgEquiv
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L] [FiniteDimensional K M]
    (e : L ≃ₐ[K] M) :
    (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) ≃+
      (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K M) :=
  QuotientAddGroup.quotientAddEquivOfEq
    (cyclicGaloisH2BaseNormImage_eq_of_algEquiv K L M e)

/-- Cyclic degree-two cohomology is invariant under `K`-algebra equivalence of finite cyclic
Galois extensions. -/
noncomputable def cyclicGaloisH2AddEquivOfAlgEquiv
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M] [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (e : L ≃ₐ[K] M) : cyclicGaloisH2 K L ≃+ cyclicGaloisH2 K M :=
  (cyclicGaloisH2BaseNormQuotientEquiv K L).symm |>.trans
    ((cyclicGaloisH2BaseNormQuotientAddEquivOfAlgEquiv K L M e).trans
      (cyclicGaloisH2BaseNormQuotientEquiv K M))

/-- A ring equivalence induces a multiplicative equivalence of unit groups. -/
def unitsMulEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Rˣ ≃* Sˣ where
  toFun := Units.map e.toMonoidHom
  invFun := Units.map e.symm.toMonoidHom
  left_inv x := by
    apply Units.ext
    simp
  right_inv x := by
    apply Units.ext
    simp
  map_mul' x y := by simp

/-- Additive presentation of the unit equivalence induced by a ring equivalence. -/
def additiveUnitsAddEquivOfRingEquiv {R S : Type} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Additive Rˣ ≃+ Additive Sˣ :=
  MulEquiv.toAdditive (unitsMulEquivOfRingEquiv e)

/-- Compatible equivalences of base and extension fields intertwine the two field-norm maps on
units. -/
theorem additiveUnitsAddEquivOfRingEquiv_cyclicGaloisAdditiveNormUnits
    (K K' L L' : Type) [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L'] (eK : K ≃+* K') (eL : L ≃+* L')
    (he : (algebraMap K' L').comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap K L)) (x : Additive Lˣ) :
    additiveUnitsAddEquivOfRingEquiv eK (cyclicGaloisAdditiveNormUnits K L x) =
      cyclicGaloisAdditiveNormUnits K' L'
        (additiveUnitsAddEquivOfRingEquiv eL x) := by
  apply Additive.toMul.injective
  apply Units.ext
  change eK (Algebra.norm K ((Additive.toMul x : Lˣ) : L)) =
    Algebra.norm K' (eL ((Additive.toMul x : Lˣ) : L))
  have hnorm := Algebra.norm_eq_of_equiv_equiv eK eL he
    ((Additive.toMul x : Lˣ) : L)
  simpa using congrArg eK hnorm

/-- Compatible equivalences of base and extension fields identify their base-unit norm
quotients. This is the base-changing counterpart of
`cyclicGaloisH2BaseNormQuotientAddEquivOfAlgEquiv`. -/
noncomputable def cyclicGaloisH2BaseNormQuotientAddEquivOfEquivEquiv
    (K K' L L' : Type) [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : (algebraMap K' L').comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap K L)) :
    (Additive Kˣ ⧸ cyclicGaloisH2BaseNormImage K L) ≃+
      (Additive K'ˣ ⧸ cyclicGaloisH2BaseNormImage K' L') := by
  let fK := additiveUnitsAddEquivOfRingEquiv eK
  let fL := additiveUnitsAddEquivOfRingEquiv eL
  have he' : (algebraMap K L).comp eK.symm.toRingHom =
      eL.symm.toRingHom.comp (algebraMap K' L') := by
    ext x
    apply eL.injective
    have hx := DFunLike.congr_fun he (eK.symm x)
    simpa using hx.symm
  have hf : cyclicGaloisH2BaseNormImage K L ≤
      AddSubgroup.comap fK.toAddMonoidHom (cyclicGaloisH2BaseNormImage K' L') := by
    rintro a ⟨x, hx⟩
    refine ⟨fL x, ?_⟩
    rw [← additiveUnitsAddEquivOfRingEquiv_cyclicGaloisAdditiveNormUnits
      K K' L L' eK eL he]
    exact congrArg fK hx
  have hg : cyclicGaloisH2BaseNormImage K' L' ≤
      AddSubgroup.comap fK.symm.toAddMonoidHom (cyclicGaloisH2BaseNormImage K L) := by
    rintro a ⟨x, hx⟩
    refine ⟨additiveUnitsAddEquivOfRingEquiv eL.symm x, ?_⟩
    calc
      cyclicGaloisAdditiveNormUnits K L
          (additiveUnitsAddEquivOfRingEquiv eL.symm x) =
          additiveUnitsAddEquivOfRingEquiv eK.symm
            (cyclicGaloisAdditiveNormUnits K' L' x) :=
        (additiveUnitsAddEquivOfRingEquiv_cyclicGaloisAdditiveNormUnits
          K' K L' L eK.symm eL.symm he' x).symm
      _ = additiveUnitsAddEquivOfRingEquiv eK.symm a :=
        congrArg (additiveUnitsAddEquivOfRingEquiv eK.symm) hx
      _ = fK.symm a := by rfl
  let qf := QuotientAddGroup.map (cyclicGaloisH2BaseNormImage K L)
    (cyclicGaloisH2BaseNormImage K' L') fK.toAddMonoidHom hf
  let qg := QuotientAddGroup.map (cyclicGaloisH2BaseNormImage K' L')
    (cyclicGaloisH2BaseNormImage K L) fK.symm.toAddMonoidHom hg
  apply AddMonoidHom.toAddEquiv qf qg
  · apply AddMonoidHom.ext
    intro z
    refine QuotientAddGroup.induction_on z ?_
    intro a
    simp [qf, qg, fK]
  · apply AddMonoidHom.ext
    intro z
    refine QuotientAddGroup.induction_on z ?_
    intro a
    simp [qf, qg, fK]

/-- Cyclic degree-two cohomology is invariant under compatible equivalences of both the base and
extension fields. -/
noncomputable def cyclicGaloisH2AddEquivOfEquivEquiv
    (K K' L L' : Type) [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
    [IsGalois K L] [IsGalois K' L'] [IsCyclic Gal(L/K)] [IsCyclic Gal(L'/K')]
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : (algebraMap K' L').comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap K L)) :
    cyclicGaloisH2 K L ≃+ cyclicGaloisH2 K' L' :=
  (cyclicGaloisH2BaseNormQuotientEquiv K L).symm |>.trans
    ((cyclicGaloisH2BaseNormQuotientAddEquivOfEquivEquiv K K' L L' eK eL he).trans
      (cyclicGaloisH2BaseNormQuotientEquiv K' L'))

end

end GaloisForLFunctions.HTGeometry.ABHN
