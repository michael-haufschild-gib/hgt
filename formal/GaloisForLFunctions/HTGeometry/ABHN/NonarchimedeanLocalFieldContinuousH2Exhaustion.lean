import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldContinuousCyclicGaloisH2TorsionInvariant
import GaloisForLFunctions.HTGeometry.ABHN.RatModIntTorsionCircleCharacter

/-!
# Exhaustion of the nonarchimedean local invariant target by finite unramified `H²`

Every class in `ℚ/ℤ` has a positive finite denominator.  For every positive degree, the local
valuation infrastructure constructs a concrete monic unramified root lift, and continuous unit
`H²` of its fraction-field extension is equivalent to the corresponding torsion layer
`ℚ/ℤ[n]`.  Combining those closed results proves:

* every `ℚ/ℤ` class is realized by a concrete finite unramified continuous local `H²` class;
* every rational circle phase is realized in such a layer;
* every finite-support `ℚ/ℤ` profile is realized inside one common finite layer.

This is the finite-layer surjectivity part of the nonarchimedean local invariant.  It does not
identify the resulting `H²` classes with Brauer classes, nor identify coordinate transitions with
genuine cohomological inflation through a chosen field tower.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

/-- A finite unramified root lift has positive residue degree. -/
theorem nonarchimedeanLocalFieldAdjoinRoot_natDegree_ne_zero
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (f : Polynomial 𝒪[K]) (hf : f.Monic)
    (g : Polynomial 𝓀[K]) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g)
    (hg : Irreducible g) : f.natDegree ≠ 0 := by
  intro hzero
  apply nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K f hf g hfg hg
  rw [Polynomial.degree_eq_natDegree hf.ne_zero, hzero]
  rfl

/-- A rational invariant value is realized by continuous `H²` of a concrete finite unramified
root lift. -/
def NonarchimedeanLocalFiniteUnramifiedContinuousH2Realizes
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : RatModInt) : Prop :=
  ∃ (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
      (hf : f.Monic) (hgmonic : g.Monic)
      (hg : Irreducible g) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g),
    let e :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
        K f hf g hgmonic hfg hg
    ∃ z, ((e z : ratModIntNTorsion f.natDegree) : RatModInt) = x

/-- Every `ℚ/ℤ` class occurs at some concrete finite unramified continuous local `H²` layer. -/
theorem nonarchimedeanLocalField_every_ratModInt_realized_by_finiteUnramifiedContinuousH2
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : RatModInt) :
    NonarchimedeanLocalFiniteUnramifiedContinuousH2Realizes K x := by
  obtain ⟨n, hn, hx⟩ := ratModInt_exists_nonzero_nsmul_eq_zero x
  letI : NeZero n := ⟨hn⟩
  obtain ⟨f, g, hf, hgmonic, hg, hfg, hdegree, _⟩ :=
    nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree K n
  refine ⟨f, g, hf, hgmonic, hg, hfg, ?_⟩
  let e :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
      K f hf g hgmonic hfg hg
  have hx' : x ∈ ratModIntNTorsion f.natDegree := by
    rw [hdegree]
    exact hx
  refine ⟨e.symm ⟨x, hx'⟩, ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx'⟩)

/-- A complex phase is realized by a finite unramified continuous local `H²` invariant. -/
def NonarchimedeanLocalFiniteUnramifiedContinuousH2PhaseRealizes
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (c : ℂ) : Prop :=
  ∃ (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
      (hf : f.Monic) (hgmonic : g.Monic)
      (hg : Irreducible g) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g),
    let e :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
        K f hf g hgmonic hfg hg
    let hn := nonarchimedeanLocalFieldAdjoinRoot_natDegree_ne_zero K f hf g hfg hg
    ∃ z, ratModIntNTorsionStdAddChar f.natDegree hn (e z) = c

/-- Every rational circle phase occurs at some concrete finite unramified continuous local
`H²` layer. -/
theorem nonarchimedeanLocalField_every_ratModIntStdAddChar_realized_by_finiteUnramifiedContinuousH2
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : RatModInt) :
    NonarchimedeanLocalFiniteUnramifiedContinuousH2PhaseRealizes K
      (ratModIntStdAddChar x) := by
  obtain ⟨f, g, hf, hgmonic, hg, hfg, z, hz⟩ :=
    nonarchimedeanLocalField_every_ratModInt_realized_by_finiteUnramifiedContinuousH2 K x
  refine ⟨f, g, hf, hgmonic, hg, hfg, z, ?_⟩
  let e :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
      K f hf g hgmonic hfg hg
  let hn := nonarchimedeanLocalFieldAdjoinRoot_natDegree_ne_zero K f hf g hfg hg
  calc
    ratModIntNTorsionStdAddChar f.natDegree hn (e z) =
        ratModIntStdAddChar ((e z : ratModIntNTorsion f.natDegree) : RatModInt) :=
      (ratModIntStdAddChar_subtype_eq_ratModIntNTorsionStdAddChar
        f.natDegree hn (e z)).symm
    _ = ratModIntStdAddChar x := by rw [hz]

/-- A finite-support `ℚ/ℤ` profile is realized coordinatewise inside one finite unramified
continuous local `H²` layer. -/
def NonarchimedeanLocalFiniteUnramifiedContinuousH2RealizesProfile
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {ι : Type*} (x : ι →₀ RatModInt) : Prop :=
  ∃ (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
      (hf : f.Monic) (hgmonic : g.Monic)
      (hg : Irreducible g) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g),
    let e :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
        K f hf g hgmonic hfg hg
    ∃ z : ι →₀ _, ∀ i,
      ((e (z i) : ratModIntNTorsion f.natDegree) : RatModInt) = x i

/-- Every finite-support `ℚ/ℤ` profile is simultaneously realized at one concrete finite
unramified continuous local `H²` layer. -/
theorem nonarchimedeanLocalField_every_finsuppRatModInt_realized_by_one_finiteUnramifiedContinuousH2
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {ι : Type*} (x : ι →₀ RatModInt) :
    NonarchimedeanLocalFiniteUnramifiedContinuousH2RealizesProfile K x := by
  classical
  obtain ⟨n, hn, hx⟩ := finsupp_exists_nonzero_common_ratModIntTorsion x
  letI : NeZero n := ⟨hn⟩
  obtain ⟨f, g, hf, hgmonic, hg, hfg, hdegree, _⟩ :=
    nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree K n
  refine ⟨f, g, hf, hgmonic, hg, hfg, ?_⟩
  let e :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
      K f hf g hgmonic hfg hg
  have hx' : ∀ i, x i ∈ ratModIntNTorsion f.natDegree := by
    intro i
    rw [hdegree]
    exact hx i
  let xt : ι →₀ ratModIntNTorsion f.natDegree :=
    { toFun := fun i ↦ ⟨x i, hx' i⟩
      support := x.support
      mem_support_toFun := by intro i; simp }
  let z := Finsupp.mapRange.addMonoidHom e.symm.toAddMonoidHom xt
  refine ⟨z, ?_⟩
  intro i
  change (((e (e.symm (xt i)) : ratModIntNTorsion f.natDegree)) : RatModInt) = x i
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- A reciprocal finite-support invariant profile is realized in one finite unramified `H²`
layer with product-one standard phase. -/
def NonarchimedeanLocalFiniteUnramifiedContinuousH2RealizesReciprocalProfile
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {ι : Type*} (x : ι →₀ RatModInt) : Prop :=
  ∃ (f : Polynomial 𝒪[K]) (g : Polynomial 𝓀[K])
      (hf : f.Monic) (hgmonic : g.Monic)
      (hg : Irreducible g) (hfg : f.map (Ideal.Quotient.mk 𝓂[K]) = g),
    let e :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
        K f hf g hgmonic hfg hg
    let hn := nonarchimedeanLocalFieldAdjoinRoot_natDegree_ne_zero K f hf g hfg hg
    ∃ z : ι →₀ _,
      (∀ i, ((e (z i) : ratModIntNTorsion f.natDegree) : RatModInt) = x i) ∧
      z.prod (fun _ w ↦ ratModIntNTorsionStdAddChar f.natDegree hn (e w)) = 1

/-- Every zero-sum finite `ℚ/ℤ` profile has a simultaneous finite unramified local `H²`
realization whose standard phases multiply to one. -/
theorem nonarchimedeanLocalField_zeroSum_finsuppRatModInt_realized_with_phase_product_one
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {ι : Type*} (x : ι →₀ RatModInt)
    (hxsum : finsuppRatModIntSumAddHom ι x = 0) :
    NonarchimedeanLocalFiniteUnramifiedContinuousH2RealizesReciprocalProfile K x := by
  classical
  obtain ⟨n, hn, hx⟩ := finsupp_exists_nonzero_common_ratModIntTorsion x
  letI : NeZero n := ⟨hn⟩
  obtain ⟨f, g, hf, hgmonic, hg, hfg, hdegree, _⟩ :=
    nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree K n
  refine ⟨f, g, hf, hgmonic, hg, hfg, ?_⟩
  let e :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_continuousGaloisH2NTorsionInvariant
      K f hf g hgmonic hfg hg
  let hfn := nonarchimedeanLocalFieldAdjoinRoot_natDegree_ne_zero K f hf g hfg hg
  have hx' : ∀ i, x i ∈ ratModIntNTorsion f.natDegree := by
    intro i
    rw [hdegree]
    exact hx i
  let xt : ι →₀ ratModIntNTorsion f.natDegree :=
    { toFun := fun i ↦ ⟨x i, hx' i⟩
      support := x.support
      mem_support_toFun := by intro i; simp }
  let z := Finsupp.mapRange.addMonoidHom e.symm.toAddMonoidHom xt
  refine ⟨z, ?_, ?_⟩
  · intro i
    change (((e (e.symm (xt i)) : ratModIntNTorsion f.natDegree)) : RatModInt) = x i
    rw [AddEquiv.apply_symm_apply]
    rfl
  · calc
      z.prod (fun _ w ↦ ratModIntNTorsionStdAddChar f.natDegree hfn (e w)) =
          xt.prod (fun _ t ↦
            ratModIntNTorsionStdAddChar f.natDegree hfn (e (e.symm t))) := by
        change (Finsupp.mapRange e.symm e.symm.map_zero xt).prod _ = _
        rw [Finsupp.prod_mapRange_index]
        intro i
        rw [map_zero]
        exact (ratModIntNTorsionStdAddChar f.natDegree hfn).map_zero_eq_one
      _ = xt.prod (fun _ t ↦ ratModIntNTorsionStdAddChar f.natDegree hfn t) := by
        apply Finsupp.prod_congr
        intro i hi
        rw [AddEquiv.apply_symm_apply]
      _ = xt.prod (fun _ t ↦ ratModIntStdAddChar (t : RatModInt)) :=
        (finsuppRatModIntNTorsion_global_character_product_eq_finite
          f.natDegree hfn xt).symm
      _ = x.prod (fun _ t ↦ ratModIntStdAddChar t) := by rfl
      _ = 1 := (finsuppRatModIntStdAddChar_product_eq_one_iff_sum_eq_zero ι x).2 hxsum

end

end GaloisForLFunctions.HTGeometry.ABHN
