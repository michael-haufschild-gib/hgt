import GaloisForLFunctions.HTGeometry.ValuationSubringExtension
import Mathlib

/-!
# Gauss extension of valuation subrings

An arbitrary valuation subring extends across one free transcendental adjunction with exact
contraction and with the new generator a valuation unit.  The construction localizes the
polynomial ring over the source valuation ring at the kernel of coefficientwise residue
reduction, then applies Krull domination.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

set_option maxHeartbeats 1000000

private noncomputable def gaussResiduePolynomialMap
    {E : Type u} [Field E] (A : ValuationSubring E) :
    Polynomial A →+* Polynomial (IsLocalRing.ResidueField A) :=
  Polynomial.mapRingHom (IsLocalRing.residue A)

private noncomputable def gaussResiduePrime
    {E : Type u} [Field E] (A : ValuationSubring E) : Ideal (Polynomial A) :=
  RingHom.ker (gaussResiduePolynomialMap A)

private noncomputable instance gaussResiduePrime_isPrime
    {E : Type u} [Field E] (A : ValuationSubring E) :
    (gaussResiduePrime A).IsPrime :=
  RingHom.ker_isPrime (gaussResiduePolynomialMap A)

private abbrev gaussLocalRing
    {E : Type u} [Field E] (A : ValuationSubring E) : Type u :=
  @Localization.AtPrime (Polynomial A) _ (gaussResiduePrime A)
    (gaussResiduePrime_isPrime A)

private noncomputable instance (priority := high) gaussLocalRingSemiring
    {E : Type u} [Field E] (A : ValuationSubring E) :
    Semiring (gaussLocalRing A) :=
  (inferInstance : CommRing (gaussLocalRing A)).toSemiring

private noncomputable def gaussCoefficientToLocal
    {E : Type u} [Field E] (A : ValuationSubring E) :
    A →+* gaussLocalRing A :=
  (algebraMap (Polynomial A) (gaussLocalRing A)).comp Polynomial.C

private noncomputable instance gaussCoefficientToLocal_isLocalHom
    {E : Type u} [Field E] (A : ValuationSubring E) :
    IsLocalHom (gaussCoefficientToLocal A) := by
  refine ⟨fun a ha => ?_⟩
  have hcompl :
      Polynomial.C a ∈ (gaussResiduePrime A).primeCompl :=
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (gaussLocalRing A) (gaussResiduePrime A) (Polynomial.C a)).mp ha
  have hres : IsLocalRing.residue A a ≠ 0 := by
    intro hzero
    apply hcompl
    change gaussResiduePolynomialMap A (Polynomial.C a) = 0
    simp [gaussResiduePolynomialMap, hzero]
  by_contra hnotunit
  exact hres ((IsLocalRing.residue_eq_zero_iff a).2
    ((IsLocalRing.mem_maximalIdeal a).2 hnotunit))

private noncomputable def gaussPolynomialToRatFunc
    {E : Type u} [Field E] (A : ValuationSubring E) :
    Polynomial A →+* RatFunc E :=
  (algebraMap (Polynomial E) (RatFunc E)).comp
    (Polynomial.mapRingHom A.subtype)

private theorem gaussPolynomialToRatFunc_ne_zero
    {E : Type u} [Field E] (A : ValuationSubring E)
    (p : Polynomial A) (hp : p ≠ 0) :
    gaussPolynomialToRatFunc A p ≠ 0 := by
  intro hzero
  have hmap : Polynomial.map A.subtype p = 0 :=
    (RatFunc.algebraMap_injective E) (by
      simpa [gaussPolynomialToRatFunc] using hzero)
  have hsubtype : Function.Injective A.subtype := by
    intro x y hxy
    exact Subtype.ext hxy
  apply hp
  apply Polynomial.map_injective A.subtype hsubtype
  simpa using hmap

private noncomputable def gaussLocalToRatFunc
    {E : Type u} [Field E] (A : ValuationSubring E) :
    gaussLocalRing A →+* RatFunc E :=
  IsLocalization.lift (g := gaussPolynomialToRatFunc A)
    (fun y : (gaussResiduePrime A).primeCompl =>
    isUnit_iff_ne_zero.mpr
      (gaussPolynomialToRatFunc_ne_zero A y
        (by
          intro hy
          have hyP : (y : Polynomial A) ∈ gaussResiduePrime A := by
            rw [hy]
            exact (gaussResiduePrime A).zero_mem
          have hyNot : (y : Polynomial A) ∉ gaussResiduePrime A := y.2
          exact hyNot hyP)))

private theorem gaussLocalToRatFunc_coefficient
    {E : Type u} [Field E] (A : ValuationSubring E) (a : A) :
    gaussLocalToRatFunc A (gaussCoefficientToLocal A a) =
      algebraMap E (RatFunc E) (a : E) := by
  simp [gaussLocalToRatFunc, gaussCoefficientToLocal,
    gaussPolynomialToRatFunc]

private theorem gaussLocalToRatFunc_X
    {E : Type u} [Field E] (A : ValuationSubring E) :
    gaussLocalToRatFunc A
        (algebraMap (Polynomial A) (gaussLocalRing A) Polynomial.X) =
      RatFunc.X := by
  simp [gaussLocalToRatFunc, gaussPolynomialToRatFunc]

/-- Exact Gauss extension of an arbitrary valuation ring to one rational variable. -/
theorem exists_ratFunc_valuationSubring_gaussExtension
    {E : Type u} [Field E] (A : ValuationSubring E) :
    ∃ B : ValuationSubring (RatFunc E),
      B.comap (algebraMap E (RatFunc E)) = A ∧
      RatFunc.X ∈ B ∧ RatFunc.X⁻¹ ∈ B := by
  obtain ⟨B, hmem, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (gaussLocalToRatFunc A)
  have hcoeff : ∀ a : A, algebraMap E (RatFunc E) (a : E) ∈ B := by
    intro a
    rw [← gaussLocalToRatFunc_coefficient A a]
    exact hmem (gaussCoefficientToLocal A a)
  have hEA : ∀ x : E, algebraMap E (RatFunc E) x ∈ B ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have hxinvA : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hnot
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        exact hnot A.zero_mem
      have hinvMem : algebraMap E (RatFunc E) x⁻¹ ∈ B :=
        hcoeff ⟨x⁻¹, hxinvA⟩
      have hunit : IsUnit
          (⟨algebraMap E (RatFunc E) x⁻¹, hinvMem⟩ : B.toSubring) := by
        refine isUnit_iff_exists_inv.mpr
          ⟨⟨algebraMap E (RatFunc E) x, hx⟩, ?_⟩
        apply Subtype.ext
        simp [hx0]
      have hcLocal : IsLocalHom
          (((gaussLocalToRatFunc A).codRestrict B.toSubring hmem).comp
            (gaussCoefficientToLocal A)) := inferInstance
      have hsourceUnit : IsUnit (⟨x⁻¹, hxinvA⟩ : A) := by
        apply hcLocal.map_nonunit (⟨x⁻¹, hxinvA⟩ : A)
        convert hunit using 1
        apply Subtype.ext
        exact gaussLocalToRatFunc_coefficient A ⟨x⁻¹, hxinvA⟩
      obtain ⟨u, hu⟩ := hsourceUnit
      have huE : ((u : A) : E) = x⁻¹ := congrArg Subtype.val hu
      have huInvE : ((↑(u⁻¹) : A) : E) = x := by
        change A.subtype (↑(u⁻¹) : A) = x
        rw [map_units_inv A.subtype u]
        have huE' : A.subtype (u : A) = x⁻¹ := huE
        rw [huE', inv_inv]
      apply hnot
      rw [← huInvE]
      exact (↑(u⁻¹) : A).2
    · intro hx
      exact hcoeff ⟨x, hx⟩
  have hX : RatFunc.X ∈ B := by
    rw [← gaussLocalToRatFunc_X A]
    exact hmem (algebraMap (Polynomial A) (gaussLocalRing A) Polynomial.X)
  have hXunit : IsUnit
      (algebraMap (Polynomial A) (gaussLocalRing A) Polynomial.X) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff
      (gaussLocalRing A) (gaussResiduePrime A) Polynomial.X).2
    intro hXker
    change gaussResiduePolynomialMap A Polynomial.X = 0 at hXker
    simpa [gaussResiduePolynomialMap] using hXker
  obtain ⟨u, hu⟩ := hXunit
  have hXinvLocal :
      gaussLocalToRatFunc A (↑(u⁻¹) : gaussLocalRing A) ∈ B :=
    hmem (↑(u⁻¹) : gaussLocalRing A)
  have hXinv : RatFunc.X⁻¹ ∈ B := by
    have huMap : gaussLocalToRatFunc A (u : gaussLocalRing A) = RatFunc.X := by
      rw [hu]
      exact gaussLocalToRatFunc_X A
    have hEq : gaussLocalToRatFunc A (↑(u⁻¹) : gaussLocalRing A) =
        RatFunc.X⁻¹ := by
      rw [map_units_inv (gaussLocalToRatFunc A) u, huMap]
    rw [← hEq]
    exact hXinvLocal
  refine ⟨B, ?_, hX, hXinv⟩
  apply SetLike.ext
  intro x
  exact hEA x

/-- A valuation extends across a free transcendental adjunction while remaining trivial on the
new generator and contracting exactly to the original valuation. -/
theorem exists_valuationSubring_extension_transcendental_unit
    {E K : Type u} [Field E] [Field K] [Algebra E K]
    (A : ValuationSubring E) (x : K) (hx : Transcendental E x) :
    ∃ B : ValuationSubring K,
      B.comap (algebraMap E K) = A ∧ x ∈ B ∧ x⁻¹ ∈ B := by
  obtain ⟨A₀, hA₀, hX, hXinv⟩ :=
    exists_ratFunc_valuationSubring_gaussExtension A
  let L : IntermediateField E K := IntermediateField.adjoin E {x}
  let e : RatFunc E ≃ₐ[E] L :=
    RatFunc.algEquivOfTranscendental x hx
  let f : RatFunc E →+* K :=
    L.val.toRingHom.comp e.toRingHom
  obtain ⟨B, hB⟩ := exists_valuationSubring_extension_comap_eq A₀ f
  have hfC (c : E) :
      f (algebraMap E (RatFunc E) c) = algebraMap E K c := by
    change ((e (algebraMap E (RatFunc E) c) : L) : K) =
      algebraMap E K c
    rw [e.commutes]
    rfl
  have hfX : f RatFunc.X = x := by
    exact RatFunc.algEquivOfTranscendental_X x hx
  have hfXinv : f RatFunc.X⁻¹ = x⁻¹ := by
    calc
      f (RatFunc.X⁻¹) = (f RatFunc.X)⁻¹ := map_inv₀ f RatFunc.X
      _ = x⁻¹ := by rw [hfX]
  have hcomap : B.comap (algebraMap E K) = A := by
    apply SetLike.ext
    intro c
    change algebraMap E K c ∈ B ↔ c ∈ A
    rw [← hfC c]
    change c ∈ (B.comap f).comap (algebraMap E (RatFunc E)) ↔ c ∈ A
    rw [hB, hA₀]
  have hxB : x ∈ B := by
    rw [← hfX]
    change RatFunc.X ∈ B.comap f
    rw [hB]
    exact hX
  have hxinvB : x⁻¹ ∈ B := by
    rw [← hfXinv]
    change RatFunc.X⁻¹ ∈ B.comap f
    rw [hB]
    exact hXinv
  exact ⟨B, hcomap, hxB, hxinvB⟩

/-- A valuation extends across a finite algebraically independent family while remaining trivial
on every generator and contracting exactly to the source valuation. -/
theorem exists_valuationSubring_extension_fin_algebraicIndependent_units
    {E K : Type u} [Field E] [Field K] [Algebra E K]
    {n : ℕ} (A : ValuationSubring E) (x : Fin n → K)
    (hx : AlgebraicIndependent E x) :
    ∃ B : ValuationSubring K,
      B.comap (algebraMap E K) = A ∧
      ∀ i, x i ∈ B ∧ (x i)⁻¹ ∈ B := by
  induction n generalizing K with
  | zero =>
      obtain ⟨B, hB⟩ :=
        exists_valuationSubring_extension_comap_eq A (algebraMap E K)
      exact ⟨B, hB, fun i => Fin.elim0 i⟩
  | succ n ih =>
      let s : Set (Fin (n + 1)) := Set.range Fin.castSucc
      let L : IntermediateField E K := IntermediateField.adjoin E (x '' s)
      letI : IsScalarTower E L K :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      let y : Fin n → L := fun i =>
        ⟨x i.castSucc, IntermediateField.subset_adjoin E _
          ⟨i.castSucc, Set.mem_range_self i, rfl⟩⟩
      have hy : AlgebraicIndependent E y := by
        apply AlgebraicIndependent.of_comp L.val
        simpa [y, Function.comp_def] using
          hx.comp Fin.castSucc (Fin.castSucc_injective n)
      obtain ⟨A_L, hA_L, hyUnits⟩ := ih y hy
      have hlast : (Fin.last n : Fin (n + 1)) ∉ s := by
        rintro ⟨i, hi⟩
        exact (Fin.castSucc_lt_last i).ne hi
      have ht : Transcendental L (x (Fin.last n)) := by
        change Transcendental (IntermediateField.adjoin E (x '' s))
          (x (Fin.last n))
        rw [IntermediateField.transcendental_adjoin_iff]
        exact hx.transcendental_adjoin hlast
      obtain ⟨B, hB, hlastB, hlastInvB⟩ :=
        exists_valuationSubring_extension_transcendental_unit
          A_L (x (Fin.last n)) ht
      have hcomap : B.comap (algebraMap E K) = A := by
        rw [← hA_L, ← hB]
        apply SetLike.ext
        intro z
        change algebraMap E K z ∈ B ↔
          algebraMap L K (algebraMap E L z) ∈ B
        rw [IsScalarTower.algebraMap_apply E L K]
      refine ⟨B, hcomap, fun i => ?_⟩
      by_cases hi : i = Fin.last n
      · subst i
        exact ⟨hlastB, hlastInvB⟩
      · let j : Fin n := ⟨i, by
          have hiLe : i.val ≤ n := Nat.le_of_lt_succ i.isLt
          exact lt_of_le_of_ne hiLe (by
            intro hin
            apply hi
            apply Fin.ext
            simpa using hin)⟩
        have hji : j.castSucc = i := Fin.ext rfl
        obtain ⟨hyj, hyjInv⟩ := hyUnits j
        have hyjB : algebraMap L K (y j) ∈ B := by
          change y j ∈ B.comap (algebraMap L K)
          rw [hB]
          exact hyj
        have hyjInvB : (algebraMap L K (y j))⁻¹ ∈ B := by
          rw [← map_inv₀]
          change (y j)⁻¹ ∈ B.comap (algebraMap L K)
          rw [hB]
          exact hyjInv
        simpa [y, hji] using And.intro hyjB hyjInvB

private theorem polynomialMap_nonZeroDivisors
    {S E : Type u} [Field S] [Field E] (f : S →+* E) :
    nonZeroDivisors (Polynomial S) ≤
      Submonoid.comap (Polynomial.mapRingHom f) (nonZeroDivisors (Polynomial E)) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (Polynomial.map_injective f f.injective)

/-- Coefficient extension from a rational function field over `S` to one over `E`. -/
noncomputable def ratFuncCoefficientExtension
    {S E : Type u} [Field S] [Field E] (f : S →+* E) :
    RatFunc S →+* RatFunc E :=
  RatFunc.mapRingHom (Polynomial.mapRingHom f)
    (polynomialMap_nonZeroDivisors f)

@[simp]
theorem ratFuncCoefficientExtension_algebraMap
    {S E : Type u} [Field S] [Field E] (f : S →+* E) (s : S) :
    ratFuncCoefficientExtension f (algebraMap S (RatFunc S) s) =
      algebraMap E (RatFunc E) (f s) := by
  change RatFunc.map (Polynomial.mapRingHom f) (polynomialMap_nonZeroDivisors f) _ = _
  rw [show algebraMap S (RatFunc S) s =
    algebraMap (Polynomial S) (RatFunc S) (Polynomial.C s) by simp]
  rw [← div_one (algebraMap (Polynomial S) (RatFunc S) (Polynomial.C s))]
  have hone : (1 : RatFunc S) =
      algebraMap (Polynomial S) (RatFunc S) (1 : Polynomial S) := by simp
  rw [hone]
  rw [RatFunc.map_apply_div]
  simp

@[simp]
theorem ratFuncCoefficientExtension_X
    {S E : Type u} [Field S] [Field E] (f : S →+* E) :
    ratFuncCoefficientExtension f RatFunc.X = RatFunc.X := by
  change RatFunc.map (Polynomial.mapRingHom f) (polynomialMap_nonZeroDivisors f) _ = _
  rw [← RatFunc.algebraMap_X]
  rw [← div_one (algebraMap (Polynomial S) (RatFunc S) Polynomial.X)]
  have hone : (1 : RatFunc S) =
      algebraMap (Polynomial S) (RatFunc S) (1 : Polynomial S) := by simp
  rw [hone, RatFunc.map_apply_div]
  simp

/-- The Gauss extension preserves a trivial valuation on an embedded coefficient subfield after
adjoining the rational variable: every rational function over that subfield remains integral. -/
theorem exists_ratFunc_valuationSubring_gaussExtension_trivial_subfield
    {S E : Type u} [Field S] [Field E] [Algebra S E]
    (A : ValuationSubring E)
    (htriv : A.comap (algebraMap S E) = ⊤) :
    ∃ B : ValuationSubring (RatFunc E),
      B.comap (algebraMap E (RatFunc E)) = A ∧
      B.comap (ratFuncCoefficientExtension (algebraMap S E)) = ⊤ := by
  obtain ⟨B, hmem, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (gaussLocalToRatFunc A)
  have hcoeff : ∀ a : A, algebraMap E (RatFunc E) (a : E) ∈ B := by
    intro a
    rw [← gaussLocalToRatFunc_coefficient A a]
    exact hmem (gaussCoefficientToLocal A a)
  have hEA : ∀ x : E, algebraMap E (RatFunc E) x ∈ B ↔ x ∈ A := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have hxinvA : x⁻¹ ∈ A := (A.mem_or_inv_mem x).resolve_left hnot
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        exact hnot A.zero_mem
      have hinvMem : algebraMap E (RatFunc E) x⁻¹ ∈ B :=
        hcoeff ⟨x⁻¹, hxinvA⟩
      have hunit : IsUnit
          (⟨algebraMap E (RatFunc E) x⁻¹, hinvMem⟩ : B.toSubring) := by
        refine isUnit_iff_exists_inv.mpr
          ⟨⟨algebraMap E (RatFunc E) x, hx⟩, ?_⟩
        apply Subtype.ext
        simp [hx0]
      have hcLocal : IsLocalHom
          (((gaussLocalToRatFunc A).codRestrict B.toSubring hmem).comp
            (gaussCoefficientToLocal A)) := inferInstance
      have hsourceUnit : IsUnit (⟨x⁻¹, hxinvA⟩ : A) := by
        apply hcLocal.map_nonunit (⟨x⁻¹, hxinvA⟩ : A)
        convert hunit using 1
        apply Subtype.ext
        exact gaussLocalToRatFunc_coefficient A ⟨x⁻¹, hxinvA⟩
      obtain ⟨v, hv⟩ := hsourceUnit
      have hvE : ((v : A) : E) = x⁻¹ := congrArg Subtype.val hv
      have hvInvE : ((↑(v⁻¹) : A) : E) = x := by
        change A.subtype (↑(v⁻¹) : A) = x
        rw [map_units_inv A.subtype v]
        simpa using congrArg Inv.inv hvE
      apply hnot
      rw [← hvInvE]
      exact (↑(v⁻¹) : A).2
    · intro hx
      exact hcoeff ⟨x, hx⟩
  have hSEmem : ∀ s : S, algebraMap S E s ∈ A := by
    intro s
    change s ∈ A.comap (algebraMap S E)
    rw [htriv]
    trivial
  let fA : S →+* A := (algebraMap S E).codRestrict A.toSubring hSEmem
  let resSE : S →+* IsLocalRing.ResidueField A :=
    valuationSubringResidueEmbedding A (algebraMap S E) hSEmem
  have hresSE : Function.Injective resSE :=
    valuationSubringResidueEmbedding_injective A (algebraMap S E) hSEmem
  have hpolyUnit : ∀ p : Polynomial S, p ≠ 0 →
      IsUnit (⟨gaussLocalToRatFunc A
          (algebraMap (Polynomial A) (gaussLocalRing A) (p.map fA)),
        by
          exact hmem (algebraMap (Polynomial A) (gaussLocalRing A) (p.map fA))⟩ :
        B.toSubring) := by
    intro p hp
    have hpRes : p.map resSE ≠ 0 := by
      intro h
      apply hp
      exact (Polynomial.map_injective resSE hresSE) (by simpa using h)
    have hpNotKer : p.map fA ∈ (gaussResiduePrime A).primeCompl := by
      intro hpKer
      apply hpRes
      change gaussResiduePolynomialMap A (p.map fA) = 0 at hpKer
      simpa [gaussResiduePolynomialMap, resSE,
        valuationSubringResidueEmbedding, fA, Polynomial.map_map] using hpKer
    have hpLocal : IsUnit
        (algebraMap (Polynomial A) (gaussLocalRing A) (p.map fA)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff
        (gaussLocalRing A) (gaussResiduePrime A) (p.map fA)).2 hpNotKer
    exact hpLocal.map
      ((gaussLocalToRatFunc A).codRestrict B.toSubring hmem)
  let fPoly : Polynomial S →+* Polynomial E :=
    Polynomial.mapRingHom (algebraMap S E)
  let hfPoly : nonZeroDivisors (Polynomial S) ≤
      Submonoid.comap fPoly (nonZeroDivisors (Polynomial E)) := by
    intro p hp
    change Polynomial.map (algebraMap S E) p ∈ nonZeroDivisors (Polynomial E)
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h
    apply hp
    exact (Polynomial.map_injective (algebraMap S E)
      (RingHom.injective (algebraMap S E))) (by simpa using h)
  let fRat : RatFunc S →+* RatFunc E := RatFunc.mapRingHom fPoly hfPoly
  have hfRat : fRat = ratFuncCoefficientExtension (algebraMap S E) := by
    rfl
  have hpolyEq (p : Polynomial S) :
      fRat (algebraMap (Polynomial S) (RatFunc S) p) =
        gaussLocalToRatFunc A
          (algebraMap (Polynomial A) (gaussLocalRing A) (p.map fA)) := by
    rw [← div_one (algebraMap (Polynomial S) (RatFunc S) p)]
    change RatFunc.map fPoly hfPoly
        (algebraMap (Polynomial S) (RatFunc S) p / 1) = _
    have hone : (1 : RatFunc S) =
        algebraMap (Polynomial S) (RatFunc S) (1 : Polynomial S) := by simp
    rw [hone]
    rw [RatFunc.map_apply_div]
    simp [fPoly, fA, gaussLocalToRatFunc,
      gaussPolynomialToRatFunc, Polynomial.map_map]
    ext n
    simp [fA]
  have hRat : ∀ y : RatFunc S, fRat y ∈ B := by
    intro y
    induction y using RatFunc.induction_on with
    | _ p q hq =>
      rw [map_div₀, hpolyEq p, hpolyEq q]
      have hpMem : gaussLocalToRatFunc A
          (algebraMap (Polynomial A) (gaussLocalRing A) (p.map fA)) ∈ B :=
        hmem _
      have hqUnit := hpolyUnit q hq
      obtain ⟨uq, huq⟩ := hqUnit
      have hqInvMem : (gaussLocalToRatFunc A
          (algebraMap (Polynomial A) (gaussLocalRing A) (q.map fA)))⁻¹ ∈ B := by
        have huqVal := congrArg Subtype.val huq
        have huqInvVal : ((↑(uq⁻¹) : B.toSubring) : RatFunc E) =
            (gaussLocalToRatFunc A
              (algebraMap (Polynomial A) (gaussLocalRing A) (q.map fA)))⁻¹ := by
          change B.toSubring.subtype (↑(uq⁻¹) : B.toSubring) = _
          rw [map_units_inv B.toSubring.subtype uq]
          exact congrArg Inv.inv huqVal
        rw [← huqInvVal]
        exact (↑(uq⁻¹) : B.toSubring).2
      simpa [div_eq_mul_inv] using B.toSubring.mul_mem hpMem hqInvMem
  refine ⟨B, ?_, ?_⟩
  · apply SetLike.ext
    intro x
    exact hEA x
  · rw [← hfRat]
    apply SetLike.ext
    intro y
    constructor
    · intro _
      trivial
    · intro _
      exact hRat y

private theorem ratFuncRingHom_ext
    {S L : Type u} [Field S] [Field L] {f g : RatFunc S →+* L}
    (hS : ∀ s : S, f (algebraMap S (RatFunc S) s) =
      g (algebraMap S (RatFunc S) s))
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  apply IsFractionRing.ringHom_ext (A := Polynomial S)
  intro p
  have hp : f.comp (algebraMap (Polynomial S) (RatFunc S)) =
      g.comp (algebraMap (Polynomial S) (RatFunc S)) := by
    apply Polynomial.ringHom_ext
    · intro s
      simpa using hS s
    · simpa [RatFunc.algebraMap_X] using hX
  exact DFunLike.congr_fun hp p

/-- A valuation that is trivial on `S` extends across one element transcendental over `E`,
contracts exactly to its original valuation on `E`, and is trivial on the full simple rational
field generated by that element over `S`. -/
theorem exists_valuationSubring_extension_transcendental_trivial_adjoin
    {S E K : Type u} [Field S] [Field E] [Field K]
    [Algebra S E] [Algebra E K] [Algebra S K] [IsScalarTower S E K]
    (A : ValuationSubring E)
    (htriv : A.comap (algebraMap S E) = ⊤)
    (x : K) (hx : Transcendental E x) :
    ∃ B : ValuationSubring K,
      B.comap (algebraMap E K) = A ∧
      B.comap (IntermediateField.adjoin S ({x} : Set K)).val.toRingHom = ⊤ := by
  obtain ⟨A₀, hA₀, hSrat⟩ :=
    exists_ratFunc_valuationSubring_gaussExtension_trivial_subfield A htriv
  let L : IntermediateField E K := IntermediateField.adjoin E {x}
  let eE : RatFunc E ≃ₐ[E] L := RatFunc.algEquivOfTranscendental x hx
  let fE : RatFunc E →+* K := L.val.toRingHom.comp eE.toRingHom
  obtain ⟨B, hB⟩ := exists_valuationSubring_extension_comap_eq A₀ fE
  have hfE_const (c : E) :
      fE (algebraMap E (RatFunc E) c) = algebraMap E K c := by
    change ((eE (algebraMap E (RatFunc E) c) : L) : K) = algebraMap E K c
    rw [eE.commutes]
    rfl
  have hfE_X : fE RatFunc.X = x :=
    RatFunc.algEquivOfTranscendental_X x hx
  have hcomap : B.comap (algebraMap E K) = A := by
    apply SetLike.ext
    intro c
    change algebraMap E K c ∈ B ↔ c ∈ A
    rw [← hfE_const c]
    change c ∈ (B.comap fE).comap (algebraMap E (RatFunc E)) ↔ c ∈ A
    rw [hB, hA₀]
  have hxS : Transcendental S x :=
    hx.restrictScalars (algebraMap S E).injective
  let LS : IntermediateField S K := IntermediateField.adjoin S {x}
  let eS : RatFunc S ≃ₐ[S] LS := RatFunc.algEquivOfTranscendental x hxS
  let fS : RatFunc S →+* K := LS.val.toRingHom.comp eS.toRingHom
  have hfS_X : fS RatFunc.X = x :=
    RatFunc.algEquivOfTranscendental_X x hxS
  have hfS_const (s : S) :
      fS (algebraMap S (RatFunc S) s) = algebraMap S K s := by
    change ((eS (algebraMap S (RatFunc S) s) : LS) : K) = algebraMap S K s
    rw [eS.commutes]
    rfl
  let cSE : RatFunc S →+* RatFunc E :=
    ratFuncCoefficientExtension (algebraMap S E)
  have hcSE_const (s : S) :
      cSE (algebraMap S (RatFunc S) s) =
        algebraMap E (RatFunc E) (algebraMap S E s) := by
    exact ratFuncCoefficientExtension_algebraMap (algebraMap S E) s
  have hcSE_X : cSE RatFunc.X = RatFunc.X := by
    exact ratFuncCoefficientExtension_X (algebraMap S E)
  have hmaps : fE.comp cSE = fS := by
    apply ratFuncRingHom_ext
    · intro s
      rw [RingHom.comp_apply, hcSE_const, hfE_const, hfS_const]
      exact (IsScalarTower.algebraMap_apply S E K s).symm
    · rw [RingHom.comp_apply, hcSE_X, hfE_X, hfS_X]
  refine ⟨B, hcomap, ?_⟩
  apply SetLike.ext
  intro y
  constructor
  · intro _
    trivial
  · intro _
    let z : RatFunc S := eS.symm y
    have hzA₀ : cSE z ∈ A₀ := by
      change z ∈ A₀.comap cSE
      change z ∈ A₀.comap (ratFuncCoefficientExtension (algebraMap S E))
      rw [hSrat]
      trivial
    have hzB : fE (cSE z) ∈ B := by
      change cSE z ∈ B.comap fE
      rw [hB]
      exact hzA₀
    have hyEq : fS z = (y : K) := by
      change ((eS z : LS) : K) = (y : K)
      rw [show eS z = y by simp [z]]
    have hzMap := DFunLike.congr_fun hmaps z
    rw [RingHom.comp_apply] at hzMap
    rw [hzMap] at hzB
    change (y : K) ∈ B
    exact hyEq ▸ hzB

/-- A valuation trivial on `S` extends across a finite algebraically independent family over
`E`, contracts exactly to `E`, and remains trivial on the entire field generated by that family
over `S`. -/
theorem exists_valuationSubring_extension_fin_algebraicIndependent_trivial_adjoin
    {S E K : Type u} [Field S] [Field E] [Field K]
    [Algebra S E] [Algebra E K] [Algebra S K] [IsScalarTower S E K]
    {n : ℕ} (A : ValuationSubring E)
    (htriv : A.comap (algebraMap S E) = ⊤)
    (x : Fin n → K) (hx : AlgebraicIndependent E x) :
    ∃ B : ValuationSubring K,
      B.comap (algebraMap E K) = A ∧
      B.comap (IntermediateField.adjoin S (Set.range x)).val.toRingHom = ⊤ := by
  induction n generalizing K with
  | zero =>
      obtain ⟨B, hB⟩ :=
        exists_valuationSubring_extension_comap_eq A (algebraMap E K)
      have hSK : B.comap (algebraMap S K) = ⊤ := by
        rw [← htriv, ← hB]
        apply SetLike.ext
        intro s
        change algebraMap S K s ∈ B ↔
          algebraMap E K (algebraMap S E s) ∈ B
        rw [IsScalarTower.algebraMap_apply S E K]
      have hrange : Set.range x = (∅ : Set K) := by
        ext z
        constructor
        · rintro ⟨i, _⟩
          exact Fin.elim0 i
        · simp
      refine ⟨B, hB, ?_⟩
      rw [hrange, IntermediateField.adjoin_empty]
      apply SetLike.ext
      intro y
      constructor
      · intro _
        trivial
      · intro _
        rcases IntermediateField.mem_bot.mp y.property with ⟨s, hs⟩
        have hsB : algebraMap S K s ∈ B := by
          change s ∈ B.comap (algebraMap S K)
          rw [hSK]
          trivial
        change (y : K) ∈ B
        simpa [hs] using hsB
  | succ n ih =>
      let s : Set (Fin (n + 1)) := Set.range Fin.castSucc
      let L : IntermediateField E K := IntermediateField.adjoin E (x '' s)
      letI : IsScalarTower E L K :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      let y : Fin n → L := fun i =>
        ⟨x i.castSucc, IntermediateField.subset_adjoin E _
          ⟨i.castSucc, Set.mem_range_self i, rfl⟩⟩
      have hy : AlgebraicIndependent E y := by
        apply AlgebraicIndependent.of_comp L.val
        simpa [y, Function.comp_def] using
          hx.comp Fin.castSucc (Fin.castSucc_injective n)
      obtain ⟨A_L, hA_L, htrivPrev⟩ := ih y hy
      let T : IntermediateField S L := IntermediateField.adjoin S (Set.range y)
      have hlast : (Fin.last n : Fin (n + 1)) ∉ s := by
        rintro ⟨i, hi⟩
        exact (Fin.castSucc_lt_last i).ne hi
      have ht : Transcendental L (x (Fin.last n)) := by
        change Transcendental (IntermediateField.adjoin E (x '' s))
          (x (Fin.last n))
        rw [IntermediateField.transcendental_adjoin_iff]
        exact hx.transcendental_adjoin hlast
      obtain ⟨B, hB, htrivNext⟩ :=
        exists_valuationSubring_extension_transcendental_trivial_adjoin
          (S := T) A_L htrivPrev (x (Fin.last n)) ht
      have hcomap : B.comap (algebraMap E K) = A := by
        rw [← hA_L, ← hB]
        apply SetLike.ext
        intro z
        change algebraMap E K z ∈ B ↔
          algebraMap L K (algebraMap E L z) ∈ B
        rw [IsScalarTower.algebraMap_apply E L K]
      let G : IntermediateField T K :=
        IntermediateField.adjoin T ({x (Fin.last n)} : Set K)
      refine ⟨B, hcomap, ?_⟩
      apply SetLike.ext
      intro w
      constructor
      · intro _
        trivial
      · intro _
        have hwG : (w : K) ∈ G := by
          apply IntermediateField.adjoin_induction S
            (p := fun z _ => z ∈ G) _ _ _ _ _ w.property
          · intro z hz
            rcases hz with ⟨i, rfl⟩
            by_cases hi : i = Fin.last n
            · subst i
              exact IntermediateField.subset_adjoin T _ (Set.mem_singleton _)
            · let j : Fin n := ⟨i, by
                have hiLe : i.val ≤ n := Nat.le_of_lt_succ i.isLt
                exact lt_of_le_of_ne hiLe (by
                  intro hin
                  apply hi
                  apply Fin.ext
                  simpa using hin)⟩
              have hji : j.castSucc = i := Fin.ext rfl
              let tj : T :=
                ⟨y j, IntermediateField.subset_adjoin S _ (Set.mem_range_self j)⟩
              have htj : algebraMap T K tj ∈ G := G.algebraMap_mem tj
              have htjEq : algebraMap T K tj = x i := by
                change ((tj : T) : K) = x i
                simp [tj, y, hji]
              rw [← htjEq]
              exact htj
          · intro c
            let tc : T := algebraMap S T c
            have htc : algebraMap T K tc ∈ G := G.algebraMap_mem tc
            have htcEq : algebraMap T K tc = algebraMap S K c := by
              change ((tc : T) : K) = algebraMap S K c
              change algebraMap L K (algebraMap S L c) = algebraMap S K c
              rw [show algebraMap S L c =
                algebraMap E L (algebraMap S E c) by
                  exact IsScalarTower.algebraMap_apply S E L c]
              rw [← IsScalarTower.algebraMap_apply E L K]
              exact (IsScalarTower.algebraMap_apply S E K c).symm
            rw [← htcEq]
            exact htc
          · intro a b _ _ ha hb
            exact G.add_mem ha hb
          · intro a _ ha
            exact G.inv_mem ha
          · intro a b _ _ ha hb
            exact G.mul_mem ha hb
        have hwB : (w : K) ∈ B := by
          change (⟨w, hwG⟩ : G) ∈ B.comap G.val.toRingHom
          change (⟨w, hwG⟩ : G) ∈
            B.comap
              (IntermediateField.adjoin T
                ({x (Fin.last n)} : Set K)).val.toRingHom
          rw [htrivNext]
          trivial
        exact hwB

end

end GaloisForLFunctions.HTGeometry
