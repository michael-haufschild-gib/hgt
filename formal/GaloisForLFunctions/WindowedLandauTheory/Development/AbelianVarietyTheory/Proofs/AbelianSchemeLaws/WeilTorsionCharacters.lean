import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilPairingRadical
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.FiniteTorsionDuality
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! A line bundle with trivial translation kernel gives a perfect Weil pairing
on torsion prime to the field characteristic. -/

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

/-- The difference between the translated bundle and the original bundle. -/
noncomputable def translDiff {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)
    {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(translPt A x).left, (snd T A).left] ![1, -1]

/-- A line bundle has trivial translation kernel if local generation of its
translation difference over an affine test scheme forces the translating point to be the identity. -/
def KTriv {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (.of R) ⟶ S) (x : Over.mk t ⟶ A),
    (∀ p : Spec (.of R), ∃ U : (Spec (.of R)).Opens, p ∈ U ∧
      ∃ s : ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ U).ι).Gen, s.IsGen) →
    x = 1

end ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.CommPairing

open ReciprocityTheory.ChartRestriction.G.Out
open GrpTangent (mulN comp_mulN finiteEtaleSurjective_mulN)

attribute [local instance] Over.cartesianMonoidalCategory

private theorem finite_torsion_points {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] [LocallyOfFiniteType A.hom]
    (n : ℕ) [IsFinite (mulN A n).left] :
    Finite {x : 𝟙_ (Over (Spec (.of K))) ⟶ A // x ^ n = 1} := by
  let p := IsLocalRing.closedPoint K
  let o : A.left := (1 : 𝟙_ (Over (Spec (.of K))) ⟶ A).left p
  have hfib := (mulN A n).left.finite_preimage_singleton o
  letI : Finite ((mulN A n).left ⁻¹' {o}) := hfib.to_subtype
  refine Finite.of_injective (β := (mulN A n).left ⁻¹' {o}) (fun x => ⟨x.1.left p, ?_⟩) ?_
  · exact congrArg (fun v : 𝟙_ (Over (Spec (.of K))) ⟶ A => v.left p)
      ((comp_mulN x.1 n).trans x.2)
  · intro x y hxy
    refine Subtype.ext (Over.OverMorphism.ext ?_)
    exact ext_of_apply_closedPoint_eq A.hom (Over.w x.1) (Over.w y.1) (congrArg Subtype.val hxy)

/-- A torsion point in the radical of the Weil pairing is the identity
when the line bundle has trivial translation kernel. -/
theorem eq_one_of_trivial_weil {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (n : ℕ) (hn : (n : K) ≠ 0) (x : 𝟙_ (Over (Spec (.of K))) ⟶ A) (hx : x ^ n = 1)
    (hpair : ∀ (y : 𝟙_ (Over (Spec (.of K))) ⟶ A), y ^ n = 1 → WeilIs A L (n : ℤ) x y 1) :
    x = 1 := by
  let S := Spec (.of K)
  let T := 𝟙_ (Over S)
  let f : Fin 2 → (A.left ⟶ A.left) := ![((toUnit A ≫ x) * 𝟙 A).left, 𝟙 A.left]
  let g : Fin 2 → ((T ⊗ A).left ⟶ A.left) := ![(translPt A x).left, (snd T A).left]
  let d : Fin 2 → ℤ := ![1, -1]
  let p : T ⊗ A ⟶ A := snd T A
  obtain ⟨v, hv⟩ := exists_gen_translation_of_trivial_weil hA hL hAmp n hn x hx hpair
  have he (i : Fin 2) : p.left ≫ f i = g i := by
    fin_cases i
    · change (p ≫ ((toUnit A ≫ x) * 𝟙 A)).left = (translPt A x).left
      refine congrArg Over.Hom.left ((MonObj.comp_mul _ _ _).trans ?_)
      exact congrArg₂ (· * ·) ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ x) (toUnit_unique (p ≫ toUnit A) (fst T A)))) (Category.comp_id p)
    · exact Category.comp_id p.left
  obtain ⟨u, hu, -⟩ := exists_gen_of_formEq hL (g := g) (d := d)
    (fun U _ c => Finset.prod_congr rfl fun i _ => congrArg (fun a => c a ^ d i) (he i))
    (LB.pullGen L f d v p.left) (hv.pullGen f d p.left)
  refine hK K (𝟙 S) x fun _ => ⟨⊤, trivial, ?_⟩
  let r := ((fst T A).left ⁻¹ᵁ (⊤ : S.Opens)).ι
  exact (AbLaw.Cube.trivial_pull_linComb L hL g d r).2 ⟨_, hu.pullGen g d r⟩

/-- Multiplication by an invertible exponent has finitely many geometric torsion points. -/
theorem finite_prime_to_char_torsion {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] (hA : IsAbelianScheme A)
    (n : ℕ) (hn : (n : K) ≠ 0) :
    Finite {x : 𝟙_ (Over (Spec (.of K))) ⟶ A // x ^ n = 1} := by
  letI := hA.comm
  letI := hA.smooth
  letI := hA.proper
  letI := hA.geomConnected
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  have hunit : IsUnit (n : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using (Ne.isUnit hn).map e.toRingHom
  letI : IsFinite (mulN A n).left := (finiteEtaleSurjective_mulN A hunit).1
  exact finite_torsion_points (A := A) n

/-- The global section ring of the spectrum of an algebraically closed field
has enough roots of unity for each invertible exponent. -/
theorem spec_hasEnoughRootsOfUnity (K : Type) [Field K] [IsAlgClosed K]
    (n : ℕ) (hn : (n : K) ≠ 0) : HasEnoughRootsOfUnity Γ(Spec (.of K), ⊤) n := by
  letI : NeZero (n : K) := ⟨hn⟩
  letI : NeZero n := .of_neZero_natCast K
  let e : K ≃+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm
  letI : HasEnoughRootsOfUnity K n := inferInstance
  exact MulEquiv.hasEnoughRootsOfUnity (e.toMulEquiv.restrictRootsOfUnity n)

/-- Every character of the prime-to-characteristic torsion group is pairing
with a unique torsion point when the line bundle has trivial translation kernel. -/
theorem existsUnique_weil_character {K : Type} [Field K] [IsAlgClosed K]
    {A : Over (Spec (.of K))} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (n : ℕ) (hn : (n : K) ≠ 0)
    (χ : {x : 𝟙_ (Over (Spec (.of K))) ⟶ A // x ^ n = 1} → Γ(Spec (.of K), ⊤)ˣ)
    (hχ : ∀ x y, χ ⟨x.1 * y.1, by
      letI := hA.comm
      exact (mul_pow x.1 y.1 n).trans
        ((congrArg₂ (· * ·) x.2 y.2).trans (_root_.one_mul _))⟩ = χ x * χ y) :
    ∃! b : 𝟙_ (Over (Spec (.of K))) ⟶ A, b ^ n = 1 ∧
      ∀ x : {x : 𝟙_ (Over (Spec (.of K))) ⟶ A // x ^ n = 1}, WeilIs A L (n : ℤ) x.1 b (χ x) := by
  letI := hA.comm
  letI : NeZero (n : K) := ⟨hn⟩
  letI : NeZero n := .of_neZero_natCast K
  let S := Spec (.of K)
  let T := 𝟙_ (Over S)
  let R := Γ(S, ⊤)
  let H := T ⟶ A
  letI : CommGroup H := inferInstanceAs (CommGroup (T ⟶ A))
  letI : CommMonoid R := inferInstanceAs (CommMonoid Γ(S, ⊤))
  letI : HasEnoughRootsOfUnity R n := spec_hasEnoughRootsOfUnity K n hn
  letI : Finite {x : H // x ^ n = 1} := finite_prime_to_char_torsion hA n hn
  let W : H → H → Rˣ → Prop := fun x y c => WeilIs A L (T := T) (n : ℤ) x y c
  have hex (x y : H) := existsUnique_weilIs_of_pow_eq_one (T := T) hA hL hAmp x y n
  have hmul (x x' y : H) (c c' : Rˣ) (h : W x y c) (h' : W x' y c') : W (x * x') y (c * c') :=
    weilIs_mul_left_of_local_lifts (T := T) hA hL h h'
  have hskew (x y : H) (c : Rˣ) (h : W x y c) : W y x c⁻¹ :=
    weilIs_swap_of_local_lifts (T := T) hA hL h
  have hnd (x : H) (hx : x ^ n = 1) (h : ∀ y : H, y ^ n = 1 → W x y 1) : x = 1 :=
    eq_one_of_trivial_weil hA hL hAmp hK n hn x hx h
  exact existsUnique_pairing_eq_character (H := H) (M := R) n W hex hmul hskew hnd χ hχ

end GlobalTheory.CommPairing
