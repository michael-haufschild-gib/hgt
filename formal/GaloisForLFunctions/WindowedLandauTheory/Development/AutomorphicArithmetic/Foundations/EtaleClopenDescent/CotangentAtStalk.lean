import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectivePointRatios
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveRatioTransitions
import Mathlib.RingTheory.Localization.Ideal

/-! Cotangent generation at a rational point can be checked in the stalk,
so it is unchanged when a family of equations switches denominator. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open GaloisForLFunctions.HTGeometry UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [Field K] {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)}
  (y : X.BaseFieldPointOver K s) {U : X.Opens}

/-- A family of equations on an affine chart spans at a rational point iff its
germs span the cotangent space in the stalk. -/
theorem cotangentSpan_iff_stalk (hU : IsAffineOpen U) (hy : y.hom default ∈ U)
    (I : Ideal (SectionRing s U)) :
    let m := RingHom.ker (affinePointEval y hy).toRingHom
    let g := (X.presheaf.germ U (y.hom default) hy).hom
    let n := IsLocalRing.maximalIdeal (X.presheaf.stalk (y.hom default))
    m ≤ I ⊔ m ^ 2 ↔ n ≤ I.map g ⊔ n ^ 2 := by
  intro m g n
  let B := X.presheaf.stalk (y.hom default)
  let ε := affinePointEval y hy
  letI : Algebra Γ(X, U) B := X.presheaf.algebra_section_stalk ⟨y.hom default, hy⟩
  letI : Algebra (SectionRing s U) B := X.presheaf.algebra_section_stalk ⟨y.hom default, hy⟩
  let P := hU.primeIdealOf ⟨y.hom default, hy⟩
  let p := P.asIdeal
  letI : p.IsPrime := P.isPrime
  letI : IsLocalization.AtPrime B p := hU.isLocalization_stalk ⟨y.hom default, hy⟩
  have hp : p = n.comap g := (IsLocalization.AtPrime.under_maximalIdeal B p).symm
  have he : m = n.comap g := by
    apply SetLike.ext
    intro a
    have h := (pointEval_ne_zero_iff y.hom U hy a).trans
      (Scheme.mem_basicOpen X a (y.hom default) hy)
    change ε a = 0 ↔ g a ∈ n
    have hn : g a ∈ n ↔ ¬ IsUnit (g a) := IsLocalRing.mem_maximalIdeal (g a)
    exact (not_ne_iff.symm.trans (not_congr h)).trans hn.symm
  have hpm : p = m := hp.trans he.symm
  have hpm' : p.map g = n := IsLocalization.AtPrime.map_eq_maximalIdeal p B
  have hm : m.map g = n := (congrArg (fun J : Ideal Γ(X, U) => J.map g) hpm).symm.trans hpm'
  have hmap : (I ⊔ m ^ 2).map g = I.map g ⊔ n ^ 2 := by
    rw [Ideal.map_sup, Ideal.map_pow, hm]
  constructor
  · intro h
    rw [← hmap, ← hm]
    exact Ideal.map_mono h
  · intro h a ha
    have e : g a ∈ (I ⊔ m ^ 2).map g := hmap.symm ▸ h (hm ▸ Ideal.mem_map_of_mem g ha)
    obtain ⟨b₀, hb, hba⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl B _ a).mp e
    let b : SectionRing s U := b₀
    have hba' : b * a ∈ I ⊔ m ^ 2 := hba
    have hε : ε b ≠ 0 := fun hzero => hb (show b₀ ∈ p by rw [hpm]; exact hzero)
    let t := algebraMap K (SectionRing s U) (ε b)⁻¹
    have ht : 1 - t * b ∈ m := by
      change ε (1 - t * b) = 0
      rw [map_sub, map_one, map_mul, ε.commutes]
      change 1 - (ε b)⁻¹ * ε b = 0
      rw [inv_mul_cancel₀ hε, sub_self]
    have hta : (1 - t * b) * a ∈ m ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul ht ha
    have hsum : t * (b * a) + (1 - t * b) * a ∈ I ⊔ m ^ 2 :=
      Ideal.add_mem _ (Ideal.mul_mem_left _ _ hba') ((le_sup_right : m ^ 2 ≤ I ⊔ m ^ 2) hta)
    have eq : t * (b * a) + (1 - t * b) * a = a := by ring
    exact eq ▸ hsum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {N d : ℕ}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

private theorem germ_projectiveRatio_mul (i : X ⟶ PSpace K N)
    {u v w : MvPolynomial (Fin (N + 1)) K} (hu : u ∈ Grade (K := K) (N := N) d)
    (hv : v ∈ Grade (K := K) (N := N) d) (hw : w ∈ Grade (K := K) (N := N) d)
    {x : X} (hx : x ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u)
    (hx' : x ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) v) :
    X.presheaf.germ _ x hx (projectiveRatio i hu hv) *
      X.presheaf.germ _ x hx' (projectiveRatio i hv hw) =
    X.presheaf.germ _ x hx (projectiveRatio i hu hw) := by
  let U := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u
  let V := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) v
  have hxW : x ∈ U ⊓ V := ⟨hx, hx'⟩
  have h := congrArg (X.presheaf.germ (U ⊓ V) x hxW).hom (projectiveRatio_mul i hu hv hw)
  rw [map_mul] at h
  simpa only [TopCat.Presheaf.germ_res_apply] using h

/-- Changing a nonvanishing denominator multiplies every ratio germ by the
same unit, so the corresponding cotangent generation conditions coincide. -/
theorem cotangentSpan_projectiveRatio_iff (i : X ⟶ PSpace K N)
    {u v : MvPolynomial (Fin (N + 1)) K}
    (hu : u ∈ Grade (K := K) (N := N) d) (hv : v ∈ Grade (K := K) (N := N) d)
    {J : Type*} (w : J → MvPolynomial (Fin (N + 1)) K)
    (hw : ∀ j, w j ∈ Grade (K := K) (N := N) d)
    (huU : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u))
    (hvU : IsAffineOpen (i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) v))
    (hx : y.hom default ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u)
    (hx' : y.hom default ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) v) :
    let m := RingHom.ker (affinePointEval y hx).toRingHom
    let m' := RingHom.ker (affinePointEval y hx').toRingHom
    m ≤ Ideal.span (Set.range fun j => projectiveRatio i hu (hw j)) ⊔ m ^ 2 ↔
      m' ≤ Ideal.span (Set.range fun j => projectiveRatio i hv (hw j)) ⊔ m' ^ 2 := by
  intro m m'
  let U := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) u
  let V := i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) v
  let ru (j : J) : SectionRing s U := projectiveRatio i hu (hw j)
  let rv (j : J) : SectionRing s V := projectiveRatio i hv (hw j)
  let I : Ideal (SectionRing s U) := Ideal.span (Set.range ru)
  let I' : Ideal (SectionRing s V) := Ideal.span (Set.range rv)
  change (m ≤ I ⊔ m ^ 2) ↔ (m' ≤ I' ⊔ m' ^ 2)
  refine (cotangentSpan_iff_stalk y huU hx I).trans (Iff.trans ?_ (cotangentSpan_iff_stalk y hvU hx' I').symm)
  let x := y.hom default
  let B := X.presheaf.stalk x
  let a (j : J) : B := X.presheaf.germ _ x hx (projectiveRatio i hu (hw j))
  let b (j : J) : B := X.presheaf.germ _ x hx' (projectiveRatio i hv (hw j))
  let r : B := X.presheaf.germ _ x hx (projectiveRatio i hu hv)
  have hr : IsUnit r := by
    apply (Scheme.mem_basicOpen X _ x hx).mp
    rw [basicOpen_projectiveRatio]
    exact ⟨hx, hx'⟩
  have hab (j : J) : r * b j = a j := germ_projectiveRatio_mul i hu hv (hw j) hx hx'
  have hspan : Ideal.span (Set.range a) = Ideal.span (Set.range b) := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      rw [← hab j]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self j))
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      apply (Ideal.unit_mul_mem_iff_mem _ hr).mp
      rw [hab j]
      exact Ideal.subset_span (Set.mem_range_self j)
  let M := IsLocalRing.maximalIdeal B
  let gu : SectionRing s U →+* B := (X.presheaf.germ U x hx).hom
  let gv : SectionRing s V →+* B := (X.presheaf.germ V x hx').hom
  have eU : Set.range a = gu '' Set.range ru := Set.range_comp gu ru
  have eV : Set.range b = gv '' Set.range rv := Set.range_comp gv rv
  have hmaps : I.map gu = I'.map gv := calc
    _ = Ideal.span (gu '' Set.range ru) := Ideal.map_span _ _
    _ = Ideal.span (Set.range a) := congrArg Ideal.span eU.symm
    _ = Ideal.span (Set.range b) := hspan
    _ = Ideal.span (gv '' Set.range rv) := congrArg Ideal.span eV
    _ = _ := (Ideal.map_span _ _).symm
  change (M ≤ I.map gu ⊔ M ^ 2) ↔ (M ≤ I'.map gv ⊔ M ^ 2)
  rw [hmaps]

end GlobalTheory.SchemeCohomology
