import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveRatioTransitions
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Sections on a linear projective chart of a closed subscheme are
homogeneous fractions. A finite family admits a common denominator power. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [CommRing K] {X : Scheme.{0}} {N : ℕ}
  {l : MvPolynomial (Fin (N + 1)) K}

private abbrev grading := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

private def powFraction (hl : l.IsHomogeneous 1) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) K) (hf : f.IsHomogeneous n) :
    HomogeneousLocalization.Away (grading (K := K) (N := N)) l :=
  HomogeneousLocalization.Away.mk _ hl n f (by simpa using hf)

/-- Take the numerator divided by the specified power of the chart coordinate. -/
def projectivePowerRatio (i : X ⟶ PSpace K N) (hl : l.IsHomogeneous 1) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) K) (hf : f.IsHomogeneous n) :
    Γ(X, i ⁻¹ᵁ Proj.basicOpen (grading (K := K) (N := N)) l) :=
  (i.app _).hom ((Proj.awayToSection _ l).hom (powFraction hl n f hf))

private theorem powerRatio_pad (i : X ⟶ PSpace K N) (hl : l.IsHomogeneous 1) (n k : ℕ)
    {m : ℕ} (hm : n + k = m)
    {f : MvPolynomial (Fin (N + 1)) K} (hf : f.IsHomogeneous n)
    (h : (f * l ^ k).IsHomogeneous m) :
    projectivePowerRatio i hl m (f * l ^ k) h = projectivePowerRatio i hl n f hf := by
  subst m
  apply congrArg ((i.app _).hom ∘ (Proj.awayToSection _ l).hom)
  apply HomogeneousLocalization.val_injective
  simp only [powFraction, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, pow_add]
  ring

private theorem exists_powerRatio (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    (hl : l.IsHomogeneous 1) (a : Γ(X, i ⁻¹ᵁ Proj.basicOpen (grading (K := K) (N := N)) l)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f.IsHomogeneous n),
      projectivePowerRatio i hl n f hf = a := by
  let A := grading (K := K) (N := N)
  let U := Proj.basicOpen A l
  have hU : IsAffineOpen U := Proj.isAffineOpen_basicOpen A l hl one_pos
  obtain ⟨b, hb⟩ := i.app_surjective U hU a
  let E := Proj.basicOpenIsoAway A l hl one_pos
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso E.hom).2 b
  obtain ⟨n, f, hf, he⟩ := HomogeneousLocalization.Away.mk_surjective A hl c
  have hf' : f.IsHomogeneous n := by
    change f.IsHomogeneous (n • (1 : ℕ)) at hf
    simpa only [nsmul_eq_mul, Nat.cast_id, mul_one] using hf
  have he' : powFraction hl n f hf' = c := he
  refine ⟨n, f, hf', ?_⟩
  change (i.app U).hom (E.hom.hom (powFraction hl n f hf')) = a
  rw [he', hc, hb]

/-- The numerator degrees of finitely many sections can be made equal by
multiplying each numerator and denominator by the same power. -/
theorem exists_common_powerRatio (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    (hl : l.IsHomogeneous 1) {J : Type} [Fintype J]
    (a : J → Γ(X, i ⁻¹ᵁ Proj.basicOpen (grading (K := K) (N := N)) l)) :
    ∃ b : ℕ, ∀ n ≥ b, ∀ j, ∃ (f : MvPolynomial (Fin (N + 1)) K) (hf : f.IsHomogeneous n),
      projectivePowerRatio i hl n f hf = a j := by
  classical
  choose m f hf h using fun j => exists_powerRatio i hl (a j)
  refine ⟨Finset.univ.sup m, fun n hn j => ?_⟩
  have hm : m j ≤ n := (Finset.le_sup (f := m) (Finset.mem_univ j)).trans hn
  have hpow : (l ^ (n - m j)).IsHomogeneous (n - m j) := by
    simpa using SetLike.pow_mem_graded (n - m j) (show l ∈ grading (K := K) (N := N) 1 from hl)
  have hsum := Nat.add_sub_of_le hm
  have hh : (f j * l ^ (n - m j)).IsHomogeneous n :=
    (congrArg (fun k => (f j * l ^ (n - m j)).IsHomogeneous k) hsum).mp ((hf j).mul hpow)
  refine ⟨f j * l ^ (n - m j), hh, ?_⟩
  exact (powerRatio_pad i hl (m j) (n - m j) hsum (hf j) hh).trans (h j)

/-- Ratios with denominator a positive power restrict to the corresponding
homogeneous fraction on the original linear chart. -/
theorem projectivePowerRatio_eq_appLE (i : X ⟶ PSpace K N)
    (hl : l.IsHomogeneous 1) {n : ℕ} (hn : 0 < n)
    {f : MvPolynomial (Fin (N + 1)) K} (hf : f.IsHomogeneous n)
    (hp : (l ^ n).IsHomogeneous n) :
    let A := grading (K := K) (N := N)
    let U := Proj.basicOpen A l
    let V := Proj.basicOpen A (l ^ n)
    let e : U ≤ V := (Proj.basicOpen_pow A l n hn).ge
    (i.appLE V (i ⁻¹ᵁ U) ((Opens.map i.base).monotone e)).hom
      (homogeneousRatio hp hf) = projectivePowerRatio i hl n f hf := by
  intro A U V e
  have hsec : (PSpace K N).presheaf.map (homOfLE e).op (homogeneousRatio hp hf) =
      (Proj.awayToSection A l).hom (powFraction hl n f hf) := by
    apply Subtype.ext
    funext x
    apply HomogeneousLocalization.val_injective
    change ((homogeneousRatio hp hf).1 ⟨x.1, e x.2⟩).val =
      (((Proj.awayToSection A l).hom (powFraction hl n f hf)).1 x).val
    rw [homogeneousRatio_val]
    rfl
  have hnat := i.naturality (homOfLE e).op
  have hh := congrArg (fun r : Γ(PSpace K N, V) ⟶ Γ(X, i ⁻¹ᵁ U) =>
    r.hom (homogeneousRatio hp hf)) hnat
  exact hh.symm.trans (congrArg (i.app U).hom hsec)

/-- A homogeneous fraction on the linear chart is nonzero where its numerator
is nonzero. -/
theorem basicOpen_projectivePowerRatio (i : X ⟶ PSpace K N)
    (hl : l.IsHomogeneous 1) {n : ℕ} (hn : 0 < n)
    {f : MvPolynomial (Fin (N + 1)) K} (hf : f.IsHomogeneous n) :
    X.basicOpen (projectivePowerRatio i hl n f hf) =
      (i ⁻¹ᵁ Proj.basicOpen (grading (K := K) (N := N)) l) ⊓
      (i ⁻¹ᵁ Proj.basicOpen (grading (K := K) (N := N)) f) := by
  let A := grading (K := K) (N := N)
  let U := Proj.basicOpen A l
  let V := Proj.basicOpen A (l ^ n)
  let W := Proj.basicOpen A f
  have hVU : V = U := Proj.basicOpen_pow A l n hn
  have hp : (l ^ n).IsHomogeneous n := by simpa only [one_mul] using hl.pow n
  have he := projectivePowerRatio_eq_appLE i hl hn hf hp
  change (i.appLE V (i ⁻¹ᵁ U) (i.preimage_mono hVU.ge)).hom (homogeneousRatio hp hf) =
    projectivePowerRatio i hl n f hf at he
  rw [← he, Scheme.basicOpen_appLE, basicOpen_homogeneousRatio]
  exact le_antisymm (inf_le_inf_left _ (i.preimage_mono inf_le_right))
    (le_inf inf_le_left (le_inf (inf_le_left.trans (i.preimage_mono hVU.ge)) inf_le_right))

/-- On a fixed linear chart, division by powers of the denominator
respects products of homogeneous numerators. -/
theorem projectivePowerRatio_mul (i : X ⟶ PSpace K N) (hl : l.IsHomogeneous 1)
    {m n : ℕ} {f g : MvPolynomial (Fin (N + 1)) K}
    (hf : f.IsHomogeneous m) (hg : g.IsHomogeneous n) :
    projectivePowerRatio i hl (m + n) (f * g) (hf.mul hg) =
      projectivePowerRatio i hl m f hf * projectivePowerRatio i hl n g hg := by
  have h : powFraction hl (m + n) (f * g) (hf.mul hg) =
      powFraction hl m f hf * powFraction hl n g hg := by
    apply HomogeneousLocalization.val_injective
    simp only [powFraction, HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_mul,
      Localization.mk_mul, pow_add]
    rfl
  let F := (i.app _).hom.comp (Proj.awayToSection (grading (K := K) (N := N)) l).hom
  change F (powFraction hl (m + n) (f * g) (hf.mul hg)) =
    F (powFraction hl m f hf) * F (powFraction hl n g hg)
  rw [h, map_mul]

/-- For each positive degree, dividing by the corresponding power of the
linear chart denominator is linear on the homogeneous numerators. -/
def projectivePowerRatioLinear (i : X ⟶ PSpace K N) {s : X ⟶ Spec (CommRingCat.of K)}
    (hi : i ≫ PSpace.str K N = s) (hl : l.IsHomogeneous 1) {n : ℕ} (hn : 0 < n) :
    grading (K := K) (N := N) n →ₗ[K]
      SectionRing s (i ⁻¹ᵁ Proj.basicOpen (grading (K := K) (N := N)) l) := by
  let A := grading (K := K) (N := N)
  let e : Proj.basicOpen A l ≤ Proj.basicOpen A (l ^ n) := (Proj.basicOpen_pow A l n hn).ge
  have hp : (l ^ n).IsHomogeneous n := by simpa only [one_mul] using hl.pow n
  exact (sectionRes s (homOfLE ((Opens.map i.base).monotone e))).toLinearMap.comp
    (projectiveRatioLinear i hi hp hn)

theorem projectivePowerRatioLinear_apply (i : X ⟶ PSpace K N) {s : X ⟶ Spec (CommRingCat.of K)}
    (hi : i ≫ PSpace.str K N = s) (hl : l.IsHomogeneous 1) {n : ℕ} (hn : 0 < n)
    (f : grading (K := K) (N := N) n) :
    projectivePowerRatioLinear i hi hl hn f = projectivePowerRatio i hl n f.1 f.2 :=
  projectivePowerRatio_eq_appLE i hl hn f.2 _

end GlobalTheory.SchemeCohomology
