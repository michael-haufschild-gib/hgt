import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectivePointRatios
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! Linear forms separate a rational projective point from every other point.
Products of these linear forms give homogeneous separators for finite sets. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GaloisForLFunctions.HTGeometry UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {N : ℕ}

private abbrev Grade := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K

private theorem exists_coordinate (x : PSpace K N) :
    ∃ i : Fin (N + 1), x ∈ PSpace.coordinateOpen K N i := by
  apply Opens.mem_iSup.mp
  rw [PSpace.iSup_coordinateOpen]
  trivial

theorem baseFieldPoint_isClosed {X : Scheme.{0}} {s : X ⟶ Spec (CommRingCat.of K)}
    (y : X.BaseFieldPointOver K s) : IsClosed ({y.hom default} : Set X) := by
  letI : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  letI : IsClosedImmersion y.hom := isClosedImmersion_of_comp_eq_id s y.hom y.commutes
  have hr : Set.range y.hom = {y.hom default} := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      rw [Subsingleton.elim a default]
      exact Set.mem_singleton _
    · rintro rfl
      exact ⟨default, rfl⟩
  exact hr ▸ y.hom.isClosedEmbedding.isClosed_range

/-- A linear form can vanish at a rational point of projective space and
be nonzero at any distinct point, including a nonclosed point. -/
theorem exists_linear_form_separating (y : (PSpace K N).BaseFieldPointOver K (PSpace.str K N))
    (x : PSpace K N) (hxy : x ≠ y.hom default) :
    ∃ l : MvPolynomial (Fin (N + 1)) K, l.IsHomogeneous 1 ∧
      y.hom default ∉ Proj.basicOpen (Grade (K := K) (N := N)) l ∧
      x ∈ Proj.basicOpen (Grade (K := K) (N := N)) l := by
  classical
  obtain ⟨i, hi⟩ := exists_coordinate (y.hom default)
  let U := PSpace.coordinateOpen K N i
  let A := SectionRing (PSpace.str K N) U
  let ε : A →ₐ[K] K := affinePointEval y hi
  let r (j : Fin (N + 1)) : A := pspaceChartRatio K i j
  let Xh (j : Fin (N + 1)) : Grade (K := K) (N := N) 1 :=
    ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X K j⟩
  let L (j : Fin (N + 1)) := Xh j - ε (r j) • Xh i
  let R : Grade (K := K) (N := N) 1 →ₗ[K] A :=
    pspaceRatioLinear (Xh i).2 one_pos
  have hR (j : Fin (N + 1)) : R (L j) = r j - algebraMap K A (ε (r j)) := by
    change R (Xh j - ε (r j) • Xh i) = _
    have hself : R (Xh i) = 1 := homogeneousRatio_self (Xh i).2
    have hj : R (Xh j) = r j := rfl
    rw [map_sub, map_smul, hself, hj, Algebra.smul_def, mul_one]
  have hbasic (j : Fin (N + 1)) : (PSpace K N).basicOpen (R (L j)) =
      U ⊓ Proj.basicOpen (Grade (K := K) (N := N)) (L j).1 :=
    basicOpen_homogeneousRatio (Xh i).2 (L j).2
  have hy (j : Fin (N + 1)) :
      y.hom default ∉ Proj.basicOpen (Grade (K := K) (N := N)) (L j).1 := by
    have hz : ε (R (L j)) = 0 := by
      rw [hR, map_sub, ε.commutes]
      change ε (r j) - ε (r j) = 0
      exact sub_self _
    intro hj
    have hm : y.hom default ∈ (PSpace K N).basicOpen (R (L j)) :=
      (hbasic j).symm ▸ (show y.hom default ∈ U ⊓ _ from ⟨hi, hj⟩)
    exact ((pointEval_ne_zero_iff y.hom U hi (R (L j))).mpr hm) hz
  by_contra! h
  have hx (j : Fin (N + 1)) : (L j).1 ∈ x.asHomogeneousIdeal :=
    not_not.mp (h (L j).1 (L j).2 (hy j))
  have hxU : x ∈ U := by
    intro hn
    change MvPolynomial.X i ∈ x.asHomogeneousIdeal at hn
    obtain ⟨j, hj⟩ := exists_coordinate x
    have hmem := x.asHomogeneousIdeal.toIdeal.add_mem (hx j)
      (x.asHomogeneousIdeal.toIdeal.mul_mem_left (MvPolynomial.C (ε (r j))) hn)
    change MvPolynomial.X j - ε (r j) • MvPolynomial.X i +
      MvPolynomial.C (ε (r j)) * MvPolynomial.X i ∈ x.asHomogeneousIdeal at hmem
    rw [MvPolynomial.smul_eq_C_mul, sub_add_cancel] at hmem
    exact hj hmem
  let g : A →+* (PSpace K N).presheaf.stalk x := ((PSpace K N).presheaf.germ U x hxU).hom
  let I : Ideal A := (IsLocalRing.maximalIdeal _).comap g
  have hI (a : A) : a ∈ I ↔ x ∉ (PSpace K N).basicOpen a :=
    (not_congr (Scheme.mem_basicOpen _ a x hxU)).symm
  let E := pspaceChartAlgEquiv K i
  let q := Ideal.Quotient.mkₐ K I
  have hq : q.comp E.toAlgHom = (Algebra.ofId K (A ⧸ I)).comp (ε.comp E.toAlgHom) := by
    apply MvPolynomial.algHom_ext
    intro j
    change q (E (MvPolynomial.X j)) = algebraMap K _ (ε (E (MvPolynomial.X j)))
    rw [pspaceChartAlgEquiv_X]
    have hj : R (L j.1) ∈ I := (hI _).mpr (fun hm => ((hbasic _).le hm).2 (hx j.1))
    rw [hR] at hj
    have hj' : q (r j.1 - algebraMap K A (ε (r j.1))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hj
    rwa [map_sub, q.commutes, sub_eq_zero] at hj'
  have hker (a : A) (ha : ε a = 0) : a ∈ I := by
    obtain ⟨p, rfl⟩ := E.surjective a
    have he : q (E p) = algebraMap K (A ⧸ I) (ε (E p)) :=
      DFunLike.congr_fun hq p
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (E p) = 0
    rw [he, ha, map_zero]
  have hspec : y.hom default ⤳ x := by
    rw [specializes_iff_forall_open]
    intro V hV hxV
    have hU : IsAffineOpen U := Proj.isAffineOpen_basicOpen (Grade (K := K) (N := N))
      _ (MvPolynomial.isHomogeneous_X K i) one_pos
    obtain ⟨a, ha, hxa⟩ := hU.exists_basicOpen_le
      (V := ⟨V, hV⟩) ⟨x, hxV⟩ hxU
    apply ha
    apply (pointEval_ne_zero_iff y.hom U hi a).mp
    intro hzero
    exact (hI _).mp (hker a hzero) hxa
  exact hxy (hspec.mem_closed (baseFieldPoint_isClosed y) (Set.mem_singleton _))

/-- Forms through a finite set of rational points separate every point
outside that set in each degree at least the size of the set. -/
theorem exists_form_separating_finite_points {X : Scheme.{0}}
    {s : X ⟶ Spec (CommRingCat.of K)} (i : X ⟶ PSpace K N) [IsClosedImmersion i]
    (hi : i ≫ PSpace.str K N = s) (S : Finset (X.BaseFieldPointOver K s))
    (m : ℕ) (hm : S.card ≤ m) (x : X) (hx : ∀ y ∈ S, x ≠ y.hom default) :
    ∃ f : MvPolynomial (Fin (N + 1)) K, f.IsHomogeneous m ∧
      (∀ y ∈ S, y.hom default ∉ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) f) ∧
      x ∈ i ⁻¹ᵁ Proj.basicOpen (Grade (K := K) (N := N)) f := by
  classical
  let z (y : S) : (PSpace K N).BaseFieldPointOver K (PSpace.str K N) :=
    ⟨y.1.hom ≫ i, by rw [Category.assoc, hi, y.1.commutes]⟩
  choose l hl hz hx' using fun y : S => exists_linear_form_separating (z y) (i x)
    (fun h => hx y.1 y.2 (i.isClosedEmbedding.injective h))
  obtain ⟨j, hj⟩ := exists_coordinate (i x)
  let f := MvPolynomial.X j ^ (m - S.card) * ∏ y, l y
  have hdeg : (m - S.card) • 1 + ∑ _y : S, (1 : ℕ) = m := by
    simp only [smul_eq_mul, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
    omega
  have hprod := SetLike.prod_mem_graded (Grade (K := K) (N := N)) (fun _ : S => 1) l
    (F := Finset.univ) (fun y _ => hl y)
  have hX : (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) K) ∈ Grade (K := K) (N := N) 1 :=
    MvPolynomial.isHomogeneous_X K j
  have hpow := SetLike.pow_mem_graded (m - S.card) hX
  refine ⟨f, hdeg ▸ SetLike.mul_mem_graded hpow hprod, ?_, ?_⟩
  · intro y hy h
    apply h
    change f ∈ (i (y.hom default)).asHomogeneousIdeal
    refine Ideal.mul_mem_left _ _ ?_
    let y₀ : S := ⟨y, hy⟩
    have hvan : i (y.hom default) ∉ Proj.basicOpen (Grade (K := K) (N := N)) (l y₀) := by
      have h' := hz y₀
      change (y.hom ≫ i) default ∉ _ at h'
      rwa [Scheme.Hom.comp_apply] at h'
    have hmem : l y₀ ∈ (i (y.hom default)).asHomogeneousIdeal :=
      not_not.mp hvan
    have hdiv : l y₀ ∣ ∏ v : S, l v := Finset.dvd_prod_of_mem l (Finset.mem_univ y₀)
    exact Ideal.mem_of_dvd _ hdiv hmem
  · intro h
    rcases (i x).isPrime.mem_or_mem h with h | h
    · exact hj ((i x).isPrime.mem_of_pow_mem _ h)
    · obtain ⟨y, _, hy⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hx' y hy

end GlobalTheory.SchemeCohomology
