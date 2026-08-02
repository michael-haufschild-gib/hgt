import GaloisForLFunctions.HTGeometry.MonomialFaceIdeal
import GaloisForLFunctions.HTGeometry.SimplexConeContraction

/-!
# Exactness of the coordinate face complex in every degree

The all-face complex of the coordinate normal crossing has a cochain model: a degree-`c` cochain
assigns to every `c`-element set `S` of directions a polynomial none of whose monomials uses a
direction of `S`, that is a representative of a class of `A/(X_j : j ∈ S)`.  The differential is the
signed face sum followed by deletion of the monomials that meet the new direction.

Taking the coefficient of a fixed monomial turns this into the reduced simplicial cochain complex
on the vertex set of directions the monomial does not use.  That vertex set is nonempty whenever
the coefficient is nonzero, so the cone contraction applies blockwise, and reassembling the
finitely many blocks gives a polynomial primitive.

Hence the complex

```text
0 → A/(∏_j X_j) → ⊕_{|S|=1} A/(X_j) → ⊕_{|S|=2} A/(X_j,X_k) → ⋯
```

is exact in every degree: compatible data on the source faces glue, with no higher obstruction.
-/

open scoped BigOperators

namespace GaloisForLFunctions.FaceIdeal

open MvPolynomial HTGeometry

noncomputable section

variable {σ : Type*} {R : Type*} [CommRing R]

/-! ## The face-truncated coboundary -/

/-- Delete from `P` every monomial that uses a direction of `S`. -/
def faceTruncate (S : Finset σ) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ d ∈ P.support.filter (fun d => ∀ j ∈ S, d j = 0), monomial d (coeff d P)

theorem coeff_faceTruncate [DecidableEq σ] (S : Finset σ) (P : MvPolynomial σ R) (e : σ →₀ ℕ) :
    coeff e (faceTruncate S P) = if ∀ j ∈ S, e j = 0 then coeff e P else 0 := by
  classical
  rw [faceTruncate, coeff_sum]
  by_cases h : ∀ j ∈ S, e j = 0
  · rw [if_pos h]
    by_cases he : coeff e P = 0
    · rw [he]
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [coeff_monomial]
      split_ifs with hbe
      · rw [hbe]; exact he
      · rfl
    · refine (Finset.sum_eq_single e ?_ ?_).trans ?_
      · intro b _ hbe
        rw [coeff_monomial, if_neg hbe]
      · intro hnm
        exact absurd (Finset.mem_filter.mpr ⟨mem_support_iff.mpr he, h⟩) hnm
      · rw [coeff_monomial, if_pos rfl]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [coeff_monomial]
    split_ifs with hbe
    · exact absurd (hbe ▸ (Finset.mem_filter.mp hb).2) h
    · rfl

/-- The cochain of coefficients of a fixed monomial. -/
def coeffCochain (d : σ →₀ ℕ) (f : Finset σ → MvPolynomial σ R) : Finset σ → R :=
  fun S => coeff d (f S)

theorem faceSign_mvPolynomial [DecidableEq σ] [LinearOrder σ] (S : Finset σ) (j : σ) :
    faceSign (MvPolynomial σ R) S j = C (faceSign R S j) := by
  simp only [faceSign, map_pow, map_neg, map_one]

theorem coeff_simplicialCoboundary [DecidableEq σ] [LinearOrder σ] (d : σ →₀ ℕ)
    (f : Finset σ → MvPolynomial σ R) (S : Finset σ) :
    coeff d (simplicialCoboundary (MvPolynomial σ R) f S) =
      simplicialCoboundary R (coeffCochain d f) S := by
  rw [simplicialCoboundary, simplicialCoboundary, coeff_sum]
  exact Finset.sum_congr rfl fun v _ => by
    rw [faceSign_mvPolynomial, coeff_C_mul]
    rfl

/-- The differential of the coordinate face complex: signed face sum, then deletion of the
monomials that meet the face. -/
def faceCoboundary [DecidableEq σ] [LinearOrder σ] (f : Finset σ → MvPolynomial σ R) :
    Finset σ → MvPolynomial σ R :=
  fun S => faceTruncate S (simplicialCoboundary (MvPolynomial σ R) f S)

theorem coeff_faceCoboundary [DecidableEq σ] [LinearOrder σ] (d : σ →₀ ℕ)
    (f : Finset σ → MvPolynomial σ R) (S : Finset σ) :
    coeff d (faceCoboundary f S) =
      if ∀ j ∈ S, d j = 0 then simplicialCoboundary R (coeffCochain d f) S else 0 := by
  rw [faceCoboundary, coeff_faceTruncate, coeff_simplicialCoboundary]

/-! ## The vertex set of a monomial -/

/-- The directions a monomial does not use. -/
def unusedDirections [Fintype σ] [DecidableEq σ] (d : σ →₀ ℕ) : Finset σ :=
  Finset.univ.filter fun j => d j = 0

theorem subset_unusedDirections_iff [Fintype σ] [DecidableEq σ] (S : Finset σ) (d : σ →₀ ℕ) :
    S ⊆ unusedDirections d ↔ ∀ j ∈ S, d j = 0 := by
  constructor
  · intro h j hj
    exact (Finset.mem_filter.mp (h hj)).2
  · intro h j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h j hj⟩

/-! ## The blockwise cone primitive -/

/-- The cone primitive of the monomial block of a face cochain, at the least unused direction. -/
def facePrimitive [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (f : Finset σ → MvPolynomial σ R) (d : σ →₀ ℕ) : Finset σ → R :=
  if hne : (unusedDirections d).Nonempty then
    simplicialCone R ((unusedDirections d).min' hne) (coeffCochain d f)
  else 0

theorem facePrimitive_of_nonempty [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (f : Finset σ → MvPolynomial σ R) (d : σ →₀ ℕ)
    (hne : (unusedDirections d).Nonempty) :
    facePrimitive f d =
      simplicialCone R ((unusedDirections d).min' hne) (coeffCochain d f) :=
  dif_pos hne

theorem facePrimitive_of_isEmpty [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (f : Finset σ → MvPolynomial σ R) (d : σ →₀ ℕ)
    (hne : ¬ (unusedDirections d).Nonempty) : facePrimitive f d = 0 :=
  dif_neg hne

theorem facePrimitive_of_coeffCochain_eq_zero [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (f : Finset σ → MvPolynomial σ R) (d : σ →₀ ℕ)
    (hzero : coeffCochain d f = 0) : facePrimitive f d = 0 := by
  by_cases hne : (unusedDirections d).Nonempty
  · rw [facePrimitive_of_nonempty f d hne, hzero]
    funext τ
    rw [simplicialCone]
    split_ifs with h
    · rfl
    · rw [Pi.zero_apply, mul_zero]
      rfl
  · exact facePrimitive_of_isEmpty f d hne

/-! ## Exactness -/

/-- **The coordinate face complex is exact in every degree.**  A cochain of degree `c + 1` whose
values avoid their own faces and which is killed by the face-truncated coboundary is the
coboundary of a cochain of degree `c` with the same avoidance property. -/
theorem faceComplex_exact [Fintype σ] [DecidableEq σ] [LinearOrder σ] (c : ℕ)
    {f : Finset σ → MvPolynomial σ R}
    (hcard : ∀ S : Finset σ, S.card ≠ c + 1 → f S = 0)
    (havoid : ∀ (S : Finset σ) (d : σ →₀ ℕ), coeff d (f S) ≠ 0 → ∀ j ∈ S, d j = 0)
    (hcocycle : ∀ S : Finset σ, faceCoboundary f S = 0) :
    ∃ h : Finset σ → MvPolynomial σ R,
      (∀ S : Finset σ, S.card ≠ c → h S = 0) ∧
      (∀ (S : Finset σ) (d : σ →₀ ℕ), coeff d (h S) ≠ 0 → ∀ j ∈ S, d j = 0) ∧
      ∀ S : Finset σ, faceCoboundary h S = f S := by
  classical
  have hgcard : ∀ d : σ →₀ ℕ, coeffCochain d f ∈ cardCochains R (c + 1) := by
    intro d S hS
    rw [coeffCochain, hcard S hS, coeff_zero]
  have hgsupp : ∀ (d : σ →₀ ℕ) (τ : Finset σ), ¬ τ ⊆ unusedDirections d →
      coeffCochain d f τ = 0 := by
    intro d τ hτ
    by_contra hne
    exact hτ ((subset_unusedDirections_iff τ d).mpr (havoid τ d hne))
  have hgcocycle : ∀ (d : σ →₀ ℕ) (S : Finset σ), S ⊆ unusedDirections d →
      simplicialCoboundary R (coeffCochain d f) S = 0 := by
    intro d S hS
    have hcb := coeff_faceCoboundary d f S
    rw [hcocycle S, coeff_zero, if_pos ((subset_unusedDirections_iff S d).mp hS)] at hcb
    exact hcb.symm
  have hpcard : ∀ d : σ →₀ ℕ, facePrimitive f d ∈ cardCochains R c := by
    intro d
    by_cases hne : (unusedDirections d).Nonempty
    · rw [facePrimitive_of_nonempty f d hne]
      exact simplicialCone_mem_cardCochains (hgcard d)
    · rw [facePrimitive_of_isEmpty f d hne]
      exact Submodule.zero_mem _
  have hpsupp : ∀ (d : σ →₀ ℕ) (τ : Finset σ), ¬ τ ⊆ unusedDirections d →
      facePrimitive f d τ = 0 := by
    intro d τ hτ
    by_cases hne : (unusedDirections d).Nonempty
    · rw [facePrimitive_of_nonempty f d hne]
      exact simplicialCone_support (hgsupp d) τ hτ
    · rw [facePrimitive_of_isEmpty f d hne]
      rfl
  have hpprim : ∀ (d : σ →₀ ℕ) (S : Finset σ), S ⊆ unusedDirections d →
      simplicialCoboundary R (facePrimitive f d) S = coeffCochain d f S := by
    intro d S hS
    by_cases hne : (unusedDirections d).Nonempty
    · rw [facePrimitive_of_nonempty f d hne]
      exact simplicialCoboundary_simplicialCone_of_subset
        ((unusedDirections d).min'_mem hne) (hgcocycle d) hS
    · rw [facePrimitive_of_isEmpty f d hne]
      have hSempty : S = ∅ := by
        rw [Finset.not_nonempty_iff_eq_empty] at hne
        rw [hne] at hS
        exact Finset.subset_empty.mp hS
      rw [hSempty, simplicialCoboundary_empty, coeffCochain, hcard ∅ (by simp), coeff_zero]
  set D : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun S : Finset σ => (f S).support with hD
  have hgzero : ∀ e ∉ D, coeffCochain e f = 0 := by
    intro e he
    funext S
    have hns : e ∉ (f S).support := fun hmem =>
      he (Finset.mem_biUnion.mpr ⟨S, Finset.mem_univ S, hmem⟩)
    rw [coeffCochain]
    exact notMem_support_iff.mp hns
  have hpzero : ∀ e ∉ D, facePrimitive f e = 0 := fun e he =>
    facePrimitive_of_coeffCochain_eq_zero f e (hgzero e he)
  have hcoeff : ∀ (S : Finset σ) (e : σ →₀ ℕ),
      coeff e (∑ d ∈ D, monomial d (facePrimitive f d S)) = facePrimitive f e S := by
    intro S e
    rw [coeff_sum]
    by_cases he : e ∈ D
    · refine (Finset.sum_eq_single e ?_ ?_).trans ?_
      · intro b _ hbe
        rw [coeff_monomial, if_neg hbe]
      · intro hnm
        exact absurd he hnm
      · rw [coeff_monomial, if_pos rfl]
    · have hz : facePrimitive f e S = 0 := by rw [hpzero e he]; rfl
      rw [hz]
      refine Finset.sum_eq_zero fun b hb => ?_
      rw [coeff_monomial]
      split_ifs with hbe
      · exact absurd (hbe ▸ hb) he
      · rfl
  refine ⟨fun S => ∑ d ∈ D, monomial d (facePrimitive f d S), ?_, ?_, ?_⟩
  · intro S hS
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [hpcard d S hS, map_zero]
  · intro S d hd
    rw [hcoeff S d] at hd
    by_contra hcon
    exact hd (hpsupp d S fun hsub => hcon ((subset_unusedDirections_iff S d).mp hsub))
  · intro S
    ext e
    rw [coeff_faceCoboundary]
    have hcc : coeffCochain e (fun T => ∑ d ∈ D, monomial d (facePrimitive f d T)) =
        facePrimitive f e := by
      funext T
      exact hcoeff T e
    rw [hcc]
    by_cases h : ∀ j ∈ S, e j = 0
    · rw [if_pos h]
      exact hpprim e S ((subset_unusedDirections_iff S e).mpr h)
    · rw [if_neg h]
      by_contra hcon
      exact h (havoid S e fun hz => hcon hz.symm)

/-! ## The complex property and the augmentation -/

theorem simplicialCoboundary_congr_of_faces [DecidableEq σ] [LinearOrder σ]
    (g g' : Finset σ → R) (S : Finset σ) (h : ∀ v ∈ S, g (S.erase v) = g' (S.erase v)) :
    simplicialCoboundary R g S = simplicialCoboundary R g' S := by
  rw [simplicialCoboundary, simplicialCoboundary]
  exact Finset.sum_congr rfl fun v hv => by rw [h v hv]

/-- **The face-truncated coboundary squares to zero.** -/
theorem faceCoboundary_faceCoboundary [DecidableEq σ] [LinearOrder σ]
    (f : Finset σ → MvPolynomial σ R) (S : Finset σ) :
    faceCoboundary (faceCoboundary f) S = 0 := by
  classical
  ext d
  rw [coeff_faceCoboundary, coeff_zero]
  split_ifs with h
  · have hagree : ∀ v ∈ S, coeffCochain d (faceCoboundary f) (S.erase v) =
        simplicialCoboundary R (coeffCochain d f) (S.erase v) := by
      intro v _
      rw [coeffCochain, coeff_faceCoboundary, if_pos]
      intro j hj
      exact h j (Finset.mem_of_mem_erase hj)
    rw [simplicialCoboundary_congr_of_faces _ _ _ hagree]
    exact congrFun (simplicialCoboundary_simplicialCoboundary (coeffCochain d f)) S
  · rfl

theorem faceSign_singleton_self [DecidableEq σ] [LinearOrder σ] (j : σ) :
    faceSign R ({j} : Finset σ) j = 1 := by
  have hfilter : ({j} : Finset σ).filter (· < j) = ∅ := by
    refine Finset.filter_eq_empty_iff.mpr fun x hx => ?_
    rw [Finset.mem_singleton] at hx
    exact hx ▸ lt_irrefl j
  rw [faceSign, hfilter, Finset.card_empty, pow_zero]

/-- **Injectivity at the augmentation.**  A degree-zero cochain killed by the coboundary has its
value in the principal ideal of the squarefree product: the global boundary class is unique. -/
theorem faceComplex_augmentation_kernel [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    {h : Finset σ → MvPolynomial σ R}
    (hcocycle : ∀ S : Finset σ, faceCoboundary h S = 0) :
    h ∅ ∈ Ideal.span {∏ j : σ, (X j : MvPolynomial σ R)} := by
  classical
  rw [mem_span_prod_X_iff]
  intro d hd j _
  by_contra hdj
  have hcb := coeff_faceCoboundary d h {j}
  have hpos : ∀ k ∈ ({j} : Finset σ), d k = 0 := by
    intro k hk
    rw [Finset.mem_singleton] at hk
    subst hk
    exact hdj
  rw [hcocycle {j}, coeff_zero, if_pos hpos] at hcb
  rw [simplicialCoboundary, Finset.sum_singleton, faceSign_singleton_self,
    Finset.erase_singleton, one_mul, coeffCochain] at hcb
  exact hd hcb.symm

/-! ## Face restriction splits a polynomial along the face ideal -/

/-- **Face splitting.**  Restricting a polynomial to a face and subtracting leaves an element of
the face ideal.  This is the step `P = P|_{x_j = 0} + x_j S` of the reverse inclusion of the
translation-annihilator theorem, with `faceTruncate` the restriction. -/
theorem sub_faceTruncate_mem_faceIdeal [DecidableEq σ] (S : Finset σ)
    (P : MvPolynomial σ R) : P - faceTruncate S P ∈ faceIdeal R S := by
  classical
  rw [mem_faceIdeal_iff]
  intro d hd
  by_contra hcon
  push Not at hcon
  rw [coeff_sub, coeff_faceTruncate, if_pos hcon, sub_self] at hd
  exact hd rfl

end

end GaloisForLFunctions.FaceIdeal
