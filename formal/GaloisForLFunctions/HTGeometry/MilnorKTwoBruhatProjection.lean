import GaloisForLFunctions.HTGeometry.MilnorKTwoWeylProjection
import GaloisForLFunctions.HTGeometry.SpecialLinearTransvectionGeneration
import GaloisForLFunctions.HTGeometry.SteinbergTWTWeylKernel
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Milnor's rank-four Bruhat projection

This file formalizes Lemma 12.6 of Milnor's proof of Matsumoto's theorem. Southwest
rank profiles recover the permutation in an upper--monomial--upper factorization; pivot-prefix
minors then recover every monomial scale. Existing rank-four Steinberg `TWT` normal forms provide
existence for every elementary matrix. The unique middle factor defines the Bruhat retraction.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {F : Type*} [Field F]

/-- Over a field, every invertible determinant-one matrix belongs to the elementary group. -/
theorem unit_mem_elementaryGroup_of_det_eq_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : (Matrix n n F)ˣ) (hA : Matrix.det (A : Matrix n n F) = 1) :
    A ∈ elementaryGroup F n := by
  obtain ⟨L, hL⟩ := isTransvectionProduct_of_det_eq_one
    (A : Matrix n n F) hA
  let g : SteinbergGroup F n :=
    (L.map fun t => steinbergX t.hij t.c).prod
  refine ⟨g, ?_⟩
  apply Units.ext
  change (steinbergToGL g : Matrix n n F) = (A : Matrix n n F)
  rw [hL]
  change (steinbergToGL
      ((L.map fun t => steinbergX t.hij t.c).prod) : Matrix n n F) = _
  clear hL A hA g
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, Units.val_mul]
      rw [steinbergToGL_x, elemUnit_val, ih]
      rfl

abbrev BruhatSuffix (r : Fin 4) := {i : Fin 4 // r ≤ i}
abbrev BruhatPrefix (s : Fin 4) := {j : Fin 4 // j ≤ s}

def southwestBlock (A : Matrix (Fin 4) (Fin 4) F) (r s : Fin 4) :
    Matrix (BruhatSuffix r) (BruhatPrefix s) F :=
  A.submatrix Subtype.val Subtype.val

def suffixPrincipalBlock (A : Matrix (Fin 4) (Fin 4) F) (r : Fin 4) :
    Matrix (BruhatSuffix r) (BruhatSuffix r) F :=
  A.submatrix Subtype.val Subtype.val

def prefixPrincipalBlock (A : Matrix (Fin 4) (Fin 4) F) (s : Fin 4) :
    Matrix (BruhatPrefix s) (BruhatPrefix s) F :=
  A.submatrix Subtype.val Subtype.val

theorem southwestBlock_mul_left (U A : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) (r s : Fin 4) :
    southwestBlock (U * A) r s = suffixPrincipalBlock U r * southwestBlock A r s := by
  classical
  ext i j
  simp only [southwestBlock, suffixPrincipalBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  have hsum := Finset.sum_subset (s₁ := Finset.Ici r) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := fun k : Fin 4 => U i.1 k * A k j.1) (by
      intro k _ hk
      rw [Finset.mem_Ici] at hk
      have hki : k < i.1 := lt_of_not_ge fun hik => hk (le_trans i.2 hik)
      rw [hU.1 i.1 k hki, zero_mul])
  rw [← hsum]
  exact Finset.sum_subtype (Finset.Ici r) (by simp) _

theorem southwestBlock_mul_right (A V : Matrix (Fin 4) (Fin 4) F)
    (hV : IsUpperUnipotent V) (r s : Fin 4) :
    southwestBlock (A * V) r s = southwestBlock A r s * prefixPrincipalBlock V s := by
  classical
  ext i j
  simp only [southwestBlock, prefixPrincipalBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  have hsum := Finset.sum_subset (s₁ := Finset.Iic s) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := fun k : Fin 4 => A i.1 k * V k j.1) (by
      intro k _ hk
      rw [Finset.mem_Iic] at hk
      have hjk : j.1 < k := lt_of_not_ge fun hkj => hk (le_trans hkj j.2)
      rw [hV.1 k j.1 hjk, mul_zero])
  rw [← hsum]
  exact Finset.sum_subtype (Finset.Iic s) (by simp) _

theorem suffixPrincipalBlock_det (U : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) (r : Fin 4) :
    (suffixPrincipalBlock U r).det = 1 := by
  classical
  rw [Matrix.det_of_upperTriangular (M := suffixPrincipalBlock U r) (by
    intro i j hji
    exact hU.1 i.1 j.1 hji)]
  simp [suffixPrincipalBlock, hU.2]

theorem prefixPrincipalBlock_det (V : Matrix (Fin 4) (Fin 4) F)
    (hV : IsUpperUnipotent V) (s : Fin 4) :
    (prefixPrincipalBlock V s).det = 1 := by
  classical
  rw [Matrix.det_of_upperTriangular (M := prefixPrincipalBlock V s) (by
    intro i j hji
    exact hV.1 i.1 j.1 hji)]
  simp [prefixPrincipalBlock, hV.2]

theorem southwestBlock_upper_monomial_upper_rank
    (U V : Matrix (Fin 4) (Fin 4) F) (hU : IsUpperUnipotent U)
    (hV : IsUpperUnipotent V) (σ : Equiv.Perm (Fin 4)) (c : Fin 4 → Fˣ)
    (r s : Fin 4) :
    (southwestBlock (U * signedMonomialMatrix σ c * V) r s).rank =
      (southwestBlock (signedMonomialMatrix σ c) r s).rank := by
  rw [southwestBlock_mul_right _ _ hV, southwestBlock_mul_left _ _ hU]
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (by
    rw [prefixPrincipalBlock_det V hV s]
    exact isUnit_one)]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by
    rw [suffixPrincipalBlock_det U hU r]
    exact isUnit_one)]

abbrev BruhatActive (σ : Equiv.Perm (Fin 4)) (r s : Fin 4) :=
  {j : BruhatPrefix s // r ≤ σ j.1}

theorem card_bruhatActive (σ : Equiv.Perm (Fin 4)) (r s : Fin 4) :
    Fintype.card (BruhatActive σ r s) =
      ((Finset.Iic s).filter fun j => r ≤ σ j).card := by
  classical
  let activeFinset : Finset (Fin 4) := (Finset.Iic s).filter (fun k => r ≤ σ k)
  let e : BruhatActive σ r s ≃ ↥activeFinset :=
    { toFun := fun j => ⟨j.1.1, by simp [activeFinset, j.1.2, j.2]⟩
      invFun := fun j => ⟨⟨j.1, by
        simpa [activeFinset] using (Finset.mem_filter.1 j.2).1⟩, by
          simpa [activeFinset] using (Finset.mem_filter.1 j.2).2⟩
      left_inv := fun j => by rfl
      right_inv := fun j => by rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe activeFinset)

theorem fin4_perm_point_eq_of_bruhatActive_card_eq (σ τ : Equiv.Perm (Fin 4))
    (h : ∀ r s, Fintype.card (BruhatActive σ r s) =
      Fintype.card (BruhatActive τ r s)) (p : Fin 4)
    (hprev : ∀ j, j < p → σ j = τ j) : σ p = τ p := by
  have hpred : ∀ r : Fin 4, (r ≤ σ p ↔ r ≤ τ p) := by
    intro r
    have hc := h r p
    rw [card_bruhatActive, card_bruhatActive] at hc
    have hfilter : (Finset.Iio p).filter (fun j => r ≤ σ j) =
        (Finset.Iio p).filter (fun j => r ≤ τ j) := by
      apply Finset.filter_congr
      intro j hj
      rw [hprev j (Finset.mem_Iio.1 hj)]
    rw [Finset.Iic_eq_cons_Iio] at hc
    simp only [Finset.filter_cons] at hc
    have hcardfilter := congrArg Finset.card hfilter
    by_cases hs : r ≤ σ p <;> by_cases ht : r ≤ τ p <;>
      simp [hs, ht] at hc ⊢ <;> omega
  exact le_antisymm ((hpred (σ p)).1 le_rfl) ((hpred (τ p)).2 le_rfl)

theorem fin4_perm_eq_of_bruhatActive_card_eq (σ τ : Equiv.Perm (Fin 4))
    (h : ∀ r s, Fintype.card (BruhatActive σ r s) =
      Fintype.card (BruhatActive τ r s)) : σ = τ := by
  have h0 : σ 0 = τ 0 := fin4_perm_point_eq_of_bruhatActive_card_eq σ τ h 0 (by omega)
  have h1 : σ 1 = τ 1 := fin4_perm_point_eq_of_bruhatActive_card_eq σ τ h 1 (by
    intro j hj
    have : j = 0 := by apply Fin.ext; omega
    simpa [this] using h0)
  have h2 : σ 2 = τ 2 := fin4_perm_point_eq_of_bruhatActive_card_eq σ τ h 2 (by
    intro j hj
    fin_cases j <;> simp_all)
  have h3 : σ 3 = τ 3 := fin4_perm_point_eq_of_bruhatActive_card_eq σ τ h 3 (by
    intro j hj
    fin_cases j <;> simp_all)
  apply Equiv.ext
  intro p
  fin_cases p <;> assumption

def pivotPrefixBlock (A : Matrix (Fin 4) (Fin 4) F)
    (σ : Equiv.Perm (Fin 4)) (s : Fin 4) :
    Matrix (BruhatPrefix s) (BruhatPrefix s) F :=
  A.submatrix (fun j => σ j.1) Subtype.val

def permutedPrefixPrincipalBlock (U : Matrix (Fin 4) (Fin 4) F)
    (σ : Equiv.Perm (Fin 4)) (s : Fin 4) :
    Matrix (BruhatPrefix s) (BruhatPrefix s) F :=
  U.submatrix (fun j => σ j.1) (fun j => σ j.1)

def prefixImage (σ : Equiv.Perm (Fin 4)) (s : Fin 4) : Finset (Fin 4) :=
  (Finset.Iic s).image σ

noncomputable def prefixImageEquiv (σ : Equiv.Perm (Fin 4)) (s : Fin 4) :
    BruhatPrefix s ≃ ↥(prefixImage σ s) where
  toFun j := ⟨σ j.1, Finset.mem_image.2 ⟨j.1, Finset.mem_Iic.2 j.2, rfl⟩⟩
  invFun i := ⟨σ.symm i.1, by
    obtain ⟨j, hj, hσj⟩ := Finset.mem_image.1 i.2
    have : σ.symm i.1 = j := by rw [← hσj, σ.symm_apply_apply]
    simpa [this] using (Finset.mem_Iic.1 hj)⟩
  left_inv j := by apply Subtype.ext; simp
  right_inv i := by apply Subtype.ext; simp

def prefixImagePrincipalBlock (U : Matrix (Fin 4) (Fin 4) F)
    (σ : Equiv.Perm (Fin 4)) (s : Fin 4) :
    Matrix ↥(prefixImage σ s) ↥(prefixImage σ s) F :=
  U.submatrix Subtype.val Subtype.val

theorem prefixImagePrincipalBlock_det (U : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) (σ : Equiv.Perm (Fin 4)) (s : Fin 4) :
    (prefixImagePrincipalBlock U σ s).det = 1 := by
  classical
  rw [Matrix.det_of_upperTriangular (M := prefixImagePrincipalBlock U σ s) (by
    intro i j hji
    exact hU.1 i.1 j.1 hji)]
  simp [prefixImagePrincipalBlock, hU.2]

theorem permutedPrefixPrincipalBlock_det (U : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) (σ : Equiv.Perm (Fin 4)) (s : Fin 4) :
    (permutedPrefixPrincipalBlock U σ s).det = 1 := by
  classical
  let e := prefixImageEquiv σ s
  have hreindex : permutedPrefixPrincipalBlock U σ s =
      (prefixImagePrincipalBlock U σ s).submatrix e e := by
    rfl
  rw [hreindex, Matrix.det_submatrix_equiv_self, prefixImagePrincipalBlock_det U hU]

theorem pivotPrefixBlock_signedMonomial (σ : Equiv.Perm (Fin 4))
    (c : Fin 4 → Fˣ) (s : Fin 4) :
    pivotPrefixBlock (signedMonomialMatrix σ c) σ s =
      Matrix.diagonal (fun j : BruhatPrefix s => (c j.1 : F)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [pivotPrefixBlock, signedMonomialMatrix]
  · have hval : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp [pivotPrefixBlock, signedMonomialMatrix, hij, hval]

theorem pivotPrefixBlock_mul_right (A V : Matrix (Fin 4) (Fin 4) F)
    (hV : IsUpperUnipotent V) (σ : Equiv.Perm (Fin 4)) (s : Fin 4) :
    pivotPrefixBlock (A * V) σ s =
      pivotPrefixBlock A σ s * prefixPrincipalBlock V s := by
  classical
  ext i j
  simp only [pivotPrefixBlock, prefixPrincipalBlock, Matrix.submatrix_apply, Matrix.mul_apply]
  have hsum := Finset.sum_subset (s₁ := Finset.Iic s) (s₂ := Finset.univ)
    (Finset.subset_univ _) (f := fun k : Fin 4 => A (σ i.1) k * V k j.1) (by
      intro k _ hk
      rw [Finset.mem_Iic] at hk
      have hjk : j.1 < k := lt_of_not_ge fun hkj => hk (le_trans hkj j.2)
      rw [hV.1 k j.1 hjk, mul_zero])
  rw [← hsum]
  exact Finset.sum_subtype (Finset.Iic s) (by simp) _

theorem pivotPrefixBlock_mul_left_signedMonomial
    (U : Matrix (Fin 4) (Fin 4) F) (σ : Equiv.Perm (Fin 4))
    (c : Fin 4 → Fˣ) (s : Fin 4) :
    pivotPrefixBlock (U * signedMonomialMatrix σ c) σ s =
      permutedPrefixPrincipalBlock U σ s *
        pivotPrefixBlock (signedMonomialMatrix σ c) σ s := by
  classical
  ext i j
  simp only [pivotPrefixBlock, permutedPrefixPrincipalBlock, Matrix.submatrix_apply,
    Matrix.mul_apply, signedMonomialMatrix]
  rw [Finset.sum_eq_single (σ j.1)]
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro k _ hkj
      rw [if_neg (fun h => hkj (Subtype.ext (σ.injective h))), mul_zero]
    · simp
  · intro k _ hk
    rw [if_neg hk]
    exact mul_zero _
  · simp

theorem pivotPrefixBlock_upper_monomial_upper_det
    (U V : Matrix (Fin 4) (Fin 4) F) (hU : IsUpperUnipotent U)
    (hV : IsUpperUnipotent V) (σ : Equiv.Perm (Fin 4))
    (c : Fin 4 → Fˣ) (s : Fin 4) :
    (pivotPrefixBlock (U * signedMonomialMatrix σ c * V) σ s).det =
      ∏ j ∈ Finset.Iic s, (c j : F) := by
  rw [pivotPrefixBlock_mul_right _ _ hV,
    pivotPrefixBlock_mul_left_signedMonomial,
    pivotPrefixBlock_signedMonomial, Matrix.det_mul, Matrix.det_mul,
    permutedPrefixPrincipalBlock_det U hU, prefixPrincipalBlock_det V hV,
    Matrix.det_diagonal, one_mul, mul_one]
  exact (Finset.prod_subtype (Finset.Iic s) (by simp) (fun j => (c j : F))).symm

theorem southwestBlock_signedMonomial_rank (σ : Equiv.Perm (Fin 4))
    (c : Fin 4 → Fˣ) (r s : Fin 4) :
    (southwestBlock (signedMonomialMatrix σ c) r s).rank =
      Fintype.card (BruhatActive σ r s) := by
  classical
  let B := southwestBlock (signedMonomialMatrix σ c) r s
  let row : BruhatActive σ r s → BruhatSuffix r := fun j => ⟨σ j.1.1, j.2⟩
  have hrow : Function.Injective row := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact σ.injective (congrArg Subtype.val hab)
  have hcol (j : BruhatActive σ r s) :
      B.col j.1 = (c j.1.1 : F) • Pi.single (row j) 1 := by
    funext i
    simp only [B, southwestBlock, Matrix.col]
    by_cases h : i.1 = σ j.1.1
    · have hij : i = row j := Subtype.ext h
      change (if i.1 = σ j.1.1 then (c j.1.1 : F) else 0) = _
      simp [hij, row]
    · have hij : i ≠ row j := fun hij => h (congrArg Subtype.val hij)
      change (if i.1 = σ j.1.1 then (c j.1.1 : F) else 0) = _
      simp [h, hij]
  have hli : LinearIndependent F (fun j : BruhatActive σ r s => B.col j.1) := by
    have hbase := (Pi.linearIndependent_single_one (BruhatSuffix r) F).comp row hrow
    have hscaled := hbase.units_smul (fun j : BruhatActive σ r s => c j.1.1)
    rw [show (fun j : BruhatActive σ r s => B.col j.1) =
        (fun j : BruhatActive σ r s => (c j.1.1 : F) • Pi.single (row j) 1) by
      funext j
      exact hcol j]
    convert hscaled using 1
    funext j i
    simp [Pi.smul_apply, Units.smul_def]
  have hspan : Submodule.span F (Set.range B.col) =
      Submodule.span F (Set.range fun j : BruhatActive σ r s => B.col j.1) := by
    apply le_antisymm
    · apply Submodule.span_le.2
      rintro _ ⟨j, rfl⟩
      by_cases hj : r ≤ σ j.1
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
      · have hzero : B.col j = 0 := by
          funext i
          simp only [B, southwestBlock, Matrix.col, Pi.zero_apply]
          have hne : i.1 ≠ σ j.1 := by
            intro h
            exact hj (h ▸ i.2)
          change (if i.1 = σ j.1 then (c j.1 : F) else 0) = 0
          simp [hne]
        rw [hzero]
        exact Submodule.zero_mem _
    · apply Submodule.span_le.2
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j.1, rfl⟩
  rw [Matrix.rank_eq_finrank_span_cols, hspan, finrank_span_eq_card hli]

theorem fin4_bruhat_permutation_unique
    (U V U' V' : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) (hV : IsUpperUnipotent V)
    (hU' : IsUpperUnipotent U') (hV' : IsUpperUnipotent V')
    (σ τ : Equiv.Perm (Fin 4)) (c d : Fin 4 → Fˣ)
    (heq : U * signedMonomialMatrix σ c * V = U' * signedMonomialMatrix τ d * V') :
    σ = τ := by
  apply fin4_perm_eq_of_bruhatActive_card_eq
  intro r s
  rw [← southwestBlock_signedMonomial_rank σ c,
    ← southwestBlock_signedMonomial_rank τ d,
    ← southwestBlock_upper_monomial_upper_rank U V hU hV,
    ← southwestBlock_upper_monomial_upper_rank U' V' hU' hV', heq]

theorem fin4_bruhat_scales_unique_of_same_permutation
    (U V U' V' : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) (hV : IsUpperUnipotent V)
    (hU' : IsUpperUnipotent U') (hV' : IsUpperUnipotent V')
    (σ : Equiv.Perm (Fin 4)) (c d : Fin 4 → Fˣ)
    (heq : U * signedMonomialMatrix σ c * V = U' * signedMonomialMatrix σ d * V') :
    c = d := by
  have hprod : ∀ s : Fin 4, (∏ j ∈ Finset.Iic s, (c j : F)) =
      ∏ j ∈ Finset.Iic s, (d j : F) := by
    intro s
    calc
      (∏ j ∈ Finset.Iic s, (c j : F)) =
          (pivotPrefixBlock (U * signedMonomialMatrix σ c * V) σ s).det :=
        (pivotPrefixBlock_upper_monomial_upper_det U V hU hV σ c s).symm
      _ = (pivotPrefixBlock (U' * signedMonomialMatrix σ d * V') σ s).det := by rw [heq]
      _ = ∏ j ∈ Finset.Iic s, (d j : F) :=
        pivotPrefixBlock_upper_monomial_upper_det U' V' hU' hV' σ d s
  have hpoint (p : Fin 4) (hprev : ∀ j, j < p → c j = d j) : c p = d p := by
    apply Units.ext
    have hp := hprod p
    rw [Finset.Iic_eq_cons_Iio] at hp
    simp only [Finset.prod_cons] at hp
    have hlower : (∏ j ∈ Finset.Iio p, (c j : F)) =
        ∏ j ∈ Finset.Iio p, (d j : F) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact congrArg Units.val (hprev j (Finset.mem_Iio.1 hj))
    rw [hlower] at hp
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 (by
      intro j _
      exact Units.ne_zero (d j))) hp
  have h0 : c 0 = d 0 := hpoint 0 (by omega)
  have h1 : c 1 = d 1 := hpoint 1 (by
    intro j hj
    have : j = 0 := by apply Fin.ext; omega
    simpa [this] using h0)
  have h2 : c 2 = d 2 := hpoint 2 (by
    intro j hj
    fin_cases j <;> simp_all)
  have h3 : c 3 = d 3 := hpoint 3 (by
    intro j hj
    fin_cases j <;> simp_all)
  funext p
  fin_cases p <;> assumption

theorem fin4_bruhat_monomial_unique
    (U V U' V' : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) (hV : IsUpperUnipotent V)
    (hU' : IsUpperUnipotent U') (hV' : IsUpperUnipotent V')
    (σ τ : Equiv.Perm (Fin 4)) (c d : Fin 4 → Fˣ)
    (heq : U * signedMonomialMatrix σ c * V = U' * signedMonomialMatrix τ d * V') :
    signedMonomialMatrix σ c = signedMonomialMatrix τ d := by
  have hσ := fin4_bruhat_permutation_unique U V U' V' hU hV hU' hV' σ τ c d heq
  subst τ
  have hc := fin4_bruhat_scales_unique_of_same_permutation U V U' V'
    hU hV hU' hV' σ c d heq
  rw [hc]

theorem fin4_steinbergToGL_det_one (x : SteinbergGroup F (Fin 4)) :
    Matrix.det (((steinbergToGL x : (Matrix (Fin 4) (Fin 4) F)ˣ) :
      Matrix (Fin 4) (Fin 4) F)) = 1 := by
  obtain ⟨w, rfl⟩ := FinFourSteinbergRootWord.exists_eval x
  induction w with
  | one => simp [FinFourSteinbergRootWord.eval]
  | snoc w i j hij a ih =>
      simp only [FinFourSteinbergRootWord.eval, map_mul, Units.val_mul, Matrix.det_mul,
        ih, one_mul, steinbergToGL_x, elemUnit_val]
      exact Matrix.det_transvection_of_ne i j hij a

structure Fin4BruhatFactorization (A : elementaryGroup F (Fin 4)) where
  left : Matrix (Fin 4) (Fin 4) F
  middle : MilnorDiagonalExtension.fieldDetOneMonomialSubgroup (F := F)
  right : Matrix (Fin 4) (Fin 4) F
  left_upper : IsUpperUnipotent left
  right_upper : IsUpperUnipotent right
  eq_factor : (A.1 : Matrix (Fin 4) (Fin 4) F) = left * (middle.1 :
    Matrix (Fin 4) (Fin 4) F) * right

theorem exists_fin4BruhatFactorization (A : elementaryGroup F (Fin 4)) :
    Nonempty (Fin4BruhatFactorization A) := by
  obtain ⟨g, hg⟩ := A.2
  have hgTWT : g ∈ steinbergTWT (F := F) (n := Fin 4) := by
    rw [fin4_steinbergTWT_eq_top]
    exact Subgroup.mem_top g
  obtain ⟨t₁, w, t₂, ht₁, hw, ht₂, hdecomp⟩ := hgTWT
  rw [upperSteinbergSubgroup_fin4_eq_tetrahedron] at ht₁ ht₂
  obtain ⟨a₁, b₁, c₁, d₁, e₁, f₁, ht₁eq⟩ := ht₁
  obtain ⟨a₂, b₂, c₂, d₂, e₂, f₂, ht₂eq⟩ := ht₂
  obtain ⟨word, hword⟩ := SteinbergWeylWord.exists_of_mem_subgroup hw
  let middleUnit : (Matrix (Fin 4) (Fin 4) F)ˣ := steinbergToGL w
  have hmiddleMatrix : (middleUnit : Matrix (Fin 4) (Fin 4) F) =
      signedMonomialMatrix word.perm word.scale := by
    change (((steinbergToGL w : (Matrix (Fin 4) (Fin 4) F)ˣ) :
      Matrix (Fin 4) (Fin 4) F)) = _
    rw [← hword]
    exact steinbergWeylWord_matrix word
  let middle : MilnorDiagonalExtension.fieldDetOneMonomialSubgroup (F := F) :=
    ⟨middleUnit, ⟨⟨word.perm, word.scale, hmiddleMatrix⟩,
      fin4_steinbergToGL_det_one w⟩⟩
  refine ⟨{
    left := (steinbergToGL t₁ : (Matrix (Fin 4) (Fin 4) F)ˣ)
    middle := middle
    right := (steinbergToGL t₂ : (Matrix (Fin 4) (Fin 4) F)ˣ)
    left_upper := ?_
    right_upper := ?_
    eq_factor := ?_ }⟩
  · rw [ht₁eq]
    exact fin4_upper_tetrahedron_matrix_isUpper a₁ b₁ c₁ d₁ e₁ f₁
  · rw [ht₂eq]
    exact fin4_upper_tetrahedron_matrix_isUpper a₂ b₂ c₂ d₂ e₂ f₂
  · change (A.1 : Matrix (Fin 4) (Fin 4) F) =
      ((steinbergToGL t₁ : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) *
        ((steinbergToGL w : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) *
        ((steinbergToGL t₂ : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F)
    calc
      (A.1 : Matrix (Fin 4) (Fin 4) F) =
          ((steinbergToGL g : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F) :=
        congrArg Units.val hg.symm
      _ = _ := by rw [hdecomp, map_mul, map_mul, Units.val_mul, Units.val_mul]

theorem Fin4BruhatFactorization.middle_unique {A : elementaryGroup F (Fin 4)}
    (x y : Fin4BruhatFactorization A) : x.middle = y.middle := by
  obtain ⟨σ, c, hx⟩ := x.middle.2.1
  obtain ⟨τ, d, hy⟩ := y.middle.2.1
  apply Subtype.ext
  apply Units.ext
  rw [hx, hy]
  have heq := x.eq_factor.symm.trans y.eq_factor
  rw [hx, hy] at heq
  exact fin4_bruhat_monomial_unique x.left x.right y.left y.right
    x.left_upper x.right_upper y.left_upper y.right_upper σ τ c d
    heq

noncomputable def fin4BruhatFactorization (A : elementaryGroup F (Fin 4)) :
    Fin4BruhatFactorization A :=
  Classical.choice (exists_fin4BruhatFactorization A)

/-- Milnor's rank-four Bruhat retraction from elementary matrices to determinant-one monomials. -/
noncomputable def fin4BruhatProjection :
    elementaryGroup F (Fin 4) →
      MilnorDiagonalExtension.fieldDetOneMonomialSubgroup (F := F) :=
  fun A => (fin4BruhatFactorization A).middle

theorem fin4BruhatProjection_eq_middle {A : elementaryGroup F (Fin 4)}
    (x : Fin4BruhatFactorization A) :
    fin4BruhatProjection A = x.middle :=
  (fin4BruhatFactorization A).middle_unique x

theorem fin4BruhatProjection_factorization (A : elementaryGroup F (Fin 4)) :
    ∃ U V : Matrix (Fin 4) (Fin 4) F,
      IsUpperUnipotent U ∧ IsUpperUnipotent V ∧
      (A.1 : Matrix (Fin 4) (Fin 4) F) =
        U * ((fin4BruhatProjection A).1 : Matrix (Fin 4) (Fin 4) F) * V := by
  let x := fin4BruhatFactorization A
  exact ⟨x.left, x.right, x.left_upper, x.right_upper, x.eq_factor⟩

theorem fin4_elementaryGroup_det_one (A : elementaryGroup F (Fin 4)) :
    Matrix.det (A.1 : Matrix (Fin 4) (Fin 4) F) = 1 := by
  obtain ⟨x, hx⟩ := A.2
  rw [← hx]
  exact fin4_steinbergToGL_det_one x

open MilnorDiagonalExtension

/-- A determinant-one diagonal matrix, regarded as an elementary matrix. -/
noncomputable def fin4DiagonalElementary (u : detOneDiagonalUnits F 4) :
    elementaryGroup F (Fin 4) :=
  ⟨detOneDiagonalMatrixUnitHom u,
    unit_mem_elementaryGroup_of_det_eq_one _
      (detOneDiagonalToFieldMonomial u).2.2⟩

/-- Conjugating an upper-unipotent matrix by a determinant-one diagonal matrix preserves it. -/
theorem detOneDiagonal_conj_isUpperUnipotent
    (u : detOneDiagonalUnits F 4) (U : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) :
    IsUpperUnipotent
      (((detOneDiagonalMatrixUnitHom u : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F) * U *
        (((detOneDiagonalMatrixUnitHom u)⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F)) := by
  change IsUpperUnipotent
    (Matrix.diagonal (fun p => (u.1 p : F)) * U *
      Matrix.diagonal (fun p => (((u.1 p)⁻¹ : Fˣ) : F)))
  constructor
  · intro r s hsr
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hU.1 r s hsr, mul_zero, zero_mul]
  · intro r
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, hU.2 r]
    simp

/-- The inverse diagonal conjugation also preserves upper-unipotent matrices. -/
theorem detOneDiagonal_inv_conj_isUpperUnipotent
    (u : detOneDiagonalUnits F 4) (U : Matrix (Fin 4) (Fin 4) F)
    (hU : IsUpperUnipotent U) :
    IsUpperUnipotent
      ((((detOneDiagonalMatrixUnitHom u)⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F) * U *
        ((detOneDiagonalMatrixUnitHom u : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F)) := by
  simpa only [map_inv, inv_inv] using
    detOneDiagonal_conj_isUpperUnipotent (u := u⁻¹) U hU

/-- Milnor's Bruhat retraction is equivariant for diagonal multiplication on the left. -/
theorem fin4BruhatProjection_diagonal_mul
    (u : detOneDiagonalUnits F 4) (A : elementaryGroup F (Fin 4)) :
    fin4BruhatProjection (fin4DiagonalElementary u * A) =
      detOneDiagonalToFieldMonomial u * fin4BruhatProjection A := by
  let x := fin4BruhatFactorization A
  let D := detOneDiagonalMatrixUnitHom u
  let y : Fin4BruhatFactorization (fin4DiagonalElementary u * A) :=
    { left := (D : Matrix (Fin 4) (Fin 4) F) * x.left *
          ((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) : Matrix (Fin 4) (Fin 4) F)
      middle := detOneDiagonalToFieldMonomial u * x.middle
      right := x.right
      left_upper := by
        simpa only [D] using
          detOneDiagonal_conj_isUpperUnipotent u x.left x.left_upper
      right_upper := x.right_upper
      eq_factor := by
        change (D : Matrix (Fin 4) (Fin 4) F) *
            (A.1 : Matrix (Fin 4) (Fin 4) F) =
          ((D : Matrix (Fin 4) (Fin 4) F) * x.left *
              ((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
                Matrix (Fin 4) (Fin 4) F)) *
            ((D : Matrix (Fin 4) (Fin 4) F) *
              (x.middle.1 : Matrix (Fin 4) (Fin 4) F)) * x.right
        rw [x.eq_factor]
        have hcancel : ((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F) *
            (D : Matrix (Fin 4) (Fin 4) F) = 1 := by
          simpa only [Units.val_mul, Units.val_inv, Units.val_one] using
            congrArg Units.val (inv_mul_cancel D)
        have hcollapse (N : Matrix (Fin 4) (Fin 4) F) :
            ((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
                Matrix (Fin 4) (Fin 4) F) *
              ((D : Matrix (Fin 4) (Fin 4) F) * N) = N := by
          rw [← Matrix.mul_assoc, hcancel, one_mul]
        calc
          (D : Matrix (Fin 4) (Fin 4) F) *
              (x.left * (x.middle.1 : Matrix (Fin 4) (Fin 4) F) * x.right) =
              (D : Matrix (Fin 4) (Fin 4) F) * x.left *
                (x.middle.1 : Matrix (Fin 4) (Fin 4) F) * x.right := by
                  simp only [Matrix.mul_assoc]
          _ = ((D : Matrix (Fin 4) (Fin 4) F) * x.left *
                ((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
                  Matrix (Fin 4) (Fin 4) F)) *
              ((D : Matrix (Fin 4) (Fin 4) F) *
                (x.middle.1 : Matrix (Fin 4) (Fin 4) F)) * x.right := by
                  simp only [Matrix.mul_assoc]
                  rw [hcollapse] }
  exact fin4BruhatProjection_eq_middle y

/-- Milnor's Bruhat retraction is equivariant for diagonal multiplication on the right. -/
theorem fin4BruhatProjection_mul_diagonal
    (A : elementaryGroup F (Fin 4)) (u : detOneDiagonalUnits F 4) :
    fin4BruhatProjection (A * fin4DiagonalElementary u) =
      fin4BruhatProjection A * detOneDiagonalToFieldMonomial u := by
  let x := fin4BruhatFactorization A
  let D := detOneDiagonalMatrixUnitHom u
  let y : Fin4BruhatFactorization (A * fin4DiagonalElementary u) :=
    { left := x.left
      middle := x.middle * detOneDiagonalToFieldMonomial u
      right := ((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
          Matrix (Fin 4) (Fin 4) F) * x.right *
        (D : Matrix (Fin 4) (Fin 4) F)
      left_upper := x.left_upper
      right_upper := by
        simpa only [D] using
          detOneDiagonal_inv_conj_isUpperUnipotent u x.right x.right_upper
      eq_factor := by
        change (A.1 : Matrix (Fin 4) (Fin 4) F) *
            (D : Matrix (Fin 4) (Fin 4) F) =
          x.left * ((x.middle.1 : Matrix (Fin 4) (Fin 4) F) *
              (D : Matrix (Fin 4) (Fin 4) F)) *
            (((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
                Matrix (Fin 4) (Fin 4) F) * x.right *
              (D : Matrix (Fin 4) (Fin 4) F))
        rw [x.eq_factor]
        have hcancel : (D : Matrix (Fin 4) (Fin 4) F) *
            ((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
              Matrix (Fin 4) (Fin 4) F) = 1 := by
          simpa only [Units.val_mul, Units.val_inv, Units.val_one] using
            congrArg Units.val (mul_inv_cancel D)
        have hcollapse (N : Matrix (Fin 4) (Fin 4) F) :
            (D : Matrix (Fin 4) (Fin 4) F) *
              (((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
                Matrix (Fin 4) (Fin 4) F) * N) = N := by
          rw [← Matrix.mul_assoc, hcancel, one_mul]
        calc
          (x.left * (x.middle.1 : Matrix (Fin 4) (Fin 4) F) * x.right) *
              (D : Matrix (Fin 4) (Fin 4) F) =
              x.left * (x.middle.1 : Matrix (Fin 4) (Fin 4) F) *
                x.right * (D : Matrix (Fin 4) (Fin 4) F) := rfl
          _ = x.left * ((x.middle.1 : Matrix (Fin 4) (Fin 4) F) *
                (D : Matrix (Fin 4) (Fin 4) F)) *
              (((D⁻¹ : (Matrix (Fin 4) (Fin 4) F)ˣ) :
                  Matrix (Fin 4) (Fin 4) F) * x.right *
                (D : Matrix (Fin 4) (Fin 4) F)) := by
                  simp only [Matrix.mul_assoc]
                  rw [hcollapse] }
  exact fin4BruhatProjection_eq_middle y

/-- The Bruhat projection fixes every elementary matrix which is already monomial. -/
theorem fin4BruhatProjection_eq_self_of_monomial (A : elementaryGroup F (Fin 4))
    (hA : MilnorDiagonalExtension.IsFieldMonomialUnit A.1) :
    ((fin4BruhatProjection A).1 : Matrix (Fin 4) (Fin 4) F) =
      (A.1 : Matrix (Fin 4) (Fin 4) F) := by
  let middle : MilnorDiagonalExtension.fieldDetOneMonomialSubgroup (F := F) :=
    ⟨A.1, hA, fin4_elementaryGroup_det_one A⟩
  let x : Fin4BruhatFactorization A :=
    { left := 1
      middle := middle
      right := 1
      left_upper := by
        constructor
        · intro r s hsr
          simp [ne_of_gt hsr]
        · simp
      right_upper := by
        constructor
        · intro r s hsr
          simp [ne_of_gt hsr]
        · simp
      eq_factor := by simp [middle] }
  have hmiddle := fin4BruhatProjection_eq_middle x
  exact congrArg (fun m => (m.1 : Matrix (Fin 4) (Fin 4) F)) hmiddle

end GaloisForLFunctions.HTGeometry
