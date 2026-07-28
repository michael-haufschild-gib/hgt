import GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame
import GaloisForLFunctions.RHTower.KrylovNearestNeighborRealization
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Krylov Gram-prefix transfer

This module proves the dimension-independent algebraic bridge from shared
Krylov moments to shared canonical nearest-neighbour coefficients.  Two
linearly independent frames may live in different ambient spaces and have
different lengths.  If their leading Gram and shifted-Gram data agree, then
the corresponding canonical compressions agree on the whole common prefix.
-/

open scoped BigOperators InnerProductSpace ComplexOrder
open Complex Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Canonical frame vector obtained by applying the conjugated inverse
Cholesky coefficients to the original frame. -/
def canonicalInverseFrameVector
    {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (u : Fin N → E) (i : Fin N) : E :=
  ∑ j, star (C i j) • u j

/-- An inverse Cholesky factor converts a frame with Gram matrix `G` into an
orthonormal frame. -/
theorem canonicalInverseFrameVector_orthonormal
    {N : ℕ} (u : Fin N → E) (C : Matrix (Fin N) (Fin N) ℂ)
    (hC : IsInverseCholeskyFrame C (Matrix.gram ℂ u)) :
    Orthonormal ℂ (canonicalInverseFrameVector C u) := by
  rw [orthonormal_iff_ite]
  intro i j
  unfold canonicalInverseFrameVector
  let x : Fin N → ℂ := fun k => star (C i k)
  let y : Fin N → ℂ := fun k => star (C j k)
  change inner ℂ (∑ k, x k • u k) (∑ k, y k • u k) =
    if i = j then 1 else 0
  rw [← Matrix.star_dotProduct_gram_mulVec u x y]
  calc
    star x ⬝ᵥ Matrix.gram ℂ u *ᵥ y =
        (C * Matrix.gram ℂ u * Cᴴ) i j := by
      simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Pi.star_apply, x, y, star_star]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (1 : Matrix (Fin N) (Fin N) ℂ) i j := by
      exact congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) hC
    _ = if i = j then 1 else 0 := by
      rw [Matrix.one_apply]

/-- Canonical orthonormal frame determined only by a linearly independent
frame's Gram matrix. -/
def canonicalGramFrame
    {N : ℕ} (u : Fin N → E) (hli : LinearIndependent ℂ u)
    (i : Fin N) : E :=
  canonicalInverseFrameVector
    (gramSchmidtInverseFrame (Matrix.gram ℂ u)
      (Matrix.posDef_gram_of_linearIndependent hli))
    u i

/-- The canonical Gram frame is orthonormal. -/
theorem canonicalGramFrame_orthonormal
    {N : ℕ} (u : Fin N → E) (hli : LinearIndependent ℂ u) :
    Orthonormal ℂ (canonicalGramFrame u hli) := by
  apply canonicalInverseFrameVector_orthonormal
  exact gramSchmidtInverseFrame_isInverseCholeskyFrame _ _

/-- Equal Gram and shifted-Gram matrices force equal entries of the operators
compressed to their canonical Gram frames. -/
theorem canonicalCompressionEntry_eq_of_gram_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {N : ℕ}
    (u : Fin N → E) (v : Fin N → F)
    (hu : LinearIndependent ℂ u) (hv : LinearIndependent ℂ v)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hgram : Matrix.gram ℂ u = Matrix.gram ℂ v)
    (hshift : ∀ a b, inner ℂ (u a) (A (u b)) =
      inner ℂ (v a) (B (v b)))
    (i j : Fin N) :
    inner ℂ (canonicalGramFrame u hu i)
        (A (canonicalGramFrame u hu j)) =
      inner ℂ (canonicalGramFrame v hv i)
        (B (canonicalGramFrame v hv j)) := by
  let hGu := Matrix.posDef_gram_of_linearIndependent hu
  let hGv := Matrix.posDef_gram_of_linearIndependent hv
  let Cu := gramSchmidtInverseFrame (Matrix.gram ℂ u) hGu
  let Cv := gramSchmidtInverseFrame (Matrix.gram ℂ v) hGv
  have hC : Cu = Cv := by
    apply (gramSchmidtInverseFrame_eq_iff_gram_eq
      (Matrix.gram ℂ u) (Matrix.gram ℂ v) hGu hGv).2
    exact hgram
  change
    inner ℂ (canonicalInverseFrameVector Cu u i)
        (A (canonicalInverseFrameVector Cu u j)) =
      inner ℂ (canonicalInverseFrameVector Cv v i)
        (B (canonicalInverseFrameVector Cv v j))
  rw [hC]
  unfold canonicalInverseFrameVector
  simp_rw [map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, hshift]

/-- A single canonical compression entry uses only the corresponding leading
rectangle of shifted-Gram data.  This removes the spurious last corner
required by a square-prefix argument. -/
theorem canonicalCompressionEntry_eq_of_gram_eq_of_rectangle
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {N : ℕ}
    (u : Fin N → E) (v : Fin N → F)
    (hu : LinearIndependent ℂ u) (hv : LinearIndependent ℂ v)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hgram : Matrix.gram ℂ u = Matrix.gram ℂ v)
    (i j : Fin N)
    (hshift : ∀ a b, a ≤ i → b ≤ j →
      inner ℂ (u a) (A (u b)) =
        inner ℂ (v a) (B (v b))) :
    inner ℂ (canonicalGramFrame u hu i)
        (A (canonicalGramFrame u hu j)) =
      inner ℂ (canonicalGramFrame v hv i)
        (B (canonicalGramFrame v hv j)) := by
  let hGu := Matrix.posDef_gram_of_linearIndependent hu
  let hGv := Matrix.posDef_gram_of_linearIndependent hv
  let Cu := gramSchmidtInverseFrame (Matrix.gram ℂ u) hGu
  let Cv := gramSchmidtInverseFrame (Matrix.gram ℂ v) hGv
  have hC : Cu = Cv := by
    apply (gramSchmidtInverseFrame_eq_iff_gram_eq
      (Matrix.gram ℂ u) (Matrix.gram ℂ v) hGu hGv).2
    exact hgram
  change
    inner ℂ (canonicalInverseFrameVector Cu u i)
        (A (canonicalInverseFrameVector Cu u j)) =
      inner ℂ (canonicalInverseFrameVector Cv v i)
        (B (canonicalInverseFrameVector Cv v j))
  rw [hC]
  unfold canonicalInverseFrameVector
  simp_rw [map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hai : a ≤ i
  · apply Finset.sum_congr rfl
    intro b _hb
    by_cases hbj : b ≤ j
    · rw [hshift a b hai hbj]
    · have hzero : Cv j b = 0 := by
        apply gramSchmidtInverseFrame_lowerTriangular
          (Matrix.gram ℂ v) hGv
        exact lt_of_not_ge hbj
      rw [hzero]
      simp
  · have hzero : Cv i a = 0 := by
      apply gramSchmidtInverseFrame_lowerTriangular
        (Matrix.gram ℂ v) hGv
      exact lt_of_not_ge hai
    rw [hzero]
    simp

/-- Leading square submatrix selected by the canonical inclusion
`Fin m → Fin (m + k)`. -/
def leadingAddSubmatrix {m : ℕ} (k : ℕ)
    (M : Matrix (Fin (m + k)) (Fin (m + k)) ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  M.submatrix (Fin.castAdd k) (Fin.castAdd k)

/-- Inverse Cholesky Gram--Schmidt is coherent under every finite leading
principal restriction, not only a one-step restriction. -/
theorem gramSchmidtInverseFrame_leadingAdd
    {m : ℕ} (k : ℕ)
    (G : Matrix (Fin (m + k)) (Fin (m + k)) ℂ)
    (hG : G.PosDef) :
    leadingAddSubmatrix k (gramSchmidtInverseFrame G hG) =
      gramSchmidtInverseFrame (leadingAddSubmatrix k G)
        (hG.submatrix (Fin.castAdd_injective m k)) := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      let G' : Matrix (Fin (m + k)) (Fin (m + k)) ℂ :=
        leadingPrincipalSubmatrix G
      let hG' : G'.PosDef :=
        hG.submatrix (Fin.castSucc_injective (m + k))
      have hstep :=
        gramSchmidtInverseFrame_leadingPrincipal G hG
      calc
        leadingAddSubmatrix (k + 1) (gramSchmidtInverseFrame G hG) =
            leadingAddSubmatrix k
              (leadingPrincipalSubmatrix
                (gramSchmidtInverseFrame G hG)) := by
              ext i j
              rfl
        _ = leadingAddSubmatrix k
              (gramSchmidtInverseFrame G' hG') := by
              rw [hstep]
        _ = gramSchmidtInverseFrame
              (leadingAddSubmatrix k G')
              (hG'.submatrix (Fin.castAdd_injective m k)) := ih G' hG'
        _ = gramSchmidtInverseFrame
              (leadingAddSubmatrix (k + 1) G)
              (hG.submatrix (Fin.castAdd_injective m (k + 1))) := by
              congr 1

/-- Every leading vector of the full canonical Gram frame equals the
corresponding vector obtained by canonicalizing only the leading subframe. -/
theorem canonicalGramFrame_castAdd
    {m k : ℕ} (u : Fin (m + k) → E)
    (hu : LinearIndependent ℂ u) (i : Fin m) :
    canonicalGramFrame u hu (Fin.castAdd k i) =
      canonicalGramFrame (u ∘ Fin.castAdd k)
        (hu.comp (Fin.castAdd k) (Fin.castAdd_injective m k)) i := by
  let G := Matrix.gram ℂ u
  let hG := Matrix.posDef_gram_of_linearIndependent hu
  let C := gramSchmidtInverseFrame G hG
  let u₀ : Fin m → E := u ∘ Fin.castAdd k
  let hu₀ : LinearIndependent ℂ u₀ :=
    hu.comp (Fin.castAdd k) (Fin.castAdd_injective m k)
  let G₀ := Matrix.gram ℂ u₀
  let hG₀ := Matrix.posDef_gram_of_linearIndependent hu₀
  let C₀ := gramSchmidtInverseFrame G₀ hG₀
  have hC : leadingAddSubmatrix k C = C₀ := by
    exact gramSchmidtInverseFrame_leadingAdd k G hG
  change canonicalInverseFrameVector C u (Fin.castAdd k i) =
    canonicalInverseFrameVector C₀ u₀ i
  unfold canonicalInverseFrameVector
  rw [Fin.sum_univ_add]
  have htail :
      (∑ j : Fin k,
        star (C (Fin.castAdd k i) (Fin.natAdd m j)) •
          u (Fin.natAdd m j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _hj
    have hzero : C (Fin.castAdd k i) (Fin.natAdd m j) = 0 := by
      apply gramSchmidtInverseFrame_lowerTriangular G hG
      change (i : ℕ) < m + (j : ℕ)
      omega
    rw [hzero, star_zero, zero_smul]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [← hC]
  rfl

/-- Dimension-independent prefix transfer: equal leading Gram and shifted-Gram
data force identical canonical compression entries throughout the common
prefix, even when frame lengths and ambient spaces differ. -/
theorem canonicalCompressionPrefix_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {m k l : ℕ}
    (u : Fin (m + k) → E) (v : Fin (m + l) → F)
    (hu : LinearIndependent ℂ u) (hv : LinearIndependent ℂ v)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hgram :
      Matrix.gram ℂ (u ∘ Fin.castAdd k) =
        Matrix.gram ℂ (v ∘ Fin.castAdd l))
    (hshift : ∀ a b : Fin m,
      inner ℂ (u (Fin.castAdd k a)) (A (u (Fin.castAdd k b))) =
        inner ℂ (v (Fin.castAdd l a)) (B (v (Fin.castAdd l b))))
    (i j : Fin m) :
    inner ℂ (canonicalGramFrame u hu (Fin.castAdd k i))
        (A (canonicalGramFrame u hu (Fin.castAdd k j))) =
      inner ℂ (canonicalGramFrame v hv (Fin.castAdd l i))
        (B (canonicalGramFrame v hv (Fin.castAdd l j))) := by
  rw [canonicalGramFrame_castAdd u hu i,
    canonicalGramFrame_castAdd u hu j,
    canonicalGramFrame_castAdd v hv i,
    canonicalGramFrame_castAdd v hv j]
  apply canonicalCompressionEntry_eq_of_gram_eq
  · exact hgram
  · exact hshift

/-- Dimension-independent entrywise prefix transfer from only the shifted
rectangle that can contribute to the requested entry. -/
theorem canonicalCompressionPrefixEntry_eq_of_rectangle
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {m k l : ℕ}
    (u : Fin (m + k) → E) (v : Fin (m + l) → F)
    (hu : LinearIndependent ℂ u) (hv : LinearIndependent ℂ v)
    (A : E →L[ℂ] E) (B : F →L[ℂ] F)
    (hgram :
      Matrix.gram ℂ (u ∘ Fin.castAdd k) =
        Matrix.gram ℂ (v ∘ Fin.castAdd l))
    (i j : Fin m)
    (hshift : ∀ a b : Fin m, a ≤ i → b ≤ j →
      inner ℂ (u (Fin.castAdd k a)) (A (u (Fin.castAdd k b))) =
        inner ℂ (v (Fin.castAdd l a)) (B (v (Fin.castAdd l b)))) :
    inner ℂ (canonicalGramFrame u hu (Fin.castAdd k i))
        (A (canonicalGramFrame u hu (Fin.castAdd k j))) =
      inner ℂ (canonicalGramFrame v hv (Fin.castAdd l i))
        (B (canonicalGramFrame v hv (Fin.castAdd l j))) := by
  rw [canonicalGramFrame_castAdd u hu i,
    canonicalGramFrame_castAdd u hu j,
    canonicalGramFrame_castAdd v hv i,
    canonicalGramFrame_castAdd v hv j]
  apply canonicalCompressionEntry_eq_of_gram_eq_of_rectangle
    (i := i) (j := j)
  · exact hgram
  · exact hshift

/-- The canonical Gram frame spans exactly the same finite subspace as the
original linearly independent frame. -/
theorem span_canonicalGramFrame_eq
    {N : ℕ} (u : Fin N → E) (hu : LinearIndependent ℂ u) :
    Submodule.span ℂ (Set.range (canonicalGramFrame u hu)) =
      Submodule.span ℂ (Set.range u) := by
  letI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range u)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    unfold canonicalGramFrame canonicalInverseFrameVector
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_range_self j))
  · rw [finrank_span_eq_card
        (canonicalGramFrame_orthonormal u hu).linearIndependent,
      finrank_span_eq_card hu]

/-- The `i`th canonical vector uses only original frame vectors with index at
most `i`. -/
theorem canonicalGramFrame_mem_span_Iic
    {N : ℕ} (u : Fin N → E) (hu : LinearIndependent ℂ u)
    (i : Fin N) :
    canonicalGramFrame u hu i ∈
      Submodule.span ℂ (u '' Set.Iic i) := by
  let G := Matrix.gram ℂ u
  let hG := Matrix.posDef_gram_of_linearIndependent hu
  let C := gramSchmidtInverseFrame G hG
  unfold canonicalGramFrame canonicalInverseFrameVector
  apply Submodule.sum_mem
  intro j _hj
  by_cases hji : j ≤ i
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, hji, rfl⟩)
  · have hzero : C i j = 0 := by
      apply gramSchmidtInverseFrame_lowerTriangular G hG
      exact lt_of_not_ge hji
    change star (C i j) • u j ∈ Submodule.span ℂ (u '' Set.Iic i)
    rw [hzero, star_zero, zero_smul]
    exact Submodule.zero_mem _

/-- The first canonical vector differs from the first input vector only by a
unit scalar whenever the latter is normalized. -/
theorem canonicalGramFrame_zero_phase
    {N : ℕ} [NeZero N]
    (u : Fin N → E) (hu : LinearIndependent ℂ u)
    (hu0 : ‖u 0‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      canonicalGramFrame u hu 0 = c • u 0 := by
  have hmem :=
    canonicalGramFrame_mem_span_Iic u hu (0 : Fin N)
  have hiic : Set.Iic (0 : Fin N) = {0} := by
    ext j
    simp
  rw [hiic, Set.image_singleton] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hq0 :
      ‖canonicalGramFrame u hu 0‖ = 1 :=
    (canonicalGramFrame_orthonormal u hu).norm_eq_one 0
  have hcNorm : ‖c‖ = 1 := by
    rw [← hc, norm_smul, hu0] at hq0
    simpa using hq0
  exact ⟨c, hcNorm, hc.symm⟩

/-- At every prefix, canonicalization preserves the spanned subspace
exactly. -/
theorem span_canonicalGramFrame_Iic_eq
    {N : ℕ} (u : Fin N → E) (hu : LinearIndependent ℂ u)
    (i : Fin N) :
    Submodule.span ℂ (canonicalGramFrame u hu '' Set.Iic i) =
      Submodule.span ℂ (u '' Set.Iic i) := by
  let q := canonicalGramFrame u hu
  let q₀ : ↥(Set.Iic i) → E := fun j => q j
  let u₀ : ↥(Set.Iic i) → E := fun j => u j
  have hqrange : Set.range q₀ = q '' Set.Iic i := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hurange : Set.range u₀ = u '' Set.Iic i := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.property, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
  have hqli : LinearIndependent ℂ q₀ :=
    (canonicalGramFrame_orthonormal u hu).linearIndependent.comp
      Subtype.val Subtype.val_injective
  have huli : LinearIndependent ℂ u₀ :=
    hu.comp Subtype.val Subtype.val_injective
  letI : FiniteDimensional ℂ
      (Submodule.span ℂ (u '' Set.Iic i)) :=
    FiniteDimensional.span_of_finite ℂ (Set.toFinite _)
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [Submodule.span_le]
    intro x hx
    obtain ⟨j, hji, rfl⟩ := hx
    exact (Submodule.span_mono
      (Set.image_mono (Set.Iic_subset_Iic.2 hji)))
      (canonicalGramFrame_mem_span_Iic u hu j)
  · rw [← hqrange, ← hurange,
      finrank_span_eq_card hqli, finrank_span_eq_card huli]

/-- Later canonical vectors are orthogonal to every earlier original frame
vector. -/
theorem inner_canonicalGramFrame_original_eq_zero_of_lt
    {N : ℕ} (u : Fin N → E) (hu : LinearIndependent ℂ u)
    {j i : Fin N} (hji : j < i) :
    inner ℂ (canonicalGramFrame u hu i) (u j) = 0 := by
  have huj :
      u j ∈ Submodule.span ℂ
        (canonicalGramFrame u hu '' Set.Iic j) := by
    rw [span_canonicalGramFrame_Iic_eq u hu j]
    exact Submodule.subset_span
      ⟨j, by simp, rfl⟩
  refine Submodule.span_induction
    (p := fun x _ => inner ℂ (canonicalGramFrame u hu i) x = 0)
    ?_ ?_ ?_ ?_ huj
  · intro x hx
    obtain ⟨k, hkj, rfl⟩ := hx
    have hki : i ≠ k := (hkj.trans_lt hji).ne'
    simpa [hki] using
      (orthonormal_iff_ite.mp
        (canonicalGramFrame_orthonormal u hu) i k)
  · simp
  · intro x y _hx _hy hx hy
    simp [hx, hy]
  · intro c x _hx hx
    simp [hx]

end GaloisForLFunctions.HTGeometry

namespace RHTower.ParityForecast

open GaloisForLFunctions.HTGeometry

/-- Gram entries of a finite diagonal Krylov family are the corresponding
weighted spectral moments. -/
theorem finiteKrylovVector_inner
    {r : ℕ} (energy weight : Fin r → ℝ)
    (hw : ∀ x, 0 ≤ weight x) (a b : Fin r) :
    inner ℂ (finiteKrylovVector energy weight a)
        (finiteKrylovVector energy weight b) =
      (∑ x : Fin r, weight x *
        energy x ^ ((a : ℕ) + (b : ℕ)) : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro x _hx
  simp only [finiteKrylovVector_apply]
  have ha :
      (finiteKrylovVector energy weight a).ofLp x =
        ((energy x : ℂ) ^ (a : ℕ)) *
          (Real.sqrt (weight x) : ℂ) :=
    finiteKrylovVector_apply energy weight a x
  rw [Pi.star_apply, ha]
  simp only [map_mul, map_pow, Complex.star_def, Complex.conj_ofReal]
  have hs :
      (weight x : ℂ) =
        (Real.sqrt (weight x) : ℂ) *
          (Real.sqrt (weight x) : ℂ) := by
    norm_cast
    simpa [pow_two] using (Real.sq_sqrt (hw x)).symm
  rw [hs]
  ring

/-- Shifted Gram entries of a finite diagonal Krylov family are the next
weighted spectral moments. -/
theorem finiteKrylovVector_shift_inner
    {r : ℕ} (energy weight : Fin r → ℝ)
    (hw : ∀ x, 0 ≤ weight x) (a b : Fin r) :
    inner ℂ (finiteKrylovVector energy weight a)
        (finiteIndexDiagonalHamiltonian energy
          (finiteKrylovVector energy weight b)) =
      (∑ x : Fin r, weight x *
        energy x ^ ((a : ℕ) + (b : ℕ) + 1) : ℝ) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  push_cast
  apply Finset.sum_congr rfl
  intro x _hx
  rw [finiteIndexDiagonalHamiltonian_apply]
  simp only [finiteKrylovVector_apply]
  have ha :
      (finiteKrylovVector energy weight a).ofLp x =
        ((energy x : ℂ) ^ (a : ℕ)) *
          (Real.sqrt (weight x) : ℂ) :=
    finiteKrylovVector_apply energy weight a x
  rw [Pi.star_apply, ha]
  simp only [map_mul, map_pow, Complex.star_def, Complex.conj_ofReal]
  have hs :
      (weight x : ℂ) =
        (Real.sqrt (weight x) : ℂ) *
          (Real.sqrt (weight x) : ℂ) := by
    norm_cast
    simpa [pow_two] using (Real.sq_sqrt (hw x)).symm
  rw [hs]
  ring

/-- The diagonal Hamiltonian advances every nonterminal Krylov vector by one
power. -/
theorem finiteKrylovVector_succ
    {r : ℕ} (energy weight : Fin r → ℝ) {k : Fin r}
    (hk : (k : ℕ) + 1 < r) :
    finiteIndexDiagonalHamiltonian energy
        (finiteKrylovVector energy weight k) =
      finiteKrylovVector energy weight
        ⟨(k : ℕ) + 1, hk⟩ := by
  ext j
  simp only [finiteIndexDiagonalHamiltonian_apply,
    finiteKrylovVector_apply]
  ring

/-- In the canonical Gram frame, a diagonal finite spectral Hamiltonian has
no matrix entries above the first superdiagonal. -/
theorem canonicalKrylovFrame_upper_entry_zero
    {r : ℕ} {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    {i j : Fin r} (hji : (j : ℕ) + 1 < (i : ℕ)) :
    inner ℂ
        (canonicalGramFrame
          (finiteKrylovVector energy weight)
          (finiteKrylovVector_linearIndependent henergy hweight) i)
        (finiteIndexDiagonalHamiltonian energy
          (canonicalGramFrame
            (finiteKrylovVector energy weight)
            (finiteKrylovVector_linearIndependent henergy hweight) j)) =
      0 := by
  let f := finiteKrylovVector energy weight
  let hli : LinearIndependent ℂ f :=
    finiteKrylovVector_linearIndependent henergy hweight
  let b := canonicalGramFrame f hli
  have hbspan : b j ∈ Submodule.span ℂ (f '' Set.Iic j) :=
    canonicalGramFrame_mem_span_Iic f hli j
  refine Submodule.span_induction
    (p := fun x _ =>
      inner ℂ (b i) (finiteIndexDiagonalHamiltonian energy x) = 0)
    ?_ ?_ ?_ ?_ hbspan
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := hx
    have hkn : (k : ℕ) + 1 < r := by
      have hkj : (k : ℕ) ≤ (j : ℕ) := hk
      omega
    let ks : Fin r := ⟨(k : ℕ) + 1, hkn⟩
    have hksi : ks < i := by
      change (k : ℕ) + 1 < (i : ℕ)
      have hkj : (k : ℕ) ≤ (j : ℕ) := hk
      omega
    rw [finiteKrylovVector_succ energy weight hkn]
    exact inner_canonicalGramFrame_original_eq_zero_of_lt
      f hli hksi
  · simp
  · intro x y _hx _hy hx hy
    simp [hx, hy]
  · intro c x _hx hx
    simp [hx]

/-- Canonical compression matrix of a finite diagonal spectral
Hamiltonian. -/
def canonicalKrylovCompression
    {r : ℕ} (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun i j =>
    inner ℂ
      (canonicalGramFrame
        (finiteKrylovVector energy weight)
        (finiteKrylovVector_linearIndependent henergy hweight) i)
      (finiteIndexDiagonalHamiltonian energy
        (canonicalGramFrame
          (finiteKrylovVector energy weight)
          (finiteKrylovVector_linearIndependent henergy hweight) j))

/-- The canonical Gram frame is a basis of the full finite clock space. -/
def canonicalKrylovBasis {r : ℕ}
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    OrthonormalBasis (Fin r) ℂ (FiniteIndexClockSpace (Fin r)) :=
  OrthonormalBasis.mk
    (canonicalGramFrame_orthonormal
      (finiteKrylovVector energy weight)
      (finiteKrylovVector_linearIndependent henergy hweight))
    (by
      rw [span_canonicalGramFrame_eq]
      have htop :
          Submodule.span ℂ
              (Set.range (finiteKrylovVector energy weight)) = ⊤ :=
        LinearIndependent.span_eq_top_of_card_eq_finrank'
          (finiteKrylovVector_linearIndependent henergy hweight)
          (by simp [FiniteIndexClockSpace])
      exact htop.ge)

@[simp] theorem canonicalKrylovBasis_apply {r : ℕ}
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (i : Fin r) :
    canonicalKrylovBasis energy weight henergy hweight i =
      canonicalGramFrame
        (finiteKrylovVector energy weight)
        (finiteKrylovVector_linearIndependent henergy hweight) i := by
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

/-- Fixed-coordinate unitary whose columns are the canonical Krylov basis. -/
def canonicalKrylovUnitary {r : ℕ}
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    FiniteIndexClockSpace (Fin r) ≃ₗᵢ[ℂ]
      FiniteIndexClockSpace (Fin r) :=
  (EuclideanSpace.basisFun (Fin r) ℂ).equiv
    (canonicalKrylovBasis energy weight henergy hweight)
    (Equiv.refl (Fin r))

@[simp] theorem canonicalKrylovUnitary_basis {r : ℕ}
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (i : Fin r) :
    canonicalKrylovUnitary energy weight henergy hweight
        (EuclideanSpace.basisFun (Fin r) ℂ i) =
      canonicalGramFrame
        (finiteKrylovVector energy weight)
        (finiteKrylovVector_linearIndependent henergy hweight) i := by
  rw [canonicalKrylovUnitary, OrthonormalBasis.equiv_apply_basis,
    canonicalKrylovBasis_apply]
  rfl

/-- The standard endpoint is transported to the normalized spectral weight
ket up to an irrelevant global unit phase. -/
theorem canonicalKrylovUnitary_zero_phase
    {r : ℕ} [NeZero r]
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (hweightSum : ∑ j, weight j = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧
      canonicalKrylovUnitary energy weight henergy hweight
          (EuclideanSpace.basisFun (Fin r) ℂ 0) =
        c • finiteIndexWeightKet weight := by
  have hket :
      ‖finiteIndexWeightKet weight‖ = 1 :=
    finiteIndexWeightKet_norm_eq_one weight
      (fun j => (hweight j).le) hweightSum
  have hkrylov0 :
      ‖finiteKrylovVector energy weight 0‖ = 1 := by
    simpa [finiteKrylovVector] using hket
  obtain ⟨c, hc, hphase⟩ :=
    canonicalGramFrame_zero_phase
      (finiteKrylovVector energy weight)
      (finiteKrylovVector_linearIndependent henergy hweight)
      hkrylov0
  refine ⟨c, hc, ?_⟩
  rw [canonicalKrylovUnitary_basis]
  simpa [finiteKrylovVector] using hphase

/-- Diagonal spectral dynamics transported to fixed path coordinates through
the canonical Krylov unitary. -/
def canonicalKrylovPathHamiltonian {r : ℕ}
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    FiniteIndexClockSpace (Fin r) →L[ℂ]
      FiniteIndexClockSpace (Fin r) :=
  let U := canonicalKrylovUnitary energy weight henergy hweight
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    finiteIndexDiagonalHamiltonian energy ∘L
      U.toContinuousLinearEquiv.toContinuousLinearMap

/-- Transport a phased spectral state to the fixed path coordinates, allowing
for the harmless global phase of the canonical endpoint vector. -/
def canonicalKrylovPathState {r : ℕ}
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (c : ℂ) (x : FiniteIndexClockSpace (Fin r)) :
    FiniteIndexClockSpace (Fin r) :=
  (canonicalKrylovUnitary energy weight henergy hweight).symm (c • x)

/-- Endpoint return probability of a transported spectral state. -/
def canonicalKrylovPathReturnProbability {r : ℕ} [NeZero r]
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (c : ℂ) (x : FiniteIndexClockSpace (Fin r)) : ℝ :=
  ‖inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ 0)
      (canonicalKrylovPathState energy weight
        henergy hweight c x)‖ ^ 2

/-- A common unit phase cancels from every survival amplitude after canonical
transport. -/
theorem canonicalKrylovPathState_survivalAmplitude
    {r : ℕ} [NeZero r]
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (c : ℂ) (hc : ‖c‖ = 1)
    (x₀ x : FiniteIndexClockSpace (Fin r))
    (hzero :
      canonicalKrylovUnitary energy weight henergy hweight
          (EuclideanSpace.basisFun (Fin r) ℂ 0) =
        c • x₀) :
    inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ 0)
        (canonicalKrylovPathState energy weight
          henergy hweight c x) =
      inner ℂ x₀ x := by
  let U := canonicalKrylovUnitary energy weight henergy hweight
  have hcc : star c * c = 1 := by
    change (starRingEnd ℂ) c * c = 1
    rw [← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hc]
    norm_num
  calc
    inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ 0)
        (canonicalKrylovPathState energy weight
          henergy hweight c x) =
      inner ℂ
        (U (EuclideanSpace.basisFun (Fin r) ℂ 0))
        (c • x) := by
          symm
          simpa [canonicalKrylovPathState, U] using
            U.inner_map_map
              (EuclideanSpace.basisFun (Fin r) ℂ 0)
              (U.symm (c • x))
    _ = inner ℂ (c • x₀) (c • x) := by rw [hzero]
    _ = inner ℂ x₀ x := by
      rw [inner_smul_left, inner_smul_right]
      calc
        star c * (c * inner ℂ x₀ x) =
            (star c * c) * inner ℂ x₀ x := by ring
        _ = inner ℂ x₀ x := by rw [hcc, one_mul]

/-- Canonical transport preserves the endpoint return probability exactly. -/
theorem canonicalKrylovPathReturnProbability_eq
    {r : ℕ} [NeZero r]
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (c : ℂ) (hc : ‖c‖ = 1)
    (x₀ x : FiniteIndexClockSpace (Fin r))
    (hzero :
      canonicalKrylovUnitary energy weight henergy hweight
          (EuclideanSpace.basisFun (Fin r) ℂ 0) =
        c • x₀) :
    canonicalKrylovPathReturnProbability energy weight
        henergy hweight c x =
      ‖inner ℂ x₀ x‖ ^ 2 := by
  rw [canonicalKrylovPathReturnProbability,
    canonicalKrylovPathState_survivalAmplitude
      energy weight henergy hweight c hc x₀ x hzero]

/-- The canonical path Hamiltonian is self-adjoint. -/
theorem canonicalKrylovPathHamiltonian_selfAdjoint
    {r : ℕ} (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    ContinuousLinearMap.adjoint
        (canonicalKrylovPathHamiltonian energy weight henergy hweight) =
      canonicalKrylovPathHamiltonian energy weight henergy hweight := by
  let U := canonicalKrylovUnitary energy weight henergy hweight
  simp only [canonicalKrylovPathHamiltonian,
    ContinuousLinearMap.adjoint_comp]
  rw [LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.adjoint_eq_symm,
    finiteIndexDiagonalHamiltonian_selfAdjoint]
  rw [LinearIsometryEquiv.symm_symm]
  rw [ContinuousLinearMap.comp_assoc]

/-- Exact intertwining with the diagonal realization, hence exact
isospectrality. -/
@[simp] theorem canonicalKrylovPathHamiltonian_intertwines
    {r : ℕ} (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (x : FiniteIndexClockSpace (Fin r)) :
    canonicalKrylovUnitary energy weight henergy hweight
        (canonicalKrylovPathHamiltonian energy weight
          henergy hweight x) =
      finiteIndexDiagonalHamiltonian energy
        (canonicalKrylovUnitary energy weight henergy hweight x) := by
  simp [canonicalKrylovPathHamiltonian]

/-- Matrix entries of the transported path Hamiltonian are exactly the
canonical compression coefficients. -/
theorem canonicalKrylovPathHamiltonian_entry {r : ℕ}
    (energy weight : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j)
    (i j : Fin r) :
    inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ i)
        (canonicalKrylovPathHamiltonian energy weight henergy hweight
          (EuclideanSpace.basisFun (Fin r) ℂ j)) =
      canonicalKrylovCompression energy weight
        henergy hweight i j := by
  let U := canonicalKrylovUnitary energy weight henergy hweight
  have htransport :
      U (canonicalKrylovPathHamiltonian energy weight henergy hweight
          (EuclideanSpace.basisFun (Fin r) ℂ j)) =
        finiteIndexDiagonalHamiltonian energy
          (U (EuclideanSpace.basisFun (Fin r) ℂ j)) := by
    simp [canonicalKrylovPathHamiltonian, U]
  calc
    inner ℂ (EuclideanSpace.basisFun (Fin r) ℂ i)
        (canonicalKrylovPathHamiltonian energy weight henergy hweight
          (EuclideanSpace.basisFun (Fin r) ℂ j)) =
      inner ℂ (U (EuclideanSpace.basisFun (Fin r) ℂ i))
        (U (canonicalKrylovPathHamiltonian energy weight henergy hweight
          (EuclideanSpace.basisFun (Fin r) ℂ j))) := by
            symm
            exact U.inner_map_map _ _
    _ = canonicalKrylovCompression energy weight
          henergy hweight i j := by
      rw [htransport,
        canonicalKrylovUnitary_basis,
        canonicalKrylovUnitary_basis]
      rfl

/-- The canonical compression of every finite positive spectral packet is a
nearest-neighbour path matrix. -/
theorem canonicalKrylovCompression_nearestNeighbor
    {r : ℕ} {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    ∀ i j : Fin r,
      ((i : ℕ) + 1 < (j : ℕ) ∨
        (j : ℕ) + 1 < (i : ℕ)) →
      canonicalKrylovCompression energy weight henergy hweight i j = 0 := by
  intro i j hij
  rcases hij with hij | hji
  · have hzero :=
      canonicalKrylovFrame_upper_entry_zero henergy hweight hij
    have hadj :=
      ContinuousLinearMap.adjoint_inner_right
        (finiteIndexDiagonalHamiltonian energy)
        (canonicalGramFrame
          (finiteKrylovVector energy weight)
          (finiteKrylovVector_linearIndependent henergy hweight) i)
        (canonicalGramFrame
          (finiteKrylovVector energy weight)
          (finiteKrylovVector_linearIndependent henergy hweight) j)
    rw [finiteIndexDiagonalHamiltonian_selfAdjoint] at hadj
    change
      inner ℂ
        (canonicalGramFrame
          (finiteKrylovVector energy weight)
          (finiteKrylovVector_linearIndependent henergy hweight) i)
        (finiteIndexDiagonalHamiltonian energy
          (canonicalGramFrame
            (finiteKrylovVector energy weight)
            (finiteKrylovVector_linearIndependent henergy hweight) j)) =
        0
    calc
      _ =
          inner ℂ
            (finiteIndexDiagonalHamiltonian energy
              (canonicalGramFrame
                (finiteKrylovVector energy weight)
                (finiteKrylovVector_linearIndependent henergy hweight) i))
          (canonicalGramFrame
            (finiteKrylovVector energy weight)
            (finiteKrylovVector_linearIndependent henergy hweight) j) := hadj
      _ = starRingEnd ℂ
          (inner ℂ
            (canonicalGramFrame
              (finiteKrylovVector energy weight)
              (finiteKrylovVector_linearIndependent henergy hweight) j)
            (finiteIndexDiagonalHamiltonian energy
              (canonicalGramFrame
                (finiteKrylovVector energy weight)
                (finiteKrylovVector_linearIndependent henergy hweight) i))) := by
            symm
            exact inner_conj_symm _ _
      _ = 0 := by rw [hzero]; simp
  · exact canonicalKrylovFrame_upper_entry_zero
      henergy hweight hji

/-- The transported canonical Hamiltonian is nearest-neighbour in the fixed
standard coordinates. -/
theorem canonicalKrylovPathHamiltonian_nearestNeighbor
    {r : ℕ} {energy weight : Fin r → ℝ}
    (henergy : Function.Injective energy)
    (hweight : ∀ j, 0 < weight j) :
    NearestNeighborHamiltonian
      (canonicalKrylovPathHamiltonian energy weight henergy hweight) := by
  intro i j hij
  rw [canonicalKrylovPathHamiltonian_entry]
  exact canonicalKrylovCompression_nearestNeighbor
    henergy hweight i j hij

/-- Matching moments through degree `2R+2` fixes every canonical Hamiltonian
entry whose indices lie in the first `R+2` Krylov sites and whose shifted
degree does not exceed that bound.  In particular this includes all onsite
terms through radius `R` and all bonds through the exit bond `R ↔ R+1`. -/
theorem canonicalKrylovCompression_local_eq_of_moments
    {R k : ℕ}
    (energy weight₁ weight₂ : Fin ((R + 2) + k) → ℝ)
    (henergy : Function.Injective energy)
    (hweight₁ : ∀ x, 0 < weight₁ x)
    (hweight₂ : ∀ x, 0 < weight₂ x)
    (hmoment : ∀ d : ℕ, d ≤ 2 * R + 2 →
      (∑ x, weight₁ x * energy x ^ d) =
        ∑ x, weight₂ x * energy x ^ d)
    (i j : Fin (R + 2))
    (hdegree : (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2) :
    canonicalKrylovCompression energy weight₁
        henergy hweight₁ (Fin.castAdd k i) (Fin.castAdd k j) =
      canonicalKrylovCompression energy weight₂
        henergy hweight₂ (Fin.castAdd k i) (Fin.castAdd k j) := by
  apply canonicalCompressionPrefixEntry_eq_of_rectangle
    (u := finiteKrylovVector energy weight₁)
    (v := finiteKrylovVector energy weight₂)
    (hu := finiteKrylovVector_linearIndependent henergy hweight₁)
    (hv := finiteKrylovVector_linearIndependent henergy hweight₂)
    (A := finiteIndexDiagonalHamiltonian energy)
    (B := finiteIndexDiagonalHamiltonian energy)
    (i := i) (j := j)
  · ext a b
    change
      inner ℂ
          (finiteKrylovVector energy weight₁ (Fin.castAdd k a))
          (finiteKrylovVector energy weight₁ (Fin.castAdd k b)) =
        inner ℂ
          (finiteKrylovVector energy weight₂ (Fin.castAdd k a))
          (finiteKrylovVector energy weight₂ (Fin.castAdd k b))
    rw [finiteKrylovVector_inner energy weight₁
        (fun x => (hweight₁ x).le),
      finiteKrylovVector_inner energy weight₂
        (fun x => (hweight₂ x).le)]
    norm_cast
    apply hmoment
    have ha : (a : ℕ) ≤ R + 1 := Nat.le_of_lt_succ a.isLt
    have hb : (b : ℕ) ≤ R + 1 := Nat.le_of_lt_succ b.isLt
    simp only [Fin.val_castAdd]
    omega
  · intro a b hai hbj
    rw [finiteKrylovVector_shift_inner energy weight₁
        (fun x => (hweight₁ x).le),
      finiteKrylovVector_shift_inner energy weight₂
        (fun x => (hweight₂ x).le)]
    norm_cast
    apply hmoment
    simp only [Fin.val_castAdd]
    omega

/-- Cross-dimension local moment law.  Two positive spectral packets may have
different energies, different ambient dimensions and different total support;
matching moments through `2R+2` still fixes the same local canonical entry. -/
theorem canonicalKrylovCompression_local_eq_of_moments_cross
    {R k l : ℕ}
    (energy₁ weight₁ : Fin ((R + 2) + k) → ℝ)
    (energy₂ weight₂ : Fin ((R + 2) + l) → ℝ)
    (henergy₁ : Function.Injective energy₁)
    (henergy₂ : Function.Injective energy₂)
    (hweight₁ : ∀ x, 0 < weight₁ x)
    (hweight₂ : ∀ x, 0 < weight₂ x)
    (hmoment : ∀ d : ℕ, d ≤ 2 * R + 2 →
      (∑ x, weight₁ x * energy₁ x ^ d) =
        ∑ x, weight₂ x * energy₂ x ^ d)
    (i j : Fin (R + 2))
    (hdegree : (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2) :
    canonicalKrylovCompression energy₁ weight₁
        henergy₁ hweight₁ (Fin.castAdd k i) (Fin.castAdd k j) =
      canonicalKrylovCompression energy₂ weight₂
        henergy₂ hweight₂ (Fin.castAdd l i) (Fin.castAdd l j) := by
  apply canonicalCompressionPrefixEntry_eq_of_rectangle
    (u := finiteKrylovVector energy₁ weight₁)
    (v := finiteKrylovVector energy₂ weight₂)
    (hu := finiteKrylovVector_linearIndependent henergy₁ hweight₁)
    (hv := finiteKrylovVector_linearIndependent henergy₂ hweight₂)
    (A := finiteIndexDiagonalHamiltonian energy₁)
    (B := finiteIndexDiagonalHamiltonian energy₂)
    (i := i) (j := j)
  · ext a b
    change
      inner ℂ
          (finiteKrylovVector energy₁ weight₁ (Fin.castAdd k a))
          (finiteKrylovVector energy₁ weight₁ (Fin.castAdd k b)) =
        inner ℂ
          (finiteKrylovVector energy₂ weight₂ (Fin.castAdd l a))
          (finiteKrylovVector energy₂ weight₂ (Fin.castAdd l b))
    rw [finiteKrylovVector_inner energy₁ weight₁
        (fun x => (hweight₁ x).le),
      finiteKrylovVector_inner energy₂ weight₂
        (fun x => (hweight₂ x).le)]
    norm_cast
    apply hmoment
    have ha : (a : ℕ) ≤ R + 1 := Nat.le_of_lt_succ a.isLt
    have hb : (b : ℕ) ≤ R + 1 := Nat.le_of_lt_succ b.isLt
    simp only [Fin.val_castAdd]
    omega
  · intro a b hai hbj
    rw [finiteKrylovVector_shift_inner energy₁ weight₁
        (fun x => (hweight₁ x).le),
      finiteKrylovVector_shift_inner energy₂ weight₂
        (fun x => (hweight₂ x).le)]
    norm_cast
    apply hmoment
    simp only [Fin.val_castAdd]
    omega

/-- Arbitrary-ambient version of the cross-dimension local moment law. -/
theorem canonicalKrylovCompression_local_eq_of_moments_cross_of_sizes
    {R r s : ℕ} (hsize₁ : R + 2 ≤ r) (hsize₂ : R + 2 ≤ s)
    (energy₁ weight₁ : Fin r → ℝ)
    (energy₂ weight₂ : Fin s → ℝ)
    (henergy₁ : Function.Injective energy₁)
    (henergy₂ : Function.Injective energy₂)
    (hweight₁ : ∀ x, 0 < weight₁ x)
    (hweight₂ : ∀ x, 0 < weight₂ x)
    (hmoment : ∀ d : ℕ, d ≤ 2 * R + 2 →
      (∑ x, weight₁ x * energy₁ x ^ d) =
        ∑ x, weight₂ x * energy₂ x ^ d)
    (i j : Fin (R + 2))
    (hdegree : (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2) :
    canonicalKrylovCompression energy₁ weight₁
        henergy₁ hweight₁
        (Fin.castLE hsize₁ i) (Fin.castLE hsize₁ j) =
      canonicalKrylovCompression energy₂ weight₂
        henergy₂ hweight₂
        (Fin.castLE hsize₂ i) (Fin.castLE hsize₂ j) := by
  generalize hk : r - (R + 2) = k
  generalize hl : s - (R + 2) = l
  have hr : (R + 2) + k = r := by omega
  have hs : (R + 2) + l = s := by omega
  subst r
  subst s
  simpa using
    (canonicalKrylovCompression_local_eq_of_moments_cross
      energy₁ weight₁ energy₂ weight₂
      henergy₁ henergy₂ hweight₁ hweight₂
      hmoment i j hdegree)

/-- Ambient-dimension form of the local moment law.  It applies to every
finite spectral packet with at least `R+2` levels. -/
theorem canonicalKrylovCompression_local_eq_of_moments_of_size
    {R r : ℕ} (hsize : R + 2 ≤ r)
    (energy weight₁ weight₂ : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight₁ : ∀ x, 0 < weight₁ x)
    (hweight₂ : ∀ x, 0 < weight₂ x)
    (hmoment : ∀ d : ℕ, d ≤ 2 * R + 2 →
      (∑ x, weight₁ x * energy x ^ d) =
        ∑ x, weight₂ x * energy x ^ d)
    (i j : Fin (R + 2))
    (hdegree : (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2) :
    canonicalKrylovCompression energy weight₁
        henergy hweight₁ (Fin.castLE hsize i) (Fin.castLE hsize j) =
      canonicalKrylovCompression energy weight₂
        henergy hweight₂ (Fin.castLE hsize i) (Fin.castLE hsize j) := by
  generalize hk : r - (R + 2) = k
  have hr : (R + 2) + k = r := by omega
  subst r
  simpa using
    (canonicalKrylovCompression_local_eq_of_moments
      energy weight₁ weight₂ henergy hweight₁ hweight₂
      hmoment i j hdegree)

/-- Operational fixed-coordinate form of the local moment law: matching
moments through `2R+2` makes the two path Hamiltonians exactly identical on
all onsite terms through `R` and all bonds through `R ↔ R+1`. -/
theorem canonicalKrylovPathHamiltonian_local_eq_of_moments
    {R k : ℕ}
    (energy weight₁ weight₂ : Fin ((R + 2) + k) → ℝ)
    (henergy : Function.Injective energy)
    (hweight₁ : ∀ x, 0 < weight₁ x)
    (hweight₂ : ∀ x, 0 < weight₂ x)
    (hmoment : ∀ d : ℕ, d ≤ 2 * R + 2 →
      (∑ x, weight₁ x * energy x ^ d) =
        ∑ x, weight₂ x * energy x ^ d)
    (i j : Fin (R + 2))
    (hdegree : (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2) :
    inner ℂ
        (EuclideanSpace.basisFun (Fin ((R + 2) + k)) ℂ
          (Fin.castAdd k i))
        (canonicalKrylovPathHamiltonian energy weight₁
          henergy hweight₁
          (EuclideanSpace.basisFun (Fin ((R + 2) + k)) ℂ
            (Fin.castAdd k j))) =
      inner ℂ
        (EuclideanSpace.basisFun (Fin ((R + 2) + k)) ℂ
          (Fin.castAdd k i))
        (canonicalKrylovPathHamiltonian energy weight₂
          henergy hweight₂
          (EuclideanSpace.basisFun (Fin ((R + 2) + k)) ℂ
            (Fin.castAdd k j))) := by
  rw [canonicalKrylovPathHamiltonian_entry,
    canonicalKrylovPathHamiltonian_entry]
  exact canonicalKrylovCompression_local_eq_of_moments
    energy weight₁ weight₂ henergy hweight₁ hweight₂
    hmoment i j hdegree

/-- Ambient-dimension operational form: every sufficiently large pair of
moment-matched path Hamiltonians has exactly the same local entries. -/
theorem canonicalKrylovPathHamiltonian_local_eq_of_moments_of_size
    {R r : ℕ} (hsize : R + 2 ≤ r)
    (energy weight₁ weight₂ : Fin r → ℝ)
    (henergy : Function.Injective energy)
    (hweight₁ : ∀ x, 0 < weight₁ x)
    (hweight₂ : ∀ x, 0 < weight₂ x)
    (hmoment : ∀ d : ℕ, d ≤ 2 * R + 2 →
      (∑ x, weight₁ x * energy x ^ d) =
        ∑ x, weight₂ x * energy x ^ d)
    (i j : Fin (R + 2))
    (hdegree : (i : ℕ) + (j : ℕ) + 1 ≤ 2 * R + 2) :
    inner ℂ
        (EuclideanSpace.basisFun (Fin r) ℂ (Fin.castLE hsize i))
        (canonicalKrylovPathHamiltonian energy weight₁
          henergy hweight₁
          (EuclideanSpace.basisFun (Fin r) ℂ
            (Fin.castLE hsize j))) =
      inner ℂ
        (EuclideanSpace.basisFun (Fin r) ℂ (Fin.castLE hsize i))
        (canonicalKrylovPathHamiltonian energy weight₂
          henergy hweight₂
          (EuclideanSpace.basisFun (Fin r) ℂ
            (Fin.castLE hsize j))) := by
  rw [canonicalKrylovPathHamiltonian_entry,
    canonicalKrylovPathHamiltonian_entry]
  exact canonicalKrylovCompression_local_eq_of_moments_of_size
    hsize energy weight₁ weight₂ henergy hweight₁ hweight₂
    hmoment i j hdegree

end RHTower.ParityForecast
