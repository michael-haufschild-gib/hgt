import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanCone
import GaloisForLFunctions.HTGeometry.NumberFieldBoundedPrincipalIdeals
import GaloisForLFunctions.HTGeometry.MvPolynomialMatrixRankDefect

/-!
# Product-formula lower bound for number-field frame minors

A leading frame of an integral special-linear matrix has full column rank after every complex
embedding.  Hence one ordered maximal minor is a nonzero algebraic integer.  The same integral
minor is used at every embedding, so the algebraic-integer norm formula gives a nonnegative sum of
its logarithmic embedding magnitudes.  This is the global replacement for the false placewise
claim that every nonzero integral minor has magnitude at least one.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n k : ℕ}

/-- Evaluate a rectangular number-ring matrix at an arbitrary complex embedding. -/
def numberFieldOrderMatrixAtEmbedding (σ : K →+* ℂ)
    (M : Matrix (Fin n) (Fin k) (𝓞 K)) : Matrix (Fin n) (Fin k) ℂ :=
  M.map (σ.comp (algebraMap (𝓞 K) K))

omit [NumberField K] in
/-- Arbitrary-embedding evaluation commutes with row and column selection. -/
theorem numberFieldOrderMatrixAtEmbedding_submatrix
    (σ : K →+* ℂ) (M : Matrix (Fin n) (Fin k) (𝓞 K))
    {r c : ℕ} (rows : Fin r → Fin n) (cols : Fin c → Fin k) :
    numberFieldOrderMatrixAtEmbedding σ (M.submatrix rows cols) =
      (numberFieldOrderMatrixAtEmbedding σ M).submatrix rows cols := by
  rfl

omit [NumberField K] in
/-- Determinants commute with arbitrary complex embedding evaluation. -/
theorem numberFieldOrderMatrixAtEmbedding_det
    (σ : K →+* ℂ) (M : Matrix (Fin n) (Fin n) (𝓞 K)) :
    (numberFieldOrderMatrixAtEmbedding σ M).det =
      σ ((M.det : 𝓞 K) : K) := by
  simpa [numberFieldOrderMatrixAtEmbedding] using
    (RingHom.map_det (σ.comp (algebraMap (𝓞 K) K)) M).symm

/-- A nonsingular integral matrix determinant has nonnegative total logarithmic embedding size. -/
theorem sum_log_norm_numberFieldOrderMatrixAtEmbedding_det_nonneg
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) (hM : M.det ≠ 0) :
    0 ≤ ∑ σ : K →+* ℂ,
      Real.log ‖(numberFieldOrderMatrixAtEmbedding σ M).det‖ := by
  have hprod : 1 ≤ ∏ σ : K →+* ℂ,
      ‖(numberFieldOrderMatrixAtEmbedding σ M).det‖ := by
    simpa [numberFieldOrderMatrixAtEmbedding_det] using
      (one_le_prod_norm_embeddings M.det hM)
  have hne (σ : K →+* ℂ) :
      ‖(numberFieldOrderMatrixAtEmbedding σ M).det‖ ≠ 0 := by
    rw [numberFieldOrderMatrixAtEmbedding_det, norm_ne_zero_iff]
    intro hσ
    have hM0 : ((M.det : 𝓞 K) : K) = 0 :=
      σ.injective (hσ.trans (map_zero σ).symm)
    exact hM (by exact_mod_cast hM0)
  rw [← Real.log_prod (fun σ _ => hne σ)]
  exact Real.log_nonneg hprod

/-- Leading columns of an injective square matrix have trivial kernel. -/
theorem leadingFrame_mulVec_eq_zero
    {R : Type*} [CommRing R] {k n : ℕ} (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) R} (hG : Function.Injective G.mulVec)
    {x : Fin k → R}
    (hx : (G.submatrix id (Fin.castLE hk)).mulVec x = 0) : x = 0 := by
  classical
  set y : Fin n → R := fun m => if h : (m : ℕ) < k then x ⟨(m : ℕ), h⟩ else 0 with hy
  have hinj : Set.InjOn (Fin.castLE hk) ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
    intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  have hcast : ∀ b : Fin k, y (Fin.castLE hk b) = x b := by
    intro b
    have hb : ((Fin.castLE hk b : Fin n) : ℕ) < k := by simp
    rw [hy]
    simp only [dif_pos hb]
    exact congrArg x (Fin.ext rfl)
  have hgy : G.mulVec y = 0 := by
    funext p
    have hstep : (G.mulVec y) p = ∑ b : Fin k, G p (Fin.castLE hk b) * x b := by
      show ∑ m, G p m * y m = _
      have hre : (∑ b : Fin k, G p (Fin.castLE hk b) * x b)
          = ∑ m ∈ Finset.univ.image (Fin.castLE hk), G p m * y m := by
        rw [Finset.sum_image (f := fun m : Fin n => G p m * y m) hinj]
        exact Finset.sum_congr rfl fun b _ => by rw [hcast b]
      rw [hre]
      refine (Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_).symm
      have hmk : k ≤ (m : ℕ) := by
        by_contra hcon
        exact hm (Finset.mem_image.2
          ⟨⟨(m : ℕ), by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have hym : y m = 0 := by
        rw [hy]
        simp only [dif_neg (by omega : ¬ ((m : ℕ) < k))]
      rw [hym, mul_zero]
    have hxp : ((G.submatrix id (Fin.castLE hk)).mulVec x) p =
        ∑ b : Fin k, G p (Fin.castLE hk b) * x b := rfl
    rw [hstep, ← hxp, hx]
  have hyzero : y = 0 := hG (by simpa using hgy)
  funext b
  rw [← hcast b, hyzero]
  rfl

/-- Leading columns of an injective square matrix define an injective rectangular matrix. -/
theorem leadingFrame_mulVec_injective
    {R : Type*} [CommRing R] {k n : ℕ} (hk : k ≤ n)
    {G : Matrix (Fin n) (Fin n) R} (hG : Function.Injective G.mulVec) :
    Function.Injective (G.submatrix id (Fin.castLE hk)).mulVec := by
  intro x y hxy
  have hz : (G.submatrix id (Fin.castLE hk)).mulVec (x - y) = 0 := by
    funext i
    have hi := congrFun hxy i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib,
      Pi.zero_apply]
    exact sub_eq_zero.mpr hi
  exact sub_eq_zero.mp (leadingFrame_mulVec_eq_zero hk hG hz)

/-- A leading frame of a number-field special-linear matrix has one globally nonzero integral
maximal minor, and that same minor satisfies the complete archimedean product-formula lower bound. -/
theorem exists_numberFieldSpecialLinear_leadingMinor_productFormula
    (g : Matrix.SpecialLinearGroup (Fin n) (𝓞 K)) (hk : k ≤ n) :
    ∃ rows : Fin k → Fin n,
      ((g : Matrix (Fin n) (Fin n) (𝓞 K)).submatrix rows (Fin.castLE hk)).det ≠ 0 ∧
      0 ≤ ∑ σ : K →+* ℂ, Real.log ‖
        ((numberFieldOrderMatrixAtEmbedding σ
          ((g : Matrix (Fin n) (Fin n) (𝓞 K)).submatrix rows (Fin.castLE hk))).det)‖ := by
  classical
  let σ : K →+* ℂ := Classical.choice (inferInstance : Nonempty (K →+* ℂ))
  let G : Matrix (Fin n) (Fin n) ℂ :=
    numberFieldOrderMatrixAtEmbedding σ (g : Matrix (Fin n) (Fin n) (𝓞 K))
  have hGdet : G.det = 1 := by
    rw [show G.det = σ ((((g : Matrix (Fin n) (Fin n) (𝓞 K)).det : 𝓞 K) : K)) by
      exact numberFieldOrderMatrixAtEmbedding_det σ _]
    rw [Matrix.SpecialLinearGroup.det_coe]
    simp
  have hGunit : IsUnit G := by
    rw [Matrix.isUnit_iff_isUnit_det, hGdet]
    exact isUnit_one
  have hGinj : Function.Injective G.mulVec := Matrix.mulVec_injective_of_isUnit hGunit
  have hframe : Function.Injective
      (G.submatrix id (Fin.castLE hk)).mulVec :=
    leadingFrame_mulVec_injective hk hGinj
  obtain ⟨rows, hminorσ⟩ :=
    (matrix_mulVec_injective_iff_exists_submatrix_det_ne_zero
      (G.submatrix id (Fin.castLE hk))).mp hframe
  have hminor :
      ((g : Matrix (Fin n) (Fin n) (𝓞 K)).submatrix rows (Fin.castLE hk)).det ≠ 0 := by
    intro hzero
    apply hminorσ
    have hmap : numberFieldOrderMatrixAtEmbedding σ
        ((g : Matrix (Fin n) (Fin n) (𝓞 K)).submatrix rows (Fin.castLE hk)) =
        (G.submatrix id (Fin.castLE hk)).submatrix rows id := by
      ext i j
      rfl
    rw [← hmap, numberFieldOrderMatrixAtEmbedding_det, hzero]
    simp
  exact ⟨rows, hminor,
    sum_log_norm_numberFieldOrderMatrixAtEmbedding_det_nonneg _ hminor⟩

end

end GaloisForLFunctions.HTGeometry
