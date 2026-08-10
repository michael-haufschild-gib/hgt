import GaloisForLFunctions.RHTower.GaussFourierDiagonal

/-!
# The quasi-inner diagonal is a bounded quadratic form

The prime-scale blocks multiply by real symbols, so they are self-adjoint; the two diagonal blocks
are adjoint to one another; and multiplication by an exponential monomial preserves the inner
product.  Folding the factorisation `G = p B D B^(-2) D* B` from both ends therefore gives

`⟪e_n, G e_n⟫ = p ⟪D* B e_n, B^(-2) D* B e_n⟫`,

a quadratic form in the single vector `D* B e_n` against the *bounded* operator `B^(-2)`.  No
normalised block occurs, so no factor `d_n^(-1)` is ever produced: the error of the moving
translation enters this expression multiplied by `|d_n|²`, which is what a logarithmic mean of the
diagonal requires.
-/

namespace RHTower

open MeasureTheory GaloisForLFunctions Filter Topology

noncomputable section

/-! ## The symbols -/

theorem gaussPrimeScaleCircle_real (p : ℝ) (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (gaussPrimeScaleCircle p z) = gaussPrimeScaleCircle p z := by
  have hval : gaussPrimeScaleCircle p z =
      ((gaussPrimeScale p
        ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ) := rfl
  rw [hval, Complex.conj_ofReal]

theorem gaussPrimeScaleInvSqCircle_real (p : ℝ) (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (gaussPrimeScaleInvSqCircle p z) = gaussPrimeScaleInvSqCircle p z := by
  have hval : gaussPrimeScaleInvSqCircle p z =
      ((gaussPrimeScaleInvSq p
        ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) : ℝ) : ℂ) := rfl
  rw [hval, Complex.conj_ofReal]

theorem fourier_unimodular (n : ℤ) (z : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (fourier n z) * fourier n z = 1 := by
  rw [Complex.conj_mul', norm_fourier_eq_one]
  norm_num

/-! ## Self-adjointness and the isometry of the monomial -/

theorem gaussPrimeScaleBlock_inner {p : ℝ} (hp : 1 < p)
    (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussPrimeScaleBlock hp f) g : ℂ) = inner ℂ f (gaussPrimeScaleBlock hp g) :=
  MeasureTheory.lpBoundedMulCLM_inner_real _ _ _ (gaussPrimeScaleCircle_real p) f g

theorem gaussPrimeScaleInvSqBlock_inner {p : ℝ} (hp : 1 < p)
    (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussPrimeScaleInvSqBlock hp f) g : ℂ)
      = inner ℂ f (gaussPrimeScaleInvSqBlock hp g) :=
  MeasureTheory.lpBoundedMulCLM_inner_real _ _ _ (gaussPrimeScaleInvSqCircle_real p) f g

theorem fourierMulBlock_inner (n : ℤ)
    (f g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (fourierMulBlock n f) (fourierMulBlock n g) : ℂ) = inner ℂ f g :=
  MeasureTheory.lpBoundedMulCLM_inner_unimodular _ _ _ (fourier_unimodular n) f g

/-! ## The two diagonal blocks are adjoint -/

theorem gaussDiagonalBlock_inner {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ (gaussDiagonalBlock hm k p u) v : ℂ)
      = inner ℂ u (gaussDiagonalBlockStar hm k p v) := by
  have hrepr : (fourierBasis (T := (1 : ℝ))).repr (gaussDiagonalBlock hm k p u)
      = GaloisForLFunctions.lpDiagonalCLM (fun i : ℤ => gaussSampleValue k p i)
          (gaussSampleValueBound_nonneg hm k p) (norm_gaussSampleValue_le hm k p)
          ((fourierBasis (T := (1 : ℝ))).repr u) := by
    rw [gaussDiagonalBlock, conjugateOperator]
    simp
  have hreprStar : (fourierBasis (T := (1 : ℝ))).repr (gaussDiagonalBlockStar hm k p v)
      = GaloisForLFunctions.lpDiagonalCLM
          (fun i : ℤ => starRingEnd ℂ (gaussSampleValue k p i))
          (gaussSampleValueBound_nonneg hm k p) (norm_conj_gaussSampleValue_le hm k p)
          ((fourierBasis (T := (1 : ℝ))).repr v) := by
    rw [gaussDiagonalBlockStar, conjugateOperator]
    simp
  have hleft : (inner ℂ (gaussDiagonalBlock hm k p u) v : ℂ)
      = inner ℂ ((fourierBasis (T := (1 : ℝ))).repr (gaussDiagonalBlock hm k p u))
          ((fourierBasis (T := (1 : ℝ))).repr v) :=
    ((fourierBasis (T := (1 : ℝ))).repr.inner_map_map _ _).symm
  have hright : (inner ℂ u (gaussDiagonalBlockStar hm k p v) : ℂ)
      = inner ℂ ((fourierBasis (T := (1 : ℝ))).repr u)
          ((fourierBasis (T := (1 : ℝ))).repr (gaussDiagonalBlockStar hm k p v)) :=
    ((fourierBasis (T := (1 : ℝ))).repr.inner_map_map _ _).symm
  rw [hleft, hright, hrepr, hreprStar]
  exact GaloisForLFunctions.lpDiagonalCLM_inner _ _ _ _ (norm_conj_gaussSampleValue_le hm k p)
    _ _

theorem gaussDiagonalBlockStar_inner {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (u v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ u (gaussDiagonalBlock hm k p v) : ℂ)
      = inner ℂ (gaussDiagonalBlockStar hm k p u) v := by
  rw [← inner_conj_symm, gaussDiagonalBlock_inner, inner_conj_symm]

/-! ## The folded diagonal -/

theorem gaussQuasiInnerG_apply {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    gaussQuasiInnerG hm k p u
      = ((p : ℝ) : ℂ) •
        gaussPrimeScaleBlock hp (gaussDiagonalBlock hm k p
          (gaussPrimeScaleInvSqBlock hp (gaussDiagonalBlockStar hm k p
            (gaussPrimeScaleBlock hp u)))) := rfl

/-- **The quasi-inner diagonal is a bounded quadratic form.**  Folding the factorisation from both
ends removes every normalised block. -/
theorem inner_fourierLp_gaussQuasiInnerG {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (hp : (1 : ℝ) < (p : ℝ)) (u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    (inner ℂ u (gaussQuasiInnerG hm k p u) : ℂ)
      = ((p : ℝ) : ℂ) *
        inner ℂ (gaussDiagonalBlockStar hm k p (gaussPrimeScaleBlock hp u))
          (gaussPrimeScaleInvSqBlock hp
            (gaussDiagonalBlockStar hm k p (gaussPrimeScaleBlock hp u))) := by
  rw [gaussQuasiInnerG_apply hm k p hp, inner_smul_right]
  congr 1
  rw [← gaussPrimeScaleBlock_inner hp u, gaussDiagonalBlockStar_inner hm k p]

end

end RHTower
