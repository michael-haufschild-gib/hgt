import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndexCountsTheRightZeros
import GaloisForLFunctions.HTGeometry.ConstitutivePositiveConeMidpointRecovery
import GaloisForLFunctions.HTGeometry.IsometricCongruenceInertia

/-!
# The window index counts the jump multiples

On a family of windows `h_i` the second-order term at the multiple `K` of the critical curve is the
pencil `P_K = κ_φ W(H) + (βJ/K) A(H)` (`pencilGram_eq`). For a linearly independent family the
aliasing Gram matrix `A(H)` is positive definite, and the pencil is diagonalized by the relative
eigenvalues `λ_i` of `κ_φ W(H)` against `A(H)` (the eigenvalues of `A^{−1/2} κ_φ W(H) A^{−1/2}`):

* **Inertia of a pencil** (`hermNegIndex_add_smul_posDef`): for Hermitian `W` and positive definite
  `A`, `ind₋(W + tA) = #{i : λ_i + t < 0}`. Proof: `W + tA = S(A^{−1/2}WA^{−1/2} + t)S` with
  `S = A^{1/2}` (Sylvester), then the spectral theorem.
* **Independent families** (`aliasGram_posDef`): `A(H)` is positive definite iff no nontrivial
  combination of the windows vanishes; its form is `∫ e^{−(β+1)y} |Σ x_i H_i|²`.
* **The jump multiples** (`windowIndex_eq_card_jumpMultiples`): for `βJ > 0` the window index at
  `K` is the number of `i` with `λ_i < 0` and `K_i = βJ/(−λ_i) < K`. The window index is a step
  function of the multiple that jumps by one at each jump multiple `K_i`, counted with multiplicity;
  Weil's index of the family is the number of negative relative eigenvalues
  (`hermNegIndex_weilWindowGram_eq_card`). For a single window `K_1 = βJ‖H‖²_{−(β+1)}/(κ|Q(H)|)`
  is its critical multiple.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri HTGeometry

variable {φ : ℝ → ℝ} {A : ℝ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Inertia of a pencil -/

/-- The relative matrix `A^{−1/2} W A^{−1/2}` of a form `W` against a positive definite `A`. -/
def relMatrix (W B : Matrix ι ι ℂ) : Matrix ι ι ℂ := (CFC.sqrt B)⁻¹ * W * (CFC.sqrt B)⁻¹

theorem relMatrix_isHermitian {W B : Matrix ι ι ℂ} (hW : W.IsHermitian) (hB : B.PosDef) :
    (relMatrix W B).IsHermitian := by
  have hS := (positiveMatrixSqrt_posDef hB).isHermitian
  unfold relMatrix
  rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_nonsing_inv, hS.eq, hW.eq,
    Matrix.mul_assoc]

/-- The relative eigenvalues of `W` against `B`. -/
def relEigenvalues {W B : Matrix ι ι ℂ} (hW : W.IsHermitian) (hB : B.PosDef) : ι → ℝ :=
  (relMatrix_isHermitian hW hB).eigenvalues

theorem add_smul_eq_conj {W B : Matrix ι ι ℂ} (hB : B.PosDef) (t : ℝ) :
    W + (t : ℂ) • B = (CFC.sqrt B)ᴴ * (relMatrix W B + (t : ℂ) • 1) * CFC.sqrt B := by
  have hSd := positiveMatrixSqrt_posDef hB
  have hdet : IsUnit (CFC.sqrt B).det := (Matrix.isUnit_iff_isUnit_det _).mp hSd.isUnit
  rw [hSd.isHermitian.eq, relMatrix, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
    Matrix.mul_one, positiveMatrixSqrt_mul_self hB]

/-- **Inertia of a pencil**: `ind₋(W + tB) = #{i : λ_i + t < 0}` for Hermitian `W`, positive
definite `B` and the relative eigenvalues `λ_i` of `W` against `B`. -/
theorem hermNegIndex_add_smul_posDef {W B : Matrix ι ι ℂ} (hW : W.IsHermitian) (hB : B.PosDef)
    (t : ℝ) :
    hermNegIndex (W + (t : ℂ) • B) = ({i | relEigenvalues hW hB i + t < 0} : Finset ι).card := by
  rw [add_smul_eq_conj hB t, negIndex_conjugate _ (positiveMatrixSqrt_posDef hB).isUnit]
  set hM := relMatrix_isHermitian hW hB
  set U : Matrix ι ι ℂ := (hM.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  have hUU : Uᴴ * U = 1 := by
    rw [hU]; exact Matrix.UnitaryGroup.star_mul_self _
  have hUU' : U * Uᴴ = 1 := by
    have h := hM.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff] at h
    simpa [hU, Matrix.star_eq_conjTranspose] using h
  have key : relMatrix W B + (t : ℂ) • 1 =
      U * diagonal (fun i => ((hM.eigenvalues i + t : ℝ) : ℂ)) * Uᴴ := by
    have e : diagonal (fun i => ((hM.eigenvalues i + t : ℝ) : ℂ)) =
        diagonal (RCLike.ofReal ∘ hM.eigenvalues) + (t : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [e, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU']
    conv_lhs => rw [hM.spectral_theorem]
    rfl
  rw [key, negIndex_isometric_congr hUU, negIndex_diagonal]
  rfl

/-- A Hermitian matrix with positive form on nonzero vectors is positive definite. -/
theorem posDef_of_hermQuad_pos {B : Matrix ι ι ℂ} (hB : B.IsHermitian)
    (h : ∀ x : ι → ℂ, x ≠ 0 → 0 < hermQuad B x) : B.PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hB, fun x hx => ?_⟩
  have him : (star x ⬝ᵥ B *ᵥ x).im = 0 := Complex.conj_eq_iff_im.1 (by
    change star (star x ⬝ᵥ B *ᵥ x) = star x ⬝ᵥ B *ᵥ x
    rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hB.eq,
      ← Matrix.dotProduct_mulVec])
  rw [Complex.lt_def]
  exact ⟨by simpa [hermQuad] using h x hx, by simpa using him.symm⟩

/-! ### The aliasing Gram matrix of an independent family -/

omit [DecidableEq ι] in
/-- The form of a weighted Gram matrix: `Σ x̄_i x_j ∫ w H_i H_j = ∫ w |Σ x_j H_j|²`. -/
theorem hermQuad_weightGram_eq {w : ℝ → ℝ} (hw : Continuous w) {H : ι → ℝ → ℝ}
    (hH : ∀ i, Continuous (H i)) (hHs : ∀ i y, y ∉ Set.Icc (-A) 0 → H i y = 0) (x : ι → ℂ) :
    hermQuad (fun i j => ((∫ y, w y * (H i y * H j y) : ℝ) : ℂ)) x =
      ∫ y, w y * Complex.normSq (∑ j, x j * (H j y : ℂ)) := by
  have hint : ∀ i j, Integrable (fun y => ((w y * (H i y * H j y) : ℝ) : ℂ)) := fun i j =>
    (integrable_mul_of_window (A := A) (F := fun y => H i y * H j y) hw ((hH i).mul (hH j))
      fun y hy => by simp [hHs i y hy]).ofReal
  have hpt : ∀ y, ∑ i, star (x i) * ∑ j, ((w y * (H i y * H j y) : ℝ) : ℂ) * x j =
      ((w y * Complex.normSq (∑ j, x j * (H j y : ℂ)) : ℝ) : ℂ) := fun y => by
    rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def]
    push_cast
    ring
  have hswap : ∫ y, ∑ i, star (x i) * ∑ j, ((w y * (H i y * H j y) : ℝ) : ℂ) * x j =
      ∑ i, star (x i) * ∑ j, (∫ y, ((w y * (H i y * H j y) : ℝ) : ℂ)) * x j := by
    rw [integral_finsetSum _ fun i _ =>
      (integrable_finsetSum _ fun j _ => (hint i j).mul_const _).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, integral_finsetSum _ fun j _ => (hint i j).mul_const _]
    congr 1
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
  have key : star x ⬝ᵥ ((fun i j => ((∫ y, w y * (H i y * H j y) : ℝ) : ℂ) : Matrix ι ι ℂ) *ᵥ x) =
      ((∫ y, w y * Complex.normSq (∑ j, x j * (H j y : ℂ)) : ℝ) : ℂ) := by
    have e : ∀ i j, ((∫ y, w y * (H i y * H j y) : ℝ) : ℂ) =
        ∫ y, ((w y * (H i y * H j y) : ℝ) : ℂ) := fun i j => integral_complex_ofReal.symm
    simp only [dotProduct, mulVec, Pi.star_apply, e]
    rw [← hswap, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall hpt)
  unfold hermQuad
  rw [key, Complex.ofReal_re]

omit [DecidableEq ι] in
theorem aliasGram_isHermitian (β : ℝ) (h : ι → ℝ → ℝ) : (aliasGram β h).IsHermitian := by
  ext i j
  simp only [aliasGram, conjTranspose_apply]
  rw [Complex.star_def, Complex.conj_ofReal]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun y => by simp only; ring)

/-- **Independent families**: the aliasing Gram matrix of a linearly independent family of windows
is positive definite. -/
theorem aliasGram_posDef (β : ℝ) {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    (aliasGram β h).PosDef := by
  refine posDef_of_hermQuad_pos (aliasGram_isHermitian β h) fun x hx => ?_
  have hHc : ∀ i, Continuous (halfWeight (h i)) := fun i => (contDiff_halfWeight (hh i)).continuous
  have hHs := fun i => halfWeight_eq_zero_of_window (hsupp i)
  rw [show aliasGram β h = fun i j => ((∫ y, Real.exp (-((β + 1) * y)) *
      (halfWeight (h i) y * halfWeight (h j) y) : ℝ) : ℂ) from rfl,
    hermQuad_weightGram_eq (A := A) (by fun_prop) hHc hHs]
  -- a nonzero combination of independent windows is nonzero somewhere
  obtain ⟨y₀, hy₀⟩ : ∃ y, ∑ j, x j * (halfWeight (h j) y : ℂ) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hre : ∀ y, ∑ j, (x j).re * h j y = 0 := fun y => by
      have h1 := congrArg Complex.re (hall y)
      simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, Complex.zero_re, halfWeight] at h1
      have he : Real.exp (y / 2) ≠ 0 := (Real.exp_pos _).ne'
      have : Real.exp (y / 2) * ∑ j, (x j).re * h j y = 0 := by
        rw [Finset.mul_sum]; rw [← h1]; exact Finset.sum_congr rfl fun j _ => by ring
      exact (mul_eq_zero.mp this).resolve_left he
    have him : ∀ y, ∑ j, (x j).im * h j y = 0 := fun y => by
      have h1 := congrArg Complex.im (hall y)
      simp only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        Complex.zero_im, halfWeight] at h1
      have he : Real.exp (y / 2) ≠ 0 := (Real.exp_pos _).ne'
      have : Real.exp (y / 2) * ∑ j, (x j).im * h j y = 0 := by
        rw [Finset.mul_sum]; rw [← h1]; exact Finset.sum_congr rfl fun j _ => by ring
      exact (mul_eq_zero.mp this).resolve_left he
    have hli := Fintype.linearIndependent_iff.mp hlin
    have h1 := hli (fun j => (x j).re) (funext fun y => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact hre y)
    have h2 := hli (fun j => (x j).im) (funext fun y => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; exact him y)
    exact hx (funext fun j => Complex.ext (h1 j) (h2 j))
  have hcont : Continuous fun y => Real.exp (-((β + 1) * y)) *
      Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) := by
    refine (by fun_prop : Continuous fun y => Real.exp (-((β + 1) * y))).mul
      (Complex.continuous_normSq.comp ?_)
    exact continuous_finsetSum _ fun j _ =>
      continuous_const.mul (Complex.continuous_ofReal.comp (hHc j))
  have hcs : HasCompactSupport fun y => Real.exp (-((β + 1) * y)) *
      Complex.normSq (∑ j, x j * (halfWeight (h j) y : ℂ)) :=
    HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => by
      have hz : ∀ j, halfWeight (h j) y = 0 := fun j => hHs j y hy
      simp [hz]
  refine hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs
    (fun y => mul_nonneg (Real.exp_pos _).le (Complex.normSq_nonneg _)) (x := y₀) ?_
  exact mul_ne_zero (Real.exp_pos _).ne' (by rwa [Ne, Complex.normSq_eq_zero])

/-! ### The jump multiples -/

/-- **The window index of an independent family** is the number of relative eigenvalues `λ_i` of
Weil's part against the aliasing part with `λ_i + βJ/K < 0`. -/
theorem windowIndex_eq_card (β J K : ℝ) {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    hermNegIndex (pencilGram φ β J K h) =
      ({i | relEigenvalues (weilWindowGram_isHermitian φ h) (aliasGram_posDef β hh hsupp hlin) i +
        β * J / K < 0} : Finset ι).card := by
  rw [pencilGram_eq hh hsupp, hermNegIndex_add_smul_posDef]

/-- **Weil's index of an independent family** is its number of negative relative eigenvalues. -/
theorem hermNegIndex_weilWindowGram_eq_card (β : ℝ) {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    hermNegIndex (weilWindowGram φ h) =
      ({i | relEigenvalues (weilWindowGram_isHermitian φ h) (aliasGram_posDef β hh hsupp hlin) i <
        0} : Finset ι).card := by
  have := hermNegIndex_add_smul_posDef (weilWindowGram_isHermitian φ h)
    (aliasGram_posDef β hh hsupp hlin) 0
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at this
  exact this

/-- **The window index counts the jump multiples.** For `βJ > 0` and `K > 0` the window index of
an independent family is the number of negative relative eigenvalues `λ_i` whose jump multiple
`K_i = βJ/(−λ_i)` lies below `K`. -/
theorem windowIndex_eq_card_jumpMultiples {β J K : ℝ} (hβJ : 0 < β * J) (hK : 0 < K)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    hermNegIndex (pencilGram φ β J K h) =
      ({i | relEigenvalues (weilWindowGram_isHermitian φ h) (aliasGram_posDef β hh hsupp hlin) i <
          0 ∧ β * J / -relEigenvalues (weilWindowGram_isHermitian φ h)
            (aliasGram_posDef β hh hsupp hlin) i < K} : Finset ι).card := by
  rw [windowIndex_eq_card β J K hh hsupp hlin]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  set l := relEigenvalues (weilWindowGram_isHermitian φ h) (aliasGram_posDef β hh hsupp hlin) i
  constructor
  · intro hl
    have hbK : 0 < β * J / K := div_pos hβJ hK
    have hl0 : l < 0 := by linarith
    refine ⟨hl0, ?_⟩
    rw [div_lt_iff₀ (by linarith)]
    have := (div_lt_iff₀ hK).mp (show β * J / K < -l by linarith)
    linarith
  · rintro ⟨hl0, hlt⟩
    rw [div_lt_iff₀ (by linarith)] at hlt
    have : β * J / K < -l := by rw [div_lt_iff₀ hK]; linarith
    linarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
