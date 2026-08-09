import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperator

/-!
# Diagonal operators on a square-summable space over an arbitrary index

Multiplication by a uniformly bounded family of scalars is a bounded operator on `ℓ²` over any
index type.  The coordinate vectors form a Hilbert basis, each is an eigenvector, and the
corresponding eigenvalue is recovered from the operator as a diagonal matrix element.  Consequently
the operator is Hilbert–Schmidt exactly when the multiplier family is square-summable, and then its
Hilbert–Schmidt norm is that square-summable total.

The index type is arbitrary: no ordering, countability, or monotonicity of the multipliers is used.
-/

open scoped ENNReal InnerProductSpace BigOperators

noncomputable section

namespace HTGeometry

/-- The square-summable complex family space over an arbitrary index. -/
abbrev IndexedEllTwo (κ : Type*) := lp (fun _ : κ => ℂ) 2

variable {κ : Type*} [DecidableEq κ]

/-- The coordinate vectors of `ℓ²(κ)`, as a Hilbert basis. -/
def ellTwoCoordinateBasis (κ : Type*) [DecidableEq κ] :
    HilbertBasis κ ℂ (IndexedEllTwo κ) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (IndexedEllTwo κ))

@[simp] theorem ellTwoCoordinateBasis_apply (i : κ) :
    ellTwoCoordinateBasis κ i = lp.single 2 i (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

omit [DecidableEq κ] in
/-- Multiplying a square-summable family by a bounded family keeps it square-summable. -/
theorem memℓp_ellTwoDiagonal {lam : κ → ℂ} {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : IndexedEllTwo κ) : Memℓp (fun i => lam i * f i) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun i => ‖f i‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro i
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (hC i) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

/-- Diagonal multiplication by a bounded family, as a linear map. -/
def ellTwoDiagonalLinearMap (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) :
    IndexedEllTwo κ →ₗ[ℂ] IndexedEllTwo κ where
  toFun f := ⟨fun i => lam i * f i, memℓp_ellTwoDiagonal hC f⟩
  map_add' := by
    intro f g
    ext i
    simp [mul_add]
  map_smul' := by
    intro c f
    ext i
    simp [mul_left_comm]

omit [DecidableEq κ] in
@[simp] theorem ellTwoDiagonalLinearMap_apply (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : IndexedEllTwo κ) (i : κ) :
    (ellTwoDiagonalLinearMap lam hC f : κ → ℂ) i = lam i * f i := rfl

omit [DecidableEq κ] in
/-- The diagonal map is bounded by the multiplier bound. -/
theorem norm_ellTwoDiagonalLinearMap_le (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : IndexedEllTwo κ) : ‖ellTwoDiagonalLinearMap lam hC f‖ ≤ C * ‖f‖ := by
  rcases isEmpty_or_nonempty κ with hemp | ⟨⟨i₀⟩⟩
  · haveI := hemp
    have hf : f = 0 := by
      apply lp.ext
      funext i
      exact (IsEmpty.false i).elim
    simp [hf]
  have hCnn : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC i₀)
  have hnn : (0 : ℝ) ≤ ‖ellTwoDiagonalLinearMap lam hC f‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ C * ‖f‖ := mul_nonneg hCnn (norm_nonneg _)
  have htsumD : ‖ellTwoDiagonalLinearMap lam hC f‖ ^ (2 : ℝ)
      = ∑' i, ‖(ellTwoDiagonalLinearMap lam hC f) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : κ => ℂ) (by norm_num)
      (ellTwoDiagonalLinearMap lam hC f)
  have htsumf : ‖f‖ ^ (2 : ℝ) = ∑' i, ‖f i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : κ => ℂ) (by norm_num) f
  have hsumf : Summable fun i => ‖f i‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hsumD : Summable fun i => ‖(ellTwoDiagonalLinearMap lam hC f) i‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ i, ‖(ellTwoDiagonalLinearMap lam hC f) i‖ ^ (2 : ℝ)
      ≤ C ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ) := by
    intro i
    rw [ellTwoDiagonalLinearMap_apply, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hC i) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : ‖ellTwoDiagonalLinearMap lam hC f‖ ^ (2 : ℝ) ≤ (C * ‖f‖) ^ (2 : ℝ) := by
    rw [htsumD, Real.mul_rpow hCnn (norm_nonneg _), htsumf, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumD (hsumf.mul_left (C ^ (2 : ℝ)))
  have hx2 : ‖ellTwoDiagonalLinearMap lam hC f‖ ^ (2 : ℝ)
      = ‖ellTwoDiagonalLinearMap lam hC f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (C * ‖f‖) ^ (2 : ℝ) = (C * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

/-- **Diagonal multiplication by a bounded family, as a bounded operator on `ℓ²(κ)`.** -/
def ellTwoDiagonal (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) :
    IndexedEllTwo κ →L[ℂ] IndexedEllTwo κ :=
  LinearMap.mkContinuous (ellTwoDiagonalLinearMap lam hC) C
    (norm_ellTwoDiagonalLinearMap_le lam hC)

omit [DecidableEq κ] in
@[simp] theorem ellTwoDiagonal_apply (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : IndexedEllTwo κ) (i : κ) :
    (ellTwoDiagonal lam hC f) i = lam i * f i := rfl

omit [DecidableEq κ] in
/-- The operator norm is bounded by the multiplier bound. -/
theorem norm_ellTwoDiagonal_le (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (hCnn : 0 ≤ C) :
    ‖ellTwoDiagonal lam hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hCnn _

/-- **Every coordinate vector is an eigenvector**, with the multiplier as eigenvalue. -/
theorem ellTwoDiagonal_coordinateBasis (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (i : κ) :
    ellTwoDiagonal lam hC (ellTwoCoordinateBasis κ i)
      = lam i • ellTwoCoordinateBasis κ i := by
  ext j
  rw [ellTwoDiagonal_apply]
  simp only [ellTwoCoordinateBasis_apply, lp.coeFn_smul, Pi.smul_apply, lp.single_apply,
    Pi.single_apply, smul_eq_mul]
  split_ifs with h <;> simp [h]

/-- The image of a coordinate vector has the modulus of the corresponding multiplier. -/
theorem norm_ellTwoDiagonal_coordinateBasis (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (i : κ) : ‖ellTwoDiagonal lam hC (ellTwoCoordinateBasis κ i)‖ = ‖lam i‖ := by
  rw [ellTwoDiagonal_coordinateBasis, norm_smul, ellTwoCoordinateBasis_apply,
    lp.norm_single (E := fun _ : κ => ℂ) (p := 2) (by norm_num) i (1 : ℂ)]
  simp

/-- **The multiplier is a diagonal matrix element of the operator.**  Each eigenvalue is read off
the operator by pairing against the corresponding coordinate vector. -/
theorem inner_coordinateBasis_ellTwoDiagonal (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (i : κ) :
    ⟪ellTwoCoordinateBasis κ i, ellTwoDiagonal lam hC (ellTwoCoordinateBasis κ i)⟫_ℂ = lam i := by
  rw [ellTwoCoordinateBasis_apply,
    lp.inner_single_left (𝕜 := ℂ) (G := fun _ : κ => ℂ) i (1 : ℂ)]
  rw [ellTwoDiagonal_apply]
  simp

/-- Every multiplier value is bounded by the operator norm. -/
theorem le_norm_ellTwoDiagonal (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (i : κ) :
    ‖lam i‖ ≤ ‖ellTwoDiagonal lam hC‖ := by
  have hone : ‖(ellTwoCoordinateBasis κ i : IndexedEllTwo κ)‖ = 1 := by
    rw [ellTwoCoordinateBasis_apply,
      lp.norm_single (E := fun _ : κ => ℂ) (p := 2) (by norm_num) i (1 : ℂ)]
    simp
  have hop := (ellTwoDiagonal lam hC).le_opNorm (ellTwoCoordinateBasis κ i)
  rw [norm_ellTwoDiagonal_coordinateBasis, hone, mul_one] at hop
  exact hop

/-- **Hilbert–Schmidt exactly for square-summable multipliers.** -/
theorem isHilbertSchmidt_ellTwoDiagonal_iff (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) :
    ContinuousLinearMap.IsHilbertSchmidt (ellTwoDiagonal lam hC)
      ↔ Summable (fun i => ‖lam i‖ ^ 2) := by
  rw [ContinuousLinearMap.isHilbertSchmidt_iff_summable (ellTwoCoordinateBasis κ)]
  exact summable_congr fun i => by rw [norm_ellTwoDiagonal_coordinateBasis]

/-- The Hilbert–Schmidt norm of a diagonal operator is the square-summable total of its
multipliers. -/
theorem hsNormSq_ellTwoDiagonal (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (hsum : Summable (fun i => ‖lam i‖ ^ 2)) :
    ContinuousLinearMap.hsNormSq (ellTwoDiagonal lam hC) = ∑' i, ‖lam i‖ ^ 2 := by
  rw [ContinuousLinearMap.hsNormSq_eq
      ((isHilbertSchmidt_ellTwoDiagonal_iff lam hC).mpr hsum) (ellTwoCoordinateBasis κ)]
  exact tsum_congr fun i => by rw [norm_ellTwoDiagonal_coordinateBasis]

/-! ## Adjoint, products, and the modulus -/

omit [DecidableEq κ] in
/-- **The adjoint of a diagonal operator is diagonal with conjugated multipliers.** -/
theorem adjoint_ellTwoDiagonal (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) :
    ContinuousLinearMap.adjoint (ellTwoDiagonal lam hC)
      = ellTwoDiagonal (fun i => (starRingEnd ℂ) (lam i)) (fun i => by simpa using hC i) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  rw [RCLike.inner_apply, RCLike.inner_apply, ellTwoDiagonal_apply, ellTwoDiagonal_apply,
    map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring

omit [DecidableEq κ] in
/-- Diagonal operators compose by multiplying multipliers. -/
theorem ellTwoDiagonal_comp (lam mu : κ → ℂ) {C D : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C)
    (hD : ∀ i, ‖mu i‖ ≤ D) {E : ℝ} (hE : ∀ i, ‖lam i * mu i‖ ≤ E) :
    ellTwoDiagonal lam hC ∘L ellTwoDiagonal mu hD = ellTwoDiagonal (fun i => lam i * mu i) hE := by
  refine ContinuousLinearMap.ext fun f => ?_
  ext i
  rw [ContinuousLinearMap.comp_apply, ellTwoDiagonal_apply, ellTwoDiagonal_apply,
    ellTwoDiagonal_apply, mul_assoc]

omit [DecidableEq κ] in
/-- The squared moduli of a bounded family are bounded by the squared bound. -/
theorem norm_ofReal_sq_le (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (i : κ) :
    ‖((‖lam i‖ ^ 2 : ℝ) : ℂ)‖ ≤ C ^ 2 := by
  have h0 : (0 : ℝ) ≤ ‖lam i‖ := norm_nonneg _
  have h1 := hC i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

omit [DecidableEq κ] in
/-- The conjugate-times-self family is bounded by the squared bound. -/
theorem norm_conj_mul_self_le (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) (i : κ) :
    ‖(starRingEnd ℂ) (lam i) * lam i‖ ≤ C ^ 2 := by
  have h0 : (0 : ℝ) ≤ ‖lam i‖ := norm_nonneg _
  have h1 := hC i
  rw [norm_mul, RCLike.norm_conj]
  nlinarith

omit [DecidableEq κ] in
/-- **The modulus square of a diagonal operator is diagonal with the squared multiplier moduli.**
The singular values of a diagonal operator are therefore exactly the moduli of its multipliers. -/
theorem adjoint_comp_self_ellTwoDiagonal (lam : κ → ℂ) {C : ℝ} (hC : ∀ i, ‖lam i‖ ≤ C) :
    ContinuousLinearMap.adjoint (ellTwoDiagonal lam hC) ∘L ellTwoDiagonal lam hC
      = ellTwoDiagonal (fun i => ((‖lam i‖ ^ 2 : ℝ) : ℂ)) (norm_ofReal_sq_le lam hC) := by
  rw [adjoint_ellTwoDiagonal,
    ellTwoDiagonal_comp (fun i => (starRingEnd ℂ) (lam i)) lam
      (fun i => by simpa using hC i) hC (norm_conj_mul_self_le lam hC)]
  refine ContinuousLinearMap.ext fun f => ?_
  ext i
  rw [ellTwoDiagonal_apply, ellTwoDiagonal_apply]
  congr 1
  rw [Complex.ofReal_pow, ← Complex.conj_mul']

/-- **The multiplier modulus squared is the diagonal matrix element of the modulus square.** -/
theorem inner_coordinateBasis_adjoint_comp_self_ellTwoDiagonal (lam : κ → ℂ) {C : ℝ}
    (hC : ∀ i, ‖lam i‖ ≤ C) (i : κ) :
    ⟪ellTwoCoordinateBasis κ i,
        (ContinuousLinearMap.adjoint (ellTwoDiagonal lam hC) ∘L ellTwoDiagonal lam hC)
          (ellTwoCoordinateBasis κ i)⟫_ℂ = ((‖lam i‖ ^ 2 : ℝ) : ℂ) := by
  rw [adjoint_comp_self_ellTwoDiagonal, inner_coordinateBasis_ellTwoDiagonal]

end HTGeometry

end
