import Mathlib

/-!
# Gram–Schmidt norms and the Gram determinant (toward the Szegő determinant ratio)

Foundational identities relating the Gram–Schmidt vectors to distances, used to express the
consecutive Toeplitz/Gram determinant ratio `det Gₙ₊₁ / det Gₙ` as the squared distance
`dist²(vₙ₊₁, span{v₀,…,vₙ})` — the monic-orthogonal-polynomial norm at the heart of the first
Szegő limit theorem.

`gramSchmidt_inner_left_self` — `⟪gsᵢ, vᵢ⟫ = ⟪gsᵢ, gsᵢ⟫` (the Gram–Schmidt vector is orthogonal
to the correction terms, so its inner product with the original vector is its own squared length,
the increment in the Gram determinant recursion).
-/

open scoped InnerProductSpace
open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The `i`-th Gram–Schmidt vector is orthogonal to the lower correction terms, so its inner
product with the original vector `vᵢ` equals its own squared length. -/
theorem gramSchmidt_inner_left_self {n : ℕ} (v : Fin n → E) (i : Fin n) :
    ⟪gramSchmidt ℂ v i, v i⟫_ℂ = ⟪gramSchmidt ℂ v i, gramSchmidt ℂ v i⟫_ℂ := by
  conv_lhs => rw [gramSchmidt_def'' ℂ v i]
  rw [inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero]
  intro j hj
  have hij : i ≠ j := ((Finset.mem_Iio.mp hj).ne).symm
  rw [inner_smul_right, gramSchmidt_orthogonal ℂ v hij, mul_zero]

open Submodule in
/-- A later Gram–Schmidt vector is orthogonal to an earlier original vector: `⟪gsⱼ, vᵢ⟫ = 0` for
`i < j`.  Since `vᵢ ∈ span{gs₀,…,gsᵢ}` and `gsⱼ` is orthogonal to that span, the change-of-basis
matrix `⟪gsⱼ, vᵢ⟫/‖gsⱼ‖²` is lower-triangular; with unit diagonal (`gramSchmidt_inner_left_self`)
its determinant is `1`. -/
theorem inner_gramSchmidt_left_eq_zero_of_lt {n : ℕ} (v : Fin n → E) {i j : Fin n} (hij : i < j) :
    ⟪gramSchmidt ℂ v j, v i⟫_ℂ = 0 := by
  refine Submodule.inner_left_of_mem_orthogonal (mem_span_gramSchmidt ℂ v (le_refl i)) ?_
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    have hkj : k ≠ j := (lt_of_le_of_lt (Set.mem_Iic.mp hk) hij).ne
    exact gramSchmidt_orthogonal ℂ v hkj
  | zero => rw [inner_zero_left]
  | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]

/-- **Change of basis to the Gram–Schmidt vectors.**  Each original vector expands as
`vᵢ = ∑ⱼ (⟪gsⱼ, vᵢ⟫/‖gsⱼ‖²) • gsⱼ`.  The coefficient matrix is lower-triangular with unit diagonal,
so its determinant is `1`; this is the transition making `det(gram v) = ∏‖gsⱼ‖²`. -/
theorem eq_sum_gramSchmidt {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) (i : Fin n) :
    v i = ∑ j, (⟪gramSchmidt ℂ v j, v i⟫_ℂ / (‖gramSchmidt ℂ v j‖ : ℂ) ^ 2) • gramSchmidt ℂ v j := by
  have hzero : ∀ j ∈ Finset.univ, j ∉ Finset.Iic i →
      (⟪gramSchmidt ℂ v j, v i⟫_ℂ / (‖gramSchmidt ℂ v j‖ : ℂ) ^ 2) • gramSchmidt ℂ v j = 0 := by
    intro j _ hj
    have hij : i < j := by simpa [Finset.mem_Iic] using hj
    rw [inner_gramSchmidt_left_eq_zero_of_lt v hij, zero_div, zero_smul]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic i)) hzero,
    ← Finset.add_sum_Iio_eq_sum_Iic i]
  have hcoef : ⟪gramSchmidt ℂ v i, v i⟫_ℂ / (‖gramSchmidt ℂ v i‖ : ℂ) ^ 2 = 1 := by
    rw [gramSchmidt_inner_left_self]
    have h : ⟪gramSchmidt ℂ v i, gramSchmidt ℂ v i⟫_ℂ = ((‖gramSchmidt ℂ v i‖ ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h, ← Complex.ofReal_pow, div_self]
    exact Complex.ofReal_ne_zero.mpr
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)))
  rw [hcoef, one_smul]
  exact gramSchmidt_def'' ℂ v i

open Matrix in
/-- **Gram entry via Gram–Schmidt.**  The Gram inner product `⟪vᵢ, vⱼ⟫` expands over the
orthogonal Gram–Schmidt vectors as `∑ₖ conj(Bᵢₖ) Bⱼₖ ‖gsₖ‖²`, with `Bᵢₖ = ⟪gsₖ, vᵢ⟫/‖gsₖ‖²`.
This is the entrywise form of the factorization `gram v = (conj B) · diag ‖gs‖² · Bᵀ`, whose
determinant (with `det B = 1`, since `B` is lower-triangular with unit diagonal) is `∏ₖ ‖gsₖ‖²`. -/
theorem gram_entry_eq {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) (i j : Fin n) :
    ⟪v i, v j⟫_ℂ = ∑ k, (starRingEnd ℂ) (⟪gramSchmidt ℂ v k, v i⟫_ℂ / (‖gramSchmidt ℂ v k‖ : ℂ) ^ 2)
      * (⟪gramSchmidt ℂ v k, v j⟫_ℂ / (‖gramSchmidt ℂ v k‖ : ℂ) ^ 2)
      * ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v k⟫_ℂ := by
  conv_lhs => rw [eq_sum_gramSchmidt v hv i, eq_sum_gramSchmidt v hv j]
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_smul_left, inner_sum, Finset.sum_eq_single k]
  · rw [inner_smul_right]; ring
  · intro l _ hlk
    rw [inner_smul_right, gramSchmidt_orthogonal ℂ v (Ne.symm hlk), mul_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

open Matrix in
/-- **Gram determinant equals the product of squared Gram–Schmidt lengths.**  For a linearly
independent family `v`, `det (gram v) = ∏ₖ ⟪gsₖ, gsₖ⟫ = ∏ₖ ‖gsₖ‖²`.  Consequently the consecutive
Toeplitz/Gram determinant ratio `det Gₙ₊₁/det Gₙ` collapses to `‖gsₙ₊₁‖² = dist²(vₙ₊₁, span{v<ₙ₊₁})`,
the monic-orthogonal-polynomial norm of the first Szegő limit theorem.  The proof factors
`gram v = (conj B)·diag ⟪gsₖ,gsₖ⟫·Bᵀ` with `Bᵢₖ = ⟪gsₖ,vᵢ⟫/‖gsₖ‖²` lower-triangular with unit
diagonal (`det B = 1`). -/
theorem det_gram_eq_prod {n : ℕ} (v : Fin n → E) (hv : LinearIndependent ℂ v) :
    (Matrix.gram ℂ v).det = ∏ k, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v k⟫_ℂ := by
  set B : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i k => ⟪gramSchmidt ℂ v k, v i⟫_ℂ / (‖gramSchmidt ℂ v k‖ : ℂ) ^ 2) with hB
  set D : Fin n → ℂ := fun k => ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v k⟫_ℂ with hD
  have hgram : Matrix.gram ℂ v = B.map (starRingEnd ℂ) * Matrix.diagonal D * Bᵀ := by
    ext i j
    rw [Matrix.gram_apply, gram_entry_eq v hv i j, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Matrix.mul_diagonal, Matrix.map_apply, Matrix.transpose_apply]
    simp only [hB, Matrix.of_apply, hD]
    ring
  have hlow : ∀ i j, i < j → B i j = 0 := by
    intro i j hij
    show ⟪gramSchmidt ℂ v j, v i⟫_ℂ / (‖gramSchmidt ℂ v j‖ : ℂ) ^ 2 = 0
    rw [inner_gramSchmidt_left_eq_zero_of_lt v hij, zero_div]
  have hdetB : B.det = 1 := by
    rw [Matrix.det_of_lowerTriangular B hlow]
    apply Finset.prod_eq_one
    intro i _
    show ⟪gramSchmidt ℂ v i, v i⟫_ℂ / (‖gramSchmidt ℂ v i‖ : ℂ) ^ 2 = 1
    rw [gramSchmidt_inner_left_self]
    have h : ⟪gramSchmidt ℂ v i, gramSchmidt ℂ v i⟫_ℂ = ((‖gramSchmidt ℂ v i‖ ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h, ← Complex.ofReal_pow, div_self]
    exact Complex.ofReal_ne_zero.mpr
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hv)))
  have hdetBmap : (B.map (starRingEnd ℂ)).det = 1 :=
    (RingHom.map_det (starRingEnd ℂ) B).symm.trans (by rw [hdetB, map_one])
  rw [hgram, Matrix.det_mul, Matrix.det_mul, hdetBmap, Matrix.det_transpose, hdetB,
    Matrix.det_diagonal, one_mul, mul_one]

/-- **Gram–Schmidt is causal.**  `gramSchmidt f n` depends only on the values `f m` for `m ≤ n`.
Two `ℕ`-indexed families agreeing up to `n` have the same `n`-th Gram–Schmidt vector.  This lets
the consecutive Toeplitz determinant ratio telescope: adding one more monomial contributes exactly
one new factor `‖gsₙ₊₁‖²` to `∏ₖ ‖gsₖ‖²`. -/
theorem gramSchmidt_causal (f g : ℕ → E) (n : ℕ) (h : ∀ m, m ≤ n → f m = g m) :
    gramSchmidt ℂ f n = gramSchmidt ℂ g n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [gramSchmidt_def ℂ f n, gramSchmidt_def ℂ g n, h n le_rfl]
    congr 1
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hin : i < n := Finset.mem_Iio.mp hi
    rw [ih i hin (fun m hm => h m (hm.trans hin.le))]

/-- The correction `v k - gramSchmidt v k` lies in the span of the earlier Gram–Schmidt vectors. -/
theorem sub_gramSchmidt_mem_span (v : ℕ → E) (k : ℕ) :
    v k - gramSchmidt ℂ v k ∈ Submodule.span ℂ (gramSchmidt ℂ v '' Set.Iio k) := by
  rw [gramSchmidt_def'' ℂ v k, add_sub_cancel_left]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)

/-- **Gram–Schmidt minimizes the distance to the span of predecessors.**  `gramSchmidt v k` is the
component of `v k` orthogonal to `span{gs₀,…,gs_{k-1}} = span{v₀,…,v_{k-1}}`, so its norm is a lower
bound for `‖v k - w‖` over every `w` in that span.  This is the least-squares characterization that,
combined with the multiplication-by-`z` isometry, gives the monotone decrease of the monic
orthogonal polynomial norms. -/
theorem norm_gramSchmidt_le_of_mem_span (v : ℕ → E) (k : ℕ) {w : E}
    (hw : w ∈ Submodule.span ℂ (gramSchmidt ℂ v '' Set.Iio k)) :
    ‖gramSchmidt ℂ v k‖ ≤ ‖v k - w‖ := by
  have hu := sub_gramSchmidt_mem_span v k
  have horth : ∀ x ∈ Submodule.span ℂ (gramSchmidt ℂ v '' Set.Iio k),
      inner ℂ (gramSchmidt ℂ v k) x = (0 : ℂ) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, hi, rfl⟩ := hy
        exact gramSchmidt_orthogonal ℂ v (Set.mem_Iio.mp hi).ne'
    | zero => rw [inner_zero_right]
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]
  have hmem2 : (v k - gramSchmidt ℂ v k) - w ∈ Submodule.span ℂ (gramSchmidt ℂ v '' Set.Iio k) :=
    Submodule.sub_mem _ hu hw
  have hip : inner ℂ (gramSchmidt ℂ v k) ((v k - gramSchmidt ℂ v k) - w) = (0 : ℂ) :=
    horth _ hmem2
  have hsplit : v k - w = gramSchmidt ℂ v k + ((v k - gramSchmidt ℂ v k) - w) := by abel
  rw [hsplit]
  have hpy : ‖gramSchmidt ℂ v k + ((v k - gramSchmidt ℂ v k) - w)‖ ^ 2
      = ‖gramSchmidt ℂ v k‖ ^ 2
        + 2 * RCLike.re (inner ℂ (gramSchmidt ℂ v k) ((v k - gramSchmidt ℂ v k) - w))
        + ‖(v k - gramSchmidt ℂ v k) - w‖ ^ 2 :=
    norm_add_sq (𝕜 := ℂ) _ _
  rw [hip] at hpy
  simp only [map_zero, mul_zero, add_zero] at hpy
  nlinarith [norm_nonneg (gramSchmidt ℂ v k), norm_nonneg ((v k - gramSchmidt ℂ v k) - w),
    norm_nonneg (gramSchmidt ℂ v k + ((v k - gramSchmidt ℂ v k) - w))]

/-- **The Gram–Schmidt length is the least distance to the span of predecessors.**  `‖gramSchmidt v k‖`
is the minimum of `‖v k - w‖` over `w` in the span of the earlier vectors, attained at
`w = v k - gramSchmidt v k`.  For the analytic monomials in `L²(μ)` this is exactly the monic
orthogonal polynomial norm `‖Φₖ‖ = dist(zᵏ, {polynomials of degree < k})`. -/
theorem isLeast_norm_gramSchmidt (v : ℕ → E) (k : ℕ) :
    IsLeast ((fun w => ‖v k - w‖) '' (Submodule.span ℂ (gramSchmidt ℂ v '' Set.Iio k)))
      ‖gramSchmidt ℂ v k‖ := by
  constructor
  · refine ⟨v k - gramSchmidt ℂ v k, sub_gramSchmidt_mem_span v k, ?_⟩
    simp only [sub_sub_cancel]
  · rintro _ ⟨w, hw, rfl⟩
    exact norm_gramSchmidt_le_of_mem_span v k hw

/-- The Gram–Schmidt length is the greatest lower bound of the distances to the predecessor span. -/
theorem isGLB_norm_gramSchmidt (v : ℕ → E) (k : ℕ) :
    IsGLB ((fun w => ‖v k - w‖) '' (Submodule.span ℂ (gramSchmidt ℂ v '' Set.Iio k)))
      ‖gramSchmidt ℂ v k‖ :=
  (isLeast_norm_gramSchmidt v k).isGLB

/-- **Gram–Schmidt commutes with the `Fin (n+1)`-restriction of an `ℕ`-family.**  The Gram–Schmidt
vector of the finite restriction `fun i : Fin (n+1) => w i` at index `k` equals the Gram–Schmidt
vector of the full `ℕ`-indexed family `w` at the coerced index `↑k`.  Both `ℕ` and `Fin (n+1)` are
well-ordered with bottom, so the causal recursion (`gramSchmidt_def`) reindexes across the
order-embedding `Fin.val`; this is what lets a `Fin`-indexed Gram determinant be read off the single
`ℕ`-indexed Gram–Schmidt sequence. -/
theorem gramSchmidt_fin_val (w : ℕ → E) (n : ℕ) (k : Fin n) :
    gramSchmidt ℂ (fun i : Fin n => w (i : ℕ)) k = gramSchmidt ℂ w (k : ℕ) := by
  have key : ∀ m : ℕ, ∀ hm : m < n,
      gramSchmidt ℂ (fun i : Fin n => w (i : ℕ)) ⟨m, hm⟩ = gramSchmidt ℂ w m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      rw [gramSchmidt_def ℂ (fun i : Fin n => w (i : ℕ)) ⟨m, hm⟩, gramSchmidt_def ℂ w m]
      congr 1
      refine Finset.sum_bij' (fun (i : Fin n) _ => (i : ℕ))
        (fun (j : ℕ) hj => (⟨j, lt_trans (Finset.mem_Iio.mp hj) hm⟩ : Fin n))
        ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_Iio] at ha ⊢
        exact ha
      · intro b hb
        rw [Finset.mem_Iio] at hb ⊢
        exact hb
      · intro a ha; rfl
      · intro b hb; rfl
      · intro a ha
        have haf : a < (⟨m, hm⟩ : Fin n) := Finset.mem_Iio.mp ha
        have hlt : (a : ℕ) < m := haf
        have hia := ih (a : ℕ) hlt a.2
        rw [Fin.eta] at hia
        rw [hia]
  exact key (k : ℕ) k.2

/-- **The consecutive monomial Gram determinant telescopes.**  For a linearly independent
`ℕ`-indexed family `w`, adding one vector multiplies the Gram determinant by exactly one new factor:
`det Gₙ₊₁ = det Gₙ · ⟪gsₙ, gsₙ⟫`, where `gs` is the (single, `ℕ`-indexed) Gram–Schmidt sequence.
Hence the ratio `det Gₙ₊₁ / det Gₙ = ‖gsₙ‖²` — the squared distance from `wₙ` to `span{w₀,…,wₙ₋₁}`,
the monic orthogonal polynomial norm of the first Szegő limit theorem. -/
theorem det_gram_fin_succ (w : ℕ → E) (N : ℕ)
    (h1 : LinearIndependent ℂ (fun i : Fin (N + 1) => w (i : ℕ))) :
    (Matrix.gram ℂ (fun i : Fin (N + 1) => w (i : ℕ))).det
      = (Matrix.gram ℂ (fun i : Fin N => w (i : ℕ))).det
        * ⟪gramSchmidt ℂ w N, gramSchmidt ℂ w N⟫_ℂ := by
  have hcast : (fun i : Fin N => w (i : ℕ))
      = (fun i : Fin (N + 1) => w (i : ℕ)) ∘ Fin.castSucc := by
    funext i; simp
  have h0 : LinearIndependent ℂ (fun i : Fin N => w (i : ℕ)) := by
    rw [hcast]; exact h1.comp _ (Fin.castSucc_injective N)
  rw [det_gram_eq_prod _ h1, det_gram_eq_prod _ h0, Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [gramSchmidt_fin_val w (N + 1) i.castSucc, gramSchmidt_fin_val w N i, Fin.val_castSucc]
  · rw [gramSchmidt_fin_val w (N + 1) (Fin.last N), Fin.val_last]

end GaloisForLFunctions.HTGeometry
