/-
# The diagonal block operator on an orthonormal family

A finite orthonormal family and a finite family of complex numbers determine a diagonal operator:
the sum of the scaled rank-one projections.  Powers of such an operator are the diagonal operators
of the powers of the entries, its trace is the sum of the entries, its rank is the size of the
family, and its norm is the largest entry.  When the family is orthogonal to both the range and the
kernel complement of another operator, the two multiply to zero in both orders, so the powers of
their sum split.

This is the carrier of the vanishing micro-spectrum block in the determinant-completion law.

Main results:
* `blockOpOn`, `blockOp` — **the diagonal block operator**.
* `blockOp_comp`, `blockOp_pow` — its products and powers are diagonal in the same family.
* `opTrace_blockOp` — **its trace is the sum of its entries**.
* `norm_blockOpOn_le`, `hasRankLE_blockOpOn` — its norm and its rank.
* `add_pow_succ_of_mul_eq_zero` — the powers of an orthogonal sum split.
-/
import GaloisForLFunctions.HTGeometry.HilbertSchmidtTrace
import GaloisForLFunctions.RHTower.SchattenApproximation

open ContinuousLinearMap
open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

/-- **The powers of an orthogonal sum split.**  In any ring, two elements whose products vanish in
both orders have `(a+b)^{k+1} = a^{k+1} + b^{k+1}`. -/
theorem add_pow_succ_of_mul_eq_zero {R : Type*} [Ring R] {a b : R}
    (hab : a * b = 0) (hba : b * a = 0) : ∀ k : ℕ, (a + b) ^ (k + 1) = a ^ (k + 1) + b ^ (k + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : a ^ (k + 1) * b = 0 := by rw [pow_succ, mul_assoc, hab, mul_zero]
      have h2 : b ^ (k + 1) * a = 0 := by rw [pow_succ, mul_assoc, hba, mul_zero]
      calc (a + b) ^ (k + 1 + 1) = (a + b) ^ (k + 1) * (a + b) := by rw [pow_succ]
        _ = (a ^ (k + 1) + b ^ (k + 1)) * (a + b) := by rw [ih]
        _ = a ^ (k + 1) * a + a ^ (k + 1) * b + (b ^ (k + 1) * a + b ^ (k + 1) * b) := by
              noncomm_ring
        _ = a ^ (k + 1 + 1) + b ^ (k + 1 + 1) := by
              rw [h1, h2, ← pow_succ, ← pow_succ, add_zero, zero_add]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The diagonal block over a finite index set: the sum of the scaled rank-one projections. -/
def blockOpOn {m : ℕ} (s : Finset (Fin m)) (e : Fin m → H) (μ : Fin m → ℂ) : H →L[ℂ] H :=
  ∑ i ∈ s, (innerSL ℂ (e i)).smulRight (μ i • e i)

/-- **The diagonal block operator** with entries `μ` on an orthonormal family `e`. -/
def blockOp {m : ℕ} (e : Fin m → H) (μ : Fin m → ℂ) : H →L[ℂ] H := blockOpOn Finset.univ e μ

variable {m : ℕ} {e : Fin m → H} {μ ν : Fin m → ℂ}

theorem blockOpOn_apply (s : Finset (Fin m)) (e : Fin m → H) (μ : Fin m → ℂ) (x : H) :
    blockOpOn s e μ x = ∑ i ∈ s, (μ i * ⟪e i, x⟫_ℂ) • e i := by
  rw [blockOpOn, sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smulRight_apply, smul_smul, innerSL_apply_apply, mul_comm]

theorem blockOp_apply (e : Fin m → H) (μ : Fin m → ℂ) (x : H) :
    blockOp e μ x = ∑ i, (μ i * ⟪e i, x⟫_ℂ) • e i := blockOpOn_apply _ e μ x

theorem blockOpOn_add_compl (s : Finset (Fin m)) (e : Fin m → H) (μ : Fin m → ℂ) :
    blockOpOn s e μ + blockOpOn sᶜ e μ = blockOp e μ := by
  classical
  rw [blockOpOn, blockOpOn, blockOp, blockOpOn]
  exact Finset.sum_add_sum_compl s _

theorem blockOp_sub_blockOpOn (s : Finset (Fin m)) (e : Fin m → H) (μ : Fin m → ℂ) :
    blockOp e μ - blockOpOn s e μ = blockOpOn sᶜ e μ := by
  rw [← blockOpOn_add_compl s e μ]
  abel

/-- The block has rank at most the size of its index set. -/
theorem hasRankLE_blockOpOn (s : Finset (Fin m)) (e : Fin m → H) (μ : Fin m → ℂ) :
    HasRankLE (blockOpOn s e μ) s.card := by
  classical
  refine ⟨Submodule.span ℂ ((s.image e : Finset H) : Set H),
    FiniteDimensional.span_of_finite ℂ (Finset.finite_toSet _), ?_, ?_⟩
  · exact (finrank_span_finset_le_card _).trans Finset.card_image_le
  · intro x
    rw [blockOpOn_apply]
    refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)

theorem hasRankLE_blockOp (e : Fin m → H) (μ : Fin m → ℂ) : HasRankLE (blockOp e μ) m := by
  have h := hasRankLE_blockOpOn (Finset.univ : Finset (Fin m)) e μ
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- The squared norm of an orthonormal combination is the sum of the squared coefficients. -/
theorem norm_sq_orthonormal_sum (he : Orthonormal ℂ e) (c : Fin m → ℂ) (s : Finset (Fin m)) :
    ‖∑ i ∈ s, c i • e i‖ ^ (2 : ℕ) = ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) := by
  have h := he.inner_sum c c s
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [RCLike.conj_mul] at h
  exact_mod_cast h

/-- **The block norm is the largest entry.** -/
theorem norm_blockOpOn_le (he : Orthonormal ℂ e) (s : Finset (Fin m)) (μ : Fin m → ℂ)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, ‖μ i‖ ≤ M) : ‖blockOpOn s e μ‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun x => ?_
  have hsq : ‖blockOpOn s e μ x‖ ^ (2 : ℕ) ≤ (M * ‖x‖) ^ (2 : ℕ) := by
    rw [blockOpOn_apply, norm_sq_orthonormal_sum he _ s]
    have hstep : ∀ i ∈ s, ‖μ i * ⟪e i, x⟫_ℂ‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) * ‖⟪e i, x⟫_ℂ‖ ^ (2 : ℕ) := by
      intro i hi
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hM i hi) 2)
        (by positivity)
    calc ∑ i ∈ s, ‖μ i * ⟪e i, x⟫_ℂ‖ ^ (2 : ℕ) ≤ ∑ i ∈ s, M ^ (2 : ℕ) * ‖⟪e i, x⟫_ℂ‖ ^ (2 : ℕ) :=
          Finset.sum_le_sum hstep
      _ = M ^ (2 : ℕ) * ∑ i ∈ s, ‖⟪e i, x⟫_ℂ‖ ^ (2 : ℕ) := by rw [Finset.mul_sum]
      _ ≤ M ^ (2 : ℕ) * ‖x‖ ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left (he.sum_inner_products_le x) (by positivity)
      _ = (M * ‖x‖) ^ (2 : ℕ) := by ring
  have hnn : (0 : ℝ) ≤ M * ‖x‖ := mul_nonneg hM0 (norm_nonneg x)
  exact (sq_le_sq₀ (norm_nonneg _) hnn).mp hsq

/-- The block operators of an orthonormal family compose entrywise. -/
theorem blockOp_comp (he : Orthonormal ℂ e) (μ ν : Fin m → ℂ) :
    blockOp e μ ∘L blockOp e ν = blockOp e (fun i => μ i * ν i) := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, blockOp_apply, blockOp_apply, blockOp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he.inner_right_fintype (fun j => ν j * ⟪e j, x⟫_ℂ) i, mul_assoc]

theorem blockOp_pow (he : Orthonormal ℂ e) (μ : Fin m → ℂ) :
    ∀ k : ℕ, blockOp e μ ^ (k + 1) = blockOp e (fun i => μ i ^ (k + 1)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hmul : blockOp e μ ^ (k + 1 + 1)
          = blockOp e (fun i => μ i ^ (k + 1)) ∘L blockOp e μ := by
        rw [pow_succ, ih]
        rfl
      rw [hmul, blockOp_comp he]
      refine congrArg _ (funext fun i => ?_)
      rw [← pow_succ]

/-- **The trace of a diagonal block is the sum of its entries.** -/
theorem opTrace_blockOp [CompleteSpace H] (he : Orthonormal ℂ e) (μ : Fin m → ℂ) :
    opTrace (blockOp e μ) = ∑ i, μ i := by
  classical
  set b := hsBasis ℂ H with hb
  have hterm : ∀ k, ⟪b k, blockOp e μ (b k)⟫_ℂ
      = ∑ i, μ i * (⟪e i, b k⟫_ℂ * ⟪b k, e i⟫_ℂ) := by
    intro k
    rw [blockOp_apply, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right]
    ring
  have hsummable : ∀ i : Fin m, Summable fun k => μ i * (⟪e i, b k⟫_ℂ * ⟪b k, e i⟫_ℂ) :=
    fun i => (b.summable_inner_mul_inner (e i) (e i)).mul_left (μ i)
  have hswap : (∑' k, ∑ i, μ i * (⟪e i, b k⟫_ℂ * ⟪b k, e i⟫_ℂ))
      = ∑ i, ∑' k, μ i * (⟪e i, b k⟫_ℂ * ⟪b k, e i⟫_ℂ) :=
    Summable.tsum_finsetSum fun i _ => hsummable i
  have hinner : ∀ i : Fin m, (∑' k, μ i * (⟪e i, b k⟫_ℂ * ⟪b k, e i⟫_ℂ)) = μ i := by
    intro i
    rw [tsum_mul_left]
    have hpar : (∑' k, ⟪e i, b k⟫_ℂ * ⟪b k, e i⟫_ℂ) = ⟪e i, e i⟫_ℂ :=
      b.tsum_inner_mul_inner (e i) (e i)
    rw [hpar, inner_self_eq_norm_sq_to_K, he.1 i]
    norm_num
  rw [opTrace]
  rw [show (fun k => ⟪b k, blockOp e μ (b k)⟫_ℂ)
      = fun k => ∑ i, μ i * (⟪e i, b k⟫_ℂ * ⟪b k, e i⟫_ℂ) from funext hterm, hswap]
  exact Finset.sum_congr rfl fun i _ => hinner i

/-- A block on vectors killed by `A` is annihilated by `A` on the left. -/
theorem comp_blockOp_eq_zero (A : H →L[ℂ] H) (hA : ∀ i, A (e i) = 0) (μ : Fin m → ℂ) :
    A ∘L blockOp e μ = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, blockOp_apply, map_sum]
  simp [hA]

/-- A block on vectors orthogonal to the range of `A` annihilates `A` on the left. -/
theorem blockOp_comp_eq_zero (A : H →L[ℂ] H) (hA : ∀ i x, ⟪e i, A x⟫_ℂ = 0) (μ : Fin m → ℂ) :
    blockOp e μ ∘L A = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [comp_apply, blockOp_apply]
  simp [hA]

end

end GaloisForLFunctions.HTGeometry
