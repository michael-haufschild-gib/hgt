import Mathlib

/-!
# Finite unitriangular repair genealogy

On `H_N = ℂ^{N+1}` with orthonormal basis `e_0, …, e_N`, the backward truncated shift `B_N`
sends `e_n ↦ e_{n-1}` and kills `e_0`.  A stationary sequential repair certificate
`e_n ∼ α e_{n-1}` is the genealogy formation operator `G_{α,N} = 1 - α B_N`.

* `finiteGenealogy_mul_inverse`, `finiteGenealogyInverse_mul` : `G_{α,N}` is invertible with
  inverse the finite geometric series `∑_{k ≤ N} α^k B_N^k` (equation GR.5);
* `finiteSemanticReader_comp_finiteGenealogy` : the exact conservation identity
  `b_{α,N} G_{α,N} = π_0` (GR.6);
* `finiteSemanticReader_finiteGenealogy_single` : every repair syzygy is semantic-null and the old
  carrier is read exactly;
* `norm_finiteGenealogyInverse_le`, `sqrt_le_norm_finiteGenealogyInverse`,
  `pow_le_norm_finiteGenealogyInverse` : the three inverse bounds (GR.7);
* `finiteGenealogy_reciprocal` : the finite reciprocal boundary law with its terminal
  projection (GR.24).
-/

open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.UnitriangularGenealogy

noncomputable section

/-- The finite genealogy carrier `H_N = ℂ^{N+1}`. -/
abbrev FiniteCarrier (N : ℕ) : Type := EuclideanSpace ℂ (Fin (N + 1))

/-- Powers of a scalar multiple of an operator. -/
theorem smul_pow_operator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ)
    (T : E →L[ℂ] E) (n : ℕ) : (c • T) ^ n = c ^ n • T ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ, pow_succ, smul_mul_smul_comm]

/-- Scalars pass through a left composition factor. -/
theorem mul_smul_operator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (c : ℂ)
    (T U : E →L[ℂ] E) : T * (c • U) = c • (T * U) := by
  ext x
  simp [mul_apply_eq_comp]

variable {N : ℕ}

/-- Zero extension of a finite vector to a sequence on `ℕ`. -/
def extendSeq (x : FiniteCarrier N) (n : ℕ) : ℂ :=
  if h : n < N + 1 then x.ofLp ⟨n, h⟩ else 0

theorem extendSeq_of_lt (x : FiniteCarrier N) {n : ℕ} (h : n < N + 1) :
    extendSeq x n = x.ofLp ⟨n, h⟩ := dif_pos h

theorem extendSeq_of_le (x : FiniteCarrier N) {n : ℕ} (h : N + 1 ≤ n) :
    extendSeq x n = 0 := dif_neg (by omega)

@[simp] theorem extendSeq_fin (x : FiniteCarrier N) (m : Fin (N + 1)) :
    extendSeq x m = x.ofLp m := by
  rw [extendSeq_of_lt x m.isLt]

@[simp] theorem extendSeq_add (x y : FiniteCarrier N) (n : ℕ) :
    extendSeq (x + y) n = extendSeq x n + extendSeq y n := by
  unfold extendSeq
  split_ifs <;> simp

@[simp] theorem extendSeq_smul (c : ℂ) (x : FiniteCarrier N) (n : ℕ) :
    extendSeq (c • x) n = c * extendSeq x n := by
  unfold extendSeq
  split_ifs <;> simp

theorem sum_fin_eq_sum_range (f : ℕ → ℂ) :
    ∑ m : Fin (N + 1), f m = ∑ n ∈ Finset.range (N + 1), f n :=
  Fin.sum_univ_eq_sum_range f (N + 1)

theorem sum_fin_eq_sum_range_real (f : ℕ → ℝ) :
    ∑ m : Fin (N + 1), f m = ∑ n ∈ Finset.range (N + 1), f n :=
  Fin.sum_univ_eq_sum_range f (N + 1)

theorem norm_sq_eq_sum_range (x : FiniteCarrier N) :
    ‖x‖ ^ 2 = ∑ n ∈ Finset.range (N + 1), ‖extendSeq x n‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← sum_fin_eq_sum_range_real]
  simp

/-! ## The truncated shifts -/

/-- The backward truncated shift `B_N e_0 = 0`, `B_N e_n = e_{n-1}`, as a linear map. -/
def truncBackwardₗ (N : ℕ) : FiniteCarrier N →ₗ[ℂ] FiniteCarrier N where
  toFun x := WithLp.toLp 2 (fun m : Fin (N + 1) => extendSeq x (m + 1))
  map_add' x y := by
    ext m
    simp
  map_smul' c x := by
    ext m
    simp

/-- The backward truncated shift `B_N` (GR.1). -/
def truncBackward (N : ℕ) : FiniteCarrier N →L[ℂ] FiniteCarrier N :=
  LinearMap.toContinuousLinearMap (truncBackwardₗ N)

@[simp] theorem truncBackward_apply (x : FiniteCarrier N) (m : Fin (N + 1)) :
    (truncBackward N x).ofLp m = extendSeq x (m + 1) := rfl

theorem extendSeq_truncBackward (x : FiniteCarrier N) (n : ℕ) :
    extendSeq (truncBackward N x) n = if n < N + 1 then extendSeq x (n + 1) else 0 := by
  by_cases h : n < N + 1
  · rw [extendSeq_of_lt _ h, if_pos h]
    rfl
  · rw [extendSeq_of_le _ (by omega), if_neg h]

/-- Coordinates of the powers of the backward truncated shift. -/
theorem truncBackward_pow_apply (k : ℕ) (x : FiniteCarrier N) (m : Fin (N + 1)) :
    ((truncBackward N ^ k) x).ofLp m = extendSeq x (m + k) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp, ih, extendSeq_truncBackward]
      split_ifs with h
      · congr 1
      · rw [extendSeq_of_le _ (by omega)]

theorem norm_truncBackward_apply_le (x : FiniteCarrier N) : ‖truncBackward N x‖ ≤ ‖x‖ := by
  have hsq : ‖truncBackward N x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [norm_sq_eq_sum_range, norm_sq_eq_sum_range]
    have hcongr : ∀ n ∈ Finset.range (N + 1),
        ‖extendSeq (truncBackward N x) n‖ ^ 2 = ‖extendSeq x (n + 1)‖ ^ 2 := by
      intro n hn
      rw [extendSeq_truncBackward, if_pos (Finset.mem_range.mp hn)]
    rw [Finset.sum_congr rfl hcongr]
    have hs := Finset.sum_range_succ' (fun n => ‖extendSeq x n‖ ^ 2) (N + 1)
    have hs2 := Finset.sum_range_succ (fun n => ‖extendSeq x n‖ ^ 2) (N + 1)
    rw [extendSeq_of_le x le_rfl, norm_zero] at hs2
    have h0 : 0 ≤ ‖extendSeq x 0‖ ^ 2 := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

theorem norm_truncBackward_pow_apply_le (k : ℕ) (x : FiniteCarrier N) :
    ‖(truncBackward N ^ k) x‖ ≤ ‖x‖ := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, mul_apply_eq_comp]
      exact (ih _).trans (norm_truncBackward_apply_le x)

theorem norm_truncBackward_pow_le (k : ℕ) : ‖truncBackward N ^ k‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]
    exact norm_truncBackward_pow_apply_le k x

/-- `B_N` is nilpotent: `B_N^{N+1} = 0`. -/
theorem truncBackward_pow_eq_zero : truncBackward N ^ (N + 1) = 0 := by
  ext x m
  rw [truncBackward_pow_apply, extendSeq_of_le _ (by omega)]
  rfl

/-! ## The finite genealogy operator -/

/-- The genealogy formation operator `G_{α,N} = 1 - α B_N` (GR.3). -/
def finiteGenealogy (α : ℝ) (N : ℕ) : FiniteCarrier N →L[ℂ] FiniteCarrier N :=
  1 - (α : ℂ) • truncBackward N

/-- The finite geometric series `∑_{k ≤ N} α^k B_N^k` (GR.5). -/
def finiteGenealogyInverse (α : ℝ) (N : ℕ) : FiniteCarrier N →L[ℂ] FiniteCarrier N :=
  ∑ k ∈ Finset.range (N + 1), ((α : ℂ) ^ k) • truncBackward N ^ k

theorem finiteGenealogy_apply (α : ℝ) (x : FiniteCarrier N) (m : Fin (N + 1)) :
    (finiteGenealogy α N x).ofLp m = x.ofLp m - α * extendSeq x (m + 1) := by
  simp [finiteGenealogy]

theorem finiteGenealogyInverse_eq_geom (α : ℝ) :
    finiteGenealogyInverse α N =
      ∑ k ∈ Finset.range (N + 1), ((α : ℂ) • truncBackward N) ^ k := by
  simp only [finiteGenealogyInverse, smul_pow_operator]

/-- **(GR.5), right inverse.** -/
theorem finiteGenealogy_mul_inverse (α : ℝ) :
    finiteGenealogy α N * finiteGenealogyInverse α N = 1 := by
  rw [finiteGenealogyInverse_eq_geom, finiteGenealogy, mul_neg_geom_sum, smul_pow_operator,
    truncBackward_pow_eq_zero, smul_zero, sub_zero]

/-- **(GR.5), left inverse.** -/
theorem finiteGenealogyInverse_mul (α : ℝ) :
    finiteGenealogyInverse α N * finiteGenealogy α N = 1 := by
  rw [finiteGenealogyInverse_eq_geom, finiteGenealogy, geom_sum_mul_neg, smul_pow_operator,
    truncBackward_pow_eq_zero, smul_zero, sub_zero]

/-- The finite genealogy operator as a unit of the operator algebra. -/
def finiteGenealogyUnit (α : ℝ) (N : ℕ) : (FiniteCarrier N →L[ℂ] FiniteCarrier N)ˣ :=
  ⟨finiteGenealogy α N, finiteGenealogyInverse α N, finiteGenealogy_mul_inverse α,
    finiteGenealogyInverse_mul α⟩

/-- **Theorem 2.1(1).**  `G_{α,N}` is invertible for every `α`, and its inverse is the finite
geometric series (GR.5). -/
theorem finiteGenealogy_isUnit (α : ℝ) : IsUnit (finiteGenealogy α N) :=
  (finiteGenealogyUnit α N).isUnit

theorem ring_inverse_finiteGenealogy (α : ℝ) :
    Ring.inverse (finiteGenealogy α N) = finiteGenealogyInverse α N := by
  have h := Ring.inverse_unit (finiteGenealogyUnit α N)
  exact h

/-! ## The finite semantic reader -/

/-- The finite semantic reader `b_{α,N}(x) = ∑ α^n x_n` (GR.4), as a linear map. -/
def finiteSemanticReaderₗ (α : ℝ) (N : ℕ) : FiniteCarrier N →ₗ[ℂ] ℂ where
  toFun x := ∑ m : Fin (N + 1), (α : ℂ) ^ (m : ℕ) * x.ofLp m
  map_add' x y := by
    simp only [PiLp.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

/-- The finite semantic reader `b_{α,N}` (GR.4). -/
def finiteSemanticReader (α : ℝ) (N : ℕ) : FiniteCarrier N →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (finiteSemanticReaderₗ α N)

theorem finiteSemanticReader_apply (α : ℝ) (x : FiniteCarrier N) :
    finiteSemanticReader α N x =
      ∑ n ∈ Finset.range (N + 1), (α : ℂ) ^ n * extendSeq x n := by
  change ∑ m : Fin (N + 1), (α : ℂ) ^ (m : ℕ) * x.ofLp m = _
  rw [← sum_fin_eq_sum_range (fun n => (α : ℂ) ^ n * extendSeq x n)]
  simp

/-- The old semantic carrier coordinate `π_0`. -/
def carrierCoordinate (N : ℕ) : FiniteCarrier N →L[ℂ] ℂ :=
  EuclideanSpace.proj (0 : Fin (N + 1))

@[simp] theorem carrierCoordinate_apply (x : FiniteCarrier N) :
    carrierCoordinate N x = x.ofLp 0 := rfl

/-- **Theorem 2.1(2), the exact conservation identity (GR.6).**  `b_{α,N} G_{α,N} = π_0`. -/
theorem finiteSemanticReader_comp_finiteGenealogy (α : ℝ) :
    (finiteSemanticReader α N).comp (finiteGenealogy α N) = carrierCoordinate N := by
  ext z
  rw [ContinuousLinearMap.comp_apply, finiteSemanticReader_apply]
  have hterm : ∀ n ∈ Finset.range (N + 1),
      (α : ℂ) ^ n * extendSeq (finiteGenealogy α N z) n =
        (α : ℂ) ^ n * extendSeq z n - (α : ℂ) ^ (n + 1) * extendSeq z (n + 1) := by
    intro n hn
    have hn' := Finset.mem_range.mp hn
    rw [extendSeq_of_lt _ hn', finiteGenealogy_apply, extendSeq_of_lt z hn']
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_range_sub' (fun n => (α : ℂ) ^ n * extendSeq z n),
    extendSeq_of_le z le_rfl, carrierCoordinate_apply, extendSeq_of_lt z (Nat.succ_pos N)]
  simp

/-! ## Theorem 2.1(3): finite repair histories are changes of presentation -/

theorem extendSeq_single (n : Fin (N + 1)) (k : ℕ) :
    extendSeq (EuclideanSpace.single n (1 : ℂ)) k = if k = n then 1 else 0 := by
  by_cases h : k < N + 1
  · rw [extendSeq_of_lt _ h]
    simp [Fin.ext_iff]
  · rw [extendSeq_of_le _ (by omega), if_neg (by omega)]

/-- The zeroth column of `G_{α,N}` is the old semantic carrier `e_0`. -/
theorem finiteGenealogy_single_zero (α : ℝ) :
    finiteGenealogy α N (EuclideanSpace.single 0 1) = EuclideanSpace.single 0 1 := by
  ext m
  rw [finiteGenealogy_apply, extendSeq_single]
  simp

/-- For `n ≥ 1` the `n`-th column of `G_{α,N}` is the repair syzygy `e_n - α e_{n-1}`. -/
theorem finiteGenealogy_single_succ (α : ℝ) (n : Fin N) :
    finiteGenealogy α N (EuclideanSpace.single n.succ 1) =
      EuclideanSpace.single n.succ 1 - (α : ℂ) • EuclideanSpace.single n.castSucc 1 := by
  ext m
  rw [finiteGenealogy_apply, extendSeq_single]
  simp only [Fin.val_succ, Nat.add_right_cancel_iff, PiLp.sub_apply, PiLp.smul_apply,
    smul_eq_mul]
  simp [Fin.ext_iff]

/-- **Theorem 2.1(3).**  Every repair syzygy is semantic-null and the old carrier reads one:
`b_{α,N}(G_{α,N} e_n) = δ_{n0}`. -/
theorem finiteSemanticReader_finiteGenealogy_single (α : ℝ) (n : Fin (N + 1)) :
    finiteSemanticReader α N (finiteGenealogy α N (EuclideanSpace.single n 1)) =
      if n = 0 then 1 else 0 := by
  have h := congrArg (fun L : FiniteCarrier N →L[ℂ] ℂ => L (EuclideanSpace.single n 1))
    (finiteSemanticReader_comp_finiteGenealogy (N := N) α)
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h, carrierCoordinate_apply]
  by_cases hn : n = 0
  · subst hn
    simp
  · simp [hn, Ne.symm hn]

theorem finiteGenealogy_apply_inverse_apply (α : ℝ) (x : FiniteCarrier N) :
    finiteGenealogy α N (finiteGenealogyInverse α N x) = x := by
  have h := congrArg (fun L : FiniteCarrier N →L[ℂ] FiniteCarrier N => L x)
    (finiteGenealogy_mul_inverse (N := N) α)
  simpa [mul_apply_eq_comp] using h

theorem finiteGenealogyInverse_apply_apply (α : ℝ) (x : FiniteCarrier N) :
    finiteGenealogyInverse α N (finiteGenealogy α N x) = x := by
  have h := congrArg (fun L : FiniteCarrier N →L[ℂ] FiniteCarrier N => L x)
    (finiteGenealogyInverse_mul (N := N) α)
  simpa [mul_apply_eq_comp] using h

/-- **Theorem 2.1(3), exact carrier recovery.**  The semantic reading of any vector is the old
carrier coordinate of its repair-history presentation `G_{α,N}^{-1} x`. -/
theorem finiteSemanticReader_eq_carrierCoordinate_inverse (α : ℝ) (x : FiniteCarrier N) :
    finiteSemanticReader α N x = carrierCoordinate N (finiteGenealogyInverse α N x) := by
  have h := congrArg (fun L : FiniteCarrier N →L[ℂ] ℂ => L (finiteGenealogyInverse α N x))
    (finiteSemanticReader_comp_finiteGenealogy (N := N) α)
  simp only [ContinuousLinearMap.comp_apply, finiteGenealogy_apply_inverse_apply] at h
  exact h

/-- **Theorem 2.1(3), change of presentation.**  `G_{α,N}` is a bijection of `H_N`. -/
theorem finiteGenealogy_bijective (α : ℝ) : Function.Bijective (finiteGenealogy α N) := by
  constructor
  · intro x y hxy
    have h := congrArg (finiteGenealogyInverse α N) hxy
    rwa [finiteGenealogyInverse_apply_apply, finiteGenealogyInverse_apply_apply] at h
  · intro y
    exact ⟨finiteGenealogyInverse α N y, finiteGenealogy_apply_inverse_apply α y⟩

/-! ## Theorem 2.1(4): the inverse bounds -/

/-- **(GR.8).**  `G_{α,N}^{-1} e_N = e_N + α e_{N-1} + ⋯ + α^N e_0`, coordinatewise. -/
theorem finiteGenealogyInverse_single_last_apply (α : ℝ) (m : Fin (N + 1)) :
    (finiteGenealogyInverse α N (EuclideanSpace.single (Fin.last N) 1)).ofLp m =
      (α : ℂ) ^ (N - m) := by
  have hm : (m : ℕ) ≤ N := Nat.lt_succ_iff.mp m.isLt
  simp only [finiteGenealogyInverse, FunLike.coe_sum, Finset.sum_apply,
    FunLike.coe_smul, Pi.smul_apply, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, truncBackward_pow_apply, extendSeq_single, Fin.val_last,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (N - m)]
  · rw [if_pos (by omega)]
  · intro k _ hk
    rw [if_neg (by omega)]
  · intro hk
    exact absurd (Finset.mem_range.mpr (by omega)) hk

theorem norm_single_last : ‖(EuclideanSpace.single (Fin.last N) (1 : ℂ) : FiniteCarrier N)‖ = 1 := by
  simp

/-- **Theorem 2.1(4), subcritical bound.**  For `0 ≤ α < 1`, `‖G_{α,N}^{-1}‖ ≤ (1-α)^{-1}`. -/
theorem norm_finiteGenealogyInverse_le {α : ℝ} (h0 : 0 ≤ α) (h1 : α < 1) :
    ‖finiteGenealogyInverse α N‖ ≤ (1 - α)⁻¹ := by
  calc ‖finiteGenealogyInverse α N‖
      ≤ ∑ k ∈ Finset.range (N + 1), ‖((α : ℂ) ^ k) • truncBackward N ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), α ^ k := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul, norm_pow, Complex.norm_real, Real.norm_of_nonneg h0]
        exact mul_le_of_le_one_right (pow_nonneg h0 k) (norm_truncBackward_pow_le k)
    _ ≤ ∑' k : ℕ, α ^ k :=
        (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ fun i _ => pow_nonneg h0 i
    _ = (1 - α)⁻¹ := tsum_geometric_of_lt_one h0 h1

/-- The critical terminal vector `G_{1,N}^{-1} e_N` has norm `√(N+1)`. -/
theorem norm_finiteGenealogyInverse_one_single_last :
    ‖finiteGenealogyInverse 1 N (EuclideanSpace.single (Fin.last N) 1)‖ = Real.sqrt (N + 1) := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_eq_sum_range]
  congr 1
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ‖extendSeq (finiteGenealogyInverse 1 N (EuclideanSpace.single (Fin.last N) 1)) n‖ ^ 2
        = 1 := by
    intro n hn
    rw [extendSeq_of_lt _ (Finset.mem_range.mp hn), finiteGenealogyInverse_single_last_apply]
    simp
  rw [Finset.sum_congr rfl hterm]
  simp

/-- **Theorem 2.1(4), critical bound.**  `‖G_{1,N}^{-1}‖ ≥ √(N+1)`. -/
theorem sqrt_le_norm_finiteGenealogyInverse_one :
    Real.sqrt (N + 1) ≤ ‖finiteGenealogyInverse 1 N‖ := by
  have h := (finiteGenealogyInverse 1 N).le_opNorm (EuclideanSpace.single (Fin.last N) 1)
  rwa [norm_finiteGenealogyInverse_one_single_last, norm_single_last, mul_one] at h

/-- **Theorem 2.1(4), supercritical bound.**  `‖G_{α,N}^{-1}‖ ≥ α^N` (proved for every `α ≥ 0`,
in particular for `α > 1`). -/
theorem pow_le_norm_finiteGenealogyInverse {α : ℝ} (h0 : 0 ≤ α) :
    α ^ N ≤ ‖finiteGenealogyInverse α N‖ := by
  have hcoord := PiLp.norm_apply_le
    (finiteGenealogyInverse α N (EuclideanSpace.single (Fin.last N) 1)) 0
  rw [finiteGenealogyInverse_single_last_apply, Fin.val_zero, Nat.sub_zero, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg h0] at hcoord
  have h := (finiteGenealogyInverse α N).le_opNorm (EuclideanSpace.single (Fin.last N) 1)
  rw [norm_single_last, mul_one] at h
  exact hcoord.trans h

/-! ## The finite reciprocal boundary law (GR.24) -/

/-- The forward truncated shift `S_N e_n = e_{n+1}` (`n < N`), `S_N e_N = 0`, as a linear map. -/
def truncForwardₗ (N : ℕ) : FiniteCarrier N →ₗ[ℂ] FiniteCarrier N where
  toFun x := WithLp.toLp 2 (fun m : Fin (N + 1) => if m = 0 then 0 else extendSeq x (m - 1))
  map_add' x y := by
    ext m
    by_cases h : m = 0 <;> simp [h]
  map_smul' c x := by
    ext m
    by_cases h : m = 0 <;> simp [h]

/-- The forward truncated shift `S_N`. -/
def truncForward (N : ℕ) : FiniteCarrier N →L[ℂ] FiniteCarrier N :=
  LinearMap.toContinuousLinearMap (truncForwardₗ N)

@[simp] theorem truncForward_apply (x : FiniteCarrier N) (m : Fin (N + 1)) :
    (truncForward N x).ofLp m = if m = 0 then 0 else extendSeq x (m - 1) := rfl

/-- The finite forward shift is the adjoint of the backward truncated shift: `B_N^* = S_N`. -/
theorem adjoint_truncBackward : ContinuousLinearMap.adjoint (truncBackward N) = truncForward N := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, truncForward_apply, truncBackward_apply]
  have hL : ∑ m : Fin (N + 1), y.ofLp m *
        (starRingEnd ℂ) (if m = 0 then 0 else extendSeq x (m - 1)) =
      ∑ n ∈ Finset.range (N + 1), extendSeq y n *
        (starRingEnd ℂ) (if n = 0 then 0 else extendSeq x (n - 1)) := by
    rw [← sum_fin_eq_sum_range]
    simp
  have hR : ∑ m : Fin (N + 1), extendSeq y (m + 1) * (starRingEnd ℂ) (x.ofLp m) =
      ∑ n ∈ Finset.range (N + 1), extendSeq y (n + 1) * (starRingEnd ℂ) (extendSeq x n) := by
    rw [← sum_fin_eq_sum_range]
    simp
  rw [hL, hR, Finset.sum_range_succ', Finset.sum_range_succ, extendSeq_of_le y le_rfl]
  simp

/-- The terminal projection `P_N` onto `ℂ e_N`, as a linear map. -/
def terminalProjectionₗ (N : ℕ) : FiniteCarrier N →ₗ[ℂ] FiniteCarrier N where
  toFun x := WithLp.toLp 2 (fun m : Fin (N + 1) => if (m : ℕ) = N then x.ofLp m else 0)
  map_add' x y := by
    ext m
    by_cases h : (m : ℕ) = N <;> simp [h]
  map_smul' c x := by
    ext m
    by_cases h : (m : ℕ) = N <;> simp [h]

/-- The terminal projection `P_N` onto the terminal basis vector `e_N`. -/
def terminalProjection (N : ℕ) : FiniteCarrier N →L[ℂ] FiniteCarrier N :=
  LinearMap.toContinuousLinearMap (terminalProjectionₗ N)

@[simp] theorem terminalProjection_apply (x : FiniteCarrier N) (m : Fin (N + 1)) :
    (terminalProjection N x).ofLp m = if (m : ℕ) = N then x.ofLp m else 0 := rfl

/-- `P_N x = x_N e_N`: the orthogonal projection onto the terminal basis line. -/
theorem terminalProjection_eq (x : FiniteCarrier N) :
    terminalProjection N x = x.ofLp (Fin.last N) • EuclideanSpace.single (Fin.last N) 1 := by
  ext m
  by_cases h : (m : ℕ) = N
  · have hm : m = Fin.last N := Fin.ext h
    subst hm
    simp
  · have hm : m ≠ Fin.last N := fun hm => h (by simp [hm])
    simp [h, hm]

theorem terminalProjection_idempotent :
    terminalProjection N * terminalProjection N = terminalProjection N := by
  ext x m
  rw [mul_apply_eq_comp]
  by_cases h : (m : ℕ) = N <;> simp [h]

theorem adjoint_terminalProjection :
    ContinuousLinearMap.adjoint (terminalProjection N) = terminalProjection N := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases h : (m : ℕ) = N <;> simp [h]

/-- The terminal projection has norm one. -/
theorem norm_terminalProjection : ‖terminalProjection N‖ = 1 := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    rw [terminalProjection_eq, norm_smul, norm_single_last, mul_one, one_mul]
    exact PiLp.norm_apply_le x _
  · have h := (terminalProjection N).le_opNorm (EuclideanSpace.single (Fin.last N) 1)
    rw [terminalProjection_eq, norm_single_last, mul_one] at h
    simpa using h

/-- `B_N S_N = 1 - P_N`. -/
theorem truncBackward_mul_truncForward :
    truncBackward N * truncForward N = 1 - terminalProjection N := by
  ext x m
  rw [mul_apply_eq_comp, truncBackward_apply]
  simp only [sub_apply, one_apply_eq_self, PiLp.sub_apply, terminalProjection_apply]
  by_cases h : (m : ℕ) = N
  · rw [extendSeq_of_le _ (by omega), if_pos h, sub_self]
  · have hlt : (m : ℕ) + 1 < N + 1 := by omega
    have hm0 : (⟨(m : ℕ) + 1, hlt⟩ : Fin (N + 1)) ≠ 0 := by
      intro h0
      have := congrArg Fin.val h0
      simp at this
    rw [extendSeq_of_lt _ hlt, truncForward_apply, if_neg hm0, if_neg h, sub_zero]
    simp

theorem adjoint_finiteGenealogy (α : ℝ) :
    ContinuousLinearMap.adjoint (finiteGenealogy α N) = 1 - (α : ℂ) • truncForward N := by
  rw [finiteGenealogy, ← ContinuousLinearMap.star_eq_adjoint, star_sub, star_one, star_smul,
    ContinuousLinearMap.star_eq_adjoint, adjoint_truncBackward,
    show star (α : ℂ) = (α : ℂ) from Complex.conj_ofReal α]

/-- **(GR.24), the finite reciprocal boundary law.**  For `α ≠ 0`,
`G_{α,N} = -α B_N G_{1/α,N}^* + P_N`. -/
theorem finiteGenealogy_reciprocal {α : ℝ} (hα : α ≠ 0) :
    finiteGenealogy α N =
      -(α : ℂ) • (truncBackward N * ContinuousLinearMap.adjoint (finiteGenealogy α⁻¹ N)) +
        terminalProjection N := by
  have hα' : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  rw [adjoint_finiteGenealogy, mul_sub, mul_one, mul_smul_operator, truncBackward_mul_truncForward,
    finiteGenealogy]
  ext x m
  simp only [add_apply, sub_apply, one_apply_eq_self, smul_apply,
    PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_inv]
  field_simp
  ring
