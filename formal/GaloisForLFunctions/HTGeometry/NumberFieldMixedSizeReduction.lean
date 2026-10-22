import GaloisForLFunctions.HTGeometry.NumberFieldIntegerMatrixReduction
import GaloisForLFunctions.HTGeometry.OrderSizeReduction

/-!
# Size reduction of unipotent matrices over the mixed embedding space

For a number field `K`, matrices over `𝓞 K` act on matrices over the mixed space
`ℝ^{r₁} × ℂ^{r₂}` through the mixed embedding. A unipotent upper triangular mixed matrix `V` is
size-reduced diagonal by diagonal: at superdiagonal offset `k + 1` one right-multiplies by an
integral shear whose entries are nearest algebraic integers, which leaves the lower superdiagonals
untouched. Since `𝓞 K` has finite covering radius in the mixed space, this yields a uniform bound.

## Main results

- `IsMixedUnipotentUpper`: unipotent upper triangular matrices over the mixed space, closed under
  multiplication (`IsMixedUnipotentUpper.mul`).
- `MixedSizeReduced`: all entries on superdiagonals of offset `1, …, k` have norm at most `C`.
- `exists_numberFieldMixedOrderSweep`: one shear step extends size reduction from offset `k` to
  `k + 1`, assuming every mixed point lies within `C` of an embedded algebraic integer.
- `exists_numberFieldMixed_unipotentUpperReduction`: there is `C ≥ 0` depending only on `K` such
  that every mixed unipotent upper `V` admits an integral `N` with `det N = 1`, unipotent upper
  mixed embedding, and every strictly upper entry of `V N` of norm at most `C`.

## Hypotheses

The final theorem is unconditional. The sweep lemma takes the covering property of `𝓞 K` with
radius `C` as an explicit hypothesis; the final theorem discharges it with the proved finite
covering radius of the ring of integers.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Entrywise mixed embedding `𝓞 K → ℝ^{r₁} × ℂ^{r₂}` of a square matrix over the ring of
integers. -/
def numberFieldMixedOrderMatrix
    (M : Matrix (Fin n) (Fin n) (𝓞 K)) :
    Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) :=
  ((mixedEmbedding K).comp (algebraMap (𝓞 K) K)).mapMatrix M

omit [NumberField K] in
@[simp]
theorem numberFieldMixedOrderMatrix_one :
    numberFieldMixedOrderMatrix (K := K)
      (1 : Matrix (Fin n) (Fin n) (𝓞 K)) = 1 := by
  exact map_one _

omit [NumberField K] in
@[simp]
theorem numberFieldMixedOrderMatrix_mul
    (M N : Matrix (Fin n) (Fin n) (𝓞 K)) :
    numberFieldMixedOrderMatrix (K := K) (M * N) =
      numberFieldMixedOrderMatrix M * numberFieldMixedOrderMatrix N := by
  exact map_mul _ _ _

omit [NumberField K] in
theorem numberFieldMixedOrderMatrix_superShear
    (k : ℕ) (e : Fin n → 𝓞 K) :
    numberFieldMixedOrderMatrix (K := K) (superShear k e) =
      superShear k (fun i => mixedEmbedding K (e i : K)) := by
  classical
  ext i j <;> by_cases h : (j : ℕ) = (i : ℕ) + (k + 1) <;>
    simp [numberFieldMixedOrderMatrix, superShear_apply, h]

/-- A matrix over the mixed space is unipotent upper triangular: zero below the diagonal and `1` on
the diagonal. -/
structure IsMixedUnipotentUpper
    (V : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) : Prop where
  upper : ∀ i j, j < i → V i j = 0
  unit : ∀ i, V i i = 1

omit [NumberField K] in
/-- Products of mixed unipotent upper triangular matrices are unipotent upper triangular. -/
theorem IsMixedUnipotentUpper.mul
    {V W : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)}
    (hV : IsMixedUnipotentUpper V) (hW : IsMixedUnipotentUpper W) :
    IsMixedUnipotentUpper (V * W) := by
  classical
  constructor
  · intro i j hji
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k < i
    · rw [hV.upper i k hki, zero_mul]
    · have hjk : j < k := lt_of_lt_of_le hji (not_lt.1 hki)
      rw [hW.upper k j hjk, mul_zero]
  · intro i
    rw [Matrix.mul_apply]
    refine (Finset.sum_eq_single i (fun k _ hki => ?_)
      (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
    · rcases lt_or_gt_of_ne hki with hlt | hgt
      · rw [hV.upper i k hlt, zero_mul]
      · rw [hW.upper k i hgt, mul_zero]
    · rw [hV.unit i, hW.unit i, one_mul]

omit [NumberField K] in
theorem isMixedUnipotentUpper_superShear
    (k : ℕ) (e : Fin n → mixedEmbedding.mixedSpace K) :
    IsMixedUnipotentUpper (superShear k e) :=
  ⟨superShear_upper k e, superShear_diag k e⟩

/-- `V` is size-reduced up to offset `k` with bound `C`: every entry `V i j` with
`i < j ≤ i + k` has norm at most `C`. -/
def MixedSizeReduced (C : ℝ) (k : ℕ)
    (V : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) : Prop :=
  ∀ i j : Fin n, i < j → (j : ℕ) ≤ (i : ℕ) + k → ‖V i j‖ ≤ C

theorem mixedSizeReduced_zero (C : ℝ)
    (V : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)) :
    MixedSizeReduced C 0 V := by
  intro i j hij hle
  exact absurd (Fin.lt_def.1 hij) (not_lt_of_ge (by simpa only [Nat.add_zero] using hle))

omit [NumberField K] in
/-- For unipotent upper `V`, right multiplication by the shear on superdiagonal `k + 1` fixes the
entries on offsets `1, …, k` and adds `eᵢ` to the entry `(i, i + k + 1)`. -/
theorem mixed_mul_superShear_apply
    {V : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)}
    (hV : IsMixedUnipotentUpper V) (k : ℕ)
    (e : Fin n → mixedEmbedding.mixedSpace K) :
    (∀ i j : Fin n, i < j → (j : ℕ) ≤ (i : ℕ) + k →
        (V * superShear k e) i j = V i j) ∧
      (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + (k + 1) →
        (V * superShear k e) i j = V i j + e i) := by
  classical
  set E : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) :=
    Matrix.of fun i j => if (j : ℕ) = (i : ℕ) + (k + 1) then e i else 0 with hE
  have hEzero : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) + (k + 1) → E i j = 0 := by
    intro i j hne
    rw [hE]
    simp [hne]
  have hEval : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + (k + 1) → E i j = e i := by
    intro i j hij
    rw [hE]
    simp [hij]
  have hprod : ∀ i j : Fin n,
      (V * superShear k e) i j = V i j + (V * E) i j := by
    intro i j
    rw [superShear, ← hE, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  constructor
  · intro i j hij hle
    have hzero : (V * E) i j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun m _ => ?_
      by_cases hm : (j : ℕ) = (m : ℕ) + (k + 1)
      · have hmi : m < i := Fin.lt_def.2 (by
          have := Fin.lt_def.1 hij
          omega)
        rw [hV.1 i m hmi, zero_mul]
      · rw [hEzero m j hm, mul_zero]
    rw [hprod, hzero, add_zero]
  · intro i j hij
    have hnew : (V * E) i j = e i := by
      rw [Matrix.mul_apply]
      refine (Finset.sum_eq_single i (fun m _ hm => ?_)
        (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
      · by_cases hmj : (j : ℕ) = (m : ℕ) + (k + 1)
        · exact absurd (Fin.ext (by omega) : m = i) hm
        · rw [hEzero m j hmj, mul_zero]
      · rw [hEval i j hij, hV.2 i, one_mul]
    rw [hprod, hnew]

/-- One reduction sweep: assuming `hC`, that every mixed point is within `C` of an embedded
algebraic integer, a matrix size-reduced up to offset `k` becomes size-reduced up to `k + 1` after
an integral shear on superdiagonal `k + 1`. -/
theorem exists_numberFieldMixedOrderSweep
    {C : ℝ}
    (hC : ∀ x : mixedEmbedding.mixedSpace K,
      ∃ a : 𝓞 K, ‖x - mixedEmbedding K (a : K)‖ ≤ C)
    {V : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)}
    (hV : IsMixedUnipotentUpper V) (k : ℕ)
    (hk : MixedSizeReduced C k V) :
    ∃ e : Fin n → 𝓞 K,
      MixedSizeReduced C (k + 1)
        (V * superShear k (fun i => mixedEmbedding K (e i : K))) := by
  classical
  set e : Fin n → 𝓞 K := fun i =>
    if h : (i : ℕ) + (k + 1) < n then
      Classical.choose (hC (-(V i ⟨(i : ℕ) + (k + 1), h⟩)))
    else 0 with he
  refine ⟨e, ?_⟩
  intro i j hij hle
  obtain ⟨hlow, hnew⟩ :=
    mixed_mul_superShear_apply hV k (fun i => mixedEmbedding K (e i : K))
  rcases lt_or_eq_of_le hle with hlt | heq
  · rw [hlow i j hij (by omega)]
    exact hk i j hij (by omega)
  · rw [hnew i j heq]
    have hlt' : (i : ℕ) + (k + 1) < n := by
      have := j.isLt
      omega
    have hjeq : j = (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin n) := Fin.ext (by omega)
    have hee : e i = Classical.choose
        (hC (-(V i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin n)))) := by
      rw [he]
      simp only [dif_pos hlt']
    have hespec := Classical.choose_spec
      (hC (-(V i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin n))))
    rw [hjeq, hee]
    have hEq :
        V i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin n) +
            mixedEmbedding K
              ((Classical.choose
                (hC (-(V i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin n)))) : 𝓞 K) : K) =
          -(-(V i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin n)) -
            mixedEmbedding K
              ((Classical.choose
                (hC (-(V i (⟨(i : ℕ) + (k + 1), hlt'⟩ : Fin n)))) : 𝓞 K) : K)) := by
      ring
    rw [hEq, norm_neg]
    exact hespec

/-- Uniform mixed size reduction: a constant `C ≥ 0` depending only on `K` such that every mixed
unipotent upper `V` admits `N` over `𝓞 K` with `det N = 1`, unipotent upper mixed embedding, and all
strictly upper entries of `V N` of norm at most `C`. -/
theorem exists_numberFieldMixed_unipotentUpperReduction
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (n : ℕ) (V : Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K)),
        IsMixedUnipotentUpper V →
        ∃ N : Matrix (Fin n) (Fin n) (𝓞 K),
          N.det = 1 ∧ IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N) ∧
          ∀ i j : Fin n, i < j →
            ‖(V * numberFieldMixedOrderMatrix N) i j‖ ≤ C := by
  obtain ⟨C, hC, hcover⟩ := exists_numberFieldInteger_coveringRadius K
  refine ⟨C, hC, ?_⟩
  intro n V hV
  have hstep : ∀ k : ℕ,
      ∃ N : Matrix (Fin n) (Fin n) (𝓞 K),
        N.det = 1 ∧ IsMixedUnipotentUpper (numberFieldMixedOrderMatrix N) ∧
        MixedSizeReduced C k (V * numberFieldMixedOrderMatrix N) := by
    intro k
    induction k with
    | zero =>
        refine ⟨1, Matrix.det_one, ?_, ?_⟩
        · rw [numberFieldMixedOrderMatrix_one]
          exact ⟨fun i j hji => Matrix.one_apply_ne
            (fun h => absurd (h ▸ hji) (lt_irrefl _)), fun i => Matrix.one_apply_eq i⟩
        · rw [numberFieldMixedOrderMatrix_one, Matrix.mul_one]
          exact mixedSizeReduced_zero C V
    | succ k ih =>
        obtain ⟨N, hdet, hN, hred⟩ := ih
        obtain ⟨e, hsweep⟩ := exists_numberFieldMixedOrderSweep hcover
          (hV.mul hN) k hred
        refine ⟨N * superShear k e, ?_, ?_, ?_⟩
        · rw [Matrix.det_mul, hdet, det_superShear, one_mul]
        · rw [numberFieldMixedOrderMatrix_mul,
            numberFieldMixedOrderMatrix_superShear]
          exact hN.mul (isMixedUnipotentUpper_superShear k _)
        · rw [numberFieldMixedOrderMatrix_mul,
            numberFieldMixedOrderMatrix_superShear, ← Matrix.mul_assoc]
          exact hsweep
  obtain ⟨N, hdet, hN, hred⟩ := hstep n
  refine ⟨N, hdet, hN, ?_⟩
  intro i j hij
  exact hred i j hij (by omega)

end

end GaloisForLFunctions.HTGeometry
