import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits

/-!
# Integers along paths of forms

The third way a statement can hold at the edge is an integer that cannot jump. For Hermitian
matrices the negative index `n₋` and the positive index `n₊` are lower semicontinuous, and
`n₊ + n₋ + n₀` is the dimension, so near a matrix with nullity `n₀` the negative index can rise by
at most `n₀` and cannot fall. At a nondegenerate matrix it is locally constant.

* **Semicontinuity** (`eventually_le_hermPosIndex`, `eventually_hermNegIndex_le_add_nullIndex`).
* **Local constancy** (`eventually_hermNegIndex_eq_of_nullIndex_eq_zero`).
* **Path invariance** (`hermNegIndex_eq_of_isPreconnected`): along a continuous family of
  nondegenerate Hermitian matrices on a preconnected set the negative index is constant. It changes
  only at a crossing, a point of nonzero nullity.
* **Precision below one half** (`eq_of_abs_sub_lt_half_of_isPreconnected`): a natural-number
  reading that stays within `1/2` of a continuous real function on a preconnected set is constant.
* **Deformation to a model** (`exists_crossingFree_path_to_one_iff`): a crossing-free path of
  Hermitian matrices from `A` to the identity exists iff `A` has no negative and no null direction.
  An index computed by deformation to a positive model is the sign itself: the structural reason
  that keeps the path nondegenerate is positivity of its endpoint.
-/

open Matrix Filter Topology
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace GaloisForLFunctions.EdgeHodgeTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Semicontinuity and local constancy -/

/-- **Lower semicontinuity of the positive index.** -/
theorem eventually_le_hermPosIndex {β : Type*} {l : Filter β} {H : β → Matrix ι ι ℂ}
    {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    (hH : ∀ a b, Tendsto (fun n => H n a b) l (𝓝 (H₀ a b))) :
    ∀ᶠ n in l, hermPosIndex H₀ ≤ hermPosIndex (H n) := by
  have h := HeckeKreinToeplitz.eventually_le_hermNegIndex (H := fun n => -H n) hH₀.neg
    fun a b => by simpa only [Matrix.neg_apply] using (hH a b).neg
  simpa only [hermNegIndex, neg_neg] using h

/-- **Upper semicontinuity with nullity.** Near `H₀` the negative index exceeds that of `H₀` by at
most the nullity of `H₀`. -/
theorem eventually_hermNegIndex_le_add_nullIndex {β : Type*} {l : Filter β}
    {H : β → Matrix ι ι ℂ} {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    (hherm : ∀ᶠ n in l, (H n).IsHermitian)
    (hH : ∀ a b, Tendsto (fun n => H n a b) l (𝓝 (H₀ a b))) :
    ∀ᶠ n in l, hermNegIndex (H n) ≤ hermNegIndex H₀ + hermNullIndex H₀ := by
  filter_upwards [eventually_le_hermPosIndex hH₀ hH, hherm] with n hn hn'
  have h₀ := posIndex_add_negIndex_add_nullIndex hH₀
  have h₁ := posIndex_add_negIndex_add_nullIndex hn'
  omega

/-- **Local constancy at a nondegenerate point.** -/
theorem eventually_hermNegIndex_eq_of_nullIndex_eq_zero {β : Type*} {l : Filter β}
    {H : β → Matrix ι ι ℂ} {H₀ : Matrix ι ι ℂ} (hH₀ : H₀.IsHermitian)
    (hherm : ∀ᶠ n in l, (H n).IsHermitian)
    (hH : ∀ a b, Tendsto (fun n => H n a b) l (𝓝 (H₀ a b))) (h0 : hermNullIndex H₀ = 0) :
    ∀ᶠ n in l, hermNegIndex (H n) = hermNegIndex H₀ := by
  filter_upwards [HeckeKreinToeplitz.eventually_le_hermNegIndex hH₀ hH,
    eventually_hermNegIndex_le_add_nullIndex hH₀ hherm hH] with n h₁ h₂
  omega

/-! ### Path invariance -/

/-- A natural-number function that is eventually constant within `S` near every point of a
preconnected set `S` is constant on `S`. -/
theorem eq_of_locallyConstantOn {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {k : X → ℕ} (hk : ∀ z ∈ S, ∀ᶠ w in 𝓝[S] z, k w = k z)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) : k x = k y :=
  hS.constant (fun z hz => by rw [ContinuousWithinAt, nhds_discrete, tendsto_pure]; exact hk z hz)
    hx hy

/-- **Path invariance of the index.** Along a continuous family of nondegenerate Hermitian matrices
on a preconnected set the negative index is constant. -/
theorem hermNegIndex_eq_of_isPreconnected {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {H : X → Matrix ι ι ℂ} (hc : ContinuousOn H S)
    (hherm : ∀ x ∈ S, (H x).IsHermitian) (hnd : ∀ x ∈ S, hermNullIndex (H x) = 0)
    {x y : X} (hx : x ∈ S) (hy : y ∈ S) : hermNegIndex (H x) = hermNegIndex (H y) := by
  refine eq_of_locallyConstantOn hS (k := fun z => hermNegIndex (H z)) (fun z hz => ?_) hx hy
  have hent : ∀ a b, Tendsto (fun w => H w a b) (𝓝[S] z) (𝓝 (H z a b)) := fun a b =>
    ((continuous_id.matrix_elem a b).continuousAt.tendsto).comp (hc z hz)
  exact eventually_hermNegIndex_eq_of_nullIndex_eq_zero (hherm z hz)
    (eventually_mem_nhdsWithin.mono fun w hw => hherm w hw) hent (hnd z hz)

/-- **Precision below one half suffices.** A natural-number reading within `1/2` of a continuous
real function on a preconnected set is constant. -/
theorem eq_of_abs_sub_lt_half_of_isPreconnected {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsPreconnected S) {k : X → ℕ} {r : X → ℝ} (hr : ContinuousOn r S)
    (hk : ∀ x ∈ S, |(k x : ℝ) - r x| < 1 / 2) {x y : X} (hx : x ∈ S) (hy : y ∈ S) :
    k x = k y := by
  refine eq_of_locallyConstantOn hS (fun z hz => ?_) hx hy
  have hδ : 0 < 1 / 2 - |(k z : ℝ) - r z| := by linarith [hk z hz]
  filter_upwards [Metric.tendsto_nhds.mp (hr z hz) _ hδ, self_mem_nhdsWithin] with w hw hwS
  rw [Real.dist_eq] at hw
  have h₁ := abs_lt.mp (hk w hwS)
  have h₂ := abs_lt.mp hw
  have h₃ := neg_abs_le ((k z : ℝ) - r z)
  have h₄ := le_abs_self ((k z : ℝ) - r z)
  have e₁ : k w < k z + 1 := by exact_mod_cast (show (k w : ℝ) < k z + 1 by linarith)
  have e₂ : k z < k w + 1 := by exact_mod_cast (show (k z : ℝ) < k w + 1 by linarith)
  omega

/-! ### Deformation to a model -/

/-- The straight path `t ↦ (1 − t) A + t·1`. -/
def straightPath (A : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  ((1 - t : ℝ) : ℂ) • A + ((t : ℝ) : ℂ) • 1

theorem hermNegIndex_one : hermNegIndex (1 : Matrix ι ι ℂ) = 0 := by
  have h : (1 : Matrix ι ι ℂ) = diagonal fun _ : ι => ((1 : ℝ) : ℂ) := by simp
  rw [h, negIndex_diagonal]
  simp

theorem straightPath_isHermitian {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    (straightPath A t).IsHermitian := by
  unfold straightPath Matrix.IsHermitian
  rw [conjTranspose_add, conjTranspose_smul, conjTranspose_smul, hA.eq, conjTranspose_one]
  simp [Complex.conj_ofReal]

/-- In the eigenbasis of `A` the straight path is diagonal, with entries `(1 − t)λᵢ + t`. -/
theorem conjTranspose_mul_straightPath_mul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (t : ℝ) :
    (hA.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * straightPath A t *
        (hA.eigenvectorUnitary : Matrix ι ι ℂ) =
      diagonal fun i => (((1 - t) * hA.eigenvalues i + t : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := hA.eigenvectorUnitary
  have hU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  have hD := conjTranspose_mul_mul_eigenvectorUnitary hA
  unfold straightPath
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, hD, hU]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h, Matrix.one_apply_ne h]

/-- **Deformation to a model.** A crossing-free path of Hermitian matrices from `A` to the identity
exists iff `A` has no negative and no null direction. -/
theorem exists_crossingFree_path_to_one_iff {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (∃ H : ℝ → Matrix ι ι ℂ, ContinuousOn H (Set.Icc 0 1) ∧ H 0 = A ∧ H 1 = 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (H t).IsHermitian ∧ hermNullIndex (H t) = 0) ↔
      hermNegIndex A = 0 ∧ hermNullIndex A = 0 := by
  constructor
  · rintro ⟨H, hc, h0, h1, hH⟩
    have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have heq := hermNegIndex_eq_of_isPreconnected isPreconnected_Icc hc (fun t ht => (hH t ht).1)
      (fun t ht => (hH t ht).2) hmem0 hmem1
    rw [h0, h1, hermNegIndex_one] at heq
    exact ⟨heq, h0 ▸ (hH 0 hmem0).2⟩
  · rintro ⟨hneg, hnull⟩
    have hpos : ∀ i, 0 < hA.eigenvalues i := by
      intro i
      rw [negIndex_eq_card_neg_eigenvalues hA, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff] at hneg
      rw [nullIndex_eq_card_zero_eigenvalues hA, Finset.card_eq_zero,
        Finset.filter_eq_empty_iff] at hnull
      exact lt_of_le_of_ne (not_lt.mp (hneg (Finset.mem_univ i)))
        (Ne.symm (hnull (Finset.mem_univ i)))
    refine ⟨straightPath A, ?_, by simp [straightPath], by simp [straightPath], fun t ht => ?_⟩
    · unfold straightPath; fun_prop
    refine ⟨straightPath_isHermitian hA t, ?_⟩
    rw [← nullIndex_conjugate _ (isUnit_eigenvectorUnitary hA),
      conjTranspose_mul_straightPath_mul hA, nullIndex_diagonal, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro i _
    have := hpos i
    have : 0 < (1 - t) * hA.eigenvalues i + t := by
      rcases ht.2.lt_or_eq with h | h
      · nlinarith [ht.1]
      · rw [h]; norm_num
    exact this.ne'

end GaloisForLFunctions.EdgeHodgeTheory
