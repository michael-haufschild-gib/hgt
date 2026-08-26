import GaloisForLFunctions.RHTower.SquarefreeCutoffJumpInertia
import GaloisForLFunctions.HTGeometry.RectangularKreinInertia
import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.AveragedCentralizerProjectionFloor

/-!
# Exact spectrum of the squarefree shear kernel

For `p = k + 2`, the raw local shear block is

`K_p(i,j) = p 1_(i=0) + p 1_(j=0) - 1`.

This module proves its exact rank-two inertia, its two nonzero eigenvalues

`p/2 * (1 ± sqrt (4p - 3))`,

and explicit eigenvectors.  Tensoring a nonempty finite family gives rank `2^r`, balanced positive
and negative indices `2^(r-1)`, nullity `∏ p - 2^r`, and one explicit nonzero eigenpair for every
sign choice.  The zero-aware tensor sign-count lemmas are stated generically because local shear
blocks have nontrivial kernels.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace RHTower

open Matrix GaloisForLFunctions.HTGeometry

noncomputable section

def localPositiveFeature (k : ℕ) : Fin 1 → (Fin (k + 2) → ℂ) :=
  fun _ a => localFrame k a 0

def localNegativeFeature (k : ℕ) : Fin 1 → (Fin (k + 2) → ℂ) :=
  fun _ a => localFrame k a 1

theorem localFrame_columns_linearIndependent (k : ℕ) :
    LinearIndependent ℂ (fun i : Fin 2 => fun a => localFrame k a i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hP := localScale_ne_zero k
  have hP_inv : (localScale k)⁻¹ ≠ 0 := inv_ne_zero hP
  have hrow1 := congrFun hc (1 : Fin (k + 2))
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hrow1
  have hc1 : c 1 = 0 := by
    have hrow1' : c 1 * (localScale k)⁻¹ = 0 := by
      simpa [localFrame] using hrow1
    exact (mul_eq_zero.mp hrow1').resolve_right hP_inv
  have hrow0 := congrFun hc (0 : Fin (k + 2))
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, Pi.zero_apply] at hrow0
  have hc0 : c 0 = 0 := by
    simpa [localFrame, hc1] using hrow0
  fin_cases i
  · exact hc0
  · exact hc1

theorem localFeature_linearIndependent (k : ℕ) :
    LinearIndependent ℂ (Sum.elim (localPositiveFeature k) (localNegativeFeature k)) := by
  let e : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)
  have he : Function.Injective e := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (Subsingleton.elim i j)
    · simp [e] at hij
    · simp [e] at hij
    · exact congrArg Sum.inr (Subsingleton.elim i j)
  have h := (localFrame_columns_linearIndependent k).comp e he
  rw [show Sum.elim (localPositiveFeature k) (localNegativeFeature k) =
      (fun i : Fin 2 => fun a => localFrame k a i) ∘ e by
    funext s
    rcases s with i | i <;> fin_cases i <;>
      rfl]
  exact h

theorem localDensityBlock_eq_rectangularKreinForm (k : ℕ) :
    localDensityBlock k =
      rectangularKreinForm (localPositiveFeature k) (localNegativeFeature k) := by
  ext a b
  simp [localDensityBlock, rectangularKreinForm, localPositiveFeature, localNegativeFeature,
    Matrix.mul_apply, binaryJ, Matrix.diagonal_apply, star_localFrame, Fin.sum_univ_two]
  ring

def signWithZero (r : ℝ) : ℝ := if 0 < r then 1 else if r < 0 then -1 else 0

theorem signWithZero_mul (a b : ℝ) : signWithZero (a * b) = signWithZero a * signWithZero b := by
  by_cases ha0 : a = 0
  · subst a
    simp [signWithZero]
  by_cases hb0 : b = 0
  · subst b
    simp [signWithZero]
  rcases lt_or_gt_of_ne ha0 with ha | ha <;> rcases lt_or_gt_of_ne hb0 with hb | hb
  · have hab : 0 < a * b := mul_pos_of_neg_of_neg ha hb
    simp [signWithZero, ha, hb, hab, not_lt_of_ge ha.le, not_lt_of_ge hb.le]
  · have hab : a * b < 0 := mul_neg_of_neg_of_pos ha hb
    simp [signWithZero, ha, hb, hab, not_lt_of_ge ha.le]
  · have hab : a * b < 0 := mul_neg_of_pos_of_neg ha hb
    simp [signWithZero, ha, hb, hab, not_lt_of_ge hb.le]
  · have hab : 0 < a * b := mul_pos ha hb
    simp [signWithZero, ha, hb, hab]

theorem signWithZero_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    signWithZero (∏ i ∈ s, f i) = ∏ i ∈ s, signWithZero (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signWithZero]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, signWithZero_mul, ih]

theorem sum_signWithZero {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, signWithZero (f i)) =
      (({i | 0 < f i} : Finset ι).card : ℝ) - (({i | f i < 0} : Finset ι).card : ℝ) := by
  classical
  have hpoint : ∀ i, signWithZero (f i) =
      (if 0 < f i then 1 else 0) - (if f i < 0 then 1 else 0) := by
    intro i
    by_cases h0 : f i = 0
    · simp [signWithZero, h0]
    rcases lt_or_gt_of_ne h0 with h | h
    · simp [signWithZero, h, not_lt_of_ge h.le]
    · simp [signWithZero, h, not_lt_of_ge h.le]
  rw [Finset.sum_congr rfl fun i _ => hpoint i, Finset.sum_sub_distrib]
  simp only [Finset.sum_boole]

theorem card_pos_sub_card_neg_tensor_with_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (mu : ∀ i, α i → ℝ) :
    ((({x : ∀ i, α i | 0 < ∏ i, mu i (x i)} : Finset (∀ i, α i)).card : ℝ)
        - (({x : ∀ i, α i | ∏ i, mu i (x i) < 0} : Finset (∀ i, α i)).card : ℝ))
      = ∏ i, ((({a | 0 < mu i a} : Finset (α i)).card : ℝ)
              - (({a | mu i a < 0} : Finset (α i)).card : ℝ)) := by
  classical
  rw [← sum_signWithZero (fun x : ∀ i, α i => ∏ i, mu i (x i))]
  rw [Finset.sum_congr rfl fun x _ => signWithZero_prod Finset.univ (fun i => mu i (x i))]
  rw [sum_prod_eq_prod_sum (fun i a => signWithZero (mu i a))]
  exact Finset.prod_congr rfl fun i _ => sum_signWithZero (mu i)

def prodNonzeroEquiv
    {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (mu : ∀ i, α i → ℝ) :
    {x : ∀ i, α i // ∏ i, mu i (x i) ≠ 0} ≃ ∀ i, {a : α i // mu i a ≠ 0} where
  toFun x i := ⟨x.1 i, (Finset.prod_ne_zero_iff.mp x.2) i (Finset.mem_univ i)⟩
  invFun x := ⟨fun i => (x i).1,
    Finset.prod_ne_zero_iff.mpr fun i _ => (x i).2⟩
  left_inv x := by ext i; rfl
  right_inv x := by ext i; rfl

theorem card_ne_zero_tensor
    {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
    (mu : ∀ i, α i → ℝ) :
    ({x : ∀ i, α i | ∏ i, mu i (x i) ≠ 0} : Finset (∀ i, α i)).card =
      ∏ i, ({a | mu i a ≠ 0} : Finset (α i)).card := by
  classical
  rw [← Fintype.card_subtype]
  calc
    Fintype.card {x : ∀ i, α i // ∏ i, mu i (x i) ≠ 0} =
        Fintype.card (∀ i, {a : α i // mu i a ≠ 0}) :=
      Fintype.card_congr (prodNonzeroEquiv mu)
    _ = ∏ i, Fintype.card {a : α i // mu i a ≠ 0} := Fintype.card_pi
    _ = ∏ i, ({a | mu i a ≠ 0} : Finset (α i)).card := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Fintype.card_subtype]

theorem card_pos_add_card_neg_eq_card_ne_zero {α : Type*} [Fintype α] (f : α → ℝ) :
    ({a | 0 < f a} : Finset α).card + ({a | f a < 0} : Finset α).card =
      ({a | f a ≠ 0} : Finset α).card := by
  classical
  have hd : Disjoint ({a | 0 < f a} : Finset α) ({a | f a < 0} : Finset α) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    linarith
  rw [← Finset.card_union_of_disjoint hd]
  congr 1
  ext a
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => by rcases h with h | h <;> linarith,
    fun h => (lt_or_gt_of_ne h).symm⟩

theorem hermNegIndex_rectangularKreinForm_eq {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (hT : Function.Surjective
      ((rectangularFeatureEval w).prod (rectangularFeatureEval u))) :
    hermNegIndex (rectangularKreinForm w u) = kn := by
  have hchar := rectangular_exact_neg_inertia w u hT
  apply le_antisymm
  · obtain ⟨W, hWrank, hW⟩ :=
      exists_isPosDefOn_finrank_eq_posIndex (-(rectangularKreinForm w u))
    rw [hermNegIndex, ← hWrank]
    apply hchar.1 W
    intro y hy hy0
    have hpos := hW y hy hy0
    rw [hermQuad_neg] at hpos
    exact neg_pos.mp hpos
  · obtain ⟨W, hWrank, hW⟩ := hchar.2
    calc
      kn = Module.finrank ℂ W := hWrank.symm
      _ ≤ hermPosIndex (-(rectangularKreinForm w u)) := by
        apply finrank_le_posIndex
        intro y hy hy0
        rw [hermQuad_neg]
        exact neg_pos.mpr (hW y hy hy0)
      _ = hermNegIndex (rectangularKreinForm w u) := rfl

theorem hermPosIndex_rectangularKreinForm_eq {N kp kn : ℕ}
    (w : Fin kp → (Fin N → ℂ)) (u : Fin kn → (Fin N → ℂ))
    (hT : Function.Surjective
      ((rectangularFeatureEval w).prod (rectangularFeatureEval u))) :
    hermPosIndex (rectangularKreinForm w u) = kp := by
  have hchar := rectangular_exact_pos_inertia w u hT
  apply le_antisymm
  · obtain ⟨W, hWrank, hW⟩ :=
      exists_isPosDefOn_finrank_eq_posIndex (rectangularKreinForm w u)
    rw [← hWrank]
    exact hchar.1 W hW
  · obtain ⟨W, hWrank, hW⟩ := hchar.2
    calc
      kp = Module.finrank ℂ W := hWrank.symm
      _ ≤ hermPosIndex (rectangularKreinForm w u) := finrank_le_posIndex hW

theorem localDensityBlock_posIndex (k : ℕ) : hermPosIndex (localDensityBlock k) = 1 := by
  rw [localDensityBlock_eq_rectangularKreinForm]
  apply hermPosIndex_rectangularKreinForm_eq
  exact rectangular_eval_surjective_of_linearIndependent _ _ (localFeature_linearIndependent k)

theorem localDensityBlock_negIndex (k : ℕ) : hermNegIndex (localDensityBlock k) = 1 := by
  rw [localDensityBlock_eq_rectangularKreinForm]
  apply hermNegIndex_rectangularKreinForm_eq
  exact rectangular_eval_surjective_of_linearIndependent _ _ (localFeature_linearIndependent k)

theorem localDensityBlock_nullIndex (k : ℕ) : hermNullIndex (localDensityBlock k) = k := by
  have h := posIndex_add_negIndex_add_nullIndex (isHermitian_localDensityBlock k)
  rw [localDensityBlock_posIndex, localDensityBlock_negIndex] at h
  simp only [Fintype.card_fin] at h
  omega

theorem tensorFamily_inertia_of_local_one_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    (M : ∀ i, Matrix (α i) (α i) ℂ)
    (hM : ∀ i, (M i).IsHermitian)
    (hpos : ∀ i, hermPosIndex (M i) = 1)
    (hneg : ∀ i, hermNegIndex (M i) = 1) :
    hermPosIndex (tensorFamily M) = 2 ^ (Fintype.card ι - 1) ∧
      hermNegIndex (tensorFamily M) = 2 ^ (Fintype.card ι - 1) ∧
      hermNullIndex (tensorFamily M) =
        (∏ i, Fintype.card (α i)) - 2 ^ Fintype.card ι := by
  classical
  let mu : ∀ i, α i → ℝ := fun i => (hM i).eigenvalues
  have hposCard : ∀ i, ({a | 0 < mu i a} : Finset (α i)).card = 1 := by
    intro i
    rw [← posIndex_eq_card_pos_eigenvalues (hM i), hpos i]
  have hnegCard : ∀ i, ({a | mu i a < 0} : Finset (α i)).card = 1 := by
    intro i
    rw [← negIndex_eq_card_neg_eigenvalues (hM i), hneg i]
  have hneCard : ∀ i, ({a | mu i a ≠ 0} : Finset (α i)).card = 2 := by
    intro i
    rw [← card_pos_add_card_neg_eq_card_ne_zero (mu i), hposCard i, hnegCard i]
  have hdiff := card_pos_sub_card_neg_tensor_with_zero mu
  have hdiff0 :
      ((({x : ∀ i, α i | 0 < ∏ i, mu i (x i)} : Finset (∀ i, α i)).card : ℝ)
          - (({x : ∀ i, α i | ∏ i, mu i (x i) < 0} : Finset (∀ i, α i)).card : ℝ)) = 0 := by
    rw [hdiff]
    obtain ⟨i0⟩ := ‹Nonempty ι›
    apply Finset.prod_eq_zero (Finset.mem_univ i0)
    rw [hposCard i0, hnegCard i0]
    norm_num
  have hbalance :
      ({x : ∀ i, α i | 0 < ∏ i, mu i (x i)} : Finset (∀ i, α i)).card =
        ({x : ∀ i, α i | ∏ i, mu i (x i) < 0} : Finset (∀ i, α i)).card := by
    exact_mod_cast (sub_eq_zero.mp hdiff0)
  have hnonzero := card_ne_zero_tensor mu
  have hnonzero' :
      ({x : ∀ i, α i | ∏ i, mu i (x i) ≠ 0} : Finset (∀ i, α i)).card =
        2 ^ Fintype.card ι := by
    rw [hnonzero]
    simp_rw [hneCard]
    rw [Finset.prod_const, Finset.card_univ]
  have htotal := card_pos_add_card_neg_eq_card_ne_zero
    (fun x : ∀ i, α i => ∏ i, mu i (x i))
  rw [hnonzero'] at htotal
  have hpow : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
    rw [hn, Nat.succ_sub_one, pow_succ]
    omega
  have hpositive :
      ({x : ∀ i, α i | 0 < ∏ i, mu i (x i)} : Finset (∀ i, α i)).card =
        2 ^ (Fintype.card ι - 1) := by
    rw [hbalance] at htotal
    rw [hpow] at htotal
    omega
  have hnegative :
      ({x : ∀ i, α i | ∏ i, mu i (x i) < 0} : Finset (∀ i, α i)).card =
        2 ^ (Fintype.card ι - 1) := hbalance.symm.trans hpositive
  have hglobalHerm : (tensorFamily M).IsHermitian := isHermitian_tensorFamily hM
  have hposGlobal : hermPosIndex (tensorFamily M) = 2 ^ (Fintype.card ι - 1) := by
    rw [posIndex_tensorFamily hM]
    exact hpositive
  have hnegGlobal : hermNegIndex (tensorFamily M) = 2 ^ (Fintype.card ι - 1) := by
    rw [negIndex_tensorFamily hM]
    exact hnegative
  refine ⟨hposGlobal, hnegGlobal, ?_⟩
  have hcomplete := posIndex_add_negIndex_add_nullIndex hglobalHerm
  rw [hposGlobal, hnegGlobal, Fintype.card_pi] at hcomplete
  have htwice : 2 ^ (Fintype.card ι - 1) + 2 ^ (Fintype.card ι - 1) =
      2 * 2 ^ (Fintype.card ι - 1) := by omega
  rw [htwice, ← hpow] at hcomplete
  omega

theorem crossingDensity_inertia
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m : ι → ℕ) :
    hermPosIndex (crossingDensity m) = 2 ^ (Fintype.card ι - 1) ∧
      hermNegIndex (crossingDensity m) = 2 ^ (Fintype.card ι - 1) ∧
      hermNullIndex (crossingDensity m) =
        (∏ i, (m i + 2)) - 2 ^ Fintype.card ι := by
  simpa [crossingDensity] using
    tensorFamily_inertia_of_local_one_one
      (fun i => localDensityBlock (m i))
      (fun i => isHermitian_localDensityBlock (m i))
      (fun i => localDensityBlock_posIndex (m i))
      (fun i => localDensityBlock_negIndex (m i))

theorem rank_eq_posIndex_add_negIndex
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    H.rank = hermPosIndex H + hermNegIndex H := by
  rw [hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  rw [← card_pos_add_card_neg_eq_card_ne_zero hH.eigenvalues]
  rw [← posIndex_eq_card_pos_eigenvalues hH, ← negIndex_eq_card_neg_eigenvalues hH]

/-- Raw local shear block `K_p`, with `p = k + 2`. -/
def localRawShearBlock (k : ℕ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  localShearKernel (localScale k) (0 : Fin (k + 2))

theorem localRawShearBlock_eq_smul_density (k : ℕ) :
    localRawShearBlock k =
      (((realScale k) ^ 2 : ℝ) : ℂ) • localDensityBlock k := by
  ext a b
  rw [localRawShearBlock, Matrix.smul_apply, smul_eq_mul, localDensityBlock_apply,
    localShearKernel, localScale_eq]
  have hP := (realScale_pos k).ne'
  have hPc : (((realScale k : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hP
  push_cast
  field_simp [hPc]

theorem realScale_sq_pos (k : ℕ) : 0 < realScale k ^ 2 := sq_pos_of_pos (realScale_pos k)

theorem isHermitian_localRawShearBlock (k : ℕ) : (localRawShearBlock k).IsHermitian := by
  rw [localRawShearBlock_eq_smul_density]
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, (isHermitian_localDensityBlock k).eq]
  simp

theorem localRawShearBlock_posIndex (k : ℕ) : hermPosIndex (localRawShearBlock k) = 1 := by
  rw [localRawShearBlock_eq_smul_density,
    posIndex_smul_pos (realScale_sq_pos k), localDensityBlock_posIndex]

theorem localRawShearBlock_negIndex (k : ℕ) : hermNegIndex (localRawShearBlock k) = 1 := by
  rw [localRawShearBlock_eq_smul_density,
    negIndex_smul_pos (realScale_sq_pos k), localDensityBlock_negIndex]

theorem localRawShearBlock_nullIndex (k : ℕ) : hermNullIndex (localRawShearBlock k) = k := by
  have h := posIndex_add_negIndex_add_nullIndex (isHermitian_localRawShearBlock k)
  rw [localRawShearBlock_posIndex, localRawShearBlock_negIndex] at h
  simp only [Fintype.card_fin] at h
  omega

def localShearEigenPlus (k : ℕ) : ℝ :=
  realScale k / 2 * (1 + Real.sqrt (4 * realScale k - 3))

def localShearEigenMinus (k : ℕ) : ℝ :=
  realScale k / 2 * (1 - Real.sqrt (4 * realScale k - 3))

theorem localShearRadicand_nonneg (k : ℕ) : 0 ≤ 4 * realScale k - 3 := by
  have hp := realScale_pos k
  rw [realScale] at hp ⊢
  linarith

theorem localShearSqrt_sq (k : ℕ) :
    Real.sqrt (4 * realScale k - 3) ^ 2 = 4 * realScale k - 3 :=
  Real.sq_sqrt (localShearRadicand_nonneg k)

theorem localShearEigenPlus_quadratic (k : ℕ) :
    localShearEigenPlus k ^ 2 - realScale k * localShearEigenPlus k -
      realScale k ^ 2 * (realScale k - 1) = 0 := by
  rw [localShearEigenPlus]
  nlinarith [localShearSqrt_sq k]

theorem localShearEigenMinus_quadratic (k : ℕ) :
    localShearEigenMinus k ^ 2 - realScale k * localShearEigenMinus k -
      realScale k ^ 2 * (realScale k - 1) = 0 := by
  rw [localShearEigenMinus]
  nlinarith [localShearSqrt_sq k]

theorem one_lt_localShearSqrt (k : ℕ) :
    1 < Real.sqrt (4 * realScale k - 3) := by
  calc
    1 = Real.sqrt 1 := by norm_num
    _ < Real.sqrt (4 * realScale k - 3) := Real.sqrt_lt_sqrt (by norm_num) (by
      rw [realScale]
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)

theorem localShearEigenPlus_pos (k : ℕ) : 0 < localShearEigenPlus k := by
  rw [localShearEigenPlus]
  have hp := realScale_pos k
  have hs := Real.sqrt_nonneg (4 * realScale k - 3)
  nlinarith

theorem localShearEigenMinus_neg (k : ℕ) : localShearEigenMinus k < 0 := by
  rw [localShearEigenMinus]
  have hp := realScale_pos k
  have hs := one_lt_localShearSqrt k
  nlinarith

def localShearEigenvector (k : ℕ) (lambda : ℝ) : Fin (k + 2) → ℂ :=
  fun a => if a = 0 then ((lambda + realScale k - 1 : ℝ) : ℂ)
    else ((realScale k - 1 : ℝ) : ℂ)

theorem localShearEigenvector_ne_zero (k : ℕ) (lambda : ℝ) :
    localShearEigenvector k lambda ≠ 0 := by
  intro hzero
  have h1 := congrFun hzero (1 : Fin (k + 2))
  simp [localShearEigenvector, realScale] at h1
  have h1re := congrArg Complex.re h1
  norm_num at h1re
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem sum_localShearEigenvector (k : ℕ) (lambda : ℝ) :
    (∑ a, localShearEigenvector k lambda a) =
      ((lambda + realScale k * (realScale k - 1) : ℝ) : ℂ) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2)))]
  have hrest :
      (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)), localShearEigenvector k lambda a) =
        ((k : ℂ) + 1) * (((realScale k - 1 : ℝ) : ℂ)) := by
    rw [← sum_erase_const k (((realScale k - 1 : ℝ) : ℂ))]
    exact Finset.sum_congr rfl fun a ha => by
      rw [localShearEigenvector, if_neg (Finset.ne_of_mem_erase ha)]
  rw [hrest, localShearEigenvector, if_pos rfl, realScale]
  push_cast
  ring

theorem localRawShearBlock_mulVec_eigenvector
    (k : ℕ) (lambda : ℝ)
    (hquad : lambda ^ 2 - realScale k * lambda -
      realScale k ^ 2 * (realScale k - 1) = 0) :
    localRawShearBlock k *ᵥ localShearEigenvector k lambda =
      (lambda : ℂ) • localShearEigenvector k lambda := by
  classical
  funext a
  rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  simp only [localRawShearBlock, localShearKernel]
  have hexpand : ∀ b : Fin (k + 2),
      (localScale k * (if a = 0 then 1 else 0) +
          localScale k * (if b = 0 then 1 else 0) - 1) *
          localShearEigenvector k lambda b =
        (localScale k * (if a = 0 then 1 else 0) - 1) *
            localShearEigenvector k lambda b +
          localScale k * ((if b = 0 then 1 else 0) *
            localShearEigenvector k lambda b) := by
    intro b
    ring
  rw [Finset.sum_congr rfl fun b _ => hexpand b, Finset.sum_add_distrib,
    ← Finset.mul_sum, sum_localShearEigenvector, ← Finset.mul_sum]
  have hdelta :
      (∑ b : Fin (k + 2), (if b = 0 then (1 : ℂ) else 0) *
        localShearEigenvector k lambda b) = localShearEigenvector k lambda 0 := by
    rw [Finset.sum_eq_single (0 : Fin (k + 2))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hdelta, localScale_eq]
  have hquadC := congrArg (fun x : ℝ => (x : ℂ)) hquad
  push_cast at hquadC
  by_cases ha : a = 0
  · subst a
    simp only [if_pos, localShearEigenvector]
    push_cast
    ring_nf at hquadC ⊢
    linear_combination -hquadC
  · simp only [if_neg ha, localShearEigenvector]
    push_cast
    ring

theorem localRawShearBlock_plus_eigenvector (k : ℕ) :
    localRawShearBlock k *ᵥ localShearEigenvector k (localShearEigenPlus k) =
      (localShearEigenPlus k : ℂ) • localShearEigenvector k (localShearEigenPlus k) :=
  localRawShearBlock_mulVec_eigenvector k _ (localShearEigenPlus_quadratic k)

theorem localRawShearBlock_minus_eigenvector (k : ℕ) :
    localRawShearBlock k *ᵥ localShearEigenvector k (localShearEigenMinus k) =
      (localShearEigenMinus k : ℂ) • localShearEigenvector k (localShearEigenMinus k) :=
  localRawShearBlock_mulVec_eigenvector k _ (localShearEigenMinus_quadratic k)

def localShearEigenvalue (k : ℕ) (s : Fin 2) : ℂ :=
  if s = 0 then (localShearEigenPlus k : ℂ) else (localShearEigenMinus k : ℂ)

def localShearSpectralVector (k : ℕ) (s : Fin 2) : Fin (k + 2) → ℂ :=
  if s = 0 then localShearEigenvector k (localShearEigenPlus k)
    else localShearEigenvector k (localShearEigenMinus k)

theorem localShearEigenvalue_injective (k : ℕ) :
    Function.Injective (localShearEigenvalue k) := by
  intro s t hst
  fin_cases s <;> fin_cases t
  · rfl
  · change (localShearEigenPlus k : ℂ) = (localShearEigenMinus k : ℂ) at hst
    have hre : localShearEigenPlus k = localShearEigenMinus k := by exact_mod_cast hst
    linarith [localShearEigenPlus_pos k, localShearEigenMinus_neg k]
  · change (localShearEigenMinus k : ℂ) = (localShearEigenPlus k : ℂ) at hst
    have hre : localShearEigenMinus k = localShearEigenPlus k := by exact_mod_cast hst
    linarith [localShearEigenPlus_pos k, localShearEigenMinus_neg k]
  · rfl

theorem localRawShearBlock_hasEigenvector (k : ℕ) (s : Fin 2) :
    Module.End.HasEigenvector
      ((localRawShearBlock k).mulVecLin : Module.End ℂ (Fin (k + 2) → ℂ))
      (localShearEigenvalue k s) (localShearSpectralVector k s) := by
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
  constructor
  · rw [Matrix.mulVecLin_apply]
    fin_cases s
    · simpa [localShearEigenvalue, localShearSpectralVector] using
        localRawShearBlock_plus_eigenvector k
    · simpa [localShearEigenvalue, localShearSpectralVector] using
        localRawShearBlock_minus_eigenvector k
  · fin_cases s
    · simpa [localShearSpectralVector] using
        localShearEigenvector_ne_zero k (localShearEigenPlus k)
    · simpa [localShearSpectralVector] using
        localShearEigenvector_ne_zero k (localShearEigenMinus k)

theorem localShearSpectralVector_linearIndependent (k : ℕ) :
    LinearIndependent ℂ (localShearSpectralVector k) :=
  Module.End.eigenvectors_linearIndependent' (localRawShearBlock k).mulVecLin
    (localShearEigenvalue k) (localShearEigenvalue_injective k)
    (localShearSpectralVector k) (localRawShearBlock_hasEigenvector k)

theorem localRawShearBlock_rank (k : ℕ) : (localRawShearBlock k).rank = 2 := by
  rw [rank_eq_posIndex_add_negIndex (isHermitian_localRawShearBlock k),
    localRawShearBlock_posIndex, localRawShearBlock_negIndex]

/-! ## Exact local operator norms -/

theorem l2_opNorm_vecMulVec_star
    {n : Type*} [Fintype n] [DecidableEq n] (x : EuclideanSpace ℂ n) :
    ‖(Matrix.vecMulVec x (star x) : Matrix n n ℂ)‖ = ‖x‖ ^ 2 := by
  rw [← InnerProductSpace.symm_toEuclideanLin_rankOne x x]
  rw [Matrix.l2_opNorm_def, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hclm : LinearMap.toContinuousLinearMap
      ((InnerProductSpace.rankOne ℂ x x : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
        EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) =
      InnerProductSpace.rankOne ℂ x x := by
    ext z
    rfl
  rw [hclm]
  simp [pow_two]

theorem l2_opNorm_vecMulVec_self_of_star
    {n : Type*} [Fintype n] [DecidableEq n] (x : n → ℂ) (hx : star x = x) :
    ‖(Matrix.vecMulVec x x : Matrix n n ℂ)‖ = ‖WithLp.toLp 2 x‖ ^ 2 := by
  have hmatrix : Matrix.vecMulVec x x =
      Matrix.vecMulVec (WithLp.toLp 2 x) (star (WithLp.toLp 2 x)) := by
    ext i j
    simp [hx]
  rw [hmatrix, l2_opNorm_vecMulVec_star]

theorem exists_eigenvalues_eq_of_hasEigenvalue
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (lambda : ℝ)
    (hlambda : Module.End.HasEigenvalue H.mulVecLin (lambda : ℂ)) :
    ∃ i, hH.eigenvalues i = lambda := by
  have hmemLin : (lambda : ℂ) ∈ spectrum ℂ H.toLin' := by
    rw [Matrix.toLin'_apply']
    exact hlambda.mem_spectrum
  have hmemMatrix : (lambda : ℂ) ∈ spectrum ℂ H := by
    simpa using hmemLin
  rw [hH.spectrum_eq_image_range] at hmemMatrix
  obtain ⟨r, ⟨i, hi⟩, hr⟩ := hmemMatrix
  refine ⟨i, ?_⟩
  subst r
  exact Complex.ofReal_injective hr

theorem l2_opNorm_eq_norm_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ‖H‖ = ‖fun i => (hH.eigenvalues i : ℂ)‖ := by
  conv_lhs => rw [isHermitian_eq_conj_diagonal hH]
  rw [l2_opNorm_unitary_conj_eq hH.eigenvectorUnitary.2, Matrix.l2_opNorm_diagonal]

theorem localShearEigenPlus_add_minus (k : ℕ) :
    localShearEigenPlus k + localShearEigenMinus k = realScale k := by
  rw [localShearEigenPlus, localShearEigenMinus]
  ring

theorem abs_localShearEigenMinus_lt_plus (k : ℕ) :
    |localShearEigenMinus k| < localShearEigenPlus k := by
  rw [abs_of_neg (localShearEigenMinus_neg k)]
  linarith [localShearEigenPlus_add_minus k, realScale_pos k]

theorem localRawShearBlock_l2_opNorm (k : ℕ) :
    ‖localRawShearBlock k‖ = localShearEigenPlus k := by
  let hH := isHermitian_localRawShearBlock k
  obtain ⟨ip, hip⟩ := exists_eigenvalues_eq_of_hasEigenvalue hH
    (localShearEigenPlus k)
    (Module.End.hasEigenvalue_of_hasEigenvector (localRawShearBlock_hasEigenvector k 0))
  obtain ⟨im, him⟩ := exists_eigenvalues_eq_of_hasEigenvalue hH
    (localShearEigenMinus k)
    (Module.End.hasEigenvalue_of_hasEigenvector (localRawShearBlock_hasEigenvector k 1))
  have hposCard :
      ({i | 0 < hH.eigenvalues i} : Finset (Fin (k + 2))).card = 1 := by
    rw [← posIndex_eq_card_pos_eigenvalues hH, localRawShearBlock_posIndex]
  have hnegCard :
      ({i | hH.eigenvalues i < 0} : Finset (Fin (k + 2))).card = 1 := by
    rw [← negIndex_eq_card_neg_eigenvalues hH, localRawShearBlock_negIndex]
  have hipMem : ip ∈ ({i | 0 < hH.eigenvalues i} : Finset (Fin (k + 2))) := by
    simp [hip, localShearEigenPlus_pos]
  have himMem : im ∈ ({i | hH.eigenvalues i < 0} : Finset (Fin (k + 2))) := by
    simp [him, localShearEigenMinus_neg]
  have hpositive : ∀ i, 0 < hH.eigenvalues i → hH.eigenvalues i = localShearEigenPlus k := by
    intro i hi
    have hiMem : i ∈ ({j | 0 < hH.eigenvalues j} : Finset (Fin (k + 2))) := by simpa
    have hii : i = ip := (Finset.card_le_one.mp (by omega :
      ({j | 0 < hH.eigenvalues j} : Finset (Fin (k + 2))).card ≤ 1))
        i hiMem ip hipMem
    simpa [hii] using hip
  have hnegative : ∀ i, hH.eigenvalues i < 0 →
      hH.eigenvalues i = localShearEigenMinus k := by
    intro i hi
    have hiMem : i ∈ ({j | hH.eigenvalues j < 0} : Finset (Fin (k + 2))) := by simpa
    have hii : i = im := (Finset.card_le_one.mp (by omega :
      ({j | hH.eigenvalues j < 0} : Finset (Fin (k + 2))).card ≤ 1))
        i hiMem im himMem
    simpa [hii] using him
  rw [l2_opNorm_eq_norm_eigenvalues hH]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (localShearEigenPlus_pos k).le).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases lt_trichotomy (hH.eigenvalues i) 0 with hi | hi | hi
    · rw [hnegative i hi]
      exact (abs_localShearEigenMinus_lt_plus k).le
    · simp [hi, (localShearEigenPlus_pos k).le]
    · rw [hpositive i hi, abs_of_pos (localShearEigenPlus_pos k)]
  · calc
      localShearEigenPlus k = ‖((localShearEigenPlus k : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (localShearEigenPlus_pos k)]
      _ = ‖((hH.eigenvalues ip : ℝ) : ℂ)‖ := by rw [hip]
      _ ≤ ‖fun i : Fin (k + 2) => ((hH.eigenvalues i : ℝ) : ℂ)‖ :=
        norm_le_pi_norm (fun i : Fin (k + 2) => ((hH.eigenvalues i : ℝ) : ℂ)) ip

/-- Normalized negative branch `B_p = p⁻² b_p b_pᵀ`, written as the outer square of the
second density-frame column `p⁻¹ b_p`. -/
def localComplementBlock (k : ℕ) : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  Matrix.vecMulVec (fun a => localFrame k a 1) (fun a => localFrame k a 1)

theorem localDensityBlock_eq_anchor_sub_complement (k : ℕ) :
    localDensityBlock k = localAnchorBlock k - localComplementBlock k := by
  ext a b
  simp [localDensityBlock, binaryJ, localComplementBlock, localAnchorBlock, Matrix.mul_apply,
    Matrix.diagonal_apply, Matrix.vecMulVec_apply, star_localFrame, Fin.sum_univ_two]
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b
      simp [localFrame]
      ring
    · simp [hb, Ne.symm hb, localFrame]
  · by_cases hb : b = 0
    · subst b
      simp [ha, localFrame]
    · simp [ha, hb, localFrame]

theorem localAnchorBlock_l2_opNorm (k : ℕ) : ‖localAnchorBlock k‖ = 1 := by
  rw [localAnchorBlock, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
    intro a
    by_cases ha : a = 0 <;> simp [ha]
  · calc
      (1 : ℝ) = ‖(if (0 : Fin (k + 2)) = 0 then (1 : ℂ) else 0)‖ := by simp
      _ ≤ ‖fun a : Fin (k + 2) => if a = 0 then (1 : ℂ) else 0‖ :=
        norm_le_pi_norm
          (fun a : Fin (k + 2) => if a = 0 then (1 : ℂ) else 0) (0 : Fin (k + 2))

theorem localFrame_one (k : ℕ) (a : Fin (k + 2)) :
    localFrame k a 1 = (localScale k)⁻¹ - if a = 0 then 1 else 0 := by
  simp [localFrame]

theorem norm_sq_localComplementVector (k : ℕ) :
    ‖WithLp.toLp 2 (fun a : Fin (k + 2) => localFrame k a 1)‖ ^ 2 =
      (realScale k - 1) / realScale k := by
  rw [EuclideanSpace.norm_sq_eq]
  simp_rw [localFrame_one]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2)))]
  have hrest :
      (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)),
        ‖(localScale k)⁻¹ - if a = 0 then 1 else 0‖ ^ 2) =
        ((k : ℝ) + 1) * (realScale k)⁻¹ ^ 2 := by
    calc
      (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)),
          ‖(localScale k)⁻¹ - if a = 0 then 1 else 0‖ ^ 2) =
          ∑ _a ∈ Finset.univ.erase (0 : Fin (k + 2)), (realScale k)⁻¹ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 := Finset.ne_of_mem_erase ha
        rw [if_neg ha0, sub_zero, localScale_eq, norm_inv, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (realScale_pos k)]
      _ = ((k : ℝ) + 1) * (realScale k)⁻¹ ^ 2 := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]
        simp only [nsmul_eq_mul]
        norm_cast
  rw [hrest]
  simp only [if_pos, localScale_eq, norm_sub_rev]
  have hp := realScale_pos k
  have hpne := hp.ne'
  have hcast : (1 : ℂ) - ((realScale k : ℂ))⁻¹ =
      (((1 - (realScale k)⁻¹ : ℝ) : ℂ)) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by exact sub_nonneg.mpr (by
      exact (inv_le_one₀ hp).mpr (by
        rw [realScale]
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith)))]
  rw [realScale]
  field_simp
  ring

theorem localComplementBlock_l2_opNorm (k : ℕ) :
    ‖localComplementBlock k‖ = (realScale k - 1) / realScale k := by
  rw [localComplementBlock,
    l2_opNorm_vecMulVec_self_of_star _ (by
      funext a
      exact star_localFrame k a 1)]
  exact norm_sq_localComplementVector k

/-- Exact local spectral gain `eta(p)`, with `p = k + 2`. -/
def localShearEta (k : ℕ) : ℝ :=
  (1 + Real.sqrt (4 * realScale k - 3)) / (2 * realScale k)

theorem localDensityBlock_l2_opNorm (k : ℕ) :
    ‖localDensityBlock k‖ = localShearEta k := by
  rw [localDensityBlock_eq_smul_shearKernel]
  change ‖(localScale k ^ 2)⁻¹ • localRawShearBlock k‖ = localShearEta k
  rw [norm_smul, localRawShearBlock_l2_opNorm, localScale_eq, norm_inv,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (realScale_pos k)]
  rw [localShearEigenPlus, localShearEta]
  have hp := (realScale_pos k).ne'
  field_simp

theorem localShearEta_pos (k : ℕ) : 0 < localShearEta k := by
  rw [localShearEta]
  have hp := realScale_pos k
  have hs := Real.sqrt_nonneg (4 * realScale k - 3)
  positivity

theorem localDensityBlock_plus_eigenvector (k : ℕ) :
    localDensityBlock k *ᵥ localShearEigenvector k (localShearEigenPlus k) =
      (localShearEta k : ℂ) • localShearEigenvector k (localShearEigenPlus k) := by
  rw [localDensityBlock_eq_smul_shearKernel]
  change ((localScale k ^ 2)⁻¹ • localRawShearBlock k) *ᵥ
      localShearEigenvector k (localShearEigenPlus k) = _
  rw [Matrix.smul_mulVec, localRawShearBlock_plus_eigenvector, smul_smul]
  congr 1
  rw [localScale_eq, localShearEigenPlus, localShearEta]
  push_cast
  have hp := Complex.ofReal_ne_zero.mpr (realScale_pos k).ne'
  field_simp

theorem localDensityBlock_plus_hasEigenvalue (k : ℕ) :
    Module.End.HasEigenvalue (localDensityBlock k).mulVecLin (localShearEta k : ℂ) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (x := localShearEigenvector k (localShearEigenPlus k)) ⟨by
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact localDensityBlock_plus_eigenvector k,
    localShearEigenvector_ne_zero k (localShearEigenPlus k)⟩

theorem isHermitian_localComplementBlock (k : ℕ) :
    (localComplementBlock k).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext a b
  simp [localComplementBlock, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply,
    star_localFrame, mul_comm]

theorem dotProduct_localComplementVector (k : ℕ) :
    (fun a : Fin (k + 2) => localFrame k a 1) ⬝ᵥ
        (fun a : Fin (k + 2) => localFrame k a 1) =
      (((realScale k - 1) / realScale k : ℝ) : ℂ) := by
  rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2)))]
  have hrest :
      (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)),
        localFrame k a 1 * localFrame k a 1) =
      ((k : ℂ) + 1) * (localScale k)⁻¹ ^ 2 := by
    calc
      (∑ a ∈ Finset.univ.erase (0 : Fin (k + 2)),
          localFrame k a 1 * localFrame k a 1) =
          ∑ _a ∈ Finset.univ.erase (0 : Fin (k + 2)), (localScale k)⁻¹ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 := Finset.ne_of_mem_erase ha
        rw [localFrame_one, if_neg ha0, sub_zero, pow_two]
      _ = ((k : ℂ) + 1) * (localScale k)⁻¹ ^ 2 := sum_erase_const k _
  rw [hrest, localFrame_one, if_pos, localScale_eq]
  push_cast
  have hp : ((realScale k : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (realScale_pos k).ne'
  field_simp [hp]
  · rw [realScale]
    push_cast
    ring
  · rfl

theorem localComplementVector_ne_zero (k : ℕ) :
    (fun a : Fin (k + 2) => localFrame k a 1) ≠ 0 := by
  intro hzero
  have h1 := congrFun hzero (1 : Fin (k + 2))
  simp [localFrame, localScale_ne_zero] at h1

theorem localComplementBlock_eigenvector (k : ℕ) :
    localComplementBlock k *ᵥ (fun a => localFrame k a 1) =
      ((((realScale k - 1) / realScale k : ℝ) : ℂ)) •
        (fun a => localFrame k a 1) := by
  rw [localComplementBlock, Matrix.vecMulVec_mulVec, dotProduct_localComplementVector]
  ext a
  change localFrame k a 1 * (((realScale k - 1) / realScale k : ℝ) : ℂ) =
    (((realScale k - 1) / realScale k : ℝ) : ℂ) * localFrame k a 1
  ring

theorem localComplementBlock_top_hasEigenvalue (k : ℕ) :
    Module.End.HasEigenvalue (localComplementBlock k).mulVecLin
      ((((realScale k - 1) / realScale k : ℝ) : ℂ)) :=
  Module.End.hasEigenvalue_of_hasEigenvector
    (x := fun a => localFrame k a 1) ⟨by
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact localComplementBlock_eigenvector k,
    localComplementVector_ne_zero k⟩

theorem localComplementNorm_nonneg (k : ℕ) :
    0 ≤ (realScale k - 1) / realScale k := by
  have hp := realScale_pos k
  have hnum : 0 ≤ realScale k - 1 := by
    rw [realScale]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  positivity

/-- Exact operator norm of a finite tensor family when every local Hermitian factor has a
nonnegative eigenvalue attaining its norm. -/
theorem tensorFamily_l2_opNorm_of_hasTopEigenvalue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Nonempty (α i)]
    (M : ∀ i, Matrix (α i) (α i) ℂ) (hM : ∀ i, (M i).IsHermitian)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hnorm : ∀ i, ‖M i‖ = c i)
    (htop : ∀ i, Module.End.HasEigenvalue (M i).mulVecLin (c i : ℂ)) :
    ‖tensorFamily M‖ = ∏ i, c i := by
  let V : Matrix (∀ i, α i) (∀ i, α i) ℂ := tensorFamily fun i =>
    ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ)
  let mu : (∀ i, α i) → ℂ := fun x => ∏ i, ((hM i).eigenvalues (x i) : ℂ)
  have hV : V ∈ unitary (Matrix (∀ i, α i) (∀ i, α i) ℂ) := by
    rw [Unitary.mem_iff]
    constructor
    · change (tensorFamily fun i =>
          ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ))ᴴ *
          tensorFamily (fun i =>
            ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ)) = 1
      rw [tensorFamily_conjTranspose, tensorFamily_mul]
      have hfamily :
          (fun i => (((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ))ᴴ *
            ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ)) =
            fun i => (1 : Matrix (α i) (α i) ℂ) := by
        funext i
        simpa only [← Matrix.star_eq_conjTranspose] using
          (Unitary.mem_iff.mp (hM i).eigenvectorUnitary.2).1
      rw [hfamily, tensorFamily_one]
    · change tensorFamily (fun i =>
          ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ)) *
          (tensorFamily fun i =>
            ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ))ᴴ = 1
      rw [tensorFamily_conjTranspose, tensorFamily_mul]
      have hfamily :
          (fun i => ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ) *
            (((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ))ᴴ) =
            fun i => (1 : Matrix (α i) (α i) ℂ) := by
        funext i
        simpa only [← Matrix.star_eq_conjTranspose] using
          (Unitary.mem_iff.mp (hM i).eigenvectorUnitary.2).2
      rw [hfamily, tensorFamily_one]
  have hspectral : tensorFamily M = V * Matrix.diagonal mu * star V := by
    have hlocal : M = fun i =>
        ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ) *
          Matrix.diagonal (fun a => (((hM i).eigenvalues a : ℝ) : ℂ)) *
          star ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ) := by
      funext i
      exact isHermitian_eq_conj_diagonal (hM i)
    rw [hlocal]
    dsimp only [V, mu]
    have hstar :
        tensorFamily (fun i =>
          star ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ)) =
        star (tensorFamily fun i =>
          ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ)) := by
      simpa only [Matrix.star_eq_conjTranspose] using
        (tensorFamily_conjTranspose (fun i =>
          ((hM i).eigenvectorUnitary : Matrix (α i) (α i) ℂ))).symm
    rw [← tensorFamily_mul, ← tensorFamily_mul, tensorFamily_diagonal, hstar]
  rw [hspectral, l2_opNorm_unitary_conj_eq hV, Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (Finset.prod_nonneg fun i _ => hc i)).mpr
    intro x
    dsimp only [mu]
    rw [norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
      (fun i _ => by
        rw [← hnorm i]
        simpa [Complex.norm_real, Real.norm_eq_abs] using
          abs_eigenvalue_le_l2_opNorm (hM i) (x i))
  · choose im him using fun i => exists_eigenvalues_eq_of_hasEigenvalue (hM i) (c i) (htop i)
    calc
      (∏ i, c i) = ‖mu (fun i => im i)‖ := by
        dsimp only [mu]
        rw [norm_prod]
        apply Finset.prod_congr rfl
        intro i _
        rw [him i, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc i)]
      _ ≤ ‖mu‖ := norm_le_pi_norm _ (fun i => im i)

def squarefreeShearEta {ι : Type*} [Fintype ι] (m : ι → ℕ) : ℝ :=
  ∏ i, localShearEta (m i)

theorem crossingDensity_l2_opNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) :
    ‖crossingDensity m‖ = squarefreeShearEta m := by
  simpa [crossingDensity, squarefreeShearEta] using
    tensorFamily_l2_opNorm_of_hasTopEigenvalue
      (fun i => localDensityBlock (m i))
      (fun i => isHermitian_localDensityBlock (m i))
      (fun i => localShearEta (m i))
      (fun i => (localShearEta_pos (m i)).le)
      (fun i => localDensityBlock_l2_opNorm (m i))
      (fun i => localDensityBlock_plus_hasEigenvalue (m i))

theorem squarefreeShearEta_pos
    {ι : Type*} [Fintype ι] (m : ι → ℕ) : 0 < squarefreeShearEta m :=
  Finset.prod_pos fun i _ => localShearEta_pos (m i)

/-! ## First-crossing conditioned tensors -/

def firstCrossingSize {ι : Type*} (k : ℕ) (m : ι → ℕ) : Option ι → ℕ
  | none => k
  | some i => m i

def firstCrossingLocalBlock
    {ι : Type*} (k : ℕ) (m : ι → ℕ) :
    ∀ s, Matrix (Fin (firstCrossingSize k m s + 2))
      (Fin (firstCrossingSize k m s + 2)) ℂ
  | none => localComplementBlock k
  | some i => localDensityBlock (m i)

def firstCrossingLocalNorm {ι : Type*} (k : ℕ) (m : ι → ℕ) : Option ι → ℝ
  | none => (realScale k - 1) / realScale k
  | some i => localShearEta (m i)

/-- The exact conditioned tensor `B_p ⊗ T_q`: the new coordinate is fixed to its negative
rank-one branch, while all earlier coordinates retain their signed density blocks. -/
def firstCrossingConditionedTensor
    {ι : Type*} [Fintype ι] (k : ℕ) (m : ι → ℕ) :
    Matrix (∀ s, Fin (firstCrossingSize k m s + 2))
      (∀ s, Fin (firstCrossingSize k m s + 2)) ℂ :=
  tensorFamily (firstCrossingLocalBlock k m)

theorem firstCrossingConditionedTensor_l2_opNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℕ) :
    ‖firstCrossingConditionedTensor k m‖ =
      ((realScale k - 1) / realScale k) * squarefreeShearEta m := by
  have h := tensorFamily_l2_opNorm_of_hasTopEigenvalue
    (firstCrossingLocalBlock k m)
    (fun s => by
      cases s with
      | none => exact isHermitian_localComplementBlock k
      | some i => exact isHermitian_localDensityBlock (m i))
    (firstCrossingLocalNorm k m)
    (fun s => by
      cases s with
      | none => exact localComplementNorm_nonneg k
      | some i => exact (localShearEta_pos (m i)).le)
    (fun s => by
      cases s with
      | none => exact localComplementBlock_l2_opNorm k
      | some i => exact localDensityBlock_l2_opNorm (m i))
    (fun s => by
      cases s with
      | none => exact localComplementBlock_top_hasEigenvalue k
      | some i => exact localDensityBlock_plus_hasEigenvalue (m i))
  simpa [firstCrossingConditionedTensor, firstCrossingLocalNorm, Fintype.prod_option,
    squarefreeShearEta] using h

/-- Tensor in which every selected coordinate has been exposed to its negative rank-one branch. -/
def allComplementTensor
    {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ :=
  tensorFamily fun i => localComplementBlock (m i)

theorem allComplementTensor_l2_opNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) :
    ‖allComplementTensor m‖ = ∏ i, (realScale (m i) - 1) / realScale (m i) := by
  simpa [allComplementTensor] using tensorFamily_l2_opNorm_of_hasTopEigenvalue
    (fun i => localComplementBlock (m i))
    (fun i => isHermitian_localComplementBlock (m i))
    (fun i => (realScale (m i) - 1) / realScale (m i))
    (fun i => localComplementNorm_nonneg (m i))
    (fun i => localComplementBlock_l2_opNorm (m i))
    (fun i => localComplementBlock_top_hasEigenvalue (m i))

theorem squarefreeShearEta_firstCrossingSize
    {ι : Type*} [Fintype ι] (k : ℕ) (m : ι → ℕ) :
    squarefreeShearEta (firstCrossingSize k m) =
      localShearEta k * squarefreeShearEta m := by
  rw [squarefreeShearEta, Fintype.prod_option, squarefreeShearEta]
  rfl

theorem firstCrossingConditionedTensor_norm_ratio
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℕ) :
    ‖firstCrossingConditionedTensor k m‖ /
        ‖crossingDensity (firstCrossingSize k m)‖ =
      ((realScale k - 1) / realScale k) / localShearEta k := by
  rw [firstCrossingConditionedTensor_l2_opNorm, crossingDensity_l2_opNorm,
    squarefreeShearEta_firstCrossingSize]
  have hq := (squarefreeShearEta_pos m).ne'
  field_simp

theorem localComplementNorm_div_eta (k : ℕ) :
    ((realScale k - 1) / realScale k) / localShearEta k =
      (Real.sqrt (4 * realScale k - 3) - 1) / 2 := by
  have hp := (realScale_pos k).ne'
  have hs0 : 1 + Real.sqrt (4 * realScale k - 3) ≠ 0 := by
    have hs := Real.sqrt_nonneg (4 * realScale k - 3)
    linarith
  rw [localShearEta]
  field_simp
  calc
    (realScale k - 1) * 2 ^ 2 = 4 * (realScale k - 1) := by ring
    _ = Real.sqrt (4 * realScale k - 3) ^ 2 - 1 := by
      rw [localShearSqrt_sq]
      ring
    _ = (1 + Real.sqrt (4 * realScale k - 3)) *
        (Real.sqrt (4 * realScale k - 3) - 1) := by ring
    _ = (1 + Real.sqrt (realScale k * 4 - 3)) *
        (Real.sqrt (realScale k * 4 - 3) - 1) := by rw [mul_comm 4 (realScale k)]

theorem firstCrossingConditionedTensor_norm_ratio_eq_sqrt
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℕ) :
    ‖firstCrossingConditionedTensor k m‖ /
        ‖crossingDensity (firstCrossingSize k m)‖ =
      (Real.sqrt (4 * realScale k - 3) - 1) / 2 := by
  rw [firstCrossingConditionedTensor_norm_ratio, localComplementNorm_div_eta]

theorem matrixQuadraticForm_norm_le_l2_opNorm
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (z : n → ℂ) :
    ‖star z ⬝ᵥ (A *ᵥ z)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 z‖ ^ 2 := by
  have hpair : star z ⬝ᵥ (A *ᵥ z) =
      inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 (A *ᵥ z)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  rw [hpair]
  calc
    ‖inner ℂ (WithLp.toLp 2 z) (WithLp.toLp 2 (A *ᵥ z))‖ ≤
        ‖WithLp.toLp 2 z‖ * ‖WithLp.toLp 2 (A *ᵥ z)‖ := norm_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 z‖ * (‖A‖ * ‖WithLp.toLp 2 z‖) := by
      gcongr
      simpa using Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 z)
    _ = ‖A‖ * ‖WithLp.toLp 2 z‖ ^ 2 := by ring

theorem matrixQuadraticForm_norm_eq_of_eigenvector
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (z : n → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hz : A *ᵥ z = (c : ℂ) • z) :
    ‖star z ⬝ᵥ (A *ᵥ z)‖ = c * ‖WithLp.toLp 2 z‖ ^ 2 := by
  rw [hz]
  have hpair : star z ⬝ᵥ ((c : ℂ) • z) =
      inner ℂ (WithLp.toLp 2 z) ((c : ℂ) • WithLp.toLp 2 z) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct, mul_comm]
  rw [hpair, inner_smul_right, inner_self_eq_norm_sq_to_K]
  simp [Complex.norm_real, Real.norm_eq_abs, hc, pow_two]

theorem firstCrossingConditionedTensor_quadratic_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (m : ι → ℕ)
    (z : (∀ s, Fin (firstCrossingSize k m s + 2)) → ℂ) :
    ‖star z ⬝ᵥ (firstCrossingConditionedTensor k m *ᵥ z)‖ ≤
      ((realScale k - 1) / realScale k) * squarefreeShearEta m *
        ‖WithLp.toLp 2 z‖ ^ 2 := by
  simpa [firstCrossingConditionedTensor_l2_opNorm] using
    matrixQuadraticForm_norm_le_l2_opNorm (firstCrossingConditionedTensor k m) z

def firstCrossingTopLocalVector
    {ι : Type*} (k : ℕ) (m : ι → ℕ) :
    ∀ s, Fin (firstCrossingSize k m s + 2) → ℂ
  | none => fun a => localFrame k a 1
  | some i => localShearEigenvector (m i) (localShearEigenPlus (m i))

def firstCrossingTopVector
    {ι : Type*} [Fintype ι] (k : ℕ) (m : ι → ℕ) :
    (∀ s, Fin (firstCrossingSize k m s + 2)) → ℂ :=
  tensorVec (firstCrossingTopLocalVector k m)

theorem firstCrossingTopVector_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℕ) :
    firstCrossingTopVector k m ≠ 0 := by
  have hlocal : ∀ s, firstCrossingTopLocalVector k m s ≠ 0 := by
    intro s
    cases s with
    | none => exact localComplementVector_ne_zero k
    | some i => exact localShearEigenvector_ne_zero (m i) (localShearEigenPlus (m i))
  choose a ha using fun s => Function.ne_iff.mp (hlocal s)
  intro hzero
  have heval := congrFun hzero (fun s => a s)
  simp only [firstCrossingTopVector, tensorVec_apply, Pi.zero_apply] at heval
  exact (Finset.prod_ne_zero_iff.mpr fun s _ => ha s) heval

theorem firstCrossingConditionedTensor_top_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℕ) :
    firstCrossingConditionedTensor k m *ᵥ firstCrossingTopVector k m =
      ((((realScale k - 1) / realScale k) * squarefreeShearEta m : ℝ) : ℂ) •
        firstCrossingTopVector k m := by
  rw [firstCrossingConditionedTensor, firstCrossingTopVector, tensorFamily_mulVec]
  have hlocal :
      (fun s => firstCrossingLocalBlock k m s *ᵥ firstCrossingTopLocalVector k m s) =
        fun s => (firstCrossingLocalNorm k m s : ℂ) •
          firstCrossingTopLocalVector k m s := by
    funext s
    cases s with
    | none => exact localComplementBlock_eigenvector k
    | some i => exact localDensityBlock_plus_eigenvector (m i)
  rw [hlocal, tensorVec_smul, Fintype.prod_option]
  change (((((realScale k - 1) / realScale k : ℝ) : ℂ) *
      ∏ i, (localShearEta (m i) : ℂ))) • _ = _
  rw [squarefreeShearEta]
  push_cast
  rfl

theorem firstCrossingConditionedTensor_quadratic_bound_sharp
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (m : ι → ℕ) :
    ‖star (firstCrossingTopVector k m) ⬝ᵥ
        (firstCrossingConditionedTensor k m *ᵥ firstCrossingTopVector k m)‖ =
      ((realScale k - 1) / realScale k) * squarefreeShearEta m *
        ‖WithLp.toLp 2 (firstCrossingTopVector k m)‖ ^ 2 := by
  apply matrixQuadraticForm_norm_eq_of_eigenvector
  · exact mul_nonneg (localComplementNorm_nonneg k) (squarefreeShearEta_pos m).le
  · exact firstCrossingConditionedTensor_top_eigenvector k m

/-! ## Exact diagonal join -/

/-- Raw squarefree shear tensor `K_l = ⊗ K_p`. -/
def squarefreeShearTensor
    {ι : Type*} [Fintype ι] (m : ι → ℕ) :
    Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ :=
  tensorFamily fun i => localRawShearBlock (m i)

def squarefreeShearDiagonal
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (x : ∀ i, Fin (m i + 2)) : ℂ :=
  squarefreeShearTensor m x x

def squarefreeShearOffDiagonal
    {ι : Type*} [Fintype ι] (m : ι → ℕ) [DecidableEq (∀ i, Fin (m i + 2))] :
    Matrix (∀ i, Fin (m i + 2)) (∀ i, Fin (m i + 2)) ℂ :=
  fun x y => if x = y then 0 else squarefreeShearTensor m x y

theorem localRawShearBlock_diagonal (k : ℕ) (a : Fin (k + 2)) :
    localRawShearBlock k a a =
      2 * localScale k * (if a = 0 then 1 else 0) - 1 := by
  rw [localRawShearBlock, localShearKernel]
  ring

theorem squarefreeShearDiagonal_eq_prod
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (x : ∀ i, Fin (m i + 2)) :
    squarefreeShearDiagonal m x =
      ∏ i, (2 * localScale (m i) * (if x i = 0 then 1 else 0) - 1) := by
  rw [squarefreeShearDiagonal, squarefreeShearTensor, tensorFamily_apply]
  exact Finset.prod_congr rfl fun i _ => localRawShearBlock_diagonal (m i) (x i)

theorem squarefreeShearOffDiagonal_add_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) :
    squarefreeShearOffDiagonal m + Matrix.diagonal (squarefreeShearDiagonal m) =
      squarefreeShearTensor m := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [squarefreeShearOffDiagonal, squarefreeShearDiagonal]
  · simp [squarefreeShearOffDiagonal, hxy]

def squarefreeShearTensorScale {ι : Type*} [Fintype ι] (m : ι → ℕ) : ℝ :=
  ∏ i, realScale (m i) ^ 2

def squarefreeShearEigenvalue
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (s : ∀ _i : ι, Fin 2) : ℂ :=
  ∏ i, localShearEigenvalue (m i) (s i)

def squarefreeShearSpectralVector
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (s : ∀ _i : ι, Fin 2) :
    (∀ i, Fin (m i + 2)) → ℂ :=
  tensorVec fun i => localShearSpectralVector (m i) (s i)

theorem squarefreeShearSpectralVector_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (s : ∀ _i : ι, Fin 2) : squarefreeShearSpectralVector m s ≠ 0 := by
  classical
  have hlocal : ∀ i, localShearSpectralVector (m i) (s i) ≠ 0 := by
    intro i
    by_cases hsi : s i = 0
    · rw [localShearSpectralVector, if_pos hsi]
      exact
        localShearEigenvector_ne_zero (m i) (localShearEigenPlus (m i))
    · rw [localShearSpectralVector, if_neg hsi]
      exact
        localShearEigenvector_ne_zero (m i) (localShearEigenMinus (m i))
  choose a ha using fun i => Function.ne_iff.mp (hlocal i)
  intro hzero
  have heval := congrFun hzero (fun i => a i)
  simp only [squarefreeShearSpectralVector, tensorVec_apply, Pi.zero_apply] at heval
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => ha i) heval

theorem squarefreeShearTensor_mulVec_spectralVector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (s : ∀ _i : ι, Fin 2) :
    squarefreeShearTensor m *ᵥ squarefreeShearSpectralVector m s =
      squarefreeShearEigenvalue m s • squarefreeShearSpectralVector m s := by
  rw [squarefreeShearTensor, squarefreeShearSpectralVector, tensorFamily_mulVec]
  have hfamily :
      (fun i => localRawShearBlock (m i) *ᵥ localShearSpectralVector (m i) (s i)) =
        fun i => localShearEigenvalue (m i) (s i) • localShearSpectralVector (m i) (s i) := by
    funext i
    exact (localRawShearBlock_hasEigenvector (m i) (s i)).apply_eq_smul
  rw [hfamily, tensorVec_smul, squarefreeShearEigenvalue]

theorem card_squarefreeShearSpectralChoices
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Fintype.card (∀ _i : ι, Fin 2) = 2 ^ Fintype.card ι := by
  rw [Fintype.card_pi]
  simp

theorem squarefreeShearTensorScale_pos
    {ι : Type*} [Fintype ι] (m : ι → ℕ) : 0 < squarefreeShearTensorScale m :=
  Finset.prod_pos fun i _ => realScale_sq_pos (m i)

theorem squarefreeShearTensor_eq_smul_crossingDensity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ) :
    squarefreeShearTensor m =
      (((squarefreeShearTensorScale m : ℝ) : ℂ)) • crossingDensity m := by
  rw [squarefreeShearTensor, crossingDensity]
  have hfamily : (fun i => localRawShearBlock (m i)) =
      fun i => ((((realScale (m i)) ^ 2 : ℝ) : ℂ)) • localDensityBlock (m i) := by
    funext i
    exact localRawShearBlock_eq_smul_density (m i)
  rw [hfamily, tensorFamily_smul]
  congr 1
  rw [squarefreeShearTensorScale]
  push_cast
  rfl

theorem squarefreeShearTensor_inertia
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m : ι → ℕ) :
    hermPosIndex (squarefreeShearTensor m) = 2 ^ (Fintype.card ι - 1) ∧
      hermNegIndex (squarefreeShearTensor m) = 2 ^ (Fintype.card ι - 1) ∧
      hermNullIndex (squarefreeShearTensor m) =
        (∏ i, (m i + 2)) - 2 ^ Fintype.card ι := by
  have hnormalized := crossingDensity_inertia m
  have hposRaw : hermPosIndex (squarefreeShearTensor m) = 2 ^ (Fintype.card ι - 1) := by
    rw [squarefreeShearTensor_eq_smul_crossingDensity,
      posIndex_smul_pos (squarefreeShearTensorScale_pos m)]
    exact hnormalized.1
  have hnegRaw : hermNegIndex (squarefreeShearTensor m) = 2 ^ (Fintype.card ι - 1) := by
    rw [squarefreeShearTensor_eq_smul_crossingDensity,
      negIndex_smul_pos (squarefreeShearTensorScale_pos m)]
    exact hnormalized.2.1
  refine ⟨hposRaw, hnegRaw, ?_⟩
  have hHerm : (squarefreeShearTensor m).IsHermitian :=
    isHermitian_tensorFamily fun i => isHermitian_localRawShearBlock (m i)
  have hcomplete := posIndex_add_negIndex_add_nullIndex hHerm
  rw [hposRaw, hnegRaw, Fintype.card_pi] at hcomplete
  simp only [Fintype.card_fin] at hcomplete
  have hpow : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
    rw [hn, Nat.succ_sub_one, pow_succ]
    omega
  have htwice : 2 ^ (Fintype.card ι - 1) + 2 ^ (Fintype.card ι - 1) =
      2 * 2 ^ (Fintype.card ι - 1) := by omega
  rw [htwice, ← hpow] at hcomplete
  omega

theorem squarefreeShearTensor_rank
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (m : ι → ℕ) : (squarefreeShearTensor m).rank = 2 ^ Fintype.card ι := by
  have hHerm : (squarefreeShearTensor m).IsHermitian :=
    isHermitian_tensorFamily fun i => isHermitian_localRawShearBlock (m i)
  rw [rank_eq_posIndex_add_negIndex hHerm]
  have hI := squarefreeShearTensor_inertia m
  rw [hI.1, hI.2.1]
  have hpow : 2 ^ Fintype.card ι = 2 * 2 ^ (Fintype.card ι - 1) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
    rw [hn, Nat.succ_sub_one, pow_succ]
    omega
  rw [hpow]
  omega

end

end RHTower
