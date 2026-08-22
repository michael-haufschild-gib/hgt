import GaloisForLFunctions.HTGeometry.HaynsworthInertia

/-!
# Iterated Kronecker products of matrix families and their inertia

For a finite family of rectangular matrices `M i : Matrix (α i) (β i) ℂ` the *tensor family*

`tensorFamily M x y = ∏ i, M i (x i) (y i)`

is the iterated Kronecker product on the product index types.  It is multiplicative, commutes with
the conjugate transpose, sends diagonal families to diagonal matrices, and therefore has inertia
determined by the products of the local eigenvalues.
-/

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace GaloisForLFunctions.HTGeometry

open Matrix

section Basic

variable {ι : Type*} [Fintype ι] {α β γ : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]

/-- The iterated Kronecker product of a family of matrices. -/
def tensorFamily (M : ∀ i, Matrix (α i) (β i) ℂ) : Matrix (∀ i, α i) (∀ i, β i) ℂ :=
  Matrix.of fun x y => ∏ i, M i (x i) (y i)

omit [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] in
@[simp] theorem tensorFamily_apply (M : ∀ i, Matrix (α i) (β i) ℂ) (x : ∀ i, α i) (y : ∀ i, β i) :
    tensorFamily M x y = ∏ i, M i (x i) (y i) := rfl

omit [∀ i, Fintype (α i)] [∀ i, Fintype (γ i)] in
theorem tensorFamily_mul [DecidableEq ι] (M : ∀ i, Matrix (α i) (β i) ℂ)
    (N : ∀ i, Matrix (β i) (γ i) ℂ) :
    tensorFamily M * tensorFamily N = tensorFamily fun i => M i * N i := by
  classical
  ext x y
  rw [Matrix.mul_apply]
  simp only [tensorFamily_apply, Matrix.mul_apply]
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (β i)))
    (fun i b => M i (x i) b * N i b (y i)), Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun z _ => (Finset.prod_mul_distrib).symm

omit [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] in
theorem tensorFamily_conjTranspose (M : ∀ i, Matrix (α i) (β i) ℂ) :
    (tensorFamily M)ᴴ = tensorFamily fun i => (M i)ᴴ := by
  ext x y
  simp [Matrix.conjTranspose_apply]

omit [∀ i, Fintype (α i)] in
theorem tensorFamily_one [DecidableEq ι] [∀ i, DecidableEq (α i)] :
    tensorFamily (fun i => (1 : Matrix (α i) (α i) ℂ)) = 1 := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [Matrix.one_apply_eq]
  · have : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := this
    rw [Matrix.one_apply_ne hxy]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [Matrix.one_apply_ne hi]

omit [∀ i, Fintype (α i)] in
theorem tensorFamily_diagonal [∀ i, DecidableEq (α i)] [DecidableEq ι] (μ : ∀ i, α i → ℂ) :
    tensorFamily (fun i => diagonal (μ i)) = diagonal fun x => ∏ i, μ i (x i) := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst hxy
    simp [Matrix.diagonal_apply_eq]
  · have : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := this
    rw [Matrix.diagonal_apply_ne _ hxy]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)

theorem isUnit_tensorFamily [DecidableEq ι] [∀ i, DecidableEq (α i)]
    {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, IsUnit (M i)) : IsUnit (tensorFamily M) := by
  classical
  choose N hMN using fun i => (h i).exists_right_inv
  have hleft : ∀ i, N i * M i = 1 := fun i => mul_eq_one_comm.mp (hMN i)
  refine ⟨⟨tensorFamily M, tensorFamily N, ?_, ?_⟩, rfl⟩
  · rw [tensorFamily_mul,
      show (fun i => M i * N i) = (fun i => (1 : Matrix (α i) (α i) ℂ)) from funext hMN,
      tensorFamily_one]
  · rw [tensorFamily_mul,
      show (fun i => N i * M i) = (fun i => (1 : Matrix (α i) (α i) ℂ)) from funext hleft,
      tensorFamily_one]

omit [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)] in
theorem isHermitian_tensorFamily {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, (M i).IsHermitian) :
    (tensorFamily M).IsHermitian := by
  rw [Matrix.IsHermitian, tensorFamily_conjTranspose]
  congr 1
  exact funext fun i => (h i).eq

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]

/-- **Inertia of an iterated Kronecker product.**  The positive index counts the product index
points at which the product of the local eigenvalues is positive. -/
theorem posIndex_tensorFamily {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, (M i).IsHermitian) :
    hermPosIndex (tensorFamily M)
      = ({x : ∀ i, α i | 0 < ∏ i, (h i).eigenvalues (x i)} : Finset (∀ i, α i)).card := by
  classical
  choose S hS hcongr using fun i => exists_congr_diagonal (h i)
  have hdec : tensorFamily M
      = (tensorFamily S)ᴴ *
        (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ)) *
        tensorFamily S := by
    have hdiag : (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ))
        = tensorFamily fun i => diagonal (fun a => (((h i).eigenvalues a : ℝ) : ℂ)) := by
      rw [tensorFamily_diagonal]
      congr 1
      funext x
      push_cast
      rfl
    rw [hdiag, tensorFamily_conjTranspose, tensorFamily_mul, tensorFamily_mul]
    congr 1
    funext i
    exact (hcongr i).symm
  rw [hdec, posIndex_conjugate _ (isUnit_tensorFamily hS), posIndex_diagonal]

/-- **Negative index of an iterated Kronecker product.** -/
theorem negIndex_tensorFamily {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, (M i).IsHermitian) :
    hermNegIndex (tensorFamily M)
      = ({x : ∀ i, α i | ∏ i, (h i).eigenvalues (x i) < 0} : Finset (∀ i, α i)).card := by
  classical
  choose S hS hcongr using fun i => exists_congr_diagonal (h i)
  have hdec : tensorFamily M
      = (tensorFamily S)ᴴ *
        (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ)) *
        tensorFamily S := by
    have hdiag : (diagonal fun x : ∀ i, α i => ((∏ i, (h i).eigenvalues (x i) : ℝ) : ℂ))
        = tensorFamily fun i => diagonal (fun a => (((h i).eigenvalues a : ℝ) : ℂ)) := by
      rw [tensorFamily_diagonal]
      congr 1
      funext x
      push_cast
      rfl
    rw [hdiag, tensorFamily_conjTranspose, tensorFamily_mul, tensorFamily_mul]
    congr 1
    funext i
    exact (hcongr i).symm
  rw [hdec, negIndex_conjugate _ (isUnit_tensorFamily hS), negIndex_diagonal]

end Basic

section Scaling

variable {ι : Type*} [Fintype ι] {α β : ι → Type*}
  [∀ i, Fintype (α i)] [∀ i, Fintype (β i)]

omit [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] in
/-- Scaling each factor scales the tensor family by the product of the scalars. -/
theorem tensorFamily_smul (c : ι → ℂ) (M : ∀ i, Matrix (α i) (β i) ℂ) :
    tensorFamily (fun i => c i • M i) = (∏ i, c i) • tensorFamily M := by
  ext x y
  simp only [tensorFamily_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]

variable [DecidableEq ι] [∀ i, DecidableEq (α i)]

theorem tensorFamily_inv {M : ∀ i, Matrix (α i) (α i) ℂ} (h : ∀ i, IsUnit (M i)) :
    (tensorFamily M)⁻¹ = tensorFamily fun i => (M i)⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [tensorFamily_mul]
  have hfun : (fun i => M i * (M i)⁻¹) = fun i => (1 : Matrix (α i) (α i) ℂ) := by
    funext i
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (h i))
  rw [hfun, tensorFamily_one]

end Scaling

section SignCount

variable {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)] [DecidableEq ι]

/-- The two-valued sign of a real number. -/
noncomputable def rsign (r : ℝ) : ℝ := if 0 < r then 1 else -1

theorem rsign_eq_one_or (r : ℝ) : rsign r = 1 ∨ rsign r = -1 := by
  rw [rsign]
  by_cases h : 0 < r <;> simp [h]

theorem rsign_mul_abs {r : ℝ} (h : r ≠ 0) : rsign r * |r| = r := by
  rw [rsign]
  by_cases hpos : 0 < r
  · rw [if_pos hpos, one_mul, abs_of_pos hpos]
  · rw [if_neg hpos, abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) h)]
    ring

theorem sum_prod_eq_prod_sum (s : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, s i (x i)) = ∏ i, ∑ a, s i a := by
  classical
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) (fun i a => s i a),
    Fintype.piFinset_univ]

omit [∀ i, Fintype (α i)] [DecidableEq ι] in
/-- The product of two-valued signs is two-valued. -/
theorem prod_rsign_eq_one_or (μ : ∀ i, α i → ℝ) (x : ∀ i, α i) :
    (∏ i, rsign (μ i (x i))) = 1 ∨ (∏ i, rsign (μ i (x i))) = -1 := by
  classical
  refine Finset.prod_induction _ (fun y => y = 1 ∨ y = -1) ?_ (Or.inl rfl) ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  · intro i _
    exact rsign_eq_one_or _

omit [∀ i, Fintype (α i)] [DecidableEq ι] in
theorem prod_pos_iff_prod_rsign (μ : ∀ i, α i → ℝ) (hμ : ∀ i a, μ i a ≠ 0) (x : ∀ i, α i) :
    0 < (∏ i, μ i (x i)) ↔ (∏ i, rsign (μ i (x i))) = 1 := by
  classical
  have hsplit : (∏ i, μ i (x i))
      = (∏ i, rsign (μ i (x i))) * (∏ i, |μ i (x i)|) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (rsign_mul_abs (hμ i (x i))).symm
  have habs : 0 < ∏ i, |μ i (x i)| :=
    Finset.prod_pos fun i _ => abs_pos.mpr (hμ i (x i))
  constructor
  · intro hpos
    rcases prod_rsign_eq_one_or μ x with h | h
    · exact h
    · rw [hsplit, h] at hpos
      nlinarith
  · intro h
    rw [hsplit, h, one_mul]
    exact habs

theorem sum_two_valued {σ : Type*} [Fintype σ] (g : σ → ℝ) (p : σ → Prop) [DecidablePred p]
    (h1 : ∀ a, p a → g a = 1) (h2 : ∀ a, ¬ p a → g a = -1) :
    (∑ a, g a)
      = (({a | p a} : Finset σ).card : ℝ) - (({a | ¬ p a} : Finset σ).card : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ p g]
  have hA : (∑ a ∈ Finset.univ.filter p, g a) = (({a | p a} : Finset σ).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun a ha => h1 a (Finset.mem_filter.mp ha).2), Finset.sum_const,
      nsmul_eq_mul, mul_one]
  have hB : (∑ a ∈ Finset.univ.filter (fun a => ¬ p a), g a)
      = -(({a | ¬ p a} : Finset σ).card : ℝ) := by
    rw [Finset.sum_congr rfl (fun a ha => h2 a (Finset.mem_filter.mp ha).2), Finset.sum_const,
      nsmul_eq_mul, mul_neg_one]
  rw [hA, hB]
  ring

/-- **The signed count of a tensor family of nonvanishing real weights.** -/
theorem card_pos_sub_card_neg_tensor (μ : ∀ i, α i → ℝ) (hμ : ∀ i a, μ i a ≠ 0) :
    ((({x : ∀ i, α i | 0 < ∏ i, μ i (x i)} : Finset (∀ i, α i)).card : ℝ)
        - (({x : ∀ i, α i | ∏ i, μ i (x i) < 0} : Finset (∀ i, α i)).card : ℝ))
      = ∏ i, ((({a | 0 < μ i a} : Finset (α i)).card : ℝ)
              - (({a | μ i a < 0} : Finset (α i)).card : ℝ)) := by
  classical
  have hlocal : ∀ i, (∑ a, rsign (μ i a))
      = (({a | 0 < μ i a} : Finset (α i)).card : ℝ)
        - (({a | μ i a < 0} : Finset (α i)).card : ℝ) := by
    intro i
    have h := sum_two_valued (fun a => rsign (μ i a)) (fun a => 0 < μ i a)
      (fun a ha => by rw [rsign, if_pos ha]) (fun a ha => by rw [rsign, if_neg ha])
    have hset : ({a | ¬ (0 < μ i a)} : Finset (α i)) = ({a | μ i a < 0} : Finset (α i)) := by
      refine Finset.filter_congr fun a _ => ?_
      exact ⟨fun hn => lt_of_le_of_ne (not_lt.mp hn) (hμ i a), fun hn => not_lt.mpr hn.le⟩
    rw [h, hset]
  have hglobal : (∑ x : (∀ i, α i), ∏ i, rsign (μ i (x i)))
      = (({x : ∀ i, α i | 0 < ∏ i, μ i (x i)} : Finset (∀ i, α i)).card : ℝ)
        - (({x : ∀ i, α i | ∏ i, μ i (x i) < 0} : Finset (∀ i, α i)).card : ℝ) := by
    have hne : ∀ x : (∀ i, α i), (∏ i, μ i (x i)) ≠ 0 :=
      fun x => Finset.prod_ne_zero_iff.mpr fun i _ => hμ i (x i)
    have h := sum_two_valued (fun x : (∀ i, α i) => ∏ i, rsign (μ i (x i)))
      (fun x => 0 < ∏ i, μ i (x i))
      (fun x hx => (prod_pos_iff_prod_rsign μ hμ x).mp hx)
      (fun x hx => by
        rcases prod_rsign_eq_one_or μ x with h | h
        · exact absurd ((prod_pos_iff_prod_rsign μ hμ x).mpr h) hx
        · exact h)
    have hset : ({x : ∀ i, α i | ¬ (0 < ∏ i, μ i (x i))} : Finset (∀ i, α i))
        = ({x : ∀ i, α i | ∏ i, μ i (x i) < 0} : Finset (∀ i, α i)) := by
      refine Finset.filter_congr fun x _ => ?_
      exact ⟨fun hn => lt_of_le_of_ne (not_lt.mp hn) (hne x), fun hn => not_lt.mpr hn.le⟩
    rw [h, hset]
  rw [← hglobal, sum_prod_eq_prod_sum (fun i a => rsign (μ i a))]
  exact Finset.prod_congr rfl fun i _ => hlocal i

end SignCount

section Trace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The trace of an iterated Kronecker product is the product of the local traces. -/
theorem trace_tensorFamily (M : ∀ i, Matrix (α i) (α i) ℂ) :
    Matrix.trace (tensorFamily M) = ∏ i, Matrix.trace (M i) := by
  classical
  simp only [Matrix.trace, Matrix.diag, tensorFamily_apply]
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) (fun i a => M i a a),
    Fintype.piFinset_univ]

end Trace

section TensorVec

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The tensor product of a family of local vectors. -/
def tensorVec (v : ∀ i, α i → ℂ) : (∀ i, α i) → ℂ := fun x => ∏ i, v i (x i)

omit [DecidableEq ι] [∀ i, Fintype (α i)] in
@[simp] theorem tensorVec_apply (v : ∀ i, α i → ℂ) (x : ∀ i, α i) :
    tensorVec v x = ∏ i, v i (x i) := rfl

omit [DecidableEq ι] [∀ i, Fintype (α i)] in
theorem tensorVec_smul (c : ι → ℂ) (v : ∀ i, α i → ℂ) :
    tensorVec (fun i => c i • v i) = (∏ i, c i) • tensorVec v := by
  funext x
  simp only [tensorVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ i, Fintype (α i)] in
theorem tensorVec_eq_zero (v : ∀ i, α i → ℂ) (i₀ : ι) (h : v i₀ = 0) : tensorVec v = 0 := by
  funext x
  simp only [tensorVec_apply, Pi.zero_apply]
  refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
  rw [h]
  rfl

theorem tensorFamily_mulVec (M : ∀ i, Matrix (α i) (α i) ℂ) (v : ∀ i, α i → ℂ) :
    tensorFamily M *ᵥ tensorVec v = tensorVec fun i => M i *ᵥ v i := by
  classical
  funext x
  rw [Matrix.mulVec, dotProduct]
  simp only [tensorFamily_apply, tensorVec_apply, Matrix.mulVec, dotProduct]
  rw [Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i)))
    (fun i a => M i (x i) a * v i a), Fintype.piFinset_univ]
  exact Finset.sum_congr rfl fun y _ => (Finset.prod_mul_distrib).symm

end TensorVec

end GaloisForLFunctions.HTGeometry
