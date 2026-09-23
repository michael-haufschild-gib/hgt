import Mathlib
import GaloisForLFunctions.HTGeometry.EquivariantCausalizerClassification

/-!
# The positive cone and kernel fidelity of the equivariant causalizer

For real parameters the quadratic causalizer `q_{a,b}(X) = a XᴴX + b tr(XᴴX) I` has the explicit
quadratic form `a ‖Xv‖² + b ‖X‖²_F ‖v‖²`.  Cauchy–Schwarz gives `‖Xv‖² ≤ ‖X‖²_F ‖v‖²`, so the form
is nonnegative for every source exactly when `b ≥ 0` and `a + b ≥ 0`; the two extreme test data —
a single unit entry paired with the matching and with an orthogonal coordinate vector — show both
inequalities are necessary.

Within that cone, exact kernel fidelity `ker q(X) = ker X` forces `b = 0` and `a > 0`: an isotropic
term makes the causalizer invertible on a vector killed by `X`, and a vanishing scale makes it kill
a vector that `X` does not.  Conversely `q(X) = a XᴴX` with `a > 0` has exactly the kernel of `X`.
-/

namespace GaloisForLFunctions.EquivariantCausalizer

open Matrix
open scoped ComplexOrder

variable {r n : ℕ}

/-- The quadratic causalizer with real parameters. -/
noncomputable def causalizerForm (a b : ℝ) (X : Matrix (Fin r) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (a : ℂ) • (Xᴴ * X) + (b : ℂ) • ((Xᴴ * X).trace • (1 : Matrix (Fin n) (Fin n) ℂ))

theorem sum_rotate {M : Type*} [AddCommMonoid M] {α β γ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] (F : α → β → γ → M) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ a, ∑ b, F a b c := by
  calc (∑ a, ∑ b, ∑ c, F a b c) = ∑ a, ∑ c, ∑ b, F a b c :=
        Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = ∑ c, ∑ a, ∑ b, F a b c := Finset.sum_comm

theorem dotProduct_gram (X : Matrix (Fin r) (Fin n) ℂ) (v : Fin n → ℂ) :
    (star v) ⬝ᵥ ((Xᴴ * X) *ᵥ v) = ((∑ a, ‖(X *ᵥ v) a‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hL : (star v) ⬝ᵥ ((Xᴴ * X) *ᵥ v)
      = ∑ i, ∑ j, ∑ a, ((starRingEnd ℂ) (v i) * ((starRingEnd ℂ) (X a i) * X a j) * v j) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Pi.star_apply, RCLike.star_def, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ =>
      Finset.sum_congr rfl (fun a _ => by ring)))
  have hR : (∑ a, (starRingEnd ℂ) ((X *ᵥ v) a) * (X *ᵥ v) a)
      = ∑ a, ∑ i, ∑ j, ((starRingEnd ℂ) (v i) * ((starRingEnd ℂ) (X a i) * X a j) * v j) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hswap := sum_rotate (fun (i : Fin n) (j : Fin n) (a : Fin r) =>
    ((starRingEnd ℂ) (v i) * ((starRingEnd ℂ) (X a i) * X a j) * v j))
  rw [hL, hswap, ← hR]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem trace_gram (X : Matrix (Fin r) (Fin n) ℂ) :
    (Xᴴ * X).trace = ((∑ a, ∑ i, ‖X a i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  push_cast
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem dotProduct_one (v : Fin n → ℂ) :
    (star v) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) = ((∑ i, ‖v i‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring


theorem dotProduct_smul_mulVec (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    (star v) ⬝ᵥ ((c • M) *ᵥ v) = c * ((star v) ⬝ᵥ (M *ᵥ v)) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem causalizerForm_quadratic (a b : ℝ) (X : Matrix (Fin r) (Fin n) ℂ) (v : Fin n → ℂ) :
    (star v) ⬝ᵥ (causalizerForm a b X *ᵥ v)
      = ((a * (∑ p, ‖(X *ᵥ v) p‖ ^ (2 : ℕ))
          + b * (∑ p, ∑ i, ‖X p i‖ ^ (2 : ℕ)) * (∑ i, ‖v i‖ ^ (2 : ℕ)) : ℝ) : ℂ) := by
  rw [causalizerForm, Matrix.add_mulVec, dotProduct_add, dotProduct_smul_mulVec,
    dotProduct_smul_mulVec, dotProduct_smul_mulVec, dotProduct_gram, trace_gram, dotProduct_one]
  push_cast
  ring

theorem sum_norm_mulVec_sq_le (X : Matrix (Fin r) (Fin n) ℂ) (v : Fin n → ℂ) :
    (∑ p, ‖(X *ᵥ v) p‖ ^ (2 : ℕ)) ≤ (∑ p, ∑ i, ‖X p i‖ ^ (2 : ℕ)) * (∑ i, ‖v i‖ ^ (2 : ℕ)) := by
  have hrow : ∀ p, ‖(X *ᵥ v) p‖ ^ (2 : ℕ) ≤ (∑ i, ‖X p i‖ ^ (2 : ℕ)) * (∑ i, ‖v i‖ ^ (2 : ℕ)) := by
    intro p
    have h1 : ‖(X *ᵥ v) p‖ ≤ ∑ i, ‖X p i‖ * ‖v i‖ := by
      have : (X *ᵥ v) p = ∑ i, X p i * v i := rfl
      rw [this]
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl (fun i _ => norm_mul _ _)
    have h2 : (∑ i, ‖X p i‖ * ‖v i‖) ^ (2 : ℕ) ≤ (∑ i, ‖X p i‖ ^ (2 : ℕ)) * (∑ i, ‖v i‖ ^ (2 : ℕ)) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have h3 : (0:ℝ) ≤ ∑ i, ‖X p i‖ * ‖v i‖ :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    nlinarith [norm_nonneg ((X *ᵥ v) p)]
  calc (∑ p, ‖(X *ᵥ v) p‖ ^ (2 : ℕ))
      ≤ ∑ p, (∑ i, ‖X p i‖ ^ (2 : ℕ)) * (∑ i, ‖v i‖ ^ (2 : ℕ)) := Finset.sum_le_sum (fun p _ => hrow p)
    _ = (∑ p, ∑ i, ‖X p i‖ ^ (2 : ℕ)) * (∑ i, ‖v i‖ ^ (2 : ℕ)) := by rw [← Finset.sum_mul]

theorem isHermitian_causalizerForm (a b : ℝ) (X : Matrix (Fin r) (Fin n) ℂ) :
    (causalizerForm a b X).IsHermitian := by
  rw [causalizerForm, Matrix.IsHermitian]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
  rw [(Matrix.isHermitian_conjTranspose_mul_self X)]
  rw [trace_gram]
  simp [Complex.conj_ofReal]


/-- The test matrix with a single unit entry. -/
noncomputable def testMatrix (hr : 0 < r) (i : Fin n) : Matrix (Fin r) (Fin n) ℂ :=
  Matrix.single ⟨0, hr⟩ i 1

theorem sum_norm_testMatrix (hr : 0 < r) (i : Fin n) :
    (∑ p, ∑ k, ‖testMatrix hr i p k‖ ^ (2 : ℕ)) = 1 := by
  classical
  rw [Finset.sum_eq_single (⟨0, hr⟩ : Fin r)]
  · rw [Finset.sum_eq_single i]
    · simp [testMatrix]
    · intro k _ hk
      simp [testMatrix, Ne.symm hk]
    · intro hk
      exact absurd (Finset.mem_univ i) hk
  · intro p _ hp
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp [testMatrix, Ne.symm hp]
  · intro hp
    exact absurd (Finset.mem_univ (⟨0, hr⟩ : Fin r)) hp

theorem testMatrix_mulVec (hr : 0 < r) (i : Fin n) (v : Fin n → ℂ) (p : Fin r) :
    (testMatrix hr i *ᵥ v) p = (if p = ⟨0, hr⟩ then v i else 0) := by
  classical
  simp only [Matrix.mulVec, dotProduct, testMatrix, Matrix.single_apply]
  rw [Finset.sum_eq_single i]
  · by_cases hp : p = (⟨0, hr⟩ : Fin r)
    · simp [hp]
    · simp [hp, Ne.symm hp]
  · intro k _ hk
    simp [Ne.symm hk]
  · intro hk
    exact absurd (Finset.mem_univ i) hk

theorem sum_norm_single_vec (i : Fin n) :
    (∑ k, ‖(Pi.single i (1 : ℂ) : Fin n → ℂ) k‖ ^ (2 : ℕ)) = 1 := by
  classical
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro hk
    exact absurd (Finset.mem_univ i) hk


/-- **Part II.**  The equivariant causalizer is positive for every source exactly on the closed
cone `b ≥ 0`, `a + b ≥ 0`. -/
theorem posSemidef_causalizerForm_iff (hr : 0 < r) (hn : 2 ≤ n) (a b : ℝ) :
    (∀ X : Matrix (Fin r) (Fin n) ℂ, (causalizerForm a b X).PosSemidef)
      ↔ (0 ≤ b ∧ 0 ≤ a + b) := by
  classical
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by
    intro hc
    have h2 := congrArg Fin.val hc
    simp only [hi0, hi1] at h2
    exact absurd h2 (by norm_num)
  constructor
  · intro hpos
    have hb : 0 ≤ b := by
      have h := ((Matrix.posSemidef_iff_dotProduct_mulVec).mp
        (hpos (testMatrix hr i0))).2 (Pi.single i1 (1 : ℂ) : Fin n → ℂ)
      rw [causalizerForm_quadratic, sum_norm_testMatrix hr i0, sum_norm_single_vec i1] at h
      have hzero : (∑ p, ‖(testMatrix hr i0 *ᵥ (Pi.single i1 (1 : ℂ) : Fin n → ℂ)) p‖ ^ (2 : ℕ)) = 0 := by
        refine Finset.sum_eq_zero (fun p _ => ?_)
        rw [testMatrix_mulVec]
        by_cases hp : p = (⟨0, hr⟩ : Fin r) <;> simp [hp, Ne.symm hne]
      rw [hzero] at h
      rw [Complex.zero_le_real] at h
      linarith
    refine ⟨hb, ?_⟩
    have h := ((Matrix.posSemidef_iff_dotProduct_mulVec).mp
      (hpos (testMatrix hr i0))).2 (Pi.single i0 (1 : ℂ) : Fin n → ℂ)
    rw [causalizerForm_quadratic, sum_norm_testMatrix hr i0, sum_norm_single_vec i0] at h
    have hone : (∑ p, ‖(testMatrix hr i0 *ᵥ (Pi.single i0 (1 : ℂ) : Fin n → ℂ)) p‖ ^ (2 : ℕ)) = 1 := by
      rw [Finset.sum_eq_single (⟨0, hr⟩ : Fin r)]
      · rw [testMatrix_mulVec]
        simp
      · intro p _ hp
        rw [testMatrix_mulVec, if_neg hp]
        simp
      · intro hp
        exact absurd (Finset.mem_univ (⟨0, hr⟩ : Fin r)) hp
    rw [hone] at h
    rw [Complex.zero_le_real] at h
    linarith
  · rintro ⟨hb, hab⟩ X
    refine (Matrix.posSemidef_iff_dotProduct_mulVec).mpr
      ⟨isHermitian_causalizerForm a b X, fun v => ?_⟩
    rw [causalizerForm_quadratic, Complex.zero_le_real]
    have hS : (0:ℝ) ≤ ∑ p, ‖(X *ᵥ v) p‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg (fun p _ => by positivity)
    have hT : (0:ℝ) ≤ ∑ p, ∑ i, ‖X p i‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun i _ => by positivity))
    have hN : (0:ℝ) ≤ ∑ i, ‖v i‖ ^ (2 : ℕ) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    have hCS := sum_norm_mulVec_sq_le X v
    rcases le_or_gt 0 a with ha | ha
    · have h1 : 0 ≤ a * (∑ p, ‖(X *ᵥ v) p‖ ^ (2 : ℕ)) := mul_nonneg ha hS
      have h2 : 0 ≤ b * (∑ p, ∑ i, ‖X p i‖ ^ (2 : ℕ)) * (∑ i, ‖v i‖ ^ (2 : ℕ)) :=
        mul_nonneg (mul_nonneg hb hT) hN
      linarith
    · nlinarith [mul_nonneg hT hN]


theorem single_mulVec (i j : Fin n) (c : ℂ) (v : Fin n → ℂ) (k : Fin n) :
    ((Matrix.single i j c) *ᵥ v) k = if k = i then c * v j else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hk : k = i
    · simp [hk]
    · simp [hk, Ne.symm hk]
  · intro l _ hl
    simp [Ne.symm hl]
  · intro hl
    exact absurd (Finset.mem_univ j) hl

theorem smul_mulVec_apply (c : ℂ) (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (k : Fin n) :
    ((c • M) *ᵥ v) k = c * ((M *ᵥ v) k) := by
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem gram_testMatrix (hr : 0 < r) (i : Fin n) :
    (testMatrix hr i)ᴴ * testMatrix hr i = Matrix.single i i (1 : ℂ) := by
  rw [testMatrix, Matrix.conjTranspose_single]
  rw [show (star (1 : ℂ)) = (1 : ℂ) by simp]
  rw [Matrix.single_mul_single_same]
  simp

theorem trace_single_diag (i : Fin n) : (Matrix.single i i (1 : ℂ)).trace = 1 := by
  classical
  rw [Matrix.trace, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro hk
    exact absurd (Finset.mem_univ i) hk

theorem trace_testMatrix_gram (hr : 0 < r) (i : Fin n) :
    ((testMatrix hr i)ᴴ * testMatrix hr i).trace = 1 := by
  classical
  rw [gram_testMatrix hr i, Matrix.trace, Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro hk
    exact absurd (Finset.mem_univ i) hk

/-- **Part III.**  Under positivity, exact kernel fidelity selects the pure Gram causalizer with
a positive scale. -/
theorem kernel_fidelity_iff (hr : 0 < r) (hn : 2 ≤ n) (a b : ℝ) (hb : 0 ≤ b) (hab : 0 ≤ a + b) :
    (∀ (X : Matrix (Fin r) (Fin n) ℂ) (v : Fin n → ℂ),
        X *ᵥ v = 0 ↔ (causalizerForm a b X) *ᵥ v = 0)
      ↔ (b = 0 ∧ 0 < a) := by
  classical
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by
    intro hc
    have h2 := congrArg Fin.val hc
    simp only [hi0, hi1] at h2
    exact absurd h2 (by norm_num)
  constructor
  · intro hfid
    have hXv0 : testMatrix hr i0 *ᵥ (Pi.single i1 (1 : ℂ) : Fin n → ℂ) = 0 := by
      funext p
      rw [testMatrix_mulVec]
      by_cases hp : p = (⟨0, hr⟩ : Fin r) <;> simp [hp, Ne.symm hne]
    have hform := (hfid (testMatrix hr i0) (Pi.single i1 (1 : ℂ) : Fin n → ℂ)).mp hXv0
    have hb0 : b = 0 := by
      have hentry := congrFun hform i1
      rw [causalizerForm, gram_testMatrix hr i0, trace_single_diag i0] at hentry
      simp only [Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply] at hentry
      rw [smul_mulVec_apply, smul_mulVec_apply, single_mulVec, if_neg (Ne.symm hne)] at hentry
      simp only [one_smul, Matrix.one_mulVec, mul_zero, zero_add] at hentry
      have hbC : (b : ℂ) = 0 := by
        simpa using hentry
      exact_mod_cast hbC
    refine ⟨hb0, ?_⟩
    have hane : a ≠ 0 := by
      intro ha0
      have hXv : testMatrix hr i0 *ᵥ (Pi.single i0 (1 : ℂ) : Fin n → ℂ) ≠ 0 := by
        intro hc
        have := congrFun hc (⟨0, hr⟩ : Fin r)
        rw [testMatrix_mulVec, if_pos rfl] at this
        simp at this
      refine hXv ((hfid (testMatrix hr i0) (Pi.single i0 (1 : ℂ) : Fin n → ℂ)).mpr ?_)
      funext k
      rw [causalizerForm, gram_testMatrix hr i0, trace_single_diag i0]
      simp only [Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply]
      rw [smul_mulVec_apply, smul_mulVec_apply, single_mulVec, ha0, hb0]
      simp
    rcases lt_or_gt_of_ne hane with hlt | hgt
    · exfalso
      rw [hb0] at hab
      linarith
    · exact hgt
  · rintro ⟨hb0, ha⟩ X v
    subst hb0
    have hform : causalizerForm a 0 X = (a : ℂ) • (Xᴴ * X) := by
      rw [causalizerForm]
      simp
    rw [hform]
    constructor
    · intro hXv
      funext k
      rw [smul_mulVec_apply]
      rw [show ((Xᴴ * X) *ᵥ v) = Xᴴ *ᵥ (X *ᵥ v) from (Matrix.mulVec_mulVec _ _ _).symm, hXv]
      simp
    · intro hzero
      have haC : (a : ℂ) ≠ 0 := by
        simpa using ne_of_gt ha
      have hzero' : (a : ℂ) • ((Xᴴ * X) *ᵥ v) = 0 := by
        funext k
        have := congrFun hzero k
        rw [smul_mulVec_apply] at this
        simpa using this
      rw [smul_eq_zero] at hzero'
      rcases hzero' with h | h
      · exact absurd h haC
      · have hquad : (star v) ⬝ᵥ ((Xᴴ * X) *ᵥ v) = 0 := by
          rw [h]
          simp
        rw [dotProduct_gram] at hquad
        have hsum : (∑ p, ‖(X *ᵥ v) p‖ ^ (2 : ℕ)) = 0 := by
          exact_mod_cast hquad
        funext p
        have hp : ‖(X *ᵥ v) p‖ ^ (2 : ℕ) = 0 := by
          refine le_antisymm ?_ (by positivity)
          rw [← hsum]
          exact Finset.single_le_sum
            (f := fun q => ‖(X *ᵥ v) q‖ ^ (2 : ℕ)) (fun q _ => by positivity) (Finset.mem_univ p)
        have : ‖(X *ᵥ v) p‖ = 0 := by
          nlinarith [norm_nonneg ((X *ᵥ v) p)]
        simpa using this


/-- **Part I, reality.**  If every diagonal value of the causalizer is Hermitian, both parameters
are real. -/
theorem coeffs_real_of_isHermitian (hr : 0 < r) (hn : 2 ≤ n) {a b : ℂ}
    (hherm : ∀ X : Matrix (Fin r) (Fin n) ℂ,
      ((a • (Xᴴ * X) + b • ((Xᴴ * X).trace • (1 : Matrix (Fin n) (Fin n) ℂ)))).IsHermitian) :
    (starRingEnd ℂ) a = a ∧ (starRingEnd ℂ) b = b := by
  classical
  set i0 : Fin n := ⟨0, by omega⟩ with hi0
  set i1 : Fin n := ⟨1, by omega⟩ with hi1
  have hne : i0 ≠ i1 := by
    intro hc
    have h2 := congrArg Fin.val hc
    simp only [hi0, hi1] at h2
    exact absurd h2 (by norm_num)
  have h := hherm (testMatrix hr i0)
  rw [gram_testMatrix hr i0, trace_single_diag i0] at h
  rw [Matrix.IsHermitian] at h
  have hb : (starRingEnd ℂ) b = b := by
    have hentry := congrFun (congrFun h i1) i1
    simp only [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.single_apply, Matrix.one_apply_eq, one_smul] at hentry
    rw [if_neg (fun hc : i0 = i1 ∧ i0 = i1 => hne hc.1)] at hentry
    simpa using hentry
  refine ⟨?_, hb⟩
  have hentry := congrFun (congrFun h i0) i0
  simp only [Matrix.conjTranspose_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.single_apply, Matrix.one_apply_eq, one_smul] at hentry
  have hsum : (starRingEnd ℂ) a + (starRingEnd ℂ) b = a + b := by
    simpa using hentry
  rw [hb] at hsum
  linear_combination hsum

theorem gram_left_invariant {U : Matrix (Fin r) (Fin r) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin r) ℂ) (X : Matrix (Fin r) (Fin n) ℂ) :
    (U * X)ᴴ * (U * X) = Xᴴ * X := by
  rw [Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, ← Matrix.mul_assoc]
  rw [show Xᴴ * Uᴴ * U = Xᴴ * (Uᴴ * U) from Matrix.mul_assoc _ _ _]
  rw [show Uᴴ * U = 1 from by
    have := (Matrix.mem_unitaryGroup_iff' ).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this]
  simp

theorem causalizerForm_left_invariant (a b : ℝ) {U : Matrix (Fin r) (Fin r) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin r) ℂ) (X : Matrix (Fin r) (Fin n) ℂ) :
    causalizerForm a b (U * X) = causalizerForm a b X := by
  rw [causalizerForm, causalizerForm, gram_left_invariant hU X]

theorem gram_right_covariant {V : Matrix (Fin n) (Fin n) ℂ}
    (X : Matrix (Fin r) (Fin n) ℂ) :
    (X * V)ᴴ * (X * V) = Vᴴ * (Xᴴ * X) * V := by
  rw [Matrix.conjTranspose_mul]
  simp [Matrix.mul_assoc]

theorem trace_conj_eq {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    (Vᴴ * A * V).trace = A.trace := by
  rw [Matrix.trace_mul_cycle]
  rw [show V * Vᴴ = 1 from by
    have := (Matrix.mem_unitaryGroup_iff).mp hV
    rwa [Matrix.star_eq_conjTranspose] at this]
  simp

theorem causalizerForm_right_covariant (a b : ℝ) {V : Matrix (Fin n) (Fin n) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin r) (Fin n) ℂ) :
    causalizerForm a b (X * V) = Vᴴ * causalizerForm a b X * V := by
  have hVV : Vᴴ * V = 1 := by
    have := (Matrix.mem_unitaryGroup_iff').mp hV
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [causalizerForm, causalizerForm, gram_right_covariant X, trace_conj_eq hV (Xᴴ * X)]
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · simp
  · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
    congr 2
    simp [hVV]

end GaloisForLFunctions.EquivariantCausalizer
