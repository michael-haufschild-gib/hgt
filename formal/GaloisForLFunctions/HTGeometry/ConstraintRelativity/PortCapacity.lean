import Mathlib

/-!
# Prime–infinity port capacity and the root-conormal law

The transgression matrix of `N` prime relations against `r` infinity ports has the normal form
`Ω = I_N + B Mᵀ`, so its rank is at least `N − r`: no fixed finite number of ports can make all
prime valuations descend, and a rank-one common anomaly needs `r ≥ N − 1`.  The bound is sharp.

The radial stabilizer of the relation ideal is all of `ℝ` exactly when the port weights cancel the
prime logarithms, and is trivial otherwise.

For one symmetric port the transgression is `Ω_N = I_N − N⁻¹ 𝟙𝟙ᵀ`, the projection onto the
mean-zero hyperplane: kernel the constants, image the type-`A_{N−1}` root space, rank `N − 1`.  The
two-prime half-density line is the `N = 2` accident of that family, not a global one-port law.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix Module

/-! ## The sharp port-capacity bound -/

section Capacity

variable {K : Type*} [Field K] {N r : ℕ}

/-- The transgression matrix `Ω = I_N + B Mᵀ`. -/
def transgression (B M : Matrix (Fin N) (Fin r) K) : Matrix (Fin N) (Fin N) K :=
  1 + B * Mᵀ

/-- The kernel of the transgression matrix lies in the image of the port matrix. -/
theorem ker_transgression_le (B M : Matrix (Fin N) (Fin r) K) :
    LinearMap.ker (transgression B M).mulVecLin ≤ LinearMap.range B.mulVecLin := by
  intro v hv
  have hz : transgression B M *ᵥ v = 0 := hv
  rw [transgression, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at hz
  have hX : B *ᵥ (Mᵀ *ᵥ v) = -v := eq_neg_of_add_eq_zero_right hz
  exact ⟨-(Mᵀ *ᵥ v), by rw [Matrix.mulVecLin_apply, Matrix.mulVec_neg, hX, neg_neg]⟩

/-- **Sharp port-capacity bound.**  `rank Ω ≥ N − r`. -/
theorem rank_transgression_ge (B M : Matrix (Fin N) (Fin r) K) :
    N - r ≤ (transgression B M).rank := by
  have hrn := (transgression B M).mulVecLin.finrank_range_add_finrank_ker
  have hker : finrank K (LinearMap.ker (transgression B M).mulVecLin) ≤ B.rank :=
    Submodule.finrank_mono (ker_transgression_le B M)
  have hB : B.rank ≤ r := by simpa using B.rank_le_width
  have hdim : finrank K (Fin N → K) = N := by simp
  rw [hdim] at hrn
  have hrank : (transgression B M).rank
      = finrank K (LinearMap.range (transgression B M).mulVecLin) := rfl
  omega

/-- **Sharpness.**  For every `r ≤ N` the bound `N − r` is attained by the standard inclusion
port matrices. -/
theorem exists_transgression_rank_eq (hr : r ≤ N) :
    ∃ B M : Matrix (Fin N) (Fin r) K, (transgression B M).rank = N - r := by
  classical
  set e : Fin r → Fin N := Fin.castLE hr with he
  have hemem : ∀ α : Fin r, ((e α : Fin N) : ℕ) = (α : ℕ) := fun α => rfl
  refine ⟨Matrix.of fun i α => if i = e α then (-1 : K) else 0,
    Matrix.of fun i α => if i = e α then (1 : K) else 0, ?_⟩
  have hmat : transgression (K := K) (Matrix.of fun i α => if i = e α then (-1 : K) else 0)
      (Matrix.of fun i α => if i = e α then (1 : K) else 0)
      = Matrix.diagonal (fun i : Fin N => if (i : ℕ) < r then (0 : K) else 1) := by
    ext i j
    simp only [transgression, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.diagonal_apply, Matrix.of_apply]
    by_cases hi : (i : ℕ) < r
    · have hie : i = e ⟨(i : ℕ), hi⟩ := by
        apply Fin.ext
        simp [he]
      rw [Finset.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin r)]
      · by_cases hij : i = j
        · subst hij
          simp [← hie, hi]
        · simp [← hie, hij, Ne.symm hij]
      · intro α _ hα
        have hne : i ≠ e α := by
          intro hEq
          apply hα
          apply Fin.ext
          have := congrArg (fun x : Fin N => (x : ℕ)) hEq
          simpa [he, Fin.castLE] using this.symm
        simp [hne]
      · intro hcon
        simp at hcon
    · rw [Finset.sum_eq_zero]
      · by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [hij]
      · intro α _
        have hne : i ≠ e α := by
          intro hEq
          apply hi
          have := congrArg (fun x : Fin N => (x : ℕ)) hEq
          rw [this]
          exact α.isLt
        simp [hne]
  rw [hmat, Matrix.rank_diagonal]
  have hcard : Fintype.card {i : Fin N // (if (i : ℕ) < r then (0 : K) else 1) ≠ 0} = N - r := by
    rw [Fintype.card_subtype]
    have hfil : (Finset.univ.filter fun i : Fin N => (if (i : ℕ) < r then (0 : K) else 1) ≠ 0)
        = Finset.univ.filter fun i : Fin N => r ≤ (i : ℕ) := by
      have hiff : ∀ i : Fin N, ((if (i : ℕ) < r then (0 : K) else 1) ≠ 0) ↔ r ≤ (i : ℕ) := by
        intro i
        by_cases hi : (i : ℕ) < r
        · rw [if_pos hi]
          simp only [ne_eq, not_true_eq_false, false_iff, not_le]
          exact hi
        · rw [if_neg hi]
          simp only [ne_eq, one_ne_zero, not_false_eq_true, true_iff]
          omega
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hiff i]
    rw [hfil]
    rcases eq_or_lt_of_le hr with heq | hlt
    · subst heq
      rw [Nat.sub_self, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _
      simp only [not_le]
      exact i.isLt
    · have hIci : (Finset.univ.filter fun i : Fin N => r ≤ (i : ℕ))
          = Finset.Ici (⟨r, hlt⟩ : Fin N) := by
        ext i
        simp [Fin.le_def]
      rw [hIci, Fin.card_Ici]
  simpa using hcard

end Capacity

/-! ## Radial stabilizer classification -/

section Stabilizer

/-- **Radial stabilizer classification.**  The relation ideal is stabilized by the whole radial
group exactly when the port weights cancel the prime logarithms; otherwise only by the identity. -/
theorem radial_stabilizer {N : ℕ} (w : Fin N → ℝ) :
    {c : ℝ | ∀ i, Real.exp (c * w i) - 1 = 0} = (if w = 0 then Set.univ else {0}) := by
  by_cases hw : w = 0
  · subst hw
    simp
  · rw [if_neg hw]
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hc
      by_contra hcne
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
        by_contra hcon
        exact hw (funext fun i => by
          by_contra hne
          exact hcon ⟨i, hne⟩)
      have hexp : Real.exp (c * w i) = 1 := by
        have := hc i
        linarith
      have hzero : c * w i = 0 := (Real.exp_eq_one_iff _).1 hexp
      rcases mul_eq_zero.1 hzero with h | h
      · exact hcne h
      · exact hi h
    · intro hc i
      subst hc
      simp

end Stabilizer

/-! ## The symmetric one-port transgression -/

section OnePort

variable {N : ℕ}

/-- The all-ones matrix. -/
def onesMat (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Matrix.of fun _ _ => 1

/-- The symmetric one-port transgression `I_N + b 𝟙𝟙ᵀ`. -/
def symTransgression (N : ℕ) (b : ℝ) : Matrix (Fin N) (Fin N) ℝ := 1 + b • onesMat N

/-- The total-mass functional. -/
def sumForm (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ i, v i
  map_add' := by intro a b; simp [Finset.sum_add_distrib]
  map_smul' := by intro c a; simp [Finset.mul_sum]

@[simp]
theorem sumForm_apply (v : Fin N → ℝ) : sumForm N v = ∑ i, v i := rfl

@[simp]
theorem symTransgression_mulVec (b : ℝ) (v : Fin N → ℝ) (i : Fin N) :
    (symTransgression N b *ᵥ v) i = v i + b * ∑ j, v j := by
  have hentry : ∀ x, (symTransgression N b) i x = (if i = x then (1 : ℝ) else 0) + b := by
    intro x
    simp [symTransgression, onesMat, Matrix.one_apply]
  simp only [Matrix.mulVec, dotProduct, hentry, add_mul, Finset.sum_add_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ← Finset.mul_sum]

/-- On the all-ones vector the transgression acts by `1 + N b`. -/
theorem symTransgression_ones (b : ℝ) (i : Fin N) :
    (symTransgression N b *ᵥ (fun _ => (1 : ℝ))) i = 1 + N * b := by
  rw [symTransgression_mulVec]
  simp
  ring

/-- On mean-zero vectors the transgression is the identity. -/
theorem symTransgression_meanZero (b : ℝ) (v : Fin N → ℝ) (hv : ∑ j, v j = 0) :
    symTransgression N b *ᵥ v = v := by
  funext i
  rw [symTransgression_mulVec, hv]
  ring

/-- Away from the minimizing weight the transgression is injective, hence of full rank. -/
theorem symTransgression_injective (b : ℝ) (hb : 1 + N * b ≠ 0) :
    Function.Injective (symTransgression N b).mulVecLin := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hz : ∀ i, v i + b * ∑ j, v j = 0 := by
    intro i
    have h := congrFun hv i
    rw [Matrix.mulVecLin_apply, symTransgression_mulVec] at h
    simpa using h
  have hsum : (1 + N * b) * ∑ j, v j = 0 := by
    have hs : ∑ i, (v i + b * ∑ j, v j) = 0 := by
      rw [Finset.sum_eq_zero]
      intro i _
      exact hz i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hs
    linarith
  have hs0 : ∑ j, v j = 0 := by
    rcases mul_eq_zero.1 hsum with h | h
    · exact absurd h hb
    · exact h
  funext i
  have := hz i
  rw [hs0] at this
  simpa using this

/-- **The minimal-rank symmetric port.**  At `b = −1/N` the transgression kills exactly the
constants. -/
theorem symTransgression_ker_eq_span (hN : 0 < N) :
    LinearMap.ker (symTransgression N (-1 / N)).mulVecLin
      = Submodule.span ℝ {(fun _ => (1 : ℝ) : Fin N → ℝ)} := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine le_antisymm ?_ ?_
  · intro v hv
    have hz : ∀ i, v i + (-1 / N) * ∑ j, v j = 0 := by
      intro i
      have h := congrFun hv i
      rw [Matrix.mulVecLin_apply, symTransgression_mulVec] at h
      simpa using h
    refine Submodule.mem_span_singleton.2 ⟨(1 / N) * ∑ j, v j, ?_⟩
    funext i
    have hi := hz i
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    field_simp at hi ⊢
    linarith
  · rw [Submodule.span_le]
    rintro _ rfl
    have hval : symTransgression N (-1 / N) *ᵥ (fun _ => (1 : ℝ)) = 0 := by
      funext i
      rw [symTransgression_ones]
      have hz : (N : ℝ) * (-1 / N) = -1 := by field_simp
      rw [hz]
      norm_num
    exact hval

/-- **The image is the type-`A_{N−1}` root space.**  The minimal-rank symmetric transgression has
mean-zero image, and is the identity there. -/
theorem symTransgression_range_eq_meanZero (hN : 0 < N) :
    LinearMap.range (symTransgression N (-1 / N)).mulVecLin = LinearMap.ker (sumForm N) := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, sumForm_apply]
    have hexp : ∀ i, (symTransgression N (-1 / N) *ᵥ v) i = v i + (-1 / N) * ∑ j, v j :=
      fun i => symTransgression_mulVec _ _ i
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  · intro v hv
    have hsum : ∑ i, v i = 0 := hv
    exact ⟨v, by rw [Matrix.mulVecLin_apply, symTransgression_meanZero _ v hsum]⟩

/-- The rank of the minimal-rank symmetric transgression is `N − 1`. -/
theorem rank_symTransgression (hN : 0 < N) :
    (symTransgression N (-1 / N)).rank = N - 1 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hrn := (symTransgression N (-1 / N)).mulVecLin.finrank_range_add_finrank_ker
  rw [symTransgression_ker_eq_span hN] at hrn
  have hspan : finrank ℝ (Submodule.span ℝ {(fun _ => (1 : ℝ) : Fin N → ℝ)}) = 1 := by
    rw [finrank_span_singleton]
    intro hcon
    have := congrFun hcon ⟨0, hN⟩
    simp at this
  rw [hspan] at hrn
  have hdim : finrank ℝ (Fin N → ℝ) = N := by simp
  rw [hdim] at hrn
  have hrank : (symTransgression N (-1 / N)).rank
      = finrank ℝ (LinearMap.range (symTransgression N (-1 / N)).mulVecLin) := rfl
  omega

/-- **The two-prime half-density line.**  For `N = 2` the minimal symmetric transgression is the
antisymmetric half-density projection. -/
theorem symTransgression_two :
    symTransgression 2 (-1 / 2) = !![1 / 2, -(1 / 2); -(1 / 2), 1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [symTransgression, onesMat] <;> norm_num

end OnePort

end HTGeometry.ConstraintRelativity
