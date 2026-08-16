import GaloisForLFunctions.RHTower.XiZerosInfinite

/-!
# The reciprocal seam measure has infinite zeroth moment

In the reciprocal seam coordinate `y_ρ = -(ρ - 1/2)⁻²` the moments

`T k = ∑ ρ, m ρ * y ρ ^ k`

are absolutely convergent for every `k ≥ 1`, while the formal zeroth moment `T 0 = ∑ ρ, m ρ`
diverges: the completed zeta has infinitely many zeros.

Consequently the unshifted Hankel tower `[T (i + j)]` beginning at `T 0` is not an ordinary finite
Stieltjes moment matrix for the full zero divisor; the ordinary finite moment object is the shifted
tower `[T (i + j + 1)]`.
-/

noncomputable section

namespace RHTower

open scoped BigOperators

/-- The reciprocal seam coordinate of a Xi zero copy. -/
def reciprocalSeamAtom (q : XiZeroCopy) : ℂ := -(((q.1 : ℂ) - 1 / 2) ^ 2)⁻¹

theorem reciprocalSeamAtom_eq (q : XiZeroCopy) :
    reciprocalSeamAtom q = (xiSpectralPoint q ^ 2)⁻¹ := by
  rw [reciprocalSeamAtom, xiSpectralPoint]
  have hI : ((-Complex.I) ^ 2 : ℂ) = -1 := by
    rw [neg_pow, Complex.I_sq]
    norm_num
  rw [mul_pow, hI]
  field_simp

theorem norm_reciprocalSeamAtom (q : XiZeroCopy) :
    ‖reciprocalSeamAtom q‖ = 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  rw [reciprocalSeamAtom_eq, norm_inv, norm_pow, one_div]

/-- The reciprocal seam weights are summable: this is the genus-one convergence condition of the
completed zeta divisor. -/
theorem summable_norm_reciprocalSeamAtom :
    Summable (fun q : XiZeroCopy => ‖reciprocalSeamAtom q‖) := by
  refine xiSpectralPoint_inv_sq_summable.congr fun q => ?_
  rw [norm_reciprocalSeamAtom]

/-- Every reciprocal seam weight is bounded by the total seam mass. -/
theorem norm_reciprocalSeamAtom_le (q : XiZeroCopy) :
    ‖reciprocalSeamAtom q‖ ≤ ∑' p : XiZeroCopy, ‖reciprocalSeamAtom p‖ :=
  summable_norm_reciprocalSeamAtom.le_tsum q fun _ _ => norm_nonneg _

/-- **Positive-order moments converge absolutely.** -/
theorem summable_norm_reciprocalSeamAtom_pow {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun q : XiZeroCopy => ‖reciprocalSeamAtom q ^ k‖) := by
  set M : ℝ := ∑' p : XiZeroCopy, ‖reciprocalSeamAtom p‖ with hM
  have hMnonneg : 0 ≤ M := tsum_nonneg fun p => norm_nonneg _
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (summable_norm_reciprocalSeamAtom.mul_left (M ^ (k - 1)))
  have hle : ‖reciprocalSeamAtom q‖ ≤ M := norm_reciprocalSeamAtom_le q
  have hpow : ‖reciprocalSeamAtom q‖ ^ (k - 1) ≤ M ^ (k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hle (k - 1)
  have hsplit : ‖reciprocalSeamAtom q ^ k‖ =
      ‖reciprocalSeamAtom q‖ ^ (k - 1) * ‖reciprocalSeamAtom q‖ := by
    rw [norm_pow, ← pow_succ]
    congr 1
    omega
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hpow (norm_nonneg _)

/-- The complex positive-order moments are summable. -/
theorem summable_reciprocalSeamAtom_pow {k : ℕ} (hk : 1 ≤ k) :
    Summable (fun q : XiZeroCopy => reciprocalSeamAtom q ^ k) :=
  Summable.of_norm (summable_norm_reciprocalSeamAtom_pow hk)

instance : Infinite XiZeroCopy := by
  have hbase : Infinite XiDivisorSupport :=
    Set.infinite_coe_iff.mpr xiDivisorSupport_infinite
  refine Infinite.of_injective
    (fun ρ : XiDivisorSupport => (⟨ρ, ⟨0, ?_⟩⟩ : XiZeroCopy)) ?_
  · have hpos := xi_divisor_pos_on_support ρ
    omega
  · intro a b h
    exact congrArg Sigma.fst h

/-- **The zeroth moment diverges.**  Counting every divisor copy with weight one is not summable,
because the completed zeta has infinitely many zeros. -/
theorem not_summable_reciprocalSeamZerothMoment :
    ¬ Summable (fun _ : XiZeroCopy => (1 : ℝ)) := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (∑' _ : XiZeroCopy, (1 : ℝ))
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq XiZeroCopy n
  have hsum : (∑ _q ∈ s, (1 : ℝ)) ≤ ∑' _q : XiZeroCopy, (1 : ℝ) :=
    h.sum_le_tsum s fun _ _ => zero_le_one
  rw [Finset.sum_const, hs, nsmul_eq_mul, mul_one] at hsum
  linarith

/-- The seam moment tower: absolute convergence exactly from order one. -/
theorem reciprocalSeamMoment_dichotomy :
    (¬ Summable (fun _ : XiZeroCopy => (1 : ℝ))) ∧
      ∀ k : ℕ, 1 ≤ k → Summable (fun q : XiZeroCopy => reciprocalSeamAtom q ^ k) :=
  ⟨not_summable_reciprocalSeamZerothMoment, fun _ hk => summable_reciprocalSeamAtom_pow hk⟩

end RHTower
