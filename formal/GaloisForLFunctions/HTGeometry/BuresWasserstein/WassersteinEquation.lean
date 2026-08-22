import GaloisForLFunctions.HTGeometry.BuresWasserstein.OperatorGeometricMean

/-!
# The Wasserstein (Bures–Wasserstein barycentre) equation for positive operators

For a weighted family `(wᵢ, Aᵢ)` of strictly positive elements of a unital C⋆-algebra, the
Bures–Wasserstein barycentre is characterised by the first-order optimality condition

`∑ᵢ wᵢ (Aᵢ # X⁻¹) = 1`,   equivalently   `∑ᵢ wᵢ (X^{1/2} Aᵢ X^{1/2})^{1/2} = X`.

This file introduces the predicate `IsWassersteinPoint`, proves the equivalence of the two
displayed forms, and establishes the elementary structural properties of the solution set:
the two-sided Loewner bounds of Kim–Mer–Pálfia Lemma 3.3, homogeneity (Lemma 3.4), and the
permutation, repetition and unitary-congruence invariances of Proposition 6.1.
-/

open scoped NNReal Ring

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι : Type*}

/-! ### Auxiliary sandwich identities -/

variable {X : A}

lemma rpow_neg_half_mul_self_mul_rpow_neg_half (hX : IsStrictlyPositive X) :
    X ^ (-(1/2) : ℝ) * X * X ^ (-(1/2) : ℝ) = 1 := by
  nth_rewrite 2 [← rpow_half_mul_rpow_half hX]
  rw [← mul_assoc, rpow_neg_half_mul_rpow_half hX, one_mul, rpow_half_mul_rpow_neg_half hX]

/-- Conjugation by `X^{-1/2}` turns the identity into `X`. -/
lemma conj_eq_one_iff (hX : IsStrictlyPositive X) (T : A) :
    X ^ (-(1/2) : ℝ) * T * X ^ (-(1/2) : ℝ) = 1 ↔ T = X := by
  constructor
  · intro h
    have h2 : X ^ (1/2 : ℝ) * (X ^ (-(1/2) : ℝ) * T * X ^ (-(1/2) : ℝ)) * X ^ (1/2 : ℝ)
        = X ^ (1/2 : ℝ) * 1 * X ^ (1/2 : ℝ) := by rw [h]
    rwa [sandwich_peel hX, mul_one, rpow_half_mul_rpow_half hX] at h2
  · rintro rfl
    exact rpow_neg_half_mul_self_mul_rpow_neg_half hX

/-! ### The Wasserstein equation -/

/-- `X` is a **Wasserstein point** of the weighted family `(w, Av)` on `s`: it is strictly
positive and solves `∑ᵢ wᵢ (Aᵢ # X⁻¹) = 1`. -/
def IsWassersteinPoint (s : Finset ι) (w : ι → ℝ) (Av : ι → A) (X : A) : Prop :=
  IsStrictlyPositive X ∧ ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ = 1

variable {s : Finset ι} {w : ι → ℝ} {Av : ι → A}

lemma IsWassersteinPoint.strictlyPositive (h : IsWassersteinPoint s w Av X) :
    IsStrictlyPositive X := h.1

lemma IsWassersteinPoint.eq (h : IsWassersteinPoint s w Av X) :
    ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ = 1 := h.2

/-- **The two forms of the Wasserstein equation agree**:
`∑ wᵢ (Aᵢ # X⁻¹) = 1` is equivalent to `∑ wᵢ (X^{1/2} Aᵢ X^{1/2})^{1/2} = X`. -/
theorem isWassersteinPoint_iff_sqrt (hX : IsStrictlyPositive X)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) :
    IsWassersteinPoint s w Av X ↔
      ∑ i ∈ s, w i • CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ)) = X := by
  have hrw : ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ
      = X ^ (-(1/2) : ℝ)
        * (∑ i ∈ s, w i • CFC.sqrt (X ^ (1/2 : ℝ) * Av i * X ^ (1/2 : ℝ)))
        * X ^ (-(1/2) : ℝ) := by
    rw [← sum_smul_conjugate]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [gm_comm (hA i hi) hX.ringInverse, gm_ringInverse_left hX]
  constructor
  · rintro ⟨-, h⟩
    rw [hrw] at h
    exact (conj_eq_one_iff hX _).mp h
  · intro h
    exact ⟨hX, by rw [hrw]; exact (conj_eq_one_iff hX _).mpr h⟩

/-! ### Two-sided Loewner bounds (Kim–Mer–Pálfia, Lemma 3.3) -/

/-- `(c · 1) # X⁻¹ = √c · X^{-1/2}`. -/
lemma gm_smul_one_ringInverse {c : ℝ} (hc : 0 < c) (hX : IsStrictlyPositive X) :
    gm (c • (1 : A)) X⁻¹ʳ = Real.sqrt c • X ^ (-(1/2) : ℝ) := by
  have h1 : gm (c • (1 : A)) ((1 : ℝ) • X⁻¹ʳ) = Real.sqrt (c * 1) • gm 1 X⁻¹ʳ :=
    gm_smul hc one_pos isStrictlyPositive_one hX.ringInverse
  rwa [one_smul, mul_one, gm_one_left, CFC.sqrt_eq_rpow, rpow_half_ringInverse hX] at h1

/-- If every `Aᵢ` lies in the Loewner interval `[α, β]` then so does every Wasserstein point. -/
theorem IsWassersteinPoint.mem_Icc {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hsum : ∑ i ∈ s, w i = 1) (hw : ∀ i ∈ s, 0 < w i)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i))
    (hlo : ∀ i ∈ s, α • (1 : A) ≤ Av i) (hhi : ∀ i ∈ s, Av i ≤ β • (1 : A))
    (h : IsWassersteinPoint s w Av X) :
    α • (1 : A) ≤ X ∧ X ≤ β • (1 : A) := by
  obtain ⟨hX, heq⟩ := h
  have hkey : ∀ i ∈ s, Real.sqrt α • X ^ (-(1/2) : ℝ) ≤ gm (Av i) X⁻¹ʳ ∧
      gm (Av i) X⁻¹ʳ ≤ Real.sqrt β • X ^ (-(1/2) : ℝ) := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← gm_smul_one_ringInverse hα hX]
      exact gm_mono_left (IsStrictlyPositive.smul hα isStrictlyPositive_one) (hA i hi)
        hX.ringInverse (hlo i hi)
    · rw [← gm_smul_one_ringInverse hβ hX]
      exact gm_mono_left (hA i hi) (IsStrictlyPositive.smul hβ isStrictlyPositive_one)
        hX.ringInverse (hhi i hi)
  have hlow : Real.sqrt α • X ^ (-(1/2) : ℝ) ≤ 1 := by
    rw [← heq, show Real.sqrt α • X ^ (-(1/2) : ℝ)
      = ∑ i ∈ s, w i • (Real.sqrt α • X ^ (-(1/2) : ℝ)) by rw [← Finset.sum_smul, hsum, one_smul]]
    exact Finset.sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (hkey i hi).1 (hw i hi).le
  have hupp : (1 : A) ≤ Real.sqrt β • X ^ (-(1/2) : ℝ) := by
    rw [← heq, show Real.sqrt β • X ^ (-(1/2) : ℝ)
      = ∑ i ∈ s, w i • (Real.sqrt β • X ^ (-(1/2) : ℝ)) by rw [← Finset.sum_smul, hsum, one_smul]]
    exact Finset.sum_le_sum fun i hi => smul_le_smul_of_nonneg_left (hkey i hi).2 (hw i hi).le
  have hXhalf : (0 : A) ≤ X ^ (-(1/2) : ℝ) := CFC.rpow_nonneg
  have hXinv : X ^ (-(1/2) : ℝ) * X ^ (-(1/2) : ℝ) = X⁻¹ʳ :=
    rpow_neg_half_mul_rpow_neg_half hX
  have hsα : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  constructor
  · have h1 : X ^ (-(1/2) : ℝ) ≤ (Real.sqrt α)⁻¹ • (1 : A) := by
      have hs := smul_le_smul_of_nonneg_left hlow (inv_pos.mpr hsα).le
      rwa [smul_smul, inv_mul_cancel₀ hsα.ne', one_smul] at hs
    have h2 := mul_self_le_of_le_smul_one hXhalf (inv_pos.mpr hsα).le h1
    rw [hXinv] at h2
    have h3 := CStarAlgebra.ringInverse_le_ringInverse h2 hX.ringInverse
    rw [Ring.inverse_inverse hX.isUnit] at h3
    refine le_trans (le_of_eq ?_) h3
    have hsc : ((Real.sqrt α)⁻¹ * (Real.sqrt α)⁻¹)⁻¹ = α := by
      rw [← mul_inv, inv_inv, Real.mul_self_sqrt hα.le]
    rw [ringInverse_smul (by positivity) (isStrictlyPositive_one (A := A)), Ring.inverse_one, hsc]
  · have h1 : (Real.sqrt β)⁻¹ • (1 : A) ≤ X ^ (-(1/2) : ℝ) := by
      have hs := smul_le_smul_of_nonneg_left hupp (inv_pos.mpr hsβ).le
      rwa [smul_smul, inv_mul_cancel₀ hsβ.ne', one_smul] at hs
    have h2 := smul_one_le_mul_self_of_le hXhalf (inv_pos.mpr hsβ).le h1
    rw [hXinv] at h2
    have hpos : IsStrictlyPositive (((Real.sqrt β)⁻¹ * (Real.sqrt β)⁻¹) • (1 : A)) :=
      IsStrictlyPositive.smul (by positivity) isStrictlyPositive_one
    have h3 := CStarAlgebra.ringInverse_le_ringInverse h2 hpos
    rw [Ring.inverse_inverse hX.isUnit] at h3
    refine h3.trans (le_of_eq ?_)
    have hsc : ((Real.sqrt β)⁻¹ * (Real.sqrt β)⁻¹)⁻¹ = β := by
      rw [← mul_inv, inv_inv, Real.mul_self_sqrt hβ.le]
    rw [ringInverse_smul (by positivity) (isStrictlyPositive_one (A := A)), Ring.inverse_one, hsc]

/-! ### Homogeneity (Kim–Mer–Pálfia, Lemma 3.4) -/

/-- **Homogeneity of the solution set.** -/
theorem isWassersteinPoint_smul {r : ℝ} (hr : 0 < r) (hX : IsStrictlyPositive X)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) :
    IsWassersteinPoint s w (fun i => r • Av i) (r • X) ↔ IsWassersteinPoint s w Av X := by
  have hpt : ∀ i ∈ s, gm (r • Av i) (r • X)⁻¹ʳ = gm (Av i) X⁻¹ʳ := by
    intro i hi
    rw [ringInverse_smul hr hX, gm_smul hr (inv_pos.mpr hr) (hA i hi) hX.ringInverse,
      show r * r⁻¹ = 1 by field_simp, Real.sqrt_one, one_smul]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨hX, by rw [← h]; exact (Finset.sum_congr rfl fun i hi => by rw [hpt i hi]).symm⟩
  · rintro ⟨-, h⟩
    exact ⟨hX.smul hr, by rw [← h]; exact Finset.sum_congr rfl fun i hi => by rw [hpt i hi]⟩

/-! ### Permutation, repetition and unitary congruence (Proposition 6.1) -/

/-- **Permutation invariance.** -/
theorem isWassersteinPoint_reindex {κ : Type*} (e : κ ≃ ι) (t : Finset κ) :
    IsWassersteinPoint (t.map e.toEmbedding) w Av X ↔
      IsWassersteinPoint t (w ∘ e) (Av ∘ e) X := by
  unfold IsWassersteinPoint
  rw [Finset.sum_map]
  rfl

/-- **Repetition invariance**: repeating the family `k` times with weights divided by `k`
does not change the equation. -/
theorem isWassersteinPoint_repeat {k : ℕ} (hk : 0 < k) :
    IsWassersteinPoint (s ×ˢ Finset.range k) (fun p => w p.1 / k) (fun p => Av p.1) X ↔
      IsWassersteinPoint s w Av X := by
  unfold IsWassersteinPoint
  rw [Finset.sum_product]
  have : ∀ i ∈ s, (∑ _j ∈ Finset.range k, (w i / k) • gm (Av i) X⁻¹ʳ)
      = w i • gm (Av i) X⁻¹ʳ := by
    intro i _
    rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl this]

/-- **Unitary congruence invariance.** -/
theorem IsWassersteinPoint.unitary_conjugate {U : A} (hU : U ∈ unitary A)
    (hA : ∀ i ∈ s, IsStrictlyPositive (Av i)) (h : IsWassersteinPoint s w Av X) :
    IsWassersteinPoint s w (fun i => U * Av i * star U) (U * X * star U) := by
  obtain ⟨hX, heq⟩ := h
  have hUs : U * star U = 1 := Unitary.mul_star_self_of_mem hU
  have hsU' : star U * U = 1 := Unitary.star_mul_self_of_mem hU
  have hUu : IsUnit U := ⟨⟨U, star U, hUs, hsU'⟩, rfl⟩
  have hsU : IsUnit (star U) := ⟨⟨star U, U, hsU', hUs⟩, rfl⟩
  have hUinv : U⁻¹ʳ = star U := by
    rw [← mul_one U⁻¹ʳ, Ring.inverse_mul_eq_iff_eq_mul _ _ _ hUu, hUs]
  have hsUinv : (star U)⁻¹ʳ = U := by
    rw [← mul_one (star U)⁻¹ʳ, Ring.inverse_mul_eq_iff_eq_mul _ _ _ hsU, hsU']
  refine ⟨hUu.isStrictlyPositive_star_right_conjugate_iff.mpr hX, ?_⟩
  have hinv : (U * X * star U)⁻¹ʳ = U * X⁻¹ʳ * star U := by
    rw [Ring.inverse_mul (Or.inl (hUu.mul hX.isUnit)), Ring.inverse_mul (Or.inl hUu),
      hUinv, hsUinv, mul_assoc]
  rw [hinv]
  have hterm : ∀ i ∈ s, gm (U * Av i * star U) (U * X⁻¹ʳ * star U)
      = U * gm (Av i) X⁻¹ʳ * star U := fun i hi =>
    (gm_conjugate hUu (hA i hi) hX.ringInverse).symm
  have hterm' : ∀ i ∈ s, w i • (gm (U * Av i * star U) (U * X⁻¹ʳ * star U))
      = w i • (U * gm (Av i) X⁻¹ʳ * star U) := fun i hi => by rw [hterm i hi]
  calc ∑ i ∈ s, w i • ((fun i => U * Av i * star U) i #ᴳ (U * X⁻¹ʳ * star U))
      = ∑ i ∈ s, w i • (U * gm (Av i) X⁻¹ʳ * star U) := Finset.sum_congr rfl hterm'
    _ = U * (∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ) * star U := sum_smul_conjugate _ _ _ _
    _ = 1 := by rw [heq, mul_one, hUs]

/-- **Self-reference**: adjoining `X` itself with weight `w j` to the family is equivalent to
renormalising the remaining weights by `1 - w j`. -/
theorem isWassersteinPoint_insert_self [DecidableEq ι] {j : ι} (hj : j ∉ s)
    (hwj : w j ≠ 1) (hX : IsStrictlyPositive X) :
    IsWassersteinPoint (insert j s) w (Function.update Av j X) X ↔
      IsWassersteinPoint s (fun i => w i / (1 - w j)) Av X := by
  have hself : gm X X⁻¹ʳ = 1 := gm_ringInverse_self hX
  have hsplit : ∑ i ∈ insert j s, w i • gm (Function.update Av j X i) X⁻¹ʳ
      = w j • (1 : A) + ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ := by
    rw [Finset.sum_insert hj, Function.update_self, hself]
    congr 1
    exact Finset.sum_congr rfl fun i hi => by
      rw [Function.update_of_ne (by rintro rfl; exact hj hi)]
  have hscale : ∑ i ∈ s, (w i / (1 - w j)) • gm (Av i) X⁻¹ʳ
      = (1 - w j)⁻¹ • ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, div_eq_inv_mul]
  have hne : (1 : ℝ) - w j ≠ 0 := sub_ne_zero.mpr (Ne.symm hwj)
  unfold IsWassersteinPoint
  rw [hsplit, hscale]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have h2 : ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ = (1 - w j) • (1 : A) := by
      rw [sub_smul, one_smul]
      exact eq_sub_of_add_eq' h
    rw [h2, smul_smul, inv_mul_cancel₀ hne, one_smul]
  · have h2 : ∑ i ∈ s, w i • gm (Av i) X⁻¹ʳ = (1 - w j) • (1 : A) := by
      rw [← h, smul_smul, mul_inv_cancel₀ hne, one_smul]
    rw [h2, sub_smul, one_smul]
    abel

end

end GaloisForLFunctions.HTGeometry.BuresWasserstein
