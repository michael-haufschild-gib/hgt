import GaloisForLFunctions.HTGeometry.SiegelEntryBound

/-!
# The projected norm is a squared distance

The projected norm at level `i` is intrinsic: it is the squared distance of `v` from the span of the
first `i` basis vectors,

`projNorm i v = min { A[v − w] : w supported on the first i coordinates }`.

The inequality `≤` is immediate, because subtracting such a `w` cannot change the coordinates from
`i` on: an upper triangular `U` sends a vector supported below `i` to one supported below `i`.  The
attainment is the solvability of a unipotent triangular system, obtained from injectivity in equal
finite dimension.

Intrinsic-ness is what makes the Lovász swap work without computing any determinant: after
transposing two adjacent basis vectors the span of the earlier ones is unchanged, so the new
diagonal entry is the old projected norm of the transposed vector.

* `lowerSupport` : the vectors supported on the first `i` coordinates.
* `JacobiData.mulVec_lower` : `U` preserves that support condition.
* `JacobiData.projNorm_le_form_sub` : **the inequality.**
* `JacobiData.exists_proj` : **the attainment.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The vectors supported on the coordinates before `i`. -/
def lowerSupport (i : Fin n) : Submodule ℝ (Fin n → ℝ) where
  carrier := {w | ∀ p : Fin n, i ≤ p → w p = 0}
  add_mem' := by
    intro a b ha hb p hp
    show a p + b p = 0
    rw [ha p hp, hb p hp, add_zero]
  zero_mem' := by intro p _; rfl
  smul_mem' := by
    intro c a ha p hp
    show c * a p = 0
    rw [ha p hp, mul_zero]

theorem mem_lowerSupport {i : Fin n} {w : Fin n → ℝ} :
    w ∈ lowerSupport i ↔ ∀ p : Fin n, i ≤ p → w p = 0 := Iff.rfl

/-- An upper triangular matrix preserves the support condition. -/
theorem JacobiData.mulVec_lower (J : JacobiData n) {i : Fin n} {w : Fin n → ℝ}
    (hw : w ∈ lowerSupport i) {m : Fin n} (hm : i ≤ m) : (J.U *ᵥ w) m = 0 := by
  classical
  show ∑ p, J.U m p * w p = 0
  refine Finset.sum_eq_zero fun p _ => ?_
  rcases lt_or_ge p m with hpm | hpm
  · rw [J.upper m p hpm, zero_mul]
  · rw [hw p (le_trans hm hpm), mul_zero]

/-- **The projected norm is at most the squared distance to any vector supported below `i`.** -/
theorem JacobiData.projNorm_le_form_sub (J : JacobiData n) (i : Fin n) (v : Fin n → ℝ)
    {w : Fin n → ℝ} (hw : w ∈ lowerSupport i) :
    J.projNorm i v ≤ (v - w) ⬝ᵥ (J.form *ᵥ (v - w)) := by
  classical
  rw [J.quadForm_eq (v - w)]
  have hcoord : ∀ m : Fin n, i ≤ m → (J.U *ᵥ (v - w)) m = (J.U *ᵥ v) m := by
    intro m hm
    rw [Matrix.mulVec_sub]
    show (J.U *ᵥ v) m - (J.U *ᵥ w) m = (J.U *ᵥ v) m
    rw [J.mulVec_lower hw hm, sub_zero]
  rw [JacobiData.projNorm]
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset (fun m : Fin n => i ≤ m) Finset.univ)
    fun m _ _ => mul_nonneg (J.pos m).le (sq_nonneg _))
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [hcoord m hm.2]

/-- A vector supported below `i` whose first `i` transformed coordinates vanish is zero. -/
theorem JacobiData.eq_zero_of_mulVec_lower (J : JacobiData n) {i : Fin n} {w : Fin n → ℝ}
    (hw : w ∈ lowerSupport i) (h : ∀ m : Fin n, m < i → (J.U *ᵥ w) m = 0) : w = 0 := by
  classical
  have key : ∀ k : ℕ, ∀ p : Fin n, p < i → (i : ℕ) - (p : ℕ) ≤ k → w p = 0 := by
    intro k
    induction k with
    | zero =>
        intro p hp hk
        exact absurd (Fin.lt_def.1 hp) (by omega)
    | succ k ih =>
        intro p hp hk
        have hexp : (J.U *ᵥ w) p = w p + ∑ q ∈ Finset.univ.filter (fun q : Fin n => p < q),
            J.U p q * w q := by
          show ∑ q, J.U p q * w q = _
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun q : Fin n => p < q)]
          rw [add_comm]
          congr 1
          refine (Finset.sum_eq_single p (fun q hq hqp => ?_) (fun hcon => ?_)).trans ?_
          · rw [Finset.mem_filter] at hq
            have hqlt : q < p := lt_of_le_of_ne (not_lt.1 hq.2) hqp
            rw [J.upper p q hqlt, zero_mul]
          · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ p, lt_irrefl p⟩) hcon
          · rw [J.unit p, one_mul]
        have htail : (∑ q ∈ Finset.univ.filter (fun q : Fin n => p < q), J.U p q * w q) = 0 := by
          refine Finset.sum_eq_zero fun q hq => ?_
          rw [Finset.mem_filter] at hq
          rcases lt_or_ge q i with hqi | hqi
          · rw [ih q hqi (by
              have h1 := Fin.lt_def.1 hq.2
              omega), mul_zero]
          · rw [hw q hqi, mul_zero]
        have := h p hp
        rw [hexp, htail, add_zero] at this
        exact this
  funext p
  rcases lt_or_ge p i with hp | hp
  · exact key ((i : ℕ) - (p : ℕ)) p hp (le_refl _)
  · exact hw p hp

/-- The truncation of a vector to its coordinates before `i`. -/
def truncLower (i : Fin n) (x : Fin n → ℝ) : Fin n → ℝ := fun m => if m < i then x m else 0

theorem truncLower_mem (i : Fin n) (x : Fin n → ℝ) : truncLower i x ∈ lowerSupport i := by
  intro p hp
  simp [truncLower, not_lt.2 hp]

/-- The map sending a vector supported below `i` to the truncation of its transform. -/
noncomputable def JacobiData.lowerMap (J : JacobiData n) (i : Fin n) :
    lowerSupport i →ₗ[ℝ] lowerSupport i where
  toFun w := ⟨truncLower i (J.U *ᵥ (w : Fin n → ℝ)), truncLower_mem i _⟩
  map_add' := by
    intro a b
    refine Subtype.ext ?_
    funext m
    show truncLower i (J.U *ᵥ ((a : Fin n → ℝ) + b)) m
      = truncLower i (J.U *ᵥ (a : Fin n → ℝ)) m + truncLower i (J.U *ᵥ (b : Fin n → ℝ)) m
    rw [Matrix.mulVec_add]
    by_cases hm : m < i <;> simp [truncLower, hm]
  map_smul' := by
    intro c a
    refine Subtype.ext ?_
    funext m
    show truncLower i (J.U *ᵥ (c • (a : Fin n → ℝ))) m
      = c * truncLower i (J.U *ᵥ (a : Fin n → ℝ)) m
    rw [Matrix.mulVec_smul]
    by_cases hm : m < i <;> simp [truncLower, hm]

theorem JacobiData.lowerMap_injective (J : JacobiData n) (i : Fin n) :
    Function.Injective (J.lowerMap i) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => ?_
  refine Subtype.ext ?_
  refine J.eq_zero_of_mulVec_lower w.2 fun m hm => ?_
  have := congrFun (congrArg Subtype.val hw) m
  show (J.U *ᵥ (w : Fin n → ℝ)) m = 0
  simpa [JacobiData.lowerMap, truncLower, hm] using this

/-- **The projection exists**: some vector supported below `i` matches the first `i` transformed
coordinates of `v`. -/
theorem JacobiData.exists_proj (J : JacobiData n) (i : Fin n) (v : Fin n → ℝ) :
    ∃ w : Fin n → ℝ, w ∈ lowerSupport i ∧
      ∀ m : Fin n, m < i → (J.U *ᵥ w) m = (J.U *ᵥ v) m := by
  classical
  have hsurj : Function.Surjective (J.lowerMap i) :=
    LinearMap.injective_iff_surjective.1 (J.lowerMap_injective i)
  obtain ⟨w, hw⟩ := hsurj ⟨truncLower i (J.U *ᵥ v), truncLower_mem i _⟩
  refine ⟨(w : Fin n → ℝ), w.2, fun m hm => ?_⟩
  have := congrFun (congrArg Subtype.val hw) m
  simpa [JacobiData.lowerMap, truncLower, hm] using this

/-- **The projected norm is the squared distance to the span of the first `i` coordinates.** -/
theorem JacobiData.projNorm_eq_form_sub (J : JacobiData n) (i : Fin n) (v : Fin n → ℝ) :
    ∃ w : Fin n → ℝ, w ∈ lowerSupport i ∧
      J.projNorm i v = (v - w) ⬝ᵥ (J.form *ᵥ (v - w)) := by
  classical
  obtain ⟨w, hw, hmatch⟩ := J.exists_proj i v
  refine ⟨w, hw, ?_⟩
  have hall : ∀ m : Fin n, J.d m * ((J.U *ᵥ (v - w)) m) ^ (2 : ℕ)
      = if i ≤ m then J.d m * ((J.U *ᵥ v) m) ^ (2 : ℕ) else 0 := by
    intro m
    by_cases hm : i ≤ m
    · rw [if_pos hm]
      congr 2
      rw [Matrix.mulVec_sub]
      show (J.U *ᵥ v) m - (J.U *ᵥ w) m = (J.U *ᵥ v) m
      rw [J.mulVec_lower hw hm, sub_zero]
    · rw [if_neg hm]
      have hmi : m < i := not_le.1 hm
      have hz : (J.U *ᵥ (v - w)) m = 0 := by
        rw [Matrix.mulVec_sub]
        show (J.U *ᵥ v) m - (J.U *ᵥ w) m = 0
        rw [hmatch m hmi, sub_self]
      rw [hz]
      ring
  have hmain : (v - w) ⬝ᵥ (J.form *ᵥ (v - w)) = J.projNorm i v := by
    rw [J.quadForm_eq (v - w), JacobiData.projNorm,
      Finset.sum_congr rfl (fun m (_ : m ∈ (Finset.univ : Finset (Fin n))) => hall m),
      Finset.sum_ite, Finset.sum_const_zero, add_zero]
  exact hmain.symm

end GaloisForLFunctions.HTGeometry
