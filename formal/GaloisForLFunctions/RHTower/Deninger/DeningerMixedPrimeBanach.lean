import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# The mixed weighted `L¹`/`L²` prime space is complete

The restricted prime sum of the arithmetic direct image takes values in the families `(f_p)` that
are simultaneously weighted-summable and weighted-square-summable,

`∑ α_p ‖f_p‖ < ∞`,  `∑ β_p ‖f_p‖² < ∞`,

with the mixed norm `∑ α_p ‖f_p‖ + (∑ β_p ‖f_p‖²)^{1/2}`.  This is the completed mixed space that
the arithmetic direct image needs, and it is realized here without leaving mathlib's `lp` spaces:
rescaling by `α_p` sends the first condition to membership in `lp E 1`, rescaling by `√β_p` sends
the second to membership in `lp E 2`, and the mixed space is exactly the locus in
`lp E 1 × lp E 2` where the two rescalings come from a common family.  That compatibility is the
closed condition `α_p x₂(p) = √β_p x₁(p)`, an equality of two continuous functions of `x` for each
`p`, so the mixed space is a closed subspace of a product of Banach spaces and is therefore itself
a Banach space.

The mixed norm is the sum of the two `lp` norms, and completeness is inherited from the ambient
product.

* `RHTower.deningerLpEval` : coordinate evaluation on `lp`, continuous of norm at most one.
* `RHTower.deningerMixedSubmodule` : the mixed weighted `L¹`/`L²` space.
* `RHTower.deningerMixedSubmodule_isClosed` : it is closed in the product.
* `RHTower.deningerMixedSubmodule_completeSpace` : hence complete.
* `RHTower.deningerMixed_mem_iff` : membership is exactly having a common underlying family.
* `RHTower.deningerMixed_summable_one`, `RHTower.deningerMixed_summable_two` : the two weighted
  summability conditions of the underlying family.
-/

namespace RHTower

open scoped ENNReal

section MixedBanach

variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)]

/-- Coordinate evaluation on `lp`, as a continuous linear map of norm at most one. -/
noncomputable def deningerLpEval (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) : lp E p →L[ℝ] E i :=
  LinearMap.mkContinuous
    { toFun := fun x => (x : ∀ i, E i) i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1
    (fun x => by
      have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
      simpa using lp.norm_apply_le_norm hp0 x i)

@[simp] theorem deningerLpEval_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : ι) (x : lp E p) :
    deningerLpEval p i x = (x : ∀ i, E i) i := rfl

variable (α β : ι → ℝ)

/-- **The mixed weighted `L¹`/`L²` prime space.**  A pair of an `lp E 1` and an `lp E 2` element
lies in it exactly when the two are the `α`- and `√β`-rescalings of one common family. -/
def deningerMixedSubmodule : Submodule ℝ (lp E 1 × lp E 2) where
  carrier := {x | ∀ i, α i • ((x.2 : ∀ i, E i) i) = Real.sqrt (β i) • ((x.1 : ∀ i, E i) i)}
  add_mem' := by
    intro x y hx hy i
    have hx' := hx i
    have hy' := hy i
    show α i • (((x.2 + y.2 : lp E 2) : ∀ i, E i) i) =
      Real.sqrt (β i) • (((x.1 + y.1 : lp E 1) : ∀ i, E i) i)
    simp only [lp.coeFn_add, Pi.add_apply, smul_add, hx', hy']
  zero_mem' := by
    intro i
    simp
  smul_mem' := by
    intro c x hx i
    have hx' := hx i
    show α i • (((c • x.2 : lp E 2) : ∀ i, E i) i) =
      Real.sqrt (β i) • (((c • x.1 : lp E 1) : ∀ i, E i) i)
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_comm (α i) c, smul_comm (Real.sqrt (β i)) c, hx']

theorem deningerMixed_mem_def (x : lp E 1 × lp E 2) :
    x ∈ deningerMixedSubmodule α β ↔
      ∀ i, α i • ((x.2 : ∀ i, E i) i) = Real.sqrt (β i) • ((x.1 : ∀ i, E i) i) := Iff.rfl

/-- **The mixed space is closed.**  For each index the compatibility condition equates two
continuous functions of the pair. -/
theorem deningerMixedSubmodule_isClosed :
    IsClosed ((deningerMixedSubmodule α β : Submodule ℝ (lp E 1 × lp E 2)) :
      Set (lp E 1 × lp E 2)) := by
  have hset : ((deningerMixedSubmodule α β : Submodule ℝ (lp E 1 × lp E 2)) :
      Set (lp E 1 × lp E 2)) =
      ⋂ i : ι, {x : lp E 1 × lp E 2 |
        α i • ((x.2 : ∀ i, E i) i) = Real.sqrt (β i) • ((x.1 : ∀ i, E i) i)} := by
    ext x
    simp [deningerMixedSubmodule, Set.mem_iInter]
  rw [hset]
  refine isClosed_iInter fun i => isClosed_eq ?_ ?_
  · exact (continuous_const_smul (α i)).comp
      (((deningerLpEval (2 : ℝ≥0∞) i).continuous).comp continuous_snd)
  · exact (continuous_const_smul (Real.sqrt (β i))).comp
      (((deningerLpEval (1 : ℝ≥0∞) i).continuous).comp continuous_fst)

/-- **The mixed weighted `L¹`/`L²` prime space is complete.**  It is a closed subspace of a product
of two Banach spaces. -/
theorem deningerMixedSubmodule_completeSpace [∀ i, CompleteSpace (E i)] :
    CompleteSpace ((deningerMixedSubmodule α β : Submodule ℝ (lp E 1 × lp E 2))) :=
  (deningerMixedSubmodule_isClosed α β).completeSpace_coe

/-- Membership in the mixed space is exactly the existence of a common underlying family. -/
theorem deningerMixed_mem_iff (hα : ∀ i, α i ≠ 0) (x : lp E 1 × lp E 2) :
    x ∈ deningerMixedSubmodule α β ↔
      ∃ f : ∀ i, E i, (∀ i, (x.1 : ∀ i, E i) i = α i • f i) ∧
        (∀ i, (x.2 : ∀ i, E i) i = Real.sqrt (β i) • f i) := by
  constructor
  · intro hx
    refine ⟨fun i => (α i)⁻¹ • ((x.1 : ∀ i, E i) i), fun i => ?_, fun i => ?_⟩
    · rw [smul_inv_smul₀ (hα i)]
    · have hxi := hx i
      have : α i • ((x.2 : ∀ i, E i) i) = α i • (Real.sqrt (β i) • ((α i)⁻¹ •
          ((x.1 : ∀ i, E i) i))) := by
        rw [smul_comm (Real.sqrt (β i)) ((α i)⁻¹), smul_inv_smul₀ (hα i)]
        exact hxi
      exact smul_right_injective _ (hα i) this
  · rintro ⟨f, h1, h2⟩ i
    rw [h1 i, h2 i, smul_comm]

/-- The `α`-weighted absolute summability of the underlying family. -/
theorem deningerMixed_summable_one (hα : ∀ i, 0 ≤ α i) (x : lp E 1) (f : ∀ i, E i)
    (hf : ∀ i, (x : ∀ i, E i) i = α i • f i) :
    Summable fun i => α i * ‖f i‖ := by
  have hsum : Summable fun i => ‖(x : ∀ i, E i) i‖ := by
    have h := (lp.memℓp x).summable (p := 1) (by norm_num)
    simpa using h
  refine hsum.congr fun i => ?_
  rw [hf i, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hα i)]

/-- The `β`-weighted square summability of the underlying family. -/
theorem deningerMixed_summable_two (hβ : ∀ i, 0 ≤ β i) (x : lp E 2) (f : ∀ i, E i)
    (hf : ∀ i, (x : ∀ i, E i) i = Real.sqrt (β i) • f i) :
    Summable fun i => β i * ‖f i‖ ^ 2 := by
  have hsum : Summable fun i => ‖(x : ∀ i, E i) i‖ ^ 2 := by
    have h := (lp.memℓp x).summable (p := 2) (by norm_num)
    refine h.congr fun i => ?_
    rw [show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) by norm_num,
      show ((2 : ℝ) = ((2 : ℕ) : ℝ)) by norm_num, Real.rpow_natCast]
  refine hsum.congr fun i => ?_
  rw [hf i, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (hβ i)]


variable [DecidableEq ι]

/-- The single-prime truncation of a pair, as an element of the product. -/
noncomputable def deningerMixedSingle (x : lp E 1 × lp E 2) (i : ι) : lp E 1 × lp E 2 :=
  (lp.single 1 i ((x.1 : ∀ j, E j) i), lp.single 2 i ((x.2 : ∀ j, E j) i))

/-- A single-prime truncation of a member of the mixed space is again a member: the compatibility
condition is the one at that prime, and every other coordinate is zero. -/
theorem deningerMixedSingle_mem (x : lp E 1 × lp E 2)
    (hx : x ∈ deningerMixedSubmodule α β) (i : ι) :
    deningerMixedSingle x i ∈ deningerMixedSubmodule α β := by
  intro j
  by_cases hji : j = i
  · subst hji
    simpa [deningerMixedSingle, lp.single_apply_self] using hx j
  · simp [deningerMixedSingle, Pi.single_eq_of_ne hji]

omit [∀ i, NormedSpace ℝ (E i)] in
/-- **`(7)`: the mixed space is the completion of the finitely supported packet families.**  Every
member is the unconditional sum of its single-prime truncations, each of which is again a member,
so the strict inductive limit of the finite direct sums is dense and its completion is the mixed
space itself. -/
theorem deningerMixed_hasSum_single (x : lp E 1 × lp E 2) :
    HasSum (fun i => deningerMixedSingle x i) x := by
  have h1 := lp.hasSum_single (p := (1 : ℝ≥0∞)) (by norm_num) x.1
  have h2 := lp.hasSum_single (p := (2 : ℝ≥0∞)) (by norm_num) x.2
  simpa [deningerMixedSingle] using h1.prodMk h2

end MixedBanach

end RHTower
