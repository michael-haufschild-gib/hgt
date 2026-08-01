import GaloisForLFunctions.RHTower.DeningerL2Definite
import GaloisForLFunctions.RHTower.DeningerKummerSpaceInnerPos

/-!
# Definiteness of the `L²` form on the Kummer space

Definiteness of the place norm transports along the whole chain: a nonzero algebraic number of
vanishing `L²` norm is a root of unity, so its class in `𝒢 = Q̄ˣ/μ_∞` is trivial, and a fraction
of vanishing norm in `𝒢 ⊗ ℚ` has trivial numerator, hence is zero.

* `deningerAbsL2Inner_self_eq_zero` : the absolute form is definite modulo torsion.
* `deningerKummerL2Inner_self_eq_zero` : the form on `𝒢` is definite.
* `deningerSpaceL2Inner_self_eq_zero` : the form on `𝒢 ⊗ ℚ` is definite.
-/

namespace RHTower

open NumberField

open scoped IntermediateField

section AbsoluteDefinite

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

omit [Algebra.IsAlgebraic ℚ F] in
/-- Finite order transfers back from a subfield element. -/
theorem deningerIntermediate_isOfFinOrder_of {E : IntermediateField ℚ F} {α : F} (hα : α ∈ E)
    (h : IsOfFinOrder (⟨α, hα⟩ : E)) : IsOfFinOrder α := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp h
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  have := congrArg (fun z : E => (z : F)) hpow
  simpa using this

/-- **The absolute form is definite modulo torsion.** -/
theorem deningerAbsL2Inner_self_eq_zero {α : F} (hα : α ≠ 0)
    (h : deningerAbsL2Inner α α = 0) : IsOfFinOrder α := by
  have hαm : α ∈ (ℚ⟮α, α⟯ : IntermediateField ℚ F) :=
    IntermediateField.subset_adjoin ℚ {α, α} (by simp)
  have h2 : deningerNormalizedL2Inner (ℚ⟮α, α⟯ : IntermediateField ℚ F) ⟨α, hαm⟩ ⟨α, hαm⟩ = 0 := by
    rw [← deningerAbsL2Inner_intermediateField (ℚ⟮α, α⟯ : IntermediateField ℚ F) hαm hαm hα hα]
    exact h
  rw [deningerNormalizedL2Inner, deningerL2Inner_self, div_eq_zero_iff] at h2
  refine deningerIntermediate_isOfFinOrder_of hαm ?_
  exact deningerL2NormSq_eq_zero (deningerIntermediate_ne_zero hαm hα)
    (h2.resolve_right deningerFinrank_ne_zero)

end AbsoluteDefinite

section KummerDefinite

variable {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]

/-- **The form on the Kummer group is definite.** -/
theorem deningerKummerL2Inner_self_eq_zero {x : deningerKummerGroup F}
    (h : deningerKummerL2Inner x x = 0) : x = 1 := by
  induction x using QuotientGroup.induction_on with
  | H u =>
    refine (QuotientGroup.eq_one_iff u).mpr ((CommGroup.mem_torsion u).mpr ?_)
    exact deningerUnits_isOfFinOrder_iff.mp
      (deningerAbsL2Inner_self_eq_zero u.ne_zero h)

/-- **The additive form on the Kummer group is definite.** -/
theorem deningerKummerAddL2Inner_self_eq_zero {a : deningerKummerAdd F}
    (h : deningerKummerAddL2Inner a a = 0) : a = 0 :=
  deningerKummerL2Inner_self_eq_zero h

/-- **The form on the Kummer space is definite.** -/
theorem deningerSpaceL2Inner_self_eq_zero {x : deningerKummerSpace F}
    (h : deningerSpaceL2Inner x x = 0) : x = 0 := by
  induction x using DivisibleHull.ind with
  | mk m s =>
    rw [deningerSpaceL2Inner_mk, div_eq_zero_iff] at h
    have hs : ((s : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr s.ne_zero
    have hprod : ((s : ℕ) : ℝ) * ((s : ℕ) : ℝ) ≠ 0 := mul_ne_zero hs hs
    have hm : deningerKummerAddL2Inner m m = 0 := h.resolve_right hprod
    rw [deningerKummerAddL2Inner_self_eq_zero hm, DivisibleHull.mk_zero]

end KummerDefinite

end RHTower
