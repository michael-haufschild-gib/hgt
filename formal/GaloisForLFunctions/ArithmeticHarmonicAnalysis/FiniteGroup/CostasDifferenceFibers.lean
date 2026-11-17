import Mathlib.FieldTheory.Finite.Basic

/-!
# Exact diagonal difference fibers

For every additive automorphism L of a field, the diagonal (L(t), t) has
unique differences off the two identity axes. Over a finite field the full
multiplicity law is q·1 + G − E − H, the classical diagonal model in
Low–Schmidt, arXiv:2611.20974, equation (2).
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Costas
variable {F : Type*} [Field F] (L : F ≃+ F)
local instance : DecidableEq F := Classical.decEq F

private theorem ratio_sub_one_ne {r : Fˣ} (hr : r ≠ 1) : (r : F) - 1 ≠ 0 := by
  intro h
  apply hr
  exact Units.ext (sub_eq_zero.mp h)

/-- Every nonidentity multiplicative direction gives an additive permutation of differences. -/
def differenceEquiv (r : Fˣ) (hr : r ≠ 1) : F ≃+ F where
  toFun t := L (((r : F) - 1) * t)
  invFun x := ((r : F) - 1)⁻¹ * L.symm x
  left_inv t := by
    change ((r : F) - 1)⁻¹ * L.symm (L (((r : F) - 1) * t)) = t
    rw [L.symm_apply_apply, ← mul_assoc, inv_mul_cancel₀ (ratio_sub_one_ne hr), one_mul]
  right_inv x := by
    change L (((r : F) - 1) * (((r : F) - 1)⁻¹ * L.symm x)) = x
    rw [← mul_assoc, mul_inv_cancel₀ (ratio_sub_one_ne hr), one_mul, L.apply_symm_apply]
  map_add' s t := by rw [mul_add, map_add]

theorem differenceEquiv_apply (r : Fˣ) (hr : r ≠ 1) (t : F) :
    differenceEquiv L r hr t = L ((r : F) * t) - L t := by
  change L (((r : F) - 1) * t) = _
  rw [sub_mul, one_mul, map_sub]

/-- Fibers of the difference map on the additive/multiplicative diagonal. -/
def DifferenceFiber (x : F) (r : Fˣ) :=
  {st : Fˣ × Fˣ // L (st.1 : F) - L (st.2 : F) = x ∧ st.1 / st.2 = r}

/-- Off the two identity axes, every difference has a unique ordered representation. -/
theorem unique_difference (x : F) (r : Fˣ) (hx : x ≠ 0) (hr : r ≠ 1) :
    ∃! st : Fˣ × Fˣ, L (st.1 : F) - L (st.2 : F) = x ∧ st.1 / st.2 = r := by
  let D := differenceEquiv L r hr
  have ht : D.symm x ≠ 0 := by
    intro h
    apply hx
    rw [← D.apply_symm_apply x, h, map_zero]
  let t : Fˣ := Units.mk0 (D.symm x) ht
  have hd : L (((r * t : Fˣ) : F)) - L (t : F) = x := by
    change L ((r : F) * D.symm x) - L (D.symm x) = x
    rw [← differenceEquiv_apply L r hr]
    exact D.apply_symm_apply x
  refine ⟨(r * t, t), ⟨hd, by simp⟩, ?_⟩
  rintro ⟨s, u⟩ ⟨hxu, hru⟩
  have hs : s = r * u := by
    have h := congrArg (fun z : Fˣ => z * u) hru
    simpa only [div_eq_mul_inv, mul_assoc, inv_mul_cancel, mul_one] using h
  have hu : u = t := by
    apply Units.ext
    apply D.injective
    change differenceEquiv L r hr (u : F) = differenceEquiv L r hr (D.symm x)
    rw [differenceEquiv_apply, D.apply_symm_apply]
    rw [hs] at hxu
    exact hxu
  exact Prod.ext (by rw [hs, hu]) hu

/-- A zero additive displacement forces the identity multiplicative ratio. -/
theorem zero_displacement_ratio (st : Fˣ × Fˣ)
    (h : L (st.1 : F) - L (st.2 : F) = 0) : st.1 / st.2 = 1 := by
  have hst : st.1 = st.2 := Units.ext (L.injective (sub_eq_zero.mp h))
  simp [hst]

/-- The identity fiber is exactly the diagonal of the nonzero field elements. -/
def identityFiberEquiv : DifferenceFiber L 0 1 ≃ Fˣ where
  toFun st := st.val.2
  invFun t := ⟨(t, t), by simp⟩
  left_inv st := by
    apply Subtype.ext
    apply Prod.ext
    · exact (Units.ext (L.injective (sub_eq_zero.mp st.property.1))).symm
    · rfl
  right_inv t := rfl

/-- Nontrivial ratios and zero displacement never occur together. -/
theorem zeroFiber_empty (r : Fˣ) (hr : r ≠ 1) : IsEmpty (DifferenceFiber L 0 r) :=
  ⟨fun st => hr (st.property.2.symm.trans (zero_displacement_ratio L st.val st.property.1))⟩

/-- A nonzero displacement cannot have identity ratio. -/
theorem identityRatio_empty (x : F) (hx : x ≠ 0) : IsEmpty (DifferenceFiber L x 1) := by
  refine ⟨fun st => ?_⟩
  have hs : st.val.1 = st.val.2 := div_eq_one.mp st.property.2
  apply hx
  have h := st.property.1
  rw [hs, sub_self] at h
  exact h.symm

/-- A nondegenerate difference fiber has cardinality exactly one, without enumeration. -/
theorem nondegenerateFiber_card (x : F) (r : Fˣ) (hx : x ≠ 0) (hr : r ≠ 1) :
    Nat.card (DifferenceFiber L x r) = 1 := by
  obtain ⟨st, hst, hu⟩ := unique_difference L x r hx hr
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨fun a b => Subtype.ext ((hu a.val a.property).trans (hu b.val b.property).symm)⟩,
    ⟨⟨st, hst⟩⟩⟩

/-- Complete difference multiplicity, including both degenerate axes. -/
theorem differenceFiber_card (x : F) (r : Fˣ) :
    Nat.card (DifferenceFiber L x r) =
      if x = 0 then (if r = 1 then Nat.card F - 1 else 0)
      else (if r = 1 then 0 else 1) := by
  classical
  by_cases hx : x = 0
  · subst x
    by_cases hr : r = 1
    · subst r
      simp only
      exact (Nat.card_congr (identityFiberEquiv L)).trans (Nat.card_units F)
    · letI := zeroFiber_empty L r hr
      simp [hr]
  · by_cases hr : r = 1
    · subst r
      letI := identityRatio_empty L x hx
      simp [hx]
    · simpa only [if_neg hx, if_neg hr] using nondegenerateFiber_card L x r hx hr

/-- Coefficientwise divided-difference-set identity: q·1 + G - E - H. -/
theorem differenceFiber_groupRing_coeff [Finite F] (x : F) (r : Fˣ) :
    (Nat.card (DifferenceFiber L x r) : ℤ) =
      (Nat.card F : ℤ) * (if x = 0 ∧ r = 1 then 1 else 0) + 1 -
        (if r = 1 then 1 else 0) - (if x = 0 then 1 else 0) := by
  classical
  have hcard : 1 ≤ Nat.card F := by
    letI := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos
  rw [differenceFiber_card]
  by_cases hx : x = 0 <;> by_cases hr : r = 1 <;>
    simp [hx, hr, Nat.cast_sub hcard]

#print axioms differenceFiber_card
#print axioms differenceFiber_groupRing_coeff
#print axioms unique_difference
#print axioms identityFiberEquiv
#print axioms nondegenerateFiber_card
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Costas
