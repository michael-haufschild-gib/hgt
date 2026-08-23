import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.GroupTheory.MonoidLocalization.MonoidWithZero

/-!
# Extending a pointed multiplicative map to the fraction fields

A map `P : D → O` between integral domains which sends `0` to `0` and `1` to `1`, is
multiplicative, and vanishes only at `0` extends to a pointed multiplicative map of the fraction
fields by `P (a / b) = P a / P b`.  The extension is the lift of `P` along the localization of the
multiplicative monoid of `D` at its nonzero elements, so no additivity is needed anywhere.
-/

namespace HTGeometry

variable {D O K L : Type*}
variable [CommRing D] [IsDomain D] [Field K] [Algebra D K] [IsFractionRing D K]
variable [CommRing O] [IsDomain O] [Field L] [Algebra O L] [IsFractionRing O L]

/-- The map `D → L` obtained from a pointed multiplicative map `P : D → O`. -/
noncomputable def fractionMulComp (P : D →*₀ O) : D →*₀ L :=
  ((algebraMap O L).toMonoidWithZeroHom).comp P

omit [IsDomain D] [IsDomain O] [IsFractionRing O L] in
@[simp] theorem fractionMulComp_apply (P : D →*₀ O) (d : D) :
    fractionMulComp (L := L) P d = algebraMap O L (P d) := rfl

omit [IsDomain O] in
theorem fractionMulComp_isUnit (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0)
    (y : nonZeroDivisors D) : IsUnit (fractionMulComp (L := L) P y) := by
  have hy : (y : D) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 y.2
  have h1 : P (y : D) ≠ 0 := hP _ hy
  have h2 : algebraMap O L (P (y : D)) ≠ 0 := fun hc =>
    h1 ((injective_iff_map_eq_zero (algebraMap O L)).1 (IsFractionRing.injective O L) _ hc)
  exact isUnit_iff_ne_zero.2 h2

/-- **The extension of a pointed multiplicative map to the fraction fields.**  It is the lift of
`P` along the localization of the multiplicative monoid of `D` at the nonzero elements. -/
noncomputable def fractionMulExtend (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0) : K →*₀ L :=
  (IsLocalization.toLocalizationMap (nonZeroDivisors D) K).lift₀
    (fractionMulComp P) (fractionMulComp_isUnit P hP)

omit [IsDomain O] in
@[simp] theorem fractionMulExtend_algebraMap (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0)
    (d : D) : fractionMulExtend (K := K) (L := L) P hP (algebraMap D K d) = algebraMap O L (P d) :=
  (IsLocalization.toLocalizationMap (nonZeroDivisors D) K).lift_eq
    (fractionMulComp_isUnit P hP) d

omit [IsDomain O] in
theorem fractionMulExtend_ne_zero (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0) {t : K}
    (ht : t ≠ 0) : fractionMulExtend (L := L) P hP t ≠ 0 := by
  have hu : IsUnit t := isUnit_iff_ne_zero.2 ht
  exact isUnit_iff_ne_zero.1 (hu.map (fractionMulExtend (L := L) P hP))

omit [IsDomain O] in
theorem fractionMulExtend_eq_zero_iff (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0) (t : K) :
    fractionMulExtend (L := L) P hP t = 0 ↔ t = 0 := by
  constructor
  · intro h
    by_contra hne
    exact fractionMulExtend_ne_zero P hP hne h
  · rintro rfl
    exact map_zero _

omit [IsDomain O] in
/-- **The extension is the unique pointed multiplicative map restricting to `P`.**  Any two such
maps agree on a ratio because they agree on numerator and denominator and the denominator has
nonzero image. -/
theorem eq_fractionMulExtend (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0) (F : K →*₀ L)
    (hF : ∀ d : D, F (algebraMap D K d) = algebraMap O L (P d)) :
    F = fractionMulExtend P hP := by
  refine MonoidWithZeroHom.ext fun t => ?_
  obtain ⟨⟨d₁, d₂⟩, e⟩ := IsLocalization.surj (M := nonZeroDivisors D) (S := K) t
  have hd₂ : (d₂ : D) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 d₂.2
  have hne : algebraMap O L (P (d₂ : D)) ≠ 0 := fun hc =>
    hP _ hd₂ ((injective_iff_map_eq_zero (algebraMap O L)).1 (IsFractionRing.injective O L) _ hc)
  have h1 : F t * algebraMap O L (P (d₂ : D)) = algebraMap O L (P d₁) := by
    rw [← hF, ← hF, ← map_mul, e]
  have h2 : fractionMulExtend (L := L) P hP t * algebraMap O L (P (d₂ : D))
      = algebraMap O L (P d₁) := by
    rw [← fractionMulExtend_algebraMap (K := K) P hP (d₂ : D),
      ← fractionMulExtend_algebraMap (K := K) P hP d₁, ← map_mul, e]
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

/-- The character of the units induced by the extension. -/
noncomputable def fractionMulExtendUnits (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0) :
    Kˣ →* Lˣ :=
  Units.map (fractionMulExtend (K := K) (L := L) P hP).toMonoidHom

omit [IsDomain O] in
@[simp] theorem fractionMulExtendUnits_coe (P : D →*₀ O) (hP : ∀ d : D, d ≠ 0 → P d ≠ 0)
    (u : Kˣ) :
    ((fractionMulExtendUnits (L := L) P hP u : Lˣ) : L) = fractionMulExtend P hP (u : K) := rfl

end HTGeometry
