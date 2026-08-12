import GaloisForLFunctions.RHTower.BurnolSoninEvenCosineAperture

/-!
# Suzuki's literal positive-half-line `L²` carrier

Suzuki's Hankel operator acts on `L²((0,∞), dx)`.  The existing Mellin--Plancherel stack uses the
unitarily equivalent even subspace of `L²(ℝ, dx)`.  This file closes that carrier seam rather than
treating the identification as notation.

The forward unitary restricts an even function to the positive ray and multiplies it by `sqrt 2`.
Its inverse zero-extends a positive-ray class, reflects it, and divides the sum by `sqrt 2`.
All maps are constructed in `Lp`, so representative choices disappear through almost-everywhere
equality.  The resulting equivalence is the literal Hilbert-space identification used below to
transport Suzuki's operator back to `L²((0,∞), dx)`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace RHTower

/-- Suzuki's literal physical Hilbert space `L²((0,∞), dx)`, represented as Lebesgue `Lp` on the
positive ray. -/
abbrev SuzukiPositiveL2 := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

private theorem suzukiSqrtTwo_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'

/-! ## Zero extension from the positive ray -/

def suzukiPositiveZeroExtensionFun (g : SuzukiPositiveL2) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator fun x => g x

theorem memLp_suzukiPositiveZeroExtensionFun (g : SuzukiPositiveL2) :
    MemLp (suzukiPositiveZeroExtensionFun g) 2 (volume : Measure ℝ) := by
  rw [suzukiPositiveZeroExtensionFun,
    memLp_indicator_iff_restrict measurableSet_Ioi]
  exact Lp.memLp g

def suzukiPositiveZeroExtension (g : SuzukiPositiveL2) : SoninL2 :=
  (memLp_suzukiPositiveZeroExtensionFun g).toLp _

theorem suzukiPositiveZeroExtension_ae (g : SuzukiPositiveL2) :
    suzukiPositiveZeroExtension g =ᵐ[volume] suzukiPositiveZeroExtensionFun g :=
  (memLp_suzukiPositiveZeroExtensionFun g).coeFn_toLp

theorem norm_suzukiPositiveZeroExtension (g : SuzukiPositiveL2) :
    ‖suzukiPositiveZeroExtension g‖ = ‖g‖ := by
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (suzukiPositiveZeroExtension_ae g),
    suzukiPositiveZeroExtensionFun,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ioi]

def suzukiPositiveZeroExtensionLinear : SuzukiPositiveL2 →ₗ[ℂ] SoninL2 where
  toFun := suzukiPositiveZeroExtension
  map_add' f g := by
    apply Lp.ext
    have hinput := Lp.coeFn_add f g
    rw [ae_restrict_iff' measurableSet_Ioi] at hinput
    filter_upwards [suzukiPositiveZeroExtension_ae (f + g),
      suzukiPositiveZeroExtension_ae f,
      suzukiPositiveZeroExtension_ae g,
      Lp.coeFn_add (suzukiPositiveZeroExtension f)
        (suzukiPositiveZeroExtension g), hinput] with x hout hf hg hsum hin
    rw [hout, hsum, hf, hg]
    simp only [Pi.add_apply]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [suzukiPositiveZeroExtensionFun, indicator_of_mem hx]
      rw [hin hx]
    · simp [suzukiPositiveZeroExtensionFun, hx]
  map_smul' c f := by
    apply Lp.ext
    have hinput := Lp.coeFn_smul c f
    rw [ae_restrict_iff' measurableSet_Ioi] at hinput
    filter_upwards [suzukiPositiveZeroExtension_ae (c • f),
      suzukiPositiveZeroExtension_ae f,
      Lp.coeFn_smul c (suzukiPositiveZeroExtension f), hinput] with x hout hf hsum hin
    rw [hout]
    simp only [RingHom.id_apply]
    rw [hsum]
    simp only [Pi.smul_apply, smul_eq_mul, hf]
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · simp only [suzukiPositiveZeroExtensionFun, indicator_of_mem hx]
      rw [hin hx]
      rfl
    · simp [suzukiPositiveZeroExtensionFun, hx]

/-! ## Normalized restriction of the even carrier -/

/-- Restriction to the positive ray, normalized by `sqrt 2` to preserve the full even `L²` norm. -/
def suzukiPositiveRestriction (f : evenSubspace) : SuzukiPositiveL2 :=
  ((Real.sqrt 2 : ℝ) : ℂ) • soninHalfLine (f : SoninL2)

theorem suzukiPositiveRestriction_ae (f : evenSubspace) :
    suzukiPositiveRestriction f =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x => ((Real.sqrt 2 : ℝ) : ℂ) * f.1 x := by
  filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℝ) : ℂ)
      (soninHalfLine (f : SoninL2)),
    coeFn_soninHalfLine (f : SoninL2)] with x hsmul hrestrict
  rw [suzukiPositiveRestriction, hsmul, hrestrict]
  rfl

def suzukiPositiveRestrictionLinear : evenSubspace →ₗ[ℂ] SuzukiPositiveL2 where
  toFun := suzukiPositiveRestriction
  map_add' f g := by
    change ((Real.sqrt 2 : ℝ) : ℂ) • soninHalfLine ((f + g : evenSubspace).1) =
      ((Real.sqrt 2 : ℝ) : ℂ) • soninHalfLine f.1 +
        ((Real.sqrt 2 : ℝ) : ℂ) • soninHalfLine g.1
    change ((Real.sqrt 2 : ℝ) : ℂ) •
        ((Lp.memLp (f.1 + g.1)).restrict (Ioi (0 : ℝ))).toLp (f.1 + g.1) = _
    rw [Lp_toLp_restrict_add, smul_add]
  map_smul' c f := by
    change ((Real.sqrt 2 : ℝ) : ℂ) • soninHalfLine ((c • f : evenSubspace).1) =
      (RingHom.id ℂ) c • (((Real.sqrt 2 : ℝ) : ℂ) • soninHalfLine f.1)
    change ((Real.sqrt 2 : ℝ) : ℂ) •
        ((Lp.memLp (c • f.1)).restrict (Ioi (0 : ℝ))).toLp (c • f.1) = _
    rw [Lp_toLp_restrict_smul, RingHom.id_apply]
    module

theorem norm_suzukiPositiveRestriction (f : evenSubspace) :
    ‖suzukiPositiveRestriction f‖ = ‖f‖ := by
  rw [suzukiPositiveRestriction, norm_smul,
    norm_soninHalfLine f.2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]
  change Real.sqrt 2 * (‖f.1‖ / Real.sqrt 2) = ‖f.1‖
  exact mul_div_cancel₀ _ (Real.sqrt_pos.mpr (by norm_num)).ne'

def suzukiPositiveRestrictionIsometry :
    evenSubspace →ₗᵢ[ℂ] SuzukiPositiveL2 where
  __ := suzukiPositiveRestrictionLinear
  norm_map' := norm_suzukiPositiveRestriction

/-! ## Explicit even extension and inverse laws -/

/-- Even extension of a positive-ray `L²` class, divided by `sqrt 2`. -/
def suzukiEvenExtension (g : SuzukiPositiveL2) : evenSubspace :=
  ⟨((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
      (suzukiPositiveZeroExtension g + l2Reflection (suzukiPositiveZeroExtension g)), by
    rw [mem_evenSubspace_iff]
    simp only [map_smul, map_add, l2Reflection_involutive]
    rw [add_comm]⟩

theorem suzukiEvenExtension_ae (g : SuzukiPositiveL2) :
    (suzukiEvenExtension g : SoninL2) =ᵐ[volume] fun x =>
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ *
        (suzukiPositiveZeroExtensionFun g x +
          suzukiPositiveZeroExtensionFun g (-x)) := by
  have hzeroNeg := (suzukiPositiveZeroExtension_ae g).comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
      (suzukiPositiveZeroExtension g + l2Reflection (suzukiPositiveZeroExtension g)),
    Lp.coeFn_add (suzukiPositiveZeroExtension g)
      (l2Reflection (suzukiPositiveZeroExtension g)),
    l2Reflection_ae (suzukiPositiveZeroExtension g),
    suzukiPositiveZeroExtension_ae g, hzeroNeg] with x hsmul hadd href hzero hzeroNeg
  change (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
      (suzukiPositiveZeroExtension g + l2Reflection (suzukiPositiveZeroExtension g)) :
        SoninL2) x = _
  rw [hsmul, hadd, href, hzero, hzeroNeg]
  rfl

def suzukiEvenExtensionLinear : SuzukiPositiveL2 →ₗ[ℂ] evenSubspace where
  toFun := suzukiEvenExtension
  map_add' f g := by
    apply Subtype.ext
    change ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
        (suzukiPositiveZeroExtension (f + g) +
          l2Reflection (suzukiPositiveZeroExtension (f + g))) = _
    change ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
        (suzukiPositiveZeroExtensionLinear (f + g) +
          l2Reflection (suzukiPositiveZeroExtensionLinear (f + g))) = _
    rw [map_add, map_add, map_add]
    module
  map_smul' c f := by
    apply Subtype.ext
    change ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
        (suzukiPositiveZeroExtension (c • f) +
          l2Reflection (suzukiPositiveZeroExtension (c • f))) = _
    change ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
        (suzukiPositiveZeroExtensionLinear (c • f) +
          l2Reflection (suzukiPositiveZeroExtensionLinear (c • f))) = _
    rw [map_smul, map_smul, map_smul, RingHom.id_apply]
    module

theorem suzukiPositiveRestriction_evenExtension (g : SuzukiPositiveL2) :
    suzukiPositiveRestriction (suzukiEvenExtension g) = g := by
  apply Lp.ext
  filter_upwards [suzukiPositiveRestriction_ae (suzukiEvenExtension g),
    ae_restrict_of_ae (suzukiEvenExtension_ae g),
    ae_restrict_mem measurableSet_Ioi] with x hrestrict hext hx
  rw [hrestrict, hext]
  have hneg : -x ∉ Ioi (0 : ℝ) := by
    simpa only [mem_Ioi, not_lt] using (le_of_lt hx)
  rw [suzukiPositiveZeroExtensionFun, indicator_of_mem hx,
    indicator_of_notMem hneg, add_zero]
  rw [← mul_assoc, mul_inv_cancel₀ suzukiSqrtTwo_ne_zero, one_mul]

theorem suzukiEvenExtension_positiveRestriction (f : evenSubspace) :
    suzukiEvenExtension (suzukiPositiveRestriction f) = f := by
  apply Subtype.ext
  apply Lp.ext
  have hrestrict := suzukiPositiveRestriction_ae f
  rw [ae_restrict_iff' measurableSet_Ioi] at hrestrict
  have hrestrictNeg := hrestrict.comp_tendsto
    (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.tendsto_ae
  filter_upwards [suzukiEvenExtension_ae (suzukiPositiveRestriction f),
    hrestrict, hrestrictNeg, coeFn_even_ae f.2, volume.ae_ne (0 : ℝ)] with
      x hext hpos hneg heven hx0
  rw [hext]
  by_cases hx : 0 < x
  · have hxmem : x ∈ Ioi (0 : ℝ) := hx
    have hnegmem : -x ∉ Ioi (0 : ℝ) := by simp [hx.le]
    rw [suzukiPositiveZeroExtensionFun, indicator_of_mem hxmem,
      indicator_of_notMem hnegmem, add_zero, hpos hxmem,
      ← mul_assoc, inv_mul_cancel₀ suzukiSqrtTwo_ne_zero, one_mul]
  · have hxlt : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
    have hxnot : x ∉ Ioi (0 : ℝ) := by simpa only [mem_Ioi, not_lt] using hx.le
    have hnegmem : -x ∈ Ioi (0 : ℝ) := by simpa only [mem_Ioi] using neg_pos.mpr hxlt
    rw [suzukiPositiveZeroExtensionFun, indicator_of_notMem hxnot,
      indicator_of_mem hnegmem, zero_add, hneg hnegmem,
      ← mul_assoc, inv_mul_cancel₀ suzukiSqrtTwo_ne_zero, one_mul]
    exact heven.symm

/-- Exact unitary identification `L²_even(ℝ,dx) ≃ L²((0,∞),dx)` used by Suzuki's source. -/
def suzukiPositiveHalfLineUnitary : evenSubspace ≃ₗᵢ[ℂ] SuzukiPositiveL2 where
  __ := suzukiPositiveRestrictionIsometry
  invFun := suzukiEvenExtension
  left_inv := suzukiEvenExtension_positiveRestriction
  right_inv := suzukiPositiveRestriction_evenExtension

@[simp] theorem suzukiPositiveHalfLineUnitary_apply (f : evenSubspace) :
    suzukiPositiveHalfLineUnitary f = suzukiPositiveRestriction f := rfl

@[simp] theorem suzukiPositiveHalfLineUnitary_symm_apply (g : SuzukiPositiveL2) :
    suzukiPositiveHalfLineUnitary.symm g = suzukiEvenExtension g := rfl

end RHTower
