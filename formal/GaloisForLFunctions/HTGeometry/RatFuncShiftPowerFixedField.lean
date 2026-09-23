import GaloisForLFunctions.HTGeometry.RatFuncFieldShiftEquiv

/-!
# Fixed field of positive powers of rational translation

Over a characteristic-zero field, every positive iterate of the unit translation on `F(X)` has
fixed field exactly `F`.  Coordinate dilation reduces translation by the nonzero integer period to
the unit-shift fixed-field theorem.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry.FieldShift

noncomputable section

universe u

variable {F : Type u} [Field F]

theorem natDegree_C_mul_X_field {ω : F} (hω : ω ≠ 0) :
    (Polynomial.C ω * Polynomial.X).natDegree = 1 := by
  rw [Polynomial.natDegree_C_mul hω, Polynomial.natDegree_X]

theorem leadingCoeff_C_mul_X_field (ω : F) :
    (Polynomial.C ω * Polynomial.X).leadingCoeff = ω := by
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, mul_one]

theorem comp_C_mul_X_ne_zero_field {ω : F} (hω : ω ≠ 0)
    {p : Polynomial F} (hp : p ≠ 0) :
    p.comp (Polynomial.C ω * Polynomial.X) ≠ 0 := by
  intro hzero
  have hlead : (p.comp (Polynomial.C ω * Polynomial.X)).leadingCoeff
      = p.leadingCoeff * ω ^ p.natDegree := by
    rw [Polynomial.leadingCoeff_comp
      (by rw [natDegree_C_mul_X_field hω]; exact one_ne_zero),
      leadingCoeff_C_mul_X_field]
  rw [hzero, Polynomial.leadingCoeff_zero] at hlead
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (pow_ne_zero _ hω)) hlead.symm

/-- Composition with `X ↦ ωX`, as a homomorphism into the rational-function field. -/
def scaleCompHomField (ω : F) : Polynomial F →+* RatFunc F :=
  (algebraMap (Polynomial F) (RatFunc F)).comp
    (Polynomial.aeval (Polynomial.C ω * Polynomial.X) :
      Polynomial F →ₐ[F] Polynomial F).toRingHom

theorem scaleCompHomField_apply (ω : F) (p : Polynomial F) :
    scaleCompHomField ω p =
      algebraMap (Polynomial F) (RatFunc F)
        (p.comp (Polynomial.C ω * Polynomial.X)) := by
  rw [scaleCompHomField, RingHom.comp_apply]
  rfl

theorem scaleCompHomField_mem_nonZeroDivisors {ω : F} (hω : ω ≠ 0) :
    nonZeroDivisors (Polynomial F) ≤
      Submonoid.comap (scaleCompHomField ω) (nonZeroDivisors (RatFunc F)) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [scaleCompHomField_apply]
  intro h0
  exact comp_C_mul_X_ne_zero_field hω hp
    (RatFunc.algebraMap_injective F (by rw [h0, map_zero]))

/-- Coordinate dilation `r(X) ↦ r(ωX)`. -/
def ratScaleByField (ω : F) (hω : ω ≠ 0) : RatFunc F →+* RatFunc F :=
  RatFunc.liftRingHom (scaleCompHomField ω) (scaleCompHomField_mem_nonZeroDivisors hω)

theorem ratScaleByField_algebraMap {ω : F} (hω : ω ≠ 0) (p : Polynomial F) :
    ratScaleByField ω hω (algebraMap (Polynomial F) (RatFunc F) p) =
      algebraMap (Polynomial F) (RatFunc F)
        (p.comp (Polynomial.C ω * Polynomial.X)) := by
  have h := RatFunc.liftRingHom_apply_div (scaleCompHomField ω)
    (scaleCompHomField_mem_nonZeroDivisors hω) p 1
  simp only [map_one, div_one] at h
  rw [ratScaleByField, h, scaleCompHomField_apply]

theorem ratScaleByField_const {ω : F} (hω : ω ≠ 0) (t : F) :
    ratScaleByField ω hω (algebraMap F (RatFunc F) t) =
      algebraMap F (RatFunc F) t := by
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F) t,
    Polynomial.algebraMap_eq, ratScaleByField_algebraMap hω, Polynomial.C_comp]

/-- Dilation conjugates translation by `ω` to unit translation. -/
theorem ratScaleByField_ratShiftOf {ω : F} (hω : ω ≠ 0) (r : RatFunc F) :
    ratScaleByField ω hω (ratShiftOf ω r) =
      ratShift (ratScaleByField ω hω r) := by
  have hhom : (ratScaleByField ω hω).comp (ratShiftOf ω) =
      ratShift.comp (ratScaleByField ω hω) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial F)
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply, ratShiftOf_algebraMap,
      ratScaleByField_algebraMap hω, ratScaleByField_algebraMap hω,
      ratShift_algebraMap]
    congr 1
    rw [Polynomial.comp_assoc, Polynomial.comp_assoc]
    congr 1
    rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
    simp only [Polynomial.C_1]
    ring
  exact RingHom.congr_fun hhom r

/-- Translation by any nonzero field element has only constant rational invariants. -/
theorem ratShiftOf_fixed_eq_const [CharZero F] {ω : F} (hω : ω ≠ 0)
    {r : RatFunc F} (h : ratShiftOf ω r = r) :
    ∃ t : F, r = algebraMap F (RatFunc F) t := by
  have hfix : ratShift (ratScaleByField ω hω r) = ratScaleByField ω hω r := by
    rw [← ratScaleByField_ratShiftOf hω, h]
  obtain ⟨t, ht⟩ := ratShift_fixed_eq_const hfix
  refine ⟨t, (ratScaleByField ω hω).injective ?_⟩
  rw [ht, ratScaleByField_const hω]

/-- The `n`-th power of unit translation is translation by the natural-number scalar `n`. -/
theorem ratShiftEquiv_pow_apply (n : ℕ) (r : RatFunc F) :
    (ratShiftEquiv ^ n) r = ratShiftOf (n : F) r := by
  induction n with
  | zero =>
      simpa only [Nat.cast_zero] using
        (show (ratShiftEquiv ^ (0 : ℕ)) r = ratShiftOf (0 : F) r from by
          calc
            (ratShiftEquiv ^ (0 : ℕ)) r = r := by rw [pow_zero]; rfl
            _ = ratShiftOf (0 : F) r := (ratShiftOf_zero r).symm)
  | succ n ih =>
      rw [pow_succ']
      change ratShiftEquiv ((ratShiftEquiv ^ n) r) = ratShiftOf (↑(n + 1) : F) r
      rw [ih, ratShiftEquiv_apply, ← ratShiftOf_one_eq,
        ratShiftOf_ratShiftOf]
      congr 2
      push_cast
      ring

/-- Every positive power of unit translation on `F(X)` has fixed field `F`. -/
theorem ratShiftEquiv_pow_fixed_eq_const [CharZero F]
    {n : ℕ} (hn : 0 < n) {r : RatFunc F}
    (h : (ratShiftEquiv ^ n) r = r) :
    ∃ t : F, r = algebraMap F (RatFunc F) t := by
  apply ratShiftOf_fixed_eq_const (Nat.cast_ne_zero.mpr (ne_of_gt hn))
  rwa [← ratShiftEquiv_pow_apply]

end

end GaloisForLFunctions.HTGeometry.FieldShift
