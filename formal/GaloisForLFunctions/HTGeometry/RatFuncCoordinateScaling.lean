import GaloisForLFunctions.HTGeometry.ShiftedDigammaFamilyIncrement
import GaloisForLFunctions.HTGeometry.TranslationStableDifferentialAlgebraicity

/-!
# Dilating the coordinate conjugates one shift into another

Composition with `X ↦ ωX` is an automorphism of `ℂ(X)` for `ω ≠ 0`, and it conjugates the
translation by `ω` into the unit translation:

```text
(r(X + ω))(ωX) = r(ωX + ω) = (r(ωX))(X + 1).
```

It fixes the constants and carries the jet increments of a simple pole to those of the dilated pole
up to a power of `ω`:

```text
((-1)^j j! / (X + b)^{j+1})(ωX) = ω^{-(j+1)} · (-1)^j j! / (X + b/ω)^{j+1}.
```

The unit-shift orbit-residue theorem therefore transfers verbatim to the translation by any nonzero
`ω`: for shifts pairwise incongruent modulo `ωℤ`, no nonzero constant charge matrix on the increment
jets is an `ω`-shift coboundary.  Shift-invariant rational functions are constant for the same
reason.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-! ## The dilation of the coordinate -/

theorem natDegree_C_mul_X {ω : ℂ} (hω : ω ≠ 0) :
    (Polynomial.C ω * Polynomial.X).natDegree = 1 := by
  rw [Polynomial.natDegree_C_mul hω, Polynomial.natDegree_X]

theorem leadingCoeff_C_mul_X (ω : ℂ) :
    (Polynomial.C ω * Polynomial.X).leadingCoeff = ω := by
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, mul_one]

theorem comp_C_mul_X_ne_zero {ω : ℂ} (hω : ω ≠ 0) {p : Polynomial ℂ} (hp : p ≠ 0) :
    p.comp (Polynomial.C ω * Polynomial.X) ≠ 0 := by
  intro hzero
  have hlead : (p.comp (Polynomial.C ω * Polynomial.X)).leadingCoeff
      = p.leadingCoeff * ω ^ p.natDegree := by
    rw [Polynomial.leadingCoeff_comp (by rw [natDegree_C_mul_X hω]; exact one_ne_zero),
      leadingCoeff_C_mul_X]
  rw [hzero, Polynomial.leadingCoeff_zero] at hlead
  exact (mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (pow_ne_zero _ hω)) hlead.symm

/-- Composition with the dilation `X ↦ ωX`, as a map from polynomials into `ℂ(X)`. -/
def scaleCompHom (ω : ℂ) : Polynomial ℂ →+* RatFunc ℂ :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp
    (Polynomial.aeval (Polynomial.C ω * Polynomial.X) :
      Polynomial ℂ →ₐ[ℂ] Polynomial ℂ).toRingHom

theorem scaleCompHom_apply (ω : ℂ) (p : Polynomial ℂ) :
    scaleCompHom ω p
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (Polynomial.C ω * Polynomial.X)) := by
  rw [scaleCompHom, RingHom.comp_apply]
  rfl

theorem scaleCompHom_mem_nonZeroDivisors {ω : ℂ} (hω : ω ≠ 0) :
    nonZeroDivisors (Polynomial ℂ)
      ≤ Submonoid.comap (scaleCompHom ω) (nonZeroDivisors (RatFunc ℂ)) := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [scaleCompHom_apply]
  intro h0
  exact comp_C_mul_X_ne_zero hω hp
    (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))

/-- The dilation endomorphism `r(X) ↦ r(ωX)` of the rational function field. -/
def ratScaleBy (ω : ℂ) (hω : ω ≠ 0) : RatFunc ℂ →+* RatFunc ℂ :=
  RatFunc.liftRingHom (scaleCompHom ω) (scaleCompHom_mem_nonZeroDivisors hω)

theorem ratScaleBy_algebraMap {ω : ℂ} (hω : ω ≠ 0) (p : Polynomial ℂ) :
    ratScaleBy ω hω (algebraMap (Polynomial ℂ) (RatFunc ℂ) p)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ)
        (p.comp (Polynomial.C ω * Polynomial.X)) := by
  have h := RatFunc.liftRingHom_apply_div (scaleCompHom ω)
    (scaleCompHom_mem_nonZeroDivisors hω) p 1
  simp only [map_one, div_one] at h
  rw [ratScaleBy, h, scaleCompHom_apply]

theorem ratScaleBy_const {ω : ℂ} (hω : ω ≠ 0) (t : ℂ) :
    ratScaleBy ω hω (algebraMap ℂ (RatFunc ℂ) t) = algebraMap ℂ (RatFunc ℂ) t := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ) t, Polynomial.algebraMap_eq,
    ratScaleBy_algebraMap hω, Polynomial.C_comp]

theorem ratScaleBy_ratFuncC {ω : ℂ} (hω : ω ≠ 0) (t : ℂ) :
    ratScaleBy ω hω (RatFunc.C t) = RatFunc.C t := by
  rw [← RatFunc.algebraMap_C, ratScaleBy_algebraMap hω, Polynomial.C_comp]

theorem ratScaleBy_ratFuncX {ω : ℂ} (hω : ω ≠ 0) :
    ratScaleBy ω hω RatFunc.X = RatFunc.C ω * RatFunc.X := by
  rw [← RatFunc.algebraMap_X, ratScaleBy_algebraMap hω, Polynomial.X_comp, map_mul,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X]

/-! ## The dilation conjugates the shifts -/

/-- **Dilating the coordinate turns the translation by `ω` into the unit translation.** -/
theorem ratScaleBy_ratShiftBy {ω : ℂ} (hω : ω ≠ 0) (r : RatFunc ℂ) :
    ratScaleBy ω hω (ratShiftBy ω r) = ratShift (ratScaleBy ω hω r) := by
  have hhom : (ratScaleBy ω hω).comp (ratShiftBy ω)
      = ratShift.comp (ratScaleBy ω hω) := by
    apply IsFractionRing.ringHom_ext (A := Polynomial ℂ)
    intro p
    rw [RingHom.comp_apply, RingHom.comp_apply, ratShiftBy_algebraMap, ratScaleBy_algebraMap hω,
      ratScaleBy_algebraMap hω, ratShift_algebraMap]
    congr 1
    rw [Polynomial.comp_assoc, Polynomial.comp_assoc]
    congr 1
    rw [Polynomial.add_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.mul_comp,
      Polynomial.C_comp, Polynomial.X_comp]
    simp only [Polynomial.C_1]
    ring
  exact RingHom.congr_fun hhom r

/-- **Shift-invariant rational functions are constant, for every nonzero shift.** -/
theorem ratShiftBy_fixed_eq_const {ω : ℂ} (hω : ω ≠ 0) {r : RatFunc ℂ}
    (h : ratShiftBy ω r = r) : ∃ t : ℂ, r = algebraMap ℂ (RatFunc ℂ) t := by
  have hfix : ratShift (ratScaleBy ω hω r) = ratScaleBy ω hω r := by
    rw [← ratScaleBy_ratShiftBy hω, h]
  obtain ⟨t, ht⟩ := ratShift_fixed_eq_const hfix
  refine ⟨t, (ratScaleBy ω hω).injective ?_⟩
  rw [ht, ratScaleBy_const hω]

/-! ## The increments under dilation -/

theorem algebraMap_eq_ratFuncC (t : ℂ) :
    algebraMap ℂ (RatFunc ℂ) t = RatFunc.C t := by
  rw [IsScalarTower.algebraMap_apply ℂ (Polynomial ℂ) (RatFunc ℂ), Polynomial.algebraMap_eq,
    RatFunc.algebraMap_C]

theorem ratFuncC_ne_zero {t : ℂ} (ht : t ≠ 0) : (RatFunc.C t : RatFunc ℂ) ≠ 0 := by
  rw [← RatFunc.algebraMap_C]
  exact RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr ht)

/-- **The jet increments of a simple pole scale by a power of the dilation factor.** -/
theorem ratScaleBy_familyIncrement {ω : ℂ} (hω : ω ≠ 0) {r : ℕ} (b : Fin r → ℂ) (i : Fin r)
    (j : ℕ) :
    ratScaleBy ω hω (familyIncrement b i j)
      = RatFunc.C (ω⁻¹ ^ (j + 1)) * familyIncrement (fun i => b i / ω) i j := by
  have hfac : RatFunc.C ω * RatFunc.X + RatFunc.C (b i)
      = RatFunc.C ω * (RatFunc.X + RatFunc.C (b i / ω)) := by
    rw [mul_add, ← map_mul]
    congr 2
    field_simp
  have hinv : RatFunc.C (ω⁻¹ ^ (j + 1)) = ((RatFunc.C ω : RatFunc ℂ) ^ (j + 1))⁻¹ := by
    rw [inv_pow, map_inv₀, map_pow]
  rw [familyIncrement, familyIncrement, map_div₀, map_pow, map_add, ratScaleBy_ratFuncC hω,
    ratScaleBy_ratFuncC hω, ratScaleBy_ratFuncX hω, hfac, mul_pow, hinv,
    div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-! ## The orbit-residue theorem for an arbitrary shift -/

/-- **No nonzero constant charge matrix on the increments is an `ω`-shift coboundary.**  Dilating
the coordinate reduces the statement to the unit shift, where pairwise incongruence modulo `ωℤ`
becomes pairwise incongruence modulo `ℤ`. -/
theorem ratShiftBy_sub_familyIncrement_combination {ω : ℂ} (hω : ω ≠ 0) {r : ℕ} (b : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, b i - b i' ≠ (n : ℂ) * ω)
    {N : ℕ} {w : RatFunc ℂ} {delta : Fin r → Fin (N + 1) → ℂ}
    (h : ratShiftBy ω w - w = ∑ i : Fin r, ∑ j : Fin (N + 1),
      algebraMap ℂ (RatFunc ℂ) (delta i j) * familyIncrement b i (j : ℕ)) :
    ∀ i j, delta i j = 0 := by
  have hincong' : ∀ i i' : Fin r, i ≠ i' → ∀ n : ℤ, b i / ω - b i' / ω ≠ (n : ℂ) := by
    intro i i' hii n hcon
    refine hincong i i' hii n ?_
    field_simp at hcon
    linear_combination hcon
  have hscaled : ratShift (ratScaleBy ω hω w) - ratScaleBy ω hω w
      = ∑ i : Fin r, ∑ j : Fin (N + 1),
        algebraMap ℂ (RatFunc ℂ) (delta i j * ω⁻¹ ^ ((j : ℕ) + 1)) *
          familyIncrement (fun i => b i / ω) i (j : ℕ) := by
    have hC : ∀ t : ℂ, algebraMap ℂ (RatFunc ℂ) t = RatFunc.C t := algebraMap_eq_ratFuncC
    have := congrArg (ratScaleBy ω hω) h
    rw [map_sub, ratScaleBy_ratShiftBy hω] at this
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ratScaleBy_const hω, ratScaleBy_familyIncrement hω, hC, hC, map_mul, mul_assoc]
  have hzero := ratShift_sub_familyIncrement_combination (fun i => b i / ω) hincong' hscaled
  intro i j
  have := hzero i j
  rcases mul_eq_zero.mp this with h1 | h2
  · exact h1
  · exact absurd h2 (pow_ne_zero _ (inv_ne_zero hω))

end

end GaloisForLFunctions.HTGeometry
