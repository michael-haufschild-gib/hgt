import GaloisForLFunctions.HTGeometry.RationalTubeGrowth
import GaloisForLFunctions.HTGeometry.UpperEndFilter

/-!
# Rational functions as germs at the upper end

A nonzero polynomial has no zeros above a height, so its germ at the upper end is a unit.  The
universal property of the rational function field then gives a ring homomorphism

`ℂ(X) → Germ upperEndFilter ℂ`,

which is what makes an evaluation of jet polynomials with rational coefficients an honest ring
homomorphism: the poles of the coefficients are invisible at the upper end.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A nonzero polynomial has no zeros above some height. -/
theorem exists_upperTail_polyEval_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
    ∃ H : ℝ, ∀ z : ℂ, H < z.im → q.eval z ≠ 0 := by
  classical
  have hfin : (Complex.im '' {x : ℂ | q.IsRoot x}).Finite :=
    (Polynomial.finite_setOf_isRoot hq).image _
  obtain ⟨B, hB⟩ := hfin.bddAbove
  refine ⟨B, fun z hz h0 => ?_⟩
  have hroot : q.IsRoot z := h0
  have hmem : z.im ∈ Complex.im '' {x : ℂ | q.IsRoot x} := ⟨z, hroot, rfl⟩
  exact absurd (hB hmem) (not_le.mpr hz)

/-- Polynomials evaluated as functions, viewed as germs at the upper end. -/
def polyGermHom : Polynomial ℂ →+* Germ upperEndFilter ℂ where
  toFun q := (Germ.coeRingHom upperEndFilter) (fun z => q.eval z)
  map_one' := by
    have : (fun z : ℂ => (1 : Polynomial ℂ).eval z) = (1 : ℂ → ℂ) := by
      funext z
      simp
    rw [this, map_one]
  map_mul' p q := by
    have : (fun z : ℂ => (p * q).eval z) = (fun z : ℂ => p.eval z) * (fun z : ℂ => q.eval z) := by
      funext z
      simp
    rw [this, map_mul]
  map_zero' := by
    have : (fun z : ℂ => (0 : Polynomial ℂ).eval z) = (0 : ℂ → ℂ) := by
      funext z
      simp
    rw [this, map_zero]
  map_add' p q := by
    have : (fun z : ℂ => (p + q).eval z) = (fun z : ℂ => p.eval z) + (fun z : ℂ => q.eval z) := by
      funext z
      simp
    rw [this, map_add]

@[simp] theorem polyGermHom_apply (q : Polynomial ℂ) :
    polyGermHom q = (Germ.coeRingHom upperEndFilter) (fun z => q.eval z) := rfl

/-- The germ of a nonzero polynomial at the upper end is a unit. -/
theorem isUnit_polyGermHom {q : Polynomial ℂ} (hq : q ≠ 0) : IsUnit (polyGermHom q) := by
  obtain ⟨H, hH⟩ := exists_upperTail_polyEval_ne_zero hq
  have hev : ∀ᶠ z in upperEndFilter, q.eval z ≠ 0 := by
    have hmem : upperTail H ∈ upperEndFilter :=
      upperEndFilter_basis.mem_of_mem (i := H) trivial
    filter_upwards [hmem] with z hz
    exact hH z hz
  refine ⟨⟨polyGermHom q, (Germ.coeRingHom upperEndFilter) (fun z => (q.eval z)⁻¹), ?_, ?_⟩, rfl⟩
  · rw [polyGermHom_apply, ← map_mul]
    have : ((fun z : ℂ => q.eval z) * fun z : ℂ => (q.eval z)⁻¹)
        =ᶠ[upperEndFilter] (1 : ℂ → ℂ) := by
      filter_upwards [hev] with z hz
      simp [Pi.mul_apply, mul_inv_cancel₀ hz]
    rw [show (Germ.coeRingHom upperEndFilter)
        ((fun z : ℂ => q.eval z) * fun z : ℂ => (q.eval z)⁻¹)
        = (Germ.coeRingHom upperEndFilter) (1 : ℂ → ℂ) from Germ.coe_eq.mpr this, map_one]
  · rw [polyGermHom_apply, ← map_mul]
    have : ((fun z : ℂ => (q.eval z)⁻¹) * fun z : ℂ => q.eval z)
        =ᶠ[upperEndFilter] (1 : ℂ → ℂ) := by
      filter_upwards [hev] with z hz
      simp [Pi.mul_apply, inv_mul_cancel₀ hz]
    rw [show (Germ.coeRingHom upperEndFilter)
        ((fun z : ℂ => (q.eval z)⁻¹) * fun z : ℂ => q.eval z)
        = (Germ.coeRingHom upperEndFilter) (1 : ℂ → ℂ) from Germ.coe_eq.mpr this, map_one]

/-- The pointwise value of a rational function. -/
def ratFuncFun (k : RatFunc ℂ) : ℂ → ℂ := fun z => RatFunc.eval (RingHom.id ℂ) z k

theorem eventually_denom_ne_zero (k : RatFunc ℂ) :
    ∀ᶠ z in upperEndFilter, Polynomial.eval₂ (RingHom.id ℂ) z k.denom ≠ 0 := by
  obtain ⟨H, hH⟩ := exists_upperTail_polyEval_ne_zero (RatFunc.denom_ne_zero k)
  have hmem : upperTail H ∈ upperEndFilter :=
    upperEndFilter_basis.mem_of_mem (i := H) trivial
  filter_upwards [hmem] with z hz
  have hval : Polynomial.eval₂ (RingHom.id ℂ) z k.denom = k.denom.eval z := by
    simp [Polynomial.eval₂_eq_eval_map]
  rw [hval]
  exact hH z hz

/-- **Rational functions as germs at the upper end.** -/
def ratFuncGerm : RatFunc ℂ →+* Germ upperEndFilter ℂ where
  toFun k := (Germ.coeRingHom upperEndFilter) (ratFuncFun k)
  map_one' := by
    have : ratFuncFun 1 = (1 : ℂ → ℂ) := by
      funext z
      simp [ratFuncFun, RatFunc.eval_one]
    rw [this, map_one]
  map_zero' := by
    have : ratFuncFun 0 = (0 : ℂ → ℂ) := by
      funext z
      simp [ratFuncFun, RatFunc.eval]
    rw [this, map_zero]
  map_mul' k l := by
    rw [← map_mul]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [eventually_denom_ne_zero k, eventually_denom_ne_zero l] with z hk hl
    simpa [ratFuncFun, Pi.mul_apply] using RatFunc.eval_mul (f := RingHom.id ℂ) (a := z) hk hl
  map_add' k l := by
    rw [← map_add]
    refine Germ.coe_eq.mpr ?_
    filter_upwards [eventually_denom_ne_zero k, eventually_denom_ne_zero l] with z hk hl
    simpa [ratFuncFun, Pi.add_apply] using RatFunc.eval_add (f := RingHom.id ℂ) (a := z) hk hl

@[simp] theorem ratFuncGerm_apply (k : RatFunc ℂ) :
    ratFuncGerm k = (Germ.coeRingHom upperEndFilter) (ratFuncFun k) := rfl

end

end GaloisForLFunctions.HTGeometry
