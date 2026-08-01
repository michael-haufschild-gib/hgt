import GaloisForLFunctions.HTGeometry.HalfPlaneFlatFilter

/-!
# The germ ring of the upper right half-plane

Along the upper part of a right half-plane every nonzero polynomial is eventually nonzero, so its
germ is a unit and the polynomial germ map extends to the rational function field: `ℂ(s)` acts on
germs of complex functions.

Flatness only depends on the germ, and the flat germs are stable under differences and under
multiplication by any rational germ.  No nonzero rational germ is flat.  This is the coefficient
side of the annihilator space that the shift elimination consumes.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- Germs of complex functions along the upper part of the right half-plane `Re s ≥ σ₀`. -/
abbrev HalfPlaneGerm (σ₀ : ℝ) : Type := Filter.Germ (halfPlaneUpper σ₀) ℂ

/-- Flatness only depends on the germ. -/
theorem IsFlatOn.congr_eventually {σ₀ : ℝ} {A B : ℂ → ℂ}
    (h : A =ᶠ[halfPlaneUpper σ₀] B) (hA : IsFlatOn σ₀ A) : IsFlatOn σ₀ B := by
  intro N
  refine (hA N).congr' ?_
  filter_upwards [h] with s hs
  rw [hs]

/-- A germ is flat when one — equivalently every — representative is. -/
def IsFlatGerm (σ₀ : ℝ) (g : HalfPlaneGerm σ₀) : Prop :=
  Quotient.liftOn g (IsFlatOn σ₀) fun _A _B h =>
    propext ⟨fun hA => hA.congr_eventually h, fun hB => hB.congr_eventually h.symm⟩

@[simp] theorem isFlatGerm_coe {σ₀ : ℝ} (A : ℂ → ℂ) :
    IsFlatGerm σ₀ (↑A : HalfPlaneGerm σ₀) ↔ IsFlatOn σ₀ A := Iff.rfl

theorem IsFlatGerm.sub {σ₀ : ℝ} {g h : HalfPlaneGerm σ₀} (hg : IsFlatGerm σ₀ g)
    (hh : IsFlatGerm σ₀ h) : IsFlatGerm σ₀ (g - h) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    induction h using Filter.Germ.inductionOn with
    | h B => exact IsFlatOn.sub hg hh

/-- The germ of the values of a polynomial. -/
def polyGerm (σ₀ : ℝ) : Polynomial ℂ →+* HalfPlaneGerm σ₀ where
  toFun p := ((fun s : ℂ => p.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀)
  map_one' := by
    refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun s => ?_)
    simp
  map_mul' p q := by
    refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun s => ?_)
    simp
  map_zero' := by
    refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun s => ?_)
    simp
  map_add' p q := by
    refine Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun s => ?_)
    simp

theorem polyGerm_apply (σ₀ : ℝ) (p : Polynomial ℂ) :
    polyGerm σ₀ p = ((fun s : ℂ => p.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀) := rfl

/-- A nonzero polynomial is eventually nonzero on the filter. -/
theorem eventually_eval_ne_zero_filter (σ₀ : ℝ) {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∀ᶠ s : ℂ in halfPlaneUpper σ₀, p.eval s ≠ 0 := by
  have hpos : 0 < ‖p.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  filter_upwards [eventually_norm_eval_ge_filter σ₀ hp, eventually_one_le_norm σ₀] with s hs hs1
  have hpowge : (1 : ℝ) ≤ ‖s‖ ^ p.natDegree := one_le_pow₀ hs1
  have : 0 < ‖p.eval s‖ := by nlinarith
  exact norm_pos_iff.mp this

/-- The germ of a nonzero polynomial is a unit. -/
theorem isUnit_polyGerm (σ₀ : ℝ) {p : Polynomial ℂ} (hp : p ≠ 0) : IsUnit (polyGerm σ₀ p) := by
  refine IsUnit.of_mul_eq_one ((fun s : ℂ => (p.eval s)⁻¹ : ℂ → ℂ) : HalfPlaneGerm σ₀) ?_
  rw [polyGerm_apply, ← Filter.Germ.coe_mul]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_eval_ne_zero_filter σ₀ hp] with s hs
  exact mul_inv_cancel₀ hs


/-- The germ of a rational function. -/
noncomputable def ratGerm (σ₀ : ℝ) : RatFunc ℂ →+* HalfPlaneGerm σ₀ :=
  IsLocalization.lift (M := nonZeroDivisors (Polynomial ℂ)) (g := polyGerm σ₀)
    (fun y => isUnit_polyGerm σ₀ (mem_nonZeroDivisors_iff_ne_zero.mp y.2))

@[simp] theorem ratGerm_algebraMap (σ₀ : ℝ) (p : Polynomial ℂ) :
    ratGerm σ₀ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = polyGerm σ₀ p :=
  IsLocalization.lift_eq _ p

/-- The reciprocal germ of the denominator values. -/
noncomputable def denomInvGerm (σ₀ : ℝ) (q : Polynomial ℂ) : HalfPlaneGerm σ₀ :=
  ((fun s : ℂ => (q.eval s)⁻¹ : ℂ → ℂ) : HalfPlaneGerm σ₀)

theorem polyGerm_mul_denomInvGerm (σ₀ : ℝ) {q : Polynomial ℂ} (hq : q ≠ 0) :
    polyGerm σ₀ q * denomInvGerm σ₀ q = 1 := by
  rw [polyGerm_apply, denomInvGerm, ← Filter.Germ.coe_mul]
  refine Filter.Germ.coe_eq.mpr ?_
  filter_upwards [eventually_eval_ne_zero_filter σ₀ hq] with s hs
  exact mul_inv_cancel₀ hs

/-- The germ of a rational function is the germ of the quotient of its numerator and denominator
values. -/
theorem ratGerm_eq_div (σ₀ : ℝ) (k : RatFunc ℂ) :
    ratGerm σ₀ k = ((fun s : ℂ => k.num.eval s / k.denom.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀) := by
  have hden : k.denom ≠ 0 := k.denom_ne_zero
  have hdenK : algebraMap (Polynomial ℂ) (RatFunc ℂ) k.denom ≠ 0 :=
    fun h => hden (RatFunc.algebraMap_injective ℂ (by rw [h, map_zero]))
  have hk : k * algebraMap (Polynomial ℂ) (RatFunc ℂ) k.denom
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) k.num := by
    nth_rewrite 1 [← RatFunc.num_div_denom k]
    exact div_mul_cancel₀ _ hdenK
  have hmul : ratGerm σ₀ k * polyGerm σ₀ k.denom = polyGerm σ₀ k.num := by
    rw [← ratGerm_algebraMap σ₀ k.denom, ← ratGerm_algebraMap σ₀ k.num, ← map_mul, hk]
  have hfinal : polyGerm σ₀ k.num * denomInvGerm σ₀ k.denom
      = ((fun s : ℂ => k.num.eval s / k.denom.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀) := by
    rw [polyGerm_apply, denomInvGerm, ← Filter.Germ.coe_mul]
    exact Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall fun s => (div_eq_mul_inv _ _).symm)
  calc ratGerm σ₀ k
      = ratGerm σ₀ k * (polyGerm σ₀ k.denom * denomInvGerm σ₀ k.denom) := by
        rw [polyGerm_mul_denomInvGerm σ₀ hden, mul_one]
    _ = ratGerm σ₀ k * polyGerm σ₀ k.denom * denomInvGerm σ₀ k.denom := (mul_assoc _ _ _).symm
    _ = polyGerm σ₀ k.num * denomInvGerm σ₀ k.denom := by rw [hmul]
    _ = ((fun s : ℂ => k.num.eval s / k.denom.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀) := hfinal

/-- Flatness survives multiplication by a rational germ. -/
theorem IsFlatGerm.mul_ratGerm {σ₀ : ℝ} (k : RatFunc ℂ) {g : HalfPlaneGerm σ₀}
    (hg : IsFlatGerm σ₀ g) : IsFlatGerm σ₀ (ratGerm σ₀ k * g) := by
  induction g using Filter.Germ.inductionOn with
  | h A =>
    have hA : IsFlatOn σ₀ A := hg
    rw [ratGerm_eq_div]
    have hcoe : (((fun s : ℂ => k.num.eval s / k.denom.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀))
        * (↑A : HalfPlaneGerm σ₀)
        = ((fun s : ℂ => k.num.eval s * A s / k.denom.eval s : ℂ → ℂ) : HalfPlaneGerm σ₀) := by
      rw [← Filter.Germ.coe_mul]
      exact Filter.Germ.coe_eq.mpr
        (Filter.Eventually.of_forall fun s => div_mul_eq_mul_div _ _ _)
    rw [hcoe]
    exact (hA.mul_poly k.num).div_poly k.denom_ne_zero

/-- **No nonzero rational germ is flat.** -/
theorem not_isFlatGerm_ratGerm {σ₀ : ℝ} {k : RatFunc ℂ} (hk : k ≠ 0) :
    ¬ IsFlatGerm σ₀ (ratGerm σ₀ k) := by
  intro hflat
  have hnum : k.num ≠ 0 := fun h => hk (RatFunc.num_eq_zero_iff.mp h)
  have hden : k.denom ≠ 0 := k.denom_ne_zero
  rw [ratGerm_eq_div] at hflat
  have hA : IsFlatOn σ₀ (fun s : ℂ => k.num.eval s / k.denom.eval s) := hflat
  have hmul := hA.mul_poly k.denom
  have hcongr : IsFlatOn σ₀ (fun s : ℂ => k.num.eval s) := by
    refine hmul.congr_eventually ?_
    filter_upwards [eventually_eval_ne_zero_filter σ₀ hden] with s hs
    rw [mul_comm, div_mul_cancel₀ _ hs]
  exact not_isFlatOn_polynomial hnum hcongr

end GaloisForLFunctions
