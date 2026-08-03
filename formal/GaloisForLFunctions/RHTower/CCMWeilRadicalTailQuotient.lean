import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The Weil defect of an aperture cut is the negative exterior tail

Three independent pieces of the exterior-tail gate.

* **The radical quotient identity.**  If `h` lies in the two-sided radical of a biadditive pairing
  and `a + b = h`, then `Q a g = -Q b g`, `Q g a = -Q g b`, and `Q a a = Q b b`; in the quotient by
  the radical the two classes are negatives of each other.  Only biadditivity is used — no
  sesquilinearity, no topology, no domain conditions.
* **The zero-integral repair cost.**  For a fixed bump `β` the rescaling `β_R x = R⁻¹ β (x/R)`
  preserves the integral while its squared `L²` norm scales by `R⁻¹`, so the integral of an
  approximant can be corrected to zero at arbitrarily small `L²` cost.  This is the quantitative
  content of the density lemma.
* **An unbounded multiplier is unbounded on indicators.**  If `|m|` exceeds `C` on a set of positive
  finite measure, the multiplier bound `‖m u‖₂ ≤ C ‖u‖₂` already fails at the indicator of that set.
  This is the step that converts unboundedness of `zeta` on the critical line into unboundedness of
  the summation map, with no closed-operator extension argument needed.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Filter Topology MeasureTheory Set

/-! ## The radical quotient identity -/

variable {V : Type*} [AddCommGroup V]

/-- A pairing additive in each argument.  This is all the quotient identity needs. -/
structure IsBiadditive (Q : V → V → ℂ) : Prop where
  left : ∀ x y z, Q (x + y) z = Q x z + Q y z
  right : ∀ x y z, Q x (y + z) = Q x y + Q x z

namespace IsBiadditive

variable {Q : V → V → ℂ}

theorem zero_left (hQ : IsBiadditive Q) (z : V) : Q 0 z = 0 := by
  have h := hQ.left 0 0 z
  rw [add_zero] at h
  linear_combination -h

theorem zero_right (hQ : IsBiadditive Q) (x : V) : Q x 0 = 0 := by
  have h := hQ.right x 0 0
  rw [add_zero] at h
  linear_combination -h

theorem neg_left (hQ : IsBiadditive Q) (x z : V) : Q (-x) z = -Q x z := by
  have h := hQ.left x (-x) z
  rw [add_neg_cancel, hQ.zero_left] at h
  linear_combination -h

theorem neg_right (hQ : IsBiadditive Q) (x y : V) : Q x (-y) = -Q x y := by
  have h := hQ.right x y (-y)
  rw [add_neg_cancel, hQ.zero_right] at h
  linear_combination -h

theorem sub_left (hQ : IsBiadditive Q) (x y z : V) : Q (x - y) z = Q x z - Q y z := by
  rw [sub_eq_add_neg, hQ.left, hQ.neg_left, sub_eq_add_neg]

theorem sub_right (hQ : IsBiadditive Q) (x y z : V) : Q x (y - z) = Q x y - Q x z := by
  rw [sub_eq_add_neg, hQ.right, hQ.neg_right, sub_eq_add_neg]

end IsBiadditive

/-- The two-sided radical of a pairing. -/
def weilRadical (Q : V → V → ℂ) : Set V := {h | (∀ g, Q h g = 0) ∧ ∀ g, Q g h = 0}

/-- The radical is an additive subgroup. -/
def weilRadicalSubgroup (Q : V → V → ℂ) (hQ : IsBiadditive Q) : AddSubgroup V where
  carrier := weilRadical Q
  zero_mem' := ⟨fun g => hQ.zero_left g, fun g => hQ.zero_right g⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun g => by rw [hQ.left, hx1, hy1, add_zero],
      fun g => by rw [hQ.right, hx2, hy2, add_zero]⟩
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨fun g => by rw [hQ.neg_left, hx1, neg_zero],
      fun g => by rw [hQ.neg_right, hx2, neg_zero]⟩

theorem mem_weilRadicalSubgroup {Q : V → V → ℂ} (hQ : IsBiadditive Q) {h : V} :
    h ∈ weilRadicalSubgroup Q hQ ↔ (∀ g, Q h g = 0) ∧ ∀ g, Q g h = 0 := Iff.rfl

/-- **Equation (2), left slot.**  An aperture cut of a radical vector pairs as the negative of its
exterior tail. -/
theorem radical_pair_left {Q : V → V → ℂ} (hQ : IsBiadditive Q) {h a b : V}
    (hh : ∀ g, Q h g = 0) (hab : a + b = h) (g : V) : Q a g = -Q b g := by
  have := hQ.left a b g
  rw [hab, hh g] at this
  linear_combination -this

/-- **Equation (2), right slot.** -/
theorem radical_pair_right {Q : V → V → ℂ} (hQ : IsBiadditive Q) {h a b : V}
    (hh : ∀ g, Q g h = 0) (hab : a + b = h) (g : V) : Q g a = -Q g b := by
  have := hQ.right g a b
  rw [hab, hh g] at this
  linear_combination -this

/-- **Equation (3).**  The aperture cut and the exterior tail have the same Weil value. -/
theorem radical_diag_eq {Q : V → V → ℂ} (hQ : IsBiadditive Q) {h a b : V}
    (hh1 : ∀ g, Q h g = 0) (hh2 : ∀ g, Q g h = 0) (hab : a + b = h) :
    Q a a = Q b b := by
  have ha : a = h - b := by rw [← hab]; abel
  rw [ha, hQ.sub_left, hQ.sub_right, hQ.sub_right]
  simp only [hh1, hh2]
  ring

/-- **Equation (4).**  In the quotient by the radical the aperture class is the negative of the
exterior-tail class. -/
theorem radical_quotient_eq_neg {Q : V → V → ℂ} (hQ : IsBiadditive Q) {h a b : V}
    (hh : h ∈ weilRadicalSubgroup Q hQ) (hab : a + b = h) :
    (QuotientAddGroup.mk' (weilRadicalSubgroup Q hQ) a)
      = -(QuotientAddGroup.mk' (weilRadicalSubgroup Q hQ) b) := by
  rw [← add_eq_zero_iff_eq_neg, ← map_add, hab]
  exact (QuotientAddGroup.eq_zero_iff h).mpr hh

/-! ## The zero-integral repair cost -/

/-- Rescaling preserves the integral. -/
theorem integral_scaledBump (β : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ, R⁻¹ * β (x / R)) = ∫ x : ℝ, β x := by
  rw [integral_const_mul, Measure.integral_comp_div β R, smul_eq_mul, abs_of_pos hR,
    ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

/-- Rescaling scales the squared `L²` norm by `R⁻¹`. -/
theorem integral_sq_scaledBump (β : ℝ → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x : ℝ, (R⁻¹ * β (x / R)) ^ 2) = R⁻¹ * ∫ x : ℝ, (β x) ^ 2 := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hpow : ∀ x : ℝ, (R⁻¹ * β (x / R)) ^ 2 = R⁻¹ ^ 2 * (fun y : ℝ => (β y) ^ 2) (x / R) := by
    intro x
    simp only
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpow), integral_const_mul,
    Measure.integral_comp_div (fun y : ℝ => (β y) ^ 2) R, smul_eq_mul, abs_of_pos hR,
    ← mul_assoc, show R⁻¹ ^ 2 * R = R⁻¹ from by field_simp]

/-- **The repair cost vanishes.**  Correcting the integral of an approximant costs `L²` norm of
order `R^(-1/2)`, which tends to zero. -/
theorem tendsto_integral_sq_scaledBump (β : ℝ → ℝ) :
    Tendsto (fun R : ℝ => R⁻¹ * ∫ x : ℝ, (β x) ^ 2) atTop (nhds 0) := by
  simpa using tendsto_inv_atTop_zero.mul_const (∫ x : ℝ, (β x) ^ 2)

/-! ## Unboundedness of a multiplier -/

/-- **An unbounded multiplier already fails the bound on one indicator.**  If `‖m‖ ^ 2` exceeds
`C ^ 2` on a set of positive finite measure then `∫_S ‖m‖ ^ 2 > C ^ 2 * |S|`, i.e. the multiplier
bound `‖m u‖₂ ≤ C ‖u‖₂` fails at `u = 1_S`.  No closed-operator extension is needed. -/
theorem lt_setIntegral_normSq_of_exceeds {m : ℝ → ℂ} {C : ℝ} {S : Set ℝ}
    (hSmeas : MeasurableSet S) (hSpos : 0 < volume S) (hSfin : volume S ≠ ⊤)
    (hint : IntegrableOn (fun t => ‖m t‖ ^ 2) S)
    (hm : ∀ t ∈ S, C ^ 2 < ‖m t‖ ^ 2) :
    C ^ 2 * (volume S).toReal < ∫ t in S, ‖m t‖ ^ 2 := by
  have hconstint : IntegrableOn (fun _ : ℝ => C ^ 2) S := integrableOn_const hSfin
  have hgint : IntegrableOn (fun t => ‖m t‖ ^ 2 - C ^ 2) S := hint.sub hconstint
  have hae : 0 ≤ᵐ[volume.restrict S] fun t => ‖m t‖ ^ 2 - C ^ 2 := by
    filter_upwards [ae_restrict_mem hSmeas] with t ht
    have := hm t ht
    show (0 : ℝ) ≤ ‖m t‖ ^ 2 - C ^ 2
    linarith
  have hsupp : (Function.support fun t => ‖m t‖ ^ 2 - C ^ 2) ∩ S = S := by
    refine Set.inter_eq_right.mpr fun t ht => ?_
    have hlt := hm t ht
    show ‖m t‖ ^ 2 - C ^ 2 ≠ 0
    exact sub_ne_zero.mpr (ne_of_gt hlt)
  have hpos : 0 < ∫ t in S, (‖m t‖ ^ 2 - C ^ 2) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hae hgint, hsupp]
    exact hSpos
  have hsplit : (∫ t in S, (‖m t‖ ^ 2 - C ^ 2))
      = (∫ t in S, ‖m t‖ ^ 2) - C ^ 2 * (volume S).toReal := by
    rw [integral_sub hint hconstint, setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  rw [hsplit] at hpos
  linarith

end GaloisForLFunctions.RHTower

end
