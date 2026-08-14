import GaloisForLFunctions.HTGeometry.ConstitutiveFunctionalEquationPacketLift
import Mathlib.Tactic

/-!
# Causal Jordan formation mechanics

A signed observer coordinate is the quotient of two nonnegative formation legs.  The legs compose
strictly, while the quotient chart acquires an exact cancellation-reserve cocycle.  Functional
equation swaps the legs and preserves both reserve and least common causal delay.  A reciprocal
radial family has uniformly bounded common delay exactly at its fixed point.

This is an unconditional finite-dimensional algebraic/properness layer.  It does not assert RH and
does not replace the already formalized Markov-kernel information-isometry theorem imported above.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Positive two-leg formation state before signed cancellation. -/
structure CausalJordanFormation where
  positive : ℝ
  negative : ℝ
  positive_nonneg : 0 ≤ positive
  negative_nonneg : 0 ≤ negative

namespace CausalJordanFormation

/-- Signed observer quotient of a positive formation state. -/
def visible (s : CausalJordanFormation) : ℝ := s.positive - s.negative

/-- Positive history hidden by signed cancellation. -/
def reserve (s : CausalJordanFormation) : ℝ := min s.positive s.negative

/-- Least delay that causally admits both functional-equation orientations. -/
def commonDelay (s : CausalJordanFormation) : ℝ := max s.positive s.negative

/-- Strict formation composition adds both positive legs before cancellation. -/
def fuse (s t : CausalJordanFormation) : CausalJordanFormation where
  positive := s.positive + t.positive
  negative := s.negative + t.negative
  positive_nonneg := add_nonneg s.positive_nonneg t.positive_nonneg
  negative_nonneg := add_nonneg s.negative_nonneg t.negative_nonneg

/-- Functional equation exchanges the two formation polarities. -/
def reflect (s : CausalJordanFormation) : CausalJordanFormation where
  positive := s.negative
  negative := s.positive
  positive_nonneg := s.negative_nonneg
  negative_nonneg := s.positive_nonneg

/-- Cancellation born when two visible laws are fused. -/
def cancellationBirth (x y : ℝ) : ℝ := (|x| + |y| - |x + y|) / 2

theorem visible_fuse (s t : CausalJordanFormation) :
    visible (fuse s t) = visible s + visible t := by
  simp [visible, fuse]
  ring

theorem fuse_assoc (r s t : CausalJordanFormation) :
    fuse (fuse r s) t = fuse r (fuse s t) := by
  cases r
  cases s
  cases t
  simp [fuse, add_assoc]

/-- Exact Jordan identity reconstructing reserve from total positive formation and visible law. -/
theorem two_mul_reserve_eq (s : CausalJordanFormation) :
    2 * reserve s = s.positive + s.negative - |visible s| := by
  rcases le_total s.positive s.negative with h | h
  · rw [reserve, min_eq_left h, visible, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [reserve, min_eq_right h, visible, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Least common causal delay is visible displacement plus hidden reserve. -/
theorem commonDelay_eq_abs_visible_add_reserve (s : CausalJordanFormation) :
    commonDelay s = |visible s| + reserve s := by
  rcases le_total s.positive s.negative with h | h
  · rw [commonDelay, max_eq_right h, reserve, min_eq_left h, visible,
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [commonDelay, max_eq_left h, reserve, min_eq_right h, visible,
      abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem cancellationBirth_nonneg (x y : ℝ) : 0 ≤ cancellationBirth x y := by
  unfold cancellationBirth
  linarith [abs_add_le x y]

/-- **Reserve fusion law.** Strict positive-leg addition descends to a nonlinear signed chart;
opposite visible laws create exactly the triangle-inequality defect as new reserve. -/
theorem reserve_fuse (s t : CausalJordanFormation) :
    reserve (fuse s t) =
      reserve s + reserve t + cancellationBirth (visible s) (visible t) := by
  have hf := two_mul_reserve_eq (fuse s t)
  have hs := two_mul_reserve_eq s
  have ht := two_mul_reserve_eq t
  rw [visible_fuse] at hf
  change 2 * reserve (fuse s t) =
    (s.positive + t.positive) + (s.negative + t.negative) -
      |visible s + visible t| at hf
  unfold cancellationBirth
  ring_nf at hf hs ht ⊢
  linarith

/-- The reserve correction obeys the exact associativity cocycle identity. -/
theorem cancellationBirth_cocycle (x y z : ℝ) :
    cancellationBirth x y + cancellationBirth (x + y) z =
      cancellationBirth y z + cancellationBirth x (y + z) := by
  unfold cancellationBirth
  rw [add_assoc x y z]
  ring

theorem visible_reflect (s : CausalJordanFormation) :
    visible (reflect s) = -visible s := by
  simp [visible, reflect]

theorem reserve_reflect (s : CausalJordanFormation) : reserve (reflect s) = reserve s := by
  simp [reserve, reflect, min_comm]

theorem commonDelay_reflect (s : CausalJordanFormation) :
    commonDelay (reflect s) = commonDelay s := by
  simp [commonDelay, reflect, max_comm]

theorem reflect_fuse (s t : CausalJordanFormation) :
    reflect (fuse s t) = fuse (reflect s) (reflect t) := by
  rfl

theorem reflect_involution (s : CausalJordanFormation) : reflect (reflect s) = s := by
  cases s
  rfl

/-- Every common recovery rule factoring through the signed quotient is constant on reserve
fibres. -/
theorem commonRecovery_eq_of_visible {A : Type*} (K : ℝ → A)
    {s t : CausalJordanFormation} (h : visible s = visible t) :
    K (visible s) = K (visible t) := by
  rw [h]

/-- A quotient action intertwining sign reversal lifts information-neutrally across formation
reflection: reserve changes nowhere and the recovered output is transformed, not erased. -/
theorem commonRecovery_reflect {A : Type*} (K : ℝ → A) (ρ : A → A)
    (hρ : ∀ x, K (-x) = ρ (K x)) (s : CausalJordanFormation) :
    K (visible (reflect s)) = ρ (K (visible s)) := by
  rw [visible_reflect, hρ]

end CausalJordanFormation

/-! ## Reciprocal common-delay properness -/

/-- Direct positive radial edge leg at aperture `n`. -/
def reciprocalDirectLeg (q : ℝ) (n : ℕ) : ℝ := |1 - q| * q ^ n

/-- Reflected positive radial edge leg at aperture `n`. -/
def reciprocalReflectedLeg (q : ℝ) (n : ℕ) : ℝ :=
  |1 - q⁻¹| * (q⁻¹) ^ n

/-- Least positive budget admitting both reciprocal orientations. -/
def reciprocalCommonDelay (q : ℝ) (n : ℕ) : ℝ :=
  max (reciprocalDirectLeg q n) (reciprocalReflectedLeg q n)

/-- Cofinal common-delay properness. -/
def BoundedReciprocalCommonDelay (q : ℝ) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, reciprocalCommonDelay q n ≤ C

theorem reciprocalDirectLeg_inv (q : ℝ) (n : ℕ) :
    reciprocalDirectLeg q⁻¹ n = reciprocalReflectedLeg q n := by
  rfl

theorem reciprocalReflectedLeg_inv (q : ℝ) (n : ℕ) :
    reciprocalReflectedLeg q⁻¹ n = reciprocalDirectLeg q n := by
  simp [reciprocalReflectedLeg, reciprocalDirectLeg]

/-- Functional equation preserves the full common-delay profile pointwise. -/
theorem reciprocalCommonDelay_inv (q : ℝ) (n : ℕ) :
    reciprocalCommonDelay q⁻¹ n = reciprocalCommonDelay q n := by
  simp [reciprocalCommonDelay, reciprocalDirectLeg_inv, reciprocalReflectedLeg_inv, max_comm]

/-- **Global formation/properness theorem.** For a positive reciprocal radial law, one finite
common-delay budget works at every aperture exactly at the functional-equation fixed point. -/
theorem boundedReciprocalCommonDelay_iff {q : ℝ} (hq : 0 < q) :
    BoundedReciprocalCommonDelay q ↔ q = 1 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hq1
    rcases lt_or_gt_of_ne hq1 with hlt | hgt
    · have hi : 1 < q⁻¹ := (one_lt_inv₀ hq).2 hlt
      have hf : 0 < |1 - q⁻¹| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hi))
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / |1 - q⁻¹|) hi
      have hlarge : C < reciprocalReflectedLeg q n := by
        rw [reciprocalReflectedLeg]
        simpa [mul_comm] using (div_lt_iff₀ hf).mp hn
      exact (not_lt_of_ge ((le_max_right _ _).trans (hC n))) hlarge
    · have hf : 0 < |1 - q| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hgt))
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (C / |1 - q|) hgt
      have hlarge : C < reciprocalDirectLeg q n := by
        rw [reciprocalDirectLeg]
        simpa [mul_comm] using (div_lt_iff₀ hf).mp hn
      exact (not_lt_of_ge ((le_max_left _ _).trans (hC n))) hlarge
  · rintro rfl
    refine ⟨0, fun n => ?_⟩
    simp [reciprocalCommonDelay, reciprocalDirectLeg, reciprocalReflectedLeg]

/-- Closed visible formation can retain arbitrary positive reserve and common delay. -/
theorem closedFormation_with_reserve (r : ℝ) (hr : 0 ≤ r) :
    let s : CausalJordanFormation := ⟨r, r, hr, hr⟩
    CausalJordanFormation.visible s = 0 ∧
      CausalJordanFormation.reserve s = r ∧
      CausalJordanFormation.commonDelay s = r := by
  simp [CausalJordanFormation.visible, CausalJordanFormation.reserve,
    CausalJordanFormation.commonDelay]

/-- **Causal Jordan capstone.** Formation composition generates nonnegative hidden reserve,
functional equation preserves that reserve and common delay, closed observation does not imply
zero formation, and cofinal reciprocal common-delay properness selects only the fixed point. -/
theorem causalJordanFormation_mechanism_certificate :
    (∀ x y : ℝ, 0 ≤ CausalJordanFormation.cancellationBirth x y) ∧
      (∀ s : CausalJordanFormation,
        CausalJordanFormation.reserve (CausalJordanFormation.reflect s) =
          CausalJordanFormation.reserve s ∧
        CausalJordanFormation.commonDelay (CausalJordanFormation.reflect s) =
          CausalJordanFormation.commonDelay s) ∧
      (∀ (r : ℝ) (hr : 0 ≤ r),
        CausalJordanFormation.visible ⟨r, r, hr, hr⟩ = 0 ∧
          CausalJordanFormation.reserve ⟨r, r, hr, hr⟩ = r ∧
          CausalJordanFormation.commonDelay ⟨r, r, hr, hr⟩ = r) ∧
      (∀ q : ℝ, 0 < q → (BoundedReciprocalCommonDelay q ↔ q = 1)) := by
  exact ⟨CausalJordanFormation.cancellationBirth_nonneg,
    fun s => ⟨CausalJordanFormation.reserve_reflect s,
      CausalJordanFormation.commonDelay_reflect s⟩,
    closedFormation_with_reserve,
    fun q hq => boundedReciprocalCommonDelay_iff hq⟩

end

end GaloisForLFunctions.HTGeometry
