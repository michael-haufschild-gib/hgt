import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

/-!
# Formal inversion and the sharp third-coefficient boundary of the alternating source

The literal coefficients are `(-1)^(n-1) n^(-s)`. Their formal power series has a
compositional inverse at every complex parameter. The third coefficient defect
`a₃-a₂²` is nevertheless `3^(-s)-4^(-s)`, whose exact horizontal maximum is
`3^(-sigma)+4^(-sigma)`, attained at one explicit height independent of sigma.

There is a unique real cutoff strictly between one half and one where that
maximum equals one. This classifies the coefficient bound and separates it from
formal invertibility. No analytic univalence theorem, endpoint inverse extension,
zeta nonvanishing, or RH implication is asserted in this module.
-/

noncomputable section
namespace RHTower.AlternatingInverseCoefficient
open Complex

/-- Literal alternating Dirichlet coefficient, with the constant coefficient set to zero. -/
def coefficient (s : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else (-1 : ℂ) ^ (n - 1) * (n : ℂ) ^ (-s)

/-- The full formal generating series of the literal alternating coefficients. -/
def formalSeries (s : ℂ) : PowerSeries ℂ := PowerSeries.mk (coefficient s)

@[simp] theorem formalSeries_constantCoeff (s : ℂ) : (formalSeries s).constantCoeff = 0 := by
  simp [formalSeries, coefficient]

@[simp] theorem formalSeries_coeff_one (s : ℂ) : (formalSeries s).coeff 1 = 1 := by
  simp [formalSeries, coefficient]

/-- Canonical compositional inverse, available for every complex parameter. -/
def formalInverse (s : ℂ) : PowerSeries ℂ :=
  (formalSeries s).substInvOfIsUnit (by simp)

/-- The formal inverse is a right compositional inverse at every parameter. -/
theorem formalSeries_subst_inverse (s : ℂ) :
    (formalSeries s).subst (formalInverse s) = PowerSeries.X := by
  exact PowerSeries.subst_substInvOfIsUnit_right _ (formalSeries_constantCoeff s) _

/-- The formal inverse is a left compositional inverse at every parameter. -/
theorem formalInverse_subst_series (s : ℂ) :
    (formalInverse s).subst (formalSeries s) = PowerSeries.X := by
  exact PowerSeries.subst_substInvOfIsUnit_left _ (formalSeries_constantCoeff s) _

/-- Third coefficient defect of the actual alternating source. -/
def defect (s : ℂ) : ℂ := coefficient s 3 - coefficient s 2 ^ 2

/-- One explicit height at which the third-coefficient terms have opposite phases. -/
def height : ℝ := Real.pi / (Real.log 4 - Real.log 3)

/-- Exact horizontal maximum of the third coefficient defect. -/
def envelope (sigma : ℝ) : ℝ := (3 : ℝ) ^ (-sigma) + (4 : ℝ) ^ (-sigma)

/-- Multiplication of the literal second coefficient gives the frequency at four. -/
theorem defect_eq (s : ℂ) : defect s = (3 : ℂ) ^ (-s) - (4 : ℂ) ^ (-s) := by
  have h := Complex.mul_cpow_ofReal_nonneg (a := 2) (b := 2) (by norm_num) (by norm_num) (-s)
  norm_num at h
  simp [defect, coefficient, pow_two, ← h]

private theorem cpow_split {a : ℝ} (ha : 0 < a) (sigma t : ℝ) :
    (a : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * I)) =
      ((a ^ (-sigma) : ℝ) : ℂ) * exp (((-t * Real.log a : ℝ) : ℂ) * I) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'), ← Complex.ofReal_log ha.le,
    Real.rpow_def_of_pos ha, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem cpow_norm {a : ℝ} (ha : 0 < a) (sigma t : ℝ) :
    ‖(a : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * I))‖ = a ^ (-sigma) := by
  rw [cpow_split ha, norm_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ha _)]

/-- Uniform horizontal upper bound for every real part, with no zero premise. -/
theorem norm_defect_le (sigma t : ℝ) :
    ‖defect ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ envelope sigma := by
  rw [defect_eq]
  calc
    _ ≤ ‖(3 : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * I))‖ +
      ‖(4 : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * I))‖ := norm_sub_le _ _
    _ = envelope sigma := by
      rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
        show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
        cpow_norm (by norm_num), cpow_norm (by norm_num)]
      rfl

private theorem phase_four :
    exp (((-height * Real.log 4 : ℝ) : ℂ) * I) =
      -exp (((-height * Real.log 3 : ℝ) : ℂ) * I) := by
  have hlog : Real.log 4 - Real.log 3 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (Real.log_lt_log (by norm_num) (by norm_num)))
  have h : -height * Real.log 4 = -height * Real.log 3 - Real.pi := by
    dsimp [height]
    field_simp
    ring
  rw [h, Complex.ofReal_sub, sub_mul, Complex.exp_sub,
    Complex.exp_pi_mul_I, div_neg, div_one]

/-- The horizontal upper bound is attained at the explicit opposite-phase height. -/
theorem norm_defect_at_height (sigma : ℝ) :
    ‖defect ((sigma : ℂ) + (height : ℂ) * I)‖ = envelope sigma := by
  rw [defect_eq,
    show (3 : ℂ) = ((3 : ℝ) : ℂ) by norm_num,
    show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num,
    cpow_split (by norm_num), cpow_split (by norm_num), phase_four]
  have h : (((3 : ℝ) ^ (-sigma) : ℝ) : ℂ) * exp (((-height * Real.log 3 : ℝ) : ℂ) * I) -
      (((4 : ℝ) ^ (-sigma) : ℝ) : ℂ) * -exp (((-height * Real.log 3 : ℝ) : ℂ) * I) =
      ((envelope sigma : ℝ) : ℂ) * exp (((-height * Real.log 3 : ℝ) : ℂ) * I) := by
    dsimp [envelope]
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by dsimp [envelope]; positivity)]

/-- Complete classification of every uniform horizontal coefficient bound. -/
theorem horizontal_bound_iff (sigma C : ℝ) :
    (∀ t : ℝ, ‖defect ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ C) ↔ envelope sigma ≤ C := by
  constructor
  · intro h
    simpa only [norm_defect_at_height] using h height
  · intro h t
    exact (norm_defect_le sigma t).trans h

/-- The exact coefficient envelope depends continuously on the real part. -/
theorem envelope_continuous : Continuous envelope := by
  exact ((Real.continuous_const_rpow (by norm_num : (3 : ℝ) ≠ 0)).comp
    continuous_neg).add ((Real.continuous_const_rpow (by norm_num : (4 : ℝ) ≠ 0)).comp
    continuous_neg)

/-- The exact coefficient envelope strictly decreases with the real part. -/
theorem envelope_strictAnti : StrictAnti envelope := by
  intro a b hab
  apply add_lt_add
  · exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hab)
  · exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_neg hab)

/-- At one half the coefficient envelope is strictly greater than one. -/
theorem one_lt_envelope_half : 1 < envelope (1 / 2) := by
  have hfour : (4 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 / 2 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), ← Real.sqrt_eq_rpow]
    norm_num
  have hthree := Real.rpow_lt_rpow_of_neg (x := (3 : ℝ)) (y := 4)
    (z := -(1 / 2)) (by norm_num) (by norm_num) (by norm_num)
  rw [hfour] at hthree
  dsimp [envelope]
  rw [hfour]
  linarith

/-- At one the coefficient envelope is strictly less than one. -/
theorem envelope_one_lt_one : envelope 1 < 1 := by
  norm_num [envelope, Real.rpow_neg_one]

/-- There is exactly one crossing of the unit coefficient ceiling between one half and one. -/
theorem exists_unique_cutoff : ∃! b : ℝ, 1 / 2 < b ∧ b < 1 ∧ envelope b = 1 := by
  obtain ⟨b, hb, heq⟩ := intermediate_value_Icc' (by norm_num : (1 / 2 : ℝ) ≤ 1)
    envelope_continuous.continuousOn
    (show (1 : ℝ) ∈ Set.Icc (envelope 1) (envelope (1 / 2)) from
      ⟨envelope_one_lt_one.le, one_lt_envelope_half.le⟩)
  have hlo : 1 / 2 < b := by
    by_contra h
    have hbeq : b = 1 / 2 := le_antisymm (le_of_not_gt h) hb.1
    rw [hbeq] at heq
    linarith [one_lt_envelope_half]
  have hhi : b < 1 := by
    by_contra h
    have hbeq : b = 1 := le_antisymm hb.2 (le_of_not_gt h)
    rw [hbeq] at heq
    linarith [envelope_one_lt_one]
  exact ⟨b, ⟨hlo, hhi, heq⟩, fun y hy => envelope_strictAnti.injective (hy.2.2.trans heq.symm)⟩

/-- The uniquely characterized crossing of the unit coefficient ceiling. -/
def cutoff : ℝ := Classical.choose exists_unique_cutoff

/-- The cutoff lies strictly inside the critical strip and has envelope exactly one. -/
theorem cutoff_spec : 1 / 2 < cutoff ∧ cutoff < 1 ∧ envelope cutoff = 1 :=
  (Classical.choose_spec exists_unique_cutoff).1

/-- The unit ceiling holds precisely on and to the right of its scalar cutoff. -/
theorem envelope_le_one_iff (sigma : ℝ) : envelope sigma ≤ 1 ↔ cutoff ≤ sigma := by
  rw [← cutoff_spec.2.2]
  exact envelope_strictAnti.le_iff_ge

/-- Exact real-part classification of the uniform unit coefficient bound. -/
theorem horizontal_unit_bound_iff (sigma : ℝ) :
    (∀ t : ℝ, ‖defect ((sigma : ℂ) + (t : ℂ) * I)‖ ≤ 1) ↔ cutoff ≤ sigma := by
  rw [horizontal_bound_iff, envelope_le_one_iff]

/-- Every real part below the cutoff violates the unit ceiling at the same explicit height. -/
theorem defect_exceeds_one_below_cutoff {sigma : ℝ} (hs : sigma < cutoff) :
    1 < ‖defect ((sigma : ℂ) + (height : ℂ) * I)‖ := by
  rw [norm_defect_at_height, ← cutoff_spec.2.2]
  exact envelope_strictAnti hs

/-- A literal strict-half-strip parameter with formal inverse violates the unit coefficient ceiling. -/
theorem exists_strict_half_strip_violation :
    ∃ s : ℂ, 1 / 2 < s.re ∧ s.re < 1 ∧ 1 < ‖defect s‖ := by
  let sigma : ℝ := (1 / 2 + cutoff) / 2
  have hlo : 1 / 2 < sigma := by dsimp [sigma]; linarith [cutoff_spec.1]
  have hmid : sigma < cutoff := by dsimp [sigma]; linarith [cutoff_spec.1]
  refine ⟨(sigma : ℂ) + (height : ℂ) * I, ?_, ?_, defect_exceeds_one_below_cutoff hmid⟩
  · simpa using hlo
  · simpa using hmid.trans cutoff_spec.2.1

end RHTower.AlternatingInverseCoefficient
