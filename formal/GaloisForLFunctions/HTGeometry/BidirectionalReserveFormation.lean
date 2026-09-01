import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Bidirectional reserve-formation geometry

An unreduced history keeps positive and negative formation channels separately.  Its visible
current is their difference, while their minimum is hidden reserve.  Componentwise fusion creates
a nonnegative reserve transgression.  The transgression is an associative cocycle and pays exactly
half of every loss of visible current.

The same primitive forces the half-density exponent: diagonal-gauge invariance gives
`alpha + beta = 1`, reflection gives `alpha = beta`, hence both give `alpha = beta = 1/2`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- An unreduced forward/backward formation history in one ordered additive channel. -/
abbrev BidirectionalFormation (G : Type*) := G × G

namespace BidirectionalFormation

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- Functional-equation reflection swaps forward and backward formation. -/
def reflect (x : BidirectionalFormation G) : BidirectionalFormation G := (x.2, x.1)

/-- Oriented observer current. -/
def current (x : BidirectionalFormation G) : G := x.1 - x.2

/-- Phase-blind visible magnitude. -/
def visible (x : BidirectionalFormation G) : G := |current x|

/-- Common forward/backward formation hidden by the current observer. -/
def reserve (x : BidirectionalFormation G) : G := min x.1 x.2

/-- Complete unreduced formation activity. -/
def activity (x : BidirectionalFormation G) : G := x.1 + x.2

/-- Reserve created when two histories fuse componentwise. -/
def transgression (x y : BidirectionalFormation G) : G :=
  reserve (x + y) - reserve x - reserve y

@[simp]
theorem reflect_reflect (x : BidirectionalFormation G) : reflect (reflect x) = x := by
  cases x
  rfl

@[simp]
theorem current_reflect (x : BidirectionalFormation G) :
    current (reflect x) = -current x := by
  simp [current, reflect]

@[simp]
theorem visible_reflect (x : BidirectionalFormation G) :
    visible (reflect x) = visible x := by
  simp [visible]

@[simp]
theorem reserve_reflect (x : BidirectionalFormation G) :
    reserve (reflect x) = reserve x := by
  simp [reserve, reflect, min_comm]

@[simp]
theorem activity_reflect (x : BidirectionalFormation G) :
    activity (reflect x) = activity x := by
  simp [activity, reflect, add_comm]

/-- **Joint reconstruction.** Complete activity is visible current plus twice hidden reserve. -/
theorem activity_eq_visible_add_two_reserve (x : BidirectionalFormation G) :
    activity x = visible x + (2 : ℕ) • reserve x := by
  rcases x with ⟨p, q⟩
  simp only [activity, visible, current, reserve]
  have hmax : max p q - min p q = |p - q| := by
    rw [max_sub_min_eq_abs, abs_sub_comm]
  have hadd : max p q + min p q = p + q := max_add_min p q
  rw [← hmax, ← hadd]
  abel

/-- Fusion cannot destroy reserve: cross-direction cancellation only creates it. -/
theorem transgression_nonneg (x y : BidirectionalFormation G) :
    0 ≤ transgression x y := by
  rcases x with ⟨p, q⟩
  rcases y with ⟨r, s⟩
  simp only [transgression, reserve, Prod.fst_add, Prod.snd_add]
  have h : min p q + min r s ≤ min (p + r) (q + s) :=
    min_add_min_le_min_add_add
  rw [sub_sub]
  exact sub_nonneg.mpr h

/-- **Fusion conservation.** Lost visible current becomes exactly twice reserve transgression. -/
theorem visible_fusion_conservation (x y : BidirectionalFormation G) :
    visible x + visible y = visible (x + y) + (2 : ℕ) • transgression x y := by
  have hx := activity_eq_visible_add_two_reserve x
  have hy := activity_eq_visible_add_two_reserve y
  have hxy := activity_eq_visible_add_two_reserve (x + y)
  have hactivity : activity (x + y) = activity x + activity y := by
    rcases x with ⟨p, q⟩
    rcases y with ⟨r, s⟩
    simp only [activity, Prod.fst_add, Prod.snd_add]
    abel
  rw [hactivity, hx, hy] at hxy
  simp only [transgression]
  calc
    visible x + visible y =
        (visible x + (2 : ℕ) • reserve x) +
          (visible y + (2 : ℕ) • reserve y) -
            (2 : ℕ) • reserve x - (2 : ℕ) • reserve y := by abel
    _ = visible (x + y) + (2 : ℕ) • reserve (x + y) -
          (2 : ℕ) • reserve x - (2 : ℕ) • reserve y := by rw [hxy]
    _ = visible (x + y) +
          (2 : ℕ) • (reserve (x + y) - reserve x - reserve y) := by abel

/-- **Associative formation law.** Reserve transgression is a two-cocycle. -/
theorem transgression_cocycle (x y z : BidirectionalFormation G) :
    transgression x y + transgression (x + y) z =
      transgression y z + transgression x (y + z) := by
  rcases x with ⟨p, q⟩
  rcases y with ⟨r, s⟩
  rcases z with ⟨u, v⟩
  simp only [transgression, reserve, Prod.fst_add, Prod.snd_add, add_assoc]
  abel

@[simp]
theorem reflect_add (x y : BidirectionalFormation G) :
    reflect (x + y) = reflect x + reflect y := by
  cases x
  cases y
  rfl

/-- Reserve transgression is reflection-even. -/
@[simp]
theorem transgression_reflect (x y : BidirectionalFormation G) :
    transgression (reflect x) (reflect y) = transgression x y := by
  rw [transgression, ← reflect_add, reserve_reflect, reserve_reflect, reserve_reflect]
  rfl

/-- Fusion of two currents with the same nonnegative orientation creates no reserve. -/
theorem transgression_eq_zero_of_currents_nonneg
    (x y : BidirectionalFormation G) (hx : 0 ≤ current x) (hy : 0 ≤ current y) :
    transgression x y = 0 := by
  rcases x with ⟨p, q⟩
  rcases y with ⟨r, s⟩
  change 0 ≤ p - q at hx
  change 0 ≤ r - s at hy
  have hqp : q ≤ p := sub_nonneg.mp hx
  have hsr : s ≤ r := sub_nonneg.mp hy
  have hsum : q + s ≤ p + r := add_le_add hqp hsr
  simp [transgression, reserve, min_eq_right hqp, min_eq_right hsr,
    min_eq_right hsum]

/-- Fusion of two currents with the same nonpositive orientation creates no reserve. -/
theorem transgression_eq_zero_of_currents_nonpos
    (x y : BidirectionalFormation G) (hx : current x ≤ 0) (hy : current y ≤ 0) :
    transgression x y = 0 := by
  rcases x with ⟨p, q⟩
  rcases y with ⟨r, s⟩
  change p - q ≤ 0 at hx
  change r - s ≤ 0 at hy
  have hpq : p ≤ q := sub_nonpos.mp hx
  have hrs : r ≤ s := sub_nonpos.mp hy
  have hsum : p + r ≤ q + s := add_le_add hpq hrs
  simp [transgression, reserve, min_eq_left hpq, min_eq_left hrs,
    min_eq_left hsum]

/-- Oppositely oriented fusion creates exactly the smaller visible current as reserve. -/
theorem transgression_eq_min_visible_of_current_nonneg_nonpos
    (x y : BidirectionalFormation G) (hx : 0 ≤ current x) (hy : current y ≤ 0) :
    transgression x y = min (visible x) (visible y) := by
  rcases x with ⟨p, q⟩
  rcases y with ⟨r, s⟩
  change 0 ≤ p - q at hx
  change r - s ≤ 0 at hy
  have hqp : q ≤ p := sub_nonneg.mp hx
  have hrs : r ≤ s := sub_nonpos.mp hy
  simp only [current, visible, transgression, reserve, Prod.fst_add, Prod.snd_add]
  rw [abs_of_nonneg hx, abs_of_nonpos hy, neg_sub]
  rw [min_eq_right hqp, min_eq_left hrs]
  by_cases h : p - q ≤ s - r
  · have hsum : p + r ≤ q + s := by
      have hh := add_le_add_left h (q + r)
      convert hh using 1 <;> abel
    rw [min_eq_left h, min_eq_left hsum]
    abel
  · have h' : s - r ≤ p - q := le_of_not_ge h
    have hsum : q + s ≤ p + r := by
      have hh := add_le_add_left h' (q + r)
      convert hh using 1 <;> abel
    rw [min_eq_right h', min_eq_right hsum]
    abel

/-- The opposite orientation gives the same exact smaller-visible-current law. -/
theorem transgression_eq_min_visible_of_current_nonpos_nonneg
    (x y : BidirectionalFormation G) (hx : current x ≤ 0) (hy : 0 ≤ current y) :
    transgression x y = min (visible x) (visible y) := by
  have h := transgression_eq_min_visible_of_current_nonneg_nonpos
    (reflect x) (reflect y)
    (by simpa using neg_nonneg.mpr hx)
    (by simpa using neg_nonpos.mpr hy)
  simpa using h

end BidirectionalFormation

/-- Logarithmic monomial potential on reserve and the two formation channels. -/
def formationLogPotential (α β r x y : ℝ) : ℝ := r - α * x - β * y

/-- Diagonal gauge shift has exact anomaly `(1 - alpha - beta) t`. -/
theorem formationLogPotential_gauge_shift (α β r x y t : ℝ) :
    formationLogPotential α β (r + t) (x + t) (y + t) -
      formationLogPotential α β r x y = (1 - α - β) * t := by
  simp [formationLogPotential]
  ring

/-- Diagonal-gauge invariance forces and is forced by complementary exponents. -/
theorem formationLogPotential_diagonalGaugeInvariant_iff (α β : ℝ) :
    (∀ r x y t, formationLogPotential α β (r + t) (x + t) (y + t) =
      formationLogPotential α β r x y) ↔ α + β = 1 := by
  constructor
  · intro h
    have h1 := h 0 0 0 1
    simp [formationLogPotential] at h1
    linarith
  · intro hab r x y t
    have hdiff := formationLogPotential_gauge_shift α β r x y t
    have hz : 1 - α - β = 0 := by linarith
    rw [hz, zero_mul] at hdiff
    exact sub_eq_zero.mp hdiff

/-- Reflection invariance forces and is forced by equal exponents. -/
theorem formationLogPotential_reflectionInvariant_iff (α β : ℝ) :
    (∀ r x y, formationLogPotential α β r y x = formationLogPotential α β r x y) ↔
      α = β := by
  constructor
  · intro h
    have h1 := h 0 1 0
    simp [formationLogPotential] at h1
    linarith
  · rintro rfl
    intro r x y
    simp [formationLogPotential]
    ring

/-- **Half-density uniqueness.** Diagonal gauge plus reflection force exponent `1/2`. -/
theorem formationLogPotential_gauge_reflection_unique (α β : ℝ) :
    ((∀ r x y t, formationLogPotential α β (r + t) (x + t) (y + t) =
        formationLogPotential α β r x y) ∧
      (∀ r x y, formationLogPotential α β r y x = formationLogPotential α β r x y)) ↔
      α = 1 / 2 ∧ β = 1 / 2 := by
  rw [formationLogPotential_diagonalGaugeInvariant_iff,
    formationLogPotential_reflectionInvariant_iff]
  constructor
  · rintro ⟨hsum, heq⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-- The unique balanced potential is minus one half of visible current. -/
theorem criticalFormationLogPotential_eq_neg_visible_half (x y : ℝ) :
    formationLogPotential (1 / 2) (1 / 2) (min x y) x y = -|x - y| / 2 := by
  have h := BidirectionalFormation.activity_eq_visible_add_two_reserve (G := ℝ) (x, y)
  simp only [BidirectionalFormation.activity, BidirectionalFormation.visible,
    BidirectionalFormation.current, BidirectionalFormation.reserve, nsmul_eq_mul] at h
  simp [formationLogPotential]
  norm_num at h ⊢
  linarith

/-- Positivity is the exponential quotient `exp (-visible / 2)` at the forced exponent. -/
theorem criticalFormationExpPotential_eq_exp_neg_visible_half (x y : ℝ) :
    Real.exp (formationLogPotential (1 / 2) (1 / 2) (min x y) x y) =
      Real.exp (-|x - y| / 2) := by
  rw [criticalFormationLogPotential_eq_neg_visible_half]

end GaloisForLFunctions.HTGeometry
