import Mathlib

/-!
# Character-domain formation mechanics

Finite formation syntax transports every leaf reporter by an affine sign/shift law.  The same
module certifies a concrete cofinal admission work which is zero only at the neutral character and
infinite everywhere else.
-/

open scoped ENNReal NNReal

namespace CharacterDomainFormation

inductive Polarity where
  | positive
  | negative
  deriving DecidableEq, Repr

def Polarity.act : Polarity → ℝ → ℝ
  | .positive, t => t
  | .negative, t => -t

def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

@[simp] theorem Polarity.positive_act (t : ℝ) : Polarity.positive.act t = t := rfl

@[simp] theorem Polarity.negative_act (t : ℝ) : Polarity.negative.act t = -t := rfl

@[simp] theorem Polarity.flip_act (p : Polarity) (t : ℝ) :
    p.flip.act t = p.act (-t) := by
  cases p <;> simp [Polarity.flip, Polarity.act]

@[simp] theorem Polarity.act_add (p : Polarity) (s t : ℝ) :
    p.act (s + t) = p.act s + p.act t := by
  cases p <;> simp [Polarity.act]
  ring

inductive Expr (ι : Type*) where
  | leaf (i : ι)
  | mix (left right : Expr ι)
  | fuse (left right : Expr ι)
  | tilt (a : ℝ) (child : Expr ι)
  | reflect (child : Expr ι)
  | recover (child : Expr ι)

structure Constraint (ι : Type*) where
  leaf : ι
  polarity : Polarity
  offset : ℝ

def Constraint.eval (c : Constraint ι) (t : ℝ) : ℝ :=
  c.polarity.act t + c.offset

def Constraint.shift (a : ℝ) (c : Constraint ι) : Constraint ι where
  leaf := c.leaf
  polarity := c.polarity
  offset := c.offset + c.polarity.act a

def Constraint.reflect (c : Constraint ι) : Constraint ι where
  leaf := c.leaf
  polarity := c.polarity.flip
  offset := c.offset

@[simp] theorem Constraint.eval_shift (c : Constraint ι) (a t : ℝ) :
    (c.shift a).eval t = c.eval (t + a) := by
  cases c with
  | mk leaf polarity offset =>
      cases polarity <;> simp [Constraint.shift, Constraint.eval, Polarity.act] <;> ring

@[simp] theorem Constraint.eval_reflect (c : Constraint ι) (t : ℝ) :
    c.reflect.eval t = c.eval (-t) := by
  cases c with
  | mk leaf polarity offset =>
      cases polarity <;> simp [Constraint.reflect, Constraint.eval, Polarity.flip, Polarity.act]

def Expr.constraints : Expr ι → List (Constraint ι)
  | .leaf i => [{ leaf := i, polarity := .positive, offset := 0 }]
  | .mix left right => left.constraints ++ right.constraints
  | .fuse left right => left.constraints ++ right.constraints
  | .tilt a child => child.constraints.map (Constraint.shift a)
  | .reflect child => child.constraints.map Constraint.reflect
  | .recover child => child.constraints

def Expr.Admitted (domain : ι → Set ℝ) : Expr ι → ℝ → Prop
  | .leaf i, t => t ∈ domain i
  | .mix left right, t => left.Admitted domain t ∧ right.Admitted domain t
  | .fuse left right, t => left.Admitted domain t ∧ right.Admitted domain t
  | .tilt a child, t => child.Admitted domain (t + a)
  | .reflect child, t => child.Admitted domain (-t)
  | .recover child, t => child.Admitted domain t

def Constraint.Holds (domain : ι → Set ℝ) (c : Constraint ι) (t : ℝ) : Prop :=
  c.eval t ∈ domain c.leaf

@[simp] theorem Constraint.shift_leaf (a : ℝ) (c : Constraint ι) :
    (c.shift a).leaf = c.leaf := rfl

@[simp] theorem Constraint.reflect_leaf (c : Constraint ι) : c.reflect.leaf = c.leaf := rfl

@[simp] theorem Constraint.holds_shift (domain : ι → Set ℝ) (a : ℝ) (c : Constraint ι) (t : ℝ) :
    (c.shift a).Holds domain t ↔ c.Holds domain (t + a) := by
  simp [Constraint.Holds]

@[simp] theorem Constraint.holds_reflect (domain : ι → Set ℝ) (c : Constraint ι) (t : ℝ) :
    c.reflect.Holds domain t ↔ c.Holds domain (-t) := by
  simp [Constraint.Holds]

/-- Every finite formation expression is admitted exactly when all affine leaf constraints hold. -/
theorem Expr.admitted_iff_constraints (domain : ι → Set ℝ) (E : Expr ι) (t : ℝ) :
    E.Admitted domain t ↔ ∀ c ∈ E.constraints, c.Holds domain t := by
  induction E generalizing t with
  | leaf i => simp [Expr.Admitted, Expr.constraints, Constraint.Holds, Constraint.eval]
  | mix left right ihLeft ihRight =>
      simp [Expr.Admitted, Expr.constraints, ihLeft, ihRight, or_imp, forall_and]
  | fuse left right ihLeft ihRight =>
      simp [Expr.Admitted, Expr.constraints, ihLeft, ihRight, or_imp, forall_and]
  | tilt a child ih =>
      simp [Expr.Admitted, Expr.constraints, ih (t + a)]
  | reflect child ih =>
      simp [Expr.Admitted, Expr.constraints, ih (-t)]
  | recover child ih =>
      simpa [Expr.Admitted, Expr.constraints] using ih t

/-- Recovery is exactly neutral for character admission. -/
@[simp] theorem Expr.recover_admitted_iff (domain : ι → Set ℝ) (E : Expr ι) (t : ℝ) :
    (Expr.recover E).Admitted domain t ↔ E.Admitted domain t := by
  rfl

/-- Reflection acts by negation on the reporter parameter. -/
@[simp] theorem Expr.reflect_admitted_iff (domain : ι → Set ℝ) (E : Expr ι) (t : ℝ) :
    (Expr.reflect E).Admitted domain t ↔ E.Admitted domain (-t) := by
  rfl

/-- Tilt acts by translation on the reporter parameter. -/
@[simp] theorem Expr.tilt_admitted_iff (domain : ι → Set ℝ) (E : Expr ι) (a t : ℝ) :
    (Expr.tilt a E).Admitted domain t ↔ E.Admitted domain (t + a) := by
  rfl

/-- Positive alternatives and independent fusion have the same intersection shadow on domains. -/
theorem Expr.mix_fuse_admission_same (domain : ι → Set ℝ) (E F : Expr ι) (t : ℝ) :
    (Expr.mix E F).Admitted domain t ↔ (Expr.fuse E F).Admitted domain t := by
  rfl

/-- Concrete cofinal relative-admission work for widths `1/(n+1)`. -/
noncomputable def cofinalWork (t : ℝ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * |t|)

@[simp] theorem cofinalWork_zero : cofinalWork 0 = 0 := by
  simp [cofinalWork]

theorem cofinalWork_eq_top_of_ne_zero {t : ℝ} (ht : t ≠ 0) : cofinalWork t = ⊤ := by
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro r
  have habs : 0 < |t| := abs_pos.mpr ht
  obtain ⟨n, hn⟩ := exists_nat_ge ((r : ℝ) / |t|)
  apply le_trans ?_ (le_iSup (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1) * |t|)) n)
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  calc
    (r : ℝ) = ((r : ℝ) / |t|) * |t| := by field_simp
    _ ≤ (n : ℝ) * |t| := mul_le_mul_of_nonneg_right hn (le_of_lt habs)
    _ ≤ ((n : ℝ) + 1) * |t| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg t)

/-- Cofinal work is finite exactly at the neutral character. -/
theorem cofinalWork_ne_top_iff (t : ℝ) : cofinalWork t ≠ ⊤ ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht
    exact h (cofinalWork_eq_top_of_ne_zero ht)
  · rintro rfl
    simp

/-- Every finite cofinal-work sublevel is the singleton neutral character. -/
theorem cofinalWork_le_coe_iff (t : ℝ) (C : ℝ≥0) :
    cofinalWork t ≤ (C : ℝ≥0∞) ↔ t = 0 := by
  constructor
  · intro h
    have hne : cofinalWork t ≠ ⊤ := by
      intro htop
      rw [htop] at h
      exact ENNReal.coe_ne_top (top_le_iff.mp h)
    exact (cofinalWork_ne_top_iff t).mp hne
  · rintro rfl
    simp

end CharacterDomainFormation
