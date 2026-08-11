import Mathlib.Analysis.Normed.Module.Basic

/-!
# Constitutive passive-cycle mechanics

Work lost by heterogeneous process transitions composes exactly.  If every leg of a closed process
cycle is passive in one source work norm, every defect current on the cycle vanishes.  A strict
zero-defect detector therefore selects its neutral locus.  These results separate dissipative
defect from conservative phase/history without any RH premise or computation proof.
-/

namespace GaloisForLFunctions.HTGeometry

variable {E F G : Type*}

/-- Work lost by one heterogeneous process transition. -/
def workDefect (WE : E → ℝ) (WF : F → ℝ) (f : E → F) (x : E) : ℝ :=
  WE x - WF (f x)

/-- Work defects compose exactly through a heterogeneous process chain. -/
theorem workDefect_comp (WE : E → ℝ) (WF : F → ℝ) (WG : G → ℝ)
    (f : E → F) (g : F → G) (x : E) :
    workDefect WE WG (g ∘ f) x =
      workDefect WE WF f x + workDefect WF WG g (f x) := by
  simp [workDefect]

/-- Norm work lost by one process transition. -/
def passiveDefect [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (f : E → F) (x : E) : ℝ :=
  ‖x‖ - ‖f x‖

/-- Passivity is exactly nonnegativity of the defect current. -/
theorem passiveDefect_nonneg_iff
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (f : E → F) (x : E) :
    0 ≤ passiveDefect f x ↔ ‖f x‖ ≤ ‖x‖ := by
  exact sub_nonneg

/-- Passive norm defects obey exact serial conservation. -/
theorem passiveDefect_comp
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [SeminormedAddCommGroup G]
    (f : E → F) (g : F → G) (x : E) :
    passiveDefect (g ∘ f) x =
      passiveDefect f x + passiveDefect g (f x) := by
  simp [passiveDefect]

/-- A passive map with a passive pointwise reconstruction preserves norm. -/
theorem passive_split_cycle_norm_eq
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (q : E → F) (r : F → E) (x : E)
    (hq : ‖q x‖ ≤ ‖x‖)
    (hr : ∀ y : F, ‖r y‖ ≤ ‖y‖)
    (hsplit : r (q x) = x) :
    ‖q x‖ = ‖x‖ := by
  apply le_antisymm hq
  calc
    ‖x‖ = ‖r (q x)‖ := (congrArg norm hsplit).symm
    _ ≤ ‖q x‖ := hr (q x)

/-- Every leg of a passive two-cycle has zero defect. -/
theorem passive_split_cycle_defects_eq_zero
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (q : E → F) (r : F → E) (x : E)
    (hq : ‖q x‖ ≤ ‖x‖)
    (hr : ∀ y : F, ‖r y‖ ≤ ‖y‖)
    (hsplit : r (q x) = x) :
    passiveDefect q x = 0 ∧ passiveDefect r (q x) = 0 := by
  have hnorm := passive_split_cycle_norm_eq q r x hq hr hsplit
  constructor
  · simp [passiveDefect, hnorm]
  · simp [passiveDefect, hsplit, hnorm]

/-- Every leg of a passive heterogeneous three-cycle has zero defect. -/
theorem passive_three_cycle_defects_eq_zero
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [SeminormedAddCommGroup G]
    (f : E → F) (g : F → G) (h : G → E) (x : E)
    (hf : ‖f x‖ ≤ ‖x‖)
    (hg : ‖g (f x)‖ ≤ ‖f x‖)
    (hh : ‖h (g (f x))‖ ≤ ‖g (f x)‖)
    (hcycle : h (g (f x)) = x) :
    passiveDefect f x = 0 ∧
      passiveDefect g (f x) = 0 ∧
      passiveDefect h (g (f x)) = 0 := by
  have hback : ‖x‖ ≤ ‖g (f x)‖ := by
    calc
      ‖x‖ = ‖h (g (f x))‖ := (congrArg norm hcycle).symm
      _ ≤ ‖g (f x)‖ := hh
  have hgf : ‖g (f x)‖ = ‖x‖ :=
    le_antisymm (hg.trans hf) hback
  have hfx : ‖f x‖ = ‖x‖ :=
    le_antisymm hf (hback.trans hg)
  simp [passiveDefect, hcycle, hgf, hfx]

/-- A strict zero-defect detector selects its neutral locus on every passive split cycle. -/
theorem neutral_of_passive_split_cycle
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (q : E → F) (r : F → E) (x : E)
    (Neutral : E → Prop)
    (hq : ‖q x‖ ≤ ‖x‖)
    (hr : ∀ y : F, ‖r y‖ ≤ ‖y‖)
    (hsplit : r (q x) = x)
    (hstrict : passiveDefect q x = 0 → Neutral x) :
    Neutral x :=
  hstrict (passive_split_cycle_defects_eq_zero q r x hq hr hsplit).1

/-- A passive closed three-cycle cannot contain a strictly positive defect leg. -/
theorem no_positive_defect_in_passive_three_cycle
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [SeminormedAddCommGroup G]
    (f : E → F) (g : F → G) (h : G → E) (x : E)
    (hf : ‖f x‖ ≤ ‖x‖)
    (hg : ‖g (f x)‖ ≤ ‖f x‖)
    (hh : ‖h (g (f x))‖ ≤ ‖g (f x)‖)
    (hcycle : h (g (f x)) = x) :
    ¬ (0 < passiveDefect f x ∨
      0 < passiveDefect g (f x) ∨
      0 < passiveDefect h (g (f x))) := by
  obtain ⟨hf0, hg0, hh0⟩ :=
    passive_three_cycle_defects_eq_zero f g h x hf hg hh hcycle
  simp [hf0, hg0, hh0]

end GaloisForLFunctions.HTGeometry
