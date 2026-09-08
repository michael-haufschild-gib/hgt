import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Exact conservation and exchange in a two-mode collision block

The orthogonal correction in arXiv:2608.29825, equation (34), removes the
energy direction and retains the perpendicular exchange direction. Writing
the invariant direction as `(1,b)` removes all positivity premises: its
squared length is positive for every real `b`. The paper's two Laguerre rows
are obtained by taking `b = sqrt ((2/3) * (ν+1))` whenever `ν+1` is nonnegative.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Conserved linear combination of the two mode coefficients. -/
def collisionInvariant (b : ℝ) (x : ℝ × ℝ) : ℝ := x.1 + b * x.2

/-- Coefficient along the perpendicular energy-exchange direction. -/
def collisionExchange (b : ℝ) (x : ℝ × ℝ) : ℝ := x.2 - b * x.1

/-- Orthogonal removal of the invariant direction, retaining energy exchange. -/
def collisionConservationProject (b : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (-b * collisionExchange b x / (1 + b ^ 2),
    collisionExchange b x / (1 + b ^ 2))

/-- The denominator never degenerates, including at zero internal weight. -/
theorem collisionModeDenominator_pos (b : ℝ) : 0 < 1 + b ^ 2 := by positivity

/-- Every corrected collision column conserves the prescribed total energy. -/
@[simp] theorem collisionInvariant_project (b : ℝ) (x : ℝ × ℝ) :
    collisionInvariant b (collisionConservationProject b x) = 0 := by
  simp only [collisionInvariant, collisionConservationProject]
  ring

/-- Conservation correction leaves the physical exchange coefficient unchanged. -/
@[simp] theorem collisionExchange_project (b : ℝ) (x : ℝ × ℝ) :
    collisionExchange b (collisionConservationProject b x) = collisionExchange b x := by
  have hd := ne_of_gt (collisionModeDenominator_pos b)
  simp only [collisionExchange, collisionConservationProject]
  field_simp
  ring

/-- Repeating the correction changes nothing. -/
@[simp] theorem collisionConservationProject_idempotent (b : ℝ) (x : ℝ × ℝ) :
    collisionConservationProject b (collisionConservationProject b x) =
      collisionConservationProject b x := by
  change (-b * collisionExchange b (collisionConservationProject b x) / (1 + b ^ 2),
    collisionExchange b (collisionConservationProject b x) / (1 + b ^ 2)) = _
  rw [collisionExchange_project]
  rfl

/-- Exact invariant/exchange reconstruction of an arbitrary row pair. -/
theorem collisionMode_reconstruction (b : ℝ) (x : ℝ × ℝ) :
    x = ((collisionInvariant b x - b * collisionExchange b x) / (1 + b ^ 2),
      (b * collisionInvariant b x + collisionExchange b x) / (1 + b ^ 2)) := by
  have hd := ne_of_gt (collisionModeDenominator_pos b)
  apply Prod.ext <;> simp only [collisionInvariant, collisionExchange] <;>
    field_simp <;> ring

/-- The correction is exactly identity minus the rank-one invariant projector. -/
theorem collisionConservationProject_eq_sub (b : ℝ) (x : ℝ × ℝ) :
    collisionConservationProject b x =
      (x.1 - collisionInvariant b x / (1 + b ^ 2),
       x.2 - b * collisionInvariant b x / (1 + b ^ 2)) := by
  have hd := ne_of_gt (collisionModeDenominator_pos b)
  apply Prod.ext <;>
    simp only [collisionConservationProject, collisionInvariant, collisionExchange] <;>
    field_simp <;> ring

/-- Fixed rows are precisely the energy-conserving rows. -/
theorem collisionConservationProject_fixed_iff (b : ℝ) (x : ℝ × ℝ) :
    collisionConservationProject b x = x ↔ collisionInvariant b x = 0 := by
  constructor
  · intro h
    simpa only [h] using collisionInvariant_project b x
  · intro h
    rw [collisionConservationProject_eq_sub, h]
    simp

/-- The correction kills exactly the pure invariant direction. -/
theorem collisionConservationProject_zero_iff (b : ℝ) (x : ℝ × ℝ) :
    collisionConservationProject b x = 0 ↔ collisionExchange b x = 0 := by
  constructor
  · intro h
    have := collisionExchange_project b x
    simpa [h, collisionExchange] using this.symm
  · intro h
    simp [collisionConservationProject, h]

/-- Invariant and exchange coordinates account for the entire Euclidean energy. -/
theorem collisionMode_pythagoras (b : ℝ) (x : ℝ × ℝ) :
    collisionInvariant b x ^ 2 + collisionExchange b x ^ 2 =
      (1 + b ^ 2) * (x.1 ^ 2 + x.2 ^ 2) := by
  simp only [collisionInvariant, collisionExchange]
  ring

/-- Exact energy removed by conservation correction. -/
theorem collisionConservationProject_energy (b : ℝ) (x : ℝ × ℝ) :
    (collisionConservationProject b x).1 ^ 2 +
      (collisionConservationProject b x).2 ^ 2 +
      collisionInvariant b x ^ 2 / (1 + b ^ 2) = x.1 ^ 2 + x.2 ^ 2 := by
  have hd := ne_of_gt (collisionModeDenominator_pos b)
  simp only [collisionConservationProject, collisionInvariant, collisionExchange]
  field_simp
  ring

/-- Correction cannot increase the squared Euclidean norm. -/
theorem collisionConservationProject_contractive (b : ℝ) (x : ℝ × ℝ) :
    (collisionConservationProject b x).1 ^ 2 +
      (collisionConservationProject b x).2 ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
  have hp : 0 ≤ collisionInvariant b x ^ 2 / (1 + b ^ 2) := by positivity
  linarith [collisionConservationProject_energy b x]

/-- Scalar multiplication commutes with correction. -/
theorem collisionConservationProject_smul (b c : ℝ) (x : ℝ × ℝ) :
    collisionConservationProject b (c • x) = c • collisionConservationProject b x := by
  apply Prod.ext <;>
    simp only [collisionConservationProject, collisionExchange, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul] <;> ring

/-- Adding physical channels commutes with correction. -/
theorem collisionConservationProject_add (b : ℝ) (x y : ℝ × ℝ) :
    collisionConservationProject b (x + y) =
      collisionConservationProject b x + collisionConservationProject b y := by
  apply Prod.ext <;>
    simp only [collisionConservationProject, collisionExchange, Prod.fst_add,
      Prod.snd_add] <;> ring

/-- The surviving exchange vector is never removed. -/
theorem collisionConservationProject_exchangeVector (b c : ℝ) :
    collisionConservationProject b (-b * c, c) = (-b * c, c) := by
  apply (collisionConservationProject_fixed_iff b _).mpr
  simp only [collisionInvariant]
  ring

/-- The invariant vector is removed exactly. -/
theorem collisionConservationProject_invariantVector (b c : ℝ) :
    collisionConservationProject b (c, b * c) = 0 := by
  apply (collisionConservationProject_zero_iff b _).mpr
  simp [collisionExchange]

/-- Exact relaxation preserving the invariant and damping the exchange direction. -/
def collisionRelaxation (b r t : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  x + (Real.exp (-r ^ 2 * t) - 1) • collisionConservationProject b x

/-- Total energy is constant along the relaxation at every real time. -/
theorem collisionRelaxation_invariant (b r t : ℝ) (x : ℝ × ℝ) :
    collisionInvariant b (collisionRelaxation b r t x) = collisionInvariant b x := by
  simp only [collisionInvariant, collisionRelaxation, collisionConservationProject,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The exchange mode obeys the exact Landau--Teller exponential law. -/
theorem collisionRelaxation_exchange (b r t : ℝ) (x : ℝ × ℝ) :
    collisionExchange b (collisionRelaxation b r t x) =
      Real.exp (-r ^ 2 * t) * collisionExchange b x := by
  have hd := ne_of_gt (collisionModeDenominator_pos b)
  simp only [collisionExchange, collisionRelaxation, collisionConservationProject,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  field_simp
  ring

/-- The complete row pair, rather than only its energy, satisfies the semigroup law. -/
theorem collisionRelaxation_add_time (b r s t : ℝ) (x : ℝ × ℝ) :
    collisionRelaxation b r (s + t) x =
      collisionRelaxation b r s (collisionRelaxation b r t x) := by
  have he : Real.exp (-r ^ 2 * (s + t)) =
      Real.exp (-r ^ 2 * s) * Real.exp (-r ^ 2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [collisionRelaxation, collisionConservationProject_add,
    collisionConservationProject_smul, collisionConservationProject_idempotent, he]
  module

end GaloisForLFunctions.HTGeometry
