import Mathlib

/-!
# The killed Dirichlet form of a finite reversible chain

A finite reversible Markov chain carries a stationary inner product in which the transition operator
is self-adjoint.  Killing it at a fixed rate produces a strictly positive operator whose quadratic
form splits into a mass term and a gate-gradient term, and whose spectrum is confined to a window
around one.

That two-sided bound makes the killed operator invertible, so the form defines a genuine inner
product and its dual negative-energy norm.  Cauchy--Schwarz for the killed form, together with the
window, is the entire analytic content of discounted capacity estimates.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

/-- A finite reversible Markov chain with a strictly positive stationary probability law. -/
structure ReversibleChain (S : Type*) [Fintype S] where
  /-- The one-step transition law. -/
  kernel : S → S → ℝ
  /-- The stationary law. -/
  stat : S → ℝ
  kernel_nonneg : ∀ x y, 0 ≤ kernel x y
  row_sum : ∀ x, ∑ y, kernel x y = 1
  stat_pos : ∀ x, 0 < stat x
  stat_sum : ∑ x, stat x = 1
  reversible : ∀ x y, stat x * kernel x y = stat y * kernel y x

namespace ReversibleChain

variable {S : Type*} [Fintype S] [DecidableEq S] (C : ReversibleChain S)

/-- The stationary inner product. -/
def inner (f g : S → ℝ) : ℝ := ∑ x, C.stat x * (f x * g x)

/-- One transition step applied to a function. -/
def step (f : S → ℝ) : S → ℝ := fun x => ∑ y, C.kernel x y * f y

/-- The killed operator `I - a P`. -/
def killed (a : ℝ) (f : S → ℝ) : S → ℝ := fun x => f x - a * C.step f x

/-- The killed Dirichlet form. -/
def energyBil (a : ℝ) (f g : S → ℝ) : ℝ := C.inner f (C.killed a g)

/-- The killed Dirichlet energy. -/
def energy (a : ℝ) (f : S → ℝ) : ℝ := C.energyBil a f f

theorem inner_comm (f g : S → ℝ) : C.inner f g = C.inner g f := by
  simp only [inner]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem inner_nonneg (f : S → ℝ) : 0 ≤ C.inner f f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (C.stat_pos x).le (mul_self_nonneg _)

theorem inner_self_eq_zero {f : S → ℝ} (h : C.inner f f = 0) : f = 0 := by
  funext x
  have hterm : ∀ y ∈ Finset.univ, 0 ≤ C.stat y * (f y * f y) := fun y _ =>
    mul_nonneg (C.stat_pos y).le (mul_self_nonneg _)
  have hx := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h x (Finset.mem_univ x)
  have := mul_eq_zero.mp hx
  rcases this with h1 | h2
  · exact absurd h1 (C.stat_pos x).ne'
  · exact mul_self_eq_zero.mp h2

theorem inner_add_left (f g h : S → ℝ) :
    C.inner (f + g) h = C.inner f h + C.inner g h := by
  simp only [inner, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem inner_smul_left (c : ℝ) (f g : S → ℝ) : C.inner (c • f) g = c * C.inner f g := by
  simp only [inner, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem step_add (f g : S → ℝ) : C.step (f + g) = C.step f + C.step g := by
  funext x
  simp only [step, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem step_smul (c : ℝ) (f : S → ℝ) : C.step (c • f) = c • C.step f := by
  funext x
  simp only [step, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem killed_add (a : ℝ) (f g : S → ℝ) :
    C.killed a (f + g) = C.killed a f + C.killed a g := by
  funext x
  simp only [killed, step_add, Pi.add_apply]
  ring

theorem killed_smul (a c : ℝ) (f : S → ℝ) : C.killed a (c • f) = c • C.killed a f := by
  funext x
  simp only [killed, step_smul, Pi.smul_apply, smul_eq_mul]
  ring

/-- The transition operator is self-adjoint for the stationary inner product. -/
theorem inner_step_symm (f g : S → ℝ) : C.inner f (C.step g) = C.inner (C.step f) g := by
  simp only [inner, step, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  have h := C.reversible x y
  calc C.stat x * (f x * (C.kernel x y * g y))
      = (C.stat x * C.kernel x y) * (f x * g y) := by ring
    _ = (C.stat y * C.kernel y x) * (f x * g y) := by rw [h]
    _ = C.stat y * (C.kernel y x * f x * g y) := by ring

/-- Expansion of the killed form into a mass term and a transition term. -/
theorem inner_killed_expand (a : ℝ) (f g : S → ℝ) :
    C.inner f (C.killed a g) = C.inner f g - a * C.inner f (C.step g) := by
  simp only [inner, killed, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The killed operator is self-adjoint for the stationary inner product. -/
theorem inner_killed_symm (a : ℝ) (f g : S → ℝ) :
    C.inner f (C.killed a g) = C.inner (C.killed a f) g := by
  rw [inner_killed_expand, inner_comm C (C.killed a f) g, inner_killed_expand,
    inner_comm C g f, inner_comm C g (C.step f), inner_step_symm]

theorem energyBil_symm (a : ℝ) (f g : S → ℝ) : C.energyBil a f g = C.energyBil a g f := by
  rw [energyBil, energyBil, inner_killed_symm, inner_comm]

/-- The gate-gradient form. -/
def gradSq (f : S → ℝ) : ℝ := ∑ x, ∑ y, C.stat x * C.kernel x y * (f x - f y) ^ (2 : ℕ)

/-- The gate-sum form. -/
def sumSq (f : S → ℝ) : ℝ := ∑ x, ∑ y, C.stat x * C.kernel x y * (f x + f y) ^ (2 : ℕ)

theorem gradSq_nonneg (f : S → ℝ) : 0 ≤ C.gradSq f :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (C.stat_pos x).le (C.kernel_nonneg x y)) (sq_nonneg _)

theorem sumSq_nonneg (f : S → ℝ) : 0 ≤ C.sumSq f :=
  Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
    mul_nonneg (mul_nonneg (C.stat_pos x).le (C.kernel_nonneg x y)) (sq_nonneg _)

theorem double_sum_target (h : S → ℝ) :
    ∑ x, ∑ y, C.stat x * C.kernel x y * h y = ∑ y, C.stat y * h y := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hrev : ∀ x : S, C.stat x * C.kernel x y * h y = C.stat y * C.kernel y x * h y := by
    intro x
    rw [C.reversible x y]
  rw [Finset.sum_congr rfl fun x _ => hrev x, ← Finset.sum_mul, ← Finset.mul_sum, C.row_sum y,
    mul_one]

theorem double_sum_source (h : S → ℝ) :
    ∑ x, ∑ y, C.stat x * C.kernel x y * h x = ∑ x, C.stat x * h x := by
  refine Finset.sum_congr rfl fun x _ => ?_
  have : ∀ y : S, C.stat x * C.kernel x y * h x = (C.stat x * h x) * C.kernel x y := by
    intro y; ring
  rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.mul_sum, C.row_sum x, mul_one]

theorem inner_step_eq_double_sum (f : S → ℝ) :
    C.inner f (C.step f) = ∑ x, ∑ y, C.stat x * C.kernel x y * (f x * f y) := by
  simp only [inner, step, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- The gate-gradient identity of a reversible chain. -/
theorem inner_sub_step_eq (f : S → ℝ) :
    C.inner f f - C.inner f (C.step f) = C.gradSq f / 2 := by
  have hsq : ∀ x y : S, C.stat x * C.kernel x y * (f x - f y) ^ (2 : ℕ) =
      C.stat x * C.kernel x y * (f x * f x) + C.stat x * C.kernel x y * (f y * f y) -
        2 * (C.stat x * C.kernel x y * (f x * f y)) := by
    intro x y; ring
  have hself : C.inner f f = ∑ x, C.stat x * (f x * f x) := rfl
  have h1 : ∑ x, ∑ y, C.stat x * C.kernel x y * (f x * f x) = C.inner f f := by
    rw [double_sum_source C (fun x => f x * f x), hself]
  have h2 : ∑ x, ∑ y, C.stat x * C.kernel x y * (f y * f y) = C.inner f f := by
    rw [double_sum_target C (fun y => f y * f y), hself]
  have hexp : C.gradSq f =
      (∑ x, ∑ y, C.stat x * C.kernel x y * (f x * f x)) +
        (∑ x, ∑ y, C.stat x * C.kernel x y * (f y * f y)) -
        2 * ∑ x, ∑ y, C.stat x * C.kernel x y * (f x * f y) := by
    simp only [gradSq, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsq x y
  rw [hexp, h1, h2, ← inner_step_eq_double_sum]
  ring

/-- The gate-sum identity of a reversible chain. -/
theorem inner_add_step_eq (f : S → ℝ) :
    C.inner f f + C.inner f (C.step f) = C.sumSq f / 2 := by
  have hsq : ∀ x y : S, C.stat x * C.kernel x y * (f x + f y) ^ (2 : ℕ) =
      C.stat x * C.kernel x y * (f x * f x) + C.stat x * C.kernel x y * (f y * f y) +
        2 * (C.stat x * C.kernel x y * (f x * f y)) := by
    intro x y; ring
  have hself : C.inner f f = ∑ x, C.stat x * (f x * f x) := rfl
  have h1 : ∑ x, ∑ y, C.stat x * C.kernel x y * (f x * f x) = C.inner f f := by
    rw [double_sum_source C (fun x => f x * f x), hself]
  have h2 : ∑ x, ∑ y, C.stat x * C.kernel x y * (f y * f y) = C.inner f f := by
    rw [double_sum_target C (fun y => f y * f y), hself]
  have hexp : C.sumSq f =
      (∑ x, ∑ y, C.stat x * C.kernel x y * (f x * f x)) +
        (∑ x, ∑ y, C.stat x * C.kernel x y * (f y * f y)) +
        2 * ∑ x, ∑ y, C.stat x * C.kernel x y * (f x * f y) := by
    simp only [sumSq, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hsq x y
  rw [hexp, h1, h2, ← inner_step_eq_double_sum]
  ring

/-- **Exact gate-gradient energy.**  The killed energy splits into a mass term and a
gate-gradient term. -/
theorem energy_eq (a : ℝ) (f : S → ℝ) :
    C.energy a f = (1 - a) * C.inner f f + a * (C.gradSq f / 2) := by
  rw [energy, energyBil, inner_killed_expand, ← inner_sub_step_eq]
  ring

theorem energy_eq_sub (a : ℝ) (f : S → ℝ) :
    C.energy a f = (1 + a) * C.inner f f - a * (C.sumSq f / 2) := by
  rw [energy, energyBil, inner_killed_expand, ← inner_add_step_eq]
  ring

/-- **Killed spectral window.**  The killed energy is confined between the two multiples of the
stationary norm. -/
theorem energy_window {a : ℝ} (ha0 : 0 ≤ a) (f : S → ℝ) :
    (1 - a) * C.inner f f ≤ C.energy a f ∧ C.energy a f ≤ (1 + a) * C.inner f f := by
  constructor
  · rw [energy_eq]
    have := mul_nonneg ha0 (div_nonneg (C.gradSq_nonneg f) (by norm_num : (0:ℝ) ≤ 2))
    linarith
  · rw [energy_eq_sub]
    have := mul_nonneg ha0 (div_nonneg (C.sumSq_nonneg f) (by norm_num : (0:ℝ) ≤ 2))
    linarith

theorem energy_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (f : S → ℝ) : 0 ≤ C.energy a f := by
  refine le_trans ?_ (C.energy_window ha0 f).1
  exact mul_nonneg (by linarith) (C.inner_nonneg f)

theorem energy_eq_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {f : S → ℝ} (h : C.energy a f = 0) :
    f = 0 := by
  have hle := (C.energy_window ha0 f).1
  rw [h] at hle
  have hinner : C.inner f f ≤ 0 := by
    by_contra hc
    have hpos : 0 < C.inner f f := lt_of_not_ge hc
    nlinarith
  exact C.inner_self_eq_zero (le_antisymm hinner (C.inner_nonneg f))


theorem inner_add_right (f g h : S → ℝ) :
    C.inner f (g + h) = C.inner f g + C.inner f h := by
  rw [inner_comm, inner_add_left, inner_comm C g f, inner_comm C h f]

theorem inner_smul_right (c : ℝ) (f g : S → ℝ) : C.inner f (c • g) = c * C.inner f g := by
  rw [inner_comm, inner_smul_left, inner_comm C g f]

theorem energyBil_add_right (a : ℝ) (f g h : S → ℝ) :
    C.energyBil a f (g + h) = C.energyBil a f g + C.energyBil a f h := by
  rw [energyBil, energyBil, energyBil, killed_add, inner_add_right]

theorem energyBil_smul_right (a c : ℝ) (f g : S → ℝ) :
    C.energyBil a f (c • g) = c * C.energyBil a f g := by
  rw [energyBil, energyBil, killed_smul, inner_smul_right]

theorem energyBil_add_left (a : ℝ) (f g h : S → ℝ) :
    C.energyBil a (f + g) h = C.energyBil a f h + C.energyBil a g h := by
  rw [energyBil_symm, energyBil_add_right, energyBil_symm C a h f, energyBil_symm C a h g]

theorem energyBil_smul_left (a c : ℝ) (f g : S → ℝ) :
    C.energyBil a (c • f) g = c * C.energyBil a f g := by
  rw [energyBil_symm, energyBil_smul_right, energyBil_symm C a g f]

theorem energy_add_smul (a t : ℝ) (f g : S → ℝ) :
    C.energy a (f + t • g) =
      C.energy a f + 2 * t * C.energyBil a f g + t ^ (2 : ℕ) * C.energy a g := by
  rw [energy, energyBil_add_left, energyBil_add_right, energyBil_add_right,
    energyBil_smul_left, energyBil_smul_right, energyBil_smul_right, energyBil_smul_left,
    energyBil_symm C a g f, energy, energy]
  ring

/-- **Cauchy--Schwarz for the killed Dirichlet form.** -/
theorem energyBil_sq_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (f g : S → ℝ) :
    (C.energyBil a f g) ^ (2 : ℕ) ≤ C.energy a f * C.energy a g := by
  have hquad : ∀ t : ℝ,
      0 ≤ C.energy a g * (t * t) + 2 * C.energyBil a f g * t + C.energy a f := by
    intro t
    have h := C.energy_nonneg ha0 ha1 (f + t • g)
    rw [energy_add_smul] at h
    nlinarith [h]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- The killed operator as a linear endomorphism. -/
def killedLin (a : ℝ) : (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := C.killed a
  map_add' := C.killed_add a
  map_smul' := fun c f => C.killed_smul a c f

theorem killedLin_apply (a : ℝ) (f : S → ℝ) : C.killedLin a f = C.killed a f := rfl

theorem killedLin_injective {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Function.Injective (C.killedLin a) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine C.energy_eq_zero ha0 ha1 ?_
  rw [energy, energyBil, ← killedLin_apply, hf]
  simp [inner]

theorem killedLin_surjective {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Function.Surjective (C.killedLin a) :=
  LinearMap.injective_iff_surjective.mp (C.killedLin_injective ha0 ha1)

open Classical in
/-- The inverse of the killed operator. -/
noncomputable def killedInv (a : ℝ) (g : S → ℝ) : S → ℝ :=
  if h : ∃ u, C.killed a u = g then h.choose else 0

theorem killed_killedInv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (g : S → ℝ) :
    C.killed a (C.killedInv a g) = g := by
  classical
  have hex : ∃ u, C.killed a u = g := by
    obtain ⟨u, hu⟩ := C.killedLin_surjective ha0 ha1 g
    exact ⟨u, hu⟩
  rw [killedInv, dif_pos hex]
  exact hex.choose_spec

/-- The dual negative-energy square of a signed density. -/
noncomputable def negEnergySq (a : ℝ) (g : S → ℝ) : ℝ := C.inner g (C.killedInv a g)

theorem energy_killedInv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (g : S → ℝ) :
    C.energy a (C.killedInv a g) = C.negEnergySq a g := by
  rw [energy, energyBil, C.killed_killedInv ha0 ha1, negEnergySq, C.inner_comm]

theorem inner_eq_energyBil_killedInv {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (g h : S → ℝ) :
    C.inner g h = C.energyBil a (C.killedInv a g) h := by
  rw [energyBil, C.inner_killed_symm, C.killed_killedInv ha0 ha1]

/-- **Dual capacity bound.**  The pairing of a signed density with a function is controlled by the
killed energy of the function and the dual negative-energy square of the density. -/
theorem inner_sq_le_energy_mul_negEnergySq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (g h : S → ℝ) :
    (C.inner g h) ^ (2 : ℕ) ≤ C.negEnergySq a g * C.energy a h := by
  rw [C.inner_eq_energyBil_killedInv ha0 ha1]
  refine le_trans (C.energyBil_sq_le ha0 ha1.le _ h) (le_of_eq ?_)
  rw [C.energy_killedInv ha0 ha1]

theorem negEnergySq_nonneg {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (g : S → ℝ) :
    0 ≤ C.negEnergySq a g := by
  rw [← C.energy_killedInv ha0 ha1]
  exact C.energy_nonneg ha0 ha1.le _

/-- **Global discrepancy obstruction.**  The dual negative-energy square dominates the chi-square
divergence up to the killed spectral radius. -/
theorem inner_le_mul_negEnergySq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (g : S → ℝ) :
    C.inner g g ≤ (1 + a) * C.negEnergySq a g := by
  rcases eq_or_lt_of_le (C.inner_nonneg g) with h | h
  · rw [← h]
    have := C.negEnergySq_nonneg ha0 ha1 g
    nlinarith
  · have hcs := C.inner_sq_le_energy_mul_negEnergySq ha0 ha1 g g
    have hwin := (C.energy_window ha0 g).2
    have hneg := C.negEnergySq_nonneg ha0 ha1 g
    nlinarith


theorem energy_add (a : ℝ) (f g : S → ℝ) :
    C.energy a (f + g) = C.energy a f + 2 * C.energyBil a f g + C.energy a g := by
  have := C.energy_add_smul a 1 f g
  simpa using this

theorem killed_one (a : ℝ) : C.killed a (1 : S → ℝ) = (1 - a) • (1 : S → ℝ) := by
  funext x
  simp only [killed, step, Pi.one_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  rw [C.row_sum x, mul_one]

theorem inner_one_left (f : S → ℝ) : C.inner 1 f = ∑ x, C.stat x * f x := by
  simp only [inner, Pi.one_apply, one_mul]


end ReversibleChain

end GaloisForLFunctions.RHTower
