import GaloisForLFunctions.RHTower.ReversibleKilledWalk
import GaloisForLFunctions.RHTower.DiscreteMarkovRenewal

/-!
# Discounted capacity of a first-entrance target

The discounted first-entrance mass of a target is the equilibrium potential of the killed
reversible chain: it is one on the target, harmonic for the killed operator off the target, and it
uniquely minimizes the killed Dirichlet energy among functions with that boundary value.

Its energy is the discounted capacity, its killed image is the equilibrium charge, and the
stationary mean of the potential is capacity divided by the killing rate.  The elementary capacity
window then pins the stationary first-entrance mass to the target volume within a fixed factor.
-/

open scoped ENNReal

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

namespace ReversibleChain

variable {S : Type*} [Fintype S] [DecidableEq S] (C : ReversibleChain S)

/-- The extended-nonnegative transition law of the chain. -/
noncomputable def ennKernel : S → S → ℝ≥0∞ := fun x y => ENNReal.ofReal (C.kernel x y)

theorem tsum_ennKernel (x : S) : (∑' y : S, C.ennKernel x y) = 1 := by
  simp only [ennKernel]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun y _ => C.kernel_nonneg x y),
    C.row_sum x, ENNReal.ofReal_one]

/-- The equilibrium potential of a target: its discounted first-entrance mass. -/
noncomputable def potential (a : ℝ) (A : Set S) (x : S) : ℝ :=
  (entranceMass C.ennKernel (ENNReal.ofReal a) A x A).toReal

theorem entranceMass_ne_top {a : ℝ} (ha1 : a ≤ 1) (A : Set S) (x : S) :
    entranceMass C.ennKernel (ENNReal.ofReal a) A x A ≠ ⊤ := by
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  refine entranceMass_le_one C.ennKernel C.tsum_ennKernel ?_ A x A
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal ha1

theorem potential_nonneg (a : ℝ) (A : Set S) (x : S) : 0 ≤ C.potential a A x :=
  ENNReal.toReal_nonneg

theorem potential_le_one {a : ℝ} (ha1 : a ≤ 1) (A : Set S) (x : S) :
    C.potential a A x ≤ 1 := by
  have hle : entranceMass C.ennKernel (ENNReal.ofReal a) A x A ≤ 1 := by
    refine entranceMass_le_one C.ennKernel C.tsum_ennKernel ?_ A x A
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ha1
  have h := ENNReal.toReal_le_toReal (C.entranceMass_ne_top ha1 A x) ENNReal.one_ne_top |>.mpr hle
  rw [potential]
  simpa using h

/-- The equilibrium potential is one on the target. -/
theorem potential_of_mem (a : ℝ) {A : Set S} {x : S} (hx : x ∈ A) : C.potential a A x = 1 := by
  rw [potential, entranceMass_of_mem C.ennKernel (ENNReal.ofReal a) A hx,
    Set.indicator_of_mem hx]
  simp

/-- The equilibrium potential takes one killed step off the target. -/
theorem potential_of_notMem {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Set S} {x : S}
    (hx : x ∉ A) : C.potential a A x = a * C.step (C.potential a A) x := by
  have hne : ∀ y : S, C.ennKernel x y * entranceMass C.ennKernel (ENNReal.ofReal a) A y A ≠ ⊤ := by
    intro y
    exact ENNReal.mul_ne_top (by simp [ennKernel]) (C.entranceMass_ne_top ha1 A y)
  rw [potential, entranceMass_of_notMem C.ennKernel (ENNReal.ofReal a) A hx, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ha0, tsum_fintype, ENNReal.toReal_sum (fun y _ => hne y)]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [ENNReal.toReal_mul, ennKernel, ENNReal.toReal_ofReal (C.kernel_nonneg x y), potential]

/-- **Bellman--Dirichlet equation.**  The equilibrium potential is killed-harmonic off the
target. -/
theorem killed_potential_of_notMem {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Set S} {x : S}
    (hx : x ∉ A) : C.killed a (C.potential a A) x = 0 := by
  rw [killed, ← C.potential_of_notMem ha0 ha1 hx, sub_self]

/-- **Uniqueness of the equilibrium potential.**  A function vanishing on the target and
killed-harmonic off it is zero. -/
theorem eq_zero_of_boundary_of_killed_harmonic {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {A : Set S}
    {u : S → ℝ} (hbnd : ∀ x ∈ A, u x = 0) (hharm : ∀ x, x ∉ A → C.killed a u x = 0) : u = 0 := by
  refine C.energy_eq_zero ha0 ha1 ?_
  rw [energy, energyBil, inner]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x ∈ A
  · rw [hbnd x hx]
    ring
  · rw [hharm x hx]
    ring

theorem energyBil_potential_eq_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Set S} {g : S → ℝ}
    (hg : ∀ x ∈ A, g x = 0) : C.energyBil a (C.potential a A) g = 0 := by
  rw [energyBil_symm, energyBil, inner]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x ∈ A
  · rw [hg x hx]
    ring
  · rw [C.killed_potential_of_notMem ha0 ha1 hx]
    ring

/-- **Dirichlet principle.**  The equilibrium potential minimizes the killed energy among all
functions equal to one on the target. -/
theorem energy_potential_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Set S} {f : S → ℝ}
    (hf : ∀ x ∈ A, f x = 1) :
    C.energy a (C.potential a A) ≤ C.energy a f := by
  have hdecomp : f = C.potential a A + (f - C.potential a A) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hg : ∀ x ∈ A, (f - C.potential a A) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply, hf x hx, C.potential_of_mem a hx, sub_self]
  have hbil := C.energyBil_potential_eq_zero ha0 ha1 hg
  have hexp := C.energy_add a (C.potential a A) (f - C.potential a A)
  rw [← hdecomp, hbil] at hexp
  have hnn := C.energy_nonneg ha0 ha1 (f - C.potential a A)
  linarith

/-- **Uniqueness of the minimizer.** -/
theorem eq_potential_of_energy_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {A : Set S} {f : S → ℝ}
    (hf : ∀ x ∈ A, f x = 1) (heq : C.energy a f = C.energy a (C.potential a A)) :
    f = C.potential a A := by
  have hdecomp : f = C.potential a A + (f - C.potential a A) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hg : ∀ x ∈ A, (f - C.potential a A) x = 0 := by
    intro x hx
    simp only [Pi.sub_apply, hf x hx, C.potential_of_mem a hx, sub_self]
  have hbil := C.energyBil_potential_eq_zero ha0 ha1.le hg
  have hexp := C.energy_add a (C.potential a A) (f - C.potential a A)
  rw [← hdecomp, hbil] at hexp
  have hzero : C.energy a (f - C.potential a A) = 0 := by linarith
  have := C.energy_eq_zero ha0 ha1 hzero
  funext x
  have hx := congrFun this x
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hx
  exact hx

/-- The discounted capacity of a target. -/
noncomputable def capacity (a : ℝ) (A : Set S) : ℝ := C.energy a (C.potential a A)

/-- The equilibrium charge of a target. -/
noncomputable def charge (a : ℝ) (A : Set S) : S → ℝ := C.killed a (C.potential a A)

theorem charge_of_notMem {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Set S} {x : S} (hx : x ∉ A) :
    C.charge a A x = 0 := C.killed_potential_of_notMem ha0 ha1 hx

theorem step_potential_le_one {a : ℝ} (ha1 : a ≤ 1) (A : Set S) (x : S) :
    C.step (C.potential a A) x ≤ 1 := by
  rw [step]
  calc ∑ y, C.kernel x y * C.potential a A y ≤ ∑ y, C.kernel x y * 1 := by
        refine Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_left (C.potential_le_one ha1 A y) (C.kernel_nonneg x y)
    _ = 1 := by simp [C.row_sum x]

/-- The equilibrium charge is bounded below by the killing rate on the target. -/
theorem charge_ge_of_mem {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {A : Set S} {x : S} (hx : x ∈ A) :
    1 - a ≤ C.charge a A x := by
  rw [charge, killed, C.potential_of_mem a hx]
  have := C.step_potential_le_one ha1 A x
  nlinarith

/-- **Charge support and stationary mean.**  The capacity is the stationary mass of the charge and
the killed stationary mean of the potential. -/
theorem capacity_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (A : Set S) :
    C.capacity a A = ∑ x, C.stat x * C.charge a A x ∧
      C.capacity a A = (1 - a) * ∑ x, C.stat x * C.potential a A x := by
  have hfirst : C.capacity a A = ∑ x, C.stat x * C.charge a A x := by
    rw [capacity, energy, energyBil, inner]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x ∈ A
    · rw [C.potential_of_mem a hx, charge, one_mul]
    · rw [C.charge_of_notMem ha0 ha1 hx, C.killed_potential_of_notMem ha0 ha1 hx]
      ring
  refine ⟨hfirst, ?_⟩
  have hsecond : (∑ x, C.stat x * C.charge a A x) =
      (1 - a) * ∑ x, C.stat x * C.potential a A x := by
    have h1 : (∑ x, C.stat x * C.charge a A x) = C.inner 1 (C.killed a (C.potential a A)) := by
      rw [inner_one_left]
      rfl
    rw [h1, C.inner_killed_symm, C.killed_one, C.inner_smul_left, C.inner_one_left]
  rw [hfirst, hsecond]

end ReversibleChain

end GaloisForLFunctions.RHTower
