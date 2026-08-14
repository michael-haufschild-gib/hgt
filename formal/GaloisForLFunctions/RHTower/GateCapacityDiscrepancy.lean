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

/-- The stationary mass of a target. -/
noncomputable def statMeasure (A : Set S) : ℝ := ∑ x, Set.indicator A C.stat x

theorem statMeasure_nonneg (A : Set S) : 0 ≤ C.statMeasure A := by
  classical
  refine Finset.sum_nonneg fun x _ => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx]
    exact (C.stat_pos x).le
  · rw [Set.indicator_of_notMem hx]

theorem inner_indicator_nonneg (A : Set S) :
    0 ≤ C.inner (Set.indicator A 1) (C.step (Set.indicator A 1)) := by
  classical
  have hnn : ∀ x : S, 0 ≤ Set.indicator A (1 : S → ℝ) x := by
    intro x
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      norm_num
    · rw [Set.indicator_of_notMem hx]
  refine Finset.sum_nonneg fun x _ => ?_
  refine mul_nonneg (C.stat_pos x).le (mul_nonneg (hnn x) ?_)
  exact Finset.sum_nonneg fun y _ => mul_nonneg (C.kernel_nonneg x y) (hnn y)

theorem inner_indicator_self (A : Set S) :
    C.inner (Set.indicator A 1) (Set.indicator A 1) = C.statMeasure A := by
  classical
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- **Sharp elementary capacity window.** -/
theorem capacity_window {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (A : Set S) :
    (1 - a) * C.statMeasure A ≤ C.capacity a A ∧
      C.capacity a A ≤ C.statMeasure A ∧ C.capacity a A ≤ 1 - a := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rw [(C.capacity_eq ha0 ha1 A).2]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by linarith : (0:ℝ) ≤ 1 - a)
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx, C.potential_of_mem a hx, mul_one]
    · rw [Set.indicator_of_notMem hx]
      exact mul_nonneg (C.stat_pos x).le (C.potential_nonneg a A x)
  · have hle := C.energy_potential_le ha0 ha1
      (f := Set.indicator A (1 : S → ℝ)) (fun x hx => by rw [Set.indicator_of_mem hx]; rfl)
    refine le_trans hle (le_of_le_of_eq ?_ (C.inner_indicator_self A))
    rw [energy, energyBil, inner_killed_expand]
    have := mul_nonneg ha0 (C.inner_indicator_nonneg A)
    linarith
  · have hle := C.energy_potential_le ha0 ha1 (A := A) (f := (1 : S → ℝ)) (fun x _ => rfl)
    refine le_trans hle (le_of_eq ?_)
    rw [energy, energyBil, C.killed_one, C.inner_smul_right, C.inner_one_left]
    simp [C.stat_sum]

/-- **Stationary first-entrance mean.**  The stationary mean of the equilibrium potential is the
capacity divided by the killing rate. -/
theorem stationary_mean {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (A : Set S) :
    ∑ x, C.stat x * C.potential a A x = C.capacity a A / (1 - a) := by
  have h := (C.capacity_eq ha0 ha1.le A).2
  have hpos : (0:ℝ) < 1 - a := by linarith
  rw [h, mul_comm, mul_div_assoc, div_self hpos.ne', mul_one]

/-- The stationary first-entrance mass differs from the target volume by at most the killing
factor. -/
theorem statMeasure_le_stationary_mean {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (A : Set S) :
    C.statMeasure A ≤ ∑ x, C.stat x * C.potential a A x ∧
      ∑ x, C.stat x * C.potential a A x ≤ C.statMeasure A / (1 - a) := by
  have hwin := C.capacity_window ha0 ha1.le A
  have hmean := C.stationary_mean ha0 ha1 A
  have hpos : (0:ℝ) < 1 - a := by linarith
  constructor
  · rw [hmean, le_div_iff₀ hpos]
    have := hwin.1
    linarith
  · rw [hmean, div_le_div_iff_of_pos_right hpos]
    exact hwin.2.1

/-- The density of a law against the stationary law. -/
noncomputable def density (ν : S → ℝ) : S → ℝ := fun x => ν x / C.stat x

theorem stat_mul_density (ν : S → ℝ) (x : S) : C.stat x * C.density ν x = ν x := by
  rw [density, mul_div_cancel₀ _ (C.stat_pos x).ne']

/-- The directional capacity discrepancy of a law. -/
noncomputable def discrepancy (a : ℝ) (A : Set S) (ν : S → ℝ) : ℝ :=
  C.inner (C.density ν - 1) (C.potential a A)

/-- The chi-square divergence of a law against the stationary law. -/
noncomputable def chiSq (ν : S → ℝ) : ℝ := C.inner (C.density ν - 1) (C.density ν - 1)

/-- The killed negative-energy square of a law against the stationary law. -/
noncomputable def dualNormSq (a : ℝ) (ν : S → ℝ) : ℝ := C.negEnergySq a (C.density ν - 1)

/-- **Capacity--discrepancy law.**  The mean first-entrance mass of a law is the stationary mean
plus its directional capacity discrepancy. -/
theorem mean_potential_eq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (A : Set S) (ν : S → ℝ) :
    ∑ x, ν x * C.potential a A x =
      C.capacity a A / (1 - a) + C.discrepancy a A ν := by
  have hterm : ∀ x : S, C.stat x * ((C.density ν - 1) x * C.potential a A x) =
      ν x * C.potential a A x - C.stat x * C.potential a A x := by
    intro x
    simp only [Pi.sub_apply, Pi.one_apply]
    have h := C.stat_mul_density ν x
    linear_combination (C.potential a A x) * h
  rw [discrepancy, inner, Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_sub_distrib,
    ← C.stationary_mean ha0 ha1 A]
  ring

/-- **Directional discrepancy bound.**  The directional discrepancy is controlled by capacity and
the killed negative-energy square. -/
theorem abs_discrepancy_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (A : Set S) (ν : S → ℝ) :
    |C.discrepancy a A ν| ≤ Real.sqrt (C.capacity a A) * Real.sqrt (C.dualNormSq a ν) := by
  have hcs := C.inner_sq_le_energy_mul_negEnergySq ha0 ha1 (C.density ν - 1) (C.potential a A)
  have hsq : (C.discrepancy a A ν) ^ 2 ≤ C.capacity a A * C.dualNormSq a ν := by
    rw [discrepancy, capacity, dualNormSq, mul_comm]
    exact hcs
  have hnn : 0 ≤ C.capacity a A * C.dualNormSq a ν :=
    le_trans (sq_nonneg _) hsq
  have hcap : (0:ℝ) ≤ C.capacity a A := C.energy_nonneg ha0 ha1.le _
  have hle := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_mul hcap] at hle

/-- **Global discrepancy obstruction.**  The killed negative-energy square dominates the
chi-square divergence up to the killed spectral radius. -/
theorem chiSq_le_dualNormSq {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (ν : S → ℝ) :
    C.chiSq ν ≤ (1 + a) * C.dualNormSq a ν :=
  C.inner_le_mul_negEnergySq ha0 ha1 _

theorem chiSq_eq {ν : S → ℝ} (hν : ∑ x, ν x = 1) :
    C.chiSq ν = (∑ x, C.stat x * C.density ν x ^ 2) - 1 := by
  have hterm : ∀ x : S, C.stat x * ((C.density ν - 1) x * (C.density ν - 1) x) =
      C.stat x * C.density ν x ^ 2 - 2 * ν x + C.stat x := by
    intro x
    simp only [Pi.sub_apply, Pi.one_apply]
    have h := C.stat_mul_density ν x
    linear_combination (-2 : ℝ) * h
  rw [chiSq, inner, Finset.sum_congr rfl fun x _ => hterm x]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hν, C.stat_sum]
  ring

/-- **Support obstruction.**  A law supported on a small target has large chi-square
divergence. -/
theorem chiSq_ge_of_support {ν : S → ℝ} (hν : ∑ x, ν x = 1) {B : Set S}
    (hsupp : ∀ x, x ∉ B → ν x = 0) :
    (C.statMeasure B)⁻¹ - 1 ≤ C.chiSq ν := by
  classical
  have hf : ∀ x : S, Real.sqrt (C.stat x) ^ 2 = C.stat x :=
    fun x => Real.sq_sqrt (C.stat_pos x).le
  have hpair : ∀ x : S, Set.indicator B (fun x => Real.sqrt (C.stat x)) x *
      (Set.indicator B (fun x => Real.sqrt (C.stat x) * C.density ν x) x) = ν x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have : Real.sqrt (C.stat x) * (Real.sqrt (C.stat x) * C.density ν x) =
          C.stat x * C.density ν x := by
        rw [← mul_assoc, ← pow_two, hf x]
      rw [this, C.stat_mul_density]
    · rw [Set.indicator_of_notMem hx, zero_mul, hsupp x hx]
  have hsq1 : ∀ x : S, Set.indicator B (fun x => Real.sqrt (C.stat x)) x ^ 2 =
      Set.indicator B C.stat x := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hf x]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      norm_num
  have hsq2 : ∀ x : S, Set.indicator B (fun x => Real.sqrt (C.stat x) * C.density ν x) x ^ 2 ≤
      C.stat x * C.density ν x ^ 2 := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, mul_pow, hf x]
    · rw [Set.indicator_of_notMem hx]
      have := mul_nonneg (C.stat_pos x).le (sq_nonneg (C.density ν x))
      simpa using this
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun x => Set.indicator B (fun x => Real.sqrt (C.stat x)) x)
    (fun x => Set.indicator B (fun x => Real.sqrt (C.stat x) * C.density ν x) x)
  rw [Finset.sum_congr rfl fun x _ => hpair x, hν,
    Finset.sum_congr rfl fun x _ => hsq1 x] at hcs
  have hle : ∑ x, Set.indicator B (fun x => Real.sqrt (C.stat x) * C.density ν x) x ^ 2 ≤
      ∑ x, C.stat x * C.density ν x ^ 2 := Finset.sum_le_sum fun x _ => hsq2 x
  have hmain : 1 ≤ C.statMeasure B * ∑ x, C.stat x * C.density ν x ^ 2 := by
    refine le_trans (le_of_eq (by norm_num)) (le_trans hcs ?_)
    exact mul_le_mul_of_nonneg_left hle (C.statMeasure_nonneg B)
  have hβ : 0 < C.statMeasure B := by
    rcases lt_or_eq_of_le (C.statMeasure_nonneg B) with h | h
    · exact h
    · exfalso
      rw [← h, zero_mul] at hmain
      linarith
  have hfinal : (C.statMeasure B)⁻¹ ≤ ∑ x, C.stat x * C.density ν x ^ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hβ, mul_comm]
    exact hmain
  rw [C.chiSq_eq hν]
  linarith

/-- The perturbation of the stationary law in a fixed direction. -/
noncomputable def perturbedLaw (g : S → ℝ) (η : ℝ) : S → ℝ := fun x => C.stat x * (1 + η * g x)

theorem sum_perturbedLaw {g : S → ℝ} (hg : ∑ x, C.stat x * g x = 0) (η : ℝ) :
    ∑ x, C.perturbedLaw g η x = 1 := by
  have hterm : ∀ x : S, C.perturbedLaw g η x = C.stat x + η * (C.stat x * g x) := by
    intro x
    rw [perturbedLaw]
    ring
  rw [Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_add_distrib, ← Finset.mul_sum, hg,
    C.stat_sum, mul_zero, add_zero]

theorem perturbedLaw_nonneg {g : S → ℝ} {η : ℝ} (hη : ∀ x, 0 ≤ 1 + η * g x) (x : S) :
    0 ≤ C.perturbedLaw g η x :=
  mul_nonneg (C.stat_pos x).le (hη x)

/-- Every direction admits a positive perturbation scale keeping the law nonnegative. -/
theorem exists_perturbation_nonneg (g : S → ℝ) : ∃ η : ℝ, 0 < η ∧ ∀ x, 0 ≤ 1 + η * g x := by
  classical
  set T : ℝ := ∑ y, |g y| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun y _ => abs_nonneg _
  have hpos : (0 : ℝ) < 1 + T := by linarith
  refine ⟨1 / (1 + T), by positivity, fun x => ?_⟩
  have hbound : |g x| ≤ T :=
    Finset.single_le_sum (f := fun y => |g y|) (fun y _ => abs_nonneg _) (Finset.mem_univ x)
  have hge : -T ≤ g x := by
    have := neg_abs_le (g x)
    linarith
  have hrw : 1 + (1 / (1 + T)) * g x = ((1 + T) + g x) / (1 + T) := by
    field_simp
  rw [hrw]
  exact div_nonneg (by linarith) hpos.le

theorem density_perturbedLaw (g : S → ℝ) (η : ℝ) (x : S) :
    C.density (C.perturbedLaw g η) x = 1 + η * g x := by
  rw [density, perturbedLaw, mul_comm, mul_div_assoc, div_self (C.stat_pos x).ne', mul_one]

/-- **Directional matching without Haar convergence.**  A law perturbed in a direction orthogonal
to the equilibrium potential has vanishing directional capacity discrepancy. -/
theorem discrepancy_perturbedLaw {a : ℝ} (A : Set S) {g : S → ℝ} (η : ℝ)
    (hgh : C.inner g (C.potential a A) = 0) :
    C.discrepancy a A (C.perturbedLaw g η) = 0 := by
  have hdir : C.density (C.perturbedLaw g η) - 1 = η • g := by
    funext x
    simp only [Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul,
      C.density_perturbedLaw g η x]
    ring
  rw [discrepancy, hdir, C.inner_smul_left, hgh, mul_zero]

theorem perturbedLaw_ne_stat {g : S → ℝ} {η : ℝ} (hg : g ≠ 0) (hη : η ≠ 0) :
    C.perturbedLaw g η ≠ C.stat := by
  intro hc
  refine hg (funext fun x => ?_)
  have hx := congrFun hc x
  rw [perturbedLaw] at hx
  have hstat := (C.stat_pos x).ne'
  have : C.stat x * (η * g x) = 0 := by nlinarith [hx]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hstat
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hη
    · simpa using h'

/-- **Support form of the global obstruction.**  A law supported on a small target has a large
killed negative-energy square. -/
theorem dualNormSq_ge_of_support {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {ν : S → ℝ}
    (hν : ∑ x, ν x = 1) {B : Set S} (hsupp : ∀ x, x ∉ B → ν x = 0) :
    ((C.statMeasure B)⁻¹ - 1) / (1 + a) ≤ C.dualNormSq a ν := by
  have h1 := C.chiSq_ge_of_support hν hsupp
  have h2 := C.chiSq_le_dualNormSq ha0 ha1 ν
  have hpos : (0:ℝ) < 1 + a := by linarith
  rw [div_le_iff₀ hpos]
  calc (C.statMeasure B)⁻¹ - 1 ≤ C.chiSq ν := h1
    _ ≤ (1 + a) * C.dualNormSq a ν := h2
    _ = C.dualNormSq a ν * (1 + a) := by ring

end ReversibleChain

end GaloisForLFunctions.RHTower
