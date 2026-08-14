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

end ReversibleChain

end GaloisForLFunctions.RHTower
