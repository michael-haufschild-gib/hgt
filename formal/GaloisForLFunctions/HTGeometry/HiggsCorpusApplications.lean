import GaloisForLFunctions.HTGeometry.AbelianHiggsMechanism
import GaloisForLFunctions.HTGeometry.ConstitutiveEntropicAlternatingFormation
import GaloisForLFunctions.HTGeometry.ConstitutiveMarkedSymmetryQuotient
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.PortCapacity
import GaloisForLFunctions.HTGeometry.NonabelianHiggsMechanism

/-!
# Higgs mechanisms already latent in the reusable corpus

This module instantiates the Higgs interface or discharges all local premises for three existing
symmetry-selection systems.

* A marked real axis breaks `U(1)` to its half-turn subgroup `{ ±1 }`.
* A radial relation with zero weight leaves the whole radial group unbroken, while one nonzero
  weight leaves only the identity.
* Positive bipartite formation has one exact counter-shift gauge mode.  Its quadratic formation
  energy has precisely that mode as radical, giving a finite mass-form interpretation with no
  hidden massless direction.
-/

open Matrix Pointwise
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Marked-axis `U(1) → ℤ/2` breaking -/

/-- Canonical orbit-well mechanism for the corpus's marked real axis. -/
def markedAxisHiggsMechanism : HiggsMechanism Circle (Set ℂ) :=
  HiggsMechanism.canonicalOrbitWell markedAxis

/-- Unbroken marked-axis symmetry is exactly the half-turn subgroup. -/
theorem markedAxisHiggs_unbroken_eq_halfTurn :
    markedAxisHiggsMechanism.unbroken = halfTurnSubgroup :=
  stabilizer_markedAxis

/-- Quarter-turn witness used to prove marked-axis breaking is proper. -/
def circleQuarterTurn : Circle :=
  ⟨Complex.I, mem_sphere_zero_iff_norm.mpr Complex.norm_I⟩

/-- Half-turn residual group is nontrivial. -/
theorem halfTurnSubgroup_ne_bot : halfTurnSubgroup ≠ ⊥ := by
  intro hbot
  have hmem : (-1 : Circle) ∈ halfTurnSubgroup :=
    (mem_halfTurnSubgroup_iff (-1)).mpr (Or.inr rfl)
  rw [hbot] at hmem
  have hneg : (-1 : Circle) = 1 := by
    change (-1 : Circle) = 1 at hmem
    exact hmem
  have hcoe := congrArg (fun z : Circle => (z : ℂ)) hneg
  norm_num at hcoe

/-- Half-turn residual group is proper: quarter-turn is broken. -/
theorem halfTurnSubgroup_ne_top : halfTurnSubgroup ≠ ⊤ := by
  intro htop
  have hmem : circleQuarterTurn ∈ halfTurnSubgroup := by
    rw [htop]
    trivial
  rcases (mem_halfTurnSubgroup_iff circleQuarterTurn).mp hmem with h | h
  · have hcoe := congrArg (fun z : Circle => (z : ℂ)) h
    have him := congrArg Complex.im hcoe
    norm_num [circleQuarterTurn] at him
  · have hcoe := congrArg (fun z : Circle => (z : ℂ)) h
    have him := congrArg Complex.im hcoe
    norm_num [circleQuarterTurn] at him

/-- Marked-axis mechanism partially breaks `U(1)` to `{ ±1 }`. -/
theorem markedAxisHiggs_partiallyBroken :
    markedAxisHiggsMechanism.IsPartiallyBroken := by
  change markedAxisHiggsMechanism.unbroken ≠ ⊥ ∧ markedAxisHiggsMechanism.unbroken ≠ ⊤
  rw [markedAxisHiggs_unbroken_eq_halfTurn]
  exact ⟨halfTurnSubgroup_ne_bot, halfTurnSubgroup_ne_top⟩

/-! ## Radial Abelian breaking -/

/-- One nonzero radial weight completely breaks radial symmetry to identity parameter. -/
theorem radialHiggs_nonzeroWeight_stabilizer :
    {c : ℝ | ∀ _i : Fin 1, Real.exp (c * 1) - 1 = 0} = {0} := by
  have hne : (fun _i : Fin 1 => (1 : ℝ)) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    norm_num at h0
  have h := HTGeometry.ConstraintRelativity.radial_stabilizer
    (fun _i : Fin 1 => (1 : ℝ))
  rw [if_neg hne] at h
  simpa using h

/-- Zero radial weight leaves full radial symmetry unbroken. -/
theorem radialHiggs_zeroWeight_unbroken :
    {c : ℝ | ∀ _i : Fin 1, Real.exp (c * 0) - 1 = 0} = Set.univ := by
  ext c
  simp

/-! ## Bipartite formation mass form -/

/-- Strictly positive singleton formation has only global counter-shift stabilizer. -/
theorem bipartiteSingletonHiggs_stabilizer (x y : Unit → ℝ) :
    bipartitePotentialForm (fun _ _ : Unit => 1) x y = (fun _ _ => 1) ↔
      ∃ c : ℝ, (∀ i, x i = c) ∧ (∀ j, y j = -c) := by
  apply bipartitePotentialForm_eq_self_iff_gauge
  intro i j
  norm_num

/-- Finite bipartite formation energy has exactly one massless global gauge mode. -/
theorem bipartiteFiniteHiggs_massless_iff_gauge
    (x : Fin 2 → ℝ) (y : Fin 3 → ℝ) :
    bipartiteFormationEnergy (fun _ _ => 1) x y = 0 ↔
      ∃ c : ℝ, (∀ i, x i = c) ∧ (∀ j, y j = -c) := by
  apply bipartiteFormationEnergy_eq_zero_iff_gauge
  intro i j
  norm_num

/-- Finite bipartite mass form is invariant under global counter-shift gauge. -/
theorem bipartiteFiniteHiggs_energy_gaugeInvariant
    (x : Fin 2 → ℝ) (y : Fin 3 → ℝ) (c : ℝ) :
    bipartiteFormationEnergy (fun _ _ => 1) (fun i => x i + c) (fun j => y j - c) =
      bipartiteFormationEnergy (fun _ _ => 1) x y :=
  bipartiteFormationEnergy_gauge (fun _ _ => 1) x y c

end GaloisForLFunctions.HTGeometry
