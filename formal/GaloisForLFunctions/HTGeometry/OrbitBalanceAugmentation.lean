import GaloisForLFunctions.HTGeometry.OrbitBalance
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The augmentation ideal on an orbit equals the augmentation kernel

On a single translation orbit, a finite integer divisor is modeled by `α →₀ ℤ`, its total exponent
is the orbit degree (augmentation map), and the constant-coefficient structural-translation
annihilator modulo differentially algebraic functions is the augmentation ideal — the span of all
balanced point-mass differences `[a] - [b]`.  The algebraic heart of that statement is the
biconditional proved here:

> a divisor lies in the augmentation ideal **iff** its total exponent (orbit degree) is zero.

This is the exact "differentially algebraic iff total exponent zero" content of the double-sine and
Barnes multiple-gamma translation-annihilator theorems, stripped of the analytic
hypertranscendence input.
-/

namespace GaloisForLFunctions

open scoped BigOperators

variable {α : Type*}

/-- The orbit degree is the value of the `linearCombination` against the all-ones vector, hence an
`ℤ`-linear map. -/
theorem orbitDegree_eq_linearCombination (D : α →₀ ℤ) :
    orbitDegree D = Finsupp.linearCombination ℤ (fun _ => (1 : ℤ)) D := by
  simp [orbitDegree, Finsupp.linearCombination_apply, Finsupp.sum]

/-- The orbit degree is homogeneous of degree one: `deg (c • D) = c · deg D`. -/
theorem orbitDegree_smul (c : ℤ) (D : α →₀ ℤ) :
    orbitDegree (c • D) = c * orbitDegree D := by
  rw [orbitDegree_eq_linearCombination, orbitDegree_eq_linearCombination, map_smul, smul_eq_mul]

variable (α) in
/-- The augmentation ideal on an orbit: the `ℤ`-span of all balanced point-mass differences
`[a] - [b]`.  Realized on divisors, this is the augmentation ideal of the orbit group ring. -/
noncomputable def augmentationSubmodule [DecidableEq α] : Submodule ℤ (α →₀ ℤ) :=
  Submodule.span ℤ (Set.range fun p : α × α => Finsupp.single p.1 1 - Finsupp.single p.2 1)

/-- **Augmentation ideal = augmentation kernel.**  A finite integer divisor lies in the
augmentation ideal (is a `ℤ`-combination of balanced point-mass differences) iff its total exponent
— the orbit degree — vanishes. -/
theorem mem_augmentationSubmodule_iff_orbitDegree_zero [DecidableEq α] (D : α →₀ ℤ) :
    D ∈ augmentationSubmodule α ↔ orbitDegree D = 0 := by
  constructor
  · intro hD
    induction hD using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        rw [orbitDegree_sub, orbitDegree_single, orbitDegree_single, sub_self]
    | zero => exact orbitDegree_zero
    | add x y _ _ ihx ihy => rw [orbitDegree_add, ihx, ihy, add_zero]
    | smul c x _ ih => rw [orbitDegree_smul, ih, mul_zero]
  · intro hD
    rcases eq_or_ne D 0 with rfl | hne
    · exact zero_mem _
    · obtain ⟨base, _⟩ := Finsupp.support_nonempty_iff.mpr hne
      rw [eq_sum_single_sub_base_of_orbitDegree_zero base D hD]
      refine Submodule.sum_mem _ fun a _ => ?_
      have hsplit : Finsupp.single a (D a) - Finsupp.single base (D a)
          = (D a) • (Finsupp.single a (1 : ℤ) - Finsupp.single base 1) := by
        simp [smul_sub, Finsupp.smul_single]
      rw [hsplit]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, base), rfl⟩)

end GaloisForLFunctions
