import GaloisForLFunctions.HTGeometry.OrbitBalanceAugmentation
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Exact order of the augmentation cocycle of a finite transitive action

For a base point `a`, the difference `[g • a] - [a]` is a degree-zero permutation
cocycle. Its multiple by `m` is a coboundary in the augmentation kernel exactly when
`|X|` divides `m`. Indeed, a primitive would make `m[a] - b` invariant, hence constant;
its augmentation is therefore divisible by `|X|`. Constant functions also give the
converse. This is the integral obstruction behind the extension-to-cocycle mechanism.
-/

namespace GaloisForLFunctions.RepresentationLifting

open scoped BigOperators

variable (G X : Type*) [Group G] [MulAction G X]

/-- Permutation action on integer-valued coordinates. -/
def integerOrbitAction (g : G) : (X → ℤ) →ₗ[ℤ] (X → ℤ) where
  toFun v x := v (g⁻¹ • x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {G X}

@[simp]
theorem integerOrbitAction_apply (g : G) (v : X → ℤ) (x : X) :
    integerOrbitAction G X g v x = v (g⁻¹ • x) := rfl

/-- Identity and multiplication act by identity and composition of the coordinate maps. -/
theorem integerOrbitAction_one (v : X → ℤ) : integerOrbitAction G X 1 v = v := by
  funext x
  simp only [integerOrbitAction_apply, inv_one, one_smul]

theorem integerOrbitAction_mul (g h : G) (v : X → ℤ) :
    integerOrbitAction G X (g * h) v =
      integerOrbitAction G X g (integerOrbitAction G X h v) := by
  funext x
  simp only [integerOrbitAction_apply, mul_inv_rev, mul_smul]

/-- Point masses are transported to their translates. -/
theorem integerOrbitAction_single [DecidableEq X] (g : G) (a : X) :
    integerOrbitAction G X g (Pi.single a 1) = Pi.single (g • a) 1 := by
  funext x
  simp only [integerOrbitAction_apply, Pi.single_apply]
  by_cases h : x = g • a
  · rw [h, inv_smul_smul, if_pos rfl, if_pos rfl]
  · have hi : g⁻¹ • x ≠ a := by
      intro hi
      apply h
      rw [← hi, smul_inv_smul]
    rw [if_neg hi, if_neg h]

/-- The connecting cocycle of the augmentation sequence. -/
def integerOrbitCocycle [DecidableEq X] (a : X) (g : G) : X → ℤ :=
  Pi.single (g • a) 1 - Pi.single a 1

/-- The orbit difference satisfies the inhomogeneous one-cocycle equation. -/
theorem integerOrbitCocycle_mul [DecidableEq X] (a : X) (g h : G) :
    integerOrbitCocycle a (g * h) =
      integerOrbitAction G X g (integerOrbitCocycle a h) + integerOrbitCocycle a g := by
  rw [integerOrbitCocycle, integerOrbitCocycle, map_sub,
    integerOrbitAction_single, integerOrbitAction_single, integerOrbitCocycle, mul_smul]
  abel

variable [Fintype X] [DecidableEq X]

/-- The connecting cocycle takes values in the augmentation kernel. -/
theorem integerOrbitCocycle_sum (a : X) (g : G) :
    ∑ x, integerOrbitCocycle a g x = 0 := by
  simp [integerOrbitCocycle, Pi.single_apply, Finset.sum_sub_distrib]

omit [Fintype X] [DecidableEq X] in
/-- Every invariant integer-valued function on a transitive set is constant. -/
theorem integerOrbitAction_invariant_iff [MulAction.IsPretransitive G X]
    (a : X) (v : X → ℤ) :
    (∀ g : G, integerOrbitAction G X g v = v) ↔ ∀ x, v x = v a := by
  constructor
  · intro h x
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G a x
    have hg := congrFun (h g) (g • a)
    simpa only [integerOrbitAction_apply, inv_smul_smul] using hg.symm
  · intro h g
    funext x
    exact (h (g⁻¹ • x)).trans (h x).symm

/-- The exact integral order of the augmentation cocycle is the orbit cardinality. -/
theorem integerOrbitCocycle_multiple_is_coboundary_iff
    [MulAction.IsPretransitive G X] (a : X) (m : ℤ) :
    (∃ b : X → ℤ, (∑ x, b x) = 0 ∧ ∀ g : G,
      m • integerOrbitCocycle a g = integerOrbitAction G X g b - b) ↔
      (Fintype.card X : ℤ) ∣ m := by
  constructor
  · rintro ⟨b, hb, hc⟩
    let v : X → ℤ := m • Pi.single a 1 - b
    have hv : ∀ g : G, integerOrbitAction G X g v = v := by
      intro g
      change integerOrbitAction G X g (m • Pi.single a 1 - b) = m • Pi.single a 1 - b
      rw [map_sub, map_smul, integerOrbitAction_single]
      have h := hc g
      simp only [integerOrbitCocycle, smul_sub] at h
      linear_combination h
    have hconst := (integerOrbitAction_invariant_iff (G := G) a v).mp hv
    have hsum : (∑ x, v x) = m := by
      simp [v, Pi.single_apply, Finset.sum_sub_distrib, hb]
    refine ⟨v a, ?_⟩
    calc
      m = ∑ x, v x := hsum.symm
      _ = ∑ _x : X, v a := Finset.sum_congr rfl (fun x _ => hconst x)
      _ = (Fintype.card X : ℤ) * v a := by simp
  · rintro ⟨k, rfl⟩
    let m : ℤ := (Fintype.card X : ℤ) * k
    refine ⟨m • Pi.single a 1 - (fun _ => k), ?_, ?_⟩
    · simp [Pi.single_apply, Finset.sum_sub_distrib, m]
    · intro g
      rw [map_sub, map_smul, integerOrbitAction_single]
      have hconst : integerOrbitAction G X g (fun _ : X => k) = fun _ => k := rfl
      rw [hconst]
      simp only [integerOrbitCocycle, smul_sub]
      abel

/-- Finite coordinates identify the permutation lattice with finitely supported divisors. -/
noncomputable def integerOrbitDivisor (v : X → ℤ) : X →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm v

/-- The coordinate augmentation kernel is the existing divisor augmentation submodule. -/
theorem integerOrbitDivisor_mem_augmentation_iff (v : X → ℤ) :
    integerOrbitDivisor v ∈ augmentationSubmodule X ↔ ∑ x, v x = 0 := by
  rw [mem_augmentationSubmodule_iff_orbitDegree_zero, orbitDegree,
    Finsupp.sum_fintype _ _ (fun _ => rfl)]
  rfl

/-- Exact cocycle order expressed in the divisor augmentation submodule. -/
theorem augmentationDivisorCocycle_order [MulAction.IsPretransitive G X] (a : X) (m : ℤ) :
    (∃ b : X → ℤ, integerOrbitDivisor b ∈ augmentationSubmodule X ∧ ∀ g : G,
      m • integerOrbitCocycle a g = integerOrbitAction G X g b - b) ↔
      (Fintype.card X : ℤ) ∣ m := by
  simp only [integerOrbitDivisor_mem_augmentation_iff]
  exact integerOrbitCocycle_multiple_is_coboundary_iff a m

/-- The regular action has augmentation-cocycle order exactly the group order. -/
theorem regularAugmentationCocycle_order [Fintype G] [DecidableEq G] (m : ℤ) :
    (∃ b : G → ℤ, (∑ g, b g) = 0 ∧ ∀ g : G,
      m • integerOrbitCocycle (1 : G) g = integerOrbitAction G G g b - b) ↔
      (Fintype.card G : ℤ) ∣ m :=
  integerOrbitCocycle_multiple_is_coboundary_iff (G := G) (1 : G) m

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.integerOrbitCocycle_multiple_is_coboundary_iff
#print axioms GaloisForLFunctions.RepresentationLifting.regularAugmentationCocycle_order
#print axioms GaloisForLFunctions.RepresentationLifting.augmentationDivisorCocycle_order
#print axioms GaloisForLFunctions.RepresentationLifting.integerOrbitCocycle_mul
