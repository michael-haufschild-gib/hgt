import GaloisForLFunctions.HTGeometry.MilnorKTameSymbol

/-!
# A discrete valuation with a chosen uniformizer

The tame symbol in degree two needs only the valuation and its residue map.  A residue map in every
degree needs one more datum: a uniformizer, which splits each unit as a power of itself times a unit
of valuation zero.  The residue of that unit part is multiplicative, is trivial on the uniformizer,
and agrees with the residue map on units of valuation zero — the three facts Milnor's construction
of the residue uses.

* `ResidueData` : **a discrete valuation with a uniformizer, whose residue map is additive on
  `1 - a`.**
* `unitPart`, `residueUnit` : **the unit part of a unit and its residue.**
* `residueUnit_mul`, `residueUnit_unif`, `residueUnit_of_mem_ker` : their basic laws.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A discrete valuation on a field, its residue homomorphism, and a chosen uniformizer.** -/
structure ResidueData (K : Type*) [Field K] (k : Type*) [Field k] extends TameData K k where
  /-- the chosen uniformizer -/
  unif : Kˣ
  /-- the uniformizer has valuation one -/
  v_unif : Multiplicative.toAdd (val unif) = 1
  /-- the residue map is additive where it is defined: for a unit of valuation zero whose
  complement also has valuation zero, the residue of `1 - a` is `1` minus the residue of `a` -/
  oneSub_res : ∀ {a : Kˣ} (ha : (a : K) ≠ 1) (h : a ∈ val.ker) (h' : oneSubUnit ha ∈ val.ker),
    ((res ⟨oneSubUnit ha, h'⟩ : kˣ) : k) = 1 - ((res ⟨a, h⟩ : kˣ) : k)

namespace ResidueData

variable {K : Type*} [Field K] {k : Type*} [Field k] (D : ResidueData K k)

/-- The valuation of a unit. -/
def val' (a : Kˣ) : ℤ := D.toTameData.v a

theorem val'_mul (a b : Kˣ) : D.val' (a * b) = D.val' a + D.val' b :=
  D.toTameData.v_mul a b

theorem val'_unif : D.val' D.unif = 1 := D.v_unif

theorem val'_eq_zero_iff {a : Kˣ} : D.val' a = 0 ↔ a ∈ D.val.ker :=
  ⟨fun h => D.toTameData.mem_ker_iff.2 h, fun h => D.toTameData.mem_ker_iff.1 h⟩

/-- **The unit part of a unit**: the unit divided by the uniformizer to the power of its
valuation. -/
def unitPart (a : Kˣ) : Kˣ := a * D.unif ^ (-D.val' a)

theorem unitPart_mem (a : Kˣ) : D.unitPart a ∈ D.val.ker := by
  refine D.toTameData.mem_ker_iff.2 ?_
  show D.toTameData.v (a * D.unif ^ (-D.val' a)) = 0
  rw [D.toTameData.v_mul, D.toTameData.v_zpow]
  show D.val' a + (-D.val' a) * D.val' D.unif = 0
  rw [val'_unif]
  ring

theorem unitPart_mul (a b : Kˣ) : D.unitPart (a * b) = D.unitPart a * D.unitPart b := by
  show (a * b) * D.unif ^ (-D.val' (a * b)) = (a * D.unif ^ (-D.val' a)) * (b * D.unif ^ (-D.val' b))
  rw [val'_mul, neg_add, zpow_add]
  simp only [mul_assoc, mul_left_comm]

theorem unitPart_of_mem_ker {a : Kˣ} (h : a ∈ D.val.ker) : D.unitPart a = a := by
  show a * D.unif ^ (-D.val' a) = a
  rw [show D.val' a = 0 from D.val'_eq_zero_iff.2 h]
  simp

theorem unitPart_unif : D.unitPart D.unif = 1 := by
  show D.unif * D.unif ^ (-D.val' D.unif) = 1
  rw [val'_unif]
  rw [show ((-1 : ℤ)) = -1 from rfl, zpow_neg, zpow_one, mul_inv_cancel]

/-- **The residue of the unit part of a unit.** -/
def residueUnit (a : Kˣ) : kˣ := D.res ⟨D.unitPart a, D.unitPart_mem a⟩

theorem residueUnit_mul (a b : Kˣ) :
    D.residueUnit (a * b) = D.residueUnit a * D.residueUnit b := by
  show D.res ⟨D.unitPart (a * b), _⟩ = D.res ⟨D.unitPart a, _⟩ * D.res ⟨D.unitPart b, _⟩
  rw [← map_mul]
  exact congrArg D.res (Subtype.ext (D.unitPart_mul a b))

theorem residueUnit_unif : D.residueUnit D.unif = 1 := by
  show D.res ⟨D.unitPart D.unif, _⟩ = 1
  rw [← map_one D.res]
  exact congrArg D.res (Subtype.ext D.unitPart_unif)

theorem residueUnit_of_mem_ker {a : Kˣ} (h : a ∈ D.val.ker) :
    D.residueUnit a = D.res ⟨a, h⟩ :=
  congrArg D.res (Subtype.ext (D.unitPart_of_mem_ker h))

theorem residueUnit_one : D.residueUnit (1 : Kˣ) = 1 := by
  rw [residueUnit_of_mem_ker D (one_mem _), ← map_one D.res]
  exact congrArg D.res (Subtype.ext rfl)

end ResidueData

end GaloisForLFunctions.HTGeometry
