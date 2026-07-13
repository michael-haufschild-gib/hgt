import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Untwisted cyclic Tate descent is orbit-type blind

For the trivial integral lattice at a fixed point of a cyclic group of order `q`, the norm is
`n ↦ qn` and the degree-zero Tate charge is reduction modulo `q`.  For the regular `q`-point
permutation lattice, every invariant vector is constant and every constant vector is a norm.

Thus ordinary degree-zero Tate descent removes a full regular packet and retains a fixed-point
residue, but the distinction is exactly stabilizer/orbit type.  Assigning it to scalar zeta zeros
would presuppose the fixed-versus-free conclusion it is meant to prove.  A live arbitrary-modulus
route needs twisted, projective, or arithmetic gluing data beyond the untwisted regular lattice.

These statements are standard integral representation theory and are not claimed as new scientific
knowledge.
-/

open scoped BigOperators

namespace RHTower

/-- Norm on a trivial integral lattice for a cyclic stabilizer of order `q`. -/
def cyclicFixedNorm (q : ℕ) (n : ℤ) : ℤ := q * n

/-- Degree-zero fixed-orbit Tate charge. -/
def cyclicFixedTateCharge (q : ℕ) (n : ℤ) : ZMod q := n

/-- The fixed-orbit charge vanishes exactly on cyclic norms. -/
theorem cyclicFixedTateCharge_eq_zero_iff_norm (q : ℕ) (c : ℤ) :
    cyclicFixedTateCharge q c = 0 ↔ ∃ n : ℤ, cyclicFixedNorm q n = c := by
  constructor
  · intro h
    have hdvd : (q : ℤ) ∣ c :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd c q).mp h
    obtain ⟨n, hn⟩ := hdvd
    refine ⟨n, ?_⟩
    simpa [cyclicFixedNorm] using hn.symm
  · rintro ⟨n, rfl⟩
    simp [cyclicFixedTateCharge, cyclicFixedNorm]

/-- The unit fixed-orbit charge survives for every nontrivial modulus. -/
theorem cyclicFixedTateCharge_one_ne_zero {q : ℕ} (hq : 1 < q) :
    cyclicFixedTateCharge q 1 ≠ 0 := by
  letI : Fact (1 < q) := ⟨hq⟩
  simp [cyclicFixedTateCharge]

/-- Norm on the integral regular permutation lattice. -/
def cyclicRegularNorm {q : ℕ} (x : Fin q → ℤ) : Fin q → ℤ :=
  fun _ => ∑ i, x i

/-- Invariance on the transitive regular orbit means that all coordinates agree. -/
def IsCyclicRegularInvariant {q : ℕ} (x : Fin q → ℤ) : Prop :=
  ∀ i j, x i = x j

/-- Every invariant vector on a nonempty regular cyclic orbit is a norm. -/
theorem cyclicRegular_invariant_is_norm {q : ℕ} (hq : 0 < q)
    {x : Fin q → ℤ} (hx : IsCyclicRegularInvariant x) :
    ∃ y : Fin q → ℤ, cyclicRegularNorm y = x := by
  let i0 : Fin q := ⟨0, hq⟩
  let y : Fin q → ℤ := fun i => if i = i0 then x i0 else 0
  refine ⟨y, ?_⟩
  funext i
  simpa [cyclicRegularNorm, y, i0] using hx i0 i

/-- The constant unit residue is invariant on the regular orbit. -/
theorem cyclicRegular_unit_invariant {q : ℕ} :
    IsCyclicRegularInvariant (fun _ : Fin q => (1 : ℤ)) := by
  intro i j
  rfl

/-- The same unit residue that survives at a fixed orbit is a norm on every nonempty regular
orbit. -/
theorem cyclicRegular_unit_is_norm {q : ℕ} (hq : 0 < q) :
    ∃ y : Fin q → ℤ, cyclicRegularNorm y = fun _ => (1 : ℤ) :=
  cyclicRegular_invariant_is_norm hq cyclicRegular_unit_invariant

/-- Ordinary cyclic Tate descent separates fixed and regular orbits, but only through their
stabilizer type. -/
theorem cyclicTate_separates_fixed_regular {q : ℕ} (hq : 1 < q) :
    cyclicFixedTateCharge q 1 ≠ 0 ∧
      IsCyclicRegularInvariant (fun _ : Fin q => (1 : ℤ)) ∧
      ∃ y : Fin q → ℤ, cyclicRegularNorm y = fun _ => (1 : ℤ) :=
  ⟨cyclicFixedTateCharge_one_ne_zero hq,
    cyclicRegular_unit_invariant,
    cyclicRegular_unit_is_norm (lt_trans Nat.zero_lt_one hq)⟩

end RHTower
