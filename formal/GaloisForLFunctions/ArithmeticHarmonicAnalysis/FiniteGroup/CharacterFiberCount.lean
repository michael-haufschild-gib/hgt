import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Counting endomorphism fibers by annihilating characters

The characters trivial on an endomorphism's image form its annihilator.
Their sum detects image membership, and their number equals the kernel
size. Thus their sum counts every fiber, including empty fibers.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {M R : Type*} [CommMonoid M] [Finite M] [CommRing R] [IsDomain R]
    [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

local instance : Fintype (MulChar M R) := Fintype.ofFinite _

/-- Characters annihilating the image of an endomorphism of the unit group. -/
def unitEndomorphismCharacters (f : Mˣ →* Mˣ) : Subgroup (MulChar M R) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar M R f.range).ofDual

omit [IsDomain R] in
/-- Membership means that the character is one on every image element. -/
theorem mem_unitEndomorphismCharacters_iff (f : Mˣ →* Mˣ) (χ : MulChar M R) :
    χ ∈ unitEndomorphismCharacters (R := R) f ↔ ∀ u : Mˣ, χ (f u : M) = 1 := by
  rw [unitEndomorphismCharacters, MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff]
  constructor
  · intro h u
    exact h (f u) ⟨u, rfl⟩
  · rintro h _ ⟨u, rfl⟩
    exact h u

private def characterEvaluation (H : Subgroup (MulChar M R)) (a : Mˣ) : MulChar H R where
  toFun χ := χ.val (a : M)
  map_one' := MulChar.one_apply_coe a
  map_mul' χ ψ := MulChar.mul_apply χ.val ψ.val (a : M)
  map_nonunit' χ hχ := (hχ (Group.isUnit χ)).elim

/-- A fiber cardinality is the sum of the characters annihilating the endomorphism image. -/
theorem unitEndomorphism_fiber_card_eq_character_sum (f : Mˣ →* Mˣ) (a : Mˣ) :
    (Nat.card {u : Mˣ | f u = a} : R) =
      ∑ χ : unitEndomorphismCharacters (R := R) f, χ.val (a : M) := by
  classical
  let H := unitEndomorphismCharacters (R := R) f
  have hcard : Nat.card H = Nat.card f.ker := by
    change Nat.card (MulChar.subgroupOrderIsoSubgroupMulChar M R f.range).ofDual = _
    rw [MulChar.card_subgroupOrderIsoSubgroupMulChar, ← Subgroup.index_eq_card,
      Subgroup.index_range]
  by_cases ha : a ∈ f.range
  · obtain ⟨u, rfl⟩ := ha
    have hfiber : Nat.card {v : Mˣ | f v = f u} = Nat.card f.ker := by
      simpa only [Set.preimage, Set.mem_singleton_iff] using Nat.card_congr (f.fiberEquivKer u)
    rw [hfiber, ← hcard]
    have heval (χ : H) : χ.val (f u : M) = 1 :=
      (mem_unitEndomorphismCharacters_iff f χ.val).mp χ.property u
    change (Nat.card H : R) = ∑ χ : H, χ.val (f u : M)
    simp only [heval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      Nat.card_eq_fintype_card]
  · have hempty : IsEmpty {u : Mˣ | f u = a} := ⟨fun u => ha ⟨u.val, u.property⟩⟩
    have hzero : Nat.card {u : Mˣ | f u = a} = 0 := Nat.card_eq_zero.mpr (Or.inl hempty)
    rw [hzero, Nat.cast_zero]
    have hnontrivial : characterEvaluation H a ≠ 1 := by
      intro heq
      have hmem : a ∈ (MulChar.subgroupOrderIsoSubgroupMulChar M R).symm
          (OrderDual.toDual H) := by
        apply MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff.mpr
        intro χ hχ
        have h := DFunLike.congr_fun heq (⟨χ, hχ⟩ : H)
        change χ (a : M) = (1 : MulChar H R) ⟨χ, hχ⟩ at h
        exact h.trans (MulChar.one_apply (Group.isUnit _))
      change a ∈ (MulChar.subgroupOrderIsoSubgroupMulChar M R).symm
        (MulChar.subgroupOrderIsoSubgroupMulChar M R f.range) at hmem
      rw [OrderIso.symm_apply_apply] at hmem
      exact ha hmem
    exact (MulChar.sum_eq_zero_of_ne_one hnontrivial).symm

omit [IsDomain R] in
/-- For a power endomorphism, the annihilator consists exactly of characters killed by that power. -/
theorem mem_powerEndomorphismCharacters_iff (n : ℕ) (χ : MulChar M R) :
    χ ∈ unitEndomorphismCharacters (R := R) (powMonoidHom n : Mˣ →* Mˣ) ↔
      χ ^ n = 1 := by
  rw [mem_unitEndomorphismCharacters_iff]
  constructor
  · intro h
    apply MulChar.ext
    intro u
    rw [MulChar.pow_apply_coe, MulChar.one_apply_coe]
    have hu := h u
    simpa only [powMonoidHom_apply, Units.val_pow_eq_pow_val, map_pow] using hu
  · intro h u
    change χ ((u : M) ^ n) = 1
    rw [map_pow, ← MulChar.pow_apply_coe, h, MulChar.one_apply_coe]

omit [IsDomain R] in
/-- In a cyclic unit group, the number of characters killed by `n` is the expected gcd. -/
theorem powerEndomorphismCharacters_card [IsCyclic Mˣ] (n : ℕ) :
    Nat.card (unitEndomorphismCharacters (R := R) (powMonoidHom n : Mˣ →* Mˣ)) =
      Nat.gcd (Nat.card Mˣ) n := by
  rw [unitEndomorphismCharacters, MulChar.card_subgroupOrderIsoSubgroupMulChar,
    ← Subgroup.index_eq_card, Subgroup.index_range, IsCyclic.card_powMonoidHom_ker]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
