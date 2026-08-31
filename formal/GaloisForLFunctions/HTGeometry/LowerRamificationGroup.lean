import GaloisForLFunctions.HTGeometry.TameInertiaRigidity
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Higher ramification groups in lower numbering

For a group acting on a commutative ring and an ideal `P`, the `n`th lower ramification group is
the congruence subgroup acting trivially modulo `P^(n+1)`.  `Mathlib` already proves that
congruence modulo any additive subgroup defines a subgroup; applying it to ideal powers supplies
the higher filtration explicitly left as a TODO in `Mathlib/RingTheory/Valuation/RamificationGroup`.
-/

namespace GaloisForLFunctions.HTGeometry

variable {S G : Type*} [CommRing S] [Group G] [MulSemiringAction G S]

/-- Lower ramification group in ideal-theoretic lower numbering:
`Gₙ = {g | g x - x ∈ Pⁿ⁺¹ for every integral x}`. -/
noncomputable def Ideal.lowerRamificationGroup (P : Ideal S) (n : ℕ) :
    Subgroup G := (P ^ (n + 1)).toAddSubgroup.inertia G

@[simp] theorem Ideal.mem_lowerRamificationGroup (P : Ideal S) (n : ℕ) (g : G) :
    g ∈ Ideal.lowerRamificationGroup (G := G) P n ↔
      ∀ x : S, g • x - x ∈ P ^ (n + 1) := Iff.rfl

@[simp] theorem Ideal.lowerRamificationGroup_zero (P : Ideal S) :
    Ideal.lowerRamificationGroup (G := G) P 0 = P.toAddSubgroup.inertia G := by
  ext g
  simp [Ideal.lowerRamificationGroup]

/-- Lower ramification groups decrease with depth. -/
theorem Ideal.lowerRamificationGroup_antitone (P : Ideal S) :
    Antitone (fun n => Ideal.lowerRamificationGroup (G := G) P n) := by
  intro m n hmn g hg x
  exact Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1) (hg x)

/-- Localized lower ramification group.  This form tests congruence after passage to the local
ring at `P`; it is the directly valuation-facing formulation used for explicit wild breaks. -/
noncomputable def Ideal.localizedLowerRamificationGroup (P : Ideal S) [P.IsPrime] (n : ℕ) :
    Subgroup G :=
  let B := Localization.AtPrime P
  ((((IsLocalRing.maximalIdeal B) ^ (n + 1)).comap (algebraMap S B)) : Ideal S).toAddSubgroup.inertia G

@[simp] theorem Ideal.mem_localizedLowerRamificationGroup
    (P : Ideal S) [P.IsPrime] (n : ℕ) (g : G) :
    g ∈ Ideal.localizedLowerRamificationGroup P n ↔
      ∀ x : S, algebraMap S (Localization.AtPrime P) (g • x - x) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (n + 1) := Iff.rfl

/-- At a maximal prime, localization does not change the ideal-theoretic lower filtration: the
pullback of every power of the local maximal ideal is the corresponding power of `P`. -/
theorem Ideal.localizedLowerRamificationGroup_eq_lowerRamificationGroup
    (P : Ideal S) [P.IsMaximal] (n : ℕ) :
    Ideal.localizedLowerRamificationGroup (G := G) P n =
      Ideal.lowerRamificationGroup (G := G) P n := by
  unfold Ideal.localizedLowerRamificationGroup Ideal.lowerRamificationGroup
  dsimp only
  have hcomap := IsLocalization.AtPrime.under_maximalIdeal_pow
    P (Localization.AtPrime P) (n + 1)
  change Ideal.comap (algebraMap S (Localization.AtPrime P))
      (IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (n + 1)) =
    P ^ (n + 1) at hcomap
  rw [hcomap]

/-- The localized lower ramification filtration decreases with depth. -/
theorem Ideal.localizedLowerRamificationGroup_antitone
    (P : Ideal S) [P.IsMaximal] :
    Antitone (fun n => Ideal.localizedLowerRamificationGroup (G := G) P n) := by
  intro m n hmn
  change Ideal.localizedLowerRamificationGroup (G := G) P n ≤
    Ideal.localizedLowerRamificationGroup (G := G) P m
  rw [Ideal.localizedLowerRamificationGroup_eq_lowerRamificationGroup,
    Ideal.localizedLowerRamificationGroup_eq_lowerRamificationGroup]
  exact Ideal.lowerRamificationGroup_antitone P hmn

open IsDiscreteValuationRing

/-- In a DVR, membership in the `n`th maximal-ideal power is exactly additive valuation at least
`n`. -/
theorem mem_maximalIdeal_pow_iff_le_addVal
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (x : B) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal B ^ n ↔ (n : ℕ∞) ≤ addVal B x := by
  obtain ⟨pi, hpi⟩ := exists_irreducible B
  rw [hpi.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← addVal_le_iff_dvd, hpi.addVal_pow]

end GaloisForLFunctions.HTGeometry
