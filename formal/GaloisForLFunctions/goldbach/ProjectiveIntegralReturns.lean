import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Integral returns of projective parity transport

A non-affine fractional linear map can return an integer only when its
denominator divides its determinant. This gives a sharp finite return count.
For the kernel `T - m*n`, the two coordinate determinants are `Δ` and `T²Δ`.
Degenerate matrices are handled explicitly; no analytic estimate is assumed.
-/

namespace GaloisForLFunctions.Goldbach

open Finset
open scoped BigOperators

/-- Both signs of the nonzero divisors; the set is empty at zero. -/
def signedDivisors (D : ℤ) : Finset ℤ :=
  D.natAbs.divisors.image (fun n : ℕ => (n : ℤ)) ∪
    D.natAbs.divisors.image (fun n : ℕ => -(n : ℤ))

theorem mem_signedDivisors (D z : ℤ) :
    z ∈ signedDivisors D ↔ z ≠ 0 ∧ z ∣ D ∧ D ≠ 0 := by
  simp only [signedDivisors, mem_union, mem_image]
  constructor
  · rintro (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hn).ne'
      have hD0 : D ≠ 0 := by
        intro hD
        simp only [hD, Int.natAbs_zero, Nat.divisors_zero, notMem_empty] at hn
      exact ⟨hn0, Int.natCast_dvd.mpr (Nat.dvd_of_mem_divisors hn), hD0⟩
    · have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hn).ne'
      have hD0 : D ≠ 0 := by
        intro hD
        simp only [hD, Int.natAbs_zero, Nat.divisors_zero, notMem_empty] at hn
      exact ⟨neg_ne_zero.mpr hn0,
        neg_dvd.mpr (Int.natCast_dvd.mpr (Nat.dvd_of_mem_divisors hn)), hD0⟩
  · rintro ⟨_, hzD, hD0⟩
    have hzmem : z.natAbs ∈ D.natAbs.divisors := Nat.mem_divisors.mpr
      ⟨Int.natAbs_dvd_natAbs.mpr hzD, by
        intro hz
        rcases Int.natAbs_eq D with h | h <;> omega⟩
    rcases Int.natAbs_eq z with hz | hz
    · exact Or.inl ⟨z.natAbs, hzmem, by omega⟩
    · exact Or.inr ⟨z.natAbs, hzmem, by omega⟩

theorem card_signedDivisors (D : ℤ) :
    (signedDivisors D).card = 2 * D.natAbs.divisors.card := by
  have hp : Function.Injective (fun n : ℕ => (n : ℤ)) := by
    intro n m h
    change (n : ℤ) = (m : ℤ) at h
    exact_mod_cast h
  have hn : Function.Injective (fun n : ℕ => -(n : ℤ)) := by
    intro n m h
    exact hp (neg_injective h)
  have hd : Disjoint (D.natAbs.divisors.image (fun n : ℕ => (n : ℤ)))
      (D.natAbs.divisors.image (fun n : ℕ => -(n : ℤ))) := by
    refine disjoint_left.mpr ?_
    rintro z hz hz'
    obtain ⟨n, hnmem, rfl⟩ := mem_image.mp hz
    obtain ⟨m, hmmem, hmn⟩ := mem_image.mp hz'
    have hnpos : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_mem_divisors hnmem
    have hmpos : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_mem_divisors hmmem
    omega
  rw [signedDivisors, card_union_of_disjoint hd,
    card_image_of_injective _ hp, card_image_of_injective _ hn]
  omega

/-- Integer coefficients; singular matrices remain visible in the return bound. -/
structure ProjectiveCoefficients where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

namespace ProjectiveCoefficients

def det (g : ProjectiveCoefficients) : ℤ := g.a * g.d - g.b * g.c

/-- Inputs at which the nonzero denominator divides the numerator. -/
def integralReturns (g : ProjectiveCoefficients) (S : Finset ℤ) : Finset ℤ :=
  S.filter (fun m => g.c * m + g.d ≠ 0 ∧ (g.c * m + g.d) ∣ (g.a * m + g.b))

/-- The full input count for affine or singular maps; otherwise the divisor cap. -/
def returnCap (g : ProjectiveCoefficients) (S : Finset ℤ) : ℕ :=
  if g.c = 0 ∨ g.det = 0 then S.card else min S.card (2 * g.det.natAbs.divisors.card)

/-- A nonsingular, non-affine map injects its integral returns into signed divisors. -/
theorem card_integralReturns_le (g : ProjectiveCoefficients) (S : Finset ℤ) :
    (g.integralReturns S).card ≤ g.returnCap S := by
  have hS : (g.integralReturns S).card ≤ S.card := card_filter_le _ _
  by_cases hg : g.c = 0 ∨ g.det = 0
  · simpa only [returnCap, if_pos hg] using hS
  · have hc : g.c ≠ 0 := fun h => hg (Or.inl h)
    have hD : g.det ≠ 0 := fun h => hg (Or.inr h)
    have hi : Function.Injective (fun m : ℤ => g.c * m + g.d) := by
      intro m n h
      exact mul_left_cancel₀ hc (add_right_cancel h)
    have hsub : (g.integralReturns S).image (fun m => g.c * m + g.d) ⊆
        signedDivisors g.det := by
      intro t ht
      obtain ⟨m, hm, rfl⟩ := mem_image.mp ht
      obtain ⟨_, hm0, hmdvd⟩ := mem_filter.mp hm
      have hdiv : (g.c * m + g.d) ∣ g.det := by
        have h := dvd_sub (dvd_mul_of_dvd_right hmdvd g.c)
          (dvd_mul_left (g.c * m + g.d) g.a)
        have he : g.c * (g.a * m + g.b) - g.a * (g.c * m + g.d) = -g.det := by
          simp only [det]
          ring
        rw [he, dvd_neg] at h
        exact h
      exact (mem_signedDivisors _ _).mpr ⟨hm0, hdiv, hD⟩
    have hbound : (g.integralReturns S).card ≤ 2 * g.det.natAbs.divisors.card := by
      calc
        _ = ((g.integralReturns S).image (fun m => g.c * m + g.d)).card :=
          (card_image_of_injective _ hi).symm
        _ ≤ (signedDivisors g.det).card := card_le_card hsub
        _ = _ := card_signedDivisors _
    simpa only [returnCap, if_neg hg] using le_min hS hbound

/-- Inversion realizes every allowed denominator, so the divisor count is sharp. -/
def inversion (D : ℤ) : ProjectiveCoefficients := ⟨0, D, 1, 0⟩

/-- Complete integral-return classification for inversion, including its degenerate case. -/
theorem integralReturns_inversion_eq (D : ℤ) (S : Finset ℤ) :
    (inversion D).integralReturns S =
      if D = 0 then S.erase 0 else S ∩ signedDivisors D := by
  by_cases hD : D = 0
  · subst D
    ext m
    simp [integralReturns, inversion, and_comm]
  · ext m
    simp [integralReturns, inversion, hD, mem_signedDivisors]

theorem integralReturns_inversion (D : ℤ) :
    (inversion D).integralReturns (signedDivisors D) = signedDivisors D := by
  apply filter_eq_self.mpr
  intro m hm
  have h := (mem_signedDivisors D m).mp hm
  simpa only [inversion, one_mul, zero_mul, add_zero, zero_add] using ⟨h.1, h.2.1⟩

theorem card_integralReturns_inversion (D : ℤ) :
    ((inversion D).integralReturns (signedDivisors D)).card = 2 * D.natAbs.divisors.card := by
  rw [integralReturns_inversion, card_signedDivisors]

/-- Applying the same map to `T/n` induces these coefficients on `n`. -/
def columnCoordinates (g : ProjectiveCoefficients) (T : ℤ) : ProjectiveCoefficients :=
  ⟨T * g.d, T ^ 2 * g.c, g.b, T * g.a⟩

theorem det_columnCoordinates (g : ProjectiveCoefficients) (T : ℤ) :
    (g.columnCoordinates T).det = T ^ 2 * g.det := by
  simp only [columnCoordinates, det]
  ring

/-- The exact numerator of projective transport of the signed arithmetic argument. -/
theorem bilinearKernel_numerator (g : ProjectiveCoefficients) (T m n : ℤ) :
    T * ((g.c * m + g.d) * (g.a * T + g.b * n) -
      (g.a * m + g.b) * (g.c * T + g.d * n)) =
        T * g.det * (T - m * n) := by
  simp only [det]
  ring

/-- Both transformed coordinates must return to the integer lattice. -/
def jointIntegralReturns (g : ProjectiveCoefficients) (T : ℤ) (S U : Finset ℤ) :
    Finset (ℤ × ℤ) := g.integralReturns S ×ˢ (g.columnCoordinates T).integralReturns U

theorem card_jointIntegralReturns_le (g : ProjectiveCoefficients) (T : ℤ) (S U : Finset ℤ) :
    (g.jointIntegralReturns T S U).card ≤
      g.returnCap S * (g.columnCoordinates T).returnCap U := by
  rw [jointIntegralReturns, card_product]
  exact Nat.mul_le_mul (g.card_integralReturns_le S)
    ((g.columnCoordinates T).card_integralReturns_le U)

/-- A family of common symmetries must pay the sum of its actual return caps. -/
theorem card_jointIntegralReturns_family_le {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (g : ι → ProjectiveCoefficients) (T : ℤ) (S U : Finset ℤ) :
    (I.biUnion (fun i => (g i).jointIntegralReturns T S U)).card ≤
      ∑ i ∈ I, (g i).returnCap S * ((g i).columnCoordinates T).returnCap U := by
  exact card_biUnion_le.trans (sum_le_sum fun i _ => (g i).card_jointIntegralReturns_le T S U)

end ProjectiveCoefficients

end GaloisForLFunctions.Goldbach
