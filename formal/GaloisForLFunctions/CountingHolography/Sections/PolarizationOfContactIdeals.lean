import GaloisForLFunctions.CountingHolography.Sections.SignedSplineSmallSections
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFrobeniusGraphsMeetInThePrimes

/-!
# Adding signed divisors to the prime-contact lattice

At a common resolution, adding a divisor multiplies the two contact ideals
and their polarized contact ideal by an integral factor. At each prime
power the extra exponent is zero, one or two, independently of all
multiplicities. The same formula applies to the negative of a divisor.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset AbsoluteGeometryOfSpecZ

/-- The local condition is the literal contact ideal of the Frobenius graph
with the diagonal in the arithmetic square. -/
theorem graphIdeal_eq_span_contactBase {k : ℕ+} (hk : 1 < k) :
    graphIdeal 1 k = Ideal.span {(contactBase k : ℤ)} := by
  by_cases h : IsPrimePow (k : ℕ)
  · obtain ⟨p, j, hp, hj, he⟩ := (isPrimePow_nat_iff _).mp h
    let P : ℕ+ := ⟨p, hp.pos⟩
    have hpow : k = P^j := PNat.eq (by simpa [P] using he.symm)
    have hbase : contactBase k = p := by
      rw [contactBase, if_pos h, ← he, Nat.pow_minFac hj.ne', hp.minFac_eq]
    rw [hbase, hpow]
    exact graphIdeal_one_prime_pow (p := P) hp hj.ne'
  · rw [graphIdeal_one_eq_top hk h, contactBase, if_neg h]
    simp

theorem card_contactRing {k : ℕ+} (hk : 1 < k) :
    Nat.card (ℤ ⧸ graphIdeal 1 k) = contactBase k := by
  rw [graphIdeal_eq_span_contactBase hk,
    Nat.card_congr (Int.quotientSpanNatEquivZMod (contactBase k)).toEquiv, Nat.card_zmod]

/-- Two oriented incidences between different packets. -/
def mixedMultiplicity (f g : ℝ → ℝ) (L n k : ℕ) : ℝ :=
  2 / Real.sqrt k * ∑ j ∈ Ioc n (n + L*n),
    (degreeSample f n j * degreeSample g n (j*k) +
      degreeSample g n j * degreeSample f n (j*k)) / j

theorem contactMultiplicity_add (f g : ℝ → ℝ) (L n k : ℕ) :
    contactMultiplicity (f+g) L n k =
      contactMultiplicity f L n k + contactMultiplicity g L n k + mixedMultiplicity f g L n k := by
  unfold contactMultiplicity mixedMultiplicity
  rw [← mul_add, ← mul_add, ← sum_add_distrib, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j _
  simp only [degreeSample, Pi.add_apply]
  ring

/-- Reversing every coefficient fixes the local incidence multiplicities
at the original finite resolution. -/
theorem contactGenerator_neg (f : ℝ → ℝ) (L n : ℕ) :
    contactGenerator (-f) L n = contactGenerator f L n := by
  simp only [contactGenerator, contactMultiplicity, degreeSample, Pi.neg_apply, neg_mul_neg]

theorem logRadius_neg (f : ℝ → ℝ) (L n : ℕ) : logRadius (-f) L n = logRadius f L n := by
  have h (t : ℝ) : sampledDegree (-f) L n t = - sampledDegree f L n t := by
    simp only [sampledDegree, degreeSample, Pi.neg_apply, neg_mul, neg_div, sum_neg_distrib]
  simp only [logRadius, h, neg_mul_neg, degreeForm, degreePairing, degreeSample, Pi.neg_apply, neg_sq]

/-- The ordinary section set is exactly the same for both signs of the
whole signed divisor, at each finite multiplicity. -/
theorem smallSections_neg {N : ℕ} (a : Fin N → ℤ) :
    smallSections (generator (-a) : ℝ) (radius (-a)) = smallSections (generator a : ℝ) (radius a) := by
  have h : packet (-a) = - packet a := by
    funext u
    simp only [packet, splineSource, Pi.neg_apply, Int.cast_neg, neg_mul, sum_neg_distrib]
  have hr : resolution (-a) = resolution a := by simp [resolution]
  simp only [generator, radius, h, hr, contactGenerator_neg, logRadius_neg]

/-- The mixed ideal uses the same residue primes as both original ideals. -/
def mixedGenerator (f g : ℝ → ℝ) (L n : ℕ) : ℚ :=
  ∏ k ∈ Icc 2 L, (contactBase k : ℚ) ^ ⌊mixedMultiplicity f g L n k⌋

private theorem floor_three (x y z : ℝ) :
    ∃ e : ℕ, e ≤ 2 ∧ ⌊x+y+z⌋ = ⌊x⌋ + ⌊y⌋ + ⌊z⌋ + e := by
  let b := ⌊x⌋ + ⌊y⌋ + ⌊z⌋
  have h₀ : b ≤ ⌊x+y+z⌋ := Int.le_floor.mpr (by
    dsimp [b]; push_cast; linarith only [Int.floor_le x, Int.floor_le y, Int.floor_le z])
  have h₃ : ⌊x+y+z⌋ < b + 3 := Int.floor_lt.mpr (by
    dsimp [b]; push_cast; linarith only [Int.lt_floor_add_one x, Int.lt_floor_add_one y, Int.lt_floor_add_one z])
  exact ⟨(⌊x+y+z⌋ - b).toNat, by omega, by dsimp [b] at *; omega⟩

/-- First variation of the fractional ideal. The index of the additional
integral restriction divides a fixed integer depending only on the window. -/
theorem contactGenerator_add (f g : ℝ → ℝ) (L n : ℕ) :
    ∃ c : ℕ, c ∣ ∏ k ∈ Icc 2 L, contactBase k ^ 2 ∧
      contactGenerator (f+g) L n =
        contactGenerator f L n * contactGenerator g L n * mixedGenerator f g L n * c := by
  choose e he heq using fun k =>
    floor_three (contactMultiplicity f L n k) (contactMultiplicity g L n k) (mixedMultiplicity f g L n k)
  refine ⟨∏ k ∈ Icc 2 L, contactBase k ^ e k,
    prod_dvd_prod_of_dvd _ _ (fun k _ => pow_dvd_pow _ (he k)), ?_⟩
  unfold contactGenerator mixedGenerator
  push_cast
  simp only [← prod_mul_distrib]
  apply prod_congr rfl
  intro k _
  have hk : (contactBase k : ℚ) ≠ 0 := (Nat.cast_pos.mpr (contactBase_pos k)).ne'
  rw [contactMultiplicity_add, heq, zpow_add₀ hk, zpow_add₀ hk, zpow_add₀ hk, zpow_natCast]

#print axioms card_contactRing
#print axioms contactGenerator_add

end GaloisForLFunctions.CountingHolography.Sections
