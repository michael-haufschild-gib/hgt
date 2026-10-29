import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHaarDivisorFormHasSubcriticalPrimeWeights
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheInversePrimeNumberOperatorHasOccupationEnergy
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanAdjunctionEnergiesAreDistinct

/-!
# Valuation occupation controlled by the original Haar divisor reserve

The primes occurring in the finite source determine its complete valuation
space. Completing only those prime ladders gives an explicit diagonal
boundary cost. The original reserve plus that cost is one half of the full
occupation energy plus the nonnegative exact cell-weight correction.
-/

noncomputable section
open Finset
open scoped Classical

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open ArithmeticFunction ArithmeticIntersectionTheory HTGeometry
  RenormalizedArithmeticPotentialTheory

private theorem oddMultiplierFiber {a b X : ℕ} (hbX : b ≤ X) :
    (∑ m ∈ Icc 2 (2 * X + 1),
      if (2 * a + 1) * m = 2 * b + 1 then vonMangoldt m / (m : ℝ) else 0) =
      if (2 * a + 1) ∣ (2 * b + 1) ∧ a ≠ b then
        vonMangoldt ((2 * b + 1) / (2 * a + 1)) /
          (((2 * b + 1) / (2 * a + 1) : ℕ) : ℝ) else 0 := by
  have ha0 : 0 < 2 * a + 1 := by omega
  by_cases h : (2 * a + 1) ∣ (2 * b + 1) ∧ a ≠ b
  · let t := (2 * b + 1) / (2 * a + 1)
    have he : (2 * a + 1) * t = 2 * b + 1 := Nat.mul_div_cancel' h.1
    have ht0 : t ≠ 0 := by intro ht; rw [ht, mul_zero] at he; omega
    have ht1 : t ≠ 1 := by
      intro ht
      rw [ht, mul_one] at he
      exact h.2 (by omega)
    have ht : t ∈ Icc 2 (2 * X + 1) := mem_Icc.mpr ⟨by omega,
      (Nat.div_le_self _ _).trans (by omega)⟩
    rw [if_pos h, sum_eq_single t, if_pos he]
    · intro m _ hmt
      exact if_neg fun hm => hmt (Nat.eq_of_mul_eq_mul_left ha0 (hm.trans he.symm))
    · exact fun hn => (hn ht).elim
  · rw [if_neg h]
    apply sum_eq_zero
    intro m hm
    apply if_neg
    intro he
    apply h
    refine ⟨⟨m, he.symm⟩, ?_⟩
    intro hab
    subst b
    have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_left ha0 (by simpa only [mul_one] using he)
    have hm2 := (mem_Icc.mp hm).1
    omega

/-- The finite divisor-edge sum is the literal symmetric inverse-prime matrix. -/
theorem oddSubcriticalPrimeForm_eq_kernel (x : ℕ → ℝ) (X : ℕ) :
    oddSubcriticalPrimeForm x X =
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X,
        x a * x b * inversePrimeKernel (2 * a + 1) (2 * b + 1) := by
  let F (a b : ℕ) : ℝ := if (2 * a + 1) ∣ (2 * b + 1) ∧ a ≠ b then
    vonMangoldt ((2 * b + 1) / (2 * a + 1)) /
      (((2 * b + 1) / (2 * a + 1) : ℕ) : ℝ) else 0
  have hne (a b : ℕ) : (2 * a + 1 ≠ 2 * b + 1) ↔ a ≠ b := by omega
  have hentry (a b : ℕ) : inversePrimeKernel (2 * a + 1) (2 * b + 1) = F a b + F b a := by
    simp only [inversePrimeKernel_eq_directed, hne, F]
  have hf : oddSubcriticalPrimeForm x X =
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, 2 * x a * x b * F a b := by
    calc
      _ = ∑ a ∈ Icc 1 X, ∑ m ∈ Icc 2 (2 * X + 1), ∑ b ∈ Icc 1 X,
          if (2 * a + 1) * m = 2 * b + 1 then
            2 * vonMangoldt m / (m : ℝ) * x a * x b else 0 := by
        unfold oddSubcriticalPrimeForm
        exact sum_comm
      _ = ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, ∑ m ∈ Icc 2 (2 * X + 1),
          if (2 * a + 1) * m = 2 * b + 1 then
            2 * vonMangoldt m / (m : ℝ) * x a * x b else 0 :=
        sum_congr rfl fun _ _ => sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro a _
        apply sum_congr rfl
        intro b hb
        change _ = 2 * x a * x b *
          (if (2 * a + 1) ∣ (2 * b + 1) ∧ a ≠ b then _ else 0)
        rw [← oddMultiplierFiber (a := a) (mem_Icc.mp hb).2, mul_sum]
        apply sum_congr rfl
        intro m _
        split_ifs <;> ring
  have hreverse : (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, x a * x b * F b a) =
      ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, x a * x b * F a b := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    exact sum_congr rfl fun b _ => by ring
  rw [hf]
  simp_rw [hentry]
  simp only [mul_add, sum_add_distrib]
  rw [hreverse, ← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  rw [← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- All prime coordinates occurring in the actual finite Haar section. -/
def haarBoundarySieve (X : ℕ) : Finset Nat.Primes :=
  (Icc 1 X).biUnion fun a => (primeExponentVector (2 * a + 1)).support

/-- The odd midpoint is an actual supported integer of the canonical sieve. -/
def haarBoundaryClass (X : ℕ) (a : ↥(Icc 1 X)) : SieveClass (haarBoundarySieve X) :=
  ⟨2 * a.val + 1, sieveSupported_of_primeExponentVector_support_subset (by positivity)
    (fun p hp => mem_biUnion.mpr ⟨a.val, a.property, hp⟩)⟩

theorem haarBoundaryClass_injective (X : ℕ) : Function.Injective (haarBoundaryClass X) := by
  intro a b h
  have he := congrArg Subtype.val h
  change 2 * a.val + 1 = 2 * b.val + 1 at he
  apply Subtype.ext
  omega

/-- Literal odd midpoint labels of the finite section. -/
def haarBoundarySet (X : ℕ) : Finset (SieveClass (haarBoundarySieve X)) :=
  univ.image (haarBoundaryClass X)

/-- The original normalized coefficient at a supported odd midpoint. -/
def haarBoundaryCoefficient (d : ℕ → ℝ) (X : ℕ)
    (n : SieveClass (haarBoundarySieve X)) : ℝ :=
  haarArithmeticCoordinate d ((n.val - 1) / 2)

theorem haarBoundaryCoefficient_class (d : ℕ → ℝ) (X : ℕ) (a : ↥(Icc 1 X)) :
    haarBoundaryCoefficient d X (haarBoundaryClass X a) = haarArithmeticCoordinate d a.val := by
  unfold haarBoundaryCoefficient haarBoundaryClass
  congr 1
  omega

/-- The actual finite Haar vector in the complete valuation Hilbert space. -/
def haarValuationVector (d : ℕ → ℝ) (X : ℕ) : FiniteNumberSpace (haarBoundarySieve X) :=
  inversePrimeFiniteVector (haarBoundarySieve X) (haarBoundarySet X) (haarBoundaryCoefficient d X)

/-- The absent odd root remains a zero coordinate in the complete valuation space. -/
theorem haarValuationVector_zeroRoot (d : ℕ → ℝ) (X : ℕ) :
    haarValuationVector d X (fun _ => 0) = 0 := by
  let root : SieveClass (haarBoundarySieve X) := ⟨1, ⟨0, by simp⟩⟩
  have he : sieveValuationEquiv (haarBoundarySieve X) root = fun _ => 0 := by
    funext p
    change (1 : ℕ).factorization (p : Nat.Primes) = 0
    simp only [Nat.factorization_one, Finsupp.zero_apply]
  have hn : root ∉ haarBoundarySet X := by
    intro h
    obtain ⟨a, _, ha⟩ := mem_image.mp h
    have hv := congrArg Subtype.val ha
    change 2 * a.val + 1 = 1 at hv
    have ha1 := (mem_Icc.mp a.property).1
    omega
  rw [haarValuationVector, ← he, inversePrimeFiniteVector_apply, if_neg hn]

private theorem haarBoundarySet_sum (X : ℕ) (g : SieveClass (haarBoundarySieve X) → ℝ) :
    (∑ n ∈ haarBoundarySet X, g n) = ∑ a : ↥(Icc 1 X), g (haarBoundaryClass X a) := by
  unfold haarBoundarySet
  exact sum_image fun a _ b _ h => haarBoundaryClass_injective X h

theorem haarBoundaryFiniteEnergy_eq (d : ℕ → ℝ) (X : ℕ) :
    inversePrimeFiniteEnergy (haarBoundarySieve X) (haarBoundarySet X)
      (haarBoundaryCoefficient d X) =
      (∑ a ∈ Icc 1 X, (Real.log ((2 * a + 1 : ℕ) : ℝ) +
        inversePrimeEuler (haarBoundarySieve X)) * haarArithmeticCoordinate d a ^ 2) -
        oddSubcriticalPrimeForm (haarArithmeticCoordinate d) X := by
  unfold inversePrimeFiniteEnergy
  simp_rw [haarBoundarySet_sum, haarBoundaryCoefficient_class]
  rw [oddSubcriticalPrimeForm_eq_kernel]
  change (∑ a : ↥(Icc 1 X),
      (Real.log ((2 * a.val + 1 : ℕ) : ℝ) + inversePrimeEuler (haarBoundarySieve X)) *
        haarArithmeticCoordinate d a.val ^ 2) -
      (∑ a : ↥(Icc 1 X), ∑ b : ↥(Icc 1 X),
        haarArithmeticCoordinate d a.val * haarArithmeticCoordinate d b.val *
          inversePrimeKernel (2 * a.val + 1) (2 * b.val + 1)) = _
  congr 1
  · exact sum_coe_sort (Icc 1 X) _
  · calc
      _ = ∑ a : ↥(Icc 1 X), ∑ b ∈ Icc 1 X,
          haarArithmeticCoordinate d a.val * haarArithmeticCoordinate d b *
            inversePrimeKernel (2 * a.val + 1) (2 * b + 1) :=
        sum_congr rfl fun a _ => sum_coe_sort (Icc 1 X) _
      _ = _ := sum_coe_sort (Icc 1 X) _

/-- Exact diagonal compensation for completing the selected prime ladders. -/
def haarValuationBoundaryCost (d : ℕ → ℝ) (X : ℕ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a ∈ Icc 1 X,
    (inversePrimeEuler (haarBoundarySieve X) - oddDivisorOutgoing X a) *
      haarArithmeticCoordinate d a ^ 2

/-- The completed number form and its boundary charge are both attached to the original source. -/
theorem haarPrimeLogDefect_add_boundary_eq_finiteEnergy (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X + haarValuationBoundaryCost d X =
      (1 / 2 : ℝ) * inversePrimeFiniteEnergy (haarBoundarySieve X) (haarBoundarySet X)
        (haarBoundaryCoefficient d X) +
      oddDivisorForm (fun a => haarBoundaryWeight a - 1 / 2) (haarArithmeticCoordinate d) X := by
  have hsum : (∑ a ∈ Icc 1 X,
      (Real.log ((2 * a + 1 : ℕ) : ℝ) + inversePrimeEuler (haarBoundarySieve X)) *
        haarArithmeticCoordinate d a ^ 2) =
      (∑ a ∈ Icc 1 X, (Real.log ((2 * a + 1 : ℕ) : ℝ) + oddDivisorOutgoing X a) *
        haarArithmeticCoordinate d a ^ 2) +
      ∑ a ∈ Icc 1 X, (inversePrimeEuler (haarBoundarySieve X) - oddDivisorOutgoing X a) *
        haarArithmeticCoordinate d a ^ 2 := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [haarBoundaryFiniteEnergy_eq, hsum,
    ← oddDivisorForm_one_add_prime, haarPrimeLogDefect_subcritical_decomposition,
    haarValuationBoundaryCost]
  ring

/-- The full excitation energy of the actual source in the complete product basis. -/
def haarValuationOccupation (d : ℕ → ℝ) (X : ℕ) (e : haarBoundarySieve X → ℕ) : ℝ :=
  inversePrimeOccupationEnergy (haarBoundarySieve X) e *
    ‖(finiteBlaschkeBasis (fun p : haarBoundarySieve X => inversePrimeParameter p)
      (fun p => inversePrimeParameter_norm_lt_one p)).repr (haarValuationVector d X) e‖ ^ 2

theorem haarValuationOccupation_nonneg (d : ℕ → ℝ) (X : ℕ) (e : haarBoundarySieve X → ℕ) :
    0 ≤ haarValuationOccupation d X e :=
  mul_nonneg (inversePrimeOccupationEnergy_nonneg (haarBoundarySieve X) e) (sq_nonneg _)

theorem haarValuationOccupation_hasSum (d : ℕ → ℝ) (X : ℕ) :
    HasSum (haarValuationOccupation d X)
      (inversePrimeFiniteEnergy (haarBoundarySieve X) (haarBoundarySet X)
        (haarBoundaryCoefficient d X)) :=
  inversePrimeFiniteEnergy_hasSum (haarBoundarySieve X) (haarBoundarySet X)
    (haarBoundaryCoefficient d X)

/-- Exact occupation-energy decomposition of every signed finite Haar divisor source.
The diagonal completion and the positive cell-weight remainder remain explicit. -/
theorem haarPrimeLogDefect_add_boundary_eq_occupation (d : ℕ → ℝ) (X : ℕ) :
    haarPrimeLogDefect d X + haarValuationBoundaryCost d X =
      (1 / 2 : ℝ) * (∑' e, haarValuationOccupation d X e) +
        oddDivisorForm (fun a => haarBoundaryWeight a - 1 / 2)
          (haarArithmeticCoordinate d) X := by
  rw [(haarValuationOccupation_hasSum d X).tsum_eq]
  exact haarPrimeLogDefect_add_boundary_eq_finiteEnergy d X

/-- The original reserve, with its stated completion cost, controls every valuation mode. -/
theorem haarPrimeLogDefect_add_boundary_ge_occupation (d : ℕ → ℝ) (X : ℕ) :
    (1 / 2 : ℝ) * (∑' e, haarValuationOccupation d X e) ≤
      haarPrimeLogDefect d X + haarValuationBoundaryCost d X := by
  have hsurplus : 0 ≤ oddDivisorForm (fun a => haarBoundaryWeight a - 1 / 2)
      (haarArithmeticCoordinate d) X := by
    have he := haarPrimeLogDefect_subcritical_decomposition d X
    have hl := haarPrimeLogDefect_ge_subcritical_form d X
    linarith only [he, hl]
  rw [haarPrimeLogDefect_add_boundary_eq_occupation]
  exact le_add_of_nonneg_right hsurplus

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
