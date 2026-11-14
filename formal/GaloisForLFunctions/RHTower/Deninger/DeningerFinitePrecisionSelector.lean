import GaloisForLFunctions.RHTower.Deninger.DeningerSUnitEndpointPage
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationSelectorResidue

/-!
# Finite precision selection from S-unit coordinates

The `S`-unit with every exponent equal to one is positive, has valuation
one on `S`, and has zero valuation elsewhere. Used as a selector parameter,
it turns one square-denominator condition into an exact finite collection
of local existence tests. Different primes may select different candidates.
The only cardinality requirement is that each prime exceed the number of
candidates, so successful residues cannot cancel.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.Arithmetic
open scoped Classical

/-- The positive squarefree parameter in the all-ones S-unit coordinate. -/
noncomputable def deningerPrecisionParameter (S : Finset Nat.Primes) : ℚ :=
  (deningerSUnitProduct S (fun _ => 1) : ℚˣ)

theorem deningerPrecisionParameter_pos (S : Finset Nat.Primes) :
    0 < deningerPrecisionParameter S :=
  deningerSUnits_pos (deningerSUnitProduct_mem S (fun _ => 1))

theorem deningerPrecisionParameter_val (S : Finset Nat.Primes) (p : Nat.Primes) :
    padicValRat (p : ℕ) (deningerPrecisionParameter S) = if p ∈ S then 1 else 0 :=
  deningerSUnitProduct_val S (fun _ => 1) p

/-- The square-denominator selector is equivalent to existence of a
passing candidate separately at each prime of `S`. All parameters are
explicit S-unit products; no noncancellation hypothesis is assumed. -/
theorem deninger_finite_precision_selector {G J : Type*}
    (S : Finset Nat.Primes) (g : Finset G) (s : Finset J) (k : J → ℕ)
    (D : G → J → ℚ) (hcard : ∀ p ∈ S, g.card < (p : ℕ)) :
    (valuationSelectorSum g s k (deningerPrecisionParameter S) D ≠ 0 ∧
      SquareDenominator (deningerPrecisionParameter S /
        valuationSelectorSum g s k (deningerPrecisionParameter S) D ^ 2)) ↔
      g.Nonempty ∧ ∀ p ∈ S, ∃ a ∈ g, ∀ j ∈ s,
        D a j = 0 ∨ (k j : ℤ) ≤ padicValRat (p : ℕ) (D a j) := by
  have hR0 := (deningerPrecisionParameter_pos S).ne'
  constructor
  · rintro ⟨hΘ, hD₂⟩
    have hg : g.Nonempty := by
      by_contra hn
      apply hΘ
      exact Finset.sum_eq_zero (fun a ha => False.elim (hn ⟨a, ha⟩))
    refine ⟨hg, ?_⟩
    intro p hp
    letI : Fact (p : ℕ).Prime := ⟨p.2⟩
    have hR : padicValRat (p : ℕ) (deningerPrecisionParameter S) = 1 := by
      rw [deningerPrecisionParameter_val, if_pos hp]
    have hodd : ¬ Even (padicValRat (p : ℕ) (deningerPrecisionParameter S)) := by
      rw [hR, Int.even_iff]
      omega
    have hΘint : 0 ≤ padicValRat (p : ℕ)
        (valuationSelectorSum g s k (deningerPrecisionParameter S) D) :=
      val_finset_sum_nonneg g _ (fun a _ =>
        valuationSelectorWeight_integral s k hodd (D a))
    have hB := (squareDenominator_iff _).mp hD₂ (p : ℕ) p.2
    rw [padicValRat.div hR0 (pow_ne_zero 2 hΘ), padicValRat.pow, hR] at hB
    have hval : padicValRat (p : ℕ)
        (valuationSelectorSum g s k (deningerPrecisionParameter S) D) = 0 := by
      rcases hB with hn | he
      · omega
      · rw [Int.even_iff] at he
        omega
    have hres := ((padicValRat_eq_zero_iff hΘ).mp hval).ratRes_ne_zero
    exact (valuationSelectorSum_residue_ne_zero_iff g s k (deningerPrecisionParameter S)
      D hR (hcard p hp)).mp hres
  · rintro ⟨hg, hpass⟩
    have hΘ := (valuationSelectorSum_pos g s k (deningerPrecisionParameter_pos S) D hg).ne'
    refine ⟨hΘ, (squareDenominator_iff _).mpr ?_⟩
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    have hR := deningerPrecisionParameter_val S ⟨p, hp⟩
    by_cases hmem : (⟨p, hp⟩ : Nat.Primes) ∈ S
    · rw [if_pos hmem] at hR
      have hres := (valuationSelectorSum_residue_ne_zero_iff g s k
        (deningerPrecisionParameter S) D hR (hcard ⟨p, hp⟩ hmem)).mpr (hpass ⟨p, hp⟩ hmem)
      have hval := val_eq_zero_of_ratRes_ne_zero hres
      left
      rw [padicValRat.div hR0 (pow_ne_zero 2 hΘ), padicValRat.pow, hR, hval]
      norm_num
    · rw [if_neg hmem] at hR
      right
      rw [padicValRat.div hR0 (pow_ne_zero 2 hΘ), padicValRat.pow, hR]
      refine ⟨-padicValRat p (valuationSelectorSum g s k (deningerPrecisionParameter S) D), ?_⟩
      ring

#print axioms deninger_finite_precision_selector

end RHTower
