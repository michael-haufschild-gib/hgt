import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFilterCoefficientField
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Vandermonde families over prime-filter coefficient fields

An injective prime label gives algebraically independent prime-supported power columns over every
proper filter coefficient field that permits finite exceptional sets. Every large prime set is
infinite, so a Vandermonde packet can be chosen inside the zero set of a hypothetical relation.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- Polynomial prime weights remain linearly independent modulo every proper filter finer than
the cofinite filter. -/
theorem filterCoefficientIndependent_powers
    (F : Filter Nat.Primes) [F.NeBot] (hF : F ≤ cofinite)
    (u : Nat.Primes → ℂ) (hu : Function.Injective u) (n : ℕ) :
    FilterCoefficientIndependent F (fun (i : Fin n) p => u p ^ (i : ℕ)) := by
  intro c hc
  let S : Set Nat.Primes := {p | ∑ i : Fin n, c i * u p ^ (i : ℕ) = 0}
  have hS : S.Infinite := by
    intro hfin
    have hn : ∀ᶠ p in F, p ∉ S := hF (eventually_cofinite.mpr (by simpa using hfin))
    obtain ⟨p, hp, hnp⟩ := (hc.and hn).exists
    exact hnp hp
  obtain ⟨t, ht, hcard⟩ := hS.exists_subset_card_eq n
  let points : Fin n → Nat.Primes := fun i =>
    ((Finset.equivFinOfCardEq hcard).symm i : Nat.Primes)
  have hpoints : Function.Injective points := by
    intro i j hij
    have heq : (Finset.equivFinOfCardEq hcard).symm i =
        (Finset.equivFinOfCardEq hcard).symm j := Subtype.ext hij
    simpa only [Equiv.apply_symm_apply] using congrArg (Finset.equivFinOfCardEq hcard) heq
  have hpacket : IsUnit
      (Matrix.of fun row (i : Fin n) => u (points row) ^ (i : ℕ)) := by
    change IsUnit (Matrix.vandermonde (u ∘ points))
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr
      (Matrix.det_vandermonde_ne_zero_iff.mpr (hu.comp hpoints))
  apply funext
  exact coefficients_eq_zero_of_fullRank_evaluation_packet
    (fun (i : Fin n) p => u p ^ (i : ℕ)) points hpacket c
    (fun row => ht ((Finset.equivFinOfCardEq hcard).symm row).2)

/-- Finite polynomial-weighted prime-series families are algebraically independent over the whole
filter coefficient field, including fields allowing infinitely many exceptional primes. -/
theorem algebraicIndependent_primePowers_over_filterField
    (F : Filter Nat.Primes) [F.NeBot] (hF : F ≤ cofinite)
    (u : Nat.Primes → ℂ) (hu : Function.Injective u) (n : ℕ) :
    AlgebraicIndependent (primeFilterCoefficientField F)
      (fun i : Fin n => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticOfPrimeColumn (fun p => u p ^ (i : ℕ)))) :=
  algebraicIndependent_primeColumns_over_filterField F _
    (filterCoefficientIndependent_powers F hF u hu n)

#print axioms algebraicIndependent_primePowers_over_filterField

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
