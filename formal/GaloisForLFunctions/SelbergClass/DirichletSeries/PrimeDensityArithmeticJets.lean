import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeFilterGeneralJacobian
import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeColorInfiniteJets
import GaloisForLFunctions.HTGeometry.HelsonZetaJetIndependence

/-!
# Full arithmetic shift–jet families over the density coefficient field

Exponential-polynomial rigidity only needs the prime coefficients to be nonzero on a set that
survives the prime filter. Combined with the general prime-value Jacobian criterion, this proves
independence for full arithmetic functions, with arbitrary composite coefficients. In particular,
each of the zeta, Möbius, and Liouville streams retains all natural shifts and logarithmic orders
over the density-zero prime coefficient field.
-/

namespace GaloisForLFunctions.SelbergClass.DirichletSeries

open ArithmeticFunction HTGeometry Filter
open scoped Classical

noncomputable section

/-- A phase nonzero on a frequent prime set preserves every finite shift–jet rectangle. -/
theorem filterCoefficientIndependent_phaseShiftedRotatedJets
    {A : Type*} [Fintype A] [DecidableEq A]
    (F : Filter Nat.Primes) (hF : F ≤ cofinite)
    (phase : Nat.Primes → ℂ) (hphase : ∃ᶠ p in F, phase p ≠ 0)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    FilterCoefficientIndependent F
      (fun ak : A × Fin (m + 1) => fun p =>
        phase p * primeShiftFactor (alpha ak.1) p * rotatedPrimeLogClock p ^ (ak.2 : ℕ)) := by
  intro c hc
  let U : Set Nat.Primes := {p | phase p ≠ 0 ∧
    ∑ ak : A × Fin (m + 1), c ak *
      (phase p * primeShiftFactor (alpha ak.1) p * rotatedPrimeLogClock p ^ (ak.2 : ℕ)) = 0}
  have hU : U.Infinite := by
    intro hfinite
    have hn : ∀ᶠ p in F, p ∉ U := hF (eventually_cofinite.mpr (by simpa using hfinite))
    apply hphase
    filter_upwards [hc, hn] with p hp hn hnonzero
    exact hn ⟨hnonzero, hp⟩
  let d : A × Fin (m + 1) → ℂ := fun ak => c ak * Complex.I ^ (ak.2 : ℕ)
  have hd : d = 0 := by
    apply primeFactorClockFiberIndependent alpha hdistinct m U hU d
    apply Set.finite_empty.subset
    intro p hp
    obtain ⟨⟨hphasep, hzero⟩, hne⟩ := hp
    apply hne
    have heq :
        (∑ ak : A × Fin (m + 1), c ak *
          (phase p * primeShiftFactor (alpha ak.1) p * rotatedPrimeLogClock p ^ (ak.2 : ℕ))) =
        phase p * ∑ ak, d ak * primeShiftFactor (alpha ak.1) p * primeLogClock p ^ (ak.2 : ℕ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ak _
      simp only [d, rotatedPrimeLogClock, mul_pow]
      ring
    rw [heq] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hphasep
  funext ak
  exact (mul_eq_zero.mp (congrFun hd ak)).resolve_right (pow_ne_zero _ Complex.I_ne_zero)

/-- The full arithmetic shift–jet rectangle is independent when its nonzero prime coefficients
survive the filter. No restriction is imposed on composite coefficients. -/
theorem algebraicIndependent_arithmeticShiftedRotatedJets_over_filterField
    {A : Type*} [Fintype A] [DecidableEq A]
    (F : Filter Nat.Primes) (hF : F ≤ cofinite)
    (f : ArithmeticFunction ℂ) (hf : ∃ᶠ (p : Nat.Primes) in F, f (p : ℕ) ≠ 0)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) (m : ℕ) :
    AlgebraicIndependent (primeFilterCoefficientField F)
      (fun ak : A × Fin (m + 1) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticShiftedRotatedJet f (alpha ak.1) ak.2)) := by
  apply algebraicIndependent_fractionArithmetic_of_filterPrimeValues
  simpa only [arithmeticShiftedRotatedJet_apply_prime] using
    filterCoefficientIndependent_phaseShiftedRotatedJets F hF
      (fun p => f (p : ℕ)) hf alpha hdistinct m

/-- All natural shifts and logarithmic orders of a full arithmetic stream are jointly
independent over the density coefficient field whenever its nonzero prime coefficients are
supported on a set that does not have prime density zero. -/
theorem algebraicIndependent_arithmeticNaturalShiftedJets_over_densityField
    (f : ArithmeticFunction ℂ)
    (hf : ¬ PrimeWindowDensityZero primeCountingWindow {p : Nat.Primes | f (p : ℕ) ≠ 0}) :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun q : ℕ × ℕ => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticShiftedRotatedJet f q.1 q.2)) := by
  let F := primeWindowDensityFilter primeCountingWindow
  have hfreq : ∃ᶠ (p : Nat.Primes) in F, f (p : ℕ) ≠ 0 := by
    change ¬ PrimeWindowDensityZero primeCountingWindow {p : Nat.Primes | ¬ (f (p : ℕ) ≠ 0)}ᶜ
    simpa only [Set.compl_setOf, not_not] using hf
  have hfull : AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun q : Unit × (ℕ × ℕ) =>
        algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
          (arithmeticShiftedRotatedJet f q.2.1 q.2.2)) := by
    rw [algebraicIndependent_natPair_iff_finiteSquares]
    intro n
    have hfin := algebraicIndependent_arithmeticShiftedRotatedJets_over_filterField F
      (primeWindowDensityFilter_le_cofinite _ primeCountingWindow_card_tendsto)
      f hfreq (fun a : Fin (n + 1) => (a : ℕ)) (primeNaturalShift_real_injective n) n
    refine hfin.comp (fun q : Unit × (Fin (n + 1) × Fin (n + 1)) => q.2) ?_
    intro q r hqr
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · exact hqr
  exact hfull.comp (fun q : ℕ × ℕ => ((), q))
    (fun _ _ h => congrArg (fun q : Unit × (ℕ × ℕ) => q.2) h)

/-- A stream nonzero at every prime has non-negligible prime support in the standard windows. -/
theorem not_densityZero_nonzero_primes
    (f : ArithmeticFunction ℂ) (hf : ∀ p : Nat.Primes, f (p : ℕ) ≠ 0) :
    ¬ PrimeWindowDensityZero primeCountingWindow {p : Nat.Primes | f (p : ℕ) ≠ 0} := by
  haveI := primeWindowDensityFilter_neBot primeCountingWindow primeCountingWindow_card_tendsto
  have hfreq : ∃ᶠ (p : Nat.Primes) in primeWindowDensityFilter primeCountingWindow,
      f (p : ℕ) ≠ 0 :=
    Frequently.of_forall hf
  change ¬ PrimeWindowDensityZero primeCountingWindow {p : Nat.Primes | ¬ (f (p : ℕ) ≠ 0)}ᶜ at hfreq
  simpa only [Set.compl_setOf, not_not] using hfreq

/-- The entire natural-shift/derivative family of zeta coefficients is independent over the
density-zero prime coefficient field. -/
theorem algebraicIndependent_zetaNaturalShiftedJets_over_densityField :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun q : ℕ × ℕ => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticShiftedRotatedJet (zeta : ArithmeticFunction ℂ) q.1 q.2)) := by
  apply algebraicIndependent_arithmeticNaturalShiftedJets_over_densityField
  exact not_densityZero_nonzero_primes _ fun p => by simp [p.2.ne_zero]

/-- The corresponding complete family for Möbius coefficients is also independent. -/
theorem algebraicIndependent_moebiusNaturalShiftedJets_over_densityField :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun q : ℕ × ℕ => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticShiftedRotatedJet (moebius : ArithmeticFunction ℂ) q.1 q.2)) := by
  apply algebraicIndependent_arithmeticNaturalShiftedJets_over_densityField
  exact not_densityZero_nonzero_primes _ fun p => by simp [moebius_apply_prime p.2]

/-- The corresponding complete family for Liouville coefficients is also independent. -/
theorem algebraicIndependent_liouvilleNaturalShiftedJets_over_densityField :
    AlgebraicIndependent (primeDensityCoefficientField primeCountingWindow)
      (fun q : ℕ × ℕ => algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (arithmeticShiftedRotatedJet (liouville : ArithmeticFunction ℂ) q.1 q.2)) := by
  apply algebraicIndependent_arithmeticNaturalShiftedJets_over_densityField
  exact not_densityZero_nonzero_primes _ fun p => by
    simp [liouville, p.2.ne_zero, cardFactors_apply_prime p.2]

#print axioms algebraicIndependent_arithmeticNaturalShiftedJets_over_densityField
#print axioms algebraicIndependent_zetaNaturalShiftedJets_over_densityField
#print axioms algebraicIndependent_moebiusNaturalShiftedJets_over_densityField
#print axioms algebraicIndependent_liouvilleNaturalShiftedJets_over_densityField

end
end GaloisForLFunctions.SelbergClass.DirichletSeries
