import GaloisForLFunctions.RHTower.SuperzetaResolvent
import GaloisForLFunctions.RHTower.FunctionalEquationParity
import GaloisForLFunctions.HTGeometry.PowerSumTorelli

/-!
# Finite superzeta spectral-Torelli universality

For fixed finite cardinality, the complete additive superzeta resolvent trace is a faithful
coordinate on spectral multisets. Equality of traces gives equality of every power-sum
coefficient, Newton recursion gives equality of every elementary symmetric function, Vieta gives
equality of spectral polynomials, and spectral Torelli recovers the multiset.
-/

namespace GaloisForLFunctions

open PowerSeries
open scoped BigOperators

noncomputable section

/-- Equal finite superzeta resolvent traces force equal spectral multisets. This is the forward,
Torelli-faithfulness direction of the universality law. -/
theorem finiteSuperzetaResolventTrace_faithful {n : ℕ} (r t : Fin n → ℂ)
    (htrace :
      (∑ i, (PowerSeries.mk fun m => r i ^ m)) =
        ∑ i, (PowerSeries.mk fun m => t i ^ m)) :
    Multiset.map r Finset.univ.val = Multiset.map t Finset.univ.val := by
  have hpow : ∀ k : ℕ, ∑ i, r i ^ k = ∑ i, t i ^ k := by
    intro k
    have hk := congrArg (PowerSeries.coeff k) htrace
    simpa only [superzeta_coeff_eq_powerSum] using hk
  apply powerSum_torelli r t
  intro k
  rw [← Finset.sum_eq_multiset_sum Finset.univ,
    ← Finset.sum_eq_multiset_sum Finset.univ]
  exact hpow k

/-- **Finite superzeta spectral-Torelli universality law.** On finite spectra of fixed cardinality,
the additive trace of local resolvents is equal exactly when the underlying spectral multisets are
equal. Thus the full superzeta series loses ordering but no spectral multiplicity or location. -/
theorem finiteSuperzetaResolventTrace_eq_iff {n : ℕ} (r t : Fin n → ℂ) :
    (∑ i, (PowerSeries.mk fun m => r i ^ m)) =
        ∑ i, (PowerSeries.mk fun m => t i ^ m) ↔
      Multiset.map r Finset.univ.val = Multiset.map t Finset.univ.val := by
  constructor
  · exact finiteSuperzetaResolventTrace_faithful r t
  · intro h
    have hs := congrArg
      (fun s : Multiset ℂ =>
        (s.map fun a => (PowerSeries.mk fun m => a ^ m)).sum) h
    simp only [Multiset.map_map, Function.comp_def] at hs
    rw [← Finset.sum_eq_multiset_sum Finset.univ,
      ← Finset.sum_eq_multiset_sum Finset.univ] at hs
    simpa using hs

/-- **Finite superzeta parity-reflection universality law.** The complete finite superzeta trace
has vanishing odd coefficient sequence exactly when its spectral multiset is invariant under
negation. Functional-equation symmetry therefore is not merely sufficient for centered odd-moment
vanishing: at fixed finite cardinality, the vanished odd face recovers the symmetry. -/
theorem finiteSuperzetaOddCoefficients_vanish_iff_negationInvariant
    {n : ℕ} (r : Fin n → ℂ) :
    (∀ m : ℕ,
      PowerSeries.coeff (2 * m + 1)
        (∑ i, (PowerSeries.mk fun k => r i ^ k)) = 0) ↔
      (Multiset.map r Finset.univ.val).map (fun z => -z) =
        Multiset.map r Finset.univ.val := by
  constructor
  · intro hodd
    have htrace :
        (∑ i, (PowerSeries.mk fun m => r i ^ m)) =
          ∑ i, (PowerSeries.mk fun m => (-r i) ^ m) := by
      ext k
      simp only [superzeta_coeff_eq_powerSum]
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · simp [pow_mul]
      · have hj := hodd j
        rw [superzeta_coeff_eq_powerSum] at hj
        have hneg : ∑ i, (-r i) ^ (2 * j + 1) =
            -(∑ i, r i ^ (2 * j + 1)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          simp [pow_add, pow_mul]
        rw [hj, hneg, hj, neg_zero]
    have hmult := finiteSuperzetaResolventTrace_faithful r (fun i => -r i) htrace
    simpa [Multiset.map_map, Function.comp_def] using hmult.symm
  · intro hs m
    rw [superzeta_coeff_eq_powerSum]
    have hm := fe_odd_moment_vanish (Multiset.map r Finset.univ.val) hs m
    simp only [Multiset.map_map, Function.comp_def] at hm
    rw [← Finset.sum_eq_multiset_sum Finset.univ] at hm
    simpa using hm

/-- Sharp finite threshold: only odd coefficient orders at most the number of spectral points are
needed to recover negation symmetry. -/
theorem finiteSuperzetaFirstOddCoefficients_vanish_iff_negationInvariant
    {n : ℕ} (r : Fin n → ℂ) :
    (∀ m : ℕ, 2 * m + 1 ≤ n →
      PowerSeries.coeff (2 * m + 1)
        (∑ i, (PowerSeries.mk fun k => r i ^ k)) = 0) ↔
      (Multiset.map r Finset.univ.val).map (fun z => -z) =
        Multiset.map r Finset.univ.val := by
  constructor
  · intro hodd
    have hpow : ∀ k, k ≤ n →
        ∑ i, r i ^ k = ∑ i, (-r i) ^ k := by
      intro k hk
      obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
      · simp [pow_mul]
      · have hj := hodd j hk
        rw [superzeta_coeff_eq_powerSum] at hj
        have hneg : ∑ i, (-r i) ^ (2 * j + 1) =
            -(∑ i, r i ^ (2 * j + 1)) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          simp [pow_add, pow_mul]
        rw [hj, hneg, hj, neg_zero]
    have hmult := powerSum_torelli_finite r (fun i => -r i) hpow
    simpa [Multiset.map_map, Function.comp_def] using hmult.symm
  · intro hs m hmle
    rw [superzeta_coeff_eq_powerSum]
    have hm := fe_odd_moment_vanish (Multiset.map r Finset.univ.val) hs m
    simp only [Multiset.map_map, Function.comp_def] at hm
    rw [← Finset.sum_eq_multiset_sum Finset.univ] at hm
    simpa using hm

/-- Literal functional-equation chart of the parity-reflection law. Vanishing of every odd
coefficient of the trace centered at `1/2` is equivalent to invariance of the original spectral
multiset under `ρ ↦ 1 - ρ`. -/
theorem finiteCenteredSuperzetaOddCoefficients_vanish_iff_reflectionInvariant
    {n : ℕ} (rho : Fin n → ℂ) :
    (∀ m : ℕ,
      PowerSeries.coeff (2 * m + 1)
        (∑ i, (PowerSeries.mk fun k => (rho i - 1 / 2) ^ k)) = 0) ↔
      (Multiset.map rho Finset.univ.val).map (fun z => 1 - z) =
        Multiset.map rho Finset.univ.val := by
  rw [finiteSuperzetaOddCoefficients_vanish_iff_negationInvariant]
  constructor
  · intro h
    have hm := congrArg
      (Multiset.map (fun z : ℂ => z + 1 / 2)) h
    simp only [Multiset.map_map, Function.comp_def] at hm
    have hleft : (fun x => -(rho x - 1 / 2) + 1 / 2) =
        (fun x => 1 - rho x) := by funext x; ring
    have hright : (fun x => rho x - 1 / 2 + 1 / 2) = rho := by
      funext x
      ring
    rw [hleft, hright] at hm
    simpa only [Multiset.map_map, Function.comp_def] using hm
  · intro h
    have hm := congrArg
      (Multiset.map (fun z : ℂ => z - 1 / 2)) h
    simp only [Multiset.map_map, Function.comp_def] at hm
    have hleft : (fun x => 1 - rho x - 1 / 2) =
        (fun x => -(rho x - 1 / 2)) := by funext x; ring
    rw [hleft] at hm
    simpa only [Multiset.map_map, Function.comp_def] using hm

/-- Sharp functional-equation chart: centered odd superzeta coefficients only through order `n`
already recover reflection invariance of an `n`-point spectrum. -/
theorem finiteCenteredSuperzetaFirstOddCoefficients_vanish_iff_reflectionInvariant
    {n : ℕ} (rho : Fin n → ℂ) :
    (∀ m : ℕ, 2 * m + 1 ≤ n →
      PowerSeries.coeff (2 * m + 1)
        (∑ i, (PowerSeries.mk fun k => (rho i - 1 / 2) ^ k)) = 0) ↔
      (Multiset.map rho Finset.univ.val).map (fun z => 1 - z) =
        Multiset.map rho Finset.univ.val := by
  rw [finiteSuperzetaFirstOddCoefficients_vanish_iff_negationInvariant]
  constructor
  · intro h
    have hm := congrArg
      (Multiset.map (fun z : ℂ => z + 1 / 2)) h
    simp only [Multiset.map_map, Function.comp_def] at hm
    have hleft : (fun x => -(rho x - 1 / 2) + 1 / 2) =
        (fun x => 1 - rho x) := by funext x; ring
    have hright : (fun x => rho x - 1 / 2 + 1 / 2) = rho := by
      funext x
      ring
    rw [hleft, hright] at hm
    simpa only [Multiset.map_map, Function.comp_def] using hm
  · intro h
    have hm := congrArg
      (Multiset.map (fun z : ℂ => z - 1 / 2)) h
    simp only [Multiset.map_map, Function.comp_def] at hm
    have hleft : (fun x => 1 - rho x - 1 / 2) =
        (fun x => -(rho x - 1 / 2)) := by funext x; ring
    rw [hleft] at hm
    simpa only [Multiset.map_map, Function.comp_def] using hm

end

end GaloisForLFunctions
