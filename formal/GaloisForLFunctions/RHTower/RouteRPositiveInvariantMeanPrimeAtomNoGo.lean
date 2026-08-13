import GaloisForLFunctions.RHTower.RouteRClosedPositiveCoinvariantCompletionNoGo
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Route R positive invariant means erase every localized prime-orbit atom

Each nontrivial rational prime-dilation orbit is a bilateral copy of `ℤ`.
This file realizes its bounded coefficient algebra as bounded continuous real
functions on the discrete integer orbit and proves the C26 obstruction on the
literal coordinate atoms.

The proof needs less than positivity: every bounded linear functional invariant
under all integer translations kills every coordinate atom.  The sum of `N`
distinct atoms still has sup norm one, whereas invariance would make its value
`N` times the value of one atom.  Thus a positive invariant mean may exist only
after erasing all localized prime provenance.
-/

open Set
open scoped BoundedContinuousFunction

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Bounded coefficient algebra on one actual bilateral prime-dilation orbit. -/
abbrev RouteRPrimeOrbitBoundedCoefficients := ℤ →ᵇ ℝ

/-- Localized coefficient at depth `n` in one prime orbit. -/
def routeRPrimeOrbitAtom (n : ℤ) : RouteRPrimeOrbitBoundedCoefficients :=
  BoundedContinuousFunction.indicator ({n} : Set ℤ) (by simp)

/-- Pullback by integer translation on the bilateral orbit. -/
def routeRPrimeOrbitTranslation (k : ℤ)
    (f : RouteRPrimeOrbitBoundedCoefficients) :
    RouteRPrimeOrbitBoundedCoefficients :=
  f.compContinuous ⟨fun n => n + k, continuous_of_discreteTopology⟩

/-- Translation carries the origin atom to every orbit atom. -/
theorem routeRPrimeOrbitTranslation_neg_atom_zero (n : ℤ) :
    routeRPrimeOrbitTranslation (-n) (routeRPrimeOrbitAtom 0) =
      routeRPrimeOrbitAtom n := by
  ext x
  simp only [routeRPrimeOrbitTranslation,
    BoundedContinuousFunction.compContinuous_apply, routeRPrimeOrbitAtom,
    BoundedContinuousFunction.indicator_apply, Set.indicator,
    Set.mem_singleton_iff]
  change (if x + -n = 0 then (1 : ℝ) else 0) = if x = n then 1 else 0
  by_cases h : x = n
  · subst h
    simp
  · have hsub : x + -n ≠ 0 := by omega
    simp [h, hsub]

/-- First `N` localized atoms in one prime orbit. -/
def routeRPrimeOrbitFinitePacket (N : ℕ) :
    RouteRPrimeOrbitBoundedCoefficients :=
  ∑ n ∈ Finset.range N, routeRPrimeOrbitAtom (n : ℤ)

/-- Disjoint coordinate packets retain sup norm at most one, independently of
their length. -/
theorem norm_routeRPrimeOrbitFinitePacket_le_one (N : ℕ) :
    ‖routeRPrimeOrbitFinitePacket N‖ ≤ 1 := by
  rw [BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)]
  intro x
  have happly :
      routeRPrimeOrbitFinitePacket N x =
        ∑ n ∈ Finset.range N, routeRPrimeOrbitAtom (n : ℤ) x := by
    simp [routeRPrimeOrbitFinitePacket]
  rw [happly]
  simp only [routeRPrimeOrbitAtom,
    BoundedContinuousFunction.indicator_apply]
  by_cases hx : ∃ n ∈ Finset.range N, (n : ℤ) = x
  · obtain ⟨n, hn, rfl⟩ := hx
    rw [Finset.sum_eq_single n]
    · simp
    · intro m hm hmn
      simp only [Set.indicator, Set.mem_singleton_iff]
      split_ifs with h
      · exact (hmn (Int.ofNat.inj h.symm)).elim
      · rfl
    · intro hnnot
      exact (hnnot hn).elim
  · have hzero : ∀ n ∈ Finset.range N,
        ({(n : ℤ)} : Set ℤ).indicator (1 : ℤ → ℝ) x = 0 := by
      intro n hn
      simp only [Set.indicator, Set.mem_singleton_iff]
      split_ifs with h
      · exact (hx ⟨n, hn, h.symm⟩).elim
      · rfl
    have hsum :
        (∑ n ∈ Finset.range N,
          ({(n : ℤ)} : Set ℤ).indicator (1 : ℤ → ℝ) x) = 0 :=
      Finset.sum_eq_zero hzero
    rw [hsum]
    norm_num

/-- C26 core: bounded translation invariance alone erases the origin atom.
Positivity and normalization cannot restore it. -/
theorem routeR_translationInvariantBoundedFunctional_atom_zero
    (L : RouteRPrimeOrbitBoundedCoefficients →L[ℝ] ℝ)
    (hinvariant : ∀ k f,
      L (routeRPrimeOrbitTranslation k f) = L f) :
    L (routeRPrimeOrbitAtom 0) = 0 := by
  have hatom (n : ℕ) :
      L (routeRPrimeOrbitAtom (n : ℤ)) =
        L (routeRPrimeOrbitAtom 0) := by
    rw [← routeRPrimeOrbitTranslation_neg_atom_zero (n : ℤ)]
    exact hinvariant (-(n : ℤ)) (routeRPrimeOrbitAtom 0)
  have hpacket (N : ℕ) :
      L (routeRPrimeOrbitFinitePacket N) =
        (N : ℝ) * L (routeRPrimeOrbitAtom 0) := by
    calc
      L (routeRPrimeOrbitFinitePacket N) =
          ∑ n ∈ Finset.range N, L (routeRPrimeOrbitAtom (n : ℤ)) := by
            simp [routeRPrimeOrbitFinitePacket]
      _ = ∑ _n ∈ Finset.range N, L (routeRPrimeOrbitAtom 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hatom n
      _ = (N : ℝ) * L (routeRPrimeOrbitAtom 0) := by simp
  by_contra hne
  have hcpos : 0 < ‖L (routeRPrimeOrbitAtom 0)‖ := norm_pos_iff.mpr hne
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (‖L‖ / ‖L (routeRPrimeOrbitAtom 0)‖)
  have hlarge :
      ‖L‖ < (N : ℝ) * ‖L (routeRPrimeOrbitAtom 0)‖ := by
    rw [div_lt_iff₀ hcpos] at hN
    simpa [mul_comm] using hN
  have hbound : ‖L (routeRPrimeOrbitFinitePacket N)‖ ≤ ‖L‖ := by
    calc
      ‖L (routeRPrimeOrbitFinitePacket N)‖ ≤
          ‖L‖ * ‖routeRPrimeOrbitFinitePacket N‖ := L.le_opNorm _
      _ ≤ ‖L‖ * 1 := mul_le_mul_of_nonneg_left
        (norm_routeRPrimeOrbitFinitePacket_le_one N) (norm_nonneg L)
      _ = ‖L‖ := mul_one _
  rw [hpacket, norm_mul, Real.norm_natCast] at hbound
  exact (not_lt_of_ge hbound) hlarge

/-- Every localized atom, not only the chosen origin, is erased. -/
theorem routeR_translationInvariantBoundedFunctional_all_atoms_zero
    (L : RouteRPrimeOrbitBoundedCoefficients →L[ℝ] ℝ)
    (hinvariant : ∀ k f,
      L (routeRPrimeOrbitTranslation k f) = L f)
    (n : ℤ) :
    L (routeRPrimeOrbitAtom n) = 0 := by
  rw [← routeRPrimeOrbitTranslation_neg_atom_zero n,
    hinvariant (-n) (routeRPrimeOrbitAtom 0),
    routeR_translationInvariantBoundedFunctional_atom_zero L hinvariant]

/-- A normalized positive invariant mean is allowed, but coefficient
faithfulness on a localized ordinary-prime atom is impossible. -/
structure RouteRPositiveInvariantMeanRetainingPrimeAtom where
  mean : RouteRPrimeOrbitBoundedCoefficients →L[ℝ] ℝ
  positive : ∀ f, (∀ n, 0 ≤ f n) → 0 ≤ mean f
  normalized : mean 1 = 1
  translation_invariant : ∀ k f,
    mean (routeRPrimeOrbitTranslation k f) = mean f
  retained_atom : mean (routeRPrimeOrbitAtom 0) ≠ 0

/-- No positive invariant mean can retain localized prime provenance. -/
theorem routeR_no_positiveInvariantMeanRetainingPrimeAtom :
    ¬ Nonempty RouteRPositiveInvariantMeanRetainingPrimeAtom := by
  rintro ⟨M⟩
  exact M.retained_atom
    (routeR_translationInvariantBoundedFunctional_atom_zero
      M.mean M.translation_invariant)

end GaloisForLFunctions.RHTower
