import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaBottomFace

/-!
# Nonresonance of the external face lattice

The bottom-layer packet of the all-order hierarchy is the set of translates of the order-one
elliptic gamma by the external lattice shifted by the fixed half period `-(1 + tau_b)/2`.  Rational
independence of `1` and the periods makes every such shift nonresonant and separates distinct
shifts, which is exactly the hypothesis of the order-one packet theorem.

Both proofs use only *integer* coefficients: clearing the half period by a factor `2` leaves an
integral relation whose coefficient of `1` is odd.

* `PeriodsIntegrallyIndependent` — the standing genericity hypothesis;
* **`thetaTranslationNonresonant_faceShiftLattice_add_half`** — half-shifted lattice points are
  nonresonant;
* **`thetaTranslationNonresonant_faceShiftLattice_sub`** — distinct lattice points are separated.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `1` together with the periods admits no nontrivial integral relation.  This is the standing
genericity hypothesis of the card, written without rational casts. -/
def PeriodsIntegrallyIndependent (τ : ι → ℂ) : Prop :=
  ∀ (m : ℤ) (n : ι → ℤ), (m : ℂ) + ∑ i, (n i : ℂ) * τ i = 0 → m = 0 ∧ ∀ i, n i = 0

/-- **Half-shifted lattice points are nonresonant.**  Doubling the relation clears the half period
and leaves an integral relation whose coefficient of `1` is odd. -/
theorem thetaTranslationNonresonant_faceShiftLattice_add_half
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) (J : Finset ι) (a b : ι)
    {g : ℂ} (hg : g ∈ faceShiftLattice τ J) :
    ThetaTranslationNonresonant (τ b) (τ a) (g + -(1 + τ b) / 2) := by
  classical
  rintro ⟨p, q, r, hpqr⟩
  obtain ⟨n, -, rfl⟩ := hg
  have hterm : ∀ i : ι,
      ((2 * n i - (if i = b then 2 * q + 1 else 0) - (if i = a then 2 * r else 0) : ℤ) : ℂ) *
          τ i =
        2 * ((n i : ℂ) * τ i) - (if i = b then ((2 * q + 1 : ℤ) : ℂ) * τ i else 0) -
          (if i = a then ((2 * r : ℤ) : ℂ) * τ i else 0) := by
    intro i
    split_ifs <;> push_cast <;> ring
  have hsum : ∑ i, ((2 * n i - (if i = b then 2 * q + 1 else 0) -
        (if i = a then 2 * r else 0) : ℤ) : ℂ) * τ i =
      2 * (∑ i, (n i : ℂ) * τ i) - ((2 * q + 1 : ℤ) : ℂ) * τ b -
        ((2 * r : ℤ) : ℂ) * τ a := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq' Finset.univ b fun i => ((2 * q + 1 : ℤ) : ℂ) * τ i,
      Finset.sum_ite_eq' Finset.univ a fun i => ((2 * r : ℤ) : ℂ) * τ i]
    simp
  have hrel : ((-(2 * p + 1) : ℤ) : ℂ) +
      ∑ i, ((2 * n i - (if i = b then 2 * q + 1 else 0) -
        (if i = a then 2 * r else 0) : ℤ) : ℂ) * τ i = 0 := by
    rw [hsum]
    push_cast
    linear_combination 2 * hpqr
  obtain ⟨hm, -⟩ := hQ _ _ hrel
  omega

/-- **Distinct lattice points are separated.**  Their difference has no component along the two
surviving periods, so an integral relation forces the two points to coincide. -/
theorem thetaTranslationNonresonant_faceShiftLattice_sub
    (τ : ι → ℂ) (hQ : PeriodsIntegrallyIndependent τ) (J : Finset ι) {a b : ι}
    (haJ : a ∉ J) (hbJ : b ∉ J)
    {g g' : ℂ} (hg : g ∈ faceShiftLattice τ J) (hg' : g' ∈ faceShiftLattice τ J)
    (hne : g ≠ g') :
    ThetaTranslationNonresonant (τ b) (τ a) (g - g') := by
  classical
  rintro ⟨p, q, r, hpqr⟩
  obtain ⟨n, hn, rfl⟩ := hg
  obtain ⟨n', hn', rfl⟩ := hg'
  have hterm : ∀ i : ι,
      ((n i - n' i - (if i = b then q else 0) - (if i = a then r else 0) : ℤ) : ℂ) * τ i =
        (n i : ℂ) * τ i - (n' i : ℂ) * τ i - (if i = b then (q : ℂ) * τ i else 0) -
          (if i = a then (r : ℂ) * τ i else 0) := by
    intro i
    split_ifs <;> push_cast <;> ring
  have hsum : ∑ i, ((n i - n' i - (if i = b then q else 0) -
        (if i = a then r else 0) : ℤ) : ℂ) * τ i =
      (∑ i, (n i : ℂ) * τ i) - (∑ i, (n' i : ℂ) * τ i) - (q : ℂ) * τ b - (r : ℂ) * τ a := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ b fun i => (q : ℂ) * τ i,
      Finset.sum_ite_eq' Finset.univ a fun i => (r : ℂ) * τ i]
    simp
  have hrel : ((-p : ℤ) : ℂ) +
      ∑ i, ((n i - n' i - (if i = b then q else 0) -
        (if i = a then r else 0) : ℤ) : ℂ) * τ i = 0 := by
    rw [hsum]
    push_cast
    linear_combination hpqr
  obtain ⟨-, hcz⟩ := hQ _ _ hrel
  refine hne (Finset.sum_congr rfl fun i _ => ?_)
  have hci := hcz i
  by_cases hiJ : i ∈ J
  · have hib : i ≠ b := fun h => hbJ (h ▸ hiJ)
    have hia : i ≠ a := fun h => haJ (h ▸ hiJ)
    rw [if_neg hib, if_neg hia] at hci
    have hnn : n i = n' i := by omega
    rw [hnn]
  · rw [hn i hiJ, hn' i hiJ]

end

end GaloisForLFunctions
