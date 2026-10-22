import GaloisForLFunctions.HTGeometry.PolynomialBalancedExactResidue

/-!
# Active atoms of an algebraic differential relation and Prouhet locking of minimal clusters

If a complex power series `F` satisfies an algebraic differential equation
`Q(X, F, F', …, F⁽ⁿ⁾) = 0`, every coefficient `N` of the left side regroups into atoms `ν`
(multisets of coefficient indices) with weights `aevalWeight n N Q ν`; writing
`|coeff i F| = e^{-b i}` turns each atom product into `e^{-val_b(ν)}` times a unit phase. This module
restricts the resulting coefficient identity to active atoms (nonzero weight) and shows that two
patterns in the minimal signature cluster of the least-source class share all moments below `⌈β⌉`,
so their difference polynomial is divisible by `(X - 1)^{⌈β⌉}` (a Prouhet–Tarry–Escott type lock).

## Main results

- `shiftedAtomPatternKey_injective`: distinct patterns give distinct shifted multiplicity keys.
- `activeAevalAtoms`, `normalized_active_aeval_coefficient_identity`: for `F` satisfying the
  relation, `∑_{ν active} aevalWeight ν · e^{-(val_b(ν) - m)} · phase(ν) = 0`.
- `activeAevalWeight_mass_le`: the active weight mass is at most the total weight mass.
- `polynomialPatternCluster_moments`: two patterns in the minimal cluster of the least-source class
  have equal moments `m_j` for all `j < ⌈β⌉`.
- `polynomialPatternCluster_prouhet_dvd`: their difference polynomial is divisible by
  `(X - 1)^{⌈β⌉}`.

## Hypotheses

Unconditional. The coefficient identity assumes the relation `aeval (formalJets n F) Q = 0`; the
cluster results assume every pattern in `S` has total count `D`.
-/

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

/-- The shifted multiplicity key of a pattern determines the pattern. -/
theorem shiftedAtomPatternKey_injective {M D q K : ℕ} :
    Function.Injective
      (shiftedAtomPatternKey q K : (Fin M → Fin (D + 1)) → ℕ →₀ ℕ) := by
  intro p r h
  apply atomPatternKey_injective
  exact Finsupp.mapDomain_injective windowShift_injective h

/-- An atom key with nonzero weight is realized by some contributing index pair. -/
theorem mem_appearingAtoms_of_aevalWeight_ne_zero
    {n N : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} {ν : ℕ →₀ ℕ}
    (hw : aevalWeight n N Q ν ≠ 0) :
    ν ∈ (sigmaIdx n N Q).image (atomKeyOf n) := by
  classical
  by_contra hν
  apply hw
  rw [aevalWeight]
  have hempty : (sigmaIdx n N Q).filter (fun x => atomKeyOf n x = ν) = ∅ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxSigma, hkey⟩ := Finset.mem_filter.mp hx
      exact (hν (Finset.mem_image.mpr ⟨x, hxSigma, hkey⟩)).elim
    · intro hx
      simp at hx
  rw [hempty]
  simp

/-- Atom keys of coefficient `N` of `Q(X, F, …, F⁽ⁿ⁾)` that carry nonzero weight. -/
def activeAevalAtoms (n N : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    Finset (ℕ →₀ ℕ) :=
  ((sigmaIdx n N Q).image (atomKeyOf n)).filter fun ν =>
    aevalWeight n N Q ν ≠ 0

theorem mem_activeAevalAtoms
    {n N : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ} {ν : ℕ →₀ ℕ} :
    ν ∈ activeAevalAtoms n N Q ↔
      ν ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
        aevalWeight n N Q ν ≠ 0 := by
  simp [activeAevalAtoms]

/-- Assuming `aeval (formalJets n F) Q = 0`: for any `b` and shift `m`, the normalized coefficient
identity `∑ aevalWeight ν · e^{-(val_b(ν) - m)} · phase(ν) = 0` holds over active atoms only. -/
theorem normalized_active_aeval_coefficient_identity
    (n N : ℕ) (F : PowerSeries ℂ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) (b : ℕ → ℝ)
    (hrel : aeval (formalJets n F) Q = 0) (m : ℝ) :
    ∑ ν ∈ activeAevalAtoms n N Q,
        aevalWeight n N Q ν *
          (Real.exp (-(atomValuation b ν - m)) : ℂ) *
            normalizedAtomPhase F b ν = 0 := by
  have hfull := normalized_aeval_coefficient_identity n N F Q b hrel m
  rw [← hfull]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ν hνall hνnot
  have hwzero : aevalWeight n N Q ν = 0 := by
    by_contra hw
    exact hνnot (Finset.mem_filter.mpr ⟨hνall, hw⟩)
  rw [hwzero, zero_mul, zero_mul]

/-- The total weight norm over active atoms is at most that over all appearing atoms. -/
theorem activeAevalWeight_mass_le (n N : ℕ)
    (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    (∑ ν ∈ activeAevalAtoms n N Q, ‖aevalWeight n N Q ν‖) ≤
      ∑ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n), ‖aevalWeight n N Q ν‖ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun ν hν hnot => norm_nonneg _)

theorem sum_image_shiftedAtomPatternKey
    {M D q K : ℕ} (C : Finset (Fin M → Fin (D + 1)))
    (f : (ℕ →₀ ℕ) → ℂ) :
    ∑ ν ∈ C.image (shiftedAtomPatternKey q K), f ν =
      ∑ p ∈ C, f (shiftedAtomPatternKey q K p) := by
  rw [Finset.sum_image]
  intro p hp r hr hpr
  exact shiftedAtomPatternKey_injective hpr

/-- Assuming count `D` on `S`: two patterns in the minimal signature cluster of the least-source
class have equal moments `m_j` for every `j < ⌈β⌉`. -/
theorem polynomialPatternCluster_moments
    {β : ℝ} {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    {p r : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2)
      (polynomialPatternLeastSourceClass S hS)
      (polynomialPatternLeastSourceClass_nonempty S hS))
    (hr : r ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2)
      (polynomialPatternLeastSourceClass S hS)
      (polynomialPatternLeastSourceClass_nonempty S hS)) :
    ∀ j < Nat.ceil β,
      polynomialPatternMoment p j = polynomialPatternMoment r j := by
  intro j hj
  let T := polynomialPatternLeastSourceClass S hS
  let hT : T.Nonempty := polynomialPatternLeastSourceClass_nonempty S hS
  have hpT : p ∈ T := polynomialPatternMinimalCluster_subset T hT hp
  have hrT : r ∈ T := polynomialPatternMinimalCluster_subset T hT hr
  have hpS : p ∈ S := polynomialPatternLeastSourceClass_subset S hS hpT
  have hrS : r ∈ S := polynomialPatternLeastSourceClass_subset S hS hrT
  rcases lt_trichotomy j 1 with hj0 | hj1 | hj2
  · have : j = 0 := by omega
    subst j
    rw [polynomialPatternMoment_zero, polynomialPatternMoment_zero,
      hcount p hpS, hcount r hrS]
  · subst j
    rw [polynomialPatternMoment_one, polynomialPatternMoment_one]
    have hpSource := sourceSum_eq_of_mem_polynomialPatternLeastSourceClass hpT
    have hrSource := sourceSum_eq_of_mem_polynomialPatternLeastSourceClass hrT
    exact hpSource.trans hrSource.symm
  · have hsig : polynomialPatternSignature (Nat.ceil β - 2) p =
        polynomialPatternSignature (Nat.ceil β - 2) r := by
      rw [signature_eq_of_mem_polynomialPatternMinimalCluster hp,
        signature_eq_of_mem_polynomialPatternMinimalCluster hr]
    have hceil3 : 3 ≤ Nat.ceil β := by omega
    let i : Fin (Nat.ceil β - 2) := ⟨j - 2, by omega⟩
    have hsigfun : (fun i : Fin (Nat.ceil β - 2) =>
        polynomialPatternMoment p ((i : ℕ) + 2)) =
        fun i : Fin (Nat.ceil β - 2) =>
          polynomialPatternMoment r ((i : ℕ) + 2) :=
      List.ofFn_injective hsig
    have hi := congrFun hsigfun i
    have hij : (i : ℕ) + 2 = j := by dsimp [i]; omega
    simpa only [hij] using hi

/-- Prouhet lock: assuming count `D` on `S`, for two patterns in the minimal signature cluster of the
least-source class, `(X - 1)^{⌈β⌉}` divides their difference polynomial. -/
theorem polynomialPatternCluster_prouhet_dvd
    {β : ℝ} {M D : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty)
    (hcount : ∀ p ∈ S, (∑ r, (p r : ℕ)) = D)
    {p r : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2)
      (polynomialPatternLeastSourceClass S hS)
      (polynomialPatternLeastSourceClass_nonempty S hS))
    (hr : r ∈ polynomialPatternMinimalCluster
      (R := Nat.ceil β - 2)
      (polynomialPatternLeastSourceClass S hS)
      (polynomialPatternLeastSourceClass_nonempty S hS)) :
    (Polynomial.X - 1) ^ Nat.ceil β ∣ atomPatternDifferencePolynomial p r := by
  let T := polynomialPatternLeastSourceClass S hS
  let hT : T.Nonempty := polynomialPatternLeastSourceClass_nonempty S hS
  have hpS : p ∈ S := polynomialPatternLeastSourceClass_subset S hS
    (polynomialPatternMinimalCluster_subset T hT hp)
  have hrS : r ∈ S := polynomialPatternLeastSourceClass_subset S hS
    (polynomialPatternMinimalCluster_subset T hT hr)
  apply sub_one_pow_dvd_of_polynomialRealCoeff_moments
  intro j hj
  rw [stretchedMoment_atomPatternDifference p r (hcount p hpS) (hcount r hrS),
    polynomialPatternCluster_moments S hS hcount hp hr j hj]
  simp

end

end GaloisForLFunctions
