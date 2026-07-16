import GaloisForLFunctions.HTGeometry.PolynomialBalancedExactResidue

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

theorem shiftedAtomPatternKey_injective {M D q K : ℕ} :
    Function.Injective
      (shiftedAtomPatternKey q K : (Fin M → Fin (D + 1)) → ℕ →₀ ℕ) := by
  intro p r h
  apply atomPatternKey_injective
  exact Finsupp.mapDomain_injective windowShift_injective h

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
      simpa using hx
  rw [hempty]
  simp

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

theorem polynomialPatternCluster_moments
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
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
    have hceil3 : 3 ≤ Nat.ceil β := by
      by_contra hnot
      have hceil2 : Nat.ceil β ≤ 2 := by omega
      have : β ≤ (2 : ℝ) := Nat.ceil_le.mp hceil2
      linarith
    let i : Fin (Nat.ceil β - 2) := ⟨j - 2, by omega⟩
    have hsigfun : (fun i : Fin (Nat.ceil β - 2) =>
        polynomialPatternMoment p ((i : ℕ) + 2)) =
        fun i : Fin (Nat.ceil β - 2) =>
          polynomialPatternMoment r ((i : ℕ) + 2) :=
      List.ofFn_injective hsig
    have hi := congrFun hsigfun i
    have hij : (i : ℕ) + 2 = j := by dsimp [i]; omega
    simpa only [hij] using hi

theorem polynomialPatternCluster_prouhet_dvd
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
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
    polynomialPatternCluster_moments hβ S hS hcount hp hr j hj]
  simp

end

end GaloisForLFunctions
