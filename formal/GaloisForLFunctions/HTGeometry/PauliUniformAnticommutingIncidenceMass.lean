import GaloisForLFunctions.HTGeometry.TwoLocalPauliExactIncidence

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev boundedLocalPauliLabel (n q : ℕ) :=
  {Q : Fin n → Option (Fin 3) // Q ∈ nonidentityPauliWords n q}

def pauliAnticommutingIncidenceMass
    {n q : ℕ} (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (Q : boundedLocalPauliLabel n q) : ℝ :=
  ∑ P : NonzeroPauliCharacter (Fin n),
    if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0

theorem fixedPauli_mass_mul_card_le_anticommuting_sum
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P)
    (P : NonzeroPauliCharacter (Fin n)) :
    ((n - 1 : ℕ) : ℝ) * mass P ≤
      ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
  let S := (nonidentityPauliWords n q).filter fun Q =>
    finitePauliConjugationSign Q P.1 = -1
  have hcard : n - 1 ≤ S.card :=
    card_filter_twoLocalPauli_anticommuting_ge hq P
  have hcardR : ((n - 1 : ℕ) : ℝ) ≤ S.card := by exact_mod_cast hcard
  calc
    ((n - 1 : ℕ) : ℝ) * mass P ≤ (S.card : ℝ) * mass P :=
      mul_le_mul_of_nonneg_right hcardR (hmass P)
    _ = ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      have hsub :
          (∑ Q ∈ nonidentityPauliWords n q,
            if finitePauliConjugationSign Q P.1 = -1 then mass P else 0) =
          ∑ Q : boundedLocalPauliLabel n q,
            if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
        exact Finset.sum_subtype (nonidentityPauliWords n q) (by simp)
          (fun Q => if finitePauliConjugationSign Q P.1 = -1 then mass P else 0)
      rw [← hsub, ← Finset.sum_filter]
      simp [S]

/-- Every non-scalar Pauli mass profile has at least `n-1` times its total
mass in the complete bounded-local anticommutation incidence. -/
theorem total_pauliAnticommutingIncidenceMass_ge
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P) :
    ((n - 1 : ℕ) : ℝ) * ∑ P, mass P ≤
      ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
  rw [Finset.mul_sum]
  calc
    (∑ P, ((n - 1 : ℕ) : ℝ) * mass P) ≤
        ∑ P, ∑ Q : boundedLocalPauliLabel n q,
          if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      exact Finset.sum_le_sum fun P _ =>
        fixedPauli_mass_mul_card_le_anticommuting_sum hq mass hmass P
    _ = ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
      rw [Finset.sum_comm]
      rfl

theorem fixedPauli_boundaryMass_le_anticommuting_sum
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P)
    (P : NonzeroPauliCharacter (Fin n)) :
    ((pauliWeight P.1 * (n - pauliWeight P.1) : ℕ) : ℝ) * mass P ≤
      ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
  let S := (nonidentityPauliWords n q).filter fun Q =>
    finitePauliConjugationSign Q P.1 = -1
  have hcard : pauliWeight P.1 * (n - pauliWeight P.1) ≤ S.card :=
    card_filter_twoLocalPauli_anticommuting_ge_boundary hq P
  have hcardR :
      ((pauliWeight P.1 * (n - pauliWeight P.1) : ℕ) : ℝ) ≤ S.card := by
    exact_mod_cast hcard
  calc
    ((pauliWeight P.1 * (n - pauliWeight P.1) : ℕ) : ℝ) * mass P ≤
        (S.card : ℝ) * mass P :=
      mul_le_mul_of_nonneg_right hcardR (hmass P)
    _ = ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      have hsub :
          (∑ Q ∈ nonidentityPauliWords n q,
            if finitePauliConjugationSign Q P.1 = -1 then mass P else 0) =
          ∑ Q : boundedLocalPauliLabel n q,
            if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
        exact Finset.sum_subtype (nonidentityPauliWords n q) (by simp)
          (fun Q => if finitePauliConjugationSign Q P.1 = -1 then mass P else 0)
      rw [← hsub, ← Finset.sum_filter]
      simp [S]

/-- Support-boundary refinement.  Incidence mass controls the Pauli-weighted
isoperimetric moment `weight * (n-weight)`, which is quadratic for extensive
Pauli support and vanishes only at the two boundary weights. -/
theorem total_pauliAnticommutingIncidenceMass_ge_boundaryMoment
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P) :
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((pauliWeight P.1 * (n - pauliWeight P.1) : ℕ) : ℝ) * mass P) ≤
      ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
  calc
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((pauliWeight P.1 * (n - pauliWeight P.1) : ℕ) : ℝ) * mass P) ≤
      ∑ P, ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      exact Finset.sum_le_sum fun P _ =>
        fixedPauli_boundaryMass_le_anticommuting_sum hq mass hmass P
    _ = ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
      rw [Finset.sum_comm]
      rfl

theorem fixedPauli_activeWeightMass_le_anticommuting_sum
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P)
    (P : NonzeroPauliCharacter (Fin n)) :
    ((pauliWeight P.1 * (n - 1) : ℕ) : ℝ) * mass P ≤
      ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
  let S := (nonidentityPauliWords n q).filter fun Q =>
    finitePauliConjugationSign Q P.1 = -1
  have hcard : pauliWeight P.1 * (n - 1) ≤ S.card :=
    card_filter_twoLocalPauli_anticommuting_ge_activeWeight hq P
  have hcardR :
      ((pauliWeight P.1 * (n - 1) : ℕ) : ℝ) ≤ S.card := by
    exact_mod_cast hcard
  calc
    ((pauliWeight P.1 * (n - 1) : ℕ) : ℝ) * mass P ≤
        (S.card : ℝ) * mass P :=
      mul_le_mul_of_nonneg_right hcardR (hmass P)
    _ = ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      have hsub :
          (∑ Q ∈ nonidentityPauliWords n q,
            if finitePauliConjugationSign Q P.1 = -1 then mass P else 0) =
          ∑ Q : boundedLocalPauliLabel n q,
            if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
        exact Finset.sum_subtype (nonidentityPauliWords n q) (by simp)
          (fun Q => if finitePauliConjugationSign Q P.1 = -1 then mass P else 0)
      rw [← hsub, ← Finset.sum_filter]
      simp [S]

/-- Active-support refinement.  Incidence mass controls the moment
`weight * (n-1)`.  Unlike the support-boundary moment, this remains quadratic
for Pauli mass at full support. -/
theorem total_pauliAnticommutingIncidenceMass_ge_activeWeightMoment
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P) :
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((pauliWeight P.1 * (n - 1) : ℕ) : ℝ) * mass P) ≤
      ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
  calc
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((pauliWeight P.1 * (n - 1) : ℕ) : ℝ) * mass P) ≤
      ∑ P, ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      exact Finset.sum_le_sum fun P _ =>
        fixedPauli_activeWeightMass_le_anticommuting_sum hq mass hmass P
    _ = ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
      rw [Finset.sum_comm]
      rfl

theorem fixedPauli_enhancedActiveWeightMass_le_anticommuting_sum
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P)
    (P : NonzeroPauliCharacter (Fin n)) :
    ((2 * pauliWeight P.1 * n : ℕ) : ℝ) * mass P ≤
      ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
  let S := (nonidentityPauliWords n q).filter fun Q =>
    finitePauliConjugationSign Q P.1 = -1
  have hcard : 2 * pauliWeight P.1 * n ≤ S.card :=
    card_filter_twoLocalPauli_anticommuting_ge_enhancedActiveWeight hq P
  have hcardR : ((2 * pauliWeight P.1 * n : ℕ) : ℝ) ≤ S.card := by
    exact_mod_cast hcard
  calc
    ((2 * pauliWeight P.1 * n : ℕ) : ℝ) * mass P ≤
        (S.card : ℝ) * mass P :=
      mul_le_mul_of_nonneg_right hcardR (hmass P)
    _ = ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      have hsub :
          (∑ Q ∈ nonidentityPauliWords n q,
            if finitePauliConjugationSign Q P.1 = -1 then mass P else 0) =
          ∑ Q : boundedLocalPauliLabel n q,
            if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
        exact Finset.sum_subtype (nonidentityPauliWords n q) (by simp)
          (fun Q => if finitePauliConjugationSign Q P.1 = -1 then mass P else 0)
      rw [← hsub, ← Finset.sum_filter]
      simp [S]

/-- Enhanced active-support law.  Complete one/two-local incidence controls
the moment `2 * weight * n`, retaining both alternate axes and the one-site
directions. -/
theorem total_pauliAnticommutingIncidenceMass_ge_enhancedActiveWeightMoment
    {n q : ℕ} (hq : 2 ≤ q)
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P) :
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((2 * pauliWeight P.1 * n : ℕ) : ℝ) * mass P) ≤
      ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
  calc
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((2 * pauliWeight P.1 * n : ℕ) : ℝ) * mass P) ≤
      ∑ P, ∑ Q : boundedLocalPauliLabel n q,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      exact Finset.sum_le_sum fun P _ =>
        fixedPauli_enhancedActiveWeightMass_le_anticommuting_sum hq mass hmass P
    _ = ∑ Q : boundedLocalPauliLabel n q,
        pauliAnticommutingIncidenceMass mass Q := by
      rw [Finset.sum_comm]
      rfl

/-- Exact fixed-target incidence identity.  No positivity premise is needed:
the complete two-local filter contains exactly `2w(3n-2w)` copies of the
target's assigned mass. -/
theorem fixedPauli_fullWeightPolynomialMass_eq_anticommuting_sum
    {n : ℕ}
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (P : NonzeroPauliCharacter (Fin n)) :
    ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) *
        mass P =
      ∑ Q : boundedLocalPauliLabel n 2,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
  let S := (nonidentityPauliWords n 2).filter fun Q =>
    finitePauliConjugationSign Q P.1 = -1
  have hcard :
      S.card = 2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) :=
    card_filter_twoLocalPauli_anticommuting_eq_fullWeightPolynomial P
  have hcardR :
      (S.card : ℝ) =
        ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  calc
    ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) *
        mass P = (S.card : ℝ) * mass P := by rw [hcardR]
    _ = ∑ Q : boundedLocalPauliLabel n 2,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      have hsub :
          (∑ Q ∈ nonidentityPauliWords n 2,
            if finitePauliConjugationSign Q P.1 = -1 then mass P else 0) =
          ∑ Q : boundedLocalPauliLabel n 2,
            if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
        exact Finset.sum_subtype (nonidentityPauliWords n 2) (by simp)
          (fun Q => if finitePauliConjugationSign Q P.1 = -1 then mass P else 0)
      rw [← hsub, ← Finset.sum_filter]
      simp [S]

theorem fixedPauli_fullWeightPolynomialMass_le_anticommuting_sum
    {n : ℕ}
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (_hmass : ∀ P, 0 ≤ mass P)
    (P : NonzeroPauliCharacter (Fin n)) :
    ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) *
        mass P ≤
      ∑ Q : boundedLocalPauliLabel n 2,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
  rw [← fixedPauli_fullWeightPolynomialMass_eq_anticommuting_sum mass P]

/-- Exact total incidence moment.  Summing over targets preserves every
source sheet and yields the full support polynomial with equality. -/
theorem total_pauliAnticommutingIncidenceMass_eq_fullWeightPolynomialMoment
    {n : ℕ}
    (mass : NonzeroPauliCharacter (Fin n) → ℝ) :
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) *
          mass P) =
      ∑ Q : boundedLocalPauliLabel n 2,
        pauliAnticommutingIncidenceMass mass Q := by
  calc
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) *
          mass P) =
      ∑ P, ∑ Q : boundedLocalPauliLabel n 2,
        if finitePauliConjugationSign Q.1 P.1 = -1 then mass P else 0 := by
      apply Finset.sum_congr rfl
      intro P _
      exact fixedPauli_fullWeightPolynomialMass_eq_anticommuting_sum mass P
    _ = ∑ Q : boundedLocalPauliLabel n 2,
        pauliAnticommutingIncidenceMass mass Q := by
      rw [Finset.sum_comm]
      rfl

/-- Full Pauli-weight polynomial incidence law.  Weight `w` contributes
`2w(3n-2w)`, including every active--active direction and all three axes on
active--inactive pairs. -/
theorem total_pauliAnticommutingIncidenceMass_ge_fullWeightPolynomialMoment
    {n : ℕ}
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (_hmass : ∀ P, 0 ≤ mass P) :
    (∑ P : NonzeroPauliCharacter (Fin n),
        ((2 * pauliWeight P.1 * (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) *
          mass P) ≤
      ∑ Q : boundedLocalPauliLabel n 2,
        pauliAnticommutingIncidenceMass mass Q := by
  rw [total_pauliAnticommutingIncidenceMass_eq_fullWeightPolynomialMoment mass]

/-- Sharp worst-weight corollary of the full polynomial law.  Every
non-scalar Pauli mass profile pays at least `6n-4` two-local incidence per
unit mass; weight one is the extremal sector. -/
theorem total_pauliAnticommutingIncidenceMass_ge_sixNSubFour
    {n : ℕ}
    (mass : NonzeroPauliCharacter (Fin n) → ℝ)
    (hmass : ∀ P, 0 ≤ mass P) :
    ((6 * n - 4 : ℕ) : ℝ) * ∑ P, mass P ≤
      ∑ Q : boundedLocalPauliLabel n 2,
        pauliAnticommutingIncidenceMass mass Q := by
  rw [Finset.mul_sum]
  calc
    (∑ P, ((6 * n - 4 : ℕ) : ℝ) * mass P) ≤
      ∑ P, ((2 * pauliWeight P.1 *
          (3 * n - 2 * pauliWeight P.1) : ℕ) : ℝ) * mass P := by
      apply Finset.sum_le_sum
      intro P _
      apply mul_le_mul_of_nonneg_right _ (hmass P)
      exact_mod_cast
        six_mul_qubitCount_sub_four_le_fullWeightPolynomial P
    _ ≤ ∑ Q : boundedLocalPauliLabel n 2,
        pauliAnticommutingIncidenceMass mass Q :=
      total_pauliAnticommutingIncidenceMass_ge_fullWeightPolynomialMoment
        mass hmass

end

end GaloisForLFunctions.HTGeometry
