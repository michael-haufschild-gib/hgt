import GaloisForLFunctions.HTGeometry.PolynomialPatternSurvivors

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

theorem atomValuation_shiftedAtomPatternKey
    {β B : ℝ} {M D q K : ℕ} (p : Fin M → Fin (D + 1))
    (hKq : K ≤ q) :
    atomValuation (fun i => B * (i : ℝ) ^ β)
        (shiftedAtomPatternKey q K p) =
      B * polynomialPatternPowerValuation β p ((q : ℝ) - K) := by
  classical
  rw [atomValuation, shiftedAtomPatternKey_eq_sum,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun r : Fin M =>
        Finsupp.single (windowShift q K (r : ℕ)) (p r : ℕ))
      (h := fun i k => (k : ℝ) * (B * (i : ℝ) ^ β))]
  · rw [polynomialPatternPowerValuation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finsupp.sum_single_index]
    · have hcast : (windowShift q K (r : ℕ) : ℝ) =
          (q : ℝ) - K + (r : ℝ) := by
        rw [windowShift, Nat.cast_add, Nat.cast_sub hKq]
      rw [hcast]
      push_cast
      ring
    · simp
  · intro a
    simp
  · intro a b c
    push_cast
    ring

theorem polynomialPatternJetGroup_nonempty_of_weightPoly_ne_zero
    {n D K τ M : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {p : Fin M → Fin (D + 1)}
    (hpoly : polynomialPatternWeightPoly n D K τ Q p ≠ 0) :
    (polynomialPatternJetGroup n D K τ Q p).Nonempty := by
  classical
  by_contra hempty
  apply hpoly
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hatt : (polynomialPatternJetGroup n D K τ Q p).attach = ∅ := by
    rw [hempty]
    simp
  simp [polynomialPatternWeightPoly, hatt]

/-- The top-shift anchor gives the least possible source sum among every
bounded pattern whose grouped weight polynomial is nonzero. -/
theorem polynomialPattern_source_floor_of_survivor
    {n D K τ M : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = D →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    {p : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternSurvivors n D K τ Q M) :
    D * K + τ + magnitudeMaxJetOrder n Q ≤
      polynomialPatternSourceSum p + magnitudeShiftCode n Q anchor := by
  classical
  obtain ⟨m, hmGroup⟩ := polynomialPatternJetGroup_nonempty_of_weightPoly_ne_zero
    (polynomialPatternSurvivors_weightPoly_ne_zero hp)
  have hmSupport : m ∈ Q.support := (Finset.mem_filter.mp hmGroup).1
  have hmD : jetMonomialDegree n m = D :=
    ((Finset.mem_filter.mp hmGroup).2).1
  have helig := ((Finset.mem_filter.mp hmGroup).2).2
  have hcode := shiftCode_add_order Q hmSupport
  have hcodele := haMax m hmSupport hmD
  change polynomialPatternSourceSum p + m 0 =
    D * K + τ + jetMonomialOrder n m at helig
  change magnitudeShiftCode n Q m + jetMonomialOrder n m =
    magnitudeMaxJetOrder n Q + m 0 at hcode
  omega

/-- An appearing anchor-balanced pattern reaches the source floor exactly. -/
theorem polynomialPattern_source_floor_eq_of_anchor_invariant
    {n D K τ M q : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (p : Fin M → Fin (D + 1))
    (hcount : (∑ r, (p r : ℕ)) = D) (hKq : K ≤ q)
    (hinv : (shiftedAtomPatternKey q K p).sum (fun i k => i * k) +
        magnitudeShiftCode n Q anchor =
      D * q + τ + magnitudeMaxJetOrder n Q) :
    polynomialPatternSourceSum p + magnitudeShiftCode n Q anchor =
      D * K + τ + magnitudeMaxJetOrder n Q := by
  rw [shiftedAtomPatternKey_weightedSum_eq p hcount] at hinv
  have hmul : D * (q - K) + D * K = D * q := by
    rw [Nat.mul_sub_left_distrib, Nat.sub_add_cancel]
    exact Nat.mul_le_mul_left D hKq
  dsimp [polynomialPatternSourceSum]
  omega

end

end GaloisForLFunctions
