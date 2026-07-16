import GaloisForLFunctions.HTGeometry.PolynomialPatternSourceFloor

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

/-- Residue-indexed balanced survival parametrized at the exact coefficient
levels `D*q+τ`, while retaining the fixed raw offsets needed by the convex
gap theorem. -/
theorem exists_eventually_balancedKey_nonzero_exact_residue
    {n : ℕ} {Q : MvPolynomial (Fin (n + 2)) ℂ}
    {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor)
    (τ : ℕ) (hτ : τ < jetMonomialDegree n anchor) :
    ∃ (K : ℕ) (δ : Fin (jetMonomialDegree n anchor) → ℕ) (Q₀ : ℕ),
      ∀ q ≥ Q₀,
        let D := jetMonomialDegree n anchor
        let qraw := q - K
        let s : Fin D → ℕ := fun i => qraw + δ i
        key s ∈ (sigmaIdx n (D * q + τ) Q).image (atomKeyOf n) ∧
          aevalWeight n (D * q + τ) Q (key s) ≠ 0 ∧
          (key s).sum (fun i k => i * k) + magnitudeShiftCode n Q anchor =
            D * q + τ + magnitudeMaxJetOrder n Q := by
  classical
  let D := jetMonomialDegree n anchor
  let J := jetMonomialOrder n anchor
  obtain ⟨δ₀, hδ₀inj, Qbal, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight_residue ha hD τ
  let δ : Fin D → ℕ := fun i => J + δ₀ i
  let C₀ := (∑ i, δ i) + anchor 0 - J
  have hJsum : J ≤ (∑ i, δ i) + anchor 0 := by
    obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    have hi : J ≤ δ i₀ := by simp [δ]
    exact hi.trans ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i₀)).trans (Nat.le_add_right _ _))
  have hNshape (q : ℕ) :
      (∑ i : Fin D, ((q + J) + δ₀ i)) + anchor 0 - J = D * q + C₀ := by
    have hsum : (∑ i : Fin D, ((q + J) + δ₀ i)) =
        D * q + ∑ i, δ i := by
      simp only [δ, Finset.sum_add_distrib]
      simp [D]
      ring
    rw [hsum]
    dsimp [C₀]
    omega
  have hdata₀ := hbalanced (Qbal + J) (Nat.le_add_right _ _)
  let N₀ := (∑ i : Fin D, ((Qbal + J) + δ₀ i)) + anchor 0 - J
  have hN₀ : N₀ = D * Qbal + C₀ := hNshape Qbal
  have hmodN₀ : Nat.ModEq D N₀ τ := by
    simpa only [D, J, N₀] using hdata₀.1
  have hmodC₀ : Nat.ModEq D C₀ τ :=
    (Nat.ModEq.modulus_mul_add (m := D) (a := Qbal) (b := C₀)).symm.trans
      (by simpa [hN₀] using hmodN₀)
  have hrem : C₀ % D = τ := by
    change C₀ % D = τ % D at hmodC₀
    have hτD : τ < D := by simpa [D] using hτ
    rw [Nat.mod_eq_of_lt hτD] at hmodC₀
    exact hmodC₀
  let K := C₀ / D
  have hC₀shape : D * K + τ = C₀ := by
    have hdiv := Nat.mod_add_div C₀ D
    rw [hrem] at hdiv
    dsimp [K]
    omega
  let Q₀ := Qbal + K
  refine ⟨K, δ, Q₀, ?_⟩
  intro q hq
  dsimp only
  let qraw := q - K
  let s : Fin D → ℕ := fun i => qraw + δ i
  have hKq : K ≤ q := (Nat.le_add_left K Qbal).trans hq
  have hqraw : Qbal ≤ qraw := by dsimp [qraw]; omega
  have hrawK : qraw + K = q := by dsimp [qraw]; omega
  have hold : Qbal ≤ qraw + J := hqraw.trans (Nat.le_add_right _ _)
  have hdata := hbalanced (qraw + J) hold
  let sOld : Fin D → ℕ := fun i => (qraw + J) + δ₀ i
  let NOld := (∑ i, sOld i) + anchor 0 - J
  have hsEq : sOld = s := by
    funext i
    simp only [sOld, s, δ]
    omega
  have hNOld : NOld = D * q + τ := by
    have hshape : NOld = D * qraw + C₀ := by
      simpa only [sOld, NOld] using hNshape qraw
    rw [hshape, ← hC₀shape, ← hrawK]
    ring
  have hmem : key sOld ∈ (sigmaIdx n NOld Q).image (atomKeyOf n) := by
    simpa only [D, J, sOld, NOld] using hdata.2.1
  have hweight : aevalWeight n NOld Q (key sOld) ≠ 0 := by
    simpa only [D, J, sOld, NOld] using hdata.2.2.1
  have hqJ : J ≤ qraw + J := Nat.le_add_left _ _
  have hqsum : J ≤ ∑ i, sOld i := by
    obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    calc
      J ≤ sOld i₀ := by dsimp [sOld]; omega
      _ ≤ ∑ i, sOld i := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i₀)
  have hinvOld := witness_sum_add_shiftCode Q ha δ₀ NOld rfl hqsum
  refine ⟨?_, ?_, ?_⟩
  · simpa [hNOld, hsEq] using hmem
  · simpa [hNOld, hsEq] using hweight
  · change (key s).sum (fun i k => i * k) + magnitudeShiftCode n Q anchor =
      D * q + τ + magnitudeMaxJetOrder n Q
    rw [← hsEq, ← hNOld]
    rw [key_weighted_sum]
    exact hinvOld

end

end GaloisForLFunctions
