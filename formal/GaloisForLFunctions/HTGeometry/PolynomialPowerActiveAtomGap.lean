import GaloisForLFunctions.HTGeometry.PolynomialPatternResidueBridge

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

lemma phaseKeyPowerValuation {β : ℝ} {D : ℕ} (t : Fin D → ℕ) :
    (key t).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
      tuplePowerValuation β t := by
  rw [valuation_eq_key_sum]
  rfl

lemma phaseSupportWindowOfKey {q K D : ℕ} (t : Fin D → ℕ)
    (hwindow : tupleInWindow q K t) {ν : ℕ →₀ ℕ} (hkey : key t = ν) :
    ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K := by
  intro i hi
  have hkeyi : key t i ≠ 0 := by simpa [hkey] using hi
  have hex : ∃ j, t j = i := by
    by_contra hno
    push Not at hno
    apply hkeyi
    simp [key, hno]
  obtain ⟨j, hj⟩ := hex
  have hjw := hwindow j
  omega

/-- Every appearing atom outside one bounded top-degree window is separated
from a fixed balanced witness by `c*q^(β-2)`.  This combines the lower-degree
`q^β` gap and the explicit convex-shell confinement gap. -/
theorem exists_eventually_activeAtom_powerGap_or_window
    {β : ℝ} (hβ : 2 < β) {n : ℕ}
    (Q : MvPolynomial (Fin (n + 2)) ℂ)
    {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support)
    (haD : jetMonomialDegree n anchor = magnitudeMaxJetDegree n Q)
    (haMax : ∀ m ∈ Q.support,
      jetMonomialDegree n m = jetMonomialDegree n anchor →
        magnitudeShiftCode n Q m ≤ magnitudeShiftCode n Q anchor)
    (hD : 0 < jetMonomialDegree n anchor)
    (δ : Fin (jetMonomialDegree n anchor) → ℕ) :
    ∃ (K : ℕ) (c : ℝ), 0 < c ∧ ∀ᶠ q : ℕ in atTop,
      let D := jetMonomialDegree n anchor
      let J := jetMonomialOrder n anchor
      let s : Fin D → ℕ := fun i => q + δ i
      let N := (∑ i, s i) + anchor 0 - J
      ∀ ν ∈ (sigmaIdx n N Q).image (atomKeyOf n),
        (ν.sum (fun _ k => k) = D ∧
          ∀ i, ν i ≠ 0 → q - K ≤ i ∧ i ≤ q + K) ∨
        (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) +
            c * (q : ℝ) ^ (β - 2) ≤
          ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) := by
  classical
  let D := jetMonomialDegree n anchor
  let J := jetMonomialOrder n anchor
  let Z := magnitudeMaxXDegree Q
  let O := magnitudeMaxJetOrder n Q
  let Csum := magnitudeShiftCode n Q anchor
  obtain ⟨cdeg, hcdeg, hdeg⟩ :=
    eventually_lowerDegree_tuplePower_rpow_gap (by linarith : 1 < β)
      hD δ (J + Z)
  obtain ⟨K, cconf, hcconf, hconf⟩ :=
    exists_eventually_bounded_powerGap hβ hD δ Csum
  let c := min cdeg cconf
  have hc : 0 < c := lt_min hcdeg hcconf
  refine ⟨K, c, hc, ?_⟩
  filter_upwards [hdeg, hconf,
    eventually_ge_atTop (max (2 * (J + Z) + 2) 1)] with q hdegq hconfq hq
  dsimp only
  let s : Fin D → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - J
  have hqJ : J ≤ q := by omega
  have hqsum : q ≤ ∑ i, s i := by
    obtain ⟨i₀⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    calc
      q ≤ s i₀ := by simp [s]
      _ ≤ ∑ i, s i := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i₀)
  have hJsum : J ≤ (∑ i, s i) + anchor 0 :=
    hqJ.trans (hqsum.trans (Nat.le_add_right _ _))
  have hNadd : N + J = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    exact Nat.sub_add_cancel hJsum
  have hDqN : D * q ≤ N + J := by
    rw [hNadd]
    have hsLower : D * q ≤ ∑ i, s i := by
      calc
        D * q = ∑ _i : Fin D, q := by simp
        _ ≤ ∑ i, s i := by
          apply Finset.sum_le_sum
          intro i _
          simp [s]
    omega
  have hNZ : Z < N := by
    have hqJZ : J + Z < q := by omega
    have hqD : q ≤ D * q := by
      simpa [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ D by omega)
    dsimp [Z]
    change magnitudeMaxXDegree Q < N
    omega
  have hwitInv : (∑ i, s i) + Csum = N + O := by
    exact witness_sum_add_shiftCode Q ha δ N rfl (hqJ.trans hqsum)
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hpowWeak : (q : ℝ) ^ (β - 2) ≤ (q : ℝ) ^ β := by
    apply Real.rpow_le_rpow_of_exponent_le hqone
    linarith
  intro ν hν
  have hcountle := appearing_atom_count_le Q hν
  change ν.sum (fun _ k => k) ≤ magnitudeMaxJetDegree n Q at hcountle
  rw [← haD] at hcountle
  rcases hcountle.eq_or_lt with hcount | hcountlt
  ·
    let t : Fin D → ℕ := tupleOfFinsupp ν D hcount
    have hbounds : D * q + (∑ i, δ i) ≤ ∑ i, t i ∧
        (∑ i, t i) ≤ D * q + (∑ i, δ i) + Csum := by
      obtain ⟨m, hm, hmD, hinv⟩ := appearing_atom_sum_add_shiftCode Q hν
      have hmTop : jetMonomialDegree n m = jetMonomialDegree n anchor := by
        rw [hmD, hcount]
      have hcodele := haMax m hm hmTop
      have hsumt := sum_tupleOfFinsupp ν D hcount
      have hsEq : (∑ i, s i) = D * q + ∑ i, δ i := by
        dsimp [s, D]
        rw [Finset.sum_add_distrib]
        simp
      change ν.sum (fun i k => i * k) + magnitudeShiftCode n Q m = N + O at hinv
      change magnitudeShiftCode n Q m ≤ Csum at hcodele
      have hinv' : (∑ i, t i) + magnitudeShiftCode n Q m = N + O := by
        rw [show (∑ i, t i) = ν.sum (fun i k => i * k) by
          simpa [t] using hsumt]
        exact hinv
      rw [hsEq] at hwitInv
      omega
    by_cases htwin : tupleInWindow q K t
    · left
      exact ⟨hcount, phaseSupportWindowOfKey t htwin
        (key_tupleOfFinsupp ν D hcount)⟩
    · right
      have hgap := hconfq t hbounds htwin
      have hνval : ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
          tuplePowerValuation β t := by
        rw [valuation_tupleOfFinsupp ν D hcount]
        rfl
      have hwitval : (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
          tuplePowerValuation β (fun i => q + δ i) := by
        simpa [s] using phaseKeyPowerValuation (β := β) s
      have hc_le : c ≤ cconf := min_le_right _ _
      have hscale : c * (q : ℝ) ^ (β - 2) ≤
          cconf * (q : ℝ) ^ (β - 2) :=
        mul_le_mul_of_nonneg_right hc_le (Real.rpow_nonneg (Nat.cast_nonneg q) _)
      rw [hνval, hwitval]
      linarith
  · right
    let d := ν.sum (fun _ k => k)
    have hdD : d < D := by simpa [d] using hcountlt
    have hsupport := appearing_atom_support_nonempty_of_maxX_lt_level Q hν
      (by simpa [Z] using hNZ)
    have hd : 0 < d := by
      by_contra hd0
      have hdEq : d = 0 := Nat.eq_zero_of_not_pos hd0
      obtain ⟨i, hi⟩ := hsupport
      have hiBound := finsupp_apply_le_count ν i
      have hiNe : ν i ≠ 0 := Finsupp.mem_support_iff.mp hi
      apply hiNe
      apply Nat.eq_zero_of_le_zero
      rw [← hdEq]
      simpa [d] using hiBound
    let t : Fin d → ℕ := tupleOfFinsupp ν d (by rfl)
    have hweightLower := (appearing_atom_weighted_sum_bounds Q hν).1
    change N - Z ≤ ν.sum (fun i k => i * k) at hweightLower
    have hsumt := sum_tupleOfFinsupp ν d (by rfl)
    have hmass : D * q ≤ (∑ i, t i) + (J + Z) := by
      rw [show (∑ i, t i) = ν.sum (fun i k => i * k) by
        simpa [t] using hsumt]
      have hNsplit : N - Z + Z = N := Nat.sub_add_cancel hNZ.le
      omega
    have hgap := hdegq d hd hdD t hmass
    have hνval : ν.sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
        tuplePowerValuation β t := by
      rw [valuation_tupleOfFinsupp ν d (by rfl)]
      rfl
    have hwitval : (key s).sum (fun i k => (k : ℝ) * (i : ℝ) ^ β) =
        tuplePowerValuation β (fun i => q + δ i) := by
      simpa [s] using phaseKeyPowerValuation (β := β) s
    have hc_le : c ≤ cdeg := min_le_left _ _
    have hscale : c * (q : ℝ) ^ (β - 2) ≤ cdeg * (q : ℝ) ^ β :=
      calc
        c * (q : ℝ) ^ (β - 2) ≤ cdeg * (q : ℝ) ^ (β - 2) :=
          mul_le_mul_of_nonneg_right hc_le (Real.rpow_nonneg (Nat.cast_nonneg q) _)
        _ ≤ cdeg * (q : ℝ) ^ β :=
          mul_le_mul_of_nonneg_left hpowWeak hcdeg.le
    rw [hνval, hwitval]
    linarith

end

end GaloisForLFunctions
