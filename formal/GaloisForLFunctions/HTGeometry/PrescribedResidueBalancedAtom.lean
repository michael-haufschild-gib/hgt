import GaloisForLFunctions.HTGeometry.MagnitudeBalancedAtomExistence

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

/-- Residue-indexed balanced survival.  For every coefficient residue modulo
the positive top jet degree, a balanced nonzero grouped atom survives at every
sufficiently large coefficient level in that residue. -/
theorem exists_eventually_balanced_nonzero_aevalWeight_residue {n : ℕ}
    {Q : MvPolynomial (Fin (n + 2)) ℂ} {anchor : Fin (n + 2) →₀ ℕ}
    (ha : anchor ∈ Q.support) (hD : 0 < jetMonomialDegree n anchor) (τ : ℕ) :
    ∃ (δ : Fin (jetMonomialDegree n anchor) → ℕ), Function.Injective δ ∧
      ∃ Q₀ : ℕ, ∀ q ≥ Q₀,
        let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
        let N := (∑ i, s i) + anchor 0 - jetMonomialOrder n anchor
        Nat.ModEq (jetMonomialDegree n anchor) N τ ∧
          key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) ∧
          aevalWeight n N Q (key s) ≠ 0 ∧
          balancedJetGroup n N (jetMonomialDegree n anchor) Q s =
            topShiftJetGroup n Q anchor := by
  classical
  let D := jetMonomialDegree n anchor
  let J := jetMonomialOrder n anchor
  let r := anchor 0 % D
  let ρ := τ + J + (D - r)
  have hrlt : r < D := by dsimp [r, D]; exact Nat.mod_lt _ hD
  have hrle : r ≤ D := hrlt.le
  have hρ : Nat.ModEq D (ρ + anchor 0) (τ + J) := by
    have hmoda : Nat.ModEq D r (anchor 0) := by
      simpa [r] using Nat.mod_modEq (anchor 0) D
    have hzero : Nat.ModEq D (D - r + anchor 0) 0 := by
      calc
        D - r + anchor 0 ≡ D - r + r [MOD D] := hmoda.symm.add_left (D - r)
        _ = D := Nat.sub_add_cancel hrle
        _ ≡ 0 [MOD D] := Nat.modulus_modEq_zero
    simpa [ρ, add_assoc] using hzero.add_left (τ + J)
  obtain ⟨δ, hδinj, hδmod, Q₀, hsurvive⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight_modSum ha hD ρ
  let Q₁ := max Q₀ J
  refine ⟨δ, hδinj, Q₁, fun q hq => ?_⟩
  have hq₀ : Q₀ ≤ q := (le_max_left _ _).trans hq
  have hqJ : J ≤ q := (le_max_right _ _).trans hq
  let s : Fin D → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - J
  have hdata := hsurvive q hq₀
  have hqsum : q ≤ ∑ i, s i := by
    obtain ⟨i0⟩ : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
    calc
      q ≤ s i0 := by simp [s]
      _ ≤ ∑ i, s i := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i0)
  have hJsum : J ≤ (∑ i, s i) + anchor 0 := by
    exact hqJ.trans (hqsum.trans (Nat.le_add_right _ _))
  have hNadd : N + J = (∑ i, s i) + anchor 0 := by
    dsimp [N]
    exact Nat.sub_add_cancel hJsum
  have hsSum : (∑ i, s i) = D * q + ∑ i, δ i := by
    dsimp [s]
    rw [Finset.sum_add_distrib]
    simp [D]
  have hδtarget : Nat.ModEq D ((∑ i, δ i) + anchor 0) (τ + J) :=
    (hδmod.add_right (anchor 0)).trans hρ
  have hNaddMod : Nat.ModEq D (N + J) (τ + J) := by
    rw [hNadd, hsSum]
    rw [add_assoc]
    exact (Nat.ModEq.modulus_mul_add (m := D) (a := q)
      (b := (∑ i, δ i) + anchor 0)).trans hδtarget
  have hNmod : Nat.ModEq D N τ := Nat.ModEq.add_right_cancel' J hNaddMod
  simpa only [D, J, s, N] using And.intro hNmod hdata

end

end GaloisForLFunctions
