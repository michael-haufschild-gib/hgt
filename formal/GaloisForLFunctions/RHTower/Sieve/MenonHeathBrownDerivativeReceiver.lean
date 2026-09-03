import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownLongFactorReceiver

/-!
# Menon's derivative-range Heath--Brown receiver

A zeta or logarithm atom in the higher-derivative range has a literal power deficit.  Rewriting
that deficit as a positive saving scale puts the factor directly into the derivative-excised
Montgomery theorem.  The result keeps the exact selected factor and erase-complement.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The selected zeta/log factor's derivative-test power saving, composed with the exact
complementary Montgomery energy of its Heath--Brown box. -/
theorem derivativeExcised_montgomery_heathBrownBox_derivativeDefect
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k)
    (j : HeathBrownBoxFactorIndex k box.m)
    (hkind : heathBrownBoxFactorKind k box.m j = .zeta ∨
      heathBrownBoxFactorKind k box.m j = .log)
    (hX : 1 ≤ X) {c : ℝ} (hc : 0 ≤ c)
    {S : Finset ℕ} {lam : ℕ → ℝ} {delta H : ℝ}
    (hdelta : 0 < delta) (hH : 0 ≤ H)
    (hgap : ∀ i, lam i + delta ≤ lam (i + 1))
    (hband : ∀ r ∈ S, delta / 2 ≤ lam r ∧ lam r + delta / 2 ≤ H)
    {D alpha : ℝ} (hD : 0 < D) {k0 : ℕ} (hk0 : 2 ≤ k0)
    (hfac : Nat.factorial (k0 - 1) ≤
      2 ^ heathBrownBoxFactorExponent box.a box.b box.q j)
    (hordinate : ∀ r ∈ S,
      0 < lam r ∧
      8 * Real.pi *
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
            ((1 : ℝ) / 3) ≤ lam r ∧
      lam r ≤ 2 * Real.pi * 2 ^ k0 *
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
            (k0 - 1) *
          (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ)) ^
            (-(1 / 3) : ℝ))
    (hlarge : ∀ r ∈ S, D ^ (alpha - c) ≤
      ‖heathBrownDyadicCoreProduct L X k box.m box.a box.b box.q
        ((c : ℂ) + (lam r : ℝ) * Complex.I)‖) :
    let N : ℝ :=
      (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
    let C : ℝ := heathBrownDerivativeConstant X
      (heathBrownBoxFactorKind k box.m j)
      (heathBrownBoxFactorExponent box.a box.b box.q j)
    let Tsave : ℝ := N ^ maynardDerivativeDeficit k0
    let I := {i : HeathBrownBoxFactorIndex k box.m //
      i ∈ (Finset.univ.erase j)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent box.a box.b box.q i
    let U : ℕ := groupedDyadicUpper q
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    (S.card : ℝ) *
        (((Tsave / C) * D ^ (alpha - c) * N ^ (c - 1)) ^ 2) ≤
      (H + 4 * (U : ℝ) * (1 + Real.log U)) *
        (1 / delta + 2 * Real.log U) *
        (((groupedDyadicLower q : ℝ) ^ (-c)) ^ 2 *
          ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent box.a box.b box.q j : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind k box.m j)
    (heathBrownBoxFactorExponent box.a box.b box.q j)
  let Tsave : ℝ := N ^ maynardDerivativeDeficit k0
  have hN : 0 < N := by dsimp [N]; positivity
  have hC : 0 < C := by
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hTsave : 0 < Tsave := Real.rpow_pos_of_pos hN _
  apply derivativeExcised_montgomery_heathBrownBox_fixedPolylog box j hc hdelta hH
    hgap hband hD hN hTsave hC
  · intro r hr
    have hq := box.factorExponent_le_log_X_of_zeta_or_log j hkind
    have hraw := norm_heathBrownBoxFactorValue_le_derivative_defect
      L X k box j hkind hX hc (hordinate r hr).1 hk0 hq hfac
        (hordinate r hr).2.1 (hordinate r hr).2.2
    calc
      ‖heathBrownBoxFactorValue L X k box
          ((c : ℂ) + (lam r : ℝ) * Complex.I) j‖ ≤
          C * N ^ (1 - c) * N ^ (-maynardDerivativeDeficit k0) := by
            simpa [C, N] using hraw
      _ = C / Tsave * N ^ (1 - c) := by
        dsimp only [Tsave]
        rw [Real.rpow_neg hN.le]
        ring
  · exact hlarge

end


end RHTower.Sieve
