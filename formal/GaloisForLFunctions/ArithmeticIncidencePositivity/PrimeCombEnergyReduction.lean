import GaloisForLFunctions.ArithmeticIncidencePositivity.TranslatePairingCalculus

/-!
# The cost side is one prime-comb energy

The reduced cost side of the ledger is a weighted sum of **first-power** charges,
`Σ_p w_p A(log p)` with the Euler weights `w_p ≍ log p/√p`. Read as a pairing it is
`⟪F, Σ_p w_p F(· + log p)⟫`, so Cauchy–Schwarz gives

    (Σ_p w_p A(log p))² ≤ A(0) · ‖Σ_p w_p F(· + log p)‖²,

and the right factor is the **prime-comb energy**

    E_w(F) = Σ_{p,q} w_p w_q A(log q − log p),

the Gram form of the weighted prime comb. Splitting it into its diagonal and its cross-prime part,

    E_w(F) = (Σ_p w_p²) A(0) + Σ_{p ≠ q} w_p w_q A(log q − log p),

the diagonal is harmless: with the Euler weights `Σ_{p ≤ e^{2r}} (log p)²/p` is *polynomial* in the
aperture, while the trivial `ℓ¹` bound on the cost side is `(Σ_p w_p)² ≍ e^{2r}`. So a nonpositive —
or merely polynomially large — cross-prime aggregate turns the exponential rate-`1` bound into a
polynomial one, which is the loss the grading treats as free.

The whole exponential obstruction of the cost side therefore sits in **one scalar**: the weighted
cross-prime correlation sum `Σ_{p ≠ q} w_p w_q A(log(q/p))`, the mean square of a prime Dirichlet
polynomial against the test's spectral measure, and no pointwise sign at a pair is needed any more.
-/

open MeasureTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {F : ℝ → ℝ}

/-- The weighted prime comb `Σ_p w_p F(· + log p)` over a finite set of moduli. -/
def primeComb (F : ℝ → ℝ) (s : Finset ℕ) (w : ℕ → ℝ) : ℝ → ℝ :=
  finsetComb F s w (fun p => Real.log p)

/-- The prime-comb energy `E_w(F) = Σ_{p,q} w_p w_q A(log q − log p)`: the Gram form of the comb. -/
def combEnergy (F : ℝ → ℝ) (s : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ p ∈ s, ∑ q ∈ s, w p * w q * autoCorr F (Real.log q - Real.log p)

/-- The comb energy is the energy of the comb, hence nonnegative. -/
theorem combEnergy_eq_testPairing (hFn : ContCompact F) (s : Finset ℕ) (w : ℕ → ℝ) :
    combEnergy F s w = testPairing (primeComb F s w) (primeComb F s w) := by
  rw [combEnergy, primeComb, testPairing_finsetComb hFn]

/-- The cost side as a pairing of the test against its prime comb. -/
theorem testPairing_primeComb (hFn : ContCompact F) (s : Finset ℕ) (w : ℕ → ℝ) :
    testPairing F (primeComb F s w) = ∑ p ∈ s, w p * autoCorr F (Real.log p) := by
  have h := testPairing_single_finsetComb hFn 0 s w (fun p => Real.log p)
  simp only [add_zero, sub_zero] at h
  rw [primeComb, h]

/-- **The cost side is bounded by one prime-comb energy.** For every finite set of moduli and every
weighting,

    (Σ_p w_p A(log p))² ≤ A(0) · E_w(F).

The whole first-power cost side of the ledger is therefore controlled by a single quadratic
functional of the weights — the Gram form of the weighted prime comb. -/
theorem sq_cost_le_mass_mul_combEnergy (hF : Continuous F) (hFc : HasCompactSupport F)
    (s : Finset ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ s, w p * autoCorr F (Real.log p)) ^ 2 ≤ autoCorr F 0 * combEnergy F s w := by
  have hFn : ContCompact F := ⟨hF, hFc⟩
  have hC : ContCompact (primeComb F s w) := by
    rw [primeComb]; exact contCompact_finsetComb hFn s w (fun p => Real.log p)
  have h := testPairing_cauchy_schwarz hFn hC
  rw [testPairing_primeComb hFn, testPairing_self_eq_autoCorr_zero,
    ← combEnergy_eq_testPairing hFn] at h
  exact h

/-- **Diagonal and cross-prime parts of the comb energy.** -/
theorem combEnergy_eq_diagonal_add_cross (s : Finset ℕ) (w : ℕ → ℝ) :
    combEnergy F s w = (∑ p ∈ s, w p ^ 2) * autoCorr F 0
      + ∑ p ∈ s, ∑ q ∈ s.erase p, w p * w q * autoCorr F (Real.log q - Real.log p) := by
  have hrow : ∀ p ∈ s, ∑ q ∈ s, w p * w q * autoCorr F (Real.log q - Real.log p)
      = w p ^ 2 * autoCorr F 0
        + ∑ q ∈ s.erase p, w p * w q * autoCorr F (Real.log q - Real.log p) := by
    intro p hp
    rw [← Finset.add_sum_erase _ _ hp, sub_self]
    ring
  rw [combEnergy, Finset.sum_congr rfl hrow, Finset.sum_add_distrib, Finset.sum_mul]

/-- **The cross-prime aggregate carries the whole rate.** If the weighted cross-prime correlation
sum is nonpositive, the cost side is at most `√(Σ_p w_p²) · A(0)`: with the Euler weights the
`ℓ²` norm of the weights is polynomial in the aperture, against the exponential `ℓ¹` norm of the
trivial bound. -/
theorem cost_le_sqrt_diagonal_mul_mass (hF : Continuous F) (hFc : HasCompactSupport F)
    (s : Finset ℕ) (w : ℕ → ℝ)
    (hcross : ∑ p ∈ s, ∑ q ∈ s.erase p,
      w p * w q * autoCorr F (Real.log q - Real.log p) ≤ 0) :
    ∑ p ∈ s, w p * autoCorr F (Real.log p)
      ≤ Real.sqrt (∑ p ∈ s, w p ^ 2) * autoCorr F 0 := by
  have h0 : 0 ≤ autoCorr F 0 := autoCorr_zero_nonneg hF hFc
  have hd : 0 ≤ ∑ p ∈ s, w p ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
  have hkey := sq_cost_le_mass_mul_combEnergy hF hFc s w
  rw [combEnergy_eq_diagonal_add_cross] at hkey
  -- drop the cross term and take square roots
  have hbound : (∑ p ∈ s, w p * autoCorr F (Real.log p)) ^ 2
      ≤ (Real.sqrt (∑ p ∈ s, w p ^ 2) * autoCorr F 0) ^ 2 := by
    have hsq : (Real.sqrt (∑ p ∈ s, w p ^ 2)) ^ 2 = ∑ p ∈ s, w p ^ 2 := Real.sq_sqrt hd
    have hmono : autoCorr F 0 * ((∑ p ∈ s, w p ^ 2) * autoCorr F 0
          + ∑ p ∈ s, ∑ q ∈ s.erase p,
            w p * w q * autoCorr F (Real.log q - Real.log p))
        ≤ autoCorr F 0 * ((∑ p ∈ s, w p ^ 2) * autoCorr F 0) := by
      have := mul_le_mul_of_nonneg_left hcross h0
      linarith [this]
    have hrw : (Real.sqrt (∑ p ∈ s, w p ^ 2) * autoCorr F 0) ^ 2
        = autoCorr F 0 * ((∑ p ∈ s, w p ^ 2) * autoCorr F 0) := by
      rw [mul_pow, hsq]
      ring
    rw [hrw]
    exact le_trans hkey hmono
  have hnn : 0 ≤ Real.sqrt (∑ p ∈ s, w p ^ 2) * autoCorr F 0 :=
    mul_nonneg (Real.sqrt_nonneg _) h0
  nlinarith [hbound, hnn]

end GaloisForLFunctions.ArithmeticIncidencePositivity
