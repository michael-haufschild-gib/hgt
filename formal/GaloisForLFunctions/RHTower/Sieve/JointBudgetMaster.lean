import GaloisForLFunctions.RHTower.Sieve.JointOmegaBudgetFromLadder

/-!
# The joint budget, with the spectral part replaced

`Sieve/JointOmegaSpectral.jointOmegaBudget` is the whole explicit cost of the joint arrangement at
one scale; its first summand is the Gallagher-weighted spectral integral.  Replacing that summand by
`Sieve/JointOmegaBudgetFromLadder.integral_kernel_normSq_jointOmega_le'` turns the budget into an
expression in five explicit quantities:

* the coefficient energy `Ec`;
* the mean-square bound `β₀` at the expiry height `T₀`;
* the Gallagher cut `Wc`;
* the two designated ranges' sizes and harmonic masses.

Everything downstream is then real analysis in those five quantities.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The joint budget with the spectral part replaced.** -/
theorem jointOmegaBudget_le {x h : ℝ} {P Q : Finset ℕ}
    {δ Wc T₀ β₀ : ℝ} (hδ : δ = fibreWidth x h) (hδ0 : 0 < δ)
    (hWc : 1 ≤ Wc) (hT₀ : 0 < T₀) (hδWc : δ * Wc ≤ 1)
    (hbound : (∫ w in Set.Icc (-T₀) T₀,
        ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ 2) ≤ β₀) :
    jointOmegaBudget x h P Q
      ≤ 16 * Real.sqrt x
          * (3 * ((5 * Real.pi / 2
                + 5 * Real.exp 1 / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / T₀)
              * ∑ n ∈ fibreIndex x h, ‖jointOmegaCoeff P Q n‖ ^ 2) / Wc
            + 3 * β₀ / Wc ^ 2)
        + 204 * (((P.card : ℝ) + 1) * ((Q.card : ℝ) + 1)) ^ 2 * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) * (Joint.mass P * Joint.mass Q)
                  * (Joint.mass P + Joint.mass Q + 1)
              + 2 * (Joint.mass P * Joint.mass Q) * (P.card : ℝ) * (Q.card : ℝ)) := by
  classical
  have hidx : fibreIndex x h = Finset.Icc 1 ⌊Real.sqrt x + h⌋₊ := rfl
  have hbound' : (∫ w in Set.Icc (-T₀) T₀,
      ‖jointOmegaPoly P Q (Finset.Icc 1 ⌊Real.sqrt x + h⌋₊) w‖ ^ 2) ≤ β₀ := by
    rw [← hidx]; exact hbound
  have hspec := integral_kernel_normSq_jointOmega_le' (P := P) (Q := Q) (A₀ := 1)
    (B₀ := ⌊Real.sqrt x + h⌋₊) (by omega) (δ := δ) hδ0 hWc hT₀ hδWc hbound'
  rw [← hidx] at hspec
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hspec (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt x)
  rw [jointOmegaBudget, ← hδ]
  have hcast : (5 * Real.pi / 2
        + 5 * Real.exp 1 / 2 * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / T₀))
      = 5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / T₀ := by
    ring
  rw [hcast] at hmul
  linarith [hmul]

end

end RHTower.Sieve
