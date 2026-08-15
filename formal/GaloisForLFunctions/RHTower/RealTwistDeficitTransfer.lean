import GaloisForLFunctions.RHTower.ZetaOneLineDeficit
import GaloisForLFunctions.RHTower.PretentiousDistance

/-!
# The real-twist gap from the zeta one-line deficit

A real multiplicative prime sequence is reflected into its own conjugate by an archimedean
character, so the character separation is at most four times its pretentious distance.  Since the
character separation is exactly the prime clock energy at the doubled frequency, the one-line zeta
deficit transfers to the twist gap with the universal factor one quarter:

```text
D_x(g, n^{iα})² ≥ (log log x - log |ζ(1 + 1/log x + 2iα)| - C)/4.
```
-/

open Filter Topology Set

namespace RHTower

noncomputable section

/-- The shifted one-line deficit of `log |ζ|` below its trivial scale. -/
def zetaLineDeficit (τ x : ℝ) : ℝ :=
  Real.log (Real.log x) - Real.log ‖riemannZeta (zetaLinePoint (1 + 1 / Real.log x) τ)‖

/-- **The deficit is a lower bound for the prime clock energy.** -/
theorem zetaLineDeficit_sub_le_primeClockEnergy {τ x : ℝ} (hx : Real.exp 2 ≤ x) :
    zetaLineDeficit τ x - zetaDeficitConst ≤ primeClockEnergy τ x := by
  have h := abs_le.mp (abs_zeta_deficit_sub_primeClockEnergy_le (τ := τ) (x := x) hx)
  rw [zetaLineDeficit]
  linarith [h.2]

/-- The character separation is the prime clock energy at the doubled frequency. -/
theorem pretentiousDistSq_primeChar_eq_primeClockEnergy (α x : ℝ) :
    pretentiousDistSq (primeChar (-α)) (primeChar α) x = primeClockEnergy (2 * α) x := by
  rw [pretentiousDistSq_primeChar, primeClockEnergy]

/-- **(Z8)+(Z10) The real-twist transfer.**  For every real prime sequence in the closed unit disc
the pretentious distance to an archimedean character receives one quarter of the zeta one-line
deficit at the doubled frequency. -/
theorem quarter_zetaLineDeficit_le_pretentiousDistSq {r : ℕ → ℝ} (hr : ∀ n, |r n| ≤ 1)
    {α x : ℝ} (hx : Real.exp 2 ≤ x) :
    (zetaLineDeficit (2 * α) x - zetaDeficitConst) / 4
      ≤ pretentiousDistSq (fun n => (r n : ℂ)) (primeChar α) x := by
  have hclock := zetaLineDeficit_sub_le_primeClockEnergy (τ := 2 * α) (x := x) hx
  have hsep := pretentiousDistSq_primeChar_le_four_mul hr α x
  rw [pretentiousDistSq_primeChar_eq_primeClockEnergy] at hsep
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  linarith [hclock, hsep]

end

end RHTower
