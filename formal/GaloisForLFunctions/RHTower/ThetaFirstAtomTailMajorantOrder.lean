import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomHighOrderMomentBounds

/-!
# The first-atom tail majorant at every even order

The existing tail majorant for the first theta atom is stated only for `r ≤ 3`, because its decay
rate `71/2` is the one produced by the bound `x ^ (2 * r) ≤ exp (6 * (x - 1))`.  The same argument
runs at every order once the decay rate is allowed to depend on the order: with
`x ^ (2 * r) ≤ exp (2 * r * (x - 1))` the exponential comparison closes with rate `83/2 - 2 * r`,
which is exactly the `r = 3` rate when `r = 3` and stays positive through `r = 20`.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Order-uniform tail majorant: for every even order `r` the first-atom density is dominated on
`[1, ∞)` by a single exponential with rate `83/2 - 2 * r`. -/
theorem thetaCuspFirstAtom_tail_density_le_exp_majorant_order
    (r : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
      79 * Real.exp (-37 / 2) *
        Real.exp (-((83 : ℝ) / 2 - 2 * (r : ℝ)) * (x - 1)) := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hxshift : 0 ≤ x - 1 := sub_nonneg.mpr hx
  have hxexp : x ≤ Real.exp (x - 1) := by
    nlinarith [Real.add_one_le_exp (x - 1)]
  have hxpow : x ^ (2 * r) ≤ Real.exp (2 * (r : ℝ) * (x - 1)) := by
    calc
      x ^ (2 * r) ≤ Real.exp (x - 1) ^ (2 * r) := pow_le_pow_left₀ hx0 hxexp _
      _ = Real.exp (((2 * r : ℕ) : ℝ) * (x - 1)) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (2 * (r : ℝ) * (x - 1)) := by push_cast; ring
  have hdouble : 46 * x - 23 ≤ Real.pi * Real.exp (2 * x) := by
    have hconvex : 1 + 2 * (x - 1) ≤ Real.exp (2 * (x - 1)) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * (x - 1))
    calc
      46 * x - 23 = 23 * (1 + 2 * (x - 1)) := by ring
      _ ≤ (Real.pi * Real.exp 2) * Real.exp (2 * (x - 1)) :=
        mul_le_mul twentyThree_lt_pi_mul_exp_two.le hconvex (by nlinarith) (by positivity)
      _ = Real.pi * Real.exp (2 * x) := by
        rw [show Real.pi * Real.exp 2 * Real.exp (2 * (x - 1)) =
          Real.pi * (Real.exp 2 * Real.exp (2 * (x - 1))) by ring, ← Real.exp_add]
        congr 1
        ring
  have hpiCoeff : 8 * Real.pi ^ (2 : ℕ) ≤ (79 : ℝ) := by
    nlinarith [Real.pi_pos, Real.pi_lt_d20]
  have hsource := HedenmalmThetaSource.thetaCuspSourceTerm_one_le x
  have henv0 := (HedenmalmThetaSource.thetaEnvelope_pos x).le
  calc
    2 * (x ^ (2 * r) * thetaCuspSourceTerm x 1) ≤
        2 * (x ^ (2 * r) *
          (4 * Real.pi ^ (2 : ℕ) * HedenmalmThetaSource.thetaEnvelope x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsource (pow_nonneg hx0 _)) (by norm_num)
    _ = 8 * Real.pi ^ (2 : ℕ) * (x ^ (2 * r) *
          HedenmalmThetaSource.thetaEnvelope x) := by ring
    _ ≤ 79 * (x ^ (2 * r) * HedenmalmThetaSource.thetaEnvelope x) :=
      mul_le_mul_of_nonneg_right hpiCoeff
        (mul_nonneg (pow_nonneg hx0 _) henv0)
    _ ≤ 79 * (Real.exp (2 * (r : ℝ) * (x - 1)) *
          HedenmalmThetaSource.thetaEnvelope x) := by gcongr
    _ = 79 * Real.exp
          (2 * (r : ℝ) * (x - 1) + 9 * x / 2 - Real.pi * Real.exp (2 * x)) := by
      rw [HedenmalmThetaSource.thetaEnvelope, ← Real.exp_add, ← Real.exp_add]
      ring
    _ ≤ 79 * Real.exp (-37 / 2 - ((83 : ℝ) / 2 - 2 * (r : ℝ)) * (x - 1)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by nlinarith [hdouble])
    _ = 79 * Real.exp (-37 / 2) *
          Real.exp (-((83 : ℝ) / 2 - 2 * (r : ℝ)) * (x - 1)) := by
      rw [show -37 / 2 - ((83 : ℝ) / 2 - 2 * (r : ℝ)) * (x - 1) =
        -37 / 2 + (-((83 : ℝ) / 2 - 2 * (r : ℝ)) * (x - 1)) by ring, Real.exp_add]
      ring

end

end RHTower
