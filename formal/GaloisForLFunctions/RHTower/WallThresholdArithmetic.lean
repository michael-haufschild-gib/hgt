import GaloisForLFunctions.RHTower.WallBlockSourceEnergy

/-!
# The exponent bookkeeping of the one-block constant

Every tail term of the one-block estimate carries the threshold in a different way, and they all land
on a *single* power of it because of one identity:

`(1+Y)^{2p} Y^{1-2σ} ≤ 4^p Y²`,   `p = 1/2 + σ`,   `Y ≥ 1`,

whose content is `2p + (1−2σ) = 2`.  The accumulated datum grows like `(1+Y)^{2p}` and the
propagator's ray mass decays like `Y^{1-2p}`; the exponents cancel to `2`, which is the square of the
one power of the threshold the card claims.

The two companion facts are that `Y^{-2σ} ≤ 1` past the threshold, and that on a *unit* block the
`L¹` mass never exceeds the `L²` mass — the only place the block's unit length is used.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The exponent identity that lands every tail term on a single power of the threshold. -/
theorem thresholdExponent_le {σ Y : ℝ} (hσ0 : 0 < σ) (hY : 1 ≤ Y) :
    (1 + Y) ^ (2 * (1 / 2 + σ)) * Y ^ (1 - 2 * σ) ≤ 4 ^ (1 / 2 + σ) * Y ^ 2 := by
  set p : ℝ := 1 / 2 + σ with hp
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one hY
  have hp0 : (0 : ℝ) < p := by rw [hp]; linarith
  have h2Y : (1 : ℝ) + Y ≤ 2 * Y := by linarith
  have hmono : (1 + Y) ^ (2 * p) ≤ (2 * Y) ^ (2 * p) :=
    Real.rpow_le_rpow (by linarith) h2Y (by linarith)
  have hsplit : (2 * Y) ^ (2 * p) = 2 ^ (2 * p) * Y ^ (2 * p) :=
    Real.mul_rpow (by norm_num) hY0.le
  have hcombine : Y ^ (2 * p) * Y ^ (1 - 2 * σ) = Y ^ (2 : ℝ) := by
    rw [← Real.rpow_add hY0]
    congr 1
    rw [hp]
    ring
  have hpow2 : Y ^ (2 : ℝ) = Y ^ 2 := Real.rpow_two Y
  have hfour : (2 : ℝ) ^ (2 * p) = 4 ^ p := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by
      rw [Real.rpow_two]; norm_num, ← Real.rpow_mul (by norm_num)]
  calc (1 + Y) ^ (2 * p) * Y ^ (1 - 2 * σ)
      ≤ (2 * Y) ^ (2 * p) * Y ^ (1 - 2 * σ) :=
        mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg hY0.le _)
    _ = 2 ^ (2 * p) * (Y ^ (2 * p) * Y ^ (1 - 2 * σ)) := by rw [hsplit]; ring
    _ = 2 ^ (2 * p) * Y ^ 2 := by rw [hcombine, hpow2]
    _ = 4 ^ p * Y ^ 2 := by rw [hfour]

theorem rpow_neg_le_one {σ Y : ℝ} (hσ0 : 0 < σ) (hY : 1 ≤ Y) : Y ^ (-(2 * σ)) ≤ 1 := by
  refine Real.rpow_le_one_of_one_le_of_nonpos hY ?_
  linarith

variable {X : Type*} [NormedAddCommGroup X]

/-- **On a unit block the `L¹` mass is at most the `L²` mass.** -/
theorem sq_lintegral_enorm_block_le {g : ℝ → X} {m : ℝ}
    (hg : AEMeasurable (fun L => ‖g L‖ₑ) (volume.restrict (Icc m (m + 1)))) :
    (∫⁻ L in Icc m (m + 1), ‖g L‖ₑ) ^ 2 ≤ ∫⁻ L in Icc m (m + 1), ‖g L‖ₑ ^ 2 := by
  have hvol : volume (Icc m (m + 1)) = 1 := by
    rw [Real.volume_Icc]
    norm_num
  have hCS := GaloisForLFunctions.HTGeometry.sq_lintegral_le_measure_mul hg
  rwa [hvol, one_mul] at hCS

end GaloisForLFunctions.RHTower
