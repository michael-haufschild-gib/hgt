import GaloisForLFunctions.HTGeometry.LiteralSourceReflectionRankGaugeLinearization
import GaloisForLFunctions.RHTower.BilateralPrimeAnglePacketSewing

/-!
# Literal-source admissible rank-gauge obstruction

The rank gauge of actual marked source execution is the canonical bilateral sewing eigenhistory.
It algebraically trivializes every nonzero character, but belongs to the moderate source category
exactly at unit character norm.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open _root_.RHTower

/-- The bilateral continuation of the source-visible natural-rank gauge. -/
def literalSourceBilateralRankGauge (z : ℂ) : ℤ → ℂ :=
  bilateralEigenFamily z

/-- On natural ranks, the bilateral gauge is the rank monomial used in source normalization. -/
theorem literalSourceBilateralRankGauge_nat (z : ℂ) (m : ℕ) :
    literalSourceBilateralRankGauge z (m : ℤ) = (z⁻¹) ^ m := by
  rw [literalSourceBilateralRankGauge, bilateralEigenFamily]
  simp [zpow_neg, zpow_natCast]

/-- The bilateral source gauge satisfies the canonical sewing recursion. -/
theorem literalSourceBilateralRankGauge_sewing
    {z : ℂ} (hz : z ≠ 0) (e : ℤ) :
    literalSourceBilateralRankGauge z (e - 1) =
      z * literalSourceBilateralRankGauge z e := by
  simp only [literalSourceBilateralRankGauge, bilateralEigenFamily]
  rw [show -(e - 1) = 1 + -e by ring, zpow_add₀ hz, zpow_one]

/-- The canonical source rank gauge is a nonzero bilateral history. -/
theorem literalSourceBilateralRankGauge_ne_zero (z : ℂ) :
    literalSourceBilateralRankGauge z ≠ 0 := by
  intro hzero
  have hzero0 := congrFun hzero 0
  simp [literalSourceBilateralRankGauge, bilateralEigenFamily] at hzero0

/-- Character inversion lifts to reversal of the same bilateral rank history. -/
theorem literalSourceBilateralRankGauge_inv
    (z : ℂ) (e : ℤ) :
    literalSourceBilateralRankGauge z⁻¹ e =
      literalSourceBilateralRankGauge z (-e) := by
  simp only [literalSourceBilateralRankGauge, bilateralEigenFamily]
  rw [inv_zpow, ← zpow_neg, neg_neg]

/-- The bilateral gauge trivializes each actual normalized depth-12 marked source execution. -/
theorem literalSourceBilateralRankGauge_mul_rankTwelveLiteralSourceMarkedExecution
    {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : z ≠ 0) (j : ℕ) :
    literalSourceBilateralRankGauge z ((12 + j : ℕ) : ℤ) *
        rankTwelveLiteralSourceMarkedExecution p z j =
      1 - z := by
  rw [literalSourceBilateralRankGauge_nat]
  exact rankTwelveLiteralSourceRankAnchoredExecution_eq hp hz j

/-- Algebraic triviality is admissible exactly at unit character norm. -/
theorem bilateralModerate_literalSourceBilateralRankGauge_iff
    {z : ℂ} (hz : z ≠ 0) :
    bilateralModerate (literalSourceBilateralRankGauge z) ↔ ‖z‖ = 1 := by
  constructor
  · intro hmod
    by_contra hnorm
    have hzero := bilateral_shift_eigen_eq_zero_of_norm_ne_one hnorm hmod
      (literalSourceBilateralRankGauge_sewing hz)
    exact literalSourceBilateralRankGauge_ne_zero z hzero
  · intro hnorm
    refine ⟨1, 0, fun e => ?_⟩
    simp [literalSourceBilateralRankGauge, bilateralEigenFamily, norm_zpow, hnorm]

/-- For a prime half-density character, admissibility is exactly the critical line. -/
theorem bilateralModerate_literalSourceHalfDensityRankGauge_iff
    {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    bilateralModerate
        (literalSourceBilateralRankGauge (bilateralHalfDensityCharacter p s)) ↔
      s.re = 1 / 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp
  exact (bilateralModerate_literalSourceBilateralRankGauge_iff
    (bilateralHalfDensityCharacter_ne_zero hp0 s)).trans
      (norm_bilateralHalfDensityCharacter_eq_one_iff hp s)

end

end GaloisForLFunctions.HTGeometry
