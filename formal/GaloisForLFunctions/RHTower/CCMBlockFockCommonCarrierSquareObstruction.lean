import GaloisForLFunctions.RHTower.CCMFirstClockBlockSubdivisionTransfer
import Mathlib.Analysis.Matrix.PosDef

/-!
# Square-capacity law for the CCM block--Fock carrier

The complete odd block--Fock resolvent

`F(r) = r + r^(5 : ℕ) + r^(9 : ℕ) + ... = r / (1 - r^(4 : ℕ))`

is strictly increasing on `0 < r < 1`.  Positivity gives an exact law for the two-node matrix
whose first diagonal and both cross entries equal `F(r)`: its second diagonal capacity is at
least `F(r)`, and that condition is sufficient.

At block scales `q` and `q²`, the aligned-seed overlap is exactly the radius at `q`, while the
natural radial energy at `q²` is strictly smaller.  Consequently the literal matrix obtained by
using the Gamma cross-overlap together with both natural radial diagonals is never positive
semidefinite.  More sharply, an added diagonal counterterm makes it positive semidefinite exactly
when it fills the radial-energy gap.

Everything here is unconditional. Result is direct two-node Cauchy--Schwarz/PSD specialization:
useful exact route audit, not new general positivity law. It rules out one common positive
Hilbert carrier for two separately valid block--Fock interfaces; it does not assert RH.
-/

open scoped Matrix

namespace RHTower

noncomputable section

/-- The complete odd block--Fock resolvent is strictly increasing inside the unit interval. -/
theorem oddBlockFockRadialSum_strictMonoOn_Ioo :
    StrictMonoOn oddBlockFockRadialSum (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [oddBlockFockRadialSum_eq hx.1.le hx.2,
    oddBlockFockRadialSum_eq hy.1.le hy.2]
  have hx4 : x ^ 4 < 1 := pow_lt_one₀ hx.1.le hx.2 (by omega)
  have hy4 : y ^ 4 < 1 := pow_lt_one₀ hy.1.le hy.2 (by omega)
  have hdx : 0 < 1 - x ^ 4 := sub_pos.mpr hx4
  have hdy : 0 < 1 - y ^ 4 := sub_pos.mpr hy4
  apply (div_lt_div_iff₀ hdx hdy).2
  have hfactor :
      y * (1 - x ^ 4) - x * (1 - y ^ 4) =
        (y - x) * (1 + x * y * (y ^ 2 + x * y + x ^ 2)) := by
    ring
  have hnonneg :
      0 ≤ x * y * (y ^ 2 + x * y + x ^ 2) := by
    exact mul_nonneg (mul_nonneg hx.1.le hy.1.le)
      (by nlinarith [sq_nonneg x, sq_nonneg y])
  rw [← sub_pos] at *
  rw [hfactor]
  positivity

/-- Two-node completion with source-forced diagonal and cross entry `F(r)`. -/
def ccmBlockFockSquareCapacityMatrix
    (r capacity : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![oddBlockFockRadialSum r, oddBlockFockRadialSum r;
     oddBlockFockRadialSum r, capacity]

/-- Any positive completion must retain at least the source-forced capacity at the second node. -/
theorem ccmBlockFockSquare_capacity_floor
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {K : Matrix (Fin 2) (Fin 2) ℝ}
    (hK : K.PosSemidef)
    (h00 : K 0 0 = oddBlockFockRadialSum r)
    (h01 : K 0 1 = oddBlockFockRadialSum r)
    (h10 : K 1 0 = oddBlockFockRadialSum r) :
    oddBlockFockRadialSum r ≤ K 1 1 := by
  have hradial : 0 < oddBlockFockRadialSum r := by
    rw [oddBlockFockRadialSum_eq hr0.le hr1]
    exact div_pos hr0 (sub_pos.mpr (pow_lt_one₀ hr0.le hr1 (by omega)))
  have hdet := hK.det_nonneg
  rw [Matrix.det_fin_two, h00, h01, h10] at hdet
  nlinarith

/-- Exact two-node square-capacity law: the capacity floor is also sufficient. -/
theorem ccmBlockFockSquareCapacityMatrix_posSemidef_iff
    {r capacity : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (ccmBlockFockSquareCapacityMatrix r capacity).PosSemidef ↔
      oddBlockFockRadialSum r ≤ capacity := by
  constructor
  · intro hK
    exact ccmBlockFockSquare_capacity_floor hr0 hr1 hK rfl rfl rfl
  · intro hcapacity
    have hradial : 0 < oddBlockFockRadialSum r := by
      rw [oddBlockFockRadialSum_eq hr0.le hr1]
      exact div_pos hr0 (sub_pos.mpr (pow_lt_one₀ hr0.le hr1 (by omega)))
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [ccmBlockFockSquareCapacityMatrix]
    · intro x
      simp [ccmBlockFockSquareCapacityMatrix]
      nlinarith [
        sq_nonneg (Matrix.vecHead x + Matrix.vecHead (Matrix.vecTail x)),
        sq_nonneg (Matrix.vecHead (Matrix.vecTail x))]

/-- Add a counterterm to the smaller, square-scale radial energy. -/
def ccmBlockFockSquareCountertermMatrix
    (r delta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ccmBlockFockSquareCapacityMatrix r
    (oddBlockFockRadialSum (r ^ 2) + delta)

/-- Exact universal repair threshold for the square-scale carrier. -/
theorem ccmBlockFockSquareCountertermMatrix_posSemidef_iff
    {r delta : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (ccmBlockFockSquareCountertermMatrix r delta).PosSemidef ↔
      oddBlockFockRadialSum r - oddBlockFockRadialSum (r ^ 2) ≤ delta := by
  rw [ccmBlockFockSquareCountertermMatrix,
    ccmBlockFockSquareCapacityMatrix_posSemidef_iff hr0 hr1]
  constructor <;> intro h <;> linarith

/-- At scales `q` and `q²`, the aligned block-seed overlap is the radius `q⁻¹ᐟ²`. -/
theorem criticalBlockSeedGram_square
    {q : ℕ} (hq : 2 ≤ q) :
    criticalBlockSeedGram q (q ^ 2) =
      (q : ℝ) ^ (-1 / 2 : ℝ) := by
  have hqposN : 0 < q := lt_of_lt_of_le (by omega) hq
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqposN
  have hqle : q ≤ q ^ 2 := by
    rw [pow_two]
    simpa using Nat.mul_le_mul_left q (show 1 ≤ q by omega)
  have hqleR : (q : ℝ) ≤ (q ^ 2 : ℕ) := by exact_mod_cast hqle
  have hr_sq :
      ((q : ℝ) ^ (-(1 / 2) : ℝ)) ^ 2 = (q : ℝ)⁻¹ := by
    rw [← Real.rpow_mul_natCast hqpos.le]
    norm_num [Real.rpow_neg_one]
  rw [criticalBlockSeedGram_eq, min_eq_left hqleR]
  norm_num [Nat.cast_pow]
  rw [← Real.rpow_pow_comm hqpos.le, hr_sq]
  field_simp

/-- The Gamma cross-overlap on a square pair equals the complete radial energy at the first node. -/
theorem oddBlockFock_of_squareSeedGram
    {q : ℕ} (hq : 2 ≤ q) :
    oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2)) =
      oddBlockFockRadialSum ((q : ℝ) ^ (-1 / 2 : ℝ)) := by
  rw [criticalBlockSeedGram_square hq]

/-- Critical radial coordinate of a positive integer block scale. -/
def ccmNaturalBlockScaleRadius (q : ℕ) : ℝ :=
  (q : ℝ) ^ (-1 / 2 : ℝ)

/-- Natural odd block--Fock diagonal energy at scale `q`. -/
def ccmNaturalBlockRadialEnergy (q : ℕ) : ℝ :=
  oddBlockFockRadialSum (ccmNaturalBlockScaleRadius q)

/-- Squaring a block scale squares its critical radial coordinate. -/
theorem ccmNaturalBlockScaleRadius_square (q : ℕ) :
    ccmNaturalBlockScaleRadius (q ^ 2) =
      ccmNaturalBlockScaleRadius q ^ 2 := by
  rw [ccmNaturalBlockScaleRadius, ccmNaturalBlockScaleRadius, Nat.cast_pow]
  exact (Real.rpow_pow_comm (Nat.cast_nonneg q) (-1 / 2 : ℝ) 2).symm

/-- Literal two-scale matrix combining Gamma cross-overlap with natural radial diagonals. -/
def ccmBlockFockCommonCarrierSquareMatrix (q : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![ccmNaturalBlockRadialEnergy q,
      oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2));
     oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2)),
      ccmNaturalBlockRadialEnergy (q ^ 2)]

/-- Literal square-scale carrier with an added second-diagonal counterterm. -/
def ccmBlockFockCommonCarrierSquareCountertermMatrix
    (q : ℕ) (delta : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ccmNaturalBlockRadialEnergy q,
      oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2));
     oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2)),
      ccmNaturalBlockRadialEnergy (q ^ 2) + delta]

theorem ccmBlockFockCommonCarrierSquareCountertermMatrix_eq
    {q : ℕ} (hq : 2 ≤ q) (delta : ℝ) :
    ccmBlockFockCommonCarrierSquareCountertermMatrix q delta =
      ccmBlockFockSquareCountertermMatrix
        (ccmNaturalBlockScaleRadius q) delta := by
  have hcross :
      oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2)) =
        ccmNaturalBlockRadialEnergy q := by
    rw [criticalBlockSeedGram_square hq]
    rfl
  have hdiag :
      ccmNaturalBlockRadialEnergy (q ^ 2) =
        oddBlockFockRadialSum (ccmNaturalBlockScaleRadius q ^ 2) := by
    rw [ccmNaturalBlockRadialEnergy, ccmNaturalBlockScaleRadius_square]
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact hcross
  · exact hcross
  · simp [ccmBlockFockCommonCarrierSquareCountertermMatrix,
      ccmBlockFockSquareCountertermMatrix,
      ccmBlockFockSquareCapacityMatrix, hdiag]

/-- Exact source-forced counterterm threshold at every integer square pair. -/
theorem ccmBlockFockCommonCarrierSquareCountertermMatrix_posSemidef_iff
    {q : ℕ} (hq : 2 ≤ q) (delta : ℝ) :
    (ccmBlockFockCommonCarrierSquareCountertermMatrix q delta).PosSemidef ↔
      ccmNaturalBlockRadialEnergy q -
        ccmNaturalBlockRadialEnergy (q ^ 2) ≤ delta := by
  have hqoneN : 1 < q := lt_of_lt_of_le (by omega) hq
  have hqone : (1 : ℝ) < q := by exact_mod_cast hqoneN
  have hr0 : 0 < ccmNaturalBlockScaleRadius q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hr1 : ccmNaturalBlockScaleRadius q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hqone (by norm_num)
  rw [ccmBlockFockCommonCarrierSquareCountertermMatrix_eq hq]
  rw [ccmBlockFockSquareCountertermMatrix_posSemidef_iff hr0 hr1]
  simp only [ccmNaturalBlockRadialEnergy, ccmNaturalBlockScaleRadius_square]

/-- Natural diagonal energy strictly decays from `q` to `q²`. -/
theorem ccmNaturalBlockRadialEnergy_square_lt
    {q : ℕ} (hq : 2 ≤ q) :
    ccmNaturalBlockRadialEnergy (q ^ 2) <
      ccmNaturalBlockRadialEnergy q := by
  have hqoneN : 1 < q := lt_of_lt_of_le (by omega) hq
  have hqone : (1 : ℝ) < q := by exact_mod_cast hqoneN
  have hr0 : 0 < ccmNaturalBlockScaleRadius q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hr1 : ccmNaturalBlockScaleRadius q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hqone (by norm_num)
  have hr2pos : 0 < ccmNaturalBlockScaleRadius q ^ 2 := sq_pos_of_pos hr0
  have hr2lt :
      ccmNaturalBlockScaleRadius q ^ 2 <
        ccmNaturalBlockScaleRadius q := by
    nlinarith
  have hr2one : ccmNaturalBlockScaleRadius q ^ 2 < 1 := hr2lt.trans hr1
  rw [ccmNaturalBlockRadialEnergy, ccmNaturalBlockScaleRadius_square]
  exact oddBlockFockRadialSum_strictMonoOn_Ioo
    ⟨hr2pos, hr2one⟩ ⟨hr0, hr1⟩ hr2lt

/-- Minimal correction required by the square-capacity law. -/
def ccmBlockFockSquareCapacityDebt (q : ℕ) : ℝ :=
  ccmNaturalBlockRadialEnergy q -
    ccmNaturalBlockRadialEnergy (q ^ 2)

/-- Exact determinant law: rank-two positivity is measured by counterterm surplus above debt. -/
theorem ccmBlockFockCommonCarrierSquareCountertermMatrix_det
    {q : ℕ} (hq : 2 ≤ q) (delta : ℝ) :
    (ccmBlockFockCommonCarrierSquareCountertermMatrix q delta).det =
      ccmNaturalBlockRadialEnergy q *
        (delta - ccmBlockFockSquareCapacityDebt q) := by
  have hcross :
      oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2)) =
        ccmNaturalBlockRadialEnergy q := by
    rw [criticalBlockSeedGram_square hq]
    rfl
  simp [ccmBlockFockCommonCarrierSquareCountertermMatrix,
    Matrix.det_fin_two, ccmBlockFockSquareCapacityDebt, hcross]
  ring

/-- At the exact capacity threshold, the repaired square pair collapses to one rank-one ray. -/
theorem ccmBlockFockCommonCarrierSquare_minimalRepair_eq
    {q : ℕ} (hq : 2 ≤ q) :
    ccmBlockFockCommonCarrierSquareCountertermMatrix q
        (ccmBlockFockSquareCapacityDebt q) =
      !![ccmNaturalBlockRadialEnergy q, ccmNaturalBlockRadialEnergy q;
         ccmNaturalBlockRadialEnergy q, ccmNaturalBlockRadialEnergy q] := by
  have hcross :
      oddBlockFockRadialSum (criticalBlockSeedGram q (q ^ 2)) =
        ccmNaturalBlockRadialEnergy q := by
    rw [criticalBlockSeedGram_square hq]
    rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ccmBlockFockCommonCarrierSquareCountertermMatrix,
      ccmBlockFockSquareCapacityDebt, hcross]

/-- The minimal source correction is positive semidefinite. -/
theorem ccmBlockFockCommonCarrierSquare_minimalRepair_posSemidef
    {q : ℕ} (hq : 2 ≤ q) :
    (ccmBlockFockCommonCarrierSquareCountertermMatrix q
      (ccmBlockFockSquareCapacityDebt q)).PosSemidef := by
  rw [ccmBlockFockCommonCarrierSquareCountertermMatrix_posSemidef_iff
    hq (ccmBlockFockSquareCapacityDebt q)]
  exact le_rfl

/-- Minimal repair has zero determinant, so it supplies no nontrivial square innovation. -/
theorem ccmBlockFockCommonCarrierSquare_minimalRepair_det
    {q : ℕ} (hq : 2 ≤ q) :
    (ccmBlockFockCommonCarrierSquareCountertermMatrix q
      (ccmBlockFockSquareCapacityDebt q)).det = 0 := by
  rw [ccmBlockFockCommonCarrierSquare_minimalRepair_eq hq]
  simp [Matrix.det_fin_two]

/-- Squaring preserves the von Mangoldt mark, including off-support inputs. -/
theorem vonMangoldt_square (q : ℕ) :
    ArithmeticFunction.vonMangoldt (q ^ 2) =
      ArithmeticFunction.vonMangoldt q := by
  simpa using
    ArithmeticFunction.vonMangoldt_apply_pow (n := q) (by omega : 2 ≠ 0)

/-- Critical source mass lost under the mark-preserving squaring map. -/
def ccmCriticalMellinSquareInnovation (q : ℕ) : ℝ :=
  criticalMellinAtomWeight q -
    criticalMellinAtomWeight (q ^ 2)

/-- Higher-grade block--Fock source mass lost under the same squaring map. -/
def ccmBlockFockTailSquareInnovation (q : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt q *
    (oddBlockFockTail (ccmNaturalBlockScaleRadius q) -
      oddBlockFockTail (ccmNaturalBlockScaleRadius q ^ 2))

/-- The critical mass at `q²` is the unchanged von Mangoldt mark times the squared radius. -/
theorem criticalMellinAtomWeight_square (q : ℕ) :
    criticalMellinAtomWeight (q ^ 2) =
      ArithmeticFunction.vonMangoldt q *
        ccmNaturalBlockScaleRadius q ^ 2 := by
  rw [criticalMellinAtomWeight, vonMangoldt_square,
    ccmNaturalBlockScaleRadius]
  rw [Nat.cast_pow]
  rw [← Real.rpow_pow_comm (Nat.cast_nonneg q)]
  ring

/-- Closed form of the higher odd block--Fock tail. -/
theorem oddBlockFockTail_eq
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    oddBlockFockTail r = r ^ 5 / (1 - r ^ 4) := by
  rw [oddBlockFockTail, oddBlockFockRadialSum_eq hr0 hr1]
  have hden : 1 - r ^ 4 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (pow_lt_one₀ hr0 hr1 (by omega)))
  field_simp [hden]
  ring

/-- The higher odd block--Fock tail is strictly increasing inside the unit interval. -/
theorem oddBlockFockTail_strictMonoOn_Ioo :
    StrictMonoOn oddBlockFockTail (Set.Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [oddBlockFockTail_eq hx.1.le hx.2,
    oddBlockFockTail_eq hy.1.le hy.2]
  have hx4 : x ^ 4 < 1 := pow_lt_one₀ hx.1.le hx.2 (by omega)
  have hy4 : y ^ 4 < 1 := pow_lt_one₀ hy.1.le hy.2 (by omega)
  have hdx : 0 < 1 - x ^ 4 := sub_pos.mpr hx4
  have hdy : 0 < 1 - y ^ 4 := sub_pos.mpr hy4
  have h5 : x ^ 5 < y ^ 5 :=
    pow_lt_pow_left₀ hxy hx.1.le (by omega)
  have h4 : x ^ 4 < y ^ 4 :=
    pow_lt_pow_left₀ hxy hx.1.le (by omega)
  have hdenlt : 1 - y ^ 4 < 1 - x ^ 4 := by linarith
  calc
    x ^ 5 / (1 - x ^ 4) <
        y ^ 5 / (1 - x ^ 4) :=
      div_lt_div_of_pos_right h5 hdx
    _ < y ^ 5 / (1 - y ^ 4) := by
      apply (div_lt_div_iff₀ hdx hdy).2
      exact mul_lt_mul_of_pos_left hdenlt (pow_pos hy.1 5)

/-- **Source fracture law.**  The marked square-capacity debt is exactly the sum of the
critical prime-weight innovation and the higher block--Fock tail innovation. -/
theorem ccmBlockFock_squareCapacity_source_fracture (q : ℕ) :
    ArithmeticFunction.vonMangoldt q *
        ccmBlockFockSquareCapacityDebt q =
      ccmCriticalMellinSquareInnovation q +
        ccmBlockFockTailSquareInnovation q := by
  unfold ccmBlockFockSquareCapacityDebt
    ccmCriticalMellinSquareInnovation
    ccmBlockFockTailSquareInnovation
  simp only [ccmNaturalBlockRadialEnergy,
    ccmNaturalBlockScaleRadius_square]
  rw [criticalMellinAtomWeight_square q,
    criticalMellinAtomWeight]
  rw [show (q : ℝ) ^ (-1 / 2 : ℝ) =
    ccmNaturalBlockScaleRadius q by rfl]
  rw [oddBlockFockTail, oddBlockFockTail]
  ring

/-- On an actual von Mangoldt source atom, the canonical square innovations normalize to exactly
the minimal carrier debt.  There is no source surplus in this decomposition. -/
theorem ccmBlockFock_normalizedSquareInnovations_eq_capacityDebt
    {q : ℕ} (hΛ : ArithmeticFunction.vonMangoldt q ≠ 0) :
    (ccmCriticalMellinSquareInnovation q +
        ccmBlockFockTailSquareInnovation q) /
        ArithmeticFunction.vonMangoldt q =
      ccmBlockFockSquareCapacityDebt q := by
  rw [← ccmBlockFock_squareCapacity_source_fracture q]
  exact mul_div_cancel_left₀ _ hΛ

/-- The canonical von Mangoldt square innovations repair positivity but leave determinant zero. -/
theorem ccmBlockFock_normalizedSquareInnovations_repair_det
    {q : ℕ} (hq : 2 ≤ q)
    (hΛ : ArithmeticFunction.vonMangoldt q ≠ 0) :
    (ccmBlockFockCommonCarrierSquareCountertermMatrix q
      ((ccmCriticalMellinSquareInnovation q +
          ccmBlockFockTailSquareInnovation q) /
        ArithmeticFunction.vonMangoldt q)).det = 0 := by
  rw [ccmBlockFockCommonCarrierSquareCountertermMatrix_det hq,
    ccmBlockFock_normalizedSquareInnovations_eq_capacityDebt hΛ]
  ring

theorem ccmCriticalMellinSquareInnovation_nonneg
    {q : ℕ} (hq : 2 ≤ q) :
    0 ≤ ccmCriticalMellinSquareInnovation q := by
  rw [ccmCriticalMellinSquareInnovation, criticalMellinAtomWeight,
    criticalMellinAtomWeight_square q]
  rw [show (q : ℝ) ^ (-1 / 2 : ℝ) =
    ccmNaturalBlockScaleRadius q by rfl]
  have hr0 : 0 < ccmNaturalBlockScaleRadius q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hr1 : ccmNaturalBlockScaleRadius q < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast (show 1 < q by omega)
    · norm_num
  rw [mul_comm (ccmNaturalBlockScaleRadius q)
    (ArithmeticFunction.vonMangoldt q)]
  have hfac :
      ArithmeticFunction.vonMangoldt q *
          ccmNaturalBlockScaleRadius q -
        ArithmeticFunction.vonMangoldt q *
          ccmNaturalBlockScaleRadius q ^ 2 =
        ArithmeticFunction.vonMangoldt q *
          (ccmNaturalBlockScaleRadius q -
            ccmNaturalBlockScaleRadius q ^ 2) := by
    ring
  rw [hfac]
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (sub_nonneg.mpr (by nlinarith))

theorem ccmBlockFockTailSquareInnovation_nonneg
    {q : ℕ} (hq : 2 ≤ q) :
    0 ≤ ccmBlockFockTailSquareInnovation q := by
  rw [ccmBlockFockTailSquareInnovation]
  have hr0 : 0 < ccmNaturalBlockScaleRadius q :=
    Real.rpow_pos_of_pos (by positivity) _
  have hr1 : ccmNaturalBlockScaleRadius q < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast (show 1 < q by omega)
    · norm_num
  have hr2pos : 0 < ccmNaturalBlockScaleRadius q ^ 2 :=
    sq_pos_of_pos hr0
  have hr2lt :
      ccmNaturalBlockScaleRadius q ^ 2 <
        ccmNaturalBlockScaleRadius q := by
    nlinarith
  have hr2one : ccmNaturalBlockScaleRadius q ^ 2 < 1 := hr2lt.trans hr1
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (sub_nonneg.mpr (oddBlockFockTail_strictMonoOn_Ioo
      ⟨hr2pos, hr2one⟩ ⟨hr0, hr1⟩ hr2lt).le)

/-- Iterated mark-preserving square orbit of an integer source atom. -/
def ccmIteratedSquare (q : ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => ccmIteratedSquare q n ^ 2

@[simp] theorem ccmIteratedSquare_zero (q : ℕ) :
    ccmIteratedSquare q 0 = q := rfl

@[simp] theorem ccmIteratedSquare_succ (q n : ℕ) :
    ccmIteratedSquare q (n + 1) =
      ccmIteratedSquare q n ^ 2 := rfl

/-- Finite square-orbit conservation: critical mass is positive innovation plus the residual
mass deeper on the same von Mangoldt-marked orbit. -/
theorem sum_ccmCriticalMellinSquareInnovation_iteratedSquare
    (q N : ℕ) :
    ∑ j ∈ Finset.range N,
        ccmCriticalMellinSquareInnovation (ccmIteratedSquare q j) =
      criticalMellinAtomWeight q -
        criticalMellinAtomWeight (ccmIteratedSquare q N) := by
  simpa only [ccmCriticalMellinSquareInnovation,
    ccmIteratedSquare_zero, ccmIteratedSquare_succ] using
      Finset.sum_range_sub'
        (fun j => criticalMellinAtomWeight (ccmIteratedSquare q j)) N

/-- **Square obstruction.**  The two natural block--Fock interfaces cannot be one positive Gram. -/
theorem ccmBlockFockCommonCarrierSquareMatrix_not_posSemidef
    {q : ℕ} (hq : 2 ≤ q) :
    ¬ (ccmBlockFockCommonCarrierSquareMatrix q).PosSemidef := by
  have hgap := ccmNaturalBlockRadialEnergy_square_lt hq
  have hzero :
      ccmBlockFockCommonCarrierSquareMatrix q =
        ccmBlockFockCommonCarrierSquareCountertermMatrix q 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ccmBlockFockCommonCarrierSquareMatrix,
        ccmBlockFockCommonCarrierSquareCountertermMatrix]
  rw [hzero,
    ccmBlockFockCommonCarrierSquareCountertermMatrix_posSemidef_iff hq 0]
  linarith

end

end RHTower
