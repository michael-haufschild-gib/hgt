import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenC1Schedule
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIISelection

/-!
# Scale bookkeeping for Matomäki--Teräväinen Proposition 2.2

This file formalizes the numerical groupings in the proof of Proposition 2.2.  The rounded
Legendre variable is subpower.  A small product of iterated prime-block scales gives Type I for the
third minorant term and Type I/II for the fourth; a large product is handled by the Type-II
selection theorem.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- Products of two quantities below powers of the same base add their exponents. -/
theorem mul_le_rpow_add_of_le
    {X a b r s : ℝ} (hX : 1 ≤ X) (_ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ X ^ r) (hb : b ≤ X ^ s) :
    a * b ≤ X ^ (r + s) := by
  calc
    a * b ≤ X ^ r * b := mul_le_mul_of_nonneg_right ha hb0
    _ ≤ X ^ r * X ^ s :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (zero_le_one.trans hX) r)
    _ = X ^ (r + s) := (Real.rpow_add (zero_lt_one.trans_le hX) r s).symm

/-- The paper's rounded Legendre cutoff `D` is eventually below every fixed positive power. -/
theorem eventually_mtTruncationNat_le_rpow_quarter
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (mtTruncationNat X : ℝ) ≤ X ^ (ε / 4) := by
  have hll := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (4 / ε)
  filter_upwards [hll, Filter.eventually_gt_atTop (Real.exp 1)] with X hllX hX
  change 4 / ε ≤ Real.log (Real.log X) at hllX
  have hXone : (1 : ℝ) < X := by
    have hone : (1 : ℝ) < Real.exp 1 := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1)
    exact hone.trans hX
  have hL : 0 < Real.log X := Real.log_pos hXone
  have hllPos : 0 < Real.log (Real.log X) := by
    have hfourDiv : 0 < 4 / ε := div_pos (by norm_num) hε
    exact hfourDiv.trans_le hllX
  have hratio : Real.log X / Real.log (Real.log X) ≤ (ε / 4) * Real.log X := by
    apply (div_le_iff₀ hllPos).2
    have hε4 : 4 ≤ ε * Real.log (Real.log X) := by
      have := (div_le_iff₀ hε).1 hllX
      nlinarith
    nlinarith
  calc
    (mtTruncationNat X : ℝ) ≤ mtTruncation X := by
      exact Nat.floor_le (Real.exp_nonneg _)
    _ = Real.exp (Real.log X / Real.log (Real.log X)) := rfl
    _ ≤ Real.exp ((ε / 4) * Real.log X) := Real.exp_le_exp.mpr hratio
    _ = X ^ (ε / 4) := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hXone)]
      congr 1
      ring

/-- Small iterated block product gives the source Type-I long coefficient scale. -/
theorem matomakiTeravainen_small_product_typeI_scale
    {X ε E Q₁ Q₂ P : ℝ}
    (hX : 1 ≤ X) (hε : 0 ≤ ε)
    (hE0 : 0 ≤ E) (hQ₁0 : 0 ≤ Q₁) (hQ₂0 : 0 ≤ Q₂) (hP0 : 0 ≤ P)
    (hE : E ≤ X ^ (ε / 4))
    (hQ₁ : Q₁ ≤ X ^ (1 / 4 - 2 * ε))
    (hQ₂ : Q₂ ≤ X ^ (1 / 4 - 2 * ε))
    (hP : P ≤ X ^ (ε / 2)) :
    E * Q₁ * Q₂ * P ≤ X ^ (1 / 2 + ε) := by
  have hEQ₁ := mul_le_rpow_add_of_le hX hE0 hQ₁0 hE hQ₁
  have hEQ₁0 : 0 ≤ E * Q₁ := mul_nonneg hE0 hQ₁0
  have hEQ₁Q₂ := mul_le_rpow_add_of_le hX hEQ₁0 hQ₂0 hEQ₁ hQ₂
  have hEQ₁Q₂0 : 0 ≤ E * Q₁ * Q₂ := mul_nonneg hEQ₁0 hQ₂0
  have hall := mul_le_rpow_add_of_le hX hEQ₁Q₂0 hP0 hEQ₁Q₂ hP
  exact hall.trans (Real.rpow_le_rpow_of_exponent_le hX (by linarith))

/-- Fourth minorant term grouping `M₁=E Q₂ Q₃`, `M₂=Q₁ P` has Type-I/II scales. -/
theorem matomakiTeravainen_small_product_typeI_II_scales
    {X ε E Q₁ Q₂ Q₃ P : ℝ}
    (hX : 1 ≤ X) (hε : 0 ≤ ε)
    (hE0 : 0 ≤ E) (hQ₁0 : 0 ≤ Q₁) (_hQ₂0 : 0 ≤ Q₂)
    (hQ₃0 : 0 ≤ Q₃) (hP0 : 0 ≤ P)
    (hE : E ≤ X ^ (ε / 4))
    (hQ₁ : Q₁ ≤ X ^ (1 / 4 - 2 * ε))
    (hQ₃Q₂ : Q₃ ≤ Q₂)
    (hgeometry : Q₁ * Q₂ ^ 4 ≤ X ^ (1 - 2 * ε))
    (hP : P ≤ X ^ (ε / 2)) :
    (E * Q₂ * Q₃) ^ 2 * (Q₁ * P) ≤ X ^ (1 - ε) ∧
      Q₁ * P ≤ X ^ (1 / 4 - ε) := by
  have hE2 : E ^ 2 ≤ X ^ (ε / 2) := by
    calc
      E ^ 2 ≤ (X ^ (ε / 4)) ^ 2 := pow_le_pow_left₀ hE0 hE 2
      _ = (X ^ (ε / 4)) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = X ^ ((ε / 4) * 2) :=
        (Real.rpow_mul (zero_le_one.trans hX) (ε / 4) 2).symm
      _ = X ^ (ε / 2) := by congr 1; ring
  have hE2P := mul_le_rpow_add_of_le hX (sq_nonneg E) hP0 hE2 hP
  have hE2Pε : E ^ 2 * P ≤ X ^ ε :=
    hE2P.trans (Real.rpow_le_rpow_of_exponent_le hX (by ring_nf; rfl))
  have hQ₃sq : Q₃ ^ 2 ≤ Q₂ ^ 2 := pow_le_pow_left₀ hQ₃0 hQ₃Q₂ 2
  have hQ₂sq0 : 0 ≤ Q₂ ^ 2 := sq_nonneg Q₂
  have hQ₁0' : 0 ≤ Q₁ := hQ₁0
  have hgeom' : Q₁ * Q₂ ^ 2 * Q₃ ^ 2 ≤ Q₁ * Q₂ ^ 4 := by
    calc
      Q₁ * Q₂ ^ 2 * Q₃ ^ 2 ≤ Q₁ * Q₂ ^ 2 * Q₂ ^ 2 :=
        mul_le_mul_of_nonneg_left hQ₃sq (mul_nonneg hQ₁0' hQ₂sq0)
      _ = Q₁ * Q₂ ^ 4 := by ring
  have hbase : Q₁ * Q₂ ^ 2 * Q₃ ^ 2 ≤ X ^ (1 - 2 * ε) := hgeom'.trans hgeometry
  have hmain := mul_le_rpow_add_of_le hX
    (mul_nonneg (sq_nonneg E) hP0)
    (mul_nonneg (mul_nonneg hQ₁0 hQ₂sq0) (sq_nonneg Q₃)) hE2Pε hbase
  have hM₂ := mul_le_rpow_add_of_le hX hQ₁0 hP0 hQ₁ hP
  constructor
  · calc
      (E * Q₂ * Q₃) ^ 2 * (Q₁ * P) =
          (E ^ 2 * P) * (Q₁ * Q₂ ^ 2 * Q₃ ^ 2) := by ring
      _ ≤ X ^ (ε + (1 - 2 * ε)) := hmain
      _ = X ^ (1 - ε) := by congr 1; ring
  · exact hM₂.trans (Real.rpow_le_rpow_of_exponent_le hX (by linarith))

end

end RHTower.Sieve
