import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortEnergyMain
import GaloisForLFunctions.RHTower.Sieve.NatDivLogPowerEndpointError

/-!
# Continuous main term for the origin-based Barban--Vehov energy

This replaces only `log (X / lcm(q,r) + 1)` by the literal continuous quotient
`log (X / lcm(q,r))`.  All three harmonic-moment constants are retained.  The endpoint error is
uniform after the outer `1/lcm(q,r)` factor and therefore sums to the same `O(M²/X)` scale as the
preceding discrete-kernel replacement.
-/

open Finset
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Continuous-quotient main term of the origin-based harmonic lcm fibre. -/
def barbanVehovShortHarmonicKernelContinuous (X q r : ℕ) : ℝ :=
  1 / (Nat.lcm q r : ℝ) *
    (Real.log ((X : ℝ) / (Nat.lcm q r : ℝ)) + harmonicLogMomentTotalConstant 0)

/-- Continuous-quotient main term of the first origin-based log lcm fibre. -/
def barbanVehovShortFirstLogKernelContinuous (X q r : ℕ) : ℝ :=
  let e := Nat.lcm q r
  let z := Real.log ((X : ℝ) / (e : ℝ))
  1 / (e : ℝ) *
    (Real.log (((e / r : ℕ) : ℝ)) * (z + harmonicLogMomentTotalConstant 0) +
      (z ^ 2 / 2 + harmonicLogMomentTotalConstant 1))

/-- Continuous-quotient main term of the second origin-based log lcm fibre. -/
def barbanVehovShortSecondLogKernelContinuous (X q r : ℕ) : ℝ :=
  let e := Nat.lcm q r
  let z := Real.log ((X : ℝ) / (e : ℝ))
  let a := Real.log (((e / q : ℕ) : ℝ))
  let b := Real.log (((e / r : ℕ) : ℝ))
  1 / (e : ℝ) *
    (a * b * (z + harmonicLogMomentTotalConstant 0) +
      (a + b) * (z ^ 2 / 2 + harmonicLogMomentTotalConstant 1) +
      (z ^ 3 / 3 + harmonicLogMomentTotalConstant 2))

private theorem abs_log_lcm_div_right_le
    {X q r : ℕ} (hq : 0 < q) (hr : 0 < r) (heX : Nat.lcm q r ≤ X) :
    |Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| ≤
      Real.log ((X + 1 : ℕ) : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have hrle : r ≤ Nat.lcm q r := Nat.le_of_dvd he (Nat.dvd_lcm_right q r)
  have hone : 1 ≤ Nat.lcm q r / r := (Nat.one_le_div_iff hr).mpr hrle
  have hupper : Nat.lcm q r / r ≤ X + 1 :=
    (Nat.div_le_self _ _).trans (heX.trans (Nat.le_succ X))
  have hnn : 0 ≤ Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast hone)
  rw [abs_of_nonneg hnn]
  exact Real.log_le_log (by exact_mod_cast hone) (by exact_mod_cast hupper)

private theorem abs_log_lcm_div_left_le
    {X q r : ℕ} (hq : 0 < q) (hr : 0 < r) (heX : Nat.lcm q r ≤ X) :
    |Real.log (((Nat.lcm q r / q : ℕ) : ℝ))| ≤
      Real.log ((X + 1 : ℕ) : ℝ) := by
  simpa only [Nat.lcm_comm] using
    abs_log_lcm_div_right_le (X := X) hr hq (by simpa only [Nat.lcm_comm] using heX)

theorem abs_barbanVehovShortHarmonicKernelMain_sub_continuous_le
    {X q r : ℕ} (hX : 0 < X) (hq : 0 < q) (hr : 0 < r) :
    |barbanVehovShortHarmonicKernelMain X q r -
        barbanVehovShortHarmonicKernelContinuous X q r| ≤ 1 / (X : ℝ) := by
  let e := Nat.lcm q r
  have he : 0 < e := Nat.lcm_pos hq hr
  have hgap :
      |Real.log (((X / e : ℕ) : ℝ) + 1) - Real.log ((X : ℝ) / (e : ℝ))| ≤
        (e : ℝ) / (X : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      abs_log_natDiv_add_one_sub_log_div_le hX he
  rw [barbanVehovShortHarmonicKernelMain, barbanVehovShortHarmonicKernelContinuous]
  simp only [harmonicLogMomentPrimitive]
  norm_num
  change |(e : ℝ)⁻¹ * (Real.log (((X / e : ℕ) : ℝ) + 1) +
      harmonicLogMomentTotalConstant 0) -
    (e : ℝ)⁻¹ * (Real.log ((X : ℝ) / (e : ℝ)) +
      harmonicLogMomentTotalConstant 0)| ≤ (X : ℝ)⁻¹
  rw [← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (e : ℝ)⁻¹)]
  calc
    (e : ℝ)⁻¹ *
        |(Real.log (((X / e : ℕ) : ℝ) + 1) + harmonicLogMomentTotalConstant 0) -
          (Real.log ((X : ℝ) / (e : ℝ)) + harmonicLogMomentTotalConstant 0)| =
      (e : ℝ)⁻¹ *
        |Real.log (((X / e : ℕ) : ℝ) + 1) - Real.log ((X : ℝ) / (e : ℝ))| := by
          congr 1
          ring_nf
    _ ≤ (e : ℝ)⁻¹ * ((e : ℝ) / (X : ℝ)) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    _ = (X : ℝ)⁻¹ := by field_simp

theorem abs_barbanVehovShortFirstLogKernelMain_sub_continuous_le
    {X q r : ℕ} (hX : 0 < X) (hq : 0 < q) (hr : 0 < r)
    (heX : Nat.lcm q r ≤ X) :
    |barbanVehovShortFirstLogKernelMain X q r -
        barbanVehovShortFirstLogKernelContinuous X q r| ≤
      2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / r : ℕ) : ℝ))
  let x := Real.log ((X : ℝ) / (e : ℝ))
  let y := Real.log (((X / e : ℕ) : ℝ) + 1)
  let K := Real.log ((X + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have ha : |a| ≤ K := by
    simpa only [a, K] using
      abs_log_lcm_div_right_le (X := X) hq hr heX
  have hK0 : 0 ≤ K := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X + 1))
  have h0 : |y - x| ≤ (e : ℝ) / (X : ℝ) := by
    simpa [x, y] using abs_log_natDiv_add_one_sub_log_div_le hX he
  have h1 : |y ^ 2 - x ^ 2| ≤ 2 * K * ((e : ℝ) / (X : ℝ)) := by
    simpa [x, y, K] using abs_log_natDiv_add_one_sq_sub_log_div_sq_le hX he heX
  rw [barbanVehovShortFirstLogKernelMain, barbanVehovShortFirstLogKernelContinuous]
  simp only [harmonicLogMomentPrimitive]
  norm_num
  change |(e : ℝ)⁻¹ *
      (a * (y + harmonicLogMomentTotalConstant 0) +
        (y ^ 2 / 2 + harmonicLogMomentTotalConstant 1)) -
    (e : ℝ)⁻¹ *
      (a * (x + harmonicLogMomentTotalConstant 0) +
        (x ^ 2 / 2 + harmonicLogMomentTotalConstant 1))| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (e : ℝ)⁻¹)]
  have hinner :
      |(a * (y + harmonicLogMomentTotalConstant 0) +
          (y ^ 2 / 2 + harmonicLogMomentTotalConstant 1)) -
        (a * (x + harmonicLogMomentTotalConstant 0) +
          (x ^ 2 / 2 + harmonicLogMomentTotalConstant 1))| ≤
        2 * K * ((e : ℝ) / (X : ℝ)) := by
    calc
      _ = |a * (y - x) + (y ^ 2 - x ^ 2) / 2| := by
        congr 1
        ring
      _ ≤ |a| * |y - x| + |y ^ 2 - x ^ 2| / 2 := by
        calc
          _ ≤ |a * (y - x)| + |(y ^ 2 - x ^ 2) / 2| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_div]; norm_num
      _ ≤ K * ((e : ℝ) / (X : ℝ)) +
          (2 * K * ((e : ℝ) / (X : ℝ))) / 2 :=
        add_le_add (mul_le_mul ha h0 (abs_nonneg _) hK0) (div_le_div_of_nonneg_right h1 (by norm_num))
      _ = 2 * K * ((e : ℝ) / (X : ℝ)) := by ring
  calc
    (e : ℝ)⁻¹ *
        |(a * (y + harmonicLogMomentTotalConstant 0) +
            (y ^ 2 / 2 + harmonicLogMomentTotalConstant 1)) -
          (a * (x + harmonicLogMomentTotalConstant 0) +
            (x ^ 2 / 2 + harmonicLogMomentTotalConstant 1))| ≤
      (e : ℝ)⁻¹ * (2 * K * ((e : ℝ) / (X : ℝ))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 2 * Real.log ((X : ℝ) + 1) / (X : ℝ) := by
      dsimp only [K]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp

theorem abs_barbanVehovShortSecondLogKernelMain_sub_continuous_le
    {X q r : ℕ} (hX : 0 < X) (hq : 0 < q) (hr : 0 < r)
    (heX : Nat.lcm q r ≤ X) :
    |barbanVehovShortSecondLogKernelMain X q r -
        barbanVehovShortSecondLogKernelContinuous X q r| ≤
      4 * Real.log ((X + 1 : ℕ) : ℝ) ^ 2 / (X : ℝ) := by
  let e := Nat.lcm q r
  let a := Real.log (((e / q : ℕ) : ℝ))
  let b := Real.log (((e / r : ℕ) : ℝ))
  let x := Real.log ((X : ℝ) / (e : ℝ))
  let y := Real.log (((X / e : ℕ) : ℝ) + 1)
  let K := Real.log ((X + 1 : ℕ) : ℝ)
  have he : 0 < e := Nat.lcm_pos hq hr
  have ha : |a| ≤ K := by
    simpa only [a, K] using
      abs_log_lcm_div_left_le (X := X) hq hr heX
  have hb : |b| ≤ K := by
    simpa only [b, K] using
      abs_log_lcm_div_right_le (X := X) hq hr heX
  have hK0 : 0 ≤ K := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X + 1))
  have hab : |a * b| ≤ K ^ 2 := by
    rw [abs_mul]
    nlinarith [mul_le_mul ha hb (abs_nonneg b) hK0]
  have habadd : |a + b| ≤ 2 * K := (abs_add_le a b).trans (by linarith)
  have h0 : |y - x| ≤ (e : ℝ) / (X : ℝ) := by
    simpa [x, y] using abs_log_natDiv_add_one_sub_log_div_le hX he
  have h1 : |y ^ 2 - x ^ 2| ≤ 2 * K * ((e : ℝ) / (X : ℝ)) := by
    simpa [x, y, K] using abs_log_natDiv_add_one_sq_sub_log_div_sq_le hX he heX
  have h2 : |y ^ 3 - x ^ 3| ≤ 3 * K ^ 2 * ((e : ℝ) / (X : ℝ)) := by
    simpa [x, y, K] using abs_log_natDiv_add_one_cube_sub_log_div_cube_le hX he heX
  rw [barbanVehovShortSecondLogKernelMain, barbanVehovShortSecondLogKernelContinuous]
  simp only [harmonicLogMomentPrimitive]
  norm_num
  change |(e : ℝ)⁻¹ *
      (a * b * (y + harmonicLogMomentTotalConstant 0) +
        (a + b) * (y ^ 2 / 2 + harmonicLogMomentTotalConstant 1) +
        (y ^ 3 / 3 + harmonicLogMomentTotalConstant 2)) -
    (e : ℝ)⁻¹ *
      (a * b * (x + harmonicLogMomentTotalConstant 0) +
        (a + b) * (x ^ 2 / 2 + harmonicLogMomentTotalConstant 1) +
        (x ^ 3 / 3 + harmonicLogMomentTotalConstant 2))| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (e : ℝ)⁻¹)]
  have hinner :
      |(a * b * (y + harmonicLogMomentTotalConstant 0) +
          (a + b) * (y ^ 2 / 2 + harmonicLogMomentTotalConstant 1) +
          (y ^ 3 / 3 + harmonicLogMomentTotalConstant 2)) -
        (a * b * (x + harmonicLogMomentTotalConstant 0) +
          (a + b) * (x ^ 2 / 2 + harmonicLogMomentTotalConstant 1) +
          (x ^ 3 / 3 + harmonicLogMomentTotalConstant 2))| ≤
        4 * K ^ 2 * ((e : ℝ) / (X : ℝ)) := by
    calc
      _ = |(a * b * (y - x) + (a + b) * ((y ^ 2 - x ^ 2) / 2)) +
          (y ^ 3 - x ^ 3) / 3| := by
        congr 1
        ring
      _ ≤ (|a * b| * |y - x| + |a + b| * (|y ^ 2 - x ^ 2| / 2)) +
          |y ^ 3 - x ^ 3| / 3 := by
        calc
          _ ≤ |a * b * (y - x) + (a + b) * ((y ^ 2 - x ^ 2) / 2)| +
              |(y ^ 3 - x ^ 3) / 3| := abs_add_le _ _
          _ ≤ (|a * b * (y - x)| + |(a + b) * ((y ^ 2 - x ^ 2) / 2)|) +
              |(y ^ 3 - x ^ 3) / 3| := add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by
            simp only [abs_mul, abs_div]
            norm_num
      _ ≤ (K ^ 2 * ((e : ℝ) / (X : ℝ)) +
            (2 * K) * ((2 * K * ((e : ℝ) / (X : ℝ))) / 2)) +
          (3 * K ^ 2 * ((e : ℝ) / (X : ℝ))) / 3 := by
        exact add_le_add
          (add_le_add
            (mul_le_mul hab h0 (abs_nonneg _) (sq_nonneg K))
            (mul_le_mul habadd (div_le_div_of_nonneg_right h1 (by norm_num))
              (by positivity) (by positivity)))
          (div_le_div_of_nonneg_right h2 (by norm_num))
      _ = 4 * K ^ 2 * ((e : ℝ) / (X : ℝ)) := by ring
  calc
    (e : ℝ)⁻¹ *
        |(a * b * (y + harmonicLogMomentTotalConstant 0) +
            (a + b) * (y ^ 2 / 2 + harmonicLogMomentTotalConstant 1) +
            (y ^ 3 / 3 + harmonicLogMomentTotalConstant 2)) -
          (a * b * (x + harmonicLogMomentTotalConstant 0) +
            (a + b) * (x ^ 2 / 2 + harmonicLogMomentTotalConstant 1) +
            (x ^ 3 / 3 + harmonicLogMomentTotalConstant 2))| ≤
      (e : ℝ)⁻¹ * (4 * K ^ 2 * ((e : ℝ) / (X : ℝ))) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 4 * Real.log ((X : ℝ) + 1) ^ 2 / (X : ℝ) := by
      dsimp only [K]
      rw [Nat.cast_add, Nat.cast_one]
      field_simp

/-- Continuous main of the base short-range form. -/
def barbanVehovShortBaseContinuous (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovShortHarmonicKernelContinuous X p.1 p.2

/-- Continuous main of the cross short-range form. -/
def barbanVehovShortCrossContinuous (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      (-(barbanVehovShortFirstLogKernelContinuous X p.1 p.2))

/-- Continuous main of the differentiated-square short-range form. -/
def barbanVehovShortDerivativeContinuous (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovShortSecondLogKernelContinuous X p.1 p.2

/-- Continuous main of the full short-range detector energy. -/
def barbanVehovShortEnergyContinuous (lam : ℝ) (X M : ℕ) : ℝ :=
  (barbanVehovShortBaseContinuous X M + 2 * lam * barbanVehovShortCrossContinuous X M +
      lam ^ 2 * barbanVehovShortDerivativeContinuous X M) /
    Real.log M ^ 2

private theorem lcm_le_sq {M q r : ℕ}
    (hq : 1 ≤ q) (hr : 1 ≤ r) (hqM : q ≤ M) (hrM : r ≤ M) :
    Nat.lcm q r ≤ M ^ 2 := by
  exact (Nat.le_of_dvd (Nat.mul_pos hq hr) (Nat.lcm_dvd_mul q r)).trans
    (by simpa only [pow_two] using Nat.mul_le_mul hqM hrM)

theorem abs_barbanVehovShortBaseMain_sub_continuous_le
    {X M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ 2 ≤ X) :
    |barbanVehovShortBaseMain X M - barbanVehovShortBaseContinuous X M| ≤
      ((M : ℝ) * Real.log M) ^ 2 * (1 / (X : ℝ)) := by
  have hX : 0 < X := by
    have hMpos : 0 < M := by omega
    have : 0 < 8 * M ^ 2 := by positivity
    omega
  have hpoint : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      |barbanVehovShortHarmonicKernelMain X p.1 p.2 -
        barbanVehovShortHarmonicKernelContinuous X p.1 p.2| ≤ 1 / (X : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact abs_barbanVehovShortHarmonicKernelMain_sub_continuous_le hX
      (Finset.mem_Icc.mp hp1).1 (Finset.mem_Icc.mp hp2).1
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovShortHarmonicKernelMain X p.1 p.2)
    (fun p => barbanVehovShortHarmonicKernelContinuous X p.1 p.2) hpoint
  rw [barbanVehovShortBaseMain, barbanVehovShortBaseContinuous]
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

theorem abs_barbanVehovShortCrossMain_sub_continuous_le
    {X M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ 2 ≤ X) :
    |barbanVehovShortCrossMain X M - barbanVehovShortCrossContinuous X M| ≤
      ((M : ℝ) * Real.log M) ^ 2 *
        (2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ)) := by
  have hX : 0 < X := by
    have hMpos : 0 < M := by omega
    have : 0 < 8 * M ^ 2 := by positivity
    omega
  have hpoint : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      |(-barbanVehovShortFirstLogKernelMain X p.1 p.2) -
        (-barbanVehovShortFirstLogKernelContinuous X p.1 p.2)| ≤
          2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1lo, hp1hi⟩ := Finset.mem_Icc.mp hp1
    obtain ⟨hp2lo, hp2hi⟩ := Finset.mem_Icc.mp hp2
    have heX : Nat.lcm p.1 p.2 ≤ X :=
      (lcm_le_sq hp1lo hp2lo hp1hi hp2hi).trans (by omega)
    rw [show (-barbanVehovShortFirstLogKernelMain X p.1 p.2) -
        (-barbanVehovShortFirstLogKernelContinuous X p.1 p.2) =
      -(barbanVehovShortFirstLogKernelMain X p.1 p.2 -
        barbanVehovShortFirstLogKernelContinuous X p.1 p.2) by ring, abs_neg]
    exact abs_barbanVehovShortFirstLogKernelMain_sub_continuous_le
      hX hp1lo hp2lo heX
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => -barbanVehovShortFirstLogKernelMain X p.1 p.2)
    (fun p => -barbanVehovShortFirstLogKernelContinuous X p.1 p.2) hpoint
  rw [barbanVehovShortCrossMain, barbanVehovShortCrossContinuous]
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

theorem abs_barbanVehovShortDerivativeMain_sub_continuous_le
    {X M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ 2 ≤ X) :
    |barbanVehovShortDerivativeMain X M - barbanVehovShortDerivativeContinuous X M| ≤
      ((M : ℝ) * Real.log M) ^ 2 *
        (4 * Real.log ((X + 1 : ℕ) : ℝ) ^ 2 / (X : ℝ)) := by
  have hX : 0 < X := by
    have hMpos : 0 < M := by omega
    have : 0 < 8 * M ^ 2 := by positivity
    omega
  have hpoint : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      |barbanVehovShortSecondLogKernelMain X p.1 p.2 -
        barbanVehovShortSecondLogKernelContinuous X p.1 p.2| ≤
          4 * Real.log ((X + 1 : ℕ) : ℝ) ^ 2 / (X : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1lo, hp1hi⟩ := Finset.mem_Icc.mp hp1
    obtain ⟨hp2lo, hp2hi⟩ := Finset.mem_Icc.mp hp2
    have heX : Nat.lcm p.1 p.2 ≤ X :=
      (lcm_le_sq hp1lo hp2lo hp1hi hp2hi).trans (by omega)
    exact abs_barbanVehovShortSecondLogKernelMain_sub_continuous_le
      hX hp1lo hp2lo heX
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovShortSecondLogKernelMain X p.1 p.2)
    (fun p => barbanVehovShortSecondLogKernelContinuous X p.1 p.2) hpoint
  rw [barbanVehovShortDerivativeMain, barbanVehovShortDerivativeContinuous]
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

private theorem abs_quadCombination_sub_le (lam A B C a b c : ℝ) :
    |(A + 2 * lam * B + lam ^ 2 * C) - (a + 2 * lam * b + lam ^ 2 * c)| ≤
      |A - a| + 2 * |lam| * |B - b| + lam ^ 2 * |C - c| := by
  rw [show (A + 2 * lam * B + lam ^ 2 * C) - (a + 2 * lam * b + lam ^ 2 * c) =
      (A - a) + 2 * lam * (B - b) + lam ^ 2 * (C - c) by ring]
  calc
    |(A - a) + 2 * lam * (B - b) + lam ^ 2 * (C - c)| ≤
        |A - a| + |2 * lam * (B - b)| + |lam ^ 2 * (C - c)| :=
      (abs_add_le ((A - a) + 2 * lam * (B - b)) (lam ^ 2 * (C - c))).trans
        (add_le_add (abs_add_le (A - a) (2 * lam * (B - b))) le_rfl)
    _ = _ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, sq_abs]

/-- Continuous endpoint replacement for the full short-energy main. -/
theorem abs_barbanVehovShortEnergyMain_sub_continuous_le
    (lam : ℝ) {X M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ 2 ≤ X) :
    |barbanVehovShortEnergyMain lam X M - barbanVehovShortEnergyContinuous lam X M| ≤
      (((M : ℝ) * Real.log M) ^ 2 * (1 / (X : ℝ)) +
          2 * |lam| * (((M : ℝ) * Real.log M) ^ 2 *
            (2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ))) +
          lam ^ 2 * (((M : ℝ) * Real.log M) ^ 2 *
            (4 * Real.log ((X + 1 : ℕ) : ℝ) ^ 2 / (X : ℝ)))) /
        Real.log M ^ 2 := by
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  rw [barbanVehovShortEnergyMain, barbanVehovShortEnergyContinuous, ← sub_div, abs_div,
    abs_of_pos (pow_pos hlog 2)]
  refine div_le_div_of_nonneg_right ?_ (pow_pos hlog 2).le
  refine (abs_quadCombination_sub_le lam _ _ _ _ _ _).trans ?_
  have hb := abs_barbanVehovShortBaseMain_sub_continuous_le (le_of_lt hM) hscale
  have hc := abs_barbanVehovShortCrossMain_sub_continuous_le (le_of_lt hM) hscale
  have hd := abs_barbanVehovShortDerivativeMain_sub_continuous_le (le_of_lt hM) hscale
  have hcm := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * |lam|)
  have hdm := mul_le_mul_of_nonneg_left hd (sq_nonneg lam)
  linarith

end

end RHTower.Sieve
