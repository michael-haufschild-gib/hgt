import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortEnergyLcm
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovOmittedError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovStrongScaleError

/-!
# Main term of the short-range mollified detector energy

Replacing each of the three origin-based lcm kernels by its main term costs, per pair, an error
carrying one factor `1/e` from the kernel and one factor `e/X` from the rescaled endpoint.  The two
cancel, so the total error is the `ℓ¹` mass of the weights times `log^j(X+1)/X`, exactly the shape
of the long-range error.

At the Levinson scaling `X ≍ T^{1/2+θ}`, `M = T^θ`, and `|λ| ≍ 1/log T`, the whole error is
`O(M²/X) = O(T^{θ-1/2})`.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- The lcm of two divisors below `M` is at most `M²`. -/
private theorem lcm_le_sq {M q r : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r) (hqM : q ≤ M) (hrM : r ≤ M) :
    Nat.lcm q r ≤ M ^ (2 : ℕ) := by
  have hmul : 0 < q * r := Nat.mul_pos hq hr
  have h1 : Nat.lcm q r ≤ q * r := Nat.le_of_dvd hmul (Nat.lcm_dvd_mul q r)
  have h2 : q * r ≤ M * M := Nat.mul_le_mul hqM hrM
  calc Nat.lcm q r ≤ q * r := h1
    _ ≤ M * M := h2
    _ = M ^ (2 : ℕ) := (sq M).symm

/-- Under the Levinson scale the rescaled endpoint clears the antitone threshold. -/
private theorem eight_le_div_lcm {X M q r : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ X) :
    8 ≤ X / Nat.lcm q r := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  rw [Nat.le_div_iff_mul_le he]
  calc 8 * Nat.lcm q r ≤ 8 * M ^ (2 : ℕ) :=
        Nat.mul_le_mul_left 8 (lcm_le_sq hq hr hqM hrM)
    _ ≤ X := hscale

/-- The complementary divisor of an lcm has logarithm below the window scale. -/
private theorem abs_log_lcm_div_le {X M q r : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ X) :
    |Real.log (((Nat.lcm q r / r : ℕ) : ℝ))| ≤ Real.log ((X + 1 : ℕ) : ℝ) := by
  have he : 0 < Nat.lcm q r := Nat.lcm_pos hq hr
  have hrle : r ≤ Nat.lcm q r := Nat.le_of_dvd he (Nat.dvd_lcm_right q r)
  have hone : 1 ≤ Nat.lcm q r / r := (Nat.one_le_div_iff hr).mpr hrle
  have hupper : Nat.lcm q r / r ≤ X + 1 := by
    have h1 : Nat.lcm q r / r ≤ Nat.lcm q r := Nat.div_le_self _ _
    have h2 : Nat.lcm q r ≤ M ^ (2 : ℕ) := lcm_le_sq hq hr hqM hrM
    have h3 : M ^ (2 : ℕ) ≤ X := by omega
    omega
  have hnn : (0 : ℝ) ≤ Real.log (((Nat.lcm q r / r : ℕ) : ℝ)) := by
    refine Real.log_nonneg ?_
    exact_mod_cast hone
  rw [abs_of_nonneg hnn]
  refine Real.log_le_log ?_ ?_
  · have : (0 : ℕ) < Nat.lcm q r / r := hone
    exact_mod_cast this
  · exact_mod_cast hupper

/-- Main term of the base lcm form of the short-range energy. -/
def barbanVehovShortBaseMain (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovShortHarmonicKernelMain X p.1 p.2

/-- Main term of the cross lcm form of the short-range energy. -/
def barbanVehovShortCrossMain (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      (-(barbanVehovShortFirstLogKernelMain X p.1 p.2))

/-- Main term of the differentiated-square lcm form of the short-range energy. -/
def barbanVehovShortDerivativeMain (X M : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
    barbanVehovWeight M p.1 * barbanVehovWeight M p.2 *
      barbanVehovShortSecondLogKernelMain X p.1 p.2

/-- Main term of the short-range mollified detector energy. -/
def barbanVehovShortEnergyMain (lam : ℝ) (X M : ℕ) : ℝ :=
  (barbanVehovShortBaseMain X M + 2 * lam * barbanVehovShortCrossMain X M +
      lam ^ (2 : ℕ) * barbanVehovShortDerivativeMain X M) /
    Real.log M ^ (2 : ℕ)

theorem abs_barbanVehovShortBaseLcm_sub_main_le
    {X M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ X) :
    |barbanVehovShortBaseLcm X M - barbanVehovShortBaseMain X M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (1 / (X : ℝ)) := by
  classical
  have hX : 0 < X := by
    have : 0 < 8 * M ^ (2 : ℕ) := by positivity
    omega
  have hpoint : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      |barbanVehovLongHarmonicKernel 0 X p.1 p.2 -
        barbanVehovShortHarmonicKernelMain X p.1 p.2| ≤ 1 / (X : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    have he : 0 < Nat.lcm p.1 p.2 := Nat.lcm_pos hp1.1 hp2.1
    have h8 := eight_le_div_lcm hp1.1 hp2.1 hp1.2 hp2.2 hscale
    refine (abs_barbanVehovLongHarmonicKernel_zeroStart_sub_main_le hp1.1 hp2.1 h8).trans ?_
    have := logPowDivId_succ_div_le (m := 0) (X := X) (e := Nat.lcm p.1 p.2) hX he
    simpa using this
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovLongHarmonicKernel 0 X p.1 p.2)
    (fun p => barbanVehovShortHarmonicKernelMain X p.1 p.2) hpoint
  rw [barbanVehovShortBaseLcm, barbanVehovShortBaseMain]
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

theorem abs_barbanVehovShortCrossLcm_sub_main_le
    {X M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ X) :
    |barbanVehovShortCrossLcm X M - barbanVehovShortCrossMain X M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ)) := by
  classical
  have hX : 0 < X := by
    have : 0 < 8 * M ^ (2 : ℕ) := by positivity
    omega
  have hlogX : (0 : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ X + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast this
  have hpoint : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      |(-(barbanVehovLongFirstLogKernel 0 X p.1 p.2)) -
        (-(barbanVehovShortFirstLogKernelMain X p.1 p.2))| ≤
          2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    have he : 0 < Nat.lcm p.1 p.2 := Nat.lcm_pos hp1.1 hp2.1
    have h8 := eight_le_div_lcm hp1.1 hp2.1 hp1.2 hp2.2 hscale
    have hbase := abs_barbanVehovLongFirstLogKernel_zeroStart_sub_main_le hp1.1 hp2.1 h8
    have hneg : |(-(barbanVehovLongFirstLogKernel 0 X p.1 p.2)) -
        (-(barbanVehovShortFirstLogKernelMain X p.1 p.2))| =
        |barbanVehovLongFirstLogKernel 0 X p.1 p.2 -
          barbanVehovShortFirstLogKernelMain X p.1 p.2| := by
      rw [← abs_neg]
      ring_nf
    rw [hneg]
    refine hbase.trans ?_
    have hlogb := abs_log_lcm_div_le hp1.1 hp2.1 hp1.2 hp2.2 hscale
    have h0 := logPowDivId_succ_div_le (m := 0) (X := X) (e := Nat.lcm p.1 p.2) hX he
    have h1 := logPowDivId_succ_div_le (m := 1) (X := X) (e := Nat.lcm p.1 p.2) hX he
    have hsplit : (|Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| *
          RHTower.logPowDivId 0 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) +
        RHTower.logPowDivId 1 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ)) / (Nat.lcm p.1 p.2 : ℝ) =
        |Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| *
            (RHTower.logPowDivId 0 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) /
              (Nat.lcm p.1 p.2 : ℝ)) +
          RHTower.logPowDivId 1 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) /
            (Nat.lcm p.1 p.2 : ℝ) := by
      field_simp
    rw [hsplit]
    have hnn0 : (0 : ℝ) ≤ RHTower.logPowDivId 0 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) /
        (Nat.lcm p.1 p.2 : ℝ) := by
      have hnn : (0 : ℝ) ≤ RHTower.logPowDivId 0 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) := by
        refine logPowDivId_nonneg_of_eight_le ?_
        have : (8 : ℕ) ≤ X / Nat.lcm p.1 p.2 + 1 := by omega
        exact_mod_cast this
      have heR : (0 : ℝ) ≤ (Nat.lcm p.1 p.2 : ℝ) := by positivity
      positivity
    simp only [pow_zero] at h0
    calc |Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ))| *
            (RHTower.logPowDivId 0 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) /
              (Nat.lcm p.1 p.2 : ℝ)) +
          RHTower.logPowDivId 1 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) /
            (Nat.lcm p.1 p.2 : ℝ)
        ≤ Real.log ((X + 1 : ℕ) : ℝ) * (1 / (X : ℝ)) +
            Real.log ((X + 1 : ℕ) : ℝ) ^ (1 : ℕ) / (X : ℝ) := by
          gcongr
      _ = 2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ) := by
          rw [pow_one]
          ring
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => -(barbanVehovLongFirstLogKernel 0 X p.1 p.2))
    (fun p => -(barbanVehovShortFirstLogKernelMain X p.1 p.2)) hpoint
  rw [barbanVehovShortCrossLcm, barbanVehovShortCrossMain]
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))


/-- The other complementary divisor of an lcm. -/
private theorem abs_log_lcm_div_left_le {X M q r : ℕ} (hq : 1 ≤ q) (hr : 1 ≤ r)
    (hqM : q ≤ M) (hrM : r ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ X) :
    |Real.log (((Nat.lcm q r / q : ℕ) : ℝ))| ≤ Real.log ((X + 1 : ℕ) : ℝ) := by
  have h := abs_log_lcm_div_le (X := X) (M := M) (q := r) (r := q) hr hq hrM hqM hscale
  rwa [Nat.lcm_comm r q] at h

theorem abs_barbanVehovShortDerivativeLcm_sub_main_le
    {X M : ℕ} (hM : 1 ≤ M) (hscale : 8 * M ^ (2 : ℕ) ≤ X) :
    |barbanVehovShortDerivativeLcm X M - barbanVehovShortDerivativeMain X M| ≤
      ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (4 * Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ)) := by
  classical
  have hX : 0 < X := by
    have : 0 < 8 * M ^ (2 : ℕ) := by positivity
    omega
  have hlogX : (0 : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ X + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast this
  have hpoint : ∀ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
      |barbanVehovLongSecondLogKernel 0 X p.1 p.2 -
        barbanVehovShortSecondLogKernelMain X p.1 p.2| ≤
          4 * Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_Icc] at hp1 hp2
    have he : 0 < Nat.lcm p.1 p.2 := Nat.lcm_pos hp1.1 hp2.1
    have h8 := eight_le_div_lcm hp1.1 hp2.1 hp1.2 hp2.2 hscale
    refine (abs_barbanVehovLongSecondLogKernel_zeroStart_sub_main_le hp1.1 hp2.1 h8).trans ?_
    have hlogr := abs_log_lcm_div_le (X := X) (M := M) hp1.1 hp2.1 hp1.2 hp2.2 hscale
    have hlogq := abs_log_lcm_div_left_le (X := X) (M := M) hp1.1 hp2.1 hp1.2 hp2.2 hscale
    have h0 := logPowDivId_succ_div_le (m := 0) (X := X) (e := Nat.lcm p.1 p.2) hX he
    have h1 := logPowDivId_succ_div_le (m := 1) (X := X) (e := Nat.lcm p.1 p.2) hX he
    have h2 := logPowDivId_succ_div_le (m := 2) (X := X) (e := Nat.lcm p.1 p.2) hX he
    simp only [pow_zero] at h0
    set a := Real.log (((Nat.lcm p.1 p.2 / p.1 : ℕ) : ℝ)) with hadef
    set b := Real.log (((Nat.lcm p.1 p.2 / p.2 : ℕ) : ℝ)) with hbdef
    set P0 := RHTower.logPowDivId 0 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) with hP0
    set P1 := RHTower.logPowDivId 1 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) with hP1
    set P2 := RHTower.logPowDivId 2 ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) with hP2
    have hnnP : ∀ m : ℕ, (0 : ℝ) ≤ RHTower.logPowDivId m
        ((X / Nat.lcm p.1 p.2 + 1 : ℕ) : ℝ) := by
      intro m
      refine logPowDivId_nonneg_of_eight_le ?_
      have : (8 : ℕ) ≤ X / Nat.lcm p.1 p.2 + 1 := by omega
      exact_mod_cast this
    have heR : (0 : ℝ) < (Nat.lcm p.1 p.2 : ℝ) := by exact_mod_cast he
    have hsplit : (|a * b| * P0 + |a + b| * P1 + P2) / (Nat.lcm p.1 p.2 : ℝ) =
        |a * b| * (P0 / (Nat.lcm p.1 p.2 : ℝ)) + |a + b| * (P1 / (Nat.lcm p.1 p.2 : ℝ)) +
          P2 / (Nat.lcm p.1 p.2 : ℝ) := by
      field_simp
    rw [hsplit]
    have hab : |a * b| ≤ Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) := by
      rw [abs_mul, sq]
      exact mul_le_mul hlogq hlogr (abs_nonneg b) hlogX
    have hsum : |a + b| ≤ 2 * Real.log ((X + 1 : ℕ) : ℝ) := by
      refine (abs_add_le a b).trans ?_
      linarith [hlogq, hlogr]
    have hP0nn : (0 : ℝ) ≤ P0 / (Nat.lcm p.1 p.2 : ℝ) := by
      rw [hP0]
      exact div_nonneg (hnnP 0) heR.le
    have hP1nn : (0 : ℝ) ≤ P1 / (Nat.lcm p.1 p.2 : ℝ) := by
      rw [hP1]
      exact div_nonneg (hnnP 1) heR.le
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hstep0 : |a * b| * (P0 / (Nat.lcm p.1 p.2 : ℝ)) ≤
        Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) * (1 / (X : ℝ)) :=
      mul_le_mul hab h0 hP0nn (by positivity)
    have hstep1 : |a + b| * (P1 / (Nat.lcm p.1 p.2 : ℝ)) ≤
        2 * Real.log ((X + 1 : ℕ) : ℝ) * (Real.log ((X + 1 : ℕ) : ℝ) ^ (1 : ℕ) / (X : ℝ)) :=
      mul_le_mul hsum h1 hP1nn (by positivity)
    have hstep2 : P2 / (Nat.lcm p.1 p.2 : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ) := h2
    have hcollect : Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) * (1 / (X : ℝ)) +
        2 * Real.log ((X + 1 : ℕ) : ℝ) * (Real.log ((X + 1 : ℕ) : ℝ) ^ (1 : ℕ) / (X : ℝ)) +
        Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ) =
        4 * Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ) := by
      rw [pow_one]
      field_simp
      ring
    linarith [hstep0, hstep1, hstep2, hcollect.ge, hcollect.le]
  have hraw := abs_sum_weight_mul_sub_le_of_pointwise
    ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M))
    (fun p => barbanVehovWeight M p.1 * barbanVehovWeight M p.2)
    (fun p => barbanVehovLongSecondLogKernel 0 X p.1 p.2)
    (fun p => barbanVehovShortSecondLogKernelMain X p.1 p.2) hpoint
  rw [barbanVehovShortDerivativeLcm, barbanVehovShortDerivativeMain]
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_product_abs_barbanVehovWeight_le hM) (by positivity))

private theorem abs_quadCombination_sub_le (lam A B C a b c : ℝ) :
    |(A + 2 * lam * B + lam ^ (2 : ℕ) * C) - (a + 2 * lam * b + lam ^ (2 : ℕ) * c)| ≤
      |A - a| + 2 * |lam| * |B - b| + lam ^ (2 : ℕ) * |C - c| := by
  rw [show (A + 2 * lam * B + lam ^ (2 : ℕ) * C) - (a + 2 * lam * b + lam ^ (2 : ℕ) * c) =
      (A - a) + 2 * lam * (B - b) + lam ^ (2 : ℕ) * (C - c) by ring]
  calc
    |(A - a) + 2 * lam * (B - b) + lam ^ (2 : ℕ) * (C - c)| ≤
        |A - a| + |2 * lam * (B - b)| + |lam ^ (2 : ℕ) * (C - c)| :=
      (abs_add_le ((A - a) + 2 * lam * (B - b)) (lam ^ (2 : ℕ) * (C - c))).trans
        (add_le_add (abs_add_le (A - a) (2 * lam * (B - b))) le_rfl)
    _ = _ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, sq_abs]

/-- **The short-range energy is its main term up to an `O(M²/X)` error.** -/
theorem abs_barbanVehovShortEnergyLcm_sub_main_le
    (lam : ℝ) {X M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ (2 : ℕ) ≤ X) :
    |barbanVehovShortEnergyLcm lam X M - barbanVehovShortEnergyMain lam X M| ≤
      (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (1 / (X : ℝ)) +
          2 * |lam| * (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
            (2 * Real.log ((X + 1 : ℕ) : ℝ) / (X : ℝ))) +
          lam ^ (2 : ℕ) * (((M : ℝ) * Real.log M) ^ (2 : ℕ) *
            (4 * Real.log ((X + 1 : ℕ) : ℝ) ^ (2 : ℕ) / (X : ℝ)))) /
        Real.log M ^ (2 : ℕ) := by
  have hM1 : 1 ≤ M := le_of_lt hM
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  rw [barbanVehovShortEnergyLcm, barbanVehovShortEnergyMain, ← sub_div, abs_div,
    abs_of_pos (pow_pos hlog 2)]
  refine div_le_div_of_nonneg_right ?_ (pow_pos hlog 2).le
  refine (abs_quadCombination_sub_le lam _ _ _ _ _ _).trans ?_
  have hb := abs_barbanVehovShortBaseLcm_sub_main_le hM1 hscale
  have hc := abs_barbanVehovShortCrossLcm_sub_main_le hM1 hscale
  have hd := abs_barbanVehovShortDerivativeLcm_sub_main_le hM1 hscale
  have h2 : (0 : ℝ) ≤ 2 * |lam| := by positivity
  have h3 : (0 : ℝ) ≤ lam ^ (2 : ℕ) := sq_nonneg lam
  have hcm := mul_le_mul_of_nonneg_left hc h2
  have hdm := mul_le_mul_of_nonneg_left hd h3
  linarith [hb, hcm, hdm]

/-- The short-range energy error with the Levinson parameter constraint. -/
theorem abs_barbanVehovShortEnergyLcm_sub_main_le_sq_div
    (lam : ℝ) {X M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ (2 : ℕ) ≤ X)
    (hlam : |lam| * Real.log ((X + 1 : ℕ) : ℝ) ≤ 1) :
    |barbanVehovShortEnergyLcm lam X M - barbanVehovShortEnergyMain lam X M| ≤
      9 * (M : ℝ) ^ (2 : ℕ) / (X : ℝ) := by
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : (0 : ℝ) < Real.log M := Real.log_pos (by linarith)
  have hX : 0 < X := by
    have : 0 < 8 * M ^ (2 : ℕ) := by positivity
    omega
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  refine (abs_barbanVehovShortEnergyLcm_sub_main_le lam hM hscale).trans ?_
  set A : ℝ := Real.log ((X + 1 : ℕ) : ℝ) with hA
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ X + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast this
  have hsq : lam ^ (2 : ℕ) * A ^ (2 : ℕ) ≤ 1 := by
    have hnn : (0 : ℝ) ≤ |lam| * A := by positivity
    have hlamsq : lam ^ (2 : ℕ) = |lam| ^ (2 : ℕ) := (sq_abs lam).symm
    nlinarith [hlam, hnn]
  have hnum : ((M : ℝ) * Real.log M) ^ (2 : ℕ) * (1 / (X : ℝ)) +
      2 * |lam| * (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (2 * A / (X : ℝ))) +
      lam ^ (2 : ℕ) * (((M : ℝ) * Real.log M) ^ (2 : ℕ) * (4 * A ^ (2 : ℕ) / (X : ℝ)))
      = (((M : ℝ) * Real.log M) ^ (2 : ℕ) / (X : ℝ)) *
        (1 + 4 * (|lam| * A) + 4 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ))) := by
    field_simp
    ring
  rw [hnum]
  have hfac : (0 : ℝ) < ((M : ℝ) * Real.log M) ^ (2 : ℕ) / (X : ℝ) := by positivity
  have hbr : (1 : ℝ) + 4 * (|lam| * A) + 4 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ)) ≤ 9 := by
    linarith [hlam, hsq]
  have hstep : (((M : ℝ) * Real.log M) ^ (2 : ℕ) / (X : ℝ)) *
      (1 + 4 * (|lam| * A) + 4 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ)))
      ≤ (((M : ℝ) * Real.log M) ^ (2 : ℕ) / (X : ℝ)) * 9 :=
    mul_le_mul_of_nonneg_left hbr hfac.le
  have hdiv : ((((M : ℝ) * Real.log M) ^ (2 : ℕ) / (X : ℝ)) * 9) / Real.log M ^ (2 : ℕ)
      = 9 * (M : ℝ) ^ (2 : ℕ) / (X : ℝ) := by
    field_simp
  calc ((((M : ℝ) * Real.log M) ^ (2 : ℕ) / (X : ℝ)) *
        (1 + 4 * (|lam| * A) + 4 * (lam ^ (2 : ℕ) * A ^ (2 : ℕ)))) / Real.log M ^ (2 : ℕ)
      ≤ ((((M : ℝ) * Real.log M) ^ (2 : ℕ) / (X : ℝ)) * 9) / Real.log M ^ (2 : ℕ) :=
        div_le_div_of_nonneg_right hstep (by positivity)
    _ = 9 * (M : ℝ) ^ (2 : ℕ) / (X : ℝ) := hdiv

end RHTower.Sieve

end
