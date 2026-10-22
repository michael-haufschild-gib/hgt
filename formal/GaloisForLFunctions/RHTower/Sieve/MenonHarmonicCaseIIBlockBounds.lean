import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIBlockParameters
import GaloisForLFunctions.RHTower.Sieve.ChebyshevBracketBound

/-!
# Elementary bounds on the Case II block parameters

For a prime block `(a, Y]` with `a < Y ≤ 2a`, Case II uses `cells = ceil((log a)^{200})`, smoothing
width `H = a/(log a)^{20}` and the line `σ = 1 + 1/log(4Y + 1)`. This module records the scalar
bounds that feed the Case II budget: two-sided bounds on the cell count, the arctan tail, the
identity `(4Y + 1)^σ = e (4Y + 1)`, a bound `K(C0) a (log a)^{40}` for the wide-interval kernel
majorant, and a bound `K_P (log a)^{134}` for the Heath-Brown window fixed polylogarithmic bound at
degree `3`.

## Main results

- `menonHarmonicCaseIICells_cast_bounds`: `(log a)^{200} ≤ cells ≤ 2 (log a)^{200}` when `log a ≥ 1`.
- `menonHarmonicCaseII_arctanTail_le`: `π - 2 arctan(cells/2) ≤ 4/cells` for `a > 1`.
- `rpow_menonHarmonicCaseIISigma_eq`: `(4Y + 1)^σ = (4Y + 1) e` for `Y > 0`.
- `menonWideIntervalAmbientKernelMajorant_caseII_le`: the kernel majorant at `(4Y, H, σ)` is at
  most `menonHarmonicCaseIIKernelConstant C0 · a · (log a)^{40}`.
- `heathBrownWindowRelevantFixedPolylogBound_caseII_le`: the fixed polylog bound is at most
  `menonHarmonicCaseIIFixedPolylogConstant · (log a)^{134}` for `a ≥ 64`.

## Hypotheses

The results are unconditional elementary estimates, under ranges such as `C0 ≥ 0`, `a > 1` or
`a ≥ 64`, `log a ≥ 1` and `a < Y ≤ 2a`.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- Kernel constant `K(C0) = 1 + 36e + 2916 e C0`. -/
def menonHarmonicCaseIIKernelConstant (C0 : ℝ) : ℝ :=
  1 + 36 * Real.exp 1 + 2916 * Real.exp 1 * C0

/-- Fixed polylog constant `K_P = 32768 · 3 · 17^6 · 8 · 512 · 513^{127}`. -/
def menonHarmonicCaseIIFixedPolylogConstant : ℝ :=
  32768 * (3 * 17 ^ (6 : ℕ)) * 8 * 512 * 513 ^ (127 : ℕ)

/-- For `log a ≥ 1`, the Case II cell count satisfies `(log a)^{200} ≤ cells ≤ 2 (log a)^{200}`. -/
theorem menonHarmonicCaseIICells_cast_bounds
    {a : ℕ} (hlog : 1 ≤ Real.log (a : ℝ)) :
    (Real.log (a : ℝ)) ^ (200 : ℕ) ≤ (menonHarmonicCaseIICells a : ℝ) ∧
      (menonHarmonicCaseIICells a : ℝ) ≤
        2 * (Real.log (a : ℝ)) ^ (200 : ℕ) := by
  have hp0 : 0 ≤ (Real.log (a : ℝ)) ^ (200 : ℕ) := by positivity
  have hp1 : 1 ≤ (Real.log (a : ℝ)) ^ (200 : ℕ) := one_le_pow₀ hlog
  constructor
  · rw [menonHarmonicCaseIICells]
    exact Nat.le_ceil _
  · have hceil := Nat.ceil_lt_add_one hp0
    rw [menonHarmonicCaseIICells]
    linarith

/-- For `a > 1`, the arctan tail satisfies `π - 2 arctan(cells/2) ≤ 4/cells`. -/
theorem menonHarmonicCaseII_arctanTail_le
    {a : ℕ} (ha : 1 < a) :
    Real.pi - 2 * Real.arctan ((menonHarmonicCaseIICells a : ℝ) / 2) ≤
      4 / (menonHarmonicCaseIICells a : ℝ) := by
  have hcells : (0 : ℝ) < (menonHarmonicCaseIICells a : ℝ) := by
    exact_mod_cast menonHarmonicCaseIICells_pos ha
  have htail := pi_div_two_sub_arctan_le
    (show (0 : ℝ) < (menonHarmonicCaseIICells a : ℝ) / 2 by positivity)
  calc
    Real.pi - 2 * Real.arctan ((menonHarmonicCaseIICells a : ℝ) / 2) =
        2 * (Real.pi / 2 - Real.arctan ((menonHarmonicCaseIICells a : ℝ) / 2)) := by ring
    _ ≤ 2 * (1 / ((menonHarmonicCaseIICells a : ℝ) / 2)) := by gcongr
    _ = 4 / (menonHarmonicCaseIICells a : ℝ) := by
      field_simp
      norm_num

/-- For `Y > 0` and `σ = 1 + 1/log(4Y + 1)`, `(4Y + 1)^σ = (4Y + 1) e`. -/
theorem rpow_menonHarmonicCaseIISigma_eq
    {Y : ℕ} (hY : 0 < Y) :
    ((((4 * Y : ℕ) : ℝ) + 1) ^ menonHarmonicCaseIISigma Y) =
      ((((4 * Y : ℕ) : ℝ) + 1) * Real.exp 1) := by
  let Z : ℝ := (((4 * Y : ℕ) : ℝ) + 1)
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hlogZ : Real.log Z ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    dsimp only [Z]
    exact_mod_cast (show 1 < 4 * Y + 1 by omega)
  rw [menonHarmonicCaseIISigma, Real.rpow_add hZ, Real.rpow_one]
  have hsmall : Z ^ (1 / Real.log Z) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    field_simp
  simpa only [Z] using congrArg (fun z : ℝ => Z * z) hsmall

/-- For `C0 ≥ 0`, `a > 1`, `log a ≥ 1` and `a < Y ≤ 2a`, the wide-interval kernel majorant at
`(4Y, a/(log a)^{20}, σ)` is at most `K(C0) · a · (log a)^{40}`. -/
theorem menonWideIntervalAmbientKernelMajorant_caseII_le
    {C0 : ℝ} (hC0 : 0 ≤ C0) {a Y : ℕ} (ha : 1 < a)
    (hlog : 1 ≤ Real.log (a : ℝ)) (haY : a < Y) (hYa : Y ≤ 2 * a) :
    menonWideIntervalAmbientKernelMajorant C0 (4 * Y)
        (menonHarmonicCaseIISmoothingWidth a) (menonHarmonicCaseIISigma Y) ≤
      menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) *
        (Real.log (a : ℝ)) ^ (40 : ℕ) := by
  let Z : ℝ := (((4 * Y : ℕ) : ℝ) + 1)
  let la : ℝ := Real.log (a : ℝ)
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hZ0 : 0 < Z := by dsimp only [Z]; positivity
  have hZR : Z ≤ 9 * (a : ℝ) := by
    dsimp only [Z]
    push_cast
    have hYaR : (Y : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hYa
    have haR : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
    nlinarith
  have hZpow : Z ^ menonHarmonicCaseIISigma Y = Z * Real.exp 1 := by
    simpa only [Z] using rpow_menonHarmonicCaseIISigma_eq (Nat.zero_lt_of_lt haY)
  have hsigma : 1 ≤ menonHarmonicCaseIISigma Y :=
    (menonHarmonicCaseIISigma_gt_one (Nat.zero_lt_of_lt haY)).le
  have hM0 : Z ^ menonHarmonicCaseIISigma Y / menonHarmonicCaseIISigma Y ≤
      9 * Real.exp 1 * (a : ℝ) := by
    rw [hZpow]
    calc
      Z * Real.exp 1 / menonHarmonicCaseIISigma Y ≤ Z * Real.exp 1 :=
        div_le_self (by positivity) hsigma
      _ ≤ 9 * (a : ℝ) * Real.exp 1 := by gcongr
      _ = 9 * Real.exp 1 * (a : ℝ) := by ring
  have hHsq : menonHarmonicCaseIISmoothingWidth a ^ 2 =
      (a : ℝ) ^ 2 / la ^ (40 : ℕ) := by
    rw [menonHarmonicCaseIISmoothingWidth]
    dsimp only [la]
    field_simp
  have hZsq : Z ^ 2 ≤ (9 * (a : ℝ)) ^ 2 := by gcongr
  have hM2 : C0 / menonHarmonicCaseIISmoothingWidth a ^ 2 * Z ^ 2 *
        Z ^ menonHarmonicCaseIISigma Y ≤
      729 * Real.exp 1 * C0 * (a : ℝ) * la ^ (40 : ℕ) := by
    rw [hHsq, hZpow]
    have hla0 : 0 < la := by dsimp only [la]; linarith
    have hleft : C0 / ((a : ℝ) ^ 2 / la ^ (40 : ℕ)) * Z ^ 2 * (Z * Real.exp 1) ≤
        C0 / ((a : ℝ) ^ 2 / la ^ (40 : ℕ)) * (9 * (a : ℝ)) ^ 2 *
          (9 * (a : ℝ) * Real.exp 1) := by
      gcongr
    calc
      C0 / ((a : ℝ) ^ 2 / la ^ (40 : ℕ)) * Z ^ 2 * (Z * Real.exp 1) ≤
          C0 / ((a : ℝ) ^ 2 / la ^ (40 : ℕ)) * (9 * (a : ℝ)) ^ 2 *
            (9 * (a : ℝ) * Real.exp 1) := hleft
      _ = 729 * Real.exp 1 * C0 * (a : ℝ) * la ^ (40 : ℕ) := by
        field_simp [ne_of_gt ha0, ne_of_gt hla0]
        ring
  have hla40 : 1 ≤ la ^ (40 : ℕ) := by dsimp only [la]; exact one_le_pow₀ hlog
  rw [menonWideIntervalAmbientKernelMajorant]
  rw [show (((4 * Y : ℕ) : ℝ) + 1) = Z by rfl]
  calc
    1 + 4 *
          (Z ^ menonHarmonicCaseIISigma Y / menonHarmonicCaseIISigma Y +
            C0 / menonHarmonicCaseIISmoothingWidth a ^ 2 * Z ^ 2 *
              Z ^ menonHarmonicCaseIISigma Y) ≤
        1 + 4 * (9 * Real.exp 1 * (a : ℝ) +
          729 * Real.exp 1 * C0 * (a : ℝ) * la ^ (40 : ℕ)) := by gcongr
    _ ≤ menonHarmonicCaseIIKernelConstant C0 * (a : ℝ) * la ^ (40 : ℕ) := by
      rw [menonHarmonicCaseIIKernelConstant]
      have ha1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
      have haL : 1 ≤ (a : ℝ) * la ^ (40 : ℕ) :=
        one_le_mul_of_one_le_of_one_le ha1 hla40
      have h36 : 36 * Real.exp 1 * (a : ℝ) ≤
          36 * Real.exp 1 * (a : ℝ) * la ^ (40 : ℕ) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hla40
            (show 0 ≤ 36 * Real.exp 1 * (a : ℝ) by positivity))
      calc
        1 + 4 * (9 * Real.exp 1 * (a : ℝ) +
            729 * Real.exp 1 * C0 * (a : ℝ) * la ^ (40 : ℕ)) =
            1 + 36 * Real.exp 1 * (a : ℝ) +
              2916 * Real.exp 1 * C0 * (a : ℝ) * la ^ (40 : ℕ) := by ring
        _ ≤ (a : ℝ) * la ^ (40 : ℕ) +
              36 * Real.exp 1 * (a : ℝ) * la ^ (40 : ℕ) +
              2916 * Real.exp 1 * C0 * (a : ℝ) * la ^ (40 : ℕ) := by gcongr
        _ = (1 + 36 * Real.exp 1 + 2916 * Real.exp 1 * C0) *
              (a : ℝ) * la ^ (40 : ℕ) := by ring

/-- For `a ≥ 64`, `log a ≥ 1` and `a < Y ≤ 2a`, the degree-3 Heath-Brown window fixed polylog bound
at `(a, 4Y, σ)` is at most `K_P · (log a)^{134}`. -/
theorem heathBrownWindowRelevantFixedPolylogBound_caseII_le
    {a Y : ℕ} (ha64 : 64 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) :
    heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ)
        (menonHarmonicCaseIISigma Y) ≤
      menonHarmonicCaseIIFixedPolylogConstant *
        (Real.log (a : ℝ)) ^ (134 : ℕ) := by
  let X : ℕ := 4 * Y
  let M : ℝ := (((64 * X : ℕ) : ℝ))
  let la : ℝ := Real.log (a : ℝ)
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have ha64R : (64 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha64
  have hbase1 : (1 : ℝ) ≤ (a : ℝ) / 64 := (one_le_div (by norm_num)).2 ha64R
  have hXpos : 0 < X := by dsimp only [X]; omega
  have hXle : (X : ℝ) ≤ 8 * (a : ℝ) := by
    dsimp only [X]
    push_cast
    have hYaR : (Y : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hYa
    nlinarith
  have hM_eq : M = 64 * (X : ℝ) := by
    simp only [M, Nat.cast_mul, Nat.cast_ofNat]
  have hMle : M ≤ 512 * (a : ℝ) := by rw [hM_eq]; nlinarith
  have hMpos : 0 < M := by rw [hM_eq]; positivity
  have hlog512 : Real.log (512 : ℝ) ≤ 511 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 512) using 1 <;> norm_num
  have hlogM : Real.log M ≤ 512 * la := by
    have hmono := Real.log_le_log hMpos hMle
    rw [Real.log_mul (by norm_num : (512 : ℝ) ≠ 0) (ne_of_gt ha0)] at hmono
    dsimp only [la]
    nlinarith
  have honeLogM : 1 + Real.log M ≤ 513 * la := by
    dsimp only [la] at hlog ⊢
    nlinarith
  have hlogCount : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 17 * la := by
    have hnat := natLogTwo_add_one_cast_le (show 1 ≤ X by omega)
    have hlog8 : Real.log (8 : ℝ) ≤ 7 :=
      by convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8) using 1 <;> norm_num
    have hlogX : Real.log (X : ℝ) ≤ 8 * la := by
      have hmono := Real.log_le_log (by positivity : (0 : ℝ) < (X : ℝ)) hXle
      rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt ha0)] at hmono
      dsimp only [la]
      nlinarith
    dsimp only [la] at hnat hlogX ⊢
    nlinarith
  have hlogCountA : ((Nat.log 2 a + 1 : ℕ) : ℝ) ≤ 17 * la := by
    have hnat := natLogTwo_add_one_cast_le (show 1 ≤ a by omega)
    dsimp only [la] at hnat ⊢
    nlinarith
  have hcardNat := card_heathBrownBoxChoice_le a X 3
  have hcard : (Fintype.card (HeathBrownBoxChoice a X 3) : ℝ) ≤
      3 * (17 * la) ^ (6 : ℕ) := by
    have hcast : (Fintype.card (HeathBrownBoxChoice a X 3) : ℝ) ≤
        3 * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (3 : ℕ)) *
          (((Nat.log 2 a + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := by
      exact_mod_cast hcardNat
    calc
      (Fintype.card (HeathBrownBoxChoice a X 3) : ℝ) ≤
          3 * (((Nat.log 2 X + 1 : ℕ) : ℝ) ^ (3 : ℕ)) *
            (((Nat.log 2 a + 1 : ℕ) : ℝ) ^ (3 : ℕ)) := hcast
      _ ≤ 3 * (17 * la) ^ (3 : ℕ) * (17 * la) ^ (3 : ℕ) := by gcongr
      _ = 3 * (17 * la) ^ (6 : ℕ) := by ring
  have hsigma := menonHarmonicCaseIISigma_gt_one (Nat.zero_lt_of_lt haY)
  have hrpow : ((a : ℝ) / 64) ^ (-menonHarmonicCaseIISigma Y) ≤
      ((a : ℝ) / 64) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
  have hratio : ((a : ℝ) / 64) ^ (-menonHarmonicCaseIISigma Y) * M ≤ 32768 := by
    have hM0 : 0 ≤ M := hMpos.le
    calc
      ((a : ℝ) / 64) ^ (-menonHarmonicCaseIISigma Y) * M ≤
          ((a : ℝ) / 64) ^ (-1 : ℝ) * M :=
        mul_le_mul_of_nonneg_right hrpow hM0
      _ = (64 / (a : ℝ)) * M := by rw [Real.rpow_neg_one]; congr 1; field_simp
      _ ≤ (64 / (a : ℝ)) * (512 * (a : ℝ)) := by gcongr
      _ = 32768 := by field_simp; norm_num
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg (by
    rw [hM_eq]
    have : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
    nlinarith)
  have honeLogM0 : 0 ≤ 1 + Real.log M := by linarith
  rw [heathBrownWindowRelevantFixedPolylogBound]
  rw [show (2 : ℝ) ^ (2 * 3) = 64 by norm_num,
    show (2 ^ 3 : ℕ) = 8 by norm_num,
    show (2 ^ (2 * 3) : ℕ) = 64 by norm_num,
    show 2 ^ (2 * 3 + 1) - 1 = 127 by norm_num]
  change ((a : ℝ) / 64) ^ (-menonHarmonicCaseIISigma Y) *
      ((Fintype.card (HeathBrownBoxChoice a X 3) : ℝ) * 8 *
        Real.log M * (M * (1 + Real.log M) ^ (127 : ℕ))) ≤ _
  rw [menonHarmonicCaseIIFixedPolylogConstant]
  calc
    ((a : ℝ) / 64) ^ (-menonHarmonicCaseIISigma Y) *
        ((Fintype.card (HeathBrownBoxChoice a X 3) : ℝ) * 8 *
          Real.log M * (M * (1 + Real.log M) ^ (127 : ℕ))) =
        (((a : ℝ) / 64) ^ (-menonHarmonicCaseIISigma Y) * M) *
          (Fintype.card (HeathBrownBoxChoice a X 3) : ℝ) * 8 *
          Real.log M * (1 + Real.log M) ^ (127 : ℕ) := by ring
    _ ≤ 32768 * (3 * (17 * la) ^ (6 : ℕ)) * 8 *
          (512 * la) * (513 * la) ^ (127 : ℕ) := by gcongr
    _ = 32768 * (3 * 17 ^ (6 : ℕ)) * 8 * 512 * 513 ^ (127 : ℕ) *
          la ^ (134 : ℕ) := by ring

end

end RHTower.Sieve
