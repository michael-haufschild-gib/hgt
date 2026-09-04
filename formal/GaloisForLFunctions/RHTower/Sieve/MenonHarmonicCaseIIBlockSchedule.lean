import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicTruncatedLadderError
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIWideOrderFourHundredLogPowCount

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Natural left endpoint of one final-range geometric prime block. -/
def menonFinalRangeBlockLowerNat (x : ℝ) (j : ℕ) : ℕ :=
  ⌊menonFinalRangeLadderBase x * (1 + menonFinalRangeLadderEta x) ^ j⌋₊

/-- Natural right endpoint of one final-range geometric prime block. -/
def menonFinalRangeBlockUpperNat (x : ℝ) (j : ℕ) : ℕ :=
  ⌊menonFinalRangeLadderBase x * (1 + menonFinalRangeLadderEta x) ^ (j + 1)⌋₊

set_option maxHeartbeats 800000 in
theorem eventually_menonFinalRangeBlock_caseII_endpoints :
    ∀ᶠ x : ℝ in atTop,
      ∀ j ∈ Finset.range (menonTruncatedRangeLadderSteps x),
        (64 : ℕ) ^ 8 ≤ menonFinalRangeBlockLowerNat x j ∧
        menonFinalRangeBlockLowerNat x j < menonFinalRangeBlockUpperNat x j ∧
        menonFinalRangeBlockUpperNat x j ≤ 2 * menonFinalRangeBlockLowerNat x j := by
  have hbaseLarge :=
    tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop ((64 : ℕ) ^ 8 + 2)
  filter_upwards [eventually_menonTruncatedRangeLadder_basic,
    eventually_menonFinalRangeLadderEta_le_two_div_log_pow_ten,
    eventually_inv_menonFinalRangeLadderBase_le_log_rpow_neg_thirty,
    eventually_ge_atTop (Real.exp 2), hbaseLarge] with x hx hetaUpper hinv hxexp hbaseLargeX
  intro j hj
  simp only [menonFinalRangeBlockLowerNat, menonFinalRangeBlockUpperNat]
  rcases hx with ⟨hxone, hlogOne, hH, hbaseOne, _htop, heta, _hsteps⟩
  let q : ℝ := menonFinalRangeLadderBase x *
    (1 + menonFinalRangeLadderEta x) ^ j
  let a : ℕ := ⌊q⌋₊
  let Y : ℕ := ⌊q * (1 + menonFinalRangeLadderEta x)⌋₊
  have hlogTwo : 2 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 2) hxexp
    simpa using h
  have hlog0 : 0 < Real.log x := Real.log_pos hxone
  have hbase0 : 0 < menonFinalRangeLadderBase x := by linarith
  have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by linarith
  have hpowStep : 1 ≤ (1 + menonFinalRangeLadderEta x) ^ j :=
    one_le_pow₀ hstep
  have hqBase : menonFinalRangeLadderBase x ≤ q := by
    dsimp only [q]
    nlinarith [mul_le_mul_of_nonneg_left hpowStep hbase0.le]
  have hq0 : 0 < q := lt_of_lt_of_le hbase0 hqBase
  have haBase : menonFinalRangePrimeCutoffNat x ≤ a := by
    rw [← Nat.floor_natCast (R := ℝ) (menonFinalRangePrimeCutoffNat x)]
    exact Nat.floor_mono hqBase
  have haLarge : (64 : ℕ) ^ 8 ≤ a := by omega
  have hpow30pos : 0 < (Real.log x) ^ (30 : ℕ) := pow_pos hlog0 _
  have hbaseLower : (Real.log x) ^ (30 : ℕ) ≤ menonFinalRangeLadderBase x := by
    have hpEq : (Real.log x) ^ (30 : ℝ) = (Real.log x) ^ (30 : ℕ) :=
      Real.rpow_natCast _ 30
    have hinv' : (menonFinalRangeLadderBase x)⁻¹ ≤
        ((Real.log x) ^ (30 : ℕ))⁻¹ := by
      rw [Real.rpow_neg hlog0.le, hpEq] at hinv
      simpa only [one_div] using hinv
    exact (inv_le_inv₀ hbase0 hpow30pos).mp hinv'
  have hetaLower : 1 / menonFinalRangeLadderH x ≤ menonFinalRangeLadderEta x := by
    have he := Real.add_one_le_exp (1 / menonFinalRangeLadderH x)
    rw [menonFinalRangeLadderEta]
    linarith
  have hpowTenPos : 0 < (Real.log x) ^ (10 : ℕ) := pow_pos hlog0 _
  have hpowTwenty : 1 < (Real.log x) ^ (20 : ℕ) :=
    one_lt_pow₀ (lt_of_lt_of_le one_lt_two hlogTwo) (by norm_num)
  have hbaseDiv : 1 < menonFinalRangeLadderBase x *
      (1 / menonFinalRangeLadderH x) := by
    rw [menonFinalRangeLadderH]
    calc
      1 < (Real.log x) ^ (20 : ℕ) := hpowTwenty
      _ = (Real.log x) ^ (30 : ℕ) * (1 / (Real.log x) ^ (10 : ℕ)) := by
        field_simp
      _ ≤ menonFinalRangeLadderBase x * (1 / (Real.log x) ^ (10 : ℕ)) :=
        mul_le_mul_of_nonneg_right hbaseLower (by positivity)
  have hqEta : 1 < q * menonFinalRangeLadderEta x := by
    exact hbaseDiv.trans_le
      (mul_le_mul hqBase hetaLower (by positivity) hq0.le)
  have haCastLe : (a : ℝ) ≤ q := by
    dsimp only [a]
    exact Nat.floor_le hq0.le
  have haLtY : a < Y := by
    have haOneLe : ((a + 1 : ℕ) : ℝ) ≤
        q * (1 + menonFinalRangeLadderEta x) := by
      push_cast
      nlinarith
    have : a + 1 ≤ Y := by
      dsimp only [Y]
      exact Nat.le_floor haOneLe
    omega
  have hpowTenFour : (4 : ℝ) ≤ (Real.log x) ^ (10 : ℕ) := by
    have hsq : (4 : ℝ) ≤ (Real.log x) ^ (2 : ℕ) := by nlinarith
    have hpowNonneg : 0 ≤ (Real.log x) ^ (8 : ℕ) := by positivity
    calc
      (4 : ℝ) ≤ (Real.log x) ^ (2 : ℕ) := hsq
      _ ≤ (Real.log x) ^ (2 : ℕ) * (Real.log x) ^ (8 : ℕ) := by
        nlinarith [one_le_pow₀ hlogOne (n := 8)]
      _ = (Real.log x) ^ (10 : ℕ) := by ring
  have hetaHalf : menonFinalRangeLadderEta x ≤ (1 : ℝ) / 2 := by
    calc
      menonFinalRangeLadderEta x ≤ 2 / (Real.log x) ^ (10 : ℕ) := hetaUpper.2.1
      _ ≤ 1 / 2 := by
        rw [div_le_iff₀ hpowTenPos]
        nlinarith
  have hqLtFloor : q < (a : ℝ) + 1 := by
    dsimp only [a]
    exact Nat.lt_floor_add_one q
  have hYlt : Y < 2 * a + 1 := by
    apply (Nat.floor_lt (mul_nonneg hq0.le (by linarith : 0 ≤ 1 + menonFinalRangeLadderEta x))).2
    push_cast
    have haOne : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 1 ≤ a by omega)
    calc
      q * (1 + menonFinalRangeLadderEta x) ≤ q * (3 / 2 : ℝ) := by
        gcongr
        linarith
      _ < ((a : ℝ) + 1) * (3 / 2 : ℝ) := by gcongr
      _ ≤ 2 * (a : ℝ) + 1 := by nlinarith
  have hY : Y ≤ 2 * a := by omega
  have hUpper :
      ⌊menonFinalRangeLadderBase x *
          (1 + menonFinalRangeLadderEta x) ^ (j + 1)⌋₊ = Y := by
    dsimp only [Y, q]
    rw [pow_succ]
    congr 1
    ring
  rw [hUpper]
  simpa only [a, q] using And.intro haLarge (And.intro haLtY hY)

set_option maxHeartbeats 800000 in
/-- Structural Case-II specialization for a multiplicatively narrow prime block. -/
theorem exists_absolute_eventually_volume_real_menonHarmonicPrimeBlock_caseII_orderFourHundred_narrow_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {Y cells : ℕ} {B sigma T : ℝ},
        a < Y → Y ≤ 2 * a → 1 < sigma → 0 ≤ B → 0 < cells →
        1 ≤ T → (cells : ℝ) / 4 ≤ T → 2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 (4 * Y) (Y : ℝ) sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
            ((cells : ℝ) * C)
        (Real.log (a : ℝ)) ^ (-300 : ℝ) < Q →
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope (4 * Y)) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        volume.real
            (menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet
              a (4 * Y) Y (Y : ℝ) B T ((cells : ℝ) / 2)) ≤
          2 * (2 * Real.pi)⁻¹ *
            (4 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1)) := by
  obtain ⟨C0, hC0, hmain⟩ :=
    exists_absolute_eventually_volume_real_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_orderFourHundred_twoSided_le
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop ((64 : ℕ) ^ 8)] with a ha ha64
  intro Y cells B sigma T haY hYa hsigma hB hcells hT hcellsT h2T
  dsimp only
  intro hQ
  have ha1 : 1 ≤ a := by omega
  have hY1 : 1 ≤ Y := by omega
  have hX : 1 ≤ 4 * Y := by omega
  have ha3 : 3 ≤ a := by omega
  have h8leSq : 8 ≤ a ^ 2 := by
    have hsq : 3 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha3 2
    omega
  have h8Mul : 8 * a ≤ a ^ 3 := by
    calc
      8 * a ≤ a ^ 2 * a := Nat.mul_le_mul_right a h8leSq
      _ = a ^ 3 := by ring
  have hXL : 4 * Y < (a + 1) ^ 3 := by
    have h8a : 4 * Y ≤ 8 * a := by omega
    have hcubic : a ^ 3 < (a + 1) ^ 3 :=
      pow_lt_pow_left₀ (by omega : a < a + 1) (Nat.zero_le a) (by norm_num)
    exact lt_of_le_of_lt (h8a.trans h8Mul) hcubic
  have hLX : a ≤ 4 * Y := by omega
  have hXaNat : 4 * Y ≤ a ^ 3 := by
    have h8a : 4 * Y ≤ 8 * a := by omega
    exact h8a.trans h8Mul
  have hXa : ((4 * Y : ℕ) : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) := by exact_mod_cast hXaNat
  have hH : (0 : ℝ) < (Y : ℝ) := by positivity
  have hYX : (Y : ℝ) + (Y : ℝ) ≤ ((4 * Y : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hscale : ((2 ^ 6 : ℕ) : ℝ) * (2 : ℝ) ^ (0 : ℝ) ≤ (a : ℝ) := by
    norm_num
    exact_mod_cast (show (64 : ℕ) ≤ a by omega)
  have hV : (0 : ℝ) ≤ (cells : ℝ) / 2 := by positivity
  have hgrid : 2 * ((cells : ℝ) / 2) = (cells : ℝ) * 1 := by ring
  have hhalfT : (1 : ℝ) / 2 ≤ T := by linarith
  have hQ' : (Real.log (a : ℝ)) ^ (-300 : ℝ) <
      (B - heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma *
          menonWideIntervalAmbientKernelMajorant C0 (4 * Y) (Y : ℝ) sigma *
            (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
        ((cells : ℝ) * 1 *
          menonWideIntervalAmbientKernelMajorant C0 (4 * Y) (Y : ℝ) sigma) := by
    simpa only [mul_one] using hQ
  have hbound := ha (L := a) (X := 4 * Y) (Y := Y) (cells := cells)
    (T0 := 2) (t := 0) (H := (Y : ℝ)) (B := B) (sigma := sigma)
    (V := (cells : ℝ) / 2) (Δ := 1) (T := T)
    hX haY hXL (by norm_num) hscale (by exact_mod_cast ha64) ha1 hLX hXa hH hYX hsigma hB hV
    (by norm_num) hcells hgrid hT hhalfT h2T hQ'
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using hbound

set_option maxHeartbeats 800000 in
/-- Structural Case-II specialization for a narrow prime block with an arbitrary positive
smoothing width fitting inside the enlarged ambient cutoff. -/
theorem exists_absolute_eventually_volume_real_menonHarmonicPrimeBlock_caseII_orderFourHundred_narrow_smoothing_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {Y cells : ℕ} {H B sigma T : ℝ},
        a < Y → Y ≤ 2 * a → 0 < H → H ≤ 3 * (Y : ℝ) →
        1 < sigma → 0 ≤ B → 0 < cells →
        1 ≤ T → (cells : ℝ) / 4 ≤ T → 2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
            ((cells : ℝ) * C)
        (Real.log (a : ℝ)) ^ (-300 : ℝ) < Q →
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope (4 * Y)) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        volume.real
            (menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet
              a (4 * Y) Y H B T ((cells : ℝ) / 2)) ≤
          2 * (2 * Real.pi)⁻¹ *
            (4 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1)) := by
  obtain ⟨C0, hC0, hmain⟩ :=
    exists_absolute_eventually_volume_real_menonHarmonicPrimeBlockExceptionalSet_caseII_wide_orderFourHundred_twoSided_le
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop ((64 : ℕ) ^ 8)] with a ha ha64
  intro Y cells H B sigma T haY hYa hH hHY hsigma hB hcells hT hcellsT h2T
  dsimp only
  intro hQ
  have ha1 : 1 ≤ a := by omega
  have hY1 : 1 ≤ Y := by omega
  have hX : 1 ≤ 4 * Y := by omega
  have ha3 : 3 ≤ a := by omega
  have h8leSq : 8 ≤ a ^ 2 := by
    have hsq : 3 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha3 2
    omega
  have h8Mul : 8 * a ≤ a ^ 3 := by
    calc
      8 * a ≤ a ^ 2 * a := Nat.mul_le_mul_right a h8leSq
      _ = a ^ 3 := by ring
  have hXL : 4 * Y < (a + 1) ^ 3 := by
    have h8a : 4 * Y ≤ 8 * a := by omega
    have hcubic : a ^ 3 < (a + 1) ^ 3 :=
      pow_lt_pow_left₀ (by omega : a < a + 1) (Nat.zero_le a) (by norm_num)
    exact lt_of_le_of_lt (h8a.trans h8Mul) hcubic
  have hLX : a ≤ 4 * Y := by omega
  have hXaNat : 4 * Y ≤ a ^ 3 := by
    have h8a : 4 * Y ≤ 8 * a := by omega
    exact h8a.trans h8Mul
  have hXa : ((4 * Y : ℕ) : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) := by exact_mod_cast hXaNat
  have hYX : (Y : ℝ) + H ≤ ((4 * Y : ℕ) : ℝ) := by
    push_cast
    linarith
  have hscale : ((2 ^ 6 : ℕ) : ℝ) * (2 : ℝ) ^ (0 : ℝ) ≤ (a : ℝ) := by
    norm_num
    exact_mod_cast (show (64 : ℕ) ≤ a by omega)
  have hV : (0 : ℝ) ≤ (cells : ℝ) / 2 := by positivity
  have hgrid : 2 * ((cells : ℝ) / 2) = (cells : ℝ) * 1 := by ring
  have hhalfT : (1 : ℝ) / 2 ≤ T := by linarith
  have hQ' : (Real.log (a : ℝ)) ^ (-300 : ℝ) <
      (B - heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma *
          menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma *
            (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
        ((cells : ℝ) * 1 *
          menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma) := by
    simpa only [mul_one] using hQ
  have hbound := ha (L := a) (X := 4 * Y) (Y := Y) (cells := cells)
    (T0 := 2) (t := 0) (H := H) (B := B) (sigma := sigma)
    (V := (cells : ℝ) / 2) (Δ := 1) (T := T)
    hX haY hXL (by norm_num) hscale (by exact_mod_cast ha64) ha1 hLX hXa hH hYX hsigma hB hV
    (by norm_num) hcells hgrid hT hhalfT h2T hQ'
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using hbound

set_option maxHeartbeats 800000 in
/-- Every literal truncated final-range block inherits the structural Case-II estimate. -/
theorem exists_absolute_eventually_volume_real_menonFinalRangeBlock_caseII_orderFourHundred_le :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonTruncatedRangeLadderSteps x),
        ∀ {cells : ℕ} {B sigma T : ℝ},
        1 < sigma → 0 ≤ B → 0 < cells →
        1 ≤ T → (cells : ℝ) / 4 ≤ T →
        2 * T ≤ (menonFinalRangeBlockLowerNat x j : ℝ) ^ (3 : ℕ) →
        let a : ℕ := menonFinalRangeBlockLowerNat x j
        let Y : ℕ := menonFinalRangeBlockUpperNat x j
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 (4 * Y) (Y : ℝ) sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
            ((cells : ℝ) * C)
        (Real.log (a : ℝ)) ^ (-300 : ℝ) < Q →
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope (4 * Y)) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        volume.real
            (menonHarmonicPrimeBlockWideOrderFourHundredGallagherExceptionalSet
              a (4 * Y) Y (Y : ℝ) B T ((cells : ℝ) / 2)) ≤
          2 * (2 * Real.pi)⁻¹ *
            (4 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1)) := by
  obtain ⟨C0, hC0, hcase⟩ :=
    exists_absolute_eventually_volume_real_menonHarmonicPrimeBlock_caseII_orderFourHundred_narrow_le
  rw [eventually_atTop] at hcase
  obtain ⟨a0, hcase⟩ := hcase
  have hbase := tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop a0
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [eventually_menonFinalRangeBlock_caseII_endpoints, hbase,
    eventually_two_le_menonFinalRangePrimeCutoffNat,
    eventually_menonTruncatedRangeLadder_basic] with x hx hbaseX hbaseTwo hbasic
  intro j hj cells B sigma T hsigma hB hcells hT hcellsT h2T
  have hend := hx j hj
  rcases hend with ⟨ha64, haY, hYa⟩
  have hbaseLe : menonFinalRangePrimeCutoffNat x ≤ menonFinalRangeBlockLowerNat x j := by
    have hbase0 : 0 < menonFinalRangeLadderBase x := by
      rw [menonFinalRangeLadderBase]
      exact_mod_cast (show 0 < menonFinalRangePrimeCutoffNat x by omega)
    have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by
      rcases hbasic with ⟨_, _, _, _, _, heta, _⟩
      linarith
    have hq : menonFinalRangeLadderBase x ≤
        menonFinalRangeLadderBase x * (1 + menonFinalRangeLadderEta x) ^ j := by
      exact le_mul_of_one_le_right hbase0.le (one_le_pow₀ hstep)
    rw [menonFinalRangeBlockLowerNat,
      ← Nat.floor_natCast (R := ℝ) (menonFinalRangePrimeCutoffNat x)]
    exact Nat.floor_mono hq
  have ha0 : a0 ≤ menonFinalRangeBlockLowerNat x j := hbaseX.trans hbaseLe
  exact hcase (menonFinalRangeBlockLowerNat x j) ha0 haY hYa hsigma hB hcells hT hcellsT h2T

end

end RHTower.Sieve
