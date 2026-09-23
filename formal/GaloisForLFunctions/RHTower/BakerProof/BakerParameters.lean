import GaloisForLFunctions.RHTower.BakerProof.AuxiliaryExtrapolation

/-!
# Polynomial parameter family for Baker extrapolation

The exponents are chosen so the auxiliary matrix has more columns than rows while the Schwarz
denominator lives at scale `t ^ (12 * n)` and every positive analytic or height contribution lives
at least one full power of `t` lower.  This strict scale gap drives the final smallness argument.
-/

open scoped Classical
open NumberField
open Filter
open Topology

namespace GaloisForLFunctions.RHTower.BakerProof.BakerParameters

/-- Width of the auxiliary exponent box. -/
def exponentWidth (n t : ℕ) : ℕ := 2 * t ^ (8 * n - 4)

/-- Number of initial integer samples. -/
def sampleCount (n t : ℕ) : ℕ := t ^ (4 * n)

/-- Multiplicity used in one extrapolation step. -/
def extrapolationOrder (n t : ℕ) : ℕ := t ^ (8 * n)

/-- Multiindex cutoff, leaving half the box available for shifts. -/
def derivativeCutoff (n t : ℕ) : ℕ := 2 * extrapolationOrder n t

/-- Schwarz-disc radius. -/
def extrapolationRadius (n t : ℕ) : ℕ := t ^ (4 * n + 1)

/-- Number of natural samples in the first quarter of the Schwarz disc, including zero. -/
def quarterSampleCount (n t : ℕ) : ℕ := extrapolationRadius n t / 4 + 1

/-- The complete positive factor in the first extrapolation step after the Schwarz node ratio has
been separated off. -/
noncomputable def firstStepGrowth (R : Relation) (c : ℤ) (t : ℕ) : ℝ :=
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let T := derivativeCutoff R.n t
  let radius := extrapolationRadius R.n t
  let Hη := R.auxiliaryCoefficientBoundClosed c L S T
  ((L ^ R.n : ℕ) : ℝ) *
      (Hη * Real.exp ((L * R.primeLogWeight) * radius)) *
    (((L ^ R.n : ℕ) : ℝ) *
      (Hη * (R.primeProduct : ℝ) ^ (L * S))) ^
        (Module.finrank ℚ R.CoefficientField - 1)

/-- The coefficient budget after replacing the Siegel exponent by its upper bound one. -/
noncomputable def linearCoefficientBudget (R : Relation) (c : ℤ) (t : ℕ) : ℝ :=
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let T := derivativeCutoff R.n t
  GelfondSchneiderSiegel.c₁ R.CoefficientField *
    (GelfondSchneiderSiegel.c₁ R.CoefficientField * ((L ^ R.n : ℕ) : ℝ) *
      R.auxiliaryHeightClosed c L S T)

/-- A purely integer-power majorant for the first-step positive growth.  Unlike `firstStepGrowth`,
it contains no real Siegel exponent. -/
noncomputable def firstStepGrowthMajorant (R : Relation) (c : ℤ) (t : ℕ) : ℝ :=
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let radius := extrapolationRadius R.n t
  let Hη := linearCoefficientBudget R c t
  ((L ^ R.n : ℕ) : ℝ) *
      (Hη * Real.exp ((L * R.primeLogWeight) * radius)) *
    (((L ^ R.n : ℕ) : ℝ) *
      (Hη * (R.primeProduct : ℝ) ^ (L * S))) ^
        (Module.finrank ℚ R.CoefficientField - 1)

/-- The algebraic base raised to the number-field degree in the normal form of the first-step
majorant. -/
noncomputable def firstStepNormalBase (R : Relation) (c : ℤ) (t : ℕ) : ℝ :=
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let T := derivativeCutoff R.n t
  GelfondSchneiderSiegel.c₁ R.CoefficientField ^ (2 : ℕ) *
    (((L ^ R.n : ℕ) : ℝ) ^ (2 : ℕ)) *
    (((S * T ^ (R.n - 1)) * L ^ R.n : ℕ) : ℝ) *
    (2 * L * R.scaledCoefficientHouseSum c) ^ ((R.n - 1) * T) *
    (R.primeProduct : ℝ) ^ (L * S)

/-- Fixed coefficient multiplying the dominant scale in the final exponential majorant. -/
noncomputable def growthExponentConstant (R : Relation) : ℝ :=
  let d := Module.finrank ℚ R.CoefficientField - 1
  R.primeLogWeight + (d + 1) * (2 * R.n + 2) + d

/-- The complete first-step majorant for a shifted component of total multiindex degree `v`. -/
noncomputable def shiftedFirstStepGrowthMajorant
    (R : Relation) (c : ℤ) (t v : ℕ) : ℝ :=
  let L := exponentWidth R.n t
  let d := Module.finrank ℚ R.CoefficientField - 1
  (2 * L * R.scaledCoefficientHouseSum c) ^ (v * (d + 1)) *
    firstStepGrowthMajorant R c t

/-- Fixed exponential coefficient after uniformly allowing every shifted component in the lower
half of the multiindex box. -/
noncomputable def shiftedGrowthExponentConstant (R : Relation) : ℝ :=
  let d := Module.finrank ℚ R.CoefficientField - 1
  growthExponentConstant R + ((R.n - 1) * (d + 1) : ℕ)

/-- A uniform growth majorant for every natural sample in the fixed Schwarz disc. -/
noncomputable def radiusStepGrowthMajorant
    (R : Relation) (c : ℤ) (t v : ℕ) : ℝ :=
  let L := exponentWidth R.n t
  let radius := extrapolationRadius R.n t
  let d := Module.finrank ℚ R.CoefficientField - 1
  shiftedFirstStepGrowthMajorant R c t v *
    ((R.primeProduct : ℝ) ^ (L * radius)) ^ d

/-- Fixed exponential coefficient for the full shifted-component, quarter-disc sample window. -/
noncomputable def radiusGrowthExponentConstant (R : Relation) : ℝ :=
  let d := Module.finrank ℚ R.CoefficientField - 1
  shiftedGrowthExponentConstant R + d * Real.log R.primeProduct

theorem firstStepGrowth_nonneg (R : Relation) (c : ℤ) (t : ℕ) :
    0 ≤ firstStepGrowth R c t := by
  unfold firstStepGrowth
  dsimp only
  have hH := R.auxiliaryCoefficientBoundClosed_nonneg c
    (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hH (Real.exp_nonneg _)))
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hH (pow_nonneg (Nat.cast_nonneg _) _))) _)

theorem linearCoefficientBudget_nonneg (R : Relation) (c : ℤ) (t : ℕ) :
    0 ≤ linearCoefficientBudget R c t := by
  unfold linearCoefficientBudget
  dsimp only
  exact mul_nonneg R.siegelConstant_nonneg
    (mul_nonneg (mul_nonneg R.siegelConstant_nonneg (Nat.cast_nonneg _))
      (R.auxiliaryHeightClosed_nonneg c
        (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)))

theorem firstStepGrowthMajorant_nonneg (R : Relation) (c : ℤ) (t : ℕ) :
    0 ≤ firstStepGrowthMajorant R c t := by
  unfold firstStepGrowthMajorant
  dsimp only
  have hH := linearCoefficientBudget_nonneg R c t
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hH (Real.exp_nonneg _)))
    (pow_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hH (pow_nonneg (Nat.cast_nonneg _) _))) _)

theorem firstStepNormalBase_nonneg (R : Relation) (c : ℤ) (t : ℕ) :
    0 ≤ firstStepNormalBase R c t := by
  have hC : 0 ≤ R.scaledCoefficientHouseSum c := by
    unfold Relation.scaledCoefficientHouseSum
    exact Finset.sum_nonneg fun i hi => house_nonneg _
  unfold firstStepNormalBase
  dsimp only
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg R.siegelConstant_nonneg 2)
          (pow_nonneg (Nat.cast_nonneg _) 2))
        (Nat.cast_nonneg _))
      (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hC) _))
    (pow_nonneg (Nat.cast_nonneg _) _)

theorem growthExponentConstant_nonneg (R : Relation) :
    0 ≤ growthExponentConstant R := by
  have hlog : 0 ≤ R.primeLogWeight := by
    unfold Relation.primeLogWeight
    exact Finset.sum_nonneg fun i hi => (R.p_prime i).log_pos.le
  unfold growthExponentConstant
  dsimp only
  positivity

/-- Exact normal form: one analytic exponential and two ordinary natural powers. -/
theorem firstStepGrowthMajorant_eq_normalForm (R : Relation) (c : ℤ) (t : ℕ) :
    let L := exponentWidth R.n t
    let S := sampleCount R.n t
    let radius := extrapolationRadius R.n t
    let d := Module.finrank ℚ R.CoefficientField - 1
    firstStepGrowthMajorant R c t =
      Real.exp ((L * R.primeLogWeight) * radius) *
        firstStepNormalBase R c t ^ (d + 1) *
        ((R.primeProduct : ℝ) ^ (L * S)) ^ d := by
  dsimp only
  unfold firstStepGrowthMajorant firstStepNormalBase linearCoefficientBudget
    Relation.auxiliaryHeightClosed
  dsimp only
  rw [pow_succ']
  simp only [mul_pow]
  ring

/-- Every fixed real multiple of a polynomial in a natural variable is eventually bounded by the
ordinary real exponential. -/
theorem eventually_const_mul_natCast_pow_le_exp (C : ℝ) (k : ℕ) :
    ∀ᶠ t : ℕ in atTop, C * (t : ℝ) ^ k ≤ Real.exp t := by
  have hratio : ∀ᶠ t : ℕ in atTop,
      C ≤ Real.exp (t : ℝ) / (t : ℝ) ^ k :=
    ((Real.tendsto_exp_div_pow_atTop k).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop C
  filter_upwards [hratio, eventually_ge_atTop 1] with t ht ht1
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht1
  exact (le_div_iff₀ (pow_pos htpos _)).mp ht

theorem rowColumnCount_cast_eq (n t : ℕ) :
    ((((sampleCount n t * derivativeCutoff n t ^ (n - 1)) *
        exponentWidth n t ^ n : ℕ) : ℝ)) =
      (2 ^ (2 * n - 1) : ℝ) *
        (t : ℝ) ^ (4 * n + (8 * n) * (n - 1) + (8 * n - 4) * n) := by
  simp only [sampleCount, derivativeCutoff, extrapolationOrder, exponentWidth,
    Nat.cast_mul, Nat.cast_pow, mul_pow, ← pow_mul]
  rw [pow_add, pow_add]
  have hpow : (2 : ℝ) ^ (n - 1) * 2 ^ n = 2 ^ (2 * n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [← hpow]
  ring

theorem columnCountSq_cast_eq (n t : ℕ) :
    ((((exponentWidth n t ^ n : ℕ) : ℝ)) ^ (2 : ℕ)) =
      (2 ^ (2 * n) : ℝ) * (t : ℝ) ^ ((8 * n - 4) * n * 2) := by
  simp only [exponentWidth, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, mul_pow, ← pow_mul]
  congr 2
  omega

theorem directionBase_eq_const_mul_pow (R : Relation) (c : ℤ) (t : ℕ) :
    (2 : ℝ) * exponentWidth R.n t * R.scaledCoefficientHouseSum c =
      (4 * R.scaledCoefficientHouseSum c) *
        (t : ℝ) ^ (8 * R.n - 4) := by
  simp [exponentWidth]
  ring

/-- The algebraic normal-form base is eventually controlled by an exponential whose exponent keeps
the exact derivative and sample scales visible. -/
theorem eventually_firstStepNormalBase_le_exp_raw
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop,
      firstStepNormalBase R c t ≤
        Real.exp (3 * (t : ℝ) +
          (t : ℝ) * ((R.n - 1) * derivativeCutoff R.n t) +
          (t : ℝ) * (exponentWidth R.n t * sampleCount R.n t)) := by
  have hc1 := eventually_const_mul_natCast_pow_le_exp
    (GelfondSchneiderSiegel.c₁ R.CoefficientField ^ (2 : ℕ)) 0
  have hL := eventually_const_mul_natCast_pow_le_exp
    (2 ^ (2 * R.n) : ℝ) ((8 * R.n - 4) * R.n * 2)
  have hRC := eventually_const_mul_natCast_pow_le_exp
    (2 ^ (2 * R.n - 1) : ℝ)
    (4 * R.n + (8 * R.n) * (R.n - 1) + (8 * R.n - 4) * R.n)
  have hD := eventually_const_mul_natCast_pow_le_exp
    (4 * R.scaledCoefficientHouseSum c) (8 * R.n - 4)
  have hP := eventually_const_mul_natCast_pow_le_exp (R.primeProduct : ℝ) 0
  filter_upwards [hc1, hL, hRC, hD, hP] with t hc1t hLt hRCt hDt hPt
  have hL' : ((((exponentWidth R.n t ^ R.n : ℕ) : ℝ)) ^ (2 : ℕ)) ≤ Real.exp t := by
    rw [columnCountSq_cast_eq]
    simpa using hLt
  have hRC' : ((((sampleCount R.n t * derivativeCutoff R.n t ^ (R.n - 1)) *
      exponentWidth R.n t ^ R.n : ℕ) : ℝ)) ≤ Real.exp t := by
    rw [rowColumnCount_cast_eq]
    exact hRCt
  have hD' : (2 : ℝ) * exponentWidth R.n t * R.scaledCoefficientHouseSum c ≤
      Real.exp t := by
    rw [directionBase_eq_const_mul_pow]
    exact hDt
  have hP' : (R.primeProduct : ℝ) ≤ Real.exp t := by
    simpa using hPt
  have hc1' : GelfondSchneiderSiegel.c₁ R.CoefficientField ^ (2 : ℕ) ≤ Real.exp t := by
    simpa using hc1t
  have hC : 0 ≤ R.scaledCoefficientHouseSum c := by
    unfold Relation.scaledCoefficientHouseSum
    exact Finset.sum_nonneg fun i hi => house_nonneg _
  have hD0 : 0 ≤ (2 : ℝ) * exponentWidth R.n t * R.scaledCoefficientHouseSum c :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hC
  unfold firstStepNormalBase
  dsimp only
  calc
    GelfondSchneiderSiegel.c₁ R.CoefficientField ^ (2 : ℕ) *
        (((exponentWidth R.n t ^ R.n : ℕ) : ℝ) ^ (2 : ℕ)) *
        (((sampleCount R.n t * derivativeCutoff R.n t ^ (R.n - 1)) *
          exponentWidth R.n t ^ R.n : ℕ) : ℝ) *
        (2 * exponentWidth R.n t * R.scaledCoefficientHouseSum c) ^
          ((R.n - 1) * derivativeCutoff R.n t) *
        (R.primeProduct : ℝ) ^
          (exponentWidth R.n t * sampleCount R.n t) ≤
      Real.exp t * Real.exp t * Real.exp t *
        (Real.exp t) ^ ((R.n - 1) * derivativeCutoff R.n t) *
        (Real.exp t) ^ (exponentWidth R.n t * sampleCount R.n t) := by
      gcongr
    _ = Real.exp (3 * (t : ℝ) +
          (t : ℝ) * ((R.n - 1) * derivativeCutoff R.n t) +
          (t : ℝ) * (exponentWidth R.n t * sampleCount R.n t)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ R.n), Nat.cast_one]
      ring

theorem rawExponent_le_dominant {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ≤ t) :
    3 * t + t * ((n - 1) * derivativeCutoff n t) +
        t * (exponentWidth n t * sampleCount n t) ≤
      (2 * n + 2) * t ^ (12 * n - 1) := by
  let N := t ^ (12 * n - 1)
  have hNexp : 1 ≤ 12 * n - 1 := by omega
  have htN : t ≤ N := by
    simpa [N] using pow_le_pow_right₀ (by omega : 1 ≤ t) hNexp
  have hderivEq : t * ((n - 1) * derivativeCutoff n t) =
      (2 * (n - 1)) * t ^ (8 * n + 1) := by
    unfold derivativeCutoff extrapolationOrder
    rw [pow_succ']
    ring
  have hderivPow : t ^ (8 * n + 1) ≤ N := by
    exact pow_le_pow_right₀ (by omega : 1 ≤ t) (by omega)
  have hderiv : t * ((n - 1) * derivativeCutoff n t) ≤
      (2 * (n - 1)) * N := by
    rw [hderivEq]
    exact Nat.mul_le_mul_left _ hderivPow
  have hsampleEq : t * (exponentWidth n t * sampleCount n t) =
      2 * t ^ (12 * n - 3) := by
    unfold exponentWidth sampleCount
    calc
      t * (2 * t ^ (8 * n - 4) * t ^ (4 * n)) =
          2 * ((t ^ (8 * n - 4) * t ^ (4 * n)) * t) := by ring
      _ = 2 * (t ^ ((8 * n - 4) + 4 * n) * t) := by rw [← pow_add]
      _ = 2 * t ^ (((8 * n - 4) + 4 * n) + 1) := by rw [pow_succ]
      _ = 2 * t ^ (12 * n - 3) := by congr 2; omega
  have hsample : t * (exponentWidth n t * sampleCount n t) ≤ N := by
    rw [hsampleEq]
    have htwo : 2 ≤ t ^ (2 : ℕ) := by
      exact ht.trans (Nat.le_pow (by omega))
    calc
      2 * t ^ (12 * n - 3) ≤ t ^ (2 : ℕ) * t ^ (12 * n - 3) :=
        Nat.mul_le_mul_right _ htwo
      _ = N := by
        rw [← pow_add]
        simp only [N]
        congr 1
        omega
  have hcoef : 3 + 2 * (n - 1) + 1 = 2 * n + 2 := by omega
  calc
    3 * t + t * ((n - 1) * derivativeCutoff n t) +
        t * (exponentWidth n t * sampleCount n t) ≤
      3 * N + (2 * (n - 1)) * N + N := by
        exact add_le_add (add_le_add (Nat.mul_le_mul_left 3 htN) hderiv) hsample
    _ = (3 + 2 * (n - 1) + 1) * N := by ring
    _ = (2 * n + 2) * N := by rw [hcoef]

theorem eventually_firstStepNormalBase_le_exp_dominant
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop,
      firstStepNormalBase R c t ≤
        Real.exp ((2 * R.n + 2) * (t ^ (12 * R.n - 1) : ℕ)) := by
  filter_upwards [eventually_firstStepNormalBase_le_exp_raw R hn c,
    eventually_ge_atTop 2] with t hraw ht
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  have hnat := rawExponent_le_dominant hn ht
  have hnsub : (R.n : ℝ) - 1 = ((R.n - 1 : ℕ) : ℝ) := by
    simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ R.n)).symm
  rw [hnsub]
  exact_mod_cast hnat

/-- The corrected parameter family has exactly twice as many columns as matrix rows. -/
theorem double_rowCount_eq_columnCount {n t : ℕ} (hn : 3 ≤ n) :
    2 * (sampleCount n t * derivativeCutoff n t ^ (n - 1)) =
      exponentWidth n t ^ n := by
  unfold sampleCount derivativeCutoff extrapolationOrder exponentWidth
  simp only [mul_pow]
  rw [← pow_mul, ← pow_mul]
  have hexp : (8 * n - 4) * n = 4 * n + (8 * n) * (n - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h₁ : 8 * (3 + k) - 4 = 20 + 8 * k := by omega
    have h₂ : 3 + k - 1 = 2 + k := by omega
    rw [h₁, h₂]
    ring
  rw [hexp, pow_add]
  have h2pow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    calc
      2 * 2 ^ (n - 1) = 2 ^ ((n - 1) + 1) := by rw [pow_succ']
      _ = 2 ^ n := by congr 1; omega
  rw [← h2pow]
  ring

/-- The polynomial parameter family always gives fewer matrix rows than columns once the reduced
relation has arity at least three. -/
theorem dimension_inequality {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ≤ t) :
    sampleCount n t * derivativeCutoff n t ^ (n - 1) <
      exponentWidth n t ^ n := by
  rw [← double_rowCount_eq_columnCount hn]
  have hrows : 0 < sampleCount n t * derivativeCutoff n t ^ (n - 1) := by
    unfold sampleCount derivativeCutoff extrapolationOrder
    positivity
  omega

/-- The exact two-to-one count makes the Siegel exponent `rows/(cols-rows)` at most one. -/
theorem double_rowCount_le_columnCount {n t : ℕ} (hn : 3 ≤ n) :
    2 * (sampleCount n t * derivativeCutoff n t ^ (n - 1)) ≤
      exponentWidth n t ^ n :=
  (double_rowCount_eq_columnCount hn).le

/-- The column count is the product of the lower shift-box count and the exact residual sample
factor `2^n * S`. -/
theorem columnCount_eq_twoPow_mul_sample_shift {n t : ℕ} (hn : 3 ≤ n) :
    exponentWidth n t ^ n =
      2 ^ n * (sampleCount n t * extrapolationOrder n t ^ (n - 1)) := by
  rw [← double_rowCount_eq_columnCount hn]
  unfold derivativeCutoff
  rw [mul_pow]
  have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    calc
      2 * 2 ^ (n - 1) = 2 ^ ((n - 1) + 1) := by rw [pow_succ']
      _ = 2 ^ n := by congr 1; omega
  rw [← hpow]
  ring

/-- Once the parameter base exceeds the fixed arity constant, the extrapolated quarter-disc row
box contains strictly more conditions than auxiliary columns. -/
theorem columnCount_lt_quarterSample_shift_count
    {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ^ (n + 2) < t) :
    exponentWidth n t ^ n <
      quarterSampleCount n t * extrapolationOrder n t ^ (n - 1) := by
  rw [columnCount_eq_twoPow_mul_sample_shift hn]
  have htpos : 0 < t :=
    lt_trans (pow_pos (by norm_num : 0 < (2 : ℕ)) _) ht
  have hSpos : 0 < sampleCount n t := by
    unfold sampleCount
    exact pow_pos htpos _
  have hscale : 2 ^ n * sampleCount n t ≤ extrapolationRadius n t / 4 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr
    have hradius : extrapolationRadius n t = t * sampleCount n t := by
      simp [extrapolationRadius, sampleCount, pow_succ, mul_comm]
    rw [hradius]
    have hmul := Nat.mul_le_mul_right (sampleCount n t) ht.le
    calc
      (2 ^ n * sampleCount n t) * 4 =
          2 ^ (n + 2) * sampleCount n t := by
        rw [pow_add]
        ring
      _ ≤ t * sampleCount n t := hmul
  have hcount : 2 ^ n * sampleCount n t < quarterSampleCount n t := by
    simpa [quarterSampleCount] using Nat.lt_succ_of_le hscale
  have hqpos : 0 < extrapolationOrder n t ^ (n - 1) := by
    unfold extrapolationOrder
    exact pow_pos (pow_pos htpos _) _
  have hmul := (Nat.mul_lt_mul_right hqpos).mpr hcount
  simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

theorem Relation.parameterizedCoefficientBoundClosed_le_linear
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (t : ℕ) (ht : 2 ≤ t) :
    R.auxiliaryCoefficientBoundClosed c
        (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) ≤
      GelfondSchneiderSiegel.c₁ R.CoefficientField *
        (GelfondSchneiderSiegel.c₁ R.CoefficientField *
          (((exponentWidth R.n t) ^ R.n : ℕ) : ℝ) *
          R.auxiliaryHeightClosed c
            (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) := by
  have hL : 0 < exponentWidth R.n t := by
    unfold exponentWidth
    exact mul_pos (by norm_num) (pow_pos (lt_of_lt_of_le (by norm_num) ht) _)
  have hS : 0 < sampleCount R.n t := by
    unfold sampleCount
    exact pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hT : 0 < derivativeCutoff R.n t := by
    unfold derivativeCutoff extrapolationOrder
    positivity
  apply R.auxiliaryCoefficientBoundClosed_le_linear
  · exact mul_pos hS (pow_pos hT _)
  · exact double_rowCount_le_columnCount hn
  · exact R.one_le_auxiliaryHeightClosed c hc hint pivot hL hS hT

theorem Relation.firstStepGrowth_le_majorant
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (t : ℕ) (ht : 2 ≤ t) :
    firstStepGrowth R c t ≤ firstStepGrowthMajorant R c t := by
  have hH := Relation.parameterizedCoefficientBoundClosed_le_linear
    R hn c hc hint pivot t ht
  have hclosed := R.auxiliaryCoefficientBoundClosed_nonneg c
    (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)
  have hlinear := linearCoefficientBudget_nonneg R c t
  unfold firstStepGrowth firstStepGrowthMajorant linearCoefficientBudget
  dsimp only
  gcongr

@[simp] theorem extrapolationRadius_eq_mul_sampleCount (n t : ℕ) :
    extrapolationRadius n t = t * sampleCount n t := by
  simp [extrapolationRadius, sampleCount, pow_succ, mul_comm]

theorem sampleCount_lt_extrapolationRadius {n t : ℕ} (ht : 2 ≤ t) :
    sampleCount n t < extrapolationRadius n t := by
  unfold sampleCount extrapolationRadius
  exact Nat.pow_lt_pow_right (lt_of_lt_of_le (by norm_num) ht) (by omega)

theorem extrapolationOrder_lt_derivativeCutoff {n t : ℕ} (ht : 2 ≤ t) :
    extrapolationOrder n t < derivativeCutoff n t := by
  simp only [extrapolationOrder, derivativeCutoff]
  have hq : 0 < t ^ (8 * n) := pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  omega

theorem exponentWidth_mul_extrapolationRadius {n t : ℕ} (hn : 3 ≤ n) :
    exponentWidth n t * extrapolationRadius n t = 2 * t ^ (12 * n - 3) := by
  unfold exponentWidth extrapolationRadius
  calc
    2 * t ^ (8 * n - 4) * t ^ (4 * n + 1) =
        2 * (t ^ (8 * n - 4) * t ^ (4 * n + 1)) := by ring
    _ = 2 * t ^ ((8 * n - 4) + (4 * n + 1)) := by rw [← pow_add]
    _ = 2 * t ^ (12 * n - 3) := by congr 2; omega

theorem extrapolationOrder_mul_sampleCount {n t : ℕ} :
    extrapolationOrder n t * sampleCount n t = t ^ (12 * n) := by
  unfold extrapolationOrder sampleCount
  rw [← pow_add]
  congr 1
  omega

theorem exponentWidth_mul_sampleCount {n t : ℕ} (hn : 3 ≤ n) :
    exponentWidth n t * sampleCount n t = 2 * t ^ (12 * n - 4) := by
  unfold exponentWidth sampleCount
  calc
    2 * t ^ (8 * n - 4) * t ^ (4 * n) =
        2 * (t ^ (8 * n - 4) * t ^ (4 * n)) := by ring
    _ = 2 * t ^ ((8 * n - 4) + 4 * n) := by rw [← pow_add]
    _ = 2 * t ^ (12 * n - 4) := by congr 2; omega

theorem two_mul_lowerScale_le_dominant {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ≤ t) :
    2 * t ^ (12 * n - 3) ≤ t ^ (12 * n - 1) := by
  have htwo : 2 ≤ t ^ (2 : ℕ) := by
    exact ht.trans (Nat.le_pow (by omega))
  calc
    2 * t ^ (12 * n - 3) ≤ t ^ (2 : ℕ) * t ^ (12 * n - 3) :=
      Nat.mul_le_mul_right _ htwo
    _ = t ^ (12 * n - 1) := by
      rw [← pow_add]
      congr 1
      omega

/-- The complete positive first-step budget is eventually bounded by a fixed exponential constant
times the subdominant scale `t^(12n-1)`. -/
theorem eventually_firstStepGrowthMajorant_le_exp_dominant
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop,
      firstStepGrowthMajorant R c t ≤
        Real.exp (growthExponentConstant R * (t ^ (12 * R.n - 1) : ℕ)) := by
  have hPev := eventually_const_mul_natCast_pow_le_exp (R.primeProduct : ℝ) 0
  filter_upwards [eventually_firstStepNormalBase_le_exp_dominant R hn c,
    hPev, eventually_ge_atTop 2] with t hX hPt ht
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let radius := extrapolationRadius R.n t
  let d := Module.finrank ℚ R.CoefficientField - 1
  let N := t ^ (12 * R.n - 1)
  have hP : (R.primeProduct : ℝ) ≤ Real.exp t := by simpa using hPt
  have hLR : L * radius ≤ N := by
    dsimp only [L, radius, N]
    rw [exponentWidth_mul_extrapolationRadius hn]
    exact two_mul_lowerScale_le_dominant hn ht
  have hLS : t * (L * S) ≤ N := by
    dsimp only [L, S, N]
    rw [exponentWidth_mul_sampleCount hn]
    calc
      t * (2 * t ^ (12 * R.n - 4)) =
          2 * (t ^ (12 * R.n - 4) * t) := by ring
      _ = 2 * t ^ ((12 * R.n - 4) + 1) := by rw [pow_succ]
      _ = 2 * t ^ (12 * R.n - 3) := by congr 2; omega
      _ ≤ t ^ (12 * R.n - 1) := two_mul_lowerScale_le_dominant hn ht
  have hlog : 0 ≤ R.primeLogWeight := by
    unfold Relation.primeLogWeight
    exact Finset.sum_nonneg fun i hi => (R.p_prime i).log_pos.le
  have hanalytic : Real.exp ((L * R.primeLogWeight) * radius) ≤
      Real.exp (R.primeLogWeight * N) := by
    apply Real.exp_le_exp.mpr
    have hLRR : (L : ℝ) * (radius : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLR
    calc
      (L : ℝ) * R.primeLogWeight * (radius : ℝ) =
          R.primeLogWeight * ((L : ℝ) * radius) := by ring
      _ ≤ R.primeLogWeight * N := mul_le_mul_of_nonneg_left hLRR hlog
  have hPM : (R.primeProduct : ℝ) ^ (L * S) ≤
      (Real.exp t) ^ (L * S) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hP _
  have hsampleExp : (Real.exp t) ^ (L * S) ≤ Real.exp N := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact_mod_cast (by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hLS)
  have hPS : (R.primeProduct : ℝ) ^ (L * S) ≤ Real.exp N :=
    hPM.trans hsampleExp
  have hX0 := firstStepNormalBase_nonneg R c t
  rw [firstStepGrowthMajorant_eq_normalForm]
  calc
    Real.exp ((L * R.primeLogWeight) * radius) *
        firstStepNormalBase R c t ^ (d + 1) *
        ((R.primeProduct : ℝ) ^ (L * S)) ^ d ≤
      Real.exp (R.primeLogWeight * N) *
        (Real.exp ((2 * R.n + 2) * N)) ^ (d + 1) *
        (Real.exp N) ^ d := by
      gcongr
    _ = Real.exp (growthExponentConstant R * N) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold growthExponentConstant
      dsimp only [d]
      push_cast
      ring

/-- The extra exponent introduced by every shift in the lower multiindex box remains on the
subdominant scale `t^(12n-1)`. -/
theorem shiftExponent_le_dominant {n d t : ℕ} (hn : 3 ≤ n) (ht : 1 ≤ t) :
    t * ((n - 1) * extrapolationOrder n t * (d + 1)) ≤
      ((n - 1) * (d + 1)) * t ^ (12 * n - 1) := by
  have hpow : t ^ (8 * n + 1) ≤ t ^ (12 * n - 1) :=
    pow_le_pow_right₀ ht (by omega)
  unfold extrapolationOrder
  calc
    t * ((n - 1) * t ^ (8 * n) * (d + 1)) =
        ((n - 1) * (d + 1)) * t ^ (8 * n + 1) := by
      rw [pow_succ']
      ring
    _ ≤ ((n - 1) * (d + 1)) * t ^ (12 * n - 1) :=
      Nat.mul_le_mul_left _ hpow

/-- Geometric Schwarz decay at scale `t^(12n)` dominates any fixed exponential at the strictly
smaller scale `t^(12n-1)`. -/
theorem eventually_decay_mul_exp_dominant_lt_one_const
    (n : ℕ) (hn : 3 ≤ n) (C : ℝ) :
    ∀ᶠ t : ℕ in atTop,
      ((2 : ℝ) / 3) ^ (t ^ (12 * n)) *
        Real.exp (C * (t ^ (12 * n - 1) : ℕ)) < 1 := by
  have hdecayT : Tendsto
      (fun t : ℕ => ((2 : ℝ) / 3) ^ t * Real.exp C)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 3)
      (by norm_num : (2 : ℝ) / 3 < 1)).mul_const
        (Real.exp C)
  have hbase : ∀ᶠ t : ℕ in atTop,
      ((2 : ℝ) / 3) ^ t * Real.exp C < 1 :=
    (tendsto_order.1 hdecayT).2 1 (by norm_num)
  filter_upwards [hbase, eventually_ge_atTop 1] with t ht ht1
  let N := t ^ (12 * n - 1)
  have hNpos : 0 < N := pow_pos (by omega) _
  have hpow : (((2 : ℝ) / 3) ^ t * Real.exp C) ^ N < 1 :=
    pow_lt_one₀ (mul_nonneg (pow_nonneg (by norm_num) _)
      (Real.exp_nonneg _)) ht hNpos.ne'
  have hscale : t ^ (12 * n) = t * N := by
    dsimp only [N]
    calc
      t ^ (12 * n) = t ^ ((12 * n - 1) + 1) := by congr 1; omega
      _ = t * t ^ (12 * n - 1) := by rw [pow_succ']
  have hexp : Real.exp (C * (N : ℕ)) = (Real.exp C) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hscale, pow_mul, hexp, ← mul_pow]
  exact hpow

theorem eventually_decay_mul_exp_dominant_lt_one (R : Relation) (hn : 3 ≤ R.n) :
    ∀ᶠ t : ℕ in atTop,
      ((2 : ℝ) / 3) ^ (t ^ (12 * R.n)) *
        Real.exp (growthExponentConstant R * (t ^ (12 * R.n - 1) : ℕ)) < 1 :=
  eventually_decay_mul_exp_dominant_lt_one_const R.n hn (growthExponentConstant R)

/-- Uniformly over the whole lower shifted-component box, the positive growth budget remains a
fixed exponential on the subdominant scale. -/
theorem eventually_shiftedFirstStepGrowthMajorant_le_exp_dominant
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop, ∀ v : ℕ,
      v ≤ (R.n - 1) * extrapolationOrder R.n t →
      shiftedFirstStepGrowthMajorant R c t v ≤
        Real.exp (shiftedGrowthExponentConstant R *
          (t ^ (12 * R.n - 1) : ℕ)) := by
  let d := Module.finrank ℚ R.CoefficientField - 1
  have hD := eventually_const_mul_natCast_pow_le_exp
    (4 * R.scaledCoefficientHouseSum c) (8 * R.n - 4)
  filter_upwards [eventually_firstStepGrowthMajorant_le_exp_dominant R hn c,
    hD, eventually_ge_atTop 1] with t hfirst hDt ht
  intro v hv
  let q := extrapolationOrder R.n t
  let N := t ^ (12 * R.n - 1)
  let D : ℝ := 2 * exponentWidth R.n t * R.scaledCoefficientHouseSum c
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by
        unfold Relation.scaledCoefficientHouseSum
        exact Finset.sum_nonneg fun i hi => house_nonneg _)
  have hDexp : D ≤ Real.exp t := by
    dsimp only [D]
    rw [directionBase_eq_const_mul_pow]
    exact hDt
  have hvexp : v * (d + 1) ≤ ((R.n - 1) * q) * (d + 1) :=
    Nat.mul_le_mul_right (d + 1) hv
  have hexpone : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp (Nat.cast_nonneg t)
  have hDpow : D ^ (v * (d + 1)) ≤
      (Real.exp t) ^ (((R.n - 1) * q) * (d + 1)) := by
    calc
      D ^ (v * (d + 1)) ≤ (Real.exp t) ^ (v * (d + 1)) :=
        pow_le_pow_left₀ hD0 hDexp _
      _ ≤ (Real.exp t) ^ (((R.n - 1) * q) * (d + 1)) :=
        pow_le_pow_right₀ hexpone hvexp
  have hshiftNat :
      t * ((R.n - 1) * q * (d + 1)) ≤
        ((R.n - 1) * (d + 1)) * N := by
    exact shiftExponent_le_dominant hn ht
  have hshiftReal :
      (t : ℝ) * (((R.n - 1) * q * (d + 1) : ℕ) : ℝ) ≤
        (((R.n - 1) * (d + 1) : ℕ) : ℝ) * (N : ℝ) := by
    exact_mod_cast hshiftNat
  have hDpow' : D ^ (v * (d + 1)) ≤
      Real.exp ((((R.n - 1) * (d + 1) : ℕ) : ℝ) * N) := by
    apply hDpow.trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by
      simpa [q, mul_assoc, mul_comm, mul_left_comm] using hshiftReal)
  have hmajor0 := firstStepGrowthMajorant_nonneg R c t
  unfold shiftedFirstStepGrowthMajorant
  dsimp only
  change D ^ (v * (d + 1)) * firstStepGrowthMajorant R c t ≤ _
  calc
    D ^ (v * (d + 1)) * firstStepGrowthMajorant R c t ≤
        Real.exp ((((R.n - 1) * (d + 1) : ℕ) : ℝ) * N) *
          Real.exp (growthExponentConstant R * N) := by
      exact mul_le_mul hDpow' hfirst hmajor0 (Real.exp_nonneg _)
    _ = Real.exp (shiftedGrowthExponentConstant R * N) := by
      rw [← Real.exp_add]
      unfold shiftedGrowthExponentConstant
      dsimp only
      congr 1
      ring

/-- The full quarter-disc growth majorant remains on the same subdominant exponential scale. -/
theorem eventually_radiusStepGrowthMajorant_le_exp_dominant
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop, ∀ v : ℕ,
      v ≤ (R.n - 1) * extrapolationOrder R.n t →
      radiusStepGrowthMajorant R c t v ≤
        Real.exp (radiusGrowthExponentConstant R *
          (t ^ (12 * R.n - 1) : ℕ)) := by
  filter_upwards [eventually_shiftedFirstStepGrowthMajorant_le_exp_dominant R hn c,
    eventually_ge_atTop 2] with t hshift ht
  intro v hv
  let L := exponentWidth R.n t
  let radius := extrapolationRadius R.n t
  let d := Module.finrank ℚ R.CoefficientField - 1
  let N := t ^ (12 * R.n - 1)
  have hLR : L * radius ≤ N := by
    dsimp only [L, radius, N]
    rw [exponentWidth_mul_extrapolationRadius hn]
    exact two_mul_lowerScale_le_dominant hn ht
  have hPpos : (0 : ℝ) < R.primeProduct := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one R.one_le_primeProduct)
  have hPone : (1 : ℝ) ≤ R.primeProduct := by exact_mod_cast R.one_le_primeProduct
  have hlogP : 0 ≤ Real.log (R.primeProduct : ℝ) := Real.log_nonneg hPone
  have hcast : (L : ℝ) * (radius : ℝ) ≤ (N : ℝ) := by exact_mod_cast hLR
  have hP : (R.primeProduct : ℝ) ^ (L * radius) ≤
      Real.exp (Real.log R.primeProduct * N) := by
    calc
      (R.primeProduct : ℝ) ^ (L * radius) =
          (Real.exp (Real.log R.primeProduct)) ^ (L * radius) := by
        rw [Real.exp_log hPpos]
      _ = Real.exp ((L * radius : ℕ) * Real.log R.primeProduct) := by
        rw [← Real.exp_nat_mul]
      _ = Real.exp (Real.log R.primeProduct * ((L : ℝ) * radius)) := by
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (Real.log R.primeProduct * N) := by
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hcast hlogP)
  have hPpow : ((R.primeProduct : ℝ) ^ (L * radius)) ^ d ≤
      Real.exp ((d : ℝ) * Real.log R.primeProduct * N) := by
    calc
      ((R.primeProduct : ℝ) ^ (L * radius)) ^ d ≤
          (Real.exp (Real.log R.primeProduct * N)) ^ d :=
        pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg _) _) hP _
      _ = Real.exp ((d : ℝ) * Real.log R.primeProduct * N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  unfold radiusStepGrowthMajorant
  dsimp only
  calc
    shiftedFirstStepGrowthMajorant R c t v *
        ((R.primeProduct : ℝ) ^ (L * radius)) ^ d ≤
      Real.exp (shiftedGrowthExponentConstant R * N) *
        Real.exp ((d : ℝ) * Real.log R.primeProduct * N) := by
      exact mul_le_mul (hshift v hv) hPpow
        (pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _)
        (Real.exp_nonneg _)
    _ = Real.exp (radiusGrowthExponentConstant R * N) := by
      rw [← Real.exp_add]
      unfold radiusGrowthExponentConstant
      dsimp only
      congr 1
      ring

/-- Schwarz decay dominates the full shifted-component growth budget uniformly throughout the
quarter-disc sample window. -/
theorem eventually_radiusStepSmallness
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop, ∀ v : ℕ,
      v ≤ (R.n - 1) * extrapolationOrder R.n t →
      ((2 : ℝ) / 3) ^
          (extrapolationOrder R.n t * sampleCount R.n t) *
        radiusStepGrowthMajorant R c t v < 1 := by
  filter_upwards [eventually_radiusStepGrowthMajorant_le_exp_dominant R hn c,
    eventually_decay_mul_exp_dominant_lt_one_const R.n hn
      (radiusGrowthExponentConstant R)] with t hgrowth hdecay
  intro v hv
  rw [extrapolationOrder_mul_sampleCount]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (hgrowth v hv) (pow_nonneg (by norm_num) _)) hdecay

/-- Every natural sample in the first quarter of the Schwarz disc belongs to the closed disc. -/
theorem quarterRadiusSample_mem_closedBall
    {n t sample : ℕ} (hquarter : 4 * sample ≤ extrapolationRadius n t) :
    (sample : ℂ) ∈ Metric.closedBall 0 (extrapolationRadius n t : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [sub_zero, Complex.norm_natCast]
  exact_mod_cast (le_trans (Nat.le_mul_of_pos_left sample (by norm_num)) hquarter)

theorem quarterSample_mem {n t : ℕ} (sample : Fin (quarterSampleCount n t)) :
    4 * (sample : ℕ) ≤ extrapolationRadius n t := by
  have hs : (sample : ℕ) ≤ extrapolationRadius n t / 4 := by
    simpa [quarterSampleCount] using sample.isLt
  have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mp hs
  simpa [mul_comm] using this

/-- Uniform node-ratio decay for every natural sample in the first quarter of the Schwarz disc. -/
theorem quarterRadiusSample_node_ratio_le_two_thirds
    {n t sample : ℕ} (ht : 4 ≤ t)
    (hquarter : 4 * sample ≤ extrapolationRadius n t) :
    let N := extrapolationOrder n t * sampleCount n t
    (((sample + sampleCount n t : ℕ) : ℝ) ^ N /
      ((extrapolationRadius n t : ℝ) - sampleCount n t) ^ N) ≤
        ((2 : ℝ) / 3) ^ N := by
  dsimp only
  have hspos : (0 : ℝ) < sampleCount n t := by
    exact_mod_cast (show 0 < sampleCount n t by
      unfold sampleCount
      exact pow_pos (by omega) _)
  have hrpos : (0 : ℝ) < (extrapolationRadius n t : ℝ) - sampleCount n t := by
    exact sub_pos.mpr (by
      exact_mod_cast sampleCount_lt_extrapolationRadius (show 2 ≤ t by omega))
  rw [← div_pow]
  apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hrpos.le)
  rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 3)]
  rw [extrapolationRadius_eq_mul_sampleCount]
  push_cast
  have htR : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hquarterR : (4 : ℝ) * sample ≤ t * sampleCount n t := by
    have hquarter' := hquarter
    rw [extrapolationRadius_eq_mul_sampleCount] at hquarter'
    exact_mod_cast hquarter'
  nlinarith

/-- The first extrapolated component value vanishes as soon as the separated decay factor dominates
the closed positive growth budget. -/
theorem Relation.firstNewSample_eq_zero_of_decay_growth_lt_one
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (t : ℕ) (ht : 4 ≤ t)
    (η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
      R.auxiliaryCoefficientBoundClosed c
        (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    (hsmall : ((2 : ℝ) / 3) ^
        (extrapolationOrder R.n t * sampleCount R.n t) *
          firstStepGrowthMajorant R c t < 1) :
    R.auxiliaryComponent c pivot (fun _ => 0) η (sampleCount R.n t) = 0 := by
  have hsmallGrowth : ((2 : ℝ) / 3) ^
      (extrapolationOrder R.n t * sampleCount R.n t) *
        firstStepGrowth R c t < 1 := by
    apply lt_of_le_of_lt _ hsmall
    exact mul_le_mul_of_nonneg_left
      (Relation.firstStepGrowth_le_majorant R hn c hc hint pivot t (by omega))
      (pow_nonneg (by norm_num) _)
  apply R.auxiliaryComponent_eq_zero_one_step_scalar
    c hc hint pivot η hker (fun _ => 0) (extrapolationOrder R.n t)
    (fun i => by
      simpa using extrapolationOrder_lt_derivativeCutoff (show 2 ≤ t by omega))
    (R.auxiliaryCoefficientBoundClosed c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    hη
    (R.auxiliaryCoefficientBoundClosed_nonneg c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    (by exact_mod_cast sampleCount_lt_extrapolationRadius (show 2 ≤ t by omega))
    (sampleCount R.n t)
    (quarterRadiusSample_mem_closedBall (by
      rw [extrapolationRadius_eq_mul_sampleCount]
      exact Nat.mul_le_mul_right (sampleCount R.n t) ht))
  simp only [Finset.sum_const_zero, pow_zero, one_mul]
  let N := extrapolationOrder R.n t * sampleCount R.n t
  let node : ℝ := ((sampleCount R.n t + sampleCount R.n t : ℕ) : ℝ)
  let den : ℝ := (extrapolationRadius R.n t : ℝ) - sampleCount R.n t
  let A : ℝ := ((exponentWidth R.n t ^ R.n : ℕ) : ℝ) *
    (R.auxiliaryCoefficientBoundClosed c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) *
      Real.exp ((exponentWidth R.n t * R.primeLogWeight) *
        extrapolationRadius R.n t))
  let H : ℝ := (((exponentWidth R.n t ^ R.n : ℕ) : ℝ) *
    (R.auxiliaryCoefficientBoundClosed c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) *
      (R.primeProduct : ℝ) ^
        (exponentWidth R.n t * sampleCount R.n t))) ^
          (Module.finrank ℚ R.CoefficientField - 1)
  have hratio : node ^ N / den ^ N ≤ ((2 : ℝ) / 3) ^ N :=
    quarterRadiusSample_node_ratio_le_two_thirds ht (by
      rw [extrapolationRadius_eq_mul_sampleCount]
      exact Nat.mul_le_mul_right (sampleCount R.n t) ht)
  have hgrowth : 0 ≤ firstStepGrowth R c t := firstStepGrowth_nonneg R c t
  have hid : (node ^ N * (A / den ^ N)) * H =
      (node ^ N / den ^ N) * firstStepGrowth R c t := by
    simp only [firstStepGrowth]
    dsimp only [N, node, den, A, H]
    ring
  rw [show
    (((sampleCount R.n t + sampleCount R.n t : ℕ) : ℝ) ^
        (extrapolationOrder R.n t * sampleCount R.n t) *
      (A / den ^ (extrapolationOrder R.n t * sampleCount R.n t))) * H =
      (node ^ N / den ^ N) * firstStepGrowth R c t by
        simpa [N, node, den] using hid]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hratio hgrowth) hsmallGrowth

/-- The same exact extrapolation step, uniformly retaining the full shifted-direction factor. -/
theorem Relation.firstNewSample_shifted_eq_zero_of_decay_growth_lt_one
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (t : ℕ) (ht : 4 ≤ t)
    (η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
      R.auxiliaryCoefficientBoundClosed c
        (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    (ν : R.NonPivot pivot → ℕ)
    (hνq : ∀ i, ν i + extrapolationOrder R.n t < derivativeCutoff R.n t)
    (hsmall : ((2 : ℝ) / 3) ^
        (extrapolationOrder R.n t * sampleCount R.n t) *
          shiftedFirstStepGrowthMajorant R c t (∑ i, ν i) < 1) :
    R.auxiliaryComponent c pivot ν η (sampleCount R.n t) = 0 := by
  let v := ∑ i, ν i
  let D : ℝ := 2 * exponentWidth R.n t * R.scaledCoefficientHouseSum c
  let d := Module.finrank ℚ R.CoefficientField - 1
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by
        unfold Relation.scaledCoefficientHouseSum
        exact Finset.sum_nonneg fun i hi => house_nonneg _)
  have hsmallGrowth : ((2 : ℝ) / 3) ^
      (extrapolationOrder R.n t * sampleCount R.n t) *
        (D ^ (v * (d + 1)) * firstStepGrowth R c t) < 1 := by
    apply lt_of_le_of_lt _ hsmall
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) _)
    apply mul_le_mul_of_nonneg_left
      (Relation.firstStepGrowth_le_majorant R hn c hc hint pivot t (by omega))
    exact pow_nonneg hD0 _
  apply R.auxiliaryComponent_eq_zero_one_step_scalar
    c hc hint pivot η hker ν (extrapolationOrder R.n t) hνq
    (R.auxiliaryCoefficientBoundClosed c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    hη
    (R.auxiliaryCoefficientBoundClosed_nonneg c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    (by exact_mod_cast sampleCount_lt_extrapolationRadius (show 2 ≤ t by omega))
    (sampleCount R.n t)
    (quarterRadiusSample_mem_closedBall (by
      rw [extrapolationRadius_eq_mul_sampleCount]
      exact Nat.mul_le_mul_right (sampleCount R.n t) ht))
  let N := extrapolationOrder R.n t * sampleCount R.n t
  let node : ℝ := ((sampleCount R.n t + sampleCount R.n t : ℕ) : ℝ)
  let den : ℝ := (extrapolationRadius R.n t : ℝ) - sampleCount R.n t
  let A : ℝ := ((exponentWidth R.n t ^ R.n : ℕ) : ℝ) *
    (D ^ v *
      R.auxiliaryCoefficientBoundClosed c
        (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) *
      Real.exp ((exponentWidth R.n t * R.primeLogWeight) *
        extrapolationRadius R.n t))
  let H : ℝ := (((exponentWidth R.n t ^ R.n : ℕ) : ℝ) *
    (D ^ v *
      R.auxiliaryCoefficientBoundClosed c
        (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) *
      (R.primeProduct : ℝ) ^
        (exponentWidth R.n t * sampleCount R.n t))) ^ d
  have hratio : node ^ N / den ^ N ≤ ((2 : ℝ) / 3) ^ N :=
    quarterRadiusSample_node_ratio_le_two_thirds ht (by
      rw [extrapolationRadius_eq_mul_sampleCount]
      exact Nat.mul_le_mul_right (sampleCount R.n t) ht)
  have hgrowth : 0 ≤ D ^ (v * (d + 1)) * firstStepGrowth R c t :=
    mul_nonneg (pow_nonneg hD0 _) (firstStepGrowth_nonneg R c t)
  have hfactor : D ^ (v * (d + 1)) = (D ^ v) ^ d * D ^ v := by
    rw [mul_add, mul_one, pow_add, pow_mul]
  have hid : (node ^ N * (A / den ^ N)) * H =
      (node ^ N / den ^ N) *
        (D ^ (v * (d + 1)) * firstStepGrowth R c t) := by
    simp only [firstStepGrowth]
    dsimp only [N, node, den, A, H, v, D, d]
    rw [hfactor]
    simp only [mul_pow]
    ring
  change (node ^ N * (A / den ^ N)) * H < 1
  rw [hid]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hratio hgrowth) hsmallGrowth

/-- The closed scalar growth at any natural sample in the Schwarz disc is bounded by the uniform
radius majorant. -/
theorem Relation.sampleStepGrowth_le_radiusMajorant
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (t : ℕ) (ht : 2 ≤ t) (v sample : ℕ)
    (hsample : sample ≤ extrapolationRadius R.n t) :
    let L := exponentWidth R.n t
    let S := sampleCount R.n t
    let T := derivativeCutoff R.n t
    let radius := extrapolationRadius R.n t
    let Hη := R.auxiliaryCoefficientBoundClosed c L S T
    (((L ^ R.n : ℕ) : ℝ) *
        ((2 * L * R.scaledCoefficientHouseSum c) ^ v * Hη *
          Real.exp ((L * R.primeLogWeight) * radius))) *
      ((((L ^ R.n : ℕ) : ℝ) *
        ((2 * L * R.scaledCoefficientHouseSum c) ^ v * Hη *
          (R.primeProduct : ℝ) ^ (L * sample))) ^
            (Module.finrank ℚ R.CoefficientField - 1)) ≤
      radiusStepGrowthMajorant R c t v := by
  dsimp only
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let radius := extrapolationRadius R.n t
  let d := Module.finrank ℚ R.CoefficientField - 1
  let D : ℝ := 2 * L * R.scaledCoefficientHouseSum c
  let H := R.auxiliaryCoefficientBoundClosed c L S (derivativeCutoff R.n t)
  let H' := linearCoefficientBudget R c t
  have hH : H ≤ H' := by
    exact Relation.parameterizedCoefficientBoundClosed_le_linear
      R hn c hc hint pivot t ht
  have hH0 : 0 ≤ H := by
    exact R.auxiliaryCoefficientBoundClosed_nonneg c L S (derivativeCutoff R.n t)
  have hH'0 : 0 ≤ H' := linearCoefficientBudget_nonneg R c t
  have hPone : (1 : ℝ) ≤ R.primeProduct := by exact_mod_cast R.one_le_primeProduct
  have hexp : L * sample ≤ L * radius := Nat.mul_le_mul_left L hsample
  have hPsample : (R.primeProduct : ℝ) ^ (L * sample) ≤
      (R.primeProduct : ℝ) ^ (L * radius) :=
    pow_le_pow_right₀ hPone hexp
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by
        unfold Relation.scaledCoefficientHouseSum
        exact Finset.sum_nonneg fun i hi => house_nonneg _)
  have hfactor : D ^ (v * (d + 1)) = (D ^ v) ^ d * D ^ v := by
    rw [mul_add, mul_one, pow_add, pow_mul]
  let X : ℝ := ((L ^ R.n : ℕ) : ℝ)
  let E : ℝ := Real.exp ((L * R.primeLogWeight) * radius)
  let Ps : ℝ := (R.primeProduct : ℝ) ^ (L * sample)
  let PS : ℝ := (R.primeProduct : ℝ) ^ (L * S)
  let PR : ℝ := (R.primeProduct : ℝ) ^ (L * radius)
  have hPsPR : Ps ≤ PR := hPsample
  have hPSone : 1 ≤ PS ^ d := by
    exact one_le_pow₀ (one_le_pow₀ hPone)
  have hX0 : 0 ≤ X := Nat.cast_nonneg _
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  have hPs0 : 0 ≤ Ps := pow_nonneg (Nat.cast_nonneg _) _
  have hPR0 : 0 ≤ PR := pow_nonneg (Nat.cast_nonneg _) _
  have hcore : X * (H * E) * (X * (H * Ps)) ^ d ≤
      X * (H' * E) * (X * (H' * PR)) ^ d := by
    gcongr
  have hB0 : 0 ≤ X * (H' * E) * (X * H') ^ d := by positivity
  have hcoreFactor : X * (H' * E) * (X * (H' * PR)) ^ d =
      (X * (H' * E) * (X * H') ^ d) * PR ^ d := by
    simp only [mul_pow]
    ring
  have hmajorFactor : firstStepGrowthMajorant R c t * PR ^ d =
      (X * (H' * E) * (X * H') ^ d * PS ^ d) * PR ^ d := by
    unfold firstStepGrowthMajorant
    dsimp only
    change (X * (H' * E) * (X * (H' * PS)) ^ d) * PR ^ d = _
    simp only [mul_pow]
    ring
  have hcoreMajor : X * (H' * E) * (X * (H' * PR)) ^ d ≤
      firstStepGrowthMajorant R c t * PR ^ d := by
    rw [hcoreFactor, hmajorFactor]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hPR0 _)
    simpa using mul_le_mul_of_nonneg_left hPSone hB0
  have hactual :
      (X * (D ^ v * H * E)) * (X * (D ^ v * H * Ps)) ^ d =
        D ^ (v * (d + 1)) * (X * (H * E) * (X * (H * Ps)) ^ d) := by
    rw [hfactor]
    simp only [mul_pow]
    ring
  change (X * (D ^ v * H * E)) * (X * (D ^ v * H * Ps)) ^ d ≤ _
  rw [hactual]
  unfold radiusStepGrowthMajorant shiftedFirstStepGrowthMajorant
  dsimp only
  simpa [D, d, PR, L, radius, mul_assoc] using
    (mul_le_mul_of_nonneg_left (hcore.trans hcoreMajor)
      (pow_nonneg hD0 (v * (d + 1))))

/-- Every shifted component in the lower multiindex box vanishes at every natural sample in the
first quarter of the Schwarz disc once the uniform scalar budget is below one. -/
theorem Relation.quarterRadiusSample_shifted_eq_zero_of_decay_growth_lt_one
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (t : ℕ) (ht : 4 ≤ t)
    (η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
      R.auxiliaryCoefficientBoundClosed c
        (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    (ν : R.NonPivot pivot → ℕ)
    (hνq : ∀ i, ν i + extrapolationOrder R.n t < derivativeCutoff R.n t)
    (sample : ℕ) (hquarter : 4 * sample ≤ extrapolationRadius R.n t)
    (hsmall : ((2 : ℝ) / 3) ^
        (extrapolationOrder R.n t * sampleCount R.n t) *
          radiusStepGrowthMajorant R c t (∑ i, ν i) < 1) :
    R.auxiliaryComponent c pivot ν η sample = 0 := by
  apply R.auxiliaryComponent_eq_zero_one_step_scalar
    c hc hint pivot η hker ν (extrapolationOrder R.n t) hνq
    (R.auxiliaryCoefficientBoundClosed c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    hη
    (R.auxiliaryCoefficientBoundClosed_nonneg c
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t))
    (by exact_mod_cast sampleCount_lt_extrapolationRadius (show 2 ≤ t by omega))
    sample (quarterRadiusSample_mem_closedBall hquarter)
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let radius := extrapolationRadius R.n t
  let v := ∑ i, ν i
  let d := Module.finrank ℚ R.CoefficientField - 1
  let D : ℝ := 2 * L * R.scaledCoefficientHouseSum c
  let Hη := R.auxiliaryCoefficientBoundClosed c L S (derivativeCutoff R.n t)
  let N := extrapolationOrder R.n t * S
  let node : ℝ := ((sample + S : ℕ) : ℝ)
  let den : ℝ := (radius : ℝ) - S
  let A : ℝ := ((L ^ R.n : ℕ) : ℝ) *
    (D ^ v * Hη * Real.exp ((L * R.primeLogWeight) * radius))
  let H : ℝ := (((L ^ R.n : ℕ) : ℝ) *
    (D ^ v * Hη * (R.primeProduct : ℝ) ^ (L * sample))) ^ d
  let G : ℝ := A * H
  have hratio : node ^ N / den ^ N ≤ ((2 : ℝ) / 3) ^ N :=
    quarterRadiusSample_node_ratio_le_two_thirds ht hquarter
  have hGle : G ≤ radiusStepGrowthMajorant R c t v := by
    exact Relation.sampleStepGrowth_le_radiusMajorant
      R hn c hc hint pivot t (by omega) v sample
        (le_trans (Nat.le_mul_of_pos_left sample (by norm_num)) hquarter)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by
        unfold Relation.scaledCoefficientHouseSum
        exact Finset.sum_nonneg fun i hi => house_nonneg _)
  have hHη0 : 0 ≤ Hη := by
    exact R.auxiliaryCoefficientBoundClosed_nonneg c L S (derivativeCutoff R.n t)
  have hG0 : 0 ≤ G := by
    dsimp only [G, A, H]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (mul_nonneg (pow_nonneg hD0 _) hHη0) (Real.exp_nonneg _)))
      (pow_nonneg
        (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (mul_nonneg (pow_nonneg hD0 _) hHη0)
            (pow_nonneg (Nat.cast_nonneg _) _))) _)
  have hid : (node ^ N * (A / den ^ N)) * H =
      (node ^ N / den ^ N) * G := by
    dsimp only [G]
    ring
  change (node ^ N * (A / den ^ N)) * H < 1
  rw [hid]
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_right hratio hG0).trans
      (mul_le_mul_of_nonneg_left hGle (pow_nonneg (by norm_num) _)))
    hsmall

/-- With a common integral coefficient scale fixed once and for all, every parameter base produces
a nonzero bounded auxiliary kernel vector. -/
theorem Relation.exists_parameterized_auxiliary_coefficients_of_scale
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
    (pivot : Fin R.n) (t : ℕ) (ht : 2 ≤ t) :
    ∃ η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField,
      η ≠ 0 ∧
        Matrix.mulVec (R.auxiliaryMatrix c hint pivot
          (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0 ∧
        ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
          R.auxiliaryCoefficientBoundClosed c
            (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) := by
  have hL : 0 < exponentWidth R.n t := by
    unfold exponentWidth
    exact mul_pos (by norm_num) (pow_pos (lt_of_lt_of_le (by norm_num) ht) _)
  have hS : 0 < sampleCount R.n t := by
    unfold sampleCount
    exact pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hT : 0 < derivativeCutoff R.n t := by
    unfold derivativeCutoff extrapolationOrder
    positivity
  have hcard := dimension_inequality hn ht
  have hcard' : Fintype.card
      (R.Row pivot (sampleCount R.n t) (derivativeCutoff R.n t)) <
      Fintype.card (R.Column (exponentWidth R.n t)) := by
    simpa using hcard
  obtain ⟨η, hη, hker, hbound⟩ :=
    R.exists_auxiliary_coefficients c hint pivot
      (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)
      hL hS hT hcard'
  refine ⟨η, hη, hker, fun m => (hbound m).trans ?_⟩
  exact R.auxiliaryCoefficientBound_le_closed c hc hint pivot
    (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) hL hcard

/-- For a fixed integral coefficient scale, the whole analytic extrapolation closes into a nonzero
kernel vector for an enlarged auxiliary matrix whose row count is strictly larger than its column
count.  The only remaining input is the terminal Baker zero lemma asserting injectivity of this
specific enlarged matrix. -/
theorem Relation.exists_parameterized_extended_auxiliary_kernel_of_scale
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n) :
    ∃ t : ℕ, 4 ≤ t ∧ 2 ^ (R.n + 2) < t ∧
      ∃ η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField,
        η ≠ 0 ∧
          Matrix.mulVec (R.auxiliaryMatrix c hint pivot
            (exponentWidth R.n t) (quarterSampleCount R.n t)
              (extrapolationOrder R.n t)) η = 0 := by
  obtain ⟨t, ⟨hsmall, ht⟩, htlarge⟩ :=
    (((eventually_radiusStepSmallness R hn c).and
      (eventually_ge_atTop 4)).and
        (eventually_ge_atTop (2 ^ (R.n + 2) + 1))).exists
  have htstrict : 2 ^ (R.n + 2) < t := by omega
  obtain ⟨η, hη, hker, hbound⟩ :=
    Relation.exists_parameterized_auxiliary_coefficients_of_scale
      R hn c hc hint pivot t (by omega)
  refine ⟨t, ht, htstrict, η, hη, ?_⟩
  apply R.auxiliaryMatrix_mulVec_eq_zero_of_component_box_zero
  intro sample ν
  let νNat : R.NonPivot pivot → ℕ := fun i => (ν i : ℕ)
  have hv : (∑ i, νNat i) ≤
      (R.n - 1) * extrapolationOrder R.n t := by
    simpa [νNat] using R.sum_rowMultiIndex_le pivot ν
  apply Relation.quarterRadiusSample_shifted_eq_zero_of_decay_growth_lt_one
    R hn c hc hint pivot t ht η hker hbound νNat
  · intro i
    calc
      νNat i + extrapolationOrder R.n t <
          extrapolationOrder R.n t + extrapolationOrder R.n t :=
        Nat.add_lt_add_right (ν i).isLt _
      _ = derivativeCutoff R.n t := by
        simp [derivativeCutoff, two_mul]
  · exact quarterSample_mem sample
  · exact hsmall (∑ i, νNat i) hv

/-- The parameter family discharges every dimension and positivity premise of the Siegel-kernel
construction, including its explicit coefficient-house estimate. -/
theorem Relation.exists_parameterized_auxiliary_coefficients
    (R : Relation) (hn : 3 ≤ R.n) (pivot : Fin R.n) (t : ℕ) (ht : 2 ≤ t) :
    ∃ c : ℤ, c ≠ 0 ∧
      ∃ (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i))
        (η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField),
        η ≠ 0 ∧
          Matrix.mulVec (R.auxiliaryMatrix c hint pivot
            (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0 ∧
          ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
            R.auxiliaryCoefficientBoundClosed c
              (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t) := by
  obtain ⟨c, hc, hint⟩ := R.exists_common_integer_scale
  have hint' : ∀ i, IsIntegral ℤ (R.scaledCoeff c i) := by
    simpa [Relation.scaledCoeff] using hint
  obtain ⟨η, hη, hker, hbound⟩ :=
    Relation.exists_parameterized_auxiliary_coefficients_of_scale
      R hn c hc hint' pivot t ht
  exact ⟨c, hc, hint', η, hη, hker, hbound⟩

end GaloisForLFunctions.RHTower.BakerProof.BakerParameters
