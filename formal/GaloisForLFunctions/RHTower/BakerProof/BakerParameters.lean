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
def exponentWidth (n t : ℕ) : ℕ := t ^ (8 * n - 2)

/-- Number of initial integer samples. -/
def sampleCount (n t : ℕ) : ℕ := t ^ (4 * n)

/-- Multiplicity used in one extrapolation step. -/
def extrapolationOrder (n t : ℕ) : ℕ := t ^ (8 * n)

/-- Multiindex cutoff, leaving half the box available for shifts. -/
def derivativeCutoff (n t : ℕ) : ℕ := 2 * extrapolationOrder n t

/-- Schwarz-disc radius. -/
def extrapolationRadius (n t : ℕ) : ℕ := t ^ (4 * n + 1)

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
  GelfondSchneiderSiegel.c₁ R.CoefficientField ^ 2 *
    (((L ^ R.n : ℕ) : ℝ) ^ 2) *
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
      (2 ^ (n - 1) : ℝ) *
        (t : ℝ) ^ (4 * n + (8 * n) * (n - 1) + (8 * n - 2) * n) := by
  simp only [sampleCount, derivativeCutoff, extrapolationOrder, exponentWidth,
    Nat.cast_mul, Nat.cast_pow, mul_pow, ← pow_mul]
  rw [pow_add, pow_add]
  ring

theorem columnCountSq_cast_eq (n t : ℕ) :
    ((((exponentWidth n t ^ n : ℕ) : ℝ)) ^ 2) =
      (t : ℝ) ^ ((8 * n - 2) * n * 2) := by
  simp only [exponentWidth, Nat.cast_pow, ← pow_mul]

theorem directionBase_eq_const_mul_pow (R : Relation) (c : ℤ) (t : ℕ) :
    (2 : ℝ) * exponentWidth R.n t * R.scaledCoefficientHouseSum c =
      (2 * R.scaledCoefficientHouseSum c) *
        (t : ℝ) ^ (8 * R.n - 2) := by
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
    (GelfondSchneiderSiegel.c₁ R.CoefficientField ^ 2) 0
  have hL := eventually_const_mul_natCast_pow_le_exp
    1 ((8 * R.n - 2) * R.n * 2)
  have hRC := eventually_const_mul_natCast_pow_le_exp
    (2 ^ (R.n - 1) : ℝ)
    (4 * R.n + (8 * R.n) * (R.n - 1) + (8 * R.n - 2) * R.n)
  have hD := eventually_const_mul_natCast_pow_le_exp
    (2 * R.scaledCoefficientHouseSum c) (8 * R.n - 2)
  have hP := eventually_const_mul_natCast_pow_le_exp (R.primeProduct : ℝ) 0
  filter_upwards [hc1, hL, hRC, hD, hP] with t hc1t hLt hRCt hDt hPt
  have hL' : ((((exponentWidth R.n t ^ R.n : ℕ) : ℝ)) ^ 2) ≤ Real.exp t := by
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
  have hc1' : GelfondSchneiderSiegel.c₁ R.CoefficientField ^ 2 ≤ Real.exp t := by
    simpa using hc1t
  have hC : 0 ≤ R.scaledCoefficientHouseSum c := by
    unfold Relation.scaledCoefficientHouseSum
    exact Finset.sum_nonneg fun i hi => house_nonneg _
  have hD0 : 0 ≤ (2 : ℝ) * exponentWidth R.n t * R.scaledCoefficientHouseSum c :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hC
  unfold firstStepNormalBase
  dsimp only
  calc
    GelfondSchneiderSiegel.c₁ R.CoefficientField ^ 2 *
        (((exponentWidth R.n t ^ R.n : ℕ) : ℝ) ^ 2) *
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

theorem rawExponent_le_dominant {n t : ℕ} (hn : 3 ≤ n) (ht : 1 ≤ t) :
    3 * t + t * ((n - 1) * derivativeCutoff n t) +
        t * (exponentWidth n t * sampleCount n t) ≤
      (2 * n + 2) * t ^ (12 * n - 1) := by
  let N := t ^ (12 * n - 1)
  have hNexp : 1 ≤ 12 * n - 1 := by omega
  have htN : t ≤ N := by
    simpa [N] using pow_le_pow_right₀ ht hNexp
  have hderivEq : t * ((n - 1) * derivativeCutoff n t) =
      (2 * (n - 1)) * t ^ (8 * n + 1) := by
    unfold derivativeCutoff extrapolationOrder
    rw [pow_succ']
    ring
  have hderivPow : t ^ (8 * n + 1) ≤ N := by
    exact pow_le_pow_right₀ ht (by omega)
  have hderiv : t * ((n - 1) * derivativeCutoff n t) ≤
      (2 * (n - 1)) * N := by
    rw [hderivEq]
    exact Nat.mul_le_mul_left _ hderivPow
  have hsampleEq : t * (exponentWidth n t * sampleCount n t) = N := by
    unfold exponentWidth sampleCount
    rw [← pow_add]
    calc
      t * t ^ ((8 * n - 2) + 4 * n) =
          t ^ (((8 * n - 2) + 4 * n) + 1) := by rw [pow_succ']
      _ = N := by simp only [N]; congr 1; omega
  have hcoef : 3 + 2 * (n - 1) + 1 = 2 * n + 2 := by omega
  calc
    3 * t + t * ((n - 1) * derivativeCutoff n t) +
        t * (exponentWidth n t * sampleCount n t) ≤
      3 * N + (2 * (n - 1)) * N + N := by
        exact add_le_add (add_le_add (Nat.mul_le_mul_left 3 htN) hderiv) hsampleEq.le
    _ = (3 + 2 * (n - 1) + 1) * N := by ring
    _ = (2 * n + 2) * N := by rw [hcoef]

theorem eventually_firstStepNormalBase_le_exp_dominant
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop,
      firstStepNormalBase R c t ≤
        Real.exp ((2 * R.n + 2) * (t ^ (12 * R.n - 1) : ℕ)) := by
  filter_upwards [eventually_firstStepNormalBase_le_exp_raw R hn c,
    eventually_ge_atTop 1] with t hraw ht
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  have hnat := rawExponent_le_dominant hn ht
  have hnsub : (R.n : ℝ) - 1 = ((R.n - 1 : ℕ) : ℝ) := by
    simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ R.n)).symm
  rw [hnsub]
  exact_mod_cast hnat

/-- The polynomial parameter family always gives fewer matrix rows than columns once the reduced
relation has arity at least three. -/
theorem dimension_inequality {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ≤ t) :
    sampleCount n t * derivativeCutoff n t ^ (n - 1) <
      exponentWidth n t ^ n := by
  unfold sampleCount derivativeCutoff extrapolationOrder exponentWidth
  rw [mul_pow, ← pow_mul, ← pow_mul]
  have hexp : (8 * n - 2) * n =
      (4 * n + (8 * n) * (n - 1)) + 2 * n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h₁ : 8 * (3 + k) - 2 = 22 + 8 * k := by omega
    have h₂ : 3 + k - 1 = 2 + k := by omega
    rw [h₁, h₂]
    ring
  rw [hexp, pow_add, pow_add]
  have hsmall : 2 ^ (n - 1) < t ^ (2 * n) := by
    apply lt_of_le_of_lt (Nat.pow_le_pow_left ht (n - 1))
    exact Nat.pow_lt_pow_right (lt_of_lt_of_le (by norm_num) ht) (by omega)
  have hpos : 0 < t ^ (4 * n + (8 * n) * (n - 1)) :=
    pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hmul := (Nat.mul_lt_mul_left hpos).2 hsmall
  simpa [pow_add, mul_assoc, mul_comm, mul_left_comm] using hmul

/-- The column count is at least twice the row count; hence the Siegel exponent `rows/(cols-rows)`
is at most one. -/
theorem double_rowCount_le_columnCount {n t : ℕ} (hn : 3 ≤ n) (ht : 2 ≤ t) :
    2 * (sampleCount n t * derivativeCutoff n t ^ (n - 1)) ≤
      exponentWidth n t ^ n := by
  unfold sampleCount derivativeCutoff extrapolationOrder exponentWidth
  rw [mul_pow, ← pow_mul, ← pow_mul]
  have hexp : (8 * n - 2) * n =
      (4 * n + (8 * n) * (n - 1)) + 2 * n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have h₁ : 8 * (3 + k) - 2 = 22 + 8 * k := by omega
    have h₂ : 3 + k - 1 = 2 + k := by omega
    rw [h₁, h₂]
    ring
  rw [hexp, pow_add, pow_add]
  have hsmall : 2 ^ n ≤ t ^ (2 * n) := by
    apply le_trans (Nat.pow_le_pow_left ht n)
    exact pow_le_pow_right₀ (by omega : 1 ≤ t) (by omega : n ≤ 2 * n)
  have h2pow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    calc
      2 * 2 ^ (n - 1) = 2 ^ ((n - 1) + 1) := by rw [pow_succ']
      _ = 2 ^ n := by congr 1; omega
  have hmul := Nat.mul_le_mul_left
    (t ^ (4 * n + (8 * n) * (n - 1))) hsmall
  calc
    2 * (t ^ (4 * n) * (2 ^ (n - 1) * t ^ ((8 * n) * (n - 1)))) =
        t ^ (4 * n + (8 * n) * (n - 1)) * 2 ^ n := by
      rw [pow_add, ← h2pow]
      ring
    _ ≤ t ^ (4 * n + (8 * n) * (n - 1)) * t ^ (2 * n) := hmul
    _ = t ^ (4 * n) * t ^ ((8 * n) * (n - 1)) * t ^ (2 * n) := by
      rw [pow_add]

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
    exact pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hS : 0 < sampleCount R.n t := by
    unfold sampleCount
    exact pow_pos (lt_of_lt_of_le (by norm_num) ht) _
  have hT : 0 < derivativeCutoff R.n t := by
    unfold derivativeCutoff extrapolationOrder
    positivity
  apply R.auxiliaryCoefficientBoundClosed_le_linear
  · exact mul_pos hS (pow_pos hT _)
  · exact double_rowCount_le_columnCount hn ht
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
    exponentWidth n t * extrapolationRadius n t = t ^ (12 * n - 1) := by
  unfold exponentWidth extrapolationRadius
  rw [← pow_add]
  congr 1
  omega

theorem extrapolationOrder_mul_sampleCount {n t : ℕ} :
    extrapolationOrder n t * sampleCount n t = t ^ (12 * n) := by
  unfold extrapolationOrder sampleCount
  rw [← pow_add]
  congr 1
  omega

theorem exponentWidth_mul_sampleCount {n t : ℕ} (hn : 3 ≤ n) :
    exponentWidth n t * sampleCount n t = t ^ (12 * n - 2) := by
  unfold exponentWidth sampleCount
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
    hPev, eventually_ge_atTop 1] with t hX hPt ht
  let L := exponentWidth R.n t
  let S := sampleCount R.n t
  let radius := extrapolationRadius R.n t
  let d := Module.finrank ℚ R.CoefficientField - 1
  let N := t ^ (12 * R.n - 1)
  have hP : (R.primeProduct : ℝ) ≤ Real.exp t := by simpa using hPt
  have hLR : L * radius = N := by
    exact exponentWidth_mul_extrapolationRadius hn
  have hLS : t * (L * S) = N := by
    dsimp only [L, S, N]
    rw [exponentWidth_mul_sampleCount hn]
    calc
      t * t ^ (12 * R.n - 2) = t ^ ((12 * R.n - 2) + 1) := by rw [pow_succ']
      _ = t ^ (12 * R.n - 1) := by congr 1; omega
  have hanalytic : Real.exp ((L * R.primeLogWeight) * radius) =
      Real.exp (R.primeLogWeight * N) := by
    congr 1
    have hLRR : (L : ℝ) * (radius : ℝ) = (N : ℝ) := by exact_mod_cast hLR
    calc
      (L : ℝ) * R.primeLogWeight * (radius : ℝ) =
          R.primeLogWeight * ((L : ℝ) * radius) := by ring
      _ = R.primeLogWeight * N := by rw [hLRR]
  have hPM : (R.primeProduct : ℝ) ^ (L * S) ≤
      (Real.exp t) ^ (L * S) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hP _
  have hX0 := firstStepNormalBase_nonneg R c t
  rw [firstStepGrowthMajorant_eq_normalForm]
  rw [hanalytic]
  calc
    Real.exp (R.primeLogWeight * N) * firstStepNormalBase R c t ^ (d + 1) *
        ((R.primeProduct : ℝ) ^ (L * S)) ^ d ≤
      Real.exp (R.primeLogWeight * N) *
        (Real.exp ((2 * R.n + 2) * N)) ^ (d + 1) *
        (((Real.exp t) ^ (L * S)) ^ d) := by
      gcongr
    _ = Real.exp (growthExponentConstant R * N) := by
      rw [← Real.exp_nat_mul, ← pow_mul, ← Real.exp_nat_mul]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      have hLSR : (t : ℝ) * (L * S : ℕ) = (N : ℝ) := by exact_mod_cast hLS
      have hterm : (L : ℝ) * (S : ℝ) * (d : ℝ) * (t : ℝ) = (d : ℝ) * N := by
        calc
          (L : ℝ) * S * d * t = d * (t * (L * S : ℕ)) := by
            push_cast
            ring
          _ = d * N := by rw [hLSR]
      unfold growthExponentConstant
      dsimp only [d]
      push_cast
      rw [hterm]
      ring

/-- Geometric Schwarz decay at scale `t^(12n)` dominates every fixed exponential at the strictly
smaller scale `t^(12n-1)`. -/
theorem eventually_decay_mul_exp_dominant_lt_one (R : Relation) (hn : 3 ≤ R.n) :
    ∀ᶠ t : ℕ in atTop,
      ((2 : ℝ) / 3) ^ (t ^ (12 * R.n)) *
        Real.exp (growthExponentConstant R * (t ^ (12 * R.n - 1) : ℕ)) < 1 := by
  have hdecayT : Tendsto
      (fun t : ℕ => ((2 : ℝ) / 3) ^ t * Real.exp (growthExponentConstant R))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 3)
      (by norm_num : (2 : ℝ) / 3 < 1)).mul_const
        (Real.exp (growthExponentConstant R))
  have hbase : ∀ᶠ t : ℕ in atTop,
      ((2 : ℝ) / 3) ^ t * Real.exp (growthExponentConstant R) < 1 :=
    (tendsto_order.1 hdecayT).2 1 (by norm_num)
  filter_upwards [hbase, eventually_ge_atTop 1] with t ht ht1
  let N := t ^ (12 * R.n - 1)
  have hNpos : 0 < N := pow_pos (by omega) _
  have hpow : (((2 : ℝ) / 3) ^ t * Real.exp (growthExponentConstant R)) ^ N < 1 :=
    pow_lt_one₀ (mul_nonneg (pow_nonneg (by norm_num) _)
      (Real.exp_nonneg _)) ht hNpos.ne'
  have hscale : t ^ (12 * R.n) = t * N := by
    dsimp only [N]
    calc
      t ^ (12 * R.n) = t ^ ((12 * R.n - 1) + 1) := by congr 1; omega
      _ = t * t ^ (12 * R.n - 1) := by rw [pow_succ']
  have hexp : Real.exp (growthExponentConstant R * (N : ℕ)) =
      (Real.exp (growthExponentConstant R)) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hscale, pow_mul, hexp, ← mul_pow]
  exact hpow

/-- The scalar smallness premise required for the first extrapolation step holds for all sufficiently
large parameter bases. -/
theorem eventually_firstStepSmallness (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ t : ℕ in atTop,
      ((2 : ℝ) / 3) ^
          (extrapolationOrder R.n t * sampleCount R.n t) *
        firstStepGrowthMajorant R c t < 1 := by
  filter_upwards [eventually_firstStepGrowthMajorant_le_exp_dominant R hn c,
    eventually_decay_mul_exp_dominant_lt_one R hn] with t hgrowth hdecay
  rw [extrapolationOrder_mul_sampleCount]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hgrowth (pow_nonneg (by norm_num) _)) hdecay

/-- The first sample beyond the interpolation set lies in the Schwarz disc. -/
theorem firstNewSample_mem_closedBall {n t : ℕ} (ht : 2 ≤ t) :
    ((sampleCount n t : ℕ) : ℂ) ∈
      Metric.closedBall 0 (extrapolationRadius n t : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [sub_zero, Complex.norm_natCast]
  exact_mod_cast (sampleCount_lt_extrapolationRadius ht).le

/-- At the first new sample, the complete Schwarz node ratio is bounded by `(2/3)^(qS)` once
`t ≥ 4`.  Its exponent is exactly the dominant scale `t^(12n)`. -/
theorem firstNewSample_node_ratio_le_two_thirds {n t : ℕ} (ht : 4 ≤ t) :
    let N := extrapolationOrder n t * sampleCount n t
    (((sampleCount n t + sampleCount n t : ℕ) : ℝ) ^ N /
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
    (firstNewSample_mem_closedBall (show 2 ≤ t by omega))
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
    firstNewSample_node_ratio_le_two_thirds ht
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
    exact pow_pos (lt_of_lt_of_le (by norm_num) ht) _
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

/-- For a fixed integral coefficient scale, some parameter base produces a nonzero auxiliary kernel
whose main component vanishes at the first sample beyond the interpolation set. -/
theorem Relation.exists_parameterized_firstNewSample_zero_of_scale
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n) :
    ∃ t : ℕ, 4 ≤ t ∧
      ∃ η : R.Column (exponentWidth R.n t) → 𝓞 R.CoefficientField,
        η ≠ 0 ∧
          Matrix.mulVec (R.auxiliaryMatrix c hint pivot
            (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) η = 0 ∧
          (∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤
            R.auxiliaryCoefficientBoundClosed c
              (exponentWidth R.n t) (sampleCount R.n t) (derivativeCutoff R.n t)) ∧
          R.auxiliaryComponent c pivot (fun _ => 0) η (sampleCount R.n t) = 0 := by
  obtain ⟨t, hsmall, ht⟩ :=
    ((eventually_firstStepSmallness R hn c).and (eventually_ge_atTop 4)).exists
  obtain ⟨η, hη, hker, hbound⟩ :=
    Relation.exists_parameterized_auxiliary_coefficients_of_scale
      R hn c hc hint pivot t (by omega)
  refine ⟨t, ht, η, hη, hker, hbound, ?_⟩
  exact Relation.firstNewSample_eq_zero_of_decay_growth_lt_one
    R hn c hc hint pivot t ht η hker hbound hsmall

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
