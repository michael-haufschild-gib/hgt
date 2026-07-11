import GaloisForLFunctions.RHTower.BakerProof.BakerParameters

/-!
# Long extrapolation for the Baker auxiliary matrix

This module turns one exact component extrapolation into an iteration on auxiliary-matrix kernels.
The same nonzero Siegel vector is retained while the consecutive sample range grows and the
multiindex cutoff decreases.
-/

open scoped Classical
open BigOperators NumberField
open Filter Topology

namespace GaloisForLFunctions.RHTower.BakerProof

namespace BakerIteration

/-- Consecutive sample count after `k` long-extrapolation enlargements. -/
def stageSampleCount (n t k : ℕ) : ℕ :=
  BakerParameters.sampleCount n t * (t / 4) ^ k

/-- Component cutoff after `k` halvings. -/
def stageOrder (n t k : ℕ) : ℕ :=
  BakerParameters.extrapolationOrder n t / 2 ^ k

/-- A fixed number of enlargements sufficient to gain one full power of the parameter base beyond
the auxiliary-column count. -/
def iterationLength (n : ℕ) : ℕ := 8 * n * (n - 1)

/-- A power-of-two multiplier chosen once so every halving through the terminal stage is exact. -/
def structuredMultiplier (n : ℕ) : ℕ := 2 ^ (iterationLength n + 1)

/-- Cofinal parameter subfamily used for the long iteration. -/
def structuredBase (n u : ℕ) : ℕ := 4 * (structuredMultiplier n * u)

/-- Closed positive growth budget at one long-extrapolation stage.  The coefficient height is kept
at the original linear Siegel bound; only the analytic radius and terminal sample factor grow. -/
noncomputable def stageGrowthMajorant
    (R : Relation) (c : ℤ) (t k v : ℕ) : ℝ :=
  let L := BakerParameters.exponentWidth R.n t
  let S := stageSampleCount R.n t (k + 1)
  let S' := stageSampleCount R.n t (k + 2)
  let radius : ℝ := t * S
  let Hη := BakerParameters.linearCoefficientBudget R c t
  let d := Module.finrank ℚ R.CoefficientField - 1
  ((L ^ R.n : ℕ) : ℝ) *
      ((2 * L * R.scaledCoefficientHouseSum c) ^ v * Hη *
        Real.exp ((L * R.primeLogWeight) * radius)) *
    ((((L ^ R.n : ℕ) : ℝ) *
      ((2 * L * R.scaledCoefficientHouseSum c) ^ v * Hη *
        (R.primeProduct : ℝ) ^ (L * S'))) ^ d)

noncomputable def stageGrowthExponentConstant (R : Relation) : ℝ :=
  let d := Module.finrank ℚ R.CoefficientField - 1
  BakerParameters.shiftedGrowthExponentConstant R +
    2 * R.primeLogWeight + 2 * d * Real.log R.primeProduct

@[simp] theorem stageSampleCount_zero (n t : ℕ) :
    stageSampleCount n t 0 = BakerParameters.sampleCount n t := by
  simp [stageSampleCount]

theorem stageSampleCount_succ (n t k : ℕ) :
    stageSampleCount n t (k + 1) = stageSampleCount n t k * (t / 4) := by
  simp [stageSampleCount, pow_succ, mul_assoc]

theorem stageSampleCount_pos {n t k : ℕ} (ht : 4 ≤ t) :
    0 < stageSampleCount n t k := by
  unfold stageSampleCount BakerParameters.sampleCount
  exact mul_pos (pow_pos (by omega) _) (pow_pos (Nat.div_pos ht (by norm_num)) _)

theorem structuredMultiplier_pos (n : ℕ) : 0 < structuredMultiplier n := by
  unfold structuredMultiplier
  positivity

theorem structuredBase_div_four (n u : ℕ) :
    structuredBase n u / 4 = structuredMultiplier n * u := by
  unfold structuredBase
  exact Nat.mul_div_cancel_left _ (by norm_num)

theorem pow_le_stageOrder_structured
    {n u k : ℕ} (hn : 3 ≤ n) (hk : k ≤ iterationLength n) :
    u ^ (8 * n) ≤ stageOrder n (structuredBase n u) (k + 1) := by
  let B := structuredMultiplier n
  let C := 4 * B
  have hBpos : 0 < B := structuredMultiplier_pos n
  have hCpos : 0 < C := mul_pos (by norm_num) hBpos
  have hdenC : 2 ^ (k + 1) ≤ C := by
    dsimp only [C, B]
    unfold structuredMultiplier
    have hp : 2 ^ (k + 1) ≤ 2 ^ (iterationLength n + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hp.trans (Nat.le_mul_of_pos_left _ (by norm_num))
  have hCpow : C ≤ C ^ (8 * n) := Nat.le_pow (by omega)
  unfold stageOrder BakerParameters.extrapolationOrder
  apply (Nat.le_div_iff_mul_le (pow_pos (by norm_num) _)).mpr
  rw [show structuredBase n u = C * u by
    simp [structuredBase, C, B, mul_assoc], mul_pow]
  calc
    u ^ (8 * n) * 2 ^ (k + 1) ≤ u ^ (8 * n) * C :=
      Nat.mul_le_mul_left _ hdenC
    _ ≤ u ^ (8 * n) * C ^ (8 * n) := Nat.mul_le_mul_left _ hCpow
    _ = C ^ (8 * n) * u ^ (8 * n) := by ring

theorem pow_le_stageSampleCount_structured
    {n u k : ℕ} :
    u ^ (4 * n + k) ≤ stageSampleCount n (structuredBase n u) k := by
  let B := structuredMultiplier n
  let C := 4 * B
  have hBpos : 0 < B := structuredMultiplier_pos n
  have huB : u ≤ B * u := Nat.le_mul_of_pos_left u hBpos
  have huC : u ≤ C * u := by
    exact huB.trans (Nat.mul_le_mul_right u (Nat.le_mul_of_pos_left B (by norm_num)))
  unfold stageSampleCount BakerParameters.sampleCount
  rw [structuredBase_div_four]
  rw [pow_add]
  exact Nat.mul_le_mul
    (Nat.pow_le_pow_left (by simpa [structuredBase, C, B, mul_assoc] using huC) (4 * n))
    (Nat.pow_le_pow_left huB k)

theorem decayExponent_le_stage
    {n u k : ℕ} (hn : 3 ≤ n) (hk : k ≤ iterationLength n) :
    u ^ (12 * n + k + 1) ≤
      stageOrder n (structuredBase n u) (k + 1) *
        stageSampleCount n (structuredBase n u) (k + 1) := by
  calc
    u ^ (12 * n + k + 1) = u ^ (8 * n) * u ^ (4 * n + (k + 1)) := by
      rw [← pow_add]
      congr 1
      omega
    _ ≤ stageOrder n (structuredBase n u) (k + 1) *
        stageSampleCount n (structuredBase n u) (k + 1) :=
      Nat.mul_le_mul (pow_le_stageOrder_structured hn hk)
        pow_le_stageSampleCount_structured

theorem exponent_balance {n : ℕ} (hn : 3 ≤ n) :
    4 * n + (iterationLength n + 1) = (8 * n - 4) * n + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [iterationLength]
  have h₁ : 8 * (3 + k) - 4 = 20 + 8 * k := by omega
  have h₂ : 3 + k - 1 = 2 + k := by omega
  rw [h₁, h₂]
  ring

theorem stageSampleCount_four_mul (n u k : ℕ) :
    stageSampleCount n (4 * u) k = 4 ^ (4 * n) * u ^ (4 * n + k) := by
  unfold stageSampleCount BakerParameters.sampleCount
  rw [Nat.mul_div_cancel_left u (by norm_num : 0 < 4)]
  simp only [mul_pow]
  ring

theorem stageSampleCount_le_pow (n t k : ℕ) :
    stageSampleCount n t k ≤ t ^ (4 * n + k) := by
  unfold stageSampleCount BakerParameters.sampleCount
  rw [pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.div_le_self t 4) k)

theorem exponentWidth_mul_stageRadius_le
    {n t k : ℕ} (hn : 3 ≤ n) :
    BakerParameters.exponentWidth n t *
        (t * stageSampleCount n t (k + 1)) ≤
      2 * t ^ (12 * n + k - 2) := by
  calc
    BakerParameters.exponentWidth n t * (t * stageSampleCount n t (k + 1)) ≤
        BakerParameters.exponentWidth n t * (t * t ^ (4 * n + (k + 1))) := by
      gcongr
      exact stageSampleCount_le_pow n t (k + 1)
    _ = 2 * t ^ (12 * n + k - 2) := by
      unfold BakerParameters.exponentWidth
      rw [show 4 * n + (k + 1) = 4 * n + k + 1 by omega]
      rw [show (2 * t ^ (8 * n - 4)) * (t * t ^ (4 * n + k + 1)) =
          2 * (t ^ (8 * n - 4) * t ^ (4 * n + k + 2)) by
        rw [pow_succ']
        ring]
      rw [← pow_add]
      congr 2
      omega

theorem exponentWidth_mul_nextStageSample_le
    {n t k : ℕ} (hn : 3 ≤ n) :
    BakerParameters.exponentWidth n t * stageSampleCount n t (k + 2) ≤
      2 * t ^ (12 * n + k - 2) := by
  calc
    BakerParameters.exponentWidth n t * stageSampleCount n t (k + 2) ≤
        BakerParameters.exponentWidth n t * t ^ (4 * n + (k + 2)) := by
      gcongr
      exact stageSampleCount_le_pow n t (k + 2)
    _ = 2 * t ^ (12 * n + k - 2) := by
      unfold BakerParameters.exponentWidth
      rw [show 4 * n + (k + 2) = 4 * n + k + 2 by omega]
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

theorem exponentWidth_four_mul_pow {n u : ℕ} :
    BakerParameters.exponentWidth n (4 * u) ^ n =
      2 ^ n * 4 ^ ((8 * n - 4) * n) * u ^ ((8 * n - 4) * n) := by
  unfold BakerParameters.exponentWidth
  simp only [mul_pow, ← pow_mul]
  ring

/-- At the terminal stage the consecutive sample range contains at least one row for every
auxiliary coefficient, once the freely chosen parameter multiple is above an explicit threshold. -/
theorem final_columnCount_le_stageSampleCount
    {n u : ℕ} (hn : 3 ≤ n)
    (hu : 2 ^ n * 4 ^ ((8 * n - 4) * n - 4 * n) ≤ u) :
    BakerParameters.exponentWidth n (4 * u) ^ n ≤
      stageSampleCount n (4 * u) (iterationLength n + 1) := by
  rw [exponentWidth_four_mul_pow,
    stageSampleCount_four_mul, exponent_balance hn]
  let E := (8 * n - 4) * n
  have h4 : 4 * n ≤ E := by
    dsimp only [E]
    apply Nat.mul_le_mul_right n
    omega
  have hpow : 4 ^ E = 4 ^ (4 * n) * 4 ^ (E - 4 * n) := by
    rw [← pow_add]
    congr 1
    omega
  rw [show (8 * n - 4) * n = E by rfl]
  rw [hpow, pow_succ]
  have hu' : 2 ^ n * 4 ^ (E - 4 * n) ≤ u := by simpa [E] using hu
  calc
    2 ^ n * (4 ^ (4 * n) * 4 ^ (E - 4 * n)) * u ^ E =
        4 ^ (4 * n) * (2 ^ n * 4 ^ (E - 4 * n)) * u ^ E := by ring
    _ ≤ 4 ^ (4 * n) * u * u ^ E := by gcongr
    _ = 4 ^ (4 * n) * (u ^ E * u) := by ring

theorem iterationLength_eq {n : ℕ} (hn : 3 ≤ n) :
    iterationLength n = (8 * n - 4) * n - 4 * n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [iterationLength]
  have h₁ : 8 * (3 + k) - 4 = 20 + 8 * k := by omega
  have h₂ : 3 + k - 1 = 2 + k := by omega
  rw [h₁, h₂]
  apply Nat.eq_sub_of_add_eq
  ring

/-- The terminal component box is nonempty under the same explicit threshold that makes the sample
range dominate the column count. -/
theorem final_stageOrder_pos
    {n u : ℕ} (hn : 3 ≤ n)
    (hu : 2 ^ n * 4 ^ ((8 * n - 4) * n - 4 * n) ≤ u) :
    0 < stageOrder n (4 * u) (iterationLength n) := by
  have hu4 : 4 ^ iterationLength n ≤ u := by
    rw [iterationLength_eq hn]
    calc
      4 ^ ((8 * n - 4) * n - 4 * n) ≤
          2 ^ n * 4 ^ ((8 * n - 4) * n - 4 * n) := by
        exact Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)
      _ ≤ u := hu
  have hdenu : 2 ^ iterationLength n ≤ u := by
    exact (Nat.pow_le_pow_left (by norm_num : 2 ≤ 4) _).trans hu4
  have htpos : 0 < 4 * u := by
    have hthreshold : 0 < 2 ^ n * 4 ^ ((8 * n - 4) * n - 4 * n) :=
      mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
    have : 0 < u := lt_of_lt_of_le hthreshold hu
    positivity
  have htPow : 4 * u ≤ (4 * u) ^ (8 * n) := by
    exact Nat.le_pow (by omega)
  unfold stageOrder BakerParameters.extrapolationOrder
  exact Nat.div_pos
    (hdenu.trans (le_trans (Nat.le_mul_of_pos_left u (by norm_num)) htPow))
    (pow_pos (by norm_num) _)

@[simp] theorem stageOrder_zero (n t : ℕ) :
    stageOrder n t 0 = BakerParameters.extrapolationOrder n t := by
  simp [stageOrder]

theorem stageOrder_succ (n t k : ℕ) :
    stageOrder n t (k + 1) = stageOrder n t k / 2 := by
  unfold stageOrder
  rw [pow_succ, ← Nat.div_div_eq_div_mul]

theorem two_mul_stageOrder_succ_le (n t k : ℕ) :
    2 * stageOrder n t (k + 1) ≤ stageOrder n t k := by
  rw [stageOrder_succ]
  exact Nat.mul_div_le _ _

/-- The next stage sample interval lies in the first quarter of the radius `t * S_k`. -/
theorem four_mul_stageSampleCount_succ_le (n t k : ℕ) :
    4 * stageSampleCount n t (k + 1) ≤ t * stageSampleCount n t k := by
  rw [stageSampleCount_succ]
  have ht := Nat.mul_div_le t 4
  calc
    4 * (stageSampleCount n t k * (t / 4)) =
        (4 * (t / 4)) * stageSampleCount n t k := by ring
    _ ≤ t * stageSampleCount n t k := Nat.mul_le_mul_right _ ht

theorem stageSampleCount_succ_le_quarterRadius (n t k : ℕ) :
    stageSampleCount n t (k + 1) ≤ t * stageSampleCount n t k / 4 + 1 := by
  have hdiv : stageSampleCount n t (k + 1) ≤ t * stageSampleCount n t k / 4 :=
    (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr
      (by simpa [mul_comm] using four_mul_stageSampleCount_succ_le n t k)
  omega

theorem stageSample_mem_closedBall {n t k : ℕ}
    (sample : Fin (stageSampleCount n t (k + 1))) :
    ((sample : ℕ) : ℂ) ∈
      Metric.closedBall 0 (t * stageSampleCount n t k : ℝ) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  simp only [sub_zero, Complex.norm_natCast]
  exact_mod_cast (le_trans (Nat.le_mul_of_pos_left (sample : ℕ) (by norm_num))
    (le_trans (Nat.mul_le_mul_left 4 sample.isLt.le)
      (four_mul_stageSampleCount_succ_le n t k)))

/-- Uniform Schwarz node decay at one long-extrapolation stage, for an arbitrary multiplicity. -/
theorem stageSample_node_ratio_le_two_thirds_of_order
    {n t k q : ℕ} (ht : 8 ≤ t)
    (hS : 0 < stageSampleCount n t k)
    (sample : Fin (stageSampleCount n t (k + 1))) :
    let S := stageSampleCount n t k
    (((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S)) /
      (((t * S : ℕ) : ℝ) - S) ^ (q * S)) ≤
        ((2 : ℝ) / 3) ^ (q * S) := by
  dsimp only
  let S := stageSampleCount n t k
  have hrpos : (0 : ℝ) < (t * S : ℕ) - S := by
    apply sub_pos.mpr
    exact_mod_cast (show S < t * S by
      simpa using (Nat.mul_lt_mul_right hS).mpr (by omega : 1 < t))
  rw [← div_pow]
  apply pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hrpos.le)
  rw [div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 3)]
  have hsamp : (sample : ℕ) ≤ S * (t / 4) := by
    simpa [S, stageSampleCount_succ] using sample.isLt.le
  have hfloor : 4 * (t / 4) ≤ t := Nat.mul_div_le t 4
  have hsampR : ((sample : ℕ) : ℝ) ≤ ((S * (t / 4) : ℕ) : ℝ) := by
    exact_mod_cast hsamp
  have hfloorR : ((4 * (t / 4) : ℕ) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hfloor
  have htR : (8 : ℝ) ≤ t := by exact_mod_cast ht
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS
  push_cast at hsampR hfloorR
  push_cast
  nlinarith

/-- Uniform Schwarz node decay at the prescribed next-stage multiplicity. -/
theorem stageSample_node_ratio_le_two_thirds
    {n t k : ℕ} (ht : 8 ≤ t)
    (hS : 0 < stageSampleCount n t k)
    (sample : Fin (stageSampleCount n t (k + 1))) :
    let S := stageSampleCount n t k
    let q := stageOrder n t (k + 1)
    (((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S)) /
      (((t * S : ℕ) : ℝ) - S) ^ (q * S)) ≤
        ((2 : ℝ) / 3) ^ (q * S) :=
  stageSample_node_ratio_le_two_thirds_of_order ht hS sample

theorem stageGrowthMajorant_nonneg
    (R : Relation) (c : ℤ) (t k v : ℕ) :
    0 ≤ stageGrowthMajorant R c t k v := by
  unfold stageGrowthMajorant
  dsimp only
  have hD : 0 ≤ (2 : ℝ) * BakerParameters.exponentWidth R.n t *
      R.scaledCoefficientHouseSum c := by
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by
        unfold Relation.scaledCoefficientHouseSum
        exact Finset.sum_nonneg fun i hi => house_nonneg _)
  have hH := BakerParameters.linearCoefficientBudget_nonneg R c t
  positivity

/-- The stage budget factors through the already-controlled first-step shifted budget and two new
positive factors carrying the enlarged radius and sample endpoint. -/
theorem stageGrowthMajorant_le_shifted_mul
    (R : Relation) (c : ℤ) (t k v : ℕ) :
    let L := BakerParameters.exponentWidth R.n t
    let S := stageSampleCount R.n t (k + 1)
    let S' := stageSampleCount R.n t (k + 2)
    let radius : ℝ := t * S
    let d := Module.finrank ℚ R.CoefficientField - 1
    stageGrowthMajorant R c t k v ≤
      BakerParameters.shiftedFirstStepGrowthMajorant R c t v *
        Real.exp ((L * R.primeLogWeight) * radius) *
          ((R.primeProduct : ℝ) ^ (L * S')) ^ d := by
  dsimp only
  let L := BakerParameters.exponentWidth R.n t
  let S₀ := BakerParameters.sampleCount R.n t
  let S := stageSampleCount R.n t (k + 1)
  let S' := stageSampleCount R.n t (k + 2)
  let r₀ := BakerParameters.extrapolationRadius R.n t
  let radius : ℝ := t * S
  let Hη := BakerParameters.linearCoefficientBudget R c t
  let d := Module.finrank ℚ R.CoefficientField - 1
  let D : ℝ := 2 * L * R.scaledCoefficientHouseSum c
  let X : ℝ := ((L ^ R.n : ℕ) : ℝ)
  let E₀ : ℝ := Real.exp ((L * R.primeLogWeight) * r₀)
  let E : ℝ := Real.exp ((L * R.primeLogWeight) * radius)
  let P₀ : ℝ := (R.primeProduct : ℝ) ^ (L * S₀)
  let P : ℝ := (R.primeProduct : ℝ) ^ (L * S')
  let G : ℝ := X * (D ^ v * Hη * E) * (X * (D ^ v * Hη * P)) ^ d
  have hG0 : 0 ≤ G := by
    dsimp only [G, X, D, Hη, E, P]
    have hH := BakerParameters.linearCoefficientBudget_nonneg R c t
    have hC : 0 ≤ R.scaledCoefficientHouseSum c := by
      unfold Relation.scaledCoefficientHouseSum
      exact Finset.sum_nonneg fun i hi => house_nonneg _
    positivity
  have hweight : 0 ≤ R.primeLogWeight := by
    unfold Relation.primeLogWeight
    exact Finset.sum_nonneg fun i hi => (R.p_prime i).log_pos.le
  have hE₀ : 1 ≤ E₀ := by
    dsimp only [E₀]
    exact Real.one_le_exp (mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hweight) (Nat.cast_nonneg _))
  have hPone : (1 : ℝ) ≤ R.primeProduct := by exact_mod_cast R.one_le_primeProduct
  have hP₀ : 1 ≤ P₀ ^ d := one_le_pow₀ (one_le_pow₀ hPone)
  have hextra : 1 ≤ E₀ * P₀ ^ d := by
    simpa using mul_le_mul hE₀ hP₀ (by norm_num : (0 : ℝ) ≤ 1) (zero_le_one.trans hE₀)
  change G ≤ _
  calc
    G ≤ G * (E₀ * P₀ ^ d) := le_mul_of_one_le_right hG0 hextra
    _ = BakerParameters.shiftedFirstStepGrowthMajorant R c t v * E * P ^ d := by
      unfold BakerParameters.shiftedFirstStepGrowthMajorant
        BakerParameters.firstStepGrowthMajorant
      dsimp only [G, X, D, Hη, E₀, E, P₀, P, L, S₀, r₀, radius, d]
      simp only [mul_pow]
      ring

/-- For each fixed iteration stage, every shifted-component growth budget lies on scale
`exp(C * t^(12n+k))`, one full power below the stage Schwarz decay. -/
theorem eventually_stageGrowthMajorant_le_exp
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (k : ℕ) :
    ∀ᶠ t : ℕ in atTop, ∀ v : ℕ,
      v ≤ (R.n - 1) * stageOrder R.n t (k + 1) →
      stageGrowthMajorant R c t k v ≤
        Real.exp (stageGrowthExponentConstant R *
          (t ^ (12 * R.n + k) : ℕ)) := by
  filter_upwards [BakerParameters.eventually_shiftedFirstStepGrowthMajorant_le_exp_dominant
    R hn c, eventually_ge_atTop 2] with t hshift ht
  intro v hv
  let L := BakerParameters.exponentWidth R.n t
  let S := stageSampleCount R.n t (k + 1)
  let S' := stageSampleCount R.n t (k + 2)
  let radius : ℝ := t * S
  let d := Module.finrank ℚ R.CoefficientField - 1
  let N := t ^ (12 * R.n + k)
  have hv' : v ≤ (R.n - 1) * BakerParameters.extrapolationOrder R.n t := by
    exact hv.trans (Nat.mul_le_mul_left _ (Nat.div_le_self _ _))
  have hshift0 := hshift v hv'
  have hpowOld : t ^ (12 * R.n - 1) ≤ N := by
    dsimp only [N]
    exact pow_le_pow_right₀ (by omega : 1 ≤ t) (by omega)
  have hCshift0 : 0 ≤ BakerParameters.shiftedGrowthExponentConstant R := by
    unfold BakerParameters.shiftedGrowthExponentConstant
    dsimp only
    exact add_nonneg (BakerParameters.growthExponentConstant_nonneg R)
      (Nat.cast_nonneg _)
  have hshiftN : BakerParameters.shiftedFirstStepGrowthMajorant R c t v ≤
      Real.exp (BakerParameters.shiftedGrowthExponentConstant R * N) := by
    apply hshift0.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hpowOld) hCshift0
  have hLRnat : L * (t * S) ≤ 2 * N := by
    dsimp only [L, S, N]
    exact (exponentWidth_mul_stageRadius_le (n := R.n) (t := t) (k := k) hn).trans
      (Nat.mul_le_mul_left 2 (pow_le_pow_right₀ (by omega : 1 ≤ t) (by omega)))
  have hLSnat : L * S' ≤ 2 * N := by
    dsimp only [L, S', N]
    exact (exponentWidth_mul_nextStageSample_le (n := R.n) (t := t) (k := k) hn).trans
      (Nat.mul_le_mul_left 2 (pow_le_pow_right₀ (by omega : 1 ≤ t) (by omega)))
  have hweight : 0 ≤ R.primeLogWeight := by
    unfold Relation.primeLogWeight
    exact Finset.sum_nonneg fun i hi => (R.p_prime i).log_pos.le
  have hanalytic : Real.exp ((L * R.primeLogWeight) * radius) ≤
      Real.exp ((2 * R.primeLogWeight) * N) := by
    apply Real.exp_le_exp.mpr
    have hLR : (L : ℝ) * (t * S : ℕ) ≤ 2 * (N : ℝ) := by exact_mod_cast hLRnat
    dsimp only [radius]
    push_cast at hLR ⊢
    nlinarith
  have hPpos : (0 : ℝ) < R.primeProduct := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one R.one_le_primeProduct)
  have hPone : (1 : ℝ) ≤ R.primeProduct := by exact_mod_cast R.one_le_primeProduct
  have hlogP : 0 ≤ Real.log (R.primeProduct : ℝ) := Real.log_nonneg hPone
  have hPbase : (R.primeProduct : ℝ) ^ (L * S') ≤
      Real.exp (Real.log R.primeProduct * (2 * N)) := by
    calc
      (R.primeProduct : ℝ) ^ (L * S') =
          (Real.exp (Real.log R.primeProduct)) ^ (L * S') := by
        rw [Real.exp_log hPpos]
      _ = Real.exp ((L * S' : ℕ) * Real.log R.primeProduct) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log R.primeProduct * (2 * N)) := by
        apply Real.exp_le_exp.mpr
        have hLS : ((L * S' : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hLSnat
        nlinarith
  have hPpow : ((R.primeProduct : ℝ) ^ (L * S')) ^ d ≤
      Real.exp ((2 * d * Real.log R.primeProduct) * N) := by
    calc
      ((R.primeProduct : ℝ) ^ (L * S')) ^ d ≤
          (Real.exp (Real.log R.primeProduct * (2 * N))) ^ d :=
        pow_le_pow_left₀ (pow_nonneg (Nat.cast_nonneg _) _) hPbase _
      _ = Real.exp ((2 * d * Real.log R.primeProduct) * N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    stageGrowthMajorant R c t k v ≤
        BakerParameters.shiftedFirstStepGrowthMajorant R c t v *
          Real.exp ((L * R.primeLogWeight) * radius) *
            ((R.primeProduct : ℝ) ^ (L * S')) ^ d :=
      stageGrowthMajorant_le_shifted_mul R c t k v
    _ ≤ Real.exp (BakerParameters.shiftedGrowthExponentConstant R * N) *
          Real.exp ((2 * R.primeLogWeight) * N) *
            Real.exp ((2 * d * Real.log R.primeProduct) * N) := by
      gcongr
    _ = Real.exp (stageGrowthExponentConstant R * N) := by
      rw [← Real.exp_add, ← Real.exp_add]
      unfold stageGrowthExponentConstant
      dsimp only [d]
      congr 1
      ring

/-- Geometric decay at scale `u^(b+1)` dominates every fixed exponential at scale `u^b`. -/
theorem eventually_decay_pow_succ_mul_exp_pow_lt_one_const
    (b : ℕ) (C : ℝ) :
    ∀ᶠ u : ℕ in atTop,
      ((2 : ℝ) / 3) ^ (u ^ (b + 1)) *
        Real.exp (C * (u ^ b : ℕ)) < 1 := by
  have hdecayU : Tendsto
      (fun u : ℕ => ((2 : ℝ) / 3) ^ u * Real.exp C)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ (2 : ℝ) / 3)
      (by norm_num : (2 : ℝ) / 3 < 1)).mul_const
        (Real.exp C)
  have hbase : ∀ᶠ u : ℕ in atTop,
      ((2 : ℝ) / 3) ^ u * Real.exp C < 1 :=
    (tendsto_order.1 hdecayU).2 1 (by norm_num)
  filter_upwards [hbase, eventually_ge_atTop 1] with u hu hu1
  let N := u ^ b
  have hNpos : 0 < N := pow_pos (by omega) _
  have hpow : (((2 : ℝ) / 3) ^ u * Real.exp C) ^ N < 1 :=
    pow_lt_one₀ (mul_nonneg (pow_nonneg (by norm_num) _)
      (Real.exp_nonneg _)) hu hNpos.ne'
  have hscale : u ^ (b + 1) = u * N := by
    dsimp only [N]
    rw [pow_succ']
  have hexp : Real.exp (C * (N : ℕ)) = (Real.exp C) ^ N := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hscale, pow_mul, hexp, ← mul_pow]
  exact hpow

theorem stageGrowthExponentConstant_nonneg (R : Relation) :
    0 ≤ stageGrowthExponentConstant R := by
  have hshift : 0 ≤ BakerParameters.shiftedGrowthExponentConstant R := by
    unfold BakerParameters.shiftedGrowthExponentConstant
    dsimp only
    exact add_nonneg (BakerParameters.growthExponentConstant_nonneg R) (Nat.cast_nonneg _)
  have hweight : 0 ≤ R.primeLogWeight := by
    unfold Relation.primeLogWeight
    exact Finset.sum_nonneg fun i hi => (R.p_prime i).log_pos.le
  have hPone : (1 : ℝ) ≤ R.primeProduct := by exact_mod_cast R.one_le_primeProduct
  have hlogP : 0 ≤ Real.log (R.primeProduct : ℝ) := Real.log_nonneg hPone
  unfold stageGrowthExponentConstant
  dsimp only
  positivity

theorem structuredBase_tendsto_atTop (n : ℕ) :
    Tendsto (structuredBase n) atTop atTop := by
  apply Filter.tendsto_atTop_mono (fun u => ?_) Filter.tendsto_id
  simpa [structuredBase, mul_assoc] using Nat.le_mul_of_pos_left u
    (mul_pos (by norm_num : 0 < (4 : ℕ)) (structuredMultiplier_pos n))

/-- On the cofinal divisible parameter subfamily, the strict one-power gap between Schwarz decay
and closed stage growth discharges every shifted-component scalar inequality at one fixed stage. -/
theorem eventually_structured_stageSmallness
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (k : ℕ)
    (hk : k < iterationLength R.n) :
    ∀ᶠ u : ℕ in atTop, ∀ v : ℕ,
      v ≤ (R.n - 1) * stageOrder R.n (structuredBase R.n u) (k + 1) →
      ((2 : ℝ) / 3) ^
          (stageOrder R.n (structuredBase R.n u) (k + 1) *
            stageSampleCount R.n (structuredBase R.n u) (k + 1)) *
        stageGrowthMajorant R c (structuredBase R.n u) k v < 1 := by
  let b := 12 * R.n + k
  let C₀ := 4 * structuredMultiplier R.n
  let C := stageGrowthExponentConstant R * (C₀ : ℝ) ^ b
  have hgrowth := (structuredBase_tendsto_atTop R.n).eventually
    (eventually_stageGrowthMajorant_le_exp R hn c k)
  have hdecay := eventually_decay_pow_succ_mul_exp_pow_lt_one_const b C
  filter_upwards [hgrowth, hdecay] with u hgrowthu hdecayu
  intro v hv
  have hgrowth' := hgrowthu v hv
  have hstruct : structuredBase R.n u = C₀ * u := by
    simp [structuredBase, C₀, mul_assoc]
  have hgrowthExact :
      Real.exp (stageGrowthExponentConstant R *
        ((structuredBase R.n u) ^ b : ℕ)) =
      Real.exp (C * (u ^ b : ℕ)) := by
    congr 1
    rw [hstruct, mul_pow]
    dsimp only [C]
    push_cast
    ring
  have hgrowthC : stageGrowthMajorant R c (structuredBase R.n u) k v ≤
      Real.exp (C * (u ^ b : ℕ)) := by
    change stageGrowthMajorant R c (structuredBase R.n u) k v ≤
      Real.exp (stageGrowthExponentConstant R *
        ((structuredBase R.n u) ^ b : ℕ)) at hgrowth'
    rw [hgrowthExact] at hgrowth'
    exact hgrowth'
  have hexp : u ^ (b + 1) ≤
      stageOrder R.n (structuredBase R.n u) (k + 1) *
        stageSampleCount R.n (structuredBase R.n u) (k + 1) := by
    dsimp only [b]
    exact decayExponent_le_stage hn hk.le
  have hdecayPow : ((2 : ℝ) / 3) ^
      (stageOrder R.n (structuredBase R.n u) (k + 1) *
        stageSampleCount R.n (structuredBase R.n u) (k + 1)) ≤
      ((2 : ℝ) / 3) ^ (u ^ (b + 1)) := by
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
  exact lt_of_le_of_lt
    (mul_le_mul hdecayPow hgrowthC (stageGrowthMajorant_nonneg R c _ k v)
      (pow_nonneg (by norm_num) _)) hdecayu

/-- All finitely many long-extrapolation scalar inequalities hold simultaneously for sufficiently
large structured parameter base. -/
theorem eventually_all_structured_stageSmallness
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) :
    ∀ᶠ u : ℕ in atTop, ∀ k < iterationLength R.n, ∀ v : ℕ,
      v ≤ (R.n - 1) * stageOrder R.n (structuredBase R.n u) (k + 1) →
      ((2 : ℝ) / 3) ^
          (stageOrder R.n (structuredBase R.n u) (k + 1) *
            stageSampleCount R.n (structuredBase R.n u) (k + 1)) *
        stageGrowthMajorant R c (structuredBase R.n u) k v < 1 := by
  have hall : ∀ᶠ u : ℕ in atTop,
      ∀ k ∈ Finset.range (iterationLength R.n), ∀ v : ℕ,
        v ≤ (R.n - 1) * stageOrder R.n (structuredBase R.n u) (k + 1) →
        ((2 : ℝ) / 3) ^
            (stageOrder R.n (structuredBase R.n u) (k + 1) *
              stageSampleCount R.n (structuredBase R.n u) (k + 1)) *
          stageGrowthMajorant R c (structuredBase R.n u) k v < 1 := by
    rw [Filter.eventually_all_finset]
    intro k hk
    exact eventually_structured_stageSmallness R hn c k (Finset.mem_range.mp hk)
  filter_upwards [hall] with u hu
  intro k hk
  exact hu k (Finset.mem_range.mpr hk)

/-- The separated node-ratio estimate turns one closed stage-majorant inequality into the exact
scalar inequality consumed by `auxiliaryMatrix_kernel_extrapolate`. -/
theorem stage_scalar_smallness_of_majorant
    (R : Relation) (c : ℤ) {pivot : Fin R.n} (t k : ℕ) (ht : 8 ≤ t)
    (sample : Fin (stageSampleCount R.n t (k + 2)))
    (ν : R.NonPivot pivot → Fin (stageOrder R.n t (k + 1)))
    (hsmall : ((2 : ℝ) / 3) ^
        (stageOrder R.n t (k + 1) * stageSampleCount R.n t (k + 1)) *
          stageGrowthMajorant R c t k (∑ i, (ν i : ℕ)) < 1) :
    let L := BakerParameters.exponentWidth R.n t
    let S := stageSampleCount R.n t (k + 1)
    let q := stageOrder R.n t (k + 1)
    let radius : ℝ := t * S
    let Hη := BakerParameters.linearCoefficientBudget R c t
    ((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S) *
      ((((L ^ R.n : ℕ) : ℝ) *
        ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
          Real.exp ((L * R.primeLogWeight) * radius))) /
        (radius - S) ^ (q * S))) *
      (((L ^ R.n : ℕ) : ℝ) *
        ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
          (R.primeProduct : ℝ) ^ (L * (sample : ℕ)))) ^
        (Module.finrank ℚ R.CoefficientField - 1) < 1 := by
  dsimp only
  let L := BakerParameters.exponentWidth R.n t
  let S := stageSampleCount R.n t (k + 1)
  let S' := stageSampleCount R.n t (k + 2)
  let q := stageOrder R.n t (k + 1)
  let radius : ℝ := t * S
  let Hη := BakerParameters.linearCoefficientBudget R c t
  let d := Module.finrank ℚ R.CoefficientField - 1
  let D : ℝ := 2 * L * R.scaledCoefficientHouseSum c
  let v := ∑ i, (ν i : ℕ)
  let node : ℝ := (((sample : ℕ) + S : ℕ) : ℝ)
  let den : ℝ := radius - S
  let X : ℝ := ((L ^ R.n : ℕ) : ℝ)
  let A : ℝ := X * (D ^ v * Hη * Real.exp ((L * R.primeLogWeight) * radius))
  let H : ℝ := (X * (D ^ v * Hη *
    (R.primeProduct : ℝ) ^ (L * (sample : ℕ)))) ^ d
  let G : ℝ := A * H
  have hratio : node ^ (q * S) / den ^ (q * S) ≤
      ((2 : ℝ) / 3) ^ (q * S) := by
    simpa [node, den, q, S, radius] using
      stageSample_node_ratio_le_two_thirds_of_order (q := q) ht
        (stageSampleCount_pos (n := R.n) (k := k + 1) (by omega)) sample
  have hPone : (1 : ℝ) ≤ R.primeProduct := by exact_mod_cast R.one_le_primeProduct
  have hsamp : (sample : ℕ) ≤ S' := sample.isLt.le
  have hPsamp : (R.primeProduct : ℝ) ^ (L * (sample : ℕ)) ≤
      (R.primeProduct : ℝ) ^ (L * S') := by
    exact pow_le_pow_right₀ hPone (Nat.mul_le_mul_left L hsamp)
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      (by
        unfold Relation.scaledCoefficientHouseSum
        exact Finset.sum_nonneg fun i hi => house_nonneg _)
  have hHη0 : 0 ≤ Hη := BakerParameters.linearCoefficientBudget_nonneg R c t
  have hG0 : 0 ≤ G := by
    dsimp only [G, A, H, X]
    positivity
  have hGle : G ≤ stageGrowthMajorant R c t k v := by
    dsimp only [G, A, H, X]
    unfold stageGrowthMajorant
    dsimp only
    gcongr
  have hid : (node ^ (q * S) * (A / den ^ (q * S))) * H =
      (node ^ (q * S) / den ^ (q * S)) * G := by
    dsimp only [G]
    ring
  change (node ^ (q * S) * (A / den ^ (q * S))) * H < 1
  rw [hid]
  exact lt_of_le_of_lt
    ((mul_le_mul_of_nonneg_right hratio hG0).trans
      (mul_le_mul_of_nonneg_left hGle (pow_nonneg (by norm_num) _))) hsmall

end BakerIteration

/-- Restricting either the sample range or the component box preserves an auxiliary-matrix kernel. -/
theorem Relation.auxiliaryMatrix_kernel_mono
    (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    {S' T' : ℕ} (hS : S' ≤ S) (hT : T' ≤ T) :
    Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S' T') η = 0 := by
  apply R.auxiliaryMatrix_mulVec_eq_zero_of_component_box_zero
  intro sample ν
  exact R.auxiliaryComponent_eq_zero_of_kernel c hint pivot η hker
    ⟨sample, lt_of_lt_of_le sample.isLt hS⟩ (fun i => (ν i : ℕ))
      (fun i => lt_of_lt_of_le (ν i).isLt hT)

/-- The unconditional first quarter-disc extrapolation is the base case of the long iteration. -/
theorem Relation.exists_parameterized_stageOne_kernel_of_scale
    (R : Relation) (hn : 3 ≤ R.n) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n) :
    ∃ t : ℕ, 4 ≤ t ∧ 2 ^ (R.n + 2) < t ∧
      ∃ η : R.Column (BakerParameters.exponentWidth R.n t) → 𝓞 R.CoefficientField,
        η ≠ 0 ∧
          Matrix.mulVec (R.auxiliaryMatrix c hint pivot
            (BakerParameters.exponentWidth R.n t)
            (BakerIteration.stageSampleCount R.n t 1)
            (BakerIteration.stageOrder R.n t 0)) η = 0 := by
  obtain ⟨t, ht, htlarge, η, hη, hker⟩ :=
    BakerParameters.Relation.exists_parameterized_extended_auxiliary_kernel_of_scale
      R hn c hc hint pivot
  refine ⟨t, ht, htlarge, η, hη, ?_⟩
  apply R.auxiliaryMatrix_kernel_mono c hint pivot η hker
  · have hs := BakerIteration.stageSampleCount_succ_le_quarterRadius R.n t 0
    simpa [BakerParameters.quarterSampleCount,
      BakerParameters.extrapolationRadius_eq_mul_sampleCount] using hs
  · simp [BakerIteration.stageOrder]

/-- One long-extrapolation transition.  Exact zeros for every component in the new `q`-box are
reassembled as a kernel for the enlarged `S' × q^(n-1)` auxiliary matrix. -/
theorem Relation.auxiliaryMatrix_kernel_extrapolate
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (Hη : ℝ)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤ Hη)
    (hHη : 0 ≤ Hη)
    (q : ℕ) (hqT : 2 * q ≤ T)
    {radius : ℝ} (hradius : (S : ℝ) < radius)
    (S' : ℕ)
    (hsample : ∀ sample : Fin S',
      ((sample : ℕ) : ℂ) ∈ Metric.closedBall 0 radius)
    (hsmall : ∀ sample : Fin S', ∀ ν : R.NonPivot pivot → Fin q,
      ((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S) *
        ((((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
            Real.exp ((L * R.primeLogWeight) * radius))) /
          (radius - S) ^ (q * S))) *
        (((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
            (R.primeProduct : ℝ) ^ (L * (sample : ℕ)))) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S' q) η = 0 := by
  apply R.auxiliaryMatrix_mulVec_eq_zero_of_component_box_zero
  intro sample ν
  have hqT' : q + q ≤ T := by simpa [two_mul] using hqT
  have hνq : ∀ i, (ν i : ℕ) + q < T := fun i =>
    lt_of_lt_of_le (Nat.add_lt_add_right (ν i).isLt q) hqT'
  exact R.auxiliaryComponent_eq_zero_one_step_scalar
    c hc hint pivot η hker (fun i => (ν i : ℕ)) q hνq
      Hη hη hHη hradius (sample : ℕ) (hsample sample) (hsmall sample ν)

/-- Finite long extrapolation.  A single coefficient vector stays in the auxiliary-matrix kernel
while the sample interval is repeatedly enlarged and the component cutoff is halved.  All analytic
work is isolated in the explicit stagewise scalar inequalities `hsmall`. -/
theorem Relation.auxiliaryMatrix_kernel_iterate
    (R : Relation) (c : ℤ) (hc : c ≠ 0)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    (t : ℕ) (ht : 8 ≤ t)
    (η : R.Column (BakerParameters.exponentWidth R.n t) → 𝓞 R.CoefficientField)
    (Hη : ℝ)
    (hη : ∀ m, house ((algebraMap (𝓞 R.CoefficientField) R.CoefficientField) (η m)) ≤ Hη)
    (hHη : 0 ≤ Hη)
    (hbase : Matrix.mulVec (R.auxiliaryMatrix c hint pivot
      (BakerParameters.exponentWidth R.n t)
      (BakerIteration.stageSampleCount R.n t 1)
      (BakerIteration.stageOrder R.n t 0)) η = 0)
    (K : ℕ)
    (hsmall : ∀ k < K,
      ∀ sample : Fin (BakerIteration.stageSampleCount R.n t (k + 2)),
      ∀ ν : R.NonPivot pivot → Fin (BakerIteration.stageOrder R.n t (k + 1)),
      let L := BakerParameters.exponentWidth R.n t
      let S := BakerIteration.stageSampleCount R.n t (k + 1)
      let q := BakerIteration.stageOrder R.n t (k + 1)
      let radius : ℝ := t * S
      ((((sample : ℕ) + S : ℕ) : ℝ) ^ (q * S) *
        ((((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
            Real.exp ((L * R.primeLogWeight) * radius))) /
          (radius - S) ^ (q * S))) *
        (((L ^ R.n : ℕ) : ℝ) *
          ((2 * L * R.scaledCoefficientHouseSum c) ^ (∑ i, (ν i : ℕ)) * Hη *
            (R.primeProduct : ℝ) ^ (L * (sample : ℕ)))) ^
          (Module.finrank ℚ R.CoefficientField - 1) < 1) :
    ∀ k ≤ K, Matrix.mulVec (R.auxiliaryMatrix c hint pivot
      (BakerParameters.exponentWidth R.n t)
      (BakerIteration.stageSampleCount R.n t (k + 1))
      (BakerIteration.stageOrder R.n t k)) η = 0 := by
  intro k hk
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
      apply R.auxiliaryMatrix_kernel_extrapolate c hc hint pivot η
        (ih (Nat.le_trans (Nat.le_succ k) hk)) Hη hη hHη
        (q := BakerIteration.stageOrder R.n t (k + 1))
        (radius := (t : ℝ) * BakerIteration.stageSampleCount R.n t (k + 1))
        (S' := BakerIteration.stageSampleCount R.n t (k + 2))
      · exact BakerIteration.two_mul_stageOrder_succ_le R.n t k
      · exact_mod_cast (show
          BakerIteration.stageSampleCount R.n t (k + 1) <
            t * BakerIteration.stageSampleCount R.n t (k + 1) by
          have hS := BakerIteration.stageSampleCount_pos (n := R.n) (k := k + 1)
            (show 4 ≤ t by omega)
          simpa using (Nat.mul_lt_mul_right hS).mpr (by omega : 1 < t))
      · exact BakerIteration.stageSample_mem_closedBall
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hsmall k (by omega)

/-- Every Baker frequency is real.  This is recorded explicitly because the terminal sampling
nodes are the positive real numbers obtained by exponentiating these frequencies. -/
theorem Relation.frequency_im_eq_zero (R : Relation) {L : ℕ}
    (m : R.Column L) : (R.frequency m).im = 0 := by
  have hfreq : R.frequency m =
      ((∑ i, ((m i : ℕ) : ℝ) * Real.log (R.p i) : ℝ) : ℂ) := by
    unfold Relation.frequency
    push_cast
    rfl
  rw [hfreq]
  exact Complex.ofReal_im _

/-- Exponentiating the real Baker frequencies preserves their injectivity. -/
theorem Relation.exp_frequency_injective (R : Relation) {L : ℕ} :
    Function.Injective (fun m : R.Column L => Complex.exp (R.frequency m)) := by
  intro m₁ m₂ h
  apply R.frequency_injective
  apply Complex.ext
  · have hre := congrArg Complex.re h
    simpa [Complex.exp_re, R.frequency_im_eq_zero] using hre
  · simp [R.frequency_im_eq_zero]

/-- The zero shifted component is exactly the original auxiliary exponential polynomial. -/
theorem Relation.auxiliaryComponent_zero_eq_auxiliaryFunction
    (R : Relation) (c : ℤ) (pivot : Fin R.n) {L : ℕ}
    (η : R.Column L → 𝓞 R.CoefficientField) (z : ℂ) :
    R.auxiliaryComponent c pivot (fun _ => 0) η z = R.auxiliaryFunction η z := by
  simp [Relation.auxiliaryComponent, Relation.auxiliaryFunction]

/-- Terminal weak zero estimate.  If the zeroth component vanishes at at least as many consecutive
natural samples as there are columns, the ordinary Vandermonde matrix in the distinct positive
nodes `exp (frequency m)` forces every coefficient to vanish. -/
theorem Relation.auxiliaryMatrix_kernel_eq_zero_of_card_le_samples
    (R : Relation) (c : ℤ)
    (hint : ∀ i, IsIntegral ℤ (R.scaledCoeff c i)) (pivot : Fin R.n)
    {L S T : ℕ} (η : R.Column L → 𝓞 R.CoefficientField)
    (hker : Matrix.mulVec (R.auxiliaryMatrix c hint pivot L S T) η = 0)
    (hT : 0 < T) (hcard : Fintype.card (R.Column L) ≤ S) :
    η = 0 := by
  let N := Fintype.card (R.Column L)
  let e : Fin N ≃ R.Column L := (Fintype.equivFin _).symm
  let μ : Fin N → ℂ := fun j => Complex.exp (R.frequency (e j))
  let coeff : Fin N → ℂ := fun j => R.integralCoeffEmbedding (η (e j))
  have hμ : Function.Injective μ := R.exp_frequency_injective.comp e.injective
  have hmom : ∀ k : Fin N, ∑ j : Fin N, coeff j * μ j ^ (k : ℕ) = 0 := by
    intro k
    let sample : Fin S := ⟨k, lt_of_lt_of_le k.isLt hcard⟩
    have hz := R.auxiliaryComponent_eq_zero_of_kernel c hint pivot η hker sample
      (fun _ => 0) (fun _ => hT)
    rw [R.auxiliaryComponent_zero_eq_auxiliaryFunction] at hz
    change (∑ m : R.Column L, R.integralCoeffEmbedding (η m) *
      Complex.exp (R.frequency m * (sample : ℕ))) = 0 at hz
    change (∑ j : Fin N, R.integralCoeffEmbedding (η (e j)) *
      Complex.exp (R.frequency (e j)) ^ (k : ℕ)) = 0
    calc
      _ = ∑ m : R.Column L, R.integralCoeffEmbedding (η m) *
          Complex.exp (R.frequency m) ^ (k : ℕ) :=
        e.sum_comp (fun m => R.integralCoeffEmbedding (η m) *
          Complex.exp (R.frequency m) ^ (k : ℕ))
      _ = ∑ m : R.Column L, R.integralCoeffEmbedding (η m) *
          Complex.exp (R.frequency m * (sample : ℕ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        congr 1
        rw [← Complex.exp_nat_mul]
        congr 1
        simp [sample]
        ring
      _ = 0 := hz
  have hcoeff : coeff = 0 := vandermonde_moments_eq_zero_of_injective hμ hmom
  funext m
  let j := e.symm m
  have hj := congrFun hcoeff j
  have he : e j = m := e.apply_symm_apply m
  change R.integralCoeffEmbedding (η (e j)) = 0 at hj
  rw [he] at hj
  exact R.integralCoeffEmbedding_injective (by simpa using hj)

end GaloisForLFunctions.RHTower.BakerProof
