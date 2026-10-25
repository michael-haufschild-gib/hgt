import GaloisForLFunctions.BiarithmeticGeometry.WeightedBaseFiveDigits
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform refinement of digit profiles

Refining the base-five grid appends one digit. After renormalization its contribution
is positive and bounded by a geometric tail. Order completeness constructs the profile
with a uniform error at every grid depth.
-/

noncomputable section
open Finset Set Filter Topology
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Read the digit row on the base-five grid and remove its dilation growth. -/
def fiveDigitGrid (a : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  a⁻¹ ^ M * fiveDigitRow a ⌊(5 : ℝ) ^ M * x⌋₊

private theorem floor_grid_div_five (M : ℕ) (x : ℝ) :
    ⌊(5 : ℝ) ^ (M + 1) * x⌋₊ / 5 = ⌊(5 : ℝ) ^ M * x⌋₊ := by
  rw [← Nat.floor_div_natCast]
  congr 1
  rw [pow_succ]
  ring

/-- The exact increment is the newly appended base-five digit. -/
theorem fiveDigitGrid_increment (a : ℝ) (ha : a ≠ 0) (M : ℕ) (x : ℝ) :
    fiveDigitGrid a (M + 1) x - fiveDigitGrid a M x =
      a⁻¹ ^ (M + 1) * (⌊(5 : ℝ) ^ (M + 1) * x⌋₊ % 5 : ℕ) := by
  rw [fiveDigitGrid, fiveDigitRow_rec, floor_grid_div_five, fiveDigitGrid, pow_succ]
  field_simp [ha] <;> ring

private theorem fiveDigitGrid_increment_bounds (a : ℝ) (ha : 0 < a) (M : ℕ) (x : ℝ) :
    0 ≤ fiveDigitGrid a (M + 1) x - fiveDigitGrid a M x ∧
    fiveDigitGrid a (M + 1) x - fiveDigitGrid a M x ≤ 4 * a⁻¹ ^ (M + 1) := by
  rw [fiveDigitGrid_increment a ha.ne']
  have hd : (⌊(5 : ℝ) ^ (M + 1) * x⌋₊ % 5 : ℕ) ≤ 4 := by omega
  have hdR : ((⌊(5 : ℝ) ^ (M + 1) * x⌋₊ % 5 : ℕ) : ℝ) ≤ 4 := by exact_mod_cast hd
  constructor
  · positivity
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hdR
      (pow_nonneg (inv_nonneg.mpr ha.le) (M + 1))

theorem fiveDigitGrid_monotone (a : ℝ) (ha : 0 < a) (x : ℝ) :
    Monotone (fun M => fiveDigitGrid a M x) := by
  apply monotone_nat_of_le_succ
  intro M
  exact sub_nonneg.mp (fiveDigitGrid_increment_bounds a ha M x).1

private theorem fiveDigitGrid_capped_antitone (a : ℝ) (ha : 1 < a) (x : ℝ) :
    Antitone (fun M => fiveDigitGrid a M x + (4 / (a - 1)) * a⁻¹ ^ M) := by
  apply antitone_nat_of_succ_le
  intro M
  have h := (fiveDigitGrid_increment_bounds a (by linarith only [ha]) M x).2
  have he : 4 * a⁻¹ ^ (M + 1) + (4 / (a - 1)) * a⁻¹ ^ (M + 1) =
      (4 / (a - 1)) * a⁻¹ ^ M := by
    rw [pow_succ]
    have ha0 : a ≠ 0 := (lt_trans zero_lt_one ha).ne'
    have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha.ne'
    field_simp [ha0, ha1] <;> ring
  linarith only [h, he]

/-- Every later grid lies within one explicit geometric tail of the earlier grid. -/
theorem fiveDigitGrid_refinement_bound (a : ℝ) (ha : 1 < a) (M N : ℕ) (hMN : M ≤ N)
    (x : ℝ) :
    0 ≤ fiveDigitGrid a N x - fiveDigitGrid a M x ∧
      fiveDigitGrid a N x - fiveDigitGrid a M x ≤ (4 / (a - 1)) * a⁻¹ ^ M := by
  refine ⟨sub_nonneg.mpr (fiveDigitGrid_monotone a (by linarith only [ha]) x hMN), ?_⟩
  have h := fiveDigitGrid_capped_antitone a ha x hMN
  have hn : 0 ≤ (4 / (a - 1)) * a⁻¹ ^ N := by positivity
  linarith only [h, hn]

private theorem fiveDigitGrid_bddAbove (a : ℝ) (ha : 1 < a) (x : ℝ) :
    BddAbove (Set.range fun M => fiveDigitGrid a M x) := by
  refine ⟨fiveDigitGrid a 0 x + 4 / (a - 1), ?_⟩
  rintro _ ⟨M, rfl⟩
  have h := (fiveDigitGrid_refinement_bound a ha 0 M (Nat.zero_le M) x).2
  simpa only [pow_zero, mul_one, add_comm] using (sub_le_iff_le_add.mp h)

/-- The increasing grid limit, defined by order completeness. -/
def fiveDigitProfile (a x : ℝ) : ℝ := sSup (Set.range fun M => fiveDigitGrid a M x)

/-- The entire nonnegative-axis profile is approximated with a uniform geometric error. -/
theorem fiveDigitProfile_sub_grid_bounds (a : ℝ) (ha : 1 < a) (M : ℕ) (x : ℝ) :
    0 ≤ fiveDigitProfile a x - fiveDigitGrid a M x ∧
      fiveDigitProfile a x - fiveDigitGrid a M x ≤ (4 / (a - 1)) * a⁻¹ ^ M := by
  have hlow : fiveDigitGrid a M x ≤ fiveDigitProfile a x :=
    le_csSup (fiveDigitGrid_bddAbove a ha x) ⟨M, rfl⟩
  refine ⟨sub_nonneg.mpr hlow, sub_le_iff_le_add.mpr ?_⟩
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨N, rfl⟩
  by_cases hMN : M ≤ N
  · exact sub_le_iff_le_add.mp (fiveDigitGrid_refinement_bound a ha M N hMN x).2
  · have h := fiveDigitGrid_monotone a (by linarith only [ha]) x (by omega : N ≤ M)
    have hp : 0 ≤ (4 / (a - 1)) * a⁻¹ ^ M := by positivity
    linarith only [h, hp]

/-- The increasing digit grids converge uniformly on the whole real axis. -/
theorem fiveDigitGrid_tendstoUniformly (a : ℝ) (ha : 1 < a) :
    TendstoUniformly (fiveDigitGrid a) (fiveDigitProfile a) atTop := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hinv : |a⁻¹| < 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr ha0.le), inv_eq_one_div]
    exact (div_lt_one ha0).mpr ha
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hinv
  have htail : Tendsto (fun M : ℕ => (4 / (a - 1)) * a⁻¹ ^ M) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 4 / (a - 1))
        atTop (𝓝 (4 / (a - 1)))).mul hpow
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [htail.eventually (gt_mem_nhds hε)] with M hM
  intro x
  obtain ⟨hlo, hhi⟩ := fiveDigitProfile_sub_grid_bounds a ha M x
  rw [Real.dist_eq, abs_of_nonneg hlo]
  exact hhi.trans_lt hM

theorem fiveDigitGrid_tendsto (a : ℝ) (ha : 1 < a) (x : ℝ) :
    Tendsto (fun M => fiveDigitGrid a M x) atTop (𝓝 (fiveDigitProfile a x)) :=
  (fiveDigitGrid_tendstoUniformly a ha).tendsto_at x

/-- Integer arguments already stabilize on the first grid. -/
theorem fiveDigitGrid_natCast (a : ℝ) (ha : a ≠ 0) (M n : ℕ) :
    fiveDigitGrid a M n = fiveDigitRow a n := by
  have hfloor : ⌊(5 : ℝ) ^ M * n⌋₊ = 5 ^ M * n := by
    have hcast : (5 : ℝ) ^ M * n = ((5 ^ M * n : ℕ) : ℝ) := by
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [hcast, Nat.floor_natCast]
  have hrow : fiveDigitRow a (5 ^ M * n) = a ^ M * fiveDigitRow a n := by
    simpa only [add_zero, fiveDigitRow_zero] using
      fiveDigitRow_concat a M n 0 (pow_pos (by omega : 0 < 5) M)
  rw [fiveDigitGrid, hfloor, hrow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha,
    one_pow, one_mul]

/-- The limiting profile retains every exact integer digit value. -/
theorem fiveDigitProfile_natCast (a : ℝ) (ha : 1 < a) (n : ℕ) :
    fiveDigitProfile a n = fiveDigitRow a n := by
  have ha0 : a ≠ 0 := (lt_trans zero_lt_one ha).ne'
  simp only [fiveDigitProfile, fiveDigitGrid_natCast a ha0]
  simp

private theorem fiveDigitGrid_mul_five (a : ℝ) (ha : a ≠ 0) (M : ℕ) (x : ℝ) :
    fiveDigitGrid a M (5 * x) = a * fiveDigitGrid a (M + 1) x := by
  have harg : (5 : ℝ) ^ M * (5 * x) = (5 : ℝ) ^ (M + 1) * x := by rw [pow_succ]; ring
  rw [fiveDigitGrid, harg, fiveDigitGrid, pow_succ (a⁻¹) M]
  calc
    _ = (a * a⁻¹) * (a⁻¹ ^ M * fiveDigitRow a ⌊(5 : ℝ) ^ (M + 1) * x⌋₊) := by
      rw [mul_inv_cancel₀ ha, one_mul]
    _ = _ := by ring

/-- The limit has exact base-five scaling. -/
theorem fiveDigitProfile_mul_five (a : ℝ) (ha : 1 < a) (x : ℝ) :
    fiveDigitProfile a (5 * x) = a * fiveDigitProfile a x := by
  have ht : Tendsto (fun M : ℕ => a * fiveDigitGrid a (M + 1) x)
      atTop (𝓝 (a * fiveDigitProfile a x)) :=
    tendsto_const_nhds.mul
      ((fiveDigitGrid_tendsto a ha x).comp (tendsto_add_atTop_nat 1))
  apply tendsto_nhds_unique (fiveDigitGrid_tendsto a ha (5 * x))
  convert ht using 1
  funext M
  exact fiveDigitGrid_mul_five a (lt_trans zero_lt_one ha).ne' M x

/-- A finite grid is constant on a sufficiently small right neighbourhood. -/
theorem fiveDigitGrid_continuousWithinAt_right (a : ℝ) (M : ℕ) (x : ℝ) :
    ContinuousWithinAt (fiveDigitGrid a M) (Ici x) x := by
  have hmul : ContinuousAt (fun y : ℝ => (5 : ℝ) ^ M * y) x := by fun_prop
  have hupper : ∀ᶠ y in 𝓝[Ici x] x,
      (5 : ℝ) ^ M * y < (⌊(5 : ℝ) ^ M * x⌋ : ℤ) + 1 :=
    (hmul.eventually (gt_mem_nhds (Int.lt_floor_add_one ((5 : ℝ) ^ M * x)))).filter_mono
      nhdsWithin_le_nhds
  have hgrid : fiveDigitGrid a M =ᶠ[𝓝[Ici x] x] fun _ => fiveDigitGrid a M x := by
    filter_upwards [hupper, self_mem_nhdsWithin] with y hy hxy
    have hfloor : ⌊(5 : ℝ) ^ M * y⌋ = ⌊(5 : ℝ) ^ M * x⌋ :=
      Int.floor_eq_iff.mpr ⟨(Int.floor_le _).trans
        (mul_le_mul_of_nonneg_left hxy (by positivity)), hy⟩
    simp only [fiveDigitGrid, ← Int.floor_toNat, hfloor]
  exact tendsto_const_nhds.congr' hgrid.symm

/-- Uniform refinement preserves the right continuity of every finite digit grid. -/
theorem fiveDigitProfile_continuousWithinAt_right (a : ℝ) (ha : 1 < a) (x : ℝ) :
    ContinuousWithinAt (fiveDigitProfile a) (Ici x) x := by
  apply continuousWithinAt_of_locally_uniform_approx_of_continuousWithinAt
    (show x ∈ Set.Ici x from Set.mem_Ici.mpr le_rfl)
  intro u hu
  obtain ⟨M, hM⟩ := ((fiveDigitGrid_tendstoUniformly a ha) u hu).exists
  exact ⟨univ, Filter.univ_mem, fiveDigitGrid a M,
    fiveDigitGrid_continuousWithinAt_right a M x, fun y _ => hM y⟩

theorem fiveDigitProfile_mul_five_pow (a : ℝ) (ha : 1 < a) (M : ℕ) (x : ℝ) :
    fiveDigitProfile a ((5 : ℝ) ^ M * x) = a ^ M * fiveDigitProfile a x := by
  induction M with
  | zero => simp only [pow_zero, one_mul]
  | succ M ih =>
    rw [pow_succ', mul_assoc, fiveDigitProfile_mul_five a ha, ih, pow_succ']
    ring

/-- Every base-five rational has its exact finite digit value in the limiting profile. -/
theorem fiveDigitProfile_fiveAdic (a : ℝ) (ha : 1 < a) (M n : ℕ) :
    fiveDigitProfile a ((n : ℝ) / (5 : ℝ) ^ M) = a⁻¹ ^ M * fiveDigitRow a n := by
  have hx : (5 : ℝ) ^ M * ((n : ℝ) / (5 : ℝ) ^ M) = n := by
    field_simp
  have h := fiveDigitProfile_mul_five_pow a ha M ((n : ℝ) / (5 : ℝ) ^ M)
  rw [hx, fiveDigitProfile_natCast a ha n] at h
  calc
    _ = a⁻¹ ^ M * (a ^ M * fiveDigitProfile a ((n : ℝ) / (5 : ℝ) ^ M)) := by
      rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (lt_trans zero_lt_one ha).ne',
        one_pow, one_mul]
    _ = _ := congrArg (fun z : ℝ => a⁻¹ ^ M * z) h.symm

end GaloisForLFunctions.BiarithmeticGeometry
