import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleSecondShadow

/-!
# Full chronological second-level convergence at a zeta zero

At a positive-real-part zeta zero, the Euler-deletion endpoint tail has the explicit Abel bound
`O(N^(-Re rho))`.  Right of the half-line, multiplying that tail by the next deletion jump gives
an absolutely summable `O(N^(-2 Re rho))` chronological second-level series.

This constructs a cutoff-independent complex second level and identifies its real part with the
strictly negative energy shadow.  It does not compare replication with Euler dilation.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace RHTower

/-- Explicit Abel constant for a modulus-`q + 1` deletion tail. -/
noncomputable def eulerDeletionAbelTailConstant (q : ℕ) (s : ℂ) : ℝ :=
  2 * q * (1 + ‖s‖ / s.re)

/-- At a zeta zero, the deletion endpoint prefix has the periodic Abel decay rate. -/
theorem norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero
    (q N : ℕ) {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    ‖∑ n ∈ Finset.range N, eulerDeletionWeightedJump q rho n‖ ≤
      eulerDeletionAbelTailConstant q rho * ((N : ℝ) + 1) ^ (-rho.re) := by
  have hconv := eulerDeletionDirichlet_convergesAt (q := q) (s := rho) hrhoRe
  have hbound0 : ∀ M,
      ‖GaloisForLFunctions.RHTower.dirichletPartialSum
        (eulerDeletionDirichletCoefficient q) M 0‖ ≤ q := by
    intro M
    simpa [GaloisForLFunctions.RHTower.dirichletPartialSum] using
      eulerDeletionDirichletCoefficient_partialSum_norm_le q M
  have htail := GaloisForLFunctions.RHTower.norm_dirichletSum_sub_partialSum_le
    (a := eulerDeletionDirichletCoefficient q) (s₀ := (0 : ℂ))
    hbound0 hrhoRe hconv N
  have hzero :=
    eulerDeletionDirichletSum_eq_zero_of_riemannZeta_eq_zero q hrhoRe hrho1 hzeta
  change GaloisForLFunctions.RHTower.dirichletSum
    (eulerDeletionDirichletCoefficient q) rho = 0 at hzero
  rw [hzero, zero_sub, norm_neg] at htail
  simpa [GaloisForLFunctions.RHTower.dirichletPartialSum,
    eulerDeletionWeightedJump, eulerDeletionAbelTailConstant] using htail

/-- Pointwise norm bound for the next weighted deletion jump. -/
theorem norm_eulerDeletionWeightedJump_le
    {q : ℕ} (hq : 0 < q) (s : ℂ) (n : ℕ) :
    ‖eulerDeletionWeightedJump q s n‖ ≤
      (q : ℝ) * ((n : ℝ) + 1) ^ (-s.re) := by
  rw [eulerDeletionWeightedJump, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]
  exact mul_le_mul_of_nonneg_right
    (norm_eulerDeletionDirichletCoefficient_le hq n)
    (Real.rpow_nonneg (by positivity) _)

/-- Summand of the strict chronological second level. -/
def chronologicalSecondTerm (z : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ i ∈ Finset.range n, z i) * star (z n)

/-- Ordered cross-level summand between two chronological paths. -/
def chronologicalCrossTerm (z w : ℕ → ℂ) (n : ℕ) : ℂ :=
  (∑ i ∈ Finset.range n, z i) * star (w n)

@[simp] theorem chronologicalCrossTerm_self (z : ℕ → ℂ) (n : ℕ) :
    chronologicalCrossTerm z z n = chronologicalSecondTerm z n := rfl

/-- Finite ordered cross level. -/
def chronologicalCrossPrefix (z w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, chronologicalCrossTerm z w n

/-- Pointwise cross bracket retained by the quasi-shuffle product. -/
def crossBracketPrefix (z w : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, z n * star (w n)

/-- Polarized finite quasi-shuffle identity for two chronological paths. -/
theorem endpoint_mul_star_endpoint_eq_cross_add_reverse_add_bracket
    (z w : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range N, z n) * star (∑ n ∈ Finset.range N, w n) =
      chronologicalCrossPrefix z w N + star (chronologicalCrossPrefix w z N) +
        crossBracketPrefix z w N := by
  induction N with
  | zero => simp [chronologicalCrossPrefix, crossBracketPrefix]
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, star_add, mul_add, add_mul, ih]
      simp only [chronologicalCrossPrefix, crossBracketPrefix, chronologicalCrossTerm,
        Finset.sum_range_succ, star_add, star_mul, star_star]
      ring

/-- At a right-half zeta zero, every chronological second summand has a summable power majorant. -/
theorem norm_chronologicalSecondTerm_eulerDeletion_le
    {q : ℕ} (hq : 0 < q) {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) (n : ℕ) :
    ‖chronologicalSecondTerm (eulerDeletionWeightedJump q rho) n‖ ≤
      (eulerDeletionAbelTailConstant q rho * q) *
        ((n : ℝ) + 1) ^ (-2 * rho.re) := by
  have hpref := norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero
    q n hrhoRe hrho1 hzeta
  have hjump := norm_eulerDeletionWeightedJump_le hq rho n
  have hpow : (((n : ℝ) + 1) ^ (-rho.re)) ^ 2 =
      ((n : ℝ) + 1) ^ (-2 * rho.re) := by
    rw [pow_two, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [chronologicalSecondTerm, norm_mul, norm_star]
  calc
    ‖∑ i ∈ Finset.range n, eulerDeletionWeightedJump q rho i‖ *
          ‖eulerDeletionWeightedJump q rho n‖ ≤
        (eulerDeletionAbelTailConstant q rho * ((n : ℝ) + 1) ^ (-rho.re)) *
          ((q : ℝ) * ((n : ℝ) + 1) ^ (-rho.re)) := by
            exact mul_le_mul hpref hjump (norm_nonneg _)
              (le_trans (norm_nonneg _) hpref)
    _ = (eulerDeletionAbelTailConstant q rho * q) *
          ((n : ℝ) + 1) ^ (-2 * rho.re) := by rw [← hpow]; ring

/-- The full complex chronological second level is absolutely summable right of the half-line. -/
theorem summable_chronologicalSecondTerm_eulerDeletion_of_zeta_zero
    {q : ℕ} (hq : 0 < q) {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Summable (chronologicalSecondTerm (eulerDeletionWeightedJump q rho)) := by
  have hrhoRe : 0 < rho.re := by linarith
  have hbase0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * rho.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * rho.re)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * rho.re)) 1).2 hbase0
  apply Summable.of_norm_bounded
    (hbase.mul_left (eulerDeletionAbelTailConstant q rho * q))
  exact norm_chronologicalSecondTerm_eulerDeletion_le hq hrhoRe hrho1 hzeta

/-- Canonical cutoff-independent complex second level of one Euler-deletion path. -/
noncomputable def eulerDeletionChronologicalSecondLimit (q : ℕ) (rho : ℂ) : ℂ :=
  ∑' n, chronologicalSecondTerm (eulerDeletionWeightedJump q rho) n

/-- Chronological second prefixes converge to the canonical complex second level. -/
theorem tendsto_chronologicalSecondPrefix_eulerDeletion_of_zeta_zero
    {q : ℕ} (hq : 0 < q) {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Tendsto (fun N => chronologicalSecondPrefix (eulerDeletionWeightedJump q rho) N)
      atTop (nhds (eulerDeletionChronologicalSecondLimit q rho)) := by
  have hsum := summable_chronologicalSecondTerm_eulerDeletion_of_zeta_zero
    hq hrhoHalf hrho1 hzeta
  simpa [chronologicalSecondPrefix, chronologicalSecondTerm,
    eulerDeletionChronologicalSecondLimit] using hsum.hasSum.tendsto_sum_nat

/-- The canonical complex level retains the strictly negative real energy shadow. -/
theorem eulerDeletionChronologicalSecondLimit_re_eq_neg_energy_half
    {q : ℕ} (hq : 0 < q) {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    (eulerDeletionChronologicalSecondLimit q rho).re =
      -eulerDeletionQuadraticEnergy q rho / 2 := by
  have hcomplex := tendsto_chronologicalSecondPrefix_eulerDeletion_of_zeta_zero
    hq hrhoHalf hrho1 hzeta
  have hre : Tendsto
      (fun N => (chronologicalSecondPrefix (eulerDeletionWeightedJump q rho) N).re)
      atTop (nhds (eulerDeletionChronologicalSecondLimit q rho).re) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp hcomplex using 1
    all_goals simp [Function.comp_def]
  exact tendsto_nhds_unique hre
    (tendsto_re_chronologicalSecondPrefix_eulerDeletion_of_zeta_zero
      hq hrhoHalf hrho1 hzeta)

/-- The cutoff-independent complex second level cannot vanish. -/
theorem eulerDeletionChronologicalSecondLimit_ne_zero
    {q : ℕ} (hq : 0 < q) {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    eulerDeletionChronologicalSecondLimit q rho ≠ 0 := by
  intro hzero
  have hre := eulerDeletionChronologicalSecondLimit_re_eq_neg_energy_half
    hq hrhoHalf hrho1 hzeta
  rw [hzero] at hre
  simp only [Complex.zero_re] at hre
  have henergy := eulerDeletionQuadraticEnergy_pos hq hrhoHalf
  linarith

/-! ## Ordered cross-modulus levels -/

/-- Every ordered cross-modulus summand has the same summable doubled-abscissa majorant. -/
theorem norm_chronologicalCrossTerm_eulerDeletion_le
    {q r : ℕ} (hr : 0 < r)
    {rho : ℂ} (hrhoRe : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) (n : ℕ) :
    ‖chronologicalCrossTerm (eulerDeletionWeightedJump q rho)
        (eulerDeletionWeightedJump r rho) n‖ ≤
      (eulerDeletionAbelTailConstant q rho * r) *
        ((n : ℝ) + 1) ^ (-2 * rho.re) := by
  have hpref := norm_eulerDeletionWeightedJump_prefix_le_of_zeta_zero
    q n hrhoRe hrho1 hzeta
  have hjump := norm_eulerDeletionWeightedJump_le hr rho n
  have hpow : (((n : ℝ) + 1) ^ (-rho.re)) ^ 2 =
      ((n : ℝ) + 1) ^ (-2 * rho.re) := by
    rw [pow_two, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [chronologicalCrossTerm, norm_mul, norm_star]
  calc
    ‖∑ i ∈ Finset.range n, eulerDeletionWeightedJump q rho i‖ *
          ‖eulerDeletionWeightedJump r rho n‖ ≤
        (eulerDeletionAbelTailConstant q rho * ((n : ℝ) + 1) ^ (-rho.re)) *
          ((r : ℝ) * ((n : ℝ) + 1) ^ (-rho.re)) := by
            exact mul_le_mul hpref hjump (norm_nonneg _)
              (le_trans (norm_nonneg _) hpref)
    _ = (eulerDeletionAbelTailConstant q rho * r) *
          ((n : ℝ) + 1) ^ (-2 * rho.re) := by rw [← hpow]; ring

/-- Ordered cross-modulus chronological levels are absolutely summable right of the half-line. -/
theorem summable_chronologicalCrossTerm_eulerDeletion_of_zeta_zero
    {q r : ℕ} (hr : 0 < r)
    {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Summable (chronologicalCrossTerm (eulerDeletionWeightedJump q rho)
      (eulerDeletionWeightedJump r rho)) := by
  have hrhoRe : 0 < rho.re := by linarith
  have hbase0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * rho.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * rho.re)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * rho.re)) 1).2 hbase0
  apply Summable.of_norm_bounded
    (hbase.mul_left (eulerDeletionAbelTailConstant q rho * r))
  exact norm_chronologicalCrossTerm_eulerDeletion_le hr hrhoRe hrho1 hzeta

/-- Canonical ordered cross-modulus chronological level. -/
noncomputable def eulerDeletionChronologicalCrossLimit
    (q r : ℕ) (rho : ℂ) : ℂ :=
  ∑' n, chronologicalCrossTerm (eulerDeletionWeightedJump q rho)
    (eulerDeletionWeightedJump r rho) n

/-- Ordinary chronological cutoffs converge to every canonical ordered cross-modulus level. -/
theorem tendsto_chronologicalCrossPrefix_eulerDeletion_of_zeta_zero
    {q r : ℕ} (hr : 0 < r)
    {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    Tendsto
      (fun N => chronologicalCrossPrefix (eulerDeletionWeightedJump q rho)
        (eulerDeletionWeightedJump r rho) N)
      atTop (nhds (eulerDeletionChronologicalCrossLimit q r rho)) := by
  have hsum := summable_chronologicalCrossTerm_eulerDeletion_of_zeta_zero
    (q := q) (r := r) hr hrhoHalf hrho1 hzeta
  simpa [chronologicalCrossPrefix, eulerDeletionChronologicalCrossLimit] using
    hsum.hasSum.tendsto_sum_nat

/-- Cross brackets of two deletion paths are absolutely summable right of the half-line. -/
theorem summable_crossBracket_eulerDeletion
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun n => eulerDeletionWeightedJump q s n *
      star (eulerDeletionWeightedJump r s n)) := by
  have hbase0 : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * s.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hbase : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-2 * s.re)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * s.re)) 1).2 hbase0
  apply Summable.of_norm_bounded (hbase.mul_left ((q : ℝ) * r))
  intro n
  have hqjump := norm_eulerDeletionWeightedJump_le hq s n
  have hrjump := norm_eulerDeletionWeightedJump_le hr s n
  have hpow : (((n : ℝ) + 1) ^ (-s.re)) ^ 2 =
      ((n : ℝ) + 1) ^ (-2 * s.re) := by
    rw [pow_two, ← Real.rpow_add (by positivity)]
    congr 1
    ring
  rw [norm_mul, norm_star]
  calc
    ‖eulerDeletionWeightedJump q s n‖ * ‖eulerDeletionWeightedJump r s n‖ ≤
        ((q : ℝ) * ((n : ℝ) + 1) ^ (-s.re)) *
          ((r : ℝ) * ((n : ℝ) + 1) ^ (-s.re)) := by
            exact mul_le_mul hqjump hrjump (norm_nonneg _)
              (mul_nonneg (by positivity) (Real.rpow_nonneg (by positivity) _))
    _ = ((q : ℝ) * r) * ((n : ℝ) + 1) ^ (-2 * s.re) := by rw [← hpow]; ring

/-- Canonical pointwise cross bracket of two weighted deletion paths. -/
noncomputable def eulerDeletionCrossBracketLimit (q r : ℕ) (s : ℂ) : ℂ :=
  ∑' n, eulerDeletionWeightedJump q s n * star (eulerDeletionWeightedJump r s n)

/-- Finite cross brackets converge to their canonical sum. -/
theorem tendsto_crossBracketPrefix_eulerDeletion
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    Tendsto (fun N => crossBracketPrefix (eulerDeletionWeightedJump q s)
      (eulerDeletionWeightedJump r s) N)
      atTop (nhds (eulerDeletionCrossBracketLimit q r s)) := by
  have hsum := summable_crossBracket_eulerDeletion hq hr hs
  simpa [crossBracketPrefix, eulerDeletionCrossBracketLimit] using
    hsum.hasSum.tendsto_sum_nat

/-- At a zeta zero, the canonical cross levels and bracket obey the exact polarized
quasi-shuffle relation. -/
theorem eulerDeletionCrossLimits_quasiShuffle_zero
    {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {rho : ℂ} (hrhoHalf : 1 / 2 < rho.re)
    (hrho1 : rho ≠ 1) (hzeta : riemannZeta rho = 0) :
    eulerDeletionChronologicalCrossLimit q r rho +
        star (eulerDeletionChronologicalCrossLimit r q rho) +
      eulerDeletionCrossBracketLimit q r rho = 0 := by
  have hrhoRe : 0 < rho.re := by linarith
  have hendq := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    q hrhoRe hrho1 hzeta
  have hendr := tendsto_eulerDeletionWeightedJump_prefix_of_zeta_zero
    r hrhoRe hrho1 hzeta
  have hleft : Tendsto
      (fun N =>
        (∑ n ∈ Finset.range N, eulerDeletionWeightedJump q rho n) *
          star (∑ n ∈ Finset.range N, eulerDeletionWeightedJump r rho n))
      atTop (nhds 0) := by
    simpa using hendq.mul hendr.star
  have hzero : Tendsto
      (fun N =>
        chronologicalCrossPrefix (eulerDeletionWeightedJump q rho)
            (eulerDeletionWeightedJump r rho) N +
          star (chronologicalCrossPrefix (eulerDeletionWeightedJump r rho)
            (eulerDeletionWeightedJump q rho) N) +
          crossBracketPrefix (eulerDeletionWeightedJump q rho)
            (eulerDeletionWeightedJump r rho) N)
      atTop (nhds 0) := by
    apply hleft.congr'
    exact Filter.Eventually.of_forall fun N =>
      endpoint_mul_star_endpoint_eq_cross_add_reverse_add_bracket
        (eulerDeletionWeightedJump q rho) (eulerDeletionWeightedJump r rho) N
  have hqr := tendsto_chronologicalCrossPrefix_eulerDeletion_of_zeta_zero
    (q := q) (r := r) hr hrhoHalf hrho1 hzeta
  have hrq := tendsto_chronologicalCrossPrefix_eulerDeletion_of_zeta_zero
    (q := r) (r := q) hq hrhoHalf hrho1 hzeta
  have hbracket := tendsto_crossBracketPrefix_eulerDeletion hq hr hrhoHalf
  have hsum := (hqr.add hrq.star).add hbracket
  exact tendsto_nhds_unique hsum hzero

end RHTower
