import GaloisForLFunctions.ArithmeticEffectivityTheory.TheBaseDoesNotExtend
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHorizonTorsion
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The polar box count and its twist by the prime nodes

The section counts proposed for the scaling surface (AOT, ACS) count degrees of freedom of a polar
box and subtract conditions at the prime-power nodes. In the effectivity calculus they separate
into two scales.

* **The polar box count is the level bound** (`polarBoxCount_eq_levelBound`). The box class
  `√N · A` has degree `t = 2√N` and Euler characteristic `N = (t/2)²` (`polarBoxCount_boxClass`).
  As a function of the degree, `(t/2)²` is the maximum of the Euler characteristic on the degree
  level under the Hodge index. It is an effectivity function iff the Hodge index holds
  (`riemannInequality_polarBoxCount_iff`); on the scaling surface of `ℤ`, iff RH.
* **The node twist** (`nodeBoxCount`, `nodeBoxCount_boxClass`). Subtracting the prime-power node
  conditions gives `(t/2)² − ψ((t/2)²)`; on the box class it is `N − log |ℤ/lcm(1..N)ℤ|`, integer
  degree minus log-torsion.
* **The node twist destroys Hilbert–Samuel** (`not_riemannInequality_nodeBoxCount`). On every polar
  surface and for every canonical class the node-twisted count violates the Riemann inequality:
  Chebyshev's bound `ψ(x) ≥ (x − 1) log 2 − log(x + 2)` removes a fraction `log 2 > ½` of the box,
  so along `nA` the count grows like `2(1 − log 2) n² < n²`.

So the abundance lives on the untwisted count, where it is the Hodge index, and the arithmetic of
the nodes lives on the twisted one, where by E4 RH is the statement that it is
`O(√N log² N)` — the square root of the box's Euler characteristic.
-/

noncomputable section

open Filter Real

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- The **polar box count** `(t/2)²` of a class of degree `t`. -/
def polarBoxCount (t : ℝ) : ℝ := (t / 2) ^ 2

theorem polarBoxCount_eq_levelBound (t : ℝ) : polarBoxCount t = levelBound 0 0 0 t := by
  simp only [polarBoxCount, levelBound]; ring

theorem pair_boxClass_ample (N : ℕ) : S.pair (boxClass S N) S.ample = 2 * Real.sqrt N := by
  rw [boxClass, pair_smul_ample, S.pair_ample_ample]; ring

/-- The polar box count of the box class is its Euler characteristic `N`. -/
theorem polarBoxCount_boxClass (N : ℕ) : polarBoxCount (S.pair (boxClass S N) S.ample) = N := by
  rw [pair_boxClass_ample, polarBoxCount, mul_div_cancel_left₀ _ two_ne_zero,
    Real.sq_sqrt (Nat.cast_nonneg N)]

/-- **The polar box count is an effectivity function iff the Hodge index holds.** -/
theorem riemannInequality_polarBoxCount_iff :
    RiemannInequality S 0 0 (fun x => max 0 (polarBoxCount (S.pair x S.ample))) ↔ S.HodgeIndex := by
  have hκ : (0 : ℝ) • S.H + (0 : ℝ) • S.V = 0 := by simp
  constructor
  · intro hRI
    exact (exists_degree_effectivity_iff_hodgeIndex S 0 0 0).mp
      ⟨fun t => max 0 (polarBoxCount t), by rw [hκ]; exact hRI⟩
  · intro hH x
    have h := eulerChar_le_levelBound S hH 0 0 0 (x := x) rfl
    rw [hκ, ← polarBoxCount_eq_levelBound] at h
    exact (le_max_of_le_right h).trans (le_add_of_nonneg_right (le_max_left _ _))

/-- **On the scaling surface of `ℤ`** the polar box count is an effectivity function iff RH. -/
theorem riemannHypothesis_iff_riemannInequality_polarBoxCount :
    RiemannHypothesis ↔ RiemannInequality scalingSurface 0 0
      (fun x => max 0 (polarBoxCount (scalingSurface.pair x scalingSurface.ample))) := by
  rw [riemannInequality_polarBoxCount_iff, scalingSurface_hodgeIndex_iff]

/-- The **node-twisted box count**: degrees of freedom minus the log-torsion of the nodes. -/
def nodeBoxCount (t : ℝ) : ℝ := polarBoxCount t - Chebyshev.psi (polarBoxCount t)

/-- On the box class the node twist is integer degree minus log-torsion. -/
theorem nodeBoxCount_boxClass (N : ℕ) :
    nodeBoxCount (S.pair (boxClass S N) S.ample) = N - logTorsion N := by
  rw [nodeBoxCount, polarBoxCount_boxClass, logTorsion_eq_psi]

/-- `log y ≤ 2 √y` for `y > 0`. -/
theorem log_le_two_mul_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hy)
  rw [Real.log_sqrt hy.le] at h
  linarith [Real.sqrt_nonneg y]

/-- **Chebyshev's bound on the node twist**:
`max(0, (t/2)² − ψ((t/2)²)) ≤ (1 − log 2)(t/2)² + log 2 + |t| + 4`. -/
theorem max_nodeBoxCount_le (t : ℝ) :
    max 0 (nodeBoxCount t) ≤ (1 - Real.log 2) * (t / 2) ^ 2 + Real.log 2 + |t| + 4 := by
  have hp : 0 ≤ polarBoxCount t := sq_nonneg _
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hψ := Chebyshev.psi_ge' hp
  have hlog := log_le_two_mul_sqrt (by linarith : 0 < polarBoxCount t + 2)
  have hsqrt : Real.sqrt (polarBoxCount t + 2) ≤ |t| / 2 + 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : polarBoxCount t = (|t| / 2) ^ 2 := by rw [polarBoxCount, div_pow, div_pow, sq_abs]
    rw [this]; nlinarith [abs_nonneg t]
  refine max_le (by nlinarith [sq_nonneg (t / 2), abs_nonneg t]) ?_
  rw [nodeBoxCount]
  have : polarBoxCount t = (t / 2) ^ 2 := rfl
  nlinarith

/-- **The node twist destroys Hilbert–Samuel.** On every polar surface, for every canonical class
and constant, the node-twisted box count violates the Riemann inequality. -/
theorem not_riemannInequality_nodeBoxCount (κ : E) (χ₀ : ℝ) :
    ¬ RiemannInequality S κ χ₀ (fun x => max 0 (nodeBoxCount (S.pair x S.ample))) := by
  intro hRI
  set k := S.pair κ S.ample
  set L := Real.log 2
  have hL : 0.6931471803 < L := Real.log_two_gt_d9
  have hL1 : L < 1 := by linarith [Real.log_two_lt_d9]
  obtain ⟨n, hn1, hn2⟩ := ((hilbertSamuel_of_riemannInequality S hRI
    (by norm_num : (4 / 5 : ℝ) < 1)).and (eventually_affine_lt_quadratic
      (by norm_num : (0 : ℝ) < 4 / 25) ((1 - L) * |k| + 4)
      ((1 - L) * k ^ 2 / 4 + 2 * L + |k| + 8))).exists
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : S.pair ((n : ℝ) • S.ample) S.ample = 2 * n := by
    rw [pair_smul_ample, S.pair_ample_ample]; ring
  have e2 : S.pair (κ - (n : ℝ) • S.ample) S.ample = k - 2 * n := by
    rw [map_sub, LinearMap.sub_apply, e1]
  simp only [e1, e2] at hn1
  have b1 := max_nodeBoxCount_le (2 * n)
  have b2 := max_nodeBoxCount_le (k - 2 * n)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * n)] at b1
  have habs : |k - 2 * n| ≤ |k| + 2 * n := by
    have := abs_sub_le k 0 (2 * n)
    rwa [sub_zero, zero_sub, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * n)] at this
  have hk : -(k * n) ≤ |k| * n := by nlinarith [neg_abs_le k]
  nlinarith [sq_nonneg (n : ℝ), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - L) (sq_nonneg k),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - L) hn0,
    mul_le_mul_of_nonneg_left hk (by linarith : (0 : ℝ) ≤ 1 - L)]

end GaloisForLFunctions.ArithmeticEffectivityTheory
