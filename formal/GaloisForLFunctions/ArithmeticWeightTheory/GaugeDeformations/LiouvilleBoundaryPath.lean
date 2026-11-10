import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.InteriorPolePersistence
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.LocalZeroClassification
import GaloisForLFunctions.FiniteFreeProbability.JensenLocalHermiteBiehler

/-!
# A bounded analytic gauge path whose pole becomes a boundary zero

The prime phases exp(iπ z^p) have normally summable deviations on every
compact subdisk of the unit disk. Their real interior fibres retain a
nonzero pole at one, whereas the endpoint is Liouville and has a simple
zero. Prime derivatives at the endpoint exclude a common bound on any
complex neighborhood of that endpoint.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCorrelationGeometry
open GaloisForLFunctions.PrimeTorusTheory
open _root_.RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- Entire prime coordinates of the path from the trivial gauge to Liouville. -/
def liouvilleBoundaryPhase (p : Nat.Primes) (z : ℂ) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * I * z ^ (p : ℕ))

/-- The actual real gauge with prime phases exp(iπ t^p). -/
def liouvilleBoundaryGauge (t : ℝ) : GaugeTorus :=
  linearPhaseGauge (fun p => Real.pi * t ^ (p : ℕ)) 1

theorem liouvilleBoundaryPhase_zero (p : Nat.Primes) : liouvilleBoundaryPhase p 0 = 1 := by
  simp only [liouvilleBoundaryPhase, zero_pow p.2.ne_zero, mul_zero, Complex.exp_zero]

theorem liouvilleBoundaryPhase_one (p : Nat.Primes) : liouvilleBoundaryPhase p 1 = -1 := by
  simp only [liouvilleBoundaryPhase, one_pow, mul_one, Complex.exp_pi_mul_I]

theorem liouvilleBoundaryPhase_eq_twist (t : ℝ) (p : Nat.Primes) :
    liouvilleBoundaryPhase p (t : ℂ) = twist (liouvilleBoundaryGauge t) p := by
  rw [liouvilleBoundaryGauge, twist_linearPhaseGauge_prime]
  simp only [liouvilleBoundaryPhase, linearPrimePhase, ofReal_mul, ofReal_pow, ofReal_one, mul_one]
  congr 1
  ring

theorem differentiable_liouvilleBoundaryPhase (p : Nat.Primes) :
    Differentiable ℂ (liouvilleBoundaryPhase p) := by
  unfold liouvilleBoundaryPhase
  fun_prop

private theorem norm_boundary_exponent (p : Nat.Primes) (z : ℂ) :
    ‖(Real.pi : ℂ) * I * z ^ (p : ℕ)‖ = Real.pi * ‖z‖ ^ (p : ℕ) := by
  rw [norm_mul, norm_mul, norm_pow, norm_I, mul_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- All prime coordinates share one bound on the unit disk. -/
theorem norm_liouvilleBoundaryPhase_le (p : Nat.Primes) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖liouvilleBoundaryPhase p z‖ ≤ Real.exp Real.pi := by
  apply (Complex.norm_exp_le_exp_norm _).trans
  apply Real.exp_le_exp.mpr
  rw [norm_boundary_exponent]
  have hp : ‖z‖ ^ (p : ℕ) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
  nlinarith only [hp, Real.pi_pos]

/-- Geometric decay of the perturbation is uniform on each compact subdisk. -/
theorem norm_liouvilleBoundaryPhase_sub_one_le (p : Nat.Primes) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖liouvilleBoundaryPhase p z - 1‖ ≤
      (Real.pi * Real.exp Real.pi) * r ^ (p : ℕ) := by
  have hp : ‖z‖ ^ (p : ℕ) ≤ r ^ (p : ℕ) := pow_le_pow_left₀ (norm_nonneg z) hz _
  have hrp : r ^ (p : ℕ) ≤ 1 := pow_le_one₀ hr hr1
  have hn : ‖(Real.pi : ℂ) * I * z ^ (p : ℕ)‖ ≤ Real.pi * r ^ (p : ℕ) := by
    rw [norm_boundary_exponent]
    exact mul_le_mul_of_nonneg_left hp Real.pi_pos.le
  have hnπ : ‖(Real.pi : ℂ) * I * z ^ (p : ℕ)‖ ≤ Real.pi := by
    exact hn.trans (by nlinarith only [hrp, Real.pi_pos])
  have hh := FiniteFreeProbability.norm_exp_sub_one_le_mul_exp
    ((Real.pi : ℂ) * I * z ^ (p : ℕ))
  exact hh.trans ((mul_le_mul hn (Real.exp_le_exp.mpr hnπ) (Real.exp_pos _).le
    (by positivity)).trans_eq (by ring))

/-- Every compact subdisk has normal prime summability at the fixed exponent 3/4. -/
theorem liouvilleBoundary_normal_summability {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun p => primeDiskDeviation liouvilleBoundaryPhase r p * (p : ℝ) ^ (-(3 / 4 : ℝ))) := by
  have hb (p : Nat.Primes) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
      ‖liouvilleBoundaryPhase p z‖ ≤ Real.exp Real.pi :=
    norm_liouvilleBoundaryPhase_le p (by simpa only [mem_ball, dist_zero_right] using (show ‖z‖ < 1 by simpa using hz).le)
  have hsup (p : Nat.Primes) : primeDiskDeviation liouvilleBoundaryPhase r p ≤
      (Real.pi * Real.exp Real.pi) * r ^ (p : ℕ) := by
    apply csSup_le
    · exact ⟨_, ⟨0, mem_closedBall_self hr, rfl⟩⟩
    rintro b ⟨z, hz, rfl⟩
    exact norm_liouvilleBoundaryPhase_sub_one_le p hr hr1.le
      (by simpa only [mem_closedBall, dist_zero_right] using hz)
  have hgeom : Summable (fun p : Nat.Primes => r ^ (p : ℕ)) :=
    (summable_geometric_of_lt_one hr hr1).subtype Nat.Prime
  apply (hgeom.mul_left (Real.pi * Real.exp Real.pi)).of_nonneg_of_le
    (fun p => mul_nonneg (primeDiskDeviation_bounds hr hr1 hb p).1 (by positivity))
  intro p
  have hp : (p : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast p.2.one_le) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hp (primeDiskDeviation_bounds hr hr1 hb p).1).trans
    (by simpa only [mul_one] using hsup p)

/-- Every real interior fibre has a nonzero pole, realized by the canonical joint germ. -/
theorem liouvilleBoundary_interior_poles (t : ℝ) (ht : |t| < 1) :
    AnalyticAt ℂ (jointGaugeRegularization liouvilleBoundaryPhase) ((t : ℂ), 1) ∧
      jointGaugeRegularization liouvilleBoundaryPhase ((t : ℂ), 1) ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re →
        jointGaugeRegularization liouvilleBoundaryPhase ((t : ℂ), s) =
          (s - 1) * gaugeFibre (liouvilleBoundaryGauge t) s := by
  let r := (|t| + 1) / 2
  have htr : |t| < r := by dsimp [r]; linarith only [ht]
  have hr1 : r < 1 := by dsimp [r]; linarith only [ht]
  have hr : 0 < r := (abs_nonneg t).trans_lt htr
  obtain ⟨hW, hWne, he⟩ := joint_regularization_at_real_of_compact_normal
    htr hr1 (by norm_num : (1 / 2 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)
    (fun p => (differentiable_liouvilleBoundaryPhase p).differentiableOn)
    (fun p z hz => norm_liouvilleBoundaryPhase_le p
      (by simpa only [mem_ball, dist_zero_right] using (show ‖z‖ < 1 by simpa using hz).le))
    (fun a _ p => liouvilleBoundaryPhase_eq_twist a p)
    (liouvilleBoundary_normal_summability hr.le hr1)
  exact ⟨hW, hWne, he t ht⟩

/-- The endpoint fibre has an actual simple holomorphic zero at one. -/
theorem liouvilleBoundary_simple_zero :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G 1 ∧ G 1 = 0 ∧ deriv G 1 ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re → G s = gaugeFibre (liouvilleBoundaryGauge 1) s := by
  have hs : Summable (fun p : Nat.Primes => ‖twist (liouvilleBoundaryGauge 1) p + 1‖ *
      (p : ℝ) ^ (-(3 / 4 : ℝ))) := by
    simp only [← liouvilleBoundaryPhase_eq_twist, ofReal_one, liouvilleBoundaryPhase_one,
      neg_add_cancel, norm_zero, zero_mul]
    exact summable_zero
  let G := liouvilleContinuation (liouvilleBoundaryGauge 1)
  have hG : AnalyticAt ℂ G 1 := analyticAt_liouvilleContinuation_one
    (by norm_num : (1 / 2 : ℝ) ≤ 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1) hs
  have hG0 : G 1 = 0 := liouvilleContinuation_one _
  have he : ∀ s : ℂ, 1 < s.re → G s = gaugeFibre (liouvilleBoundaryGauge 1) s :=
    fun s hs => liouvilleContinuation_eq_gaugeFibre _ hs
  exact ⟨G, hG, hG0, deriv_ne_zero_of_local_gauge_zero hG hG0
    (Filter.Eventually.of_forall he), he⟩

/-- Endpoint derivatives grow linearly with the prime. -/
theorem norm_deriv_liouvilleBoundaryPhase_one (p : Nat.Primes) :
    ‖deriv (liouvilleBoundaryPhase p) 1‖ = Real.pi * (p : ℝ) := by
  have hd := (((hasDerivAt_id (1 : ℂ)).pow (p : ℕ)).const_mul ((Real.pi : ℂ) * I)).cexp
  have he := hd.deriv
  change deriv (liouvilleBoundaryPhase p) 1 = _ at he
  rw [he]
  simp only [Pi.pow_apply, id_eq, one_pow, mul_one, Complex.exp_pi_mul_I,
    neg_one_mul, norm_neg, norm_mul, norm_I, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_natCast, mul_one]

/-- No complex neighborhood of the endpoint admits a prime-uniform bound. -/
theorem liouvilleBoundary_no_uniform_bound_at_one (ε : ℝ) (hε : 0 < ε) :
    ¬ ∃ M : ℝ, ∀ p z, z ∈ ball (1 : ℂ) ε → ‖liouvilleBoundaryPhase p z‖ ≤ M := by
  rintro ⟨M, hb⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 * M / ε) / Real.pi)
  obtain ⟨n, hNn, hn⟩ := Nat.exists_infinite_primes N
  let p : Nat.Primes := ⟨n, hn⟩
  have hder := Bottcher.norm_deriv_le_of_bounded_on_ball hε
    (differentiable_liouvilleBoundaryPhase p).differentiableOn (hb p) 1
    (mem_ball_self (by positivity))
  rw [norm_deriv_liouvilleBoundaryPhase_one] at hder
  have hNp : (N : ℝ) ≤ (p : ℝ) := by exact_mod_cast hNn
  have hlt : 2 * M / ε < (N : ℝ) * Real.pi := (div_lt_iff₀ Real.pi_pos).mp hN
  have hle := mul_le_mul_of_nonneg_right hNp Real.pi_pos.le
  nlinarith only [hder, hlt, hle]

#print axioms liouvilleBoundary_interior_poles
#print axioms liouvilleBoundary_simple_zero
#print axioms liouvilleBoundary_no_uniform_bound_at_one

end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
