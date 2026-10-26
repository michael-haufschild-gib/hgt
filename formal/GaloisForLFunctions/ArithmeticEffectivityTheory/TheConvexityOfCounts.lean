import GaloisForLFunctions.ArithmeticEffectivityTheory.TatesLimitLaw

/-!
# The convexity of counts: a second source of positivity

Counting produces positivity in two ways. A cardinality is nonnegative (the product formula; a
naive height, `TatesLimitLaw`). A **log-count** `h(J) = log Σ_i w_i e^{a_i J}` with weights
`w_i ≥ 0` is midpoint convex, `h(J + J′) + h(J − J′) ≥ 2 h(J)` — Cauchy–Schwarz for the counting
measure (`logCount_midpoint_convex`). Either property forces the quadratic part to be positive.

* **Convexity forces positivity** (`tateLimit_nonneg_of_midpointConvex`). If `h` on an abelian
  group satisfies an approximate parallelogram law and is midpoint convex, its Tate limit `q` is
  nonnegative: in the limit `q(x + y) + q(x − y) ≥ 2 q(x)`, and the exact parallelogram law turns
  this into `2 q(y) ≥ 0`. No lower bound on `h` is used.
* **The fifth currency** (`orbitHodgeIndex_iff_exists_convexHeight`). On a scaling datum, Rosati
  positivity at a cycle is the existence of a midpoint-convex function on `ℤ[G]` at bounded
  distance from the integral Rosati form. For `ζ`: RH iff every cycle has one
  (`riemannHypothesis_iff_forall_exists_convexHeight`).

Log-counts of nonnegative weights are convex for free, on every datum: convexity, like the
nonnegativity of cardinalities, is soft. The content is that Weil's form be the quadratic part of a
log-count attached to the arithmetic.
-/

noncomputable section

open Filter Topology Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- **Cauchy–Schwarz for counts**: `F(J + J′) F(J − J′) ≥ F(J)²` for `F(J) = Σ_i w_i e^{a_i J}`,
`w ≥ 0`. -/
theorem count_mul_count_ge_sq {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (a : ι → ℝ) (J J' : ℝ) :
    (∑ i ∈ s, w i * Real.exp (a i * J)) ^ 2 ≤
      (∑ i ∈ s, w i * Real.exp (a i * (J + J'))) * ∑ i ∈ s, w i * Real.exp (a i * (J - J')) := by
  have key : ∀ i, w i * Real.exp (a i * J) =
      Real.sqrt (w i * Real.exp (a i * (J + J'))) * Real.sqrt (w i * Real.exp (a i * (J - J'))) := by
    intro i
    rw [← Real.sqrt_mul (mul_nonneg (hw i) (Real.exp_pos _).le),
      show w i * Real.exp (a i * (J + J')) * (w i * Real.exp (a i * (J - J'))) =
        (w i * Real.exp (a i * J)) ^ 2 by
        rw [mul_pow, ← Real.exp_nat_mul, mul_mul_mul_comm, ← Real.exp_add]; ring_nf,
      Real.sqrt_sq (mul_nonneg (hw i) (Real.exp_pos _).le)]
  simp_rw [key]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i * Real.exp (a i * (J + J'))))
    (fun i => Real.sqrt (w i * Real.exp (a i * (J - J'))))
  simp only [Real.sq_sqrt (mul_nonneg (hw _) (Real.exp_pos _).le)] at hcs
  exact hcs

/-- **Log-counts are midpoint convex.** -/
theorem logCount_midpoint_convex {ι : Type*} (s : Finset ι) {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    (a : ι → ℝ) (hpos : ∀ J, 0 < ∑ i ∈ s, w i * Real.exp (a i * J)) (J J' : ℝ) :
    2 * Real.log (∑ i ∈ s, w i * Real.exp (a i * J)) ≤
      Real.log (∑ i ∈ s, w i * Real.exp (a i * (J + J'))) +
        Real.log (∑ i ∈ s, w i * Real.exp (a i * (J - J'))) := by
  have h := Real.log_le_log (pow_pos (hpos J) 2) (count_mul_count_ge_sq s hw a J J')
  rw [Real.log_pow, Real.log_mul (hpos _).ne' (hpos _).ne'] at h
  push_cast at h
  exact h

section Convexity

variable {M : Type*} [AddCommGroup M]

/-- **Convexity forces positivity.** A midpoint-convex function with an approximate parallelogram
law has a nonnegative Tate limit. -/
theorem tateLimit_nonneg_of_midpointConvex {h : M → ℝ} {B : ℝ}
    (hP : ∀ x y, |h (x + y) + h (x - y) - 2 * h x - 2 * h y| ≤ B)
    (hconv : ∀ x y, 2 * h x ≤ h (x + y) + h (x - y)) (y : M) : 0 ≤ tateLimit h y := by
  have hC := abs_two_nsmul_sub_le_of_parallelogram hP
  have hpar := tateLimit_parallelogram hP 0 y
  have hlim := ((tendsto_tateSeq hC (0 + y)).add (tendsto_tateSeq hC (0 - y))).sub
    ((tendsto_tateSeq hC 0).const_mul 2)
  have hge : 0 ≤ tateLimit h (0 + y) + tateLimit h (0 - y) - 2 * tateLimit h 0 := by
    refine ge_of_tendsto' hlim fun n => ?_
    have := hconv ((2 ^ n : ℕ) • 0) ((2 ^ n : ℕ) • y)
    rw [← nsmul_add, ← nsmul_sub] at this
    simp only [tateSeq]
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    rw [show h ((2 ^ n : ℕ) • (0 + y)) / 4 ^ n + h ((2 ^ n : ℕ) • (0 - y)) / 4 ^ n -
        2 * (h ((2 ^ n : ℕ) • 0) / 4 ^ n) =
        (h ((2 ^ n : ℕ) • (0 + y)) + h ((2 ^ n : ℕ) • (0 - y)) - 2 * h ((2 ^ n : ℕ) • 0)) / 4 ^ n
        by ring]
    exact div_nonneg (by linarith) h4.le
  linarith

/-- A function homogeneous of degree two with the parallelogram law is nonnegative iff some
midpoint-convex function lies at bounded distance from it. -/
theorem exists_convexHeight_iff_nonneg {q : M → ℝ}
    (hq : ∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y)
    (hq2 : ∀ x, q (2 • x) = 4 * q x) :
    (∃ h : M → ℝ, ∃ B : ℝ, (∀ x y, 2 * h x ≤ h (x + y) + h (x - y)) ∧ ∀ x, |h x - q x| ≤ B) ↔
      ∀ x, 0 ≤ q x := by
  constructor
  · rintro ⟨h, B, hconv, hB⟩ y
    have hP : ∀ x y, |h (x + y) + h (x - y) - 2 * h x - 2 * h y| ≤ 6 * B := by
      intro x y
      have e := hq x y
      have h1 := abs_le.mp (hB (x + y)); have h2 := abs_le.mp (hB (x - y))
      have h3 := abs_le.mp (hB x); have h4 := abs_le.mp (hB y)
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
    have hC := abs_two_nsmul_sub_le_of_parallelogram hP
    have heq : tateLimit h = q := eq_of_two_nsmul_of_bounded (tateLimit_two_nsmul hC) hq2
      (abs_tateLimit_sub_le hC) (fun x => by rw [abs_sub_comm]; exact hB x)
    rw [← heq]
    exact tateLimit_nonneg_of_midpointConvex hP hconv y
  · intro hnn
    exact ⟨q, 0, fun x y => by rw [hq]; linarith [hnn y], fun x => by simp⟩

end Convexity

section IntegralRing

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ArithmeticOrientationGeometry.ScalingDatum G E)

/-- The integral Rosati form satisfies the parallelogram law. -/
theorem intRosatiForm_parallelogram (x : E) (ξ η : G →₀ ℤ) :
    intRosatiForm D x (ξ + η) + intRosatiForm D x (ξ - η) =
      2 * intRosatiForm D x ξ + 2 * intRosatiForm D x η := by
  classical
  set S := ξ.support ∪ η.support ∪ (ξ + η).support ∪ (ξ - η).support
  have hs : ∀ ζ : G →₀ ℤ, ζ.support ⊆ S → intRosatiForm D x ζ =
      ∑ g ∈ S, ∑ h ∈ S, (ζ g : ℝ) * ζ h * D.orbitCorr x (g - h) :=
    fun ζ hζ => intRosatiForm_eq_sum_of_subset D x ζ hζ
  rw [hs (ξ + η) (by intro g hg; simp [S, hg]), hs (ξ - η) (by intro g hg; simp [S, hg]),
    hs ξ (by intro g hg; simp [S, hg]), hs η (by intro g hg; simp [S, hg]), mul_sum, mul_sum,
    ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun g _ => ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun h _ => ?_
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Int.cast_add, Int.cast_sub]
  ring

theorem intRosatiForm_two_nsmul (x : E) (ξ : G →₀ ℤ) :
    intRosatiForm D x (2 • ξ) = 4 * intRosatiForm D x ξ := by
  rw [intRosatiForm_nsmul]; norm_num

/-- **Rosati positivity is a convex height** on the integral correspondence ring. -/
theorem orbitHodgeIndex_iff_exists_convexHeight (x : E) :
    D.OrbitHodgeIndex x ↔ ∃ h : (G →₀ ℤ) → ℝ, ∃ B : ℝ,
      (∀ ξ η, 2 * h ξ ≤ h (ξ + η) + h (ξ - η)) ∧ ∀ ξ, |h ξ - intRosatiForm D x ξ| ≤ B := by
  rw [orbitHodgeIndex_iff_int, IntOrbitHodgeIndex,
    exists_convexHeight_iff_nonneg (intRosatiForm_parallelogram D x) (intRosatiForm_two_nsmul D x)]

end IntegralRing

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri in
/-- **RH as convex heights.** -/
theorem riemannHypothesis_iff_forall_exists_convexHeight :
    RiemannHypothesis ↔ ∀ x : ScalingCycle, ∃ h : (ℝ →₀ ℤ) → ℝ, ∃ B : ℝ,
      (∀ ξ η, 2 * h ξ ≤ h (ξ + η) + h (ξ - η)) ∧
        ∀ ξ, |h ξ - intRosatiForm zetaScalingDatum x ξ| ≤ B :=
  (zetaScalingDatum_hodgeIndex_iff.symm.trans
    ((ArithmeticOrientationGeometry.ScalingDatum.hodgeIndex_tfae zetaScalingDatum).out 0 1)).trans
    (forall_congr' fun x => orbitHodgeIndex_iff_exists_convexHeight _ x)

end GaloisForLFunctions.ArithmeticEffectivityTheory
