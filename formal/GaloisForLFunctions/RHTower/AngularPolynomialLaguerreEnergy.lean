import GaloisForLFunctions.RHTower.LaguerreInequality
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionProjectiveGaussRootRenewal

/-!
# Exact angular energy and real-root deletion transport

For an algebraic polynomial `Q`, evaluate it on the cosine circle. Integration by parts turns its
full-period angular kinetic energy into an exact signed radial-transport term plus the first
Laguerre form. If `Q` is real-rooted, the latter is the corpus sum-of-squares root-deletion density
and is pointwise and integrally nonnegative.

This is the finite exact identity needed to compare hard-edge Gauss-root geometry with Cayley
bandwidth. It uses the actual interval integral; no sampled or coefficient-only reporter is used.
-/

open MeasureTheory Polynomial Set
open scoped Interval

namespace HTGeometry

noncomputable section

/-- Number of roots outside the closed radius-`eta` window about `center`. -/
def multisetQuadraticOutlierCount (r : Multiset ℝ) (center eta : ℝ) : ℕ :=
  (r.filter fun x => eta ≤ |x - center|).card

/-- **Finite quadratic concentration law.** Every root outside radius `eta` spends at least
`eta²` of centered quadratic spread. -/
theorem sq_mul_multisetQuadraticOutlierCount_le_centeredSum
    (r : Multiset ℝ) (center eta : ℝ) (heta : 0 ≤ eta) :
    eta ^ 2 * (multisetQuadraticOutlierCount r center eta : ℝ) ≤
      (r.map fun x => (x - center) ^ 2).sum := by
  classical
  induction r using Multiset.induction_on with
  | empty => simp [multisetQuadraticOutlierCount]
  | @cons a r ih =>
      by_cases ha : eta ≤ |a - center|
      · have hsq : eta ^ 2 ≤ (a - center) ^ 2 := by
          nlinarith [sq_nonneg (|a - center| - eta), sq_abs (a - center)]
        have ih' : eta ^ 2 * (multisetQuadraticOutlierCount r center eta : ℝ) ≤
            (r.map fun x => (x - center) ^ 2).sum := ih
        simp [multisetQuadraticOutlierCount, ha]
        dsimp only [multisetQuadraticOutlierCount] at ih'
        nlinarith
      · simp [multisetQuadraticOutlierCount, ha]
        have hsquare : 0 ≤ (a - center) ^ 2 := sq_nonneg _
        exact ih.trans (le_add_of_nonneg_left hsquare)

/-- Centering at the empirical mean converts the centered square sum exactly into
`multisetQuadraticSpread`. -/
theorem multiset_sum_centered_sq_eq_quadraticSpread
    (r : Multiset ℝ) (n : ℕ) (hcard : r.card = n) (hn : 0 < n) :
    (r.map fun x => (x - r.sum / (n : ℝ)) ^ 2).sum = multisetQuadraticSpread r n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsum : (r.map fun x => (x - r.sum / (n : ℝ)) ^ 2).sum =
      (r.map fun x => x ^ 2).sum -
        2 * (r.sum / (n : ℝ)) * r.sum +
          (n : ℝ) * (r.sum / (n : ℝ)) ^ 2 := by
    simp_rw [show ∀ x : ℝ, (x - r.sum / (n : ℝ)) ^ 2 =
        x ^ 2 + (-2 * (r.sum / (n : ℝ))) * x +
          (r.sum / (n : ℝ)) ^ 2 by
      intro x
      ring]
    rw [Multiset.sum_map_add, Multiset.sum_map_add,
      Multiset.sum_map_mul_left]
    simp [hcard]
    ring
  rw [hsum]
  unfold multisetQuadraticSpread
  field_simp [hn0]
  ring

/-- **Spread-to-outlier budget.** At the empirical center, projective root spread bounds every
concentration-window outlier count with the sharp quadratic price `eta²`. -/
theorem sq_mul_multisetQuadraticOutlierCount_le_quadraticSpread
    (r : Multiset ℝ) (n : ℕ) (eta : ℝ)
    (hcard : r.card = n) (hn : 0 < n) (heta : 0 ≤ eta) :
    eta ^ 2 *
        (multisetQuadraticOutlierCount r (r.sum / (n : ℝ)) eta : ℝ) ≤
      multisetQuadraticSpread r n := by
  rw [← multiset_sum_centered_sq_eq_quadraticSpread r n hcard hn]
  exact sq_mul_multisetQuadraticOutlierCount_le_centeredSum
    r (r.sum / (n : ℝ)) eta heta

end

end HTGeometry

namespace RHTower

noncomputable section

/-- Evaluation of an algebraic polynomial on the cosine circle. -/
def angularPolynomialEval (Q : Polynomial ℝ) (theta : ℝ) : ℝ :=
  Polynomial.aeval (Real.cos theta) Q

/-- Exact angular derivative of `angularPolynomialEval`. -/
def angularPolynomialVelocity (Q : Polynomial ℝ) (theta : ℝ) : ℝ :=
  -Real.sin theta * Polynomial.aeval (Real.cos theta) Q.derivative

/-- Exact second angular derivative of `angularPolynomialEval`. -/
def angularPolynomialAcceleration (Q : Polynomial ℝ) (theta : ℝ) : ℝ :=
  -Real.cos theta * Polynomial.aeval (Real.cos theta) Q.derivative +
    Real.sin theta ^ 2 * Polynomial.aeval (Real.cos theta) Q.derivative.derivative

/-- First derivative law for cosine-circle polynomial evaluation. -/
theorem hasDerivAt_angularPolynomialEval (Q : Polynomial ℝ) (theta : ℝ) :
    HasDerivAt (angularPolynomialEval Q) (angularPolynomialVelocity Q theta) theta := by
  have h := (Polynomial.hasDerivAt_aeval (𝕜 := ℝ) Q (Real.cos theta)).comp theta
    (Real.hasDerivAt_cos theta)
  unfold angularPolynomialEval angularPolynomialVelocity
  convert h using 1 <;> first | apply Subsingleton.elim | ring | rfl

/-- Second derivative law for cosine-circle polynomial evaluation. -/
theorem hasDerivAt_angularPolynomialVelocity (Q : Polynomial ℝ) (theta : ℝ) :
    HasDerivAt (angularPolynomialVelocity Q) (angularPolynomialAcceleration Q theta) theta := by
  have hsin : HasDerivAt (fun t : ℝ => -Real.sin t) (-Real.cos theta) theta :=
    Real.hasDerivAt_sin theta |>.neg
  have hpoly : HasDerivAt
      (fun t : ℝ => Polynomial.aeval (Real.cos t) Q.derivative)
      (-Real.sin theta * Polynomial.aeval (Real.cos theta) Q.derivative.derivative) theta := by
    have h := (Polynomial.hasDerivAt_aeval (𝕜 := ℝ) Q.derivative (Real.cos theta)).comp theta
      (Real.hasDerivAt_cos theta)
    convert h using 1 <;> first | apply Subsingleton.elim | ring | rfl
  change HasDerivAt
    (fun t : ℝ => -Real.sin t * Polynomial.aeval (Real.cos t) Q.derivative)
    (-Real.cos theta * Polynomial.aeval (Real.cos theta) Q.derivative +
      Real.sin theta ^ 2 * Polynomial.aeval (Real.cos theta) Q.derivative.derivative) theta
  convert hsin.mul hpoly using 1 <;> first | apply Subsingleton.elim | ext <;> rfl | ring

/-- Full-period integration by parts has no endpoint term because angular velocity vanishes at
`±π`. -/
theorem integral_angularPolynomialVelocity_sq_eq_neg_eval_mul_acceleration
    (Q : Polynomial ℝ) :
    (∫ theta in (-Real.pi)..Real.pi, angularPolynomialVelocity Q theta ^ 2) =
      -∫ theta in (-Real.pi)..Real.pi,
        angularPolynomialEval Q theta * angularPolynomialAcceleration Q theta := by
  have hq : ∀ theta ∈ Set.uIcc (-Real.pi) Real.pi,
      HasDerivAt (angularPolynomialEval Q) (angularPolynomialVelocity Q theta) theta :=
    fun theta _ => hasDerivAt_angularPolynomialEval Q theta
  have hv : ∀ theta ∈ Set.uIcc (-Real.pi) Real.pi,
      HasDerivAt (angularPolynomialVelocity Q) (angularPolynomialAcceleration Q theta) theta :=
    fun theta _ => hasDerivAt_angularPolynomialVelocity Q theta
  have hqint : IntervalIntegrable (angularPolynomialVelocity Q) volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold angularPolynomialVelocity
    fun_prop
  have hvint : IntervalIntegrable (angularPolynomialAcceleration Q) volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    unfold angularPolynomialAcceleration
    fun_prop
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hq hv hqint hvint
  have hend : angularPolynomialVelocity Q Real.pi = 0 ∧
      angularPolynomialVelocity Q (-Real.pi) = 0 := by
    simp [angularPolynomialVelocity]
  rw [hend.1, hend.2, mul_zero, mul_zero, sub_zero] at hibp
  have hvelcont : Continuous (angularPolynomialVelocity Q) := by
    unfold angularPolynomialVelocity
    fun_prop
  have hqcont : Continuous (angularPolynomialEval Q) := by
    unfold angularPolynomialEval
    fun_prop
  have hacccont : Continuous (angularPolynomialAcceleration Q) := by
    unfold angularPolynomialAcceleration
    fun_prop
  have hvelsqint : IntervalIntegrable
      (fun x => angularPolynomialVelocity Q x * angularPolynomialVelocity Q x)
      volume (-Real.pi) Real.pi := by
    change IntervalIntegrable
      (angularPolynomialVelocity Q * angularPolynomialVelocity Q)
      volume (-Real.pi) Real.pi
    exact (hvelcont.mul hvelcont).intervalIntegrable (-Real.pi) Real.pi
  have hqaccint : IntervalIntegrable
      (fun x => angularPolynomialEval Q x * angularPolynomialAcceleration Q x)
      volume (-Real.pi) Real.pi := by
    change IntervalIntegrable
      (angularPolynomialEval Q * angularPolynomialAcceleration Q)
      volume (-Real.pi) Real.pi
    exact (hqcont.mul hacccont).intervalIntegrable (-Real.pi) Real.pi
  rw [intervalIntegral.integral_add hvelsqint hqaccint] at hibp
  simp only [← pow_two] at hibp
  linarith

/-- **Exact angular Laguerre transport identity.** Twice angular kinetic energy is signed radial
transport plus integrated first-Laguerre root-deletion density. -/
theorem angularPolynomialEnergy_eq_transport_add_laguerre (Q : Polynomial ℝ) :
    2 * (∫ theta in (-Real.pi)..Real.pi, angularPolynomialVelocity Q theta ^ 2) =
      ∫ theta in (-Real.pi)..Real.pi,
        Real.cos theta * Polynomial.aeval (Real.cos theta) Q *
          Polynomial.aeval (Real.cos theta) Q.derivative +
          Real.sin theta ^ 2 *
            (laguerreL1 Q).eval (Real.cos theta) := by
  have hibp := integral_angularPolynomialVelocity_sq_eq_neg_eval_mul_acceleration Q
  have hcongr : (fun theta : ℝ =>
      Real.cos theta * Polynomial.aeval (Real.cos theta) Q *
          Polynomial.aeval (Real.cos theta) Q.derivative +
        Real.sin theta ^ 2 *
          (laguerreL1 Q).eval (Real.cos theta)) =
      fun theta =>
        angularPolynomialVelocity Q theta ^ 2 -
          Polynomial.aeval (Real.cos theta) Q * angularPolynomialAcceleration Q theta := by
    funext theta
    simp [laguerreL1, angularPolynomialVelocity, angularPolynomialAcceleration]
    ring
  rw [hcongr, intervalIntegral.integral_sub]
  · unfold angularPolynomialEval at hibp
    linarith
  · apply Continuous.intervalIntegrable
    unfold angularPolynomialVelocity
    fun_prop
  · apply Continuous.intervalIntegrable
    unfold angularPolynomialAcceleration
    fun_prop

/-- Real-rootedness turns the angular Laguerre contribution into a pointwise nonnegative
root-deletion density. -/
theorem angularPolynomialLaguerreDensity_nonneg {Q : Polynomial ℝ}
    (hQ : Q.Splits) (theta : ℝ) :
    0 ≤ Real.sin theta ^ 2 *
      (laguerreL1 Q).eval (Real.cos theta) := by
  apply mul_nonneg (sq_nonneg _)
  exact laguerreL1_eval_nonneg hQ (Real.cos theta)

/-- Integrated real-root deletion energy is nonnegative on one complete angular period. -/
theorem integral_angularPolynomialLaguerreDensity_nonneg {Q : Polynomial ℝ}
    (hQ : Q.Splits) :
    0 ≤ ∫ theta in (-Real.pi)..Real.pi,
      Real.sin theta ^ 2 *
        (laguerreL1 Q).eval (Real.cos theta) := by
  apply intervalIntegral.integral_nonneg (by linarith [Real.pi_pos])
  intro theta _
  exact angularPolynomialLaguerreDensity_nonneg hQ theta

/-- For a real-rooted polynomial, angular kinetic energy dominates its signed radial transport.
The gap is exactly the nonnegative integrated root-deletion density above. -/
theorem integral_angularPolynomialTransport_le_two_energy {Q : Polynomial ℝ}
    (hQ : Q.Splits) :
    (∫ theta in (-Real.pi)..Real.pi,
      Real.cos theta * Polynomial.aeval (Real.cos theta) Q *
        Polynomial.aeval (Real.cos theta) Q.derivative) ≤
      2 * (∫ theta in (-Real.pi)..Real.pi,
        angularPolynomialVelocity Q theta ^ 2) := by
  have hid := angularPolynomialEnergy_eq_transport_add_laguerre Q
  have hnonneg := integral_angularPolynomialLaguerreDensity_nonneg hQ
  have hsplit :
      (∫ theta in (-Real.pi)..Real.pi,
        Real.cos theta * Polynomial.aeval (Real.cos theta) Q *
            Polynomial.aeval (Real.cos theta) Q.derivative +
          Real.sin theta ^ 2 *
            (laguerreL1 Q).eval (Real.cos theta)) =
        (∫ theta in (-Real.pi)..Real.pi,
          Real.cos theta * Polynomial.aeval (Real.cos theta) Q *
            Polynomial.aeval (Real.cos theta) Q.derivative) +
        ∫ theta in (-Real.pi)..Real.pi,
          Real.sin theta ^ 2 *
            (laguerreL1 Q).eval (Real.cos theta) := by
    rw [intervalIntegral.integral_add]
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
  rw [hsplit] at hid
  linarith

namespace XiShiftedCanonicalAdmission

/-- Number of current Gauss roots outside hard radius `eta` about their empirical center. -/
def projectiveGaussRootOutlierCount (s : ℕ → ℝ) (n : ℕ) (eta : ℝ) : ℕ :=
  let roots := (HTGeometry.monicOrtho s n).roots
  HTGeometry.multisetQuadraticOutlierCount roots (roots.sum / (n : ℝ)) eta

/-- Current projective Gauss-root spread pays the sharp quadratic price for every outlier. -/
theorem sq_mul_projectiveGaussRootOutlierCount_le_spread
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) (eta : ℝ) (heta : 0 ≤ eta) :
    eta ^ 2 * (projectiveGaussRootOutlierCount s n eta : ℝ) ≤
      projectiveGaussRootSpread s n := by
  have hsplit : (HTGeometry.monicOrtho s n).Splits := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (by omega : 0 < n))
    simpa only using HTGeometry.monicOrtho_splits_below h (n := k) hnN
  have hcard : (HTGeometry.monicOrtho s n).roots.card = n := by
    rw [← hsplit.natDegree_eq_card_roots]
    exact HTGeometry.natDegree_monicOrtho_eq s n
  exact HTGeometry.sq_mul_multisetQuadraticOutlierCount_le_quadraticSpread
    (HTGeometry.monicOrtho s n).roots n eta hcard (by omega) heta

/-- **Arithmetic outlier budget.** Retained source inventory funds every root outside a chosen
concentration window at exact price `2(2n+1) eta²`. This converts the nonlinear arithmetic source
account into the constrained-zero parameter required by root-sensitive Bernstein laws. -/
theorem projectiveGaussRootOutlierWork_le_retainedInventory
    {s : ℕ → ℝ} {N n : ℕ} (h : HTGeometry.PositiveMomentFormBelow s N)
    (hn : 2 ≤ n) (hnN : n < N) (eta : ℝ) (heta : 0 ≤ eta) :
    2 * (2 * n + 1 : ℝ) * eta ^ 2 *
        (projectiveGaussRootOutlierCount s n eta : ℝ) ≤
      projectiveJacobiRetainedInventory s n := by
  have hout := sq_mul_projectiveGaussRootOutlierCount_le_spread h hn hnN eta heta
  have hpart := rootSpread_part_le_projectiveJacobiRetainedInventory h hn hnN
  have hc : 0 ≤ 2 * (2 * n + 1 : ℝ) := by positivity
  nlinarith

end XiShiftedCanonicalAdmission

end

end RHTower
