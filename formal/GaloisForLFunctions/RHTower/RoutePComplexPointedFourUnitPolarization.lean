import GaloisForLFunctions.RHTower.RoutePPointedFourUnitTransverseReporter
import GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHermitianGram

/-!
# Route P: complex pointed four-unit polarization

P-G166 identifies the full-Euler transverse Fisher vector as an exact four-unit source for
pointed continued-Xi variation on the real inward ray.  This file complexifies the actual damped
Euler state before scalar observation.  Imaginary node motion is a unitary logarithmic phase, so
the same transverse source produces a genuine non-diagonal Hilbert Gram at no additional norm
cost.

No Xi zero, target interpolation polynomial, or RH premise enters the construction.
-/

open Complex Filter Set
open scoped BigOperators Topology ComplexOrder

namespace RHTower

noncomputable section

/-- Complex affine boundary point used by the full-Euler inward source. -/
def eulerPositiveComplexBoundaryParameter (sigma : ℝ) (u : ℂ) : ℂ :=
  (sigma : ℂ) + u * ((sigma - 1 : ℝ) : ℂ)

theorem one_lt_eulerPositiveComplexBoundaryParameter_re
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    1 < (eulerPositiveComplexBoundaryParameter sigma u).re := by
  simp only [eulerPositiveComplexBoundaryParameter, add_re, mul_re,
    ofReal_re, ofReal_im, mul_zero, sub_zero]
  nlinarith

/-- Full-Euler inward state with real damping and unitary logarithmic ordinate phase. -/
def eulerPositiveCriticalComplexDampedStateWeight
    (sigma : ℝ) (u : ℂ) (n : ℕ+) : ℂ :=
  Complex.exp
      (-((u.im * (sigma - 1) * Real.log (n : ℕ) : ℝ) : ℂ) * I) *
    eulerPositiveCriticalDampedStateWeight sigma u.re n

theorem eulerPositiveCriticalComplexDampedStateWeight_eq_exp
    (sigma : ℝ) (u : ℂ) (n : ℕ+) :
    eulerPositiveCriticalComplexDampedStateWeight sigma u n =
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        eulerPositiveStateWeight sigma n := by
  rw [eulerPositiveCriticalComplexDampedStateWeight,
    eulerPositiveCriticalDampedStateWeight,
    eulerPositiveCriticalDamping, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add]
  congr 2
  apply Complex.ext <;> simp
  all_goals ring

theorem norm_eulerPositiveCriticalComplexDampedStateWeight
    (sigma : ℝ) (u : ℂ) (n : ℕ+) :
    ‖eulerPositiveCriticalComplexDampedStateWeight sigma u n‖ =
      ‖eulerPositiveCriticalDampedStateWeight sigma u.re n‖ := by
  rw [eulerPositiveCriticalComplexDampedStateWeight, norm_mul]
  rw [show
      -((u.im * (sigma - 1) * Real.log (n : ℕ) : ℝ) : ℂ) * I =
        ((-(u.im * (sigma - 1) * Real.log (n : ℕ)) : ℝ) : ℂ) * I by
    push_cast
    ring]
  rw [Complex.norm_exp_ofReal_mul_I, one_mul]

private theorem summable_norm_sq_eulerPositiveCriticalComplexDampedStateWeight
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    Summable (fun n : ℕ+ =>
      ‖eulerPositiveCriticalComplexDampedStateWeight sigma u n‖ ^ 2) := by
  have h := HilbertSchmidt.summable_coe_sq
    (eulerPositiveCriticalDampedStateLp sigma u.re hsigma hu)
  exact h.congr fun n => by
    rw [norm_eulerPositiveCriticalComplexDampedStateWeight]
    rfl

/-- Actual square-summable complex full-Euler column. -/
def eulerPositiveCriticalComplexDampedStateLp
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    EulerPositiveL2 :=
  ⟨eulerPositiveCriticalComplexDampedStateWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerPositiveCriticalComplexDampedStateWeight hsigma hu)⟩

theorem eulerPositiveCriticalComplexDampedStateLp_ofReal
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositiveCriticalComplexDampedStateLp sigma (u : ℂ) hsigma hu =
      eulerPositiveCriticalDampedStateLp sigma u hsigma hu := by
  apply lp.ext
  funext n
  change eulerPositiveCriticalComplexDampedStateWeight sigma (u : ℂ) n =
    eulerPositiveCriticalDampedStateWeight sigma u n
  simp [eulerPositiveCriticalComplexDampedStateWeight]

theorem complexDamping_mul_eulerPositiveMass
    (sigma : ℝ) (u : ℂ) (n : ℕ+) :
    Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ) =
      1 / ((n : ℕ) : ℂ) ^
        eulerPositiveComplexBoundaryParameter sigma u := by
  have hnC : (((n : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast n.property.ne'
  have hlog : Complex.log (((n : ℕ) : ℂ)) =
      ((Real.log (n : ℕ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast (n : ℕ),
      ← Complex.ofReal_log (by positivity)]
  rw [eulerPositiveMass, Complex.ofReal_cpow (by positivity)]
  change
    Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        ((n : ℕ) : ℂ) ^ ((-sigma : ℝ) : ℂ) =
      1 / ((n : ℕ) : ℂ) ^ eulerPositiveComplexBoundaryParameter sigma u
  simp only [Complex.cpow_def_of_ne_zero hnC, hlog]
  rw [one_div, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  simp only [eulerPositiveComplexBoundaryParameter]
  push_cast
  ring

theorem summable_complexEulerLogDirichlet
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ =>
      (Real.log n : ℂ) / (n : ℂ) ^ s) := by
  apply Summable.of_norm
  have h := summable_abs_log_natCast_pow_mul_rpow_neg 1 s.re hs
  apply h.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -s.re ≠ 0)]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, pow_one]
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast]
    rw [norm_cpow_eq_rpow_re_of_pos hnpos]
    rw [Real.rpow_neg hnpos.le]
    ring

theorem tsum_complexEulerLogDirichlet_succ
    {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ,
      (Real.log (n + 1 : ℕ) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s) =
      ∑' n : ℕ, (Real.log n : ℂ) / (n : ℂ) ^ s := by
  have h := (summable_complexEulerLogDirichlet hs).sum_add_tsum_nat_add 1
  simpa using h

theorem tsum_complexDamping_eulerPositiveMass
    {sigma : ℝ} {u : ℂ}
    (hshift : 1 < (eulerPositiveComplexBoundaryParameter sigma u).re) :
    (∑' n : ℕ+,
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ)) =
      riemannZeta (eulerPositiveComplexBoundaryParameter sigma u) := by
  rw [show (∑' n : ℕ+,
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ)) =
      ∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^
        eulerPositiveComplexBoundaryParameter sigma u by
    apply tsum_congr
    intro n
    exact complexDamping_mul_eulerPositiveMass sigma u n]
  have hpnat :
      (∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^
          eulerPositiveComplexBoundaryParameter sigma u) =
        ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^
          eulerPositiveComplexBoundaryParameter sigma u := by
    simpa only using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => 1 / (n : ℂ) ^
          eulerPositiveComplexBoundaryParameter sigma u))
  rw [hpnat]
  simpa only [Nat.cast_add, Nat.cast_one] using
    (zeta_eq_tsum_one_div_nat_add_one_cpow hshift).symm

theorem tsum_complexDamping_eulerPositiveMass_mul_log
    {sigma : ℝ} {u : ℂ}
    (hshift : 1 < (eulerPositiveComplexBoundaryParameter sigma u).re) :
    (∑' n : ℕ+,
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ) *
          ((Real.log (n : ℕ) : ℝ) : ℂ)) =
      riemannZeta (eulerPositiveComplexBoundaryParameter sigma u) *
        infinitePrimeFlux (eulerPositiveComplexBoundaryParameter sigma u) := by
  let s := eulerPositiveComplexBoundaryParameter sigma u
  rw [show (∑' n : ℕ+,
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ) *
          ((Real.log (n : ℕ) : ℝ) : ℂ)) =
      ∑' n : ℕ+, (Real.log (n : ℕ) : ℂ) /
        ((n : ℕ) : ℂ) ^ s by
    apply tsum_congr
    intro n
    rw [show
      Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveMass sigma n : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ) =
        ((Real.log (n : ℕ) : ℝ) : ℂ) *
          (Complex.exp
              (-u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            (eulerPositiveMass sigma n : ℂ)) by ring]
    rw [complexDamping_mul_eulerPositiveMass]
    dsimp only [s]
    simp only [div_eq_mul_inv, one_mul]]
  have hpnat :
      (∑' n : ℕ+, (Real.log (n : ℕ) : ℂ) / ((n : ℕ) : ℂ) ^ s) =
        ∑' n : ℕ, (Real.log (n + 1 : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ) ^ s := by
    simpa only using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => (Real.log n : ℂ) / (n : ℂ) ^ s))
  rw [hpnat, tsum_complexEulerLogDirichlet_succ hshift]
  rw [← neg_neg (∑' n : ℕ, (Real.log n : ℂ) / (n : ℂ) ^ s),
    ← GaloisForLFunctions.zeta_deriv_eq_neg_tsum hshift]
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hshift
  simp only [infinitePrimeFlux, logDeriv_apply]
  dsimp only [s] at hz ⊢
  field_simp [hz]

/-- The base state paired with a complex inward column is the literal full-Euler overlap. -/
theorem inner_eulerPositiveState_complexDamped_eq_affineOverlap
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    inner ℂ (eulerPositiveStateLp sigma hsigma)
        (eulerPositiveCriticalComplexDampedStateLp sigma u hsigma hu) =
      eulerAffineBoundaryOverlap (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) u := by
  have hshift := one_lt_eulerPositiveComplexBoundaryParameter_re hsigma hu
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveStateLp,
    eulerPositiveCriticalComplexDampedStateLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ+,
      eulerPositiveCriticalComplexDampedStateWeight sigma u n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) =
      ∑' n : ℕ+,
        (Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveMass sigma n : ℂ)) /
            (eulerPositiveTotal sigma : ℂ) by
    apply tsum_congr
    intro n
    rw [eulerPositiveCriticalComplexDampedStateWeight_eq_exp]
    have hnorm : eulerPositiveStateWeight sigma n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_eulerPositiveStateWeight_sq hsigma]
    rw [show
      Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) by ring,
      hnorm, eulerPositiveProbability, Complex.ofReal_div]
    rw [← mul_div_assoc]]
  rw [tsum_div_const, tsum_complexDamping_eulerPositiveMass hshift,
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma]
  rfl

theorem complexDamped_pair_apply
    (sigma : ℝ) (u v : ℂ) (n : ℕ+) :
    eulerPositiveCriticalComplexDampedStateWeight sigma v n *
        (starRingEnd ℂ)
          (eulerPositiveCriticalComplexDampedStateWeight sigma u n) =
      eulerPositiveCriticalComplexDampedStateWeight sigma
          (v + (starRingEnd ℂ) u) n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) := by
  simp only [eulerPositiveCriticalComplexDampedStateWeight_eq_exp]
  have hexp :
      (starRingEnd ℂ)
          (Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ))) =
        Complex.exp
          (-(starRingEnd ℂ) u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal]
  rw [map_mul, hexp]
  rw [show
      Complex.exp
            (-v * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
          (Complex.exp
              (-(starRingEnd ℂ) u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) =
        (Complex.exp
            (-v * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          Complex.exp
            (-(starRingEnd ℂ) u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ))) *
          eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) by ring]
  rw [← Complex.exp_add]
  congr 2
  ring

/-- Exact non-diagonal full-Euler source Gram. -/
theorem inner_eulerPositiveComplexDamped_complexDamped_eq_affineOverlap
    {sigma : ℝ} {u v : ℂ} (hsigma : 1 < sigma)
    (hu : 0 ≤ u.re) (hv : 0 ≤ v.re) :
    inner ℂ
        (eulerPositiveCriticalComplexDampedStateLp sigma u hsigma hu)
        (eulerPositiveCriticalComplexDampedStateLp sigma v hsigma hv) =
      eulerAffineBoundaryOverlap (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) (v + (starRingEnd ℂ) u) := by
  have huv : 0 ≤ (v + (starRingEnd ℂ) u).re := by
    simp only [add_re, Complex.conj_re]
    linarith
  rw [show
      inner ℂ
          (eulerPositiveCriticalComplexDampedStateLp sigma u hsigma hu)
          (eulerPositiveCriticalComplexDampedStateLp sigma v hsigma hv) =
        inner ℂ (eulerPositiveStateLp sigma hsigma)
          (eulerPositiveCriticalComplexDampedStateLp sigma
            (v + (starRingEnd ℂ) u) hsigma huv) by
    rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
    simp only [eulerPositiveStateLp,
      eulerPositiveCriticalComplexDampedStateLp, RCLike.inner_apply]
    apply tsum_congr
    intro n
    exact complexDamped_pair_apply sigma u v n]
  exact inner_eulerPositiveState_complexDamped_eq_affineOverlap hsigma huv

/-- The same complex column reports the full holomorphic Euler Fisher numerator. -/
theorem inner_eulerPositiveFisherTangent_complexDamped_eq_affineScore
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    inner ℂ (eulerPositiveCriticalFisherTangentLp sigma hsigma)
        (eulerPositiveCriticalComplexDampedStateLp sigma u hsigma hu) =
      eulerAffineFisherScore (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) u := by
  have hshift := one_lt_eulerPositiveComplexBoundaryParameter_re hsigma hu
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveCriticalFisherTangentLp,
    eulerPositiveCriticalComplexDampedStateLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ+,
      eulerPositiveCriticalComplexDampedStateWeight sigma u n *
        (starRingEnd ℂ)
          (eulerPositiveCriticalFisherTangentWeight sigma n)) =
      ((-2 * (sigma - 1 : ℝ) : ℝ) : ℂ) /
          (eulerPositiveTotal sigma : ℂ) *
        ∑' n : ℕ+,
          (Complex.exp
                (-u * ((sigma - 1 : ℝ) : ℂ) *
                  ((Real.log (n : ℕ) : ℝ) : ℂ)) *
              (eulerPositiveMass sigma n : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ) -
            ((eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) *
              (Complex.exp
                  (-u * ((sigma - 1 : ℝ) : ℂ) *
                    ((Real.log (n : ℕ) : ℝ) : ℂ)) *
                (eulerPositiveMass sigma n : ℂ))) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [eulerPositiveCriticalComplexDampedStateWeight_eq_exp,
      eulerPositiveCriticalFisherTangentWeight]
    simp only [map_mul, conj_ofReal]
    have hnorm : eulerPositiveStateWeight sigma n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by rw [← Complex.ofReal_pow,
          norm_eulerPositiveStateWeight_sq hsigma]
    rw [show
      Complex.exp
            (-u * ((sigma - 1 : ℝ) : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ)) *
          eulerPositiveStateWeight sigma n *
          (((-2 * (sigma - 1) *
              (Real.log (n : ℕ) -
                eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) =
        ((-2 * (sigma - 1) : ℝ) : ℂ) *
          (Complex.exp
              (-u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            (eulerPositiveStateWeight sigma n *
              (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) *
            (((Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma : ℝ) : ℂ))) by
        push_cast
        ring,
      hnorm, eulerPositiveProbability, Complex.ofReal_div]
    push_cast
    ring]
  have hlogSum : Summable (fun n : ℕ+ =>
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ) *
          ((Real.log (n : ℕ) : ℝ) : ℂ)) := by
    have hnat := summable_complexEulerLogDirichlet hshift
    have hpnat : Summable (fun n : ℕ+ =>
        (Real.log (n : ℕ) : ℂ) /
          ((n : ℕ) : ℂ) ^ eulerPositiveComplexBoundaryParameter sigma u) := by
      simpa only [Function.comp_apply] using!
        hnat.subtype (fun n : ℕ => 0 < n)
    exact hpnat.congr fun n => by
      rw [show
        Complex.exp
              (-u * ((sigma - 1 : ℝ) : ℂ) *
                ((Real.log (n : ℕ) : ℝ) : ℂ)) *
            (eulerPositiveMass sigma n : ℂ) *
              ((Real.log (n : ℕ) : ℝ) : ℂ) =
          ((Real.log (n : ℕ) : ℝ) : ℂ) *
            (Complex.exp
                (-u * ((sigma - 1 : ℝ) : ℂ) *
                  ((Real.log (n : ℕ) : ℝ) : ℂ)) *
              (eulerPositiveMass sigma n : ℂ)) by ring,
        complexDamping_mul_eulerPositiveMass]
      simp only [div_eq_mul_inv, one_mul]
  have hmass : Summable (fun n : ℕ+ =>
      Complex.exp
          (-u * ((sigma - 1 : ℝ) : ℂ) *
            ((Real.log (n : ℕ) : ℝ) : ℂ)) *
        (eulerPositiveMass sigma n : ℂ)) := by
    have hs : Summable (fun n : ℕ+ =>
        1 / ((n : ℕ) : ℂ) ^
          eulerPositiveComplexBoundaryParameter sigma u) := by
      have hnat := Complex.summable_one_div_nat_cpow.mpr hshift
      simpa only [Function.comp_apply] using!
        hnat.subtype (fun n : ℕ => 0 < n)
    exact hs.congr fun n =>
      (complexDamping_mul_eulerPositiveMass sigma u n).symm
  have htotal : (eulerPositiveTotal sigma : ℂ) =
      riemannZeta (sigma : ℂ) :=
    ofReal_eulerPositiveTotal_eq_riemannZeta hsigma
  have hbase : riemannZeta (sigma : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)
  rw [hlogSum.tsum_sub (hmass.mul_left
      ((eulerPositiveLogMoment 1 sigma : ℝ) : ℂ)),
    tsum_mul_left,
    tsum_complexDamping_eulerPositiveMass_mul_log hshift,
    tsum_complexDamping_eulerPositiveMass hshift,
    htotal,
    ofReal_eulerPositiveLogMoment_one_eq_infinitePrimeFlux hsigma,
    eulerAffineFisherScore_eq_current_difference
      (by simpa using hsigma) hshift]
  simp only [eulerAffineBoundaryOverlap,
    eulerPositiveComplexBoundaryParameter]
  field_simp [hbase]
  push_cast
  ring

/-- Complex graph denominator retained before scalar division. -/
def eulerPositivePreScalarComplexGraphDenominator
    (sigma : ℝ) (u : ℂ) : ℂ :=
  ((sigma - 1 : ℝ) : ℂ) *
    eulerAffineBoundaryOverlap (sigma : ℂ)
      ((sigma - 1 : ℝ) : ℂ) u

theorem eulerPositivePreScalarComplexGraphDenominator_ne_zero
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    eulerPositivePreScalarComplexGraphDenominator sigma u ≠ 0 := by
  have hshift := one_lt_eulerPositiveComplexBoundaryParameter_re hsigma hu
  unfold eulerPositivePreScalarComplexGraphDenominator
  apply mul_ne_zero
  · exact_mod_cast sub_ne_zero.mpr hsigma.ne'
  · unfold eulerAffineBoundaryOverlap
    apply div_ne_zero
    · exact riemannZeta_ne_zero_of_one_lt_re hshift
    · exact riemannZeta_ne_zero_of_one_lt_re (by simpa using hsigma)

/-- Complex graph-normal coefficient of an actual full-Euler source vector. -/
def eulerPositivePreScalarComplexGraphNormalizedCoefficient
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re)
    (source : EulerPositiveL2) : ℂ :=
  inner ℂ source
      (eulerPositiveCriticalComplexDampedStateLp sigma u hsigma hu) /
    eulerPositivePreScalarComplexGraphDenominator sigma u

/-- Exact holomorphic pointed prime-current difference carried by the transverse four-unit
source. -/
theorem eulerPositivePreScalarComplexGraphNormalizedCoefficient_transverse
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    eulerPositivePreScalarComplexGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) =
      2 * (infinitePrimeFlux (eulerPositiveComplexBoundaryParameter sigma u) -
        infinitePrimeFlux (sigma : ℂ)) := by
  rw [eulerPositivePreScalarComplexGraphNormalizedCoefficient,
    eulerPositivePreScalarGammaTransverseSource, inner_neg_left,
    inner_eulerPositiveFisherTangent_complexDamped_eq_affineScore hsigma hu]
  have hden :=
    eulerPositivePreScalarComplexGraphDenominator_ne_zero hsigma hu
  apply (div_eq_iff hden).2
  rw [eulerAffineFisherScore_eq_current_difference
      (by simpa using hsigma)
      (one_lt_eulerPositiveComplexBoundaryParameter_re hsigma hu)]
  unfold eulerPositivePreScalarComplexGraphDenominator
  simp only [eulerPositiveComplexBoundaryParameter]
  ring

/-- Exact pointed completed-Xi reporter on every safe complex inward node. -/
def eulerPositiveTransverseGammaXiComplexPointedReporter
    (sigma : ℝ) (u : ℂ) (hsigma : 1 < sigma) (hu : 0 ≤ u.re) : ℂ :=
  (-I / 2) *
    (eulerPositivePreScalarComplexGraphNormalizedCoefficient sigma u hsigma hu
        (eulerPositivePreScalarGammaTransverseSource sigma hsigma) -
      2 * (logDeriv archFactor
              (eulerPositiveComplexBoundaryParameter sigma u) -
            logDeriv archFactor (sigma : ℂ)))

theorem eulerPositiveTransverseGammaXiComplexPointedReporter_eq_continued_sub_base
    {sigma : ℝ} {u : ℂ} (hsigma : 1 < sigma) (hu : 0 ≤ u.re) :
    eulerPositiveTransverseGammaXiComplexPointedReporter sigma u hsigma hu =
      continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate
            (eulerPositiveComplexBoundaryParameter sigma u)) -
        continuedPrimeArchSourceRelativeTrace
          (xiWardCenteredCoordinate (sigma : ℂ)) := by
  rw [eulerPositiveTransverseGammaXiComplexPointedReporter,
    eulerPositivePreScalarComplexGraphNormalizedCoefficient_transverse hsigma hu]
  simp only [continuedPrimeArchSourceRelativeTrace,
    xiWardCenteredCoordinate_source]
  ring

/-- Actual augmented source packet: complex inward columns plus the one transverse reporter. -/
def eulerPositiveComplexPointedTransverseVector
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    Fin n ⊕ Unit → EulerPositiveL2
  | Sum.inl i =>
      eulerPositiveCriticalComplexDampedStateLp sigma (u i) hsigma (hu i)
  | Sum.inr _ => eulerPositivePreScalarGammaTransverseSource sigma hsigma

/-- Non-diagonal full-Euler pointed Gram, formed before scalar observation. -/
def eulerPositiveComplexPointedTransverseGram
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ :=
  Matrix.gram ℂ (eulerPositiveComplexPointedTransverseVector sigma hsigma u hu)

theorem eulerPositiveComplexPointedTransverseGram_posSemidef
    {n : ℕ} (sigma : ℝ) (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    (eulerPositiveComplexPointedTransverseGram sigma hsigma u hu).PosSemidef :=
  Matrix.posSemidef_gram ℂ
    (eulerPositiveComplexPointedTransverseVector sigma hsigma u hu)

theorem eulerPositiveComplexPointedTransverseGram_topLeft
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) (i j : Fin n) :
    eulerPositiveComplexPointedTransverseGram sigma hsigma u hu
        (Sum.inl i) (Sum.inl j) =
      eulerAffineBoundaryOverlap (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ)
        (u j + (starRingEnd ℂ) (u i)) := by
  exact inner_eulerPositiveComplexDamped_complexDamped_eq_affineOverlap
    hsigma (hu i) (hu j)

theorem eulerPositiveComplexPointedTransverseGram_bottomLeft
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) (i : Fin n) :
    eulerPositiveComplexPointedTransverseGram sigma hsigma u hu
        (Sum.inr ()) (Sum.inl i) =
      -eulerAffineFisherScore (sigma : ℂ)
        ((sigma - 1 : ℝ) : ℂ) (u i) := by
  change inner ℂ (eulerPositivePreScalarGammaTransverseSource sigma hsigma)
      (eulerPositiveCriticalComplexDampedStateLp sigma (u i) hsigma (hu i)) = _
  rw [eulerPositivePreScalarGammaTransverseSource, inner_neg_left,
    inner_eulerPositiveFisherTangent_complexDamped_eq_affineScore hsigma (hu i)]

theorem eulerPositiveComplexPointedTransverseGram_bottomRight
    {n : ℕ} {sigma : ℝ} (hsigma : 1 < sigma)
    (u : Fin n → ℂ) (hu : ∀ i, 0 ≤ (u i).re) :
    eulerPositiveComplexPointedTransverseGram sigma hsigma u hu
        (Sum.inr ()) (Sum.inr ()) =
      (eulerPositiveCriticalProjectiveFisherEnergy sigma : ℂ) := by
  change inner ℂ (eulerPositivePreScalarGammaTransverseSource sigma hsigma)
      (eulerPositivePreScalarGammaTransverseSource sigma hsigma) = _
  rw [inner_self_eq_norm_sq_to_K]
  have h := congrArg (fun x : ℝ => (x : ℂ))
    (norm_eulerPositivePreScalarGammaTransverseSource_sq hsigma)
  push_cast at h
  exact h

/-- The polarized reporter retains P-G166's sharp four-unit critical source budget. -/
theorem tendsto_norm_eulerPositiveComplexPointedTransverse_source_sq :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          ‖eulerPositivePreScalarGammaTransverseSource sigma hsigma‖ ^ 2
        else 0)
      (nhdsWithin 1 (Ioi 1)) (nhds 4) :=
  tendsto_norm_eulerPositivePreScalarGammaTransverseSource_sq

end

end RHTower
