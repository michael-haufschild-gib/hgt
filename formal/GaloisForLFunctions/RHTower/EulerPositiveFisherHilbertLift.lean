import GaloisForLFunctions.RHTower.EulerAffineGammaXiWardTransport
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicAffineProjection
import GaloisForLFunctions.RHTower.EulerFisherCurvature

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal InnerProductSpace

noncomputable section
namespace RHTower

/-- Positive Euler Gibbs mass on the actual positive-integer carrier. -/
def eulerPositiveMass (sigma : ℝ) (n : ℕ+) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-sigma)

theorem eulerPositiveMass_pos (sigma : ℝ) (n : ℕ+) :
    0 < eulerPositiveMass sigma n :=
  Real.rpow_pos_of_pos (by positivity) _

theorem summable_eulerPositiveMass
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (eulerPositiveMass sigma) := by
  have hnat :
      Summable (fun n : ℕ => (n : ℝ) ^ (-sigma)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  simpa only [eulerPositiveMass, Function.comp_apply] using
    hnat.subtype (fun n : ℕ => 0 < n)

def eulerPositiveTotal (sigma : ℝ) : ℝ :=
  ∑' n : ℕ+, eulerPositiveMass sigma n

theorem eulerPositiveTotal_pos
    {sigma : ℝ} (hsigma : 1 < sigma) :
    0 < eulerPositiveTotal sigma := by
  exact (summable_eulerPositiveMass hsigma).tsum_pos
    (fun n => (eulerPositiveMass_pos sigma n).le) 1
    (eulerPositiveMass_pos sigma 1)

theorem ofReal_eulerPositiveTotal_eq_riemannZeta
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (eulerPositiveTotal sigma : ℂ) =
      riemannZeta (sigma : ℂ) := by
  rw [eulerPositiveTotal, Complex.ofReal_tsum]
  rw [show (∑' n : ℕ+, (eulerPositiveMass sigma n : ℂ)) =
      ∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^ (sigma : ℂ) by
    apply tsum_congr
    intro n
    rw [eulerPositiveMass, Complex.ofReal_cpow (by positivity)]
    rw [show ((-sigma : ℝ) : ℂ) = -(sigma : ℂ) by norm_cast,
      Complex.cpow_neg, one_div]
    norm_cast]
  have hpnat :
      (∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^ (sigma : ℂ)) =
        ∑' n : ℕ, 1 / ((n + 1 : ℕ) : ℂ) ^ (sigma : ℂ) := by
    simpa only using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ => 1 / (n : ℂ) ^ (sigma : ℂ)))
  rw [hpnat]
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hsigma)]
  apply tsum_congr
  intro n
  norm_cast

def eulerPositiveProbability (sigma : ℝ) (n : ℕ+) : ℝ :=
  eulerPositiveMass sigma n / eulerPositiveTotal sigma

theorem eulerPositiveProbability_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ+) :
    0 ≤ eulerPositiveProbability sigma n :=
  div_nonneg (eulerPositiveMass_pos sigma n).le
    (eulerPositiveTotal_pos hsigma).le

theorem summable_eulerPositiveProbability
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (eulerPositiveProbability sigma) :=
  (summable_eulerPositiveMass hsigma).div_const _

theorem tsum_eulerPositiveProbability
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ∑' n : ℕ+, eulerPositiveProbability sigma n = 1 := by
  rw [show (∑' n : ℕ+, eulerPositiveProbability sigma n) =
      (∑' n : ℕ+, eulerPositiveMass sigma n) /
        eulerPositiveTotal sigma by
    exact tsum_div_const]
  exact div_self (eulerPositiveTotal_pos hsigma).ne'

def eulerPositiveLogMoment (k : ℕ) (sigma : ℝ) : ℝ :=
  ∑' n : ℕ+,
    eulerPositiveProbability sigma n * Real.log (n : ℕ) ^ k

theorem summable_eulerPositiveLogMoment
    (k : ℕ) {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ+ =>
      eulerPositiveProbability sigma n *
        Real.log (n : ℕ) ^ k) := by
  have hmajorNat :=
    summable_abs_log_natCast_pow_mul_rpow_neg k sigma hsigma
  have hmajor :
      Summable (fun n : ℕ+ =>
        |Real.log (n : ℕ)| ^ k * ((n : ℕ) : ℝ) ^ (-sigma)) := by
    simpa only [Function.comp_apply] using
      hmajorNat.subtype (fun n : ℕ => 0 < n)
  have hmajor' := hmajor.div_const (eulerPositiveTotal sigma)
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor'
  · intro n
    exact mul_nonneg (eulerPositiveProbability_nonneg hsigma n)
      (pow_nonneg (Real.log_natCast_nonneg (n : ℕ)) k)
  · intro n
    rw [eulerPositiveProbability, eulerPositiveMass,
      abs_of_nonneg (Real.log_natCast_nonneg (n : ℕ))]
    ring_nf
    exact le_rfl

private theorem summable_complexEulerLogDirichlet
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ =>
      (Real.log n : ℂ) / (n : ℂ) ^ (sigma : ℂ)) := by
  apply Summable.of_norm
  have h :=
    summable_abs_log_natCast_pow_mul_rpow_neg 1 sigma hsigma
  apply h.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -sigma ≠ 0)]
  · have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, pow_one]
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast]
    rw [norm_cpow_eq_rpow_re_of_pos hnpos]
    simp only [Complex.ofReal_re]
    rw [Real.rpow_neg hnpos.le]
    ring

private theorem tsum_complexEulerLogDirichlet_succ
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ,
      (Real.log (n + 1) : ℂ) /
        ((n + 1 : ℕ) : ℂ) ^ (sigma : ℂ)) =
      ∑' n : ℕ,
        (Real.log n : ℂ) / (n : ℂ) ^ (sigma : ℂ) := by
  have h := (summable_complexEulerLogDirichlet hsigma).sum_add_tsum_nat_add 1
  simpa using h

theorem ofReal_eulerPositiveLogMoment_one_eq_infinitePrimeFlux
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (eulerPositiveLogMoment 1 sigma : ℂ) =
      infinitePrimeFlux (sigma : ℂ) := by
  have htotal : (eulerPositiveTotal sigma : ℂ) ≠ 0 := by
    exact_mod_cast (eulerPositiveTotal_pos hsigma).ne'
  rw [eulerPositiveLogMoment, Complex.ofReal_tsum]
  rw [show (fun n : ℕ+ =>
      ((eulerPositiveProbability sigma n *
        Real.log (n : ℕ) ^ 1 : ℝ) : ℂ)) =
      fun n : ℕ+ =>
        (Real.log (n : ℕ) : ℂ) /
          ((n : ℕ) : ℂ) ^ (sigma : ℂ) /
            (eulerPositiveTotal sigma : ℂ) by
    funext n
    rw [eulerPositiveProbability, eulerPositiveMass,
      Complex.ofReal_mul, Complex.ofReal_div, pow_one,
      Complex.ofReal_cpow (by positivity)]
    rw [show ((-sigma : ℝ) : ℂ) = -(sigma : ℂ) by norm_cast,
      Complex.cpow_neg]
    norm_cast
    ring]
  rw [tsum_div_const]
  have hpnat :
      (∑' n : ℕ+,
          (Real.log (n : ℕ) : ℂ) /
            ((n : ℕ) : ℂ) ^ (sigma : ℂ)) =
        ∑' n : ℕ,
          (Real.log (n + 1) : ℂ) /
            ((n + 1 : ℕ) : ℂ) ^ (sigma : ℂ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tsum_pnat_eq_tsum_succ
        (f := fun n : ℕ =>
          (Real.log n : ℂ) / (n : ℂ) ^ (sigma : ℂ)))
  rw [hpnat, tsum_complexEulerLogDirichlet_succ hsigma]
  rw [← neg_neg (∑' n : ℕ,
      (Real.log n : ℂ) / (n : ℂ) ^ (sigma : ℂ)),
    ← GaloisForLFunctions.zeta_deriv_eq_neg_tsum
      (by simpa using hsigma)]
  rw [ofReal_eulerPositiveTotal_eq_riemannZeta hsigma]
  simp only [infinitePrimeFlux, logDeriv_apply]
  ring

/-- Positive square root of the normalized Euler Gibbs law. -/
def eulerPositiveStateWeight (sigma : ℝ) (n : ℕ+) : ℂ :=
  Real.sqrt (eulerPositiveProbability sigma n)

theorem norm_eulerPositiveStateWeight_sq
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ+) :
    ‖eulerPositiveStateWeight sigma n‖ ^ 2 =
      eulerPositiveProbability sigma n := by
  rw [eulerPositiveStateWeight, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact eulerPositiveProbability_nonneg hsigma n

theorem summable_norm_sq_eulerPositiveStateWeight
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ+ =>
      ‖eulerPositiveStateWeight sigma n‖ ^ 2) := by
  simpa only [norm_eulerPositiveStateWeight_sq hsigma] using
    summable_eulerPositiveProbability hsigma

/-- Normalized full-Euler state on the positive-integer Hilbert carrier. -/
def eulerPositiveStateLp
    (sigma : ℝ) (hsigma : 1 < sigma) : EulerPositiveL2 :=
  ⟨eulerPositiveStateWeight sigma,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerPositiveStateWeight hsigma)⟩

theorem norm_eulerPositiveStateLp_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositiveStateLp sigma hsigma‖ ^ 2 = 1 := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  simpa only [eulerPositiveStateLp,
    norm_eulerPositiveStateWeight_sq hsigma] using
    tsum_eulerPositiveProbability hsigma

theorem norm_eulerPositiveStateLp
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositiveStateLp sigma hsigma‖ = 1 := by
  nlinarith [norm_eulerPositiveStateLp_sq hsigma,
    norm_nonneg (eulerPositiveStateLp sigma hsigma)]

/-- Critical full-Euler logarithmic Fisher tangent. -/
def eulerPositiveCriticalFisherTangentWeight
    (sigma : ℝ) (n : ℕ+) : ℂ :=
  ((-2 * (sigma - 1) *
    (Real.log (n : ℕ) - eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) *
      eulerPositiveStateWeight sigma n

private theorem norm_eulerPositiveCriticalFisherTangentWeight_sq
    {sigma : ℝ} (hsigma : 1 < sigma) (n : ℕ+) :
    ‖eulerPositiveCriticalFisherTangentWeight sigma n‖ ^ 2 =
      4 * (sigma - 1) ^ 2 *
        eulerPositiveProbability sigma n *
          (Real.log (n : ℕ) -
            eulerPositiveLogMoment 1 sigma) ^ 2 := by
  rw [eulerPositiveCriticalFisherTangentWeight, norm_mul, mul_pow,
    norm_eulerPositiveStateWeight_sq hsigma, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  ring

private theorem summable_eulerPositiveCenteredLogSq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ+ =>
      eulerPositiveProbability sigma n *
        (Real.log (n : ℕ) -
          eulerPositiveLogMoment 1 sigma) ^ 2) := by
  let m := eulerPositiveLogMoment 1 sigma
  have h2 := summable_eulerPositiveLogMoment 2 hsigma
  have h1base : Summable (fun n : ℕ+ =>
      eulerPositiveProbability sigma n * Real.log (n : ℕ)) := by
    simpa only [pow_one] using
      summable_eulerPositiveLogMoment 1 hsigma
  have h1 := h1base.mul_left (-2 * m)
  have h0 :=
    (summable_eulerPositiveProbability hsigma).mul_left (m ^ 2)
  apply (h2.add h1 |>.add h0).congr
  intro n
  dsimp [m]
  ring

private theorem tsum_eulerPositiveCenteredLogSq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    (∑' n : ℕ+,
      eulerPositiveProbability sigma n *
        (Real.log (n : ℕ) -
          eulerPositiveLogMoment 1 sigma) ^ 2) =
      eulerPositiveLogMoment 2 sigma -
        eulerPositiveLogMoment 1 sigma ^ 2 := by
  let m := eulerPositiveLogMoment 1 sigma
  have h2 := summable_eulerPositiveLogMoment 2 hsigma
  have h1base : Summable (fun n : ℕ+ =>
      eulerPositiveProbability sigma n * Real.log (n : ℕ)) := by
    simpa only [pow_one] using
      summable_eulerPositiveLogMoment 1 hsigma
  have h1 := h1base.mul_left (-2 * m)
  have h0base := summable_eulerPositiveProbability hsigma
  have h0 := h0base.mul_left (m ^ 2)
  rw [show (fun n : ℕ+ =>
      eulerPositiveProbability sigma n *
        (Real.log (n : ℕ) -
          eulerPositiveLogMoment 1 sigma) ^ 2) =
      fun n =>
        eulerPositiveProbability sigma n *
            Real.log (n : ℕ) ^ 2 +
          (-2 * m) *
            (eulerPositiveProbability sigma n *
              Real.log (n : ℕ)) +
          m ^ 2 * eulerPositiveProbability sigma n by
    funext n
    dsimp [m]
    ring]
  rw [Summable.tsum_add (h2.add h1) h0,
    Summable.tsum_add h2 h1, tsum_mul_left, tsum_mul_left]
  rw [show (∑' n : ℕ+,
      eulerPositiveProbability sigma n *
        Real.log (n : ℕ) ^ 2) =
      eulerPositiveLogMoment 2 sigma by rfl]
  rw [show (∑' n : ℕ+,
      eulerPositiveProbability sigma n *
        Real.log (n : ℕ)) =
      eulerPositiveLogMoment 1 sigma by
    unfold eulerPositiveLogMoment
    simp only [pow_one]]
  rw [tsum_eulerPositiveProbability hsigma]
  dsimp [m]
  ring

private theorem
    summable_norm_sq_eulerPositiveCriticalFisherTangentWeight
    {sigma : ℝ} (hsigma : 1 < sigma) :
    Summable (fun n : ℕ+ =>
      ‖eulerPositiveCriticalFisherTangentWeight sigma n‖ ^ 2) := by
  have h := (summable_eulerPositiveCenteredLogSq hsigma).mul_left
    (4 * (sigma - 1) ^ 2)
  apply h.congr
  intro n
  rw [norm_eulerPositiveCriticalFisherTangentWeight_sq hsigma]
  ring

/-- Critical full-Euler tangent as an actual square-summable vector. -/
def eulerPositiveCriticalFisherTangentLp
    (sigma : ℝ) (hsigma : 1 < sigma) : EulerPositiveL2 :=
  ⟨eulerPositiveCriticalFisherTangentWeight sigma,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerPositiveCriticalFisherTangentWeight hsigma)⟩

/-- Full-Euler projective Fisher energy in the direct positive-integer chart. -/
def eulerPositiveCriticalProjectiveFisherEnergy (sigma : ℝ) : ℝ :=
  4 * (sigma - 1) ^ 2 *
    (eulerPositiveLogMoment 2 sigma -
      eulerPositiveLogMoment 1 sigma ^ 2)

theorem norm_eulerPositiveCriticalFisherTangentLp_sq
    {sigma : ℝ} (hsigma : 1 < sigma) :
    ‖eulerPositiveCriticalFisherTangentLp sigma hsigma‖ ^ 2 =
      eulerPositiveCriticalProjectiveFisherEnergy sigma := by
  rw [HilbertSchmidt.lp_norm_sq_eq]
  simp only [eulerPositiveCriticalFisherTangentLp]
  rw [show (∑' n : ℕ+,
      ‖eulerPositiveCriticalFisherTangentWeight sigma n‖ ^ 2) =
      4 * (sigma - 1) ^ 2 *
        ∑' n : ℕ+,
          eulerPositiveProbability sigma n *
            (Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma) ^ 2 by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [norm_eulerPositiveCriticalFisherTangentWeight_sq hsigma]
    ring]
  rw [tsum_eulerPositiveCenteredLogSq hsigma]
  rfl

theorem inner_eulerPositiveState_fisherTangent_eq_zero
    {sigma : ℝ} (hsigma : 1 < sigma) :
    inner ℂ (eulerPositiveStateLp sigma hsigma)
      (eulerPositiveCriticalFisherTangentLp sigma hsigma) = 0 := by
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveStateLp,
    eulerPositiveCriticalFisherTangentLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ+,
      eulerPositiveCriticalFisherTangentWeight sigma n *
        (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) =
      ((-2 * (sigma - 1) : ℝ) : ℂ) *
        ∑' n : ℕ+,
          ((eulerPositiveProbability sigma n *
            (Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [eulerPositiveCriticalFisherTangentWeight]
    have hnorm :
        eulerPositiveStateWeight sigma n *
          (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by
          rw [← Complex.ofReal_pow,
            norm_eulerPositiveStateWeight_sq hsigma]
    calc
      _ = ((-2 * (sigma - 1) *
            (Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) := by
        ring
      _ = _ := by
        rw [hnorm]
        push_cast
        ring]
  have hsumReal :
      Summable (fun n : ℕ+ =>
        eulerPositiveProbability sigma n *
          (Real.log (n : ℕ) -
            eulerPositiveLogMoment 1 sigma)) := by
    have h1 : Summable (fun n : ℕ+ =>
        eulerPositiveProbability sigma n *
          Real.log (n : ℕ)) := by
      simpa only [pow_one] using
        summable_eulerPositiveLogMoment 1 hsigma
    have h0 :=
      (summable_eulerPositiveProbability hsigma).mul_left
        (-eulerPositiveLogMoment 1 sigma)
    apply (h1.add h0).congr
    intro n
    ring
  rw [← Complex.ofReal_tsum]
  rw [show (∑' n : ℕ+,
      eulerPositiveProbability sigma n *
        (Real.log (n : ℕ) -
          eulerPositiveLogMoment 1 sigma)) = 0 by
    rw [show (fun n : ℕ+ =>
        eulerPositiveProbability sigma n *
          (Real.log (n : ℕ) -
            eulerPositiveLogMoment 1 sigma)) =
        fun n =>
          eulerPositiveProbability sigma n *
              Real.log (n : ℕ) +
            (-eulerPositiveLogMoment 1 sigma) *
              eulerPositiveProbability sigma n by
      funext n
      ring]
    rw [Summable.tsum_add
      (by simpa only [pow_one] using
        summable_eulerPositiveLogMoment 1 hsigma)
      ((summable_eulerPositiveProbability hsigma).mul_left _),
      tsum_mul_left]
    rw [show (∑' n : ℕ+,
        eulerPositiveProbability sigma n *
          Real.log (n : ℕ)) =
        eulerPositiveLogMoment 1 sigma by
      unfold eulerPositiveLogMoment
      simp only [pow_one]]
    rw [tsum_eulerPositiveProbability hsigma]
    ring]
  norm_num

def eulerPositiveCriticalBoundaryParameter
    (sigma u : ℝ) : ℝ :=
  sigma + u * (sigma - 1)

theorem one_lt_eulerPositiveCriticalBoundaryParameter
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    1 < eulerPositiveCriticalBoundaryParameter sigma u := by
  unfold eulerPositiveCriticalBoundaryParameter
  nlinarith

def eulerPositiveCriticalDamping
    (sigma u : ℝ) (n : ℕ+) : ℝ :=
  Real.exp (-(u * (sigma - 1) * Real.log (n : ℕ)))

theorem eulerPositiveProbability_mul_criticalDamping
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u)
    (n : ℕ+) :
    eulerPositiveProbability sigma n *
        eulerPositiveCriticalDamping sigma u n =
      (eulerPositiveTotal
          (eulerPositiveCriticalBoundaryParameter sigma u) /
        eulerPositiveTotal sigma) *
        eulerPositiveProbability
          (eulerPositiveCriticalBoundaryParameter sigma u) n := by
  have hshift :=
    one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  have htotalSigma := (eulerPositiveTotal_pos hsigma).ne'
  have htotalShift := (eulerPositiveTotal_pos hshift).ne'
  have hnpos : (0 : ℝ) < (n : ℕ) := by positivity
  have hdamp :
      eulerPositiveCriticalDamping sigma u n =
        ((n : ℕ) : ℝ) ^ (-(u * (sigma - 1))) := by
    rw [eulerPositiveCriticalDamping,
      Real.rpow_def_of_pos hnpos]
    congr 1
    ring
  rw [eulerPositiveProbability, eulerPositiveProbability,
    eulerPositiveMass, eulerPositiveMass, hdamp]
  have hexponent :
      -sigma + -(u * (sigma - 1)) =
        -(eulerPositiveCriticalBoundaryParameter sigma u) := by
    unfold eulerPositiveCriticalBoundaryParameter
    ring
  have hpow :
      ((n : ℕ) : ℝ) ^ (-sigma) *
          ((n : ℕ) : ℝ) ^ (-(u * (sigma - 1))) =
        ((n : ℕ) : ℝ) ^
          (-(eulerPositiveCriticalBoundaryParameter sigma u)) := by
    rw [← Real.rpow_add hnpos, hexponent]
  field_simp [htotalSigma, htotalShift]
  nlinarith [hpow]

theorem tsum_eulerPositiveProbability_mul_criticalDamping
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (∑' n : ℕ+,
      eulerPositiveProbability sigma n *
        eulerPositiveCriticalDamping sigma u n) =
      eulerPositiveTotal
          (eulerPositiveCriticalBoundaryParameter sigma u) /
        eulerPositiveTotal sigma := by
  have hshift :=
    one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  rw [show (fun n : ℕ+ =>
      eulerPositiveProbability sigma n *
        eulerPositiveCriticalDamping sigma u n) =
      fun n =>
        (eulerPositiveTotal
            (eulerPositiveCriticalBoundaryParameter sigma u) /
          eulerPositiveTotal sigma) *
          eulerPositiveProbability
            (eulerPositiveCriticalBoundaryParameter sigma u) n by
    funext n
    exact eulerPositiveProbability_mul_criticalDamping
      hsigma hu n]
  rw [tsum_mul_left,
    tsum_eulerPositiveProbability hshift, mul_one]

theorem tsum_eulerPositiveProbability_mul_criticalDamping_log
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    (∑' n : ℕ+,
      eulerPositiveProbability sigma n *
        eulerPositiveCriticalDamping sigma u n *
          Real.log (n : ℕ)) =
      (eulerPositiveTotal
          (eulerPositiveCriticalBoundaryParameter sigma u) /
        eulerPositiveTotal sigma) *
        eulerPositiveLogMoment 1
          (eulerPositiveCriticalBoundaryParameter sigma u) := by
  have hshift :=
    one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  rw [show (fun n : ℕ+ =>
      eulerPositiveProbability sigma n *
          eulerPositiveCriticalDamping sigma u n *
        Real.log (n : ℕ)) =
      fun n =>
        (eulerPositiveTotal
            (eulerPositiveCriticalBoundaryParameter sigma u) /
          eulerPositiveTotal sigma) *
          (eulerPositiveProbability
              (eulerPositiveCriticalBoundaryParameter sigma u) n *
            Real.log (n : ℕ)) by
    funext n
    rw [eulerPositiveProbability_mul_criticalDamping hsigma hu n]
    ring]
  rw [tsum_mul_left]
  congr 1
  unfold eulerPositiveLogMoment
  simp only [pow_one]

/-- Full-Euler state damped in the critical logarithmic coordinate. -/
def eulerPositiveCriticalDampedStateWeight
    (sigma u : ℝ) (n : ℕ+) : ℂ :=
  (eulerPositiveCriticalDamping sigma u n : ℂ) *
    eulerPositiveStateWeight sigma n

private theorem summable_norm_sq_eulerPositiveCriticalDampedStateWeight
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    Summable (fun n : ℕ+ =>
      ‖eulerPositiveCriticalDampedStateWeight sigma u n‖ ^ 2) := by
  have hsum :=
    summable_norm_sq_eulerPositiveStateWeight hsigma
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_ hsum
  intro n
  rw [eulerPositiveCriticalDampedStateWeight, norm_mul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs,
    eulerPositiveCriticalDamping,
    abs_of_pos (Real.exp_pos _)]
  have hlog : 0 ≤ Real.log (n : ℕ) :=
    Real.log_natCast_nonneg (n : ℕ)
  have hexp :
      eulerPositiveCriticalDamping sigma u n ≤ 1 := by
    rw [eulerPositiveCriticalDamping, Real.exp_le_one_iff]
    exact neg_nonpos.mpr
      (mul_nonneg (mul_nonneg hu (sub_nonneg.mpr hsigma.le)) hlog)
  have hsq :
      eulerPositiveCriticalDamping sigma u n ^ 2 ≤ 1 := by
    have hdampPos :
        0 < eulerPositiveCriticalDamping sigma u n := by
      exact Real.exp_pos _
    nlinarith
  change eulerPositiveCriticalDamping sigma u n ^ 2 *
      ‖eulerPositiveStateWeight sigma n‖ ^ 2 ≤
    ‖eulerPositiveStateWeight sigma n‖ ^ 2
  exact mul_le_of_le_one_left (sq_nonneg _) hsq

def eulerPositiveCriticalDampedStateLp
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    EulerPositiveL2 :=
  ⟨eulerPositiveCriticalDampedStateWeight sigma u,
    HilbertSchmidt.memℓp_of_sq
      (summable_norm_sq_eulerPositiveCriticalDampedStateWeight
        hsigma hu)⟩

theorem inner_eulerPositiveFisherTangent_dampedState
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (eulerPositiveCriticalFisherTangentLp sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
      ((-2 * (sigma - 1) : ℝ) : ℂ) *
        ((eulerPositiveTotal
            (eulerPositiveCriticalBoundaryParameter sigma u) /
          eulerPositiveTotal sigma : ℝ) : ℂ) *
        ((eulerPositiveLogMoment 1
              (eulerPositiveCriticalBoundaryParameter sigma u) -
            eulerPositiveLogMoment 1 sigma : ℝ) : ℂ) := by
  rw [lp.inner_eq_tsum]
  simp only [eulerPositiveCriticalFisherTangentLp,
    eulerPositiveCriticalDampedStateLp, RCLike.inner_apply]
  rw [show (∑' n : ℕ+,
      eulerPositiveCriticalDampedStateWeight sigma u n *
        (starRingEnd ℂ)
          (eulerPositiveCriticalFisherTangentWeight sigma n)) =
      ((-2 * (sigma - 1) : ℝ) : ℂ) *
        ∑' n : ℕ+,
          ((eulerPositiveProbability sigma n *
            eulerPositiveCriticalDamping sigma u n *
              (Real.log (n : ℕ) -
                eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [eulerPositiveCriticalDampedStateWeight,
      eulerPositiveCriticalFisherTangentWeight]
    simp only [map_mul, Complex.conj_ofReal]
    have hnorm :
        eulerPositiveStateWeight sigma n *
          (starRingEnd ℂ) (eulerPositiveStateWeight sigma n) =
        (eulerPositiveProbability sigma n : ℂ) := by
      calc
        _ = ((‖eulerPositiveStateWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (eulerPositiveStateWeight sigma n)
        _ = _ := by
          rw [← Complex.ofReal_pow,
            norm_eulerPositiveStateWeight_sq hsigma]
    calc
      _ = ((-2 * (sigma - 1) *
            (Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) *
          (eulerPositiveCriticalDamping sigma u n : ℂ) *
          (eulerPositiveStateWeight sigma n *
            (starRingEnd ℂ) (eulerPositiveStateWeight sigma n)) := by
        ring
      _ = _ := by
        rw [hnorm]
        push_cast
        ring]
  rw [show (∑' n : ℕ+,
      ((eulerPositiveProbability sigma n *
        eulerPositiveCriticalDamping sigma u n *
          (Real.log (n : ℕ) -
            eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ)) =
      ((∑' n : ℕ+,
        eulerPositiveProbability sigma n *
          eulerPositiveCriticalDamping sigma u n *
            (Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma) : ℝ) : ℂ) by
    exact (Complex.ofReal_tsum _).symm]
  rw [show (∑' n : ℕ+,
      eulerPositiveProbability sigma n *
        eulerPositiveCriticalDamping sigma u n *
          (Real.log (n : ℕ) -
            eulerPositiveLogMoment 1 sigma)) =
      (∑' n : ℕ+,
        eulerPositiveProbability sigma n *
          eulerPositiveCriticalDamping sigma u n *
            Real.log (n : ℕ)) -
      eulerPositiveLogMoment 1 sigma *
        ∑' n : ℕ+,
          eulerPositiveProbability sigma n *
            eulerPositiveCriticalDamping sigma u n by
    have hshift :=
      one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
    have hlog :=
      (summable_eulerPositiveLogMoment 1 hshift).mul_left
        (eulerPositiveTotal
            (eulerPositiveCriticalBoundaryParameter sigma u) /
          eulerPositiveTotal sigma)
    have hmass :=
      (summable_eulerPositiveProbability hshift).mul_left
        (eulerPositiveTotal
            (eulerPositiveCriticalBoundaryParameter sigma u) /
          eulerPositiveTotal sigma)
    have hleft : Summable (fun n : ℕ+ =>
        eulerPositiveProbability sigma n *
          eulerPositiveCriticalDamping sigma u n *
            Real.log (n : ℕ)) := by
      apply hlog.congr
      intro n
      rw [eulerPositiveProbability_mul_criticalDamping hsigma hu n]
      simp only [pow_one]
      ring
    have hright : Summable (fun n : ℕ+ =>
        eulerPositiveProbability sigma n *
          eulerPositiveCriticalDamping sigma u n) := by
      apply hmass.congr
      intro n
      rw [eulerPositiveProbability_mul_criticalDamping hsigma hu n]
    rw [show (fun n : ℕ+ =>
        eulerPositiveProbability sigma n *
          eulerPositiveCriticalDamping sigma u n *
            (Real.log (n : ℕ) -
              eulerPositiveLogMoment 1 sigma)) =
        fun n =>
          eulerPositiveProbability sigma n *
              eulerPositiveCriticalDamping sigma u n *
                Real.log (n : ℕ) -
            eulerPositiveLogMoment 1 sigma *
              (eulerPositiveProbability sigma n *
                eulerPositiveCriticalDamping sigma u n) by
      funext n
      ring]
    rw [Summable.tsum_sub hleft
      (hright.mul_left (eulerPositiveLogMoment 1 sigma)),
      tsum_mul_left]]
  rw [tsum_eulerPositiveProbability_mul_criticalDamping_log
      hsigma hu,
    tsum_eulerPositiveProbability_mul_criticalDamping hsigma hu]
  push_cast
  ring

/-- The actual full-Euler Hilbert coefficient is exactly the intrinsic
all-Euler Fisher numerator used by Gamma completion. -/
theorem inner_eulerPositiveFisherTangent_dampedState_eq_affineScore
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    inner ℂ
        (eulerPositiveCriticalFisherTangentLp sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
      eulerAffineFisherScore
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
  have hshiftReal :=
    one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  have hshiftComplex :
      1 <
        (((sigma : ℂ) +
          (u : ℂ) * ((sigma - 1 : ℝ) : ℂ))).re := by
    push_cast
    simpa [eulerPositiveCriticalBoundaryParameter] using hshiftReal
  have hoverlap :
      ((eulerPositiveTotal
          (eulerPositiveCriticalBoundaryParameter sigma u) /
        eulerPositiveTotal sigma : ℝ) : ℂ) =
      eulerAffineBoundaryOverlap
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ) := by
    rw [Complex.ofReal_div,
      ofReal_eulerPositiveTotal_eq_riemannZeta hshiftReal,
      ofReal_eulerPositiveTotal_eq_riemannZeta hsigma]
    unfold eulerAffineBoundaryOverlap
    congr 2
    norm_cast
  rw [inner_eulerPositiveFisherTangent_dampedState hsigma hu,
    hoverlap,
    eulerAffineFisherScore_eq_current_difference
      (by simpa using hsigma) hshiftComplex]
  push_cast
  rw [
    ofReal_eulerPositiveLogMoment_one_eq_infinitePrimeFlux hshiftReal,
    ofReal_eulerPositiveLogMoment_one_eq_infinitePrimeFlux hsigma]
  have hparam :
      ((eulerPositiveCriticalBoundaryParameter sigma u : ℝ) : ℂ) =
        (sigma : ℂ) +
          (u : ℂ) * ((sigma - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [eulerPositiveCriticalBoundaryParameter]
  rw [hparam]
  have heps :
      ((sigma - 1 : ℝ) : ℂ) = (sigma : ℂ) - 1 := by
    norm_num
  rw [heps]
  ring

/-- Gamma--Xi transport evaluated directly on the actual full-Euler Hilbert
tangent coefficient.  This is proof-bearing source incidence, not a scalar
coefficient inserted independently of the source vector. -/
def eulerPositiveGammaXiWardHilbertTransportAt
    (sigma u : ℝ) (hsigma : 1 < sigma) (hu : 0 ≤ u) : ℂ :=
  eulerAffineGammaXiWardTransportV
    (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
    (fun _ =>
      inner ℂ
        (eulerPositiveCriticalFisherTangentLp sigma hsigma)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu))
    (u : ℂ)

/-- The intrinsic all-Euler Hilbert tangent, Gamma seam, and Xi continuation
compose exactly: no external doubled-prime correction and no scalarized
Möbius quotient remain in the statement. -/
theorem eulerPositiveGammaXiWardHilbertTransportAt_eq_continuedSource
    {sigma u : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) :
    eulerPositiveGammaXiWardHilbertTransportAt
        sigma u hsigma hu =
      continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)) := by
  have hshiftReal :=
    one_lt_eulerPositiveCriticalBoundaryParameter hsigma hu
  have hshiftComplex :
      1 <
        (((sigma : ℂ) +
          (u : ℂ) * ((sigma - 1 : ℝ) : ℂ))).re := by
    push_cast
    simpa [eulerPositiveCriticalBoundaryParameter] using hshiftReal
  rw [eulerPositiveGammaXiWardHilbertTransportAt,
    inner_eulerPositiveFisherTangent_dampedState_eq_affineScore
      hsigma hu]
  calc
    eulerAffineGammaXiWardTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (fun _ =>
          eulerAffineFisherScore
            (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ) (u : ℂ))
        (u : ℂ) =
      eulerAffineGammaXiWardTransportV
        (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ)
        (eulerAffineFisherScore
          (sigma : ℂ) ((sigma - 1 : ℝ) : ℂ))
        (u : ℂ) := by rfl
    _ = continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          ((sigma : ℂ) +
            (u : ℂ) * ((sigma - 1 : ℝ) : ℂ))) :=
      eulerAffineGammaXiWardTransportV_eq_continuedSource
        (by simpa using hsigma) hshiftComplex
        (by exact_mod_cast (sub_ne_zero.mpr hsigma.ne'))
    _ = continuedPrimeArchSourceRelativeTrace
        (xiWardCenteredCoordinate
          (eulerPositiveCriticalBoundaryParameter sigma u : ℂ)) := by
      congr 2
      apply Complex.ext <;>
        simp [eulerPositiveCriticalBoundaryParameter]

end RHTower
