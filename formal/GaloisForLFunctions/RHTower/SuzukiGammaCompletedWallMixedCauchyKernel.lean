import GaloisForLFunctions.RHTower.SuzukiWardAtomicContinuousLightWeld

/-!
# Mixed Cauchy covariance in the literal completed Suzuki wall

The finite prime wall is made from anchored one-depth atoms, while the regular
screw wall is made from two-depth secants.  This file isolates their actual
mixed Cauchy covariance.  It deliberately does not replace that pair by the
secant--secant covariance used for the raw reporter packet.
-/

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Literal anchored prime atom at source lag `p`. -/
def suzukiCauchyAnchoredWallAtom (p t : ℝ) : ℂ :=
  1 - suzukiCauchyWallPhase (-p) t

/-- Literal two-depth regular-screw secant at source lag `q`. -/
def suzukiCauchyWallSecantAtLag (q t : ℝ) : ℂ :=
  suzukiCauchyWallPhase (-q) t - suzukiCauchyWallPhase (-2 * q) t

/-- Cauchy covariance of the actual anchored atom against the actual secant. -/
def suzukiCauchyAnchoredSecantWallGram (p q : ℝ) : ℂ :=
  suzukiCauchyWallPhaseInner 0 (-q) -
    suzukiCauchyWallPhaseInner 0 (-2 * q) -
    suzukiCauchyWallPhaseInner (-p) (-q) +
      suzukiCauchyWallPhaseInner (-p) (-2 * q)

/-- Real form of the literal anchored--secant Cauchy covariance. -/
def suzukiCauchyAnchoredSecantGram (p q : ℝ) : ℝ :=
  Real.exp (-|q| / 2) - Real.exp (-|2 * q| / 2) -
    Real.exp (-|p - q| / 2) + Real.exp (-|p - 2 * q| / 2)

/-- The finite prime side of the literal completed wall is a finite sum of
anchored atoms at every real Cauchy height. -/
theorem suzukiUnitRieszPrimeWardWall_ofReal_eq_sum_anchored
    (N : ℕ) (t : ℝ) :
    suzukiUnitRieszPrimeWardWall N (t : ℂ) =
      ∑ k ∈ Finset.Icc 2 N,
        (ArithmeticFunction.vonMangoldt k / Real.sqrt N : ℂ) *
          suzukiCauchyAnchoredWallAtom (Real.log N - Real.log k) t := by
  rw [suzukiUnitRieszPrimeWardWall]
  apply Finset.sum_congr rfl
  intro k hk
  rw [suzukiCauchyAnchoredWallAtom,
    suzukiCauchyWallPhaseComplex_ofReal]

/-- The regular-screw integrand is a two-depth secant at real Cauchy height. -/
theorem suzukiUnitRieszReporterWallSecant_ofReal_eq_secantAtLag
    (H h t : ℝ) :
    suzukiUnitRieszReporterWallSecant H h (t : ℂ) =
      suzukiCauchyWallSecantAtLag (H - h) t := by
  rw [suzukiUnitRieszReporterWallSecant,
    suzukiCauchyWallPhaseComplex_two_mul,
    suzukiCauchyWallPhaseComplex_ofReal,
    suzukiCauchyWallPhaseComplex_ofReal,
    suzukiCauchyWallSecantAtLag]
  congr 2 <;> ring

/-- The continuous regular side of the literal completed wall is an integral
of the same two-depth secants that enter the mixed covariance. -/
theorem suzukiUnitRieszRegularWardWall_ofReal_eq_integral_secantAtLag
    (H t : ℝ) :
    suzukiUnitRieszRegularWardWall H (t : ℂ) =
      ∫ h in _root_.RHTower.unitRieszSuzukiBase..H,
        suzukiCauchyWallSecantAtLag (H - h) t *
          (screwRegularKernel h : ℂ) := by
  rw [suzukiUnitRieszRegularWardWall]
  apply intervalIntegral.integral_congr
  intro h hh
  change suzukiUnitRieszReporterWallSecant H h (t : ℂ) *
      (screwRegularKernel h : ℂ) =
    suzukiCauchyWallSecantAtLag (H - h) t *
      (screwRegularKernel h : ℂ)
  rw [suzukiUnitRieszReporterWallSecant_ofReal_eq_secantAtLag]

/-- Cauchy averaging of literal prime and regular wall shapes is the mixed
kernel, rather than the reporter's secant--secant kernel. -/
theorem suzukiCauchyAnchoredSecantWallGram_eq
    (p q : ℝ) :
    suzukiCauchyAnchoredSecantWallGram p q =
      (suzukiCauchyAnchoredSecantGram p q : ℂ) := by
  rw [suzukiCauchyAnchoredSecantWallGram,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq,
    suzukiCauchyWallPhaseInner_eq]
  have hq : |0 - -q| = |q| := by ring
  have htwoq : |0 - -2 * q| = |2 * q| := by ring
  have hpq : |-p - -q| = |p - q| := by
    rw [show -p - -q = -(p - q) by ring, abs_neg]
  have hptwoq : |-p - -2 * q| = |p - 2 * q| := by
    rw [show -p - -2 * q = -(p - 2 * q) by ring, abs_neg]
  rw [hq, htwoq, hpq, hptwoq]
  simp only [suzukiCauchyAnchoredSecantGram]
  push_cast
  ring

/-- On the source-faithful lower wedge `2q ≤ p`, the mixed covariance is
nonnegative.  Thus the completed prime-minus-regular cross term has the
favourable sign there. -/
theorem suzukiCauchyAnchoredSecantGram_nonneg_of_two_mul_le
    {p q : ℝ} (hq : 0 ≤ q) (hpq : 2 * q ≤ p) :
    0 ≤ suzukiCauchyAnchoredSecantGram p q := by
  have hpq' : q ≤ p := by linarith
  have hp_sub_q : 0 ≤ p - q := sub_nonneg.mpr hpq'
  have hp_sub_twoq : 0 ≤ p - 2 * q := sub_nonneg.mpr hpq
  have htwoq : 0 ≤ 2 * q := by linarith
  have hfirst : 0 ≤ Real.exp (-q / 2) - Real.exp (-q) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith
  have hsecond : 0 ≤
      Real.exp (-(p - 2 * q) / 2) - Real.exp (-(p - q) / 2) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    linarith
  rw [suzukiCauchyAnchoredSecantGram,
    abs_of_nonneg hq,
    abs_of_nonneg htwoq,
    abs_of_nonneg hp_sub_q,
    abs_of_nonneg hp_sub_twoq]
  have htwo : Real.exp (-(2 * q) / 2) = Real.exp (-q) := by
    congr 1
    ring
  rw [htwo]
  linarith

/-- On the opposite cone `p ≤ q`, the literal mixed covariance has an exact
factorization.  This is the obstruction side of the source geometry: deeper
regular lags cannot furnish a favourable completed cross term for an earlier
prime atom. -/
theorem suzukiCauchyAnchoredSecantGram_eq_factor_of_le
    {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    suzukiCauchyAnchoredSecantGram p q =
      (1 - Real.exp (-q / 2)) *
        (Real.exp (-q / 2) - Real.exp (-(q - p) / 2)) := by
  have hq : 0 ≤ q := hp.trans hpq
  have htwoq : 0 ≤ 2 * q := by linarith
  have hp_sub_q : p - q ≤ 0 := by linarith
  have hp_sub_twoq : p - 2 * q ≤ 0 := by linarith
  have htwo : Real.exp (-(2 * q) / 2) = Real.exp (-q) := by
    congr 1
    ring
  have hsq : Real.exp (-q) = Real.exp (-q / 2) * Real.exp (-q / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hthird : -(-(p - q)) / 2 = -(q - p) / 2 := by ring
  have hfourth : -(-(p - 2 * q)) / 2 = -(2 * q - p) / 2 := by ring
  have hsplit : Real.exp (-(2 * q - p) / 2) =
      Real.exp (-(q - p) / 2) * Real.exp (-q / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [suzukiCauchyAnchoredSecantGram,
    abs_of_nonneg hq,
    abs_of_nonneg htwoq,
    abs_of_nonpos hp_sub_q,
    abs_of_nonpos hp_sub_twoq,
    htwo, hthird, hfourth, hsplit, hsq]
  ring

/-- Every nonzero earlier prime lag sees an adverse mixed cross contribution
from every regular lag at least as deep. -/
theorem suzukiCauchyAnchoredSecantGram_neg_of_pos_le
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    suzukiCauchyAnchoredSecantGram p q < 0 := by
  rw [suzukiCauchyAnchoredSecantGram_eq_factor_of_le hp.le hpq]
  have hq : 0 < q := hp.trans_le hpq
  have hone : 0 < 1 - Real.exp (-q / 2) := by
    apply sub_pos.mpr
    have : Real.exp (-q / 2) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by linarith)
    simpa using this
  have hsecond : Real.exp (-q / 2) - Real.exp (-(q - p) / 2) < 0 := by
    apply sub_neg.mpr
    apply Real.exp_lt_exp.mpr
    linarith
  exact mul_neg_of_pos_of_neg hone hsecond

/-- Transition polynomial for the literal anchored--secant covariance.  The
coordinate is `q = p / 2 + r`; unlike the reporter-secant polynomial, its
prime factor is anchored at depth zero. -/
def suzukiCauchyAnchoredSecantTransitionPolynomial (p r : ℝ) : ℝ :=
  (1 - Real.exp (-p / 2)) * Real.exp (-3 * r / 2) +
    Real.exp (-p / 4) * (Real.exp (-r) - 1)

/-- Exact transition factorization for the literal mixed covariance. -/
theorem suzukiCauchyAnchoredSecant_transition_factorization
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) (hrp : r ≤ p / 2) :
    Real.exp (-r / 2) *
        suzukiCauchyAnchoredSecantGram p (p / 2 + r) =
      suzukiCauchyAnchoredSecantTransitionPolynomial p r := by
  have hq : 0 ≤ p / 2 + r := by linarith
  have htwoq : 0 ≤ 2 * (p / 2 + r) := by linarith
  have hmid : 0 ≤ p - (p / 2 + r) := by linarith
  have hlast : p - 2 * (p / 2 + r) ≤ 0 := by linarith
  have e1 : Real.exp (-(p / 2 + r) / 2) =
      Real.exp (-p / 4) * Real.exp (-r / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e2 : Real.exp (-(2 * (p / 2 + r)) / 2) =
      Real.exp (-p / 2) * Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e3 : Real.exp (-(p - (p / 2 + r)) / 2) =
      Real.exp (-p / 4) * Real.exp (r / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have e4 : Real.exp (-(-(p - 2 * (p / 2 + r))) / 2) =
      Real.exp (-r) := by
    congr 1
    ring
  have ehalf_sq : Real.exp (-r / 2) * Real.exp (-r / 2) = Real.exp (-r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have ehalf_cancel : Real.exp (-r / 2) * Real.exp (r / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show -r / 2 + r / 2 = 0 by ring, Real.exp_zero]
  have ethree : Real.exp (-r / 2) * Real.exp (-r) = Real.exp (-3 * r / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [suzukiCauchyAnchoredSecantGram,
    abs_of_nonneg hq,
    abs_of_nonneg htwoq,
    abs_of_nonneg hmid,
    abs_of_nonpos hlast,
    e1, e2, e3, e4,
    suzukiCauchyAnchoredSecantTransitionPolynomial]
  calc
    Real.exp (-r / 2) *
        (Real.exp (-p / 4) * Real.exp (-r / 2) -
          Real.exp (-p / 2) * Real.exp (-r) -
          Real.exp (-p / 4) * Real.exp (r / 2) + Real.exp (-r)) =
      Real.exp (-p / 4) * (Real.exp (-r / 2) * Real.exp (-r / 2)) -
        Real.exp (-p / 2) * (Real.exp (-r / 2) * Real.exp (-r)) -
        Real.exp (-p / 4) * (Real.exp (-r / 2) * Real.exp (r / 2)) +
          Real.exp (-r / 2) * Real.exp (-r) := by ring
    _ = Real.exp (-p / 4) * Real.exp (-r) -
        Real.exp (-p / 2) * Real.exp (-3 * r / 2) -
        Real.exp (-p / 4) * 1 + Real.exp (-3 * r / 2) := by
          rw [ehalf_sq, ehalf_cancel, ethree]
    _ = _ := by ring

theorem continuous_suzukiCauchyAnchoredSecantTransitionPolynomial
    (p : ℝ) :
    Continuous (suzukiCauchyAnchoredSecantTransitionPolynomial p) := by
  unfold suzukiCauchyAnchoredSecantTransitionPolynomial
  fun_prop

/-- The literal mixed transition polynomial is strictly decreasing at every
positive prime lag. -/
theorem strictAnti_suzukiCauchyAnchoredSecantTransitionPolynomial
    {p : ℝ} (hp : 0 < p) :
    StrictAnti (suzukiCauchyAnchoredSecantTransitionPolynomial p) := by
  intro a b hab
  have hcoef : 0 < 1 - Real.exp (-p / 2) := by
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hfirst : Real.exp (-3 * b / 2) < Real.exp (-3 * a / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hsecond : Real.exp (-b) < Real.exp (-a) :=
    Real.exp_lt_exp.mpr (by linarith)
  have hfirst' :
      (1 - Real.exp (-p / 2)) * Real.exp (-3 * b / 2) <
        (1 - Real.exp (-p / 2)) * Real.exp (-3 * a / 2) :=
    mul_lt_mul_of_pos_left hfirst hcoef
  have hsecond' :
      Real.exp (-p / 4) * (Real.exp (-b) - 1) <
        Real.exp (-p / 4) * (Real.exp (-a) - 1) := by
    apply mul_lt_mul_of_pos_left
    · linarith
    · exact Real.exp_pos _
  unfold suzukiCauchyAnchoredSecantTransitionPolynomial
  linarith

theorem suzukiCauchyAnchoredSecantTransitionPolynomial_zero
    (p : ℝ) :
    suzukiCauchyAnchoredSecantTransitionPolynomial p 0 =
      1 - Real.exp (-p / 2) := by
  rw [suzukiCauchyAnchoredSecantTransitionPolynomial]
  norm_num

/-- The literal midpoint lag is strictly favourable for every positive prime
lag.  This is an interior source coordinate, not an endpoint artefact. -/
theorem suzukiCauchyAnchoredSecantGram_half_pos
    {p : ℝ} (hp : 0 < p) :
    0 < suzukiCauchyAnchoredSecantGram p (p / 2) := by
  have hfactor := suzukiCauchyAnchoredSecant_transition_factorization
    (p := p) (r := 0) hp.le (by norm_num) (by linarith)
  norm_num at hfactor
  rw [hfactor, suzukiCauchyAnchoredSecantTransitionPolynomial_zero]
  apply sub_pos.mpr
  exact Real.exp_lt_one_iff.mpr (by linarith)

/-- Every genuine finite-prime atom has a strictly favourable regular-screw
midpoint inside the literal unit-Riesz aperture.  Thus the favourable mixed
cone is physically present in the actual completed source; constructing a
uniform mass coupling inside it remains the quantitative problem. -/
theorem exists_suzukiUnitRieszActualPrimeRegularFavourableMidpoint
    {N k : ℕ} (hk2 : 2 ≤ k) (hkN : k < N) :
    ∃ h ∈ Set.Ioo _root_.RHTower.unitRieszSuzukiBase (Real.log N),
      0 < suzukiCauchyAnchoredSecantGram
        (Real.log N - Real.log k) (Real.log N - h) := by
  have hkpos : 0 < (k : ℝ) := by positivity
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (lt_trans (by omega : 0 < k) hkN)
  have hkNreal : (k : ℝ) < N := by exact_mod_cast hkN
  have hlog : Real.log (k : ℝ) < Real.log N :=
    Real.strictMonoOn_log hkpos hNpos hkNreal
  have hp : 0 < Real.log N - Real.log k := by linarith
  refine ⟨(Real.log N + Real.log k) / 2, ?_, ?_⟩
  · constructor
    · have hbase : _root_.RHTower.unitRieszSuzukiBase < Real.log k :=
        _root_.RHTower.unitRieszSuzukiBase_lt_log_of_two_le hk2
      linarith
    · linarith
  · have hlag : Real.log N - (Real.log N + Real.log k) / 2 =
        (Real.log N - Real.log k) / 2 := by ring
    rw [hlag]
    exact suzukiCauchyAnchoredSecantGram_half_pos hp

theorem suzukiCauchyAnchoredSecantTransitionPolynomial_half_neg
    {p : ℝ} (hp : 0 < p) :
    suzukiCauchyAnchoredSecantTransitionPolynomial p (p / 2) < 0 := by
  have hfactor := suzukiCauchyAnchoredSecant_transition_factorization
    (p := p) (r := p / 2) hp.le (by linarith) (by linarith)
  have hfactor' :
      Real.exp (-(p / 2) / 2) * suzukiCauchyAnchoredSecantGram p p =
        suzukiCauchyAnchoredSecantTransitionPolynomial p (p / 2) := by
    convert hfactor using 1; ring
  rw [← hfactor']
  exact mul_neg_of_pos_of_neg (Real.exp_pos _)
    (suzukiCauchyAnchoredSecantGram_neg_of_pos_le hp le_rfl)

/-- Every positive anchored prime lag has one and only one regular lag in the
literal transition band where its mixed Cauchy covariance vanishes. -/
theorem existsUnique_suzukiCauchyAnchoredSecantTransitionResidual
    (p : {p : ℝ // 0 < p}) :
    ∃! r : ℝ, r ∈ Set.Ioo 0 (p.1 / 2) ∧
      suzukiCauchyAnchoredSecantTransitionPolynomial p.1 r = 0 := by
  have hleft : 0 < suzukiCauchyAnchoredSecantTransitionPolynomial p.1 0 := by
    rw [suzukiCauchyAnchoredSecantTransitionPolynomial_zero]
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by linarith [p.2])
  have hright : suzukiCauchyAnchoredSecantTransitionPolynomial p.1 (p.1 / 2) < 0 :=
    suzukiCauchyAnchoredSecantTransitionPolynomial_half_neg p.2
  have hcont : ContinuousOn (suzukiCauchyAnchoredSecantTransitionPolynomial p.1)
      (Set.Icc 0 (p.1 / 2)) :=
    (continuous_suzukiCauchyAnchoredSecantTransitionPolynomial p.1).continuousOn
  obtain ⟨r, hr, hzero⟩ := intermediate_value_Ioo'
    (show (0 : ℝ) ≤ p.1 / 2 by linarith [p.2]) hcont ⟨hright, hleft⟩
  refine ⟨r, ⟨hr, hzero⟩, fun s hs => ?_⟩
  exact (strictAnti_suzukiCauchyAnchoredSecantTransitionPolynomial p.2).injective
    (hs.2.trans hzero.symm)

/-- Canonical regular-lag residual which nulls the literal anchored--secant
covariance of one positive prime lag. -/
def suzukiCauchyAnchoredSecantTransitionResidual
    (p : {p : ℝ // 0 < p}) : ℝ :=
  Classical.choose (existsUnique_suzukiCauchyAnchoredSecantTransitionResidual p)

theorem suzukiCauchyAnchoredSecantTransitionResidual_mem
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantTransitionResidual p ∈ Set.Ioo 0 (p.1 / 2) :=
  (Classical.choose_spec (existsUnique_suzukiCauchyAnchoredSecantTransitionResidual p)).1.1

theorem suzukiCauchyAnchoredSecantTransitionResidual_eq_zero
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantTransitionPolynomial p.1
      (suzukiCauchyAnchoredSecantTransitionResidual p) = 0 :=
  (Classical.choose_spec (existsUnique_suzukiCauchyAnchoredSecantTransitionResidual p)).1.2

/-- Canonical regular lag at which one positive prime atom has zero literal
mixed covariance. -/
def suzukiCauchyAnchoredSecantTransitionLag
    (p : {p : ℝ // 0 < p}) : ℝ :=
  p.1 / 2 + suzukiCauchyAnchoredSecantTransitionResidual p

theorem suzukiCauchyAnchoredSecantTransitionLag_mem
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantTransitionLag p ∈ Set.Ioo (p.1 / 2) p.1 := by
  have hr := suzukiCauchyAnchoredSecantTransitionResidual_mem p
  constructor
  · dsimp [suzukiCauchyAnchoredSecantTransitionLag]
    linarith [hr.1]
  · dsimp [suzukiCauchyAnchoredSecantTransitionLag]
    linarith [hr.2]

theorem suzukiCauchyAnchoredSecantGram_transitionLag_eq_zero
    (p : {p : ℝ // 0 < p}) :
    suzukiCauchyAnchoredSecantGram p.1
      (suzukiCauchyAnchoredSecantTransitionLag p) = 0 := by
  let r := suzukiCauchyAnchoredSecantTransitionResidual p
  have hr := suzukiCauchyAnchoredSecantTransitionResidual_mem p
  have hfactor := suzukiCauchyAnchoredSecant_transition_factorization
    (p := p.1) (r := r) p.2.le hr.1.le hr.2.le
  have hroot := suzukiCauchyAnchoredSecantTransitionResidual_eq_zero p
  change Real.exp (-r / 2) *
      suzukiCauchyAnchoredSecantGram p.1 (p.1 / 2 + r) =
    suzukiCauchyAnchoredSecantTransitionPolynomial p.1 r at hfactor
  rw [hroot] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left (Real.exp_ne_zero _)

/-- Signed prime-minus-regular mixed cross contribution. -/
def suzukiGammaCompletedWallSignedMixedCross
    (c d p q : ℝ) : ℝ :=
  -(c * suzukiCauchyAnchoredSecantGram p q * d)

/-- The literal completed mixed cross contribution is nonpositive on the
lower wedge when both source masses are positive. -/
theorem suzukiGammaCompletedWallSignedMixedCross_nonpos_of_two_mul_le
    {c d p q : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hq : 0 ≤ q) (hpq : 2 * q ≤ p) :
    suzukiGammaCompletedWallSignedMixedCross c d p q ≤ 0 := by
  rw [suzukiGammaCompletedWallSignedMixedCross]
  have hkernel : 0 ≤ suzukiCauchyAnchoredSecantGram p q :=
    suzukiCauchyAnchoredSecantGram_nonneg_of_two_mul_le hq hpq
  nlinarith [mul_nonneg (mul_nonneg hc hkernel) hd]

/-- The opposite cone is strictly adverse for strictly positive literal source
masses: subtracting the regular wall increases the mixed Cauchy energy. -/
theorem suzukiGammaCompletedWallSignedMixedCross_pos_of_pos_le
    {c d p q : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hp : 0 < p) (hpq : p ≤ q) :
    0 < suzukiGammaCompletedWallSignedMixedCross c d p q := by
  rw [suzukiGammaCompletedWallSignedMixedCross]
  apply neg_pos.mpr
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hc
      (suzukiCauchyAnchoredSecantGram_neg_of_pos_le hp hpq)) hd

end

end GaloisForLFunctions.RHTower
