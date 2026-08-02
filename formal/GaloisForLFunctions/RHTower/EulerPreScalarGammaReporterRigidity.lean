import GaloisForLFunctions.RHTower.EulerPreScalarGammaCoPoissonReporter
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# Rigidity of the full-Euler pre-scalar Gamma reporter

For fixed `sigma > 1`, the nonnegative critical damping orbit of the normalized full-Euler state
is total in the positive-integer `ℓ²` carrier.  The proof identifies every inner-product coefficient
with an ordinary Dirichlet series.  Vanishing on the whole nonnegative orbit gives eventual
vanishing on a real half-line; L-series injectivity then kills every coordinate because the Euler
state has strictly positive weight at every positive integer.

Consequently, the division-free prime coefficient family constructed in
`EulerPreScalarGammaCoPoissonReporter` has exactly one reporter in this carrier.  That reporter is
the literal pre-scalar source, whose squared norm tends to eight.  Hence no alternate positive
same-carrier representative can compress the source to the four-unit Ward budget while preserving
all coefficients.  Any four-unit completion must change the carrier or the incidence pairing; it
cannot be obtained by selecting another vector in `EulerPositiveL2`.
-/

open Complex Filter Set
open scoped BigOperators Topology ENNReal InnerProductSpace

noncomputable section
namespace RHTower

/-- Ordinary Dirichlet coefficient attached to a positive-Euler reporter.  The coefficient at zero
is suppressed, as required by the `LSeries` convention. -/
def eulerPositiveReporterDirichletCoeff
    (sigma : ℝ) (x : EulerPositiveL2) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else
    eulerPositiveStateWeight sigma (Nat.toPNat' n) *
      (starRingEnd ℂ) (x (Nat.toPNat' n))

/-- Reporter Dirichlet coefficients are uniformly bounded by the Hilbert norm. -/
theorem norm_eulerPositiveReporterDirichletCoeff_le
    {sigma : ℝ} (hsigma : 1 < sigma) (x : EulerPositiveL2)
    {n : ℕ} (hn : n ≠ 0) :
    ‖eulerPositiveReporterDirichletCoeff sigma x n‖ ≤ ‖x‖ := by
  let p : ℕ+ := Nat.toPNat' n
  have hw := lp.norm_apply_le_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (eulerPositiveStateLp sigma hsigma) p
  change ‖eulerPositiveStateWeight sigma p‖ ≤
    ‖eulerPositiveStateLp sigma hsigma‖ at hw
  rw [norm_eulerPositiveStateLp hsigma] at hw
  have hx := lp.norm_apply_le_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) x p
  rw [eulerPositiveReporterDirichletCoeff, if_neg hn]
  change ‖eulerPositiveStateWeight sigma p *
    (starRingEnd ℂ) (x p)‖ ≤ ‖x‖
  rw [norm_mul, Complex.norm_conj]
  exact (mul_le_mul hw hx (norm_nonneg _) (by positivity)).trans_eq (one_mul _)

/-- The reporter Dirichlet series converges on a nonempty right half-plane. -/
theorem eulerPositiveReporterDirichletCoeff_abscissa_lt_top
    {sigma : ℝ} (hsigma : 1 < sigma) (x : EulerPositiveL2) :
    LSeries.abscissaOfAbsConv
        (eulerPositiveReporterDirichletCoeff sigma x) < ⊤ := by
  have hle : LSeries.abscissaOfAbsConv
      (eulerPositiveReporterDirichletCoeff sigma x) ≤ (1 : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_le_const
      ⟨‖x‖, fun n hn =>
        norm_eulerPositiveReporterDirichletCoeff_le hsigma x hn⟩
  exact hle.trans_lt (EReal.coe_lt_top 1)

private theorem eulerPositiveCriticalDamping_div_sub_one
    {sigma t : ℝ} (hsigma : 1 < sigma) (k : ℕ) :
    eulerPositiveCriticalDamping sigma (t / (sigma - 1)) (Nat.succPNat k) =
      ((k + 1 : ℕ) : ℝ) ^ (-t) := by
  have heps : sigma - 1 ≠ 0 := sub_ne_zero.mpr hsigma.ne'
  have hnpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [eulerPositiveCriticalDamping, Real.rpow_def_of_pos hnpos]
  congr 1
  rw [div_mul_cancel₀ t heps]
  simp [Nat.succ_eq_add_one]
  ring

private theorem eulerPositiveReporterDirichletTerm_eq
    {sigma t : ℝ} (hsigma : 1 < sigma)
    (x : EulerPositiveL2) (k : ℕ) :
    LSeries.term (eulerPositiveReporterDirichletCoeff sigma x) (t : ℂ) (k + 1) =
      eulerPositiveCriticalDampedStateWeight sigma (t / (sigma - 1))
          (Nat.succPNat k) *
        (starRingEnd ℂ) (x (Nat.succPNat k)) := by
  have hn : k + 1 ≠ 0 := by omega
  have hpnat : Nat.toPNat' (k + 1) = Nat.succPNat k := by
    rfl
  have hnpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hscalar :
      (1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ (t : ℂ)) =
        (eulerPositiveCriticalDamping sigma (t / (sigma - 1))
          (Nat.succPNat k) : ℂ) := by
    calc
      (1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ (t : ℂ)) =
          (((1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ t) : ℝ) : ℂ) := by
            rw [Complex.ofReal_div, Complex.ofReal_one,
              Complex.ofReal_cpow hnpos.le]
            norm_cast
      _ = ((((k + 1 : ℕ) : ℝ) ^ (-t) : ℝ) : ℂ) := by
            congr 1
            rw [Real.rpow_neg hnpos.le]
            simp only [one_div]
      _ = _ := by
            rw [eulerPositiveCriticalDamping_div_sub_one hsigma k]
  rw [LSeries.term_of_ne_zero hn,
    eulerPositiveReporterDirichletCoeff, if_neg hn, hpnat,
    eulerPositiveCriticalDampedStateWeight]
  change
    eulerPositiveStateWeight sigma (Nat.succPNat k) *
          (starRingEnd ℂ) (x (Nat.succPNat k)) /
            (((k + 1 : ℕ) : ℂ) ^ (t : ℂ)) =
      (eulerPositiveCriticalDamping sigma (t / (sigma - 1))
          (Nat.succPNat k) : ℂ) *
        eulerPositiveStateWeight sigma (Nat.succPNat k) *
          (starRingEnd ℂ) (x (Nat.succPNat k))
  rw [show
      eulerPositiveStateWeight sigma (Nat.succPNat k) *
          (starRingEnd ℂ) (x (Nat.succPNat k)) /
            (((k + 1 : ℕ) : ℂ) ^ (t : ℂ)) =
        (eulerPositiveStateWeight sigma (Nat.succPNat k) *
          (starRingEnd ℂ) (x (Nat.succPNat k))) *
            ((1 : ℂ) / (((k + 1 : ℕ) : ℂ) ^ (t : ℂ))) by ring,
    hscalar]
  ring

/-- On the absolutely convergent half-line, the reporter L-series is exactly its coefficient
against the critical damping orbit. -/
theorem LSeries_eulerPositiveReporterDirichletCoeff_eq_inner
    {sigma t : ℝ} (hsigma : 1 < sigma) (ht : 2 ≤ t)
    (x : EulerPositiveL2) :
    LSeries (eulerPositiveReporterDirichletCoeff sigma x) (t : ℂ) =
      inner ℂ x
        (eulerPositiveCriticalDampedStateLp sigma (t / (sigma - 1)) hsigma
          (div_nonneg (by linarith) (sub_nonneg.mpr hsigma.le))) := by
  have hab_le : LSeries.abscissaOfAbsConv
      (eulerPositiveReporterDirichletCoeff sigma x) ≤ (1 : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_le_const
      ⟨‖x‖, fun n hn =>
        norm_eulerPositiveReporterDirichletCoeff_le hsigma x hn⟩
  have hsum : LSeriesSummable
      (eulerPositiveReporterDirichletCoeff sigma x) (t : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (hab_le.trans_lt (by exact_mod_cast (show (1 : ℝ) < t by linarith)))
  rw [LSeries, hsum.tsum_eq_zero_add, LSeries.term_zero, zero_add,
    lp.inner_eq_tsum]
  simp only [eulerPositiveCriticalDampedStateLp, RCLike.inner_apply]
  calc
    (∑' k : ℕ,
      LSeries.term (eulerPositiveReporterDirichletCoeff sigma x) (t : ℂ) (k + 1)) =
        ∑' k : ℕ,
          eulerPositiveCriticalDampedStateWeight sigma (t / (sigma - 1))
              (Nat.succPNat k) *
            (starRingEnd ℂ) (x (Nat.succPNat k)) := by
      apply tsum_congr
      intro k
      exact eulerPositiveReporterDirichletTerm_eq hsigma x k
    _ = ∑' p : ℕ+,
          eulerPositiveCriticalDampedStateWeight sigma (t / (sigma - 1)) p *
            (starRingEnd ℂ) (x p) := by
      symm
      simpa using Equiv.pnatEquivNat.tsum_eq
        (fun k : ℕ =>
          eulerPositiveCriticalDampedStateWeight sigma (t / (sigma - 1))
              (Nat.succPNat k) *
            (starRingEnd ℂ) (x (Nat.succPNat k)))

/-- **Totality of the full-Euler damping orbit.**  A vector orthogonal to every nonnegative
critical damping of the full-Euler state is zero. -/
theorem eulerPositiveCriticalDampedState_total
    {sigma : ℝ} (hsigma : 1 < sigma) (x : EulerPositiveL2)
    (horth : ∀ (u : ℝ) (hu : 0 ≤ u),
      inner ℂ x (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) = 0) :
    x = 0 := by
  let a := eulerPositiveReporterDirichletCoeff sigma x
  have hab : LSeries.abscissaOfAbsConv a < ⊤ := by
    exact eulerPositiveReporterDirichletCoeff_abscissa_lt_top hsigma x
  have hzero : (fun t : ℝ => LSeries a t) =ᶠ[atTop] (fun _ => 0) := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    rw [show a = eulerPositiveReporterDirichletCoeff sigma x by rfl,
      LSeries_eulerPositiveReporterDirichletCoeff_eq_inner hsigma ht x,
      horth]
  have hacoeff : ∀ n ≠ 0, a n = 0 :=
    (LSeries_eventually_eq_zero_iff'.mp hzero).resolve_right hab.ne
  apply lp.ext
  funext p
  have hpzero := hacoeff (p : ℕ) (by positivity)
  have hpPNat : Nat.toPNat' (p : ℕ) = p := by
    apply Subtype.ext
    simp
  dsimp only [a, eulerPositiveReporterDirichletCoeff] at hpzero
  rw [if_neg (by positivity), hpPNat] at hpzero
  have hwpos : 0 < Real.sqrt (eulerPositiveProbability sigma p) := by
    exact Real.sqrt_pos.2 (div_pos (eulerPositiveMass_pos sigma p)
      (eulerPositiveTotal_pos hsigma))
  have hwne : eulerPositiveStateWeight sigma p ≠ 0 := by
    unfold eulerPositiveStateWeight
    exact_mod_cast hwpos.ne'
  have hxstar : (starRingEnd ℂ) (x p) = 0 :=
    (mul_eq_zero.mp hpzero).resolve_left hwne
  simpa using congrArg (starRingEnd ℂ) hxstar

/-- The complete nonnegative damping coefficient family separates reporters. -/
theorem eq_of_inner_eulerPositiveCriticalDampedState_eq
    {sigma : ℝ} (hsigma : 1 < sigma) {x y : EulerPositiveL2}
    (hcoeff : ∀ (u : ℝ) (hu : 0 ≤ u),
      inner ℂ x (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
        inner ℂ y (eulerPositiveCriticalDampedStateLp sigma u hsigma hu)) :
    x = y := by
  have hzero : ∀ (u : ℝ) (hu : 0 ≤ u),
      inner ℂ (x - y)
        (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) = 0 := by
    intro u hu
    rw [inner_sub_left, hcoeff u hu, sub_self]
  exact sub_eq_zero.mp
    (eulerPositiveCriticalDampedState_total hsigma (x - y) hzero)

/-- The literal pre-scalar Gamma source is the unique reporter of its full coefficient family in
the positive-Euler Hilbert carrier. -/
theorem eq_eulerPositivePreScalarGammaSource_of_same_coefficients
    {sigma : ℝ} (hsigma : 1 < sigma) (y : EulerPositiveL2)
    (hcoeff : ∀ (u : ℝ) (hu : 0 ≤ u),
      inner ℂ y (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
        inner ℂ (eulerPositivePreScalarGammaSource sigma hsigma)
          (eulerPositiveCriticalDampedStateLp sigma u hsigma hu)) :
    y = eulerPositivePreScalarGammaSource sigma hsigma :=
  eq_of_inner_eulerPositiveCriticalDampedState_eq hsigma hcoeff

/-- Every same-carrier reporter of the full pre-scalar coefficient family has the exact literal
source energy. -/
theorem norm_sq_eulerPositiveReporter_eq_of_same_coefficients
    {sigma : ℝ} (hsigma : 1 < sigma) (y : EulerPositiveL2)
    (hcoeff : ∀ (u : ℝ) (hu : 0 ≤ u),
      inner ℂ y (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
        inner ℂ (eulerPositivePreScalarGammaSource sigma hsigma)
          (eulerPositiveCriticalDampedStateLp sigma u hsigma hu)) :
    ‖y‖ ^ 2 = 4 * (sigma - 1) ^ 2 * eulerPositiveLogMoment 2 sigma := by
  rw [eq_eulerPositivePreScalarGammaSource_of_same_coefficients hsigma y hcoeff,
    norm_eulerPositivePreScalarGammaSource_sq hsigma]

/-- **No four-unit same-carrier compression.**  Near the critical boundary, every positive-Euler
reporter preserving all division-free prime coefficients has squared norm strictly greater than
four. -/
theorem eventually_no_four_unit_eulerPositiveReporter_with_same_coefficients :
    ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
      if hsigma : 1 < sigma then
        ∀ y : EulerPositiveL2,
          (∀ (u : ℝ) (hu : 0 ≤ u),
            inner ℂ y
                (eulerPositiveCriticalDampedStateLp sigma u hsigma hu) =
              inner ℂ (eulerPositivePreScalarGammaSource sigma hsigma)
                (eulerPositiveCriticalDampedStateLp sigma u hsigma hu)) →
            4 < ‖y‖ ^ 2
      else False := by
  filter_upwards
    [eventually_four_lt_norm_eulerPositivePreScalarGammaSource_sq]
      with sigma hfour
  split_ifs with hsigma
  · intro y hcoeff
    rw [eq_eulerPositivePreScalarGammaSource_of_same_coefficients hsigma y hcoeff]
    simpa [hsigma] using hfour
  · rw [dif_neg hsigma] at hfour
    exact hfour

end RHTower
