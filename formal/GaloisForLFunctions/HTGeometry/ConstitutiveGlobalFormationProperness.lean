import Mathlib
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.LawCommutator
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DepthDilation

/-!
# Global formation properness

This module proves a source-level selection mechanism.  The abelian-zeta-gas law commutator
creates a central formation, depth dilation amplifies its size, and one canonical source reporter
has work diverging along every nonzero scale orbit.  Consequently bounded work on the complete
scale orbit selects exactly the neutral formation.

The capstone is pre-zero and contains no Riemann-hypothesis assumption or conclusion.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped commutatorElement

noncomputable section

/-- Ambient source-depth scaling on the temperature coordinate. -/
def depthScale (d : ℝ) (θ : ℝ × ℝ) : ℝ × ℝ := (d * θ.1, θ.2)

/-- Depth scaling conjugates a temperature formation of size `u` to size `d * u`. -/
theorem depthScale_tempTranslate (d u : ℝ) (θ : ℝ × ℝ) :
    depthScale d (AbelianZetaGas.tempTranslate u θ) =
      AbelianZetaGas.tempTranslate (d * u) (depthScale d θ) := by
  ext <;> simp [depthScale]
  ring

/-- The ambient scaling agrees with the literal depth-dilation source operation. -/
theorem depthScale_eq_depthDilate (θ : AbelianZetaParameters) (d : ℕ) (hd : 1 ≤ d) :
    depthScale (d : ℝ) (θ.sigma, θ.tau) =
      ((θ.depthDilate d hd).sigma, (θ.depthDilate d hd).tau) := by
  simp [depthScale]

/-- Least-prime, least-depth source mode. -/
def leastMode : AbelianZetaMode := (⟨2, Nat.prime_two⟩, 0)

@[simp] theorem leastMode_prime : (leastMode.1 : ℕ) = 2 := rfl

@[simp] theorem leastMode_depth : AbelianZetaMode.depth leastMode = 1 := rfl

/-- Parameter-level form of the central fugacity formation. -/
def fugacityShiftParameters (θ : AbelianZetaParameters) (u : ℝ) (hu : 0 ≤ u) :
    AbelianZetaParameters where
  sigma := θ.sigma
  tau := θ.tau + u
  sigma_pos := θ.sigma_pos
  tau_nonneg := add_nonneg θ.tau_nonneg hu

@[simp] theorem fugacityShiftParameters_sigma
    (θ : AbelianZetaParameters) (u : ℝ) (hu : 0 ≤ u) :
    (fugacityShiftParameters θ u hu).sigma = θ.sigma := rfl

@[simp] theorem fugacityShiftParameters_tau
    (θ : AbelianZetaParameters) (u : ℝ) (hu : 0 ≤ u) :
    (fugacityShiftParameters θ u hu).tau = θ.tau + u := rfl

/-- Exact least-mode source ratio. -/
theorem leastMode_ratio (θ : AbelianZetaParameters) :
    θ.ratio leastMode = (2 : ℝ) ^ (-(θ.sigma + θ.tau)) := by
  rw [AbelianZetaParameters.ratio, AbelianZetaParameters.exponent]
  simp [leastMode]

/-- The generated central formation multiplies the least-mode ratio by `2 ^ (-u)`. -/
theorem leastMode_ratio_fugacityShift (θ : AbelianZetaParameters) (u : ℝ) (hu : 0 ≤ u) :
    (fugacityShiftParameters θ u hu).ratio leastMode = θ.ratio leastMode * 2 ^ (-u) := by
  rw [leastMode_ratio, leastMode_ratio]
  simp only [fugacityShiftParameters_sigma, fugacityShiftParameters_tau]
  rw [show -(θ.sigma + (θ.tau + u)) = -(θ.sigma + θ.tau) + -u by ring,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

/-- Source ratio after a formation displacement. -/
def sourceRatio (x u : ℝ) : ℝ := 2 ^ (-(x + u))

/-- Exact log-odds work of the least-mode Boolean reporter. -/
def reporterWork (q u : ℝ) : ℝ :=
  let r := q * 2 ^ (-u)
  (q - r) * (u * Real.log 2 + Real.log ((1 - r) / (1 - q)))

theorem rpow_two_neg_nonneg (u : ℝ) : 0 ≤ (2 : ℝ) ^ (-u) :=
  Real.rpow_nonneg (by norm_num) _

theorem rpow_two_neg_le_one {u : ℝ} (hu : 0 ≤ u) : (2 : ℝ) ^ (-u) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (neg_nonpos.mpr hu)

theorem rpow_two_neg_le_half {u : ℝ} (hu : 1 ≤ u) : (2 : ℝ) ^ (-u) ≤ 1 / 2 := by
  calc (2 : ℝ) ^ (-u) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

theorem shifted_ratio_le {q u : ℝ} (hq : 0 ≤ q) (hu : 0 ≤ u) :
    q * 2 ^ (-u) ≤ q := by
  nlinarith [rpow_two_neg_le_one hu]

theorem log_complement_ratio_nonneg {q u : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hu : 0 ≤ u) :
    0 ≤ Real.log ((1 - q * 2 ^ (-u)) / (1 - q)) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ (by linarith : 0 < 1 - q)]
  nlinarith [shifted_ratio_le hq0.le hu]

/-- Reporter work dominates its explicitly linear log-odds contribution. -/
theorem reporterWork_lower {q u : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hu : 0 ≤ u) :
    (q - q * 2 ^ (-u)) * (u * Real.log 2) ≤ reporterWork q u := by
  rw [reporterWork]
  have hdiff : 0 ≤ q - q * 2 ^ (-u) := by
    nlinarith [shifted_ratio_le hq0.le hu]
  have hlog := log_complement_ratio_nonneg hq0 hq1 hu
  nlinarith [mul_nonneg hdiff hlog]

/-- Global linear coercivity beyond unit formation size. -/
theorem reporterWork_linear_lower {q u : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hu : 1 ≤ u) :
    q * Real.log 2 / 2 * u ≤ reporterWork q u := by
  have hr := rpow_two_neg_le_half hu
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase := reporterWork_lower hq0 hq1 (le_trans (by norm_num) hu)
  have hdiff : q / 2 ≤ q - q * 2 ^ (-u) := by nlinarith
  have hu0 : 0 ≤ u := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hdiff (mul_nonneg hu0 (le_of_lt hlog))]

theorem reporterWork_zero (q : ℝ) : reporterWork q 0 = 0 := by
  simp [reporterWork]

theorem reporterWork_pos {q u : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hu : 0 < u) :
    0 < reporterWork q u := by
  have hrlt : (2 : ℝ) ^ (-u) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hdiff : 0 < q - q * 2 ^ (-u) := by nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase := reporterWork_lower hq0 hq1 hu.le
  have hprod : 0 < (q - q * 2 ^ (-u)) * (u * Real.log 2) :=
    mul_pos hdiff (mul_pos hu hlog)
  linarith

theorem reporterWork_eq_zero_iff {q u : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hu : 0 ≤ u) :
    reporterWork q u = 0 ↔ u = 0 := by
  constructor
  · intro h
    by_contra hne
    have hpos := reporterWork_pos hq0 hq1 (lt_of_le_of_ne hu (Ne.symm hne))
    linarith
  · rintro rfl
    exact reporterWork_zero q

/-- Every positive formation escapes along a genuinely expanding depth-scale orbit. -/
theorem scaleOrbit_tendsto {d u : ℝ} (hd : 1 < d) (hu : 0 < u) :
    Tendsto (fun n : ℕ => d ^ n * u) atTop atTop :=
  Tendsto.atTop_mul_const hu (tendsto_pow_atTop_atTop_of_one_lt hd)

/-- Reporter work tends to infinity on every nonneutral source-scale orbit. -/
theorem reporterWork_scale_tendsto {q d u : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : 1 < d) (hu : 0 < u) :
    Tendsto (fun n : ℕ => reporterWork q (d ^ n * u)) atTop atTop := by
  have horbit := scaleOrbit_tendsto hd hu
  have hc : 0 < q * Real.log 2 / 2 := by positivity
  have hlower : Tendsto (fun n : ℕ => q * Real.log 2 / 2 * (d ^ n * u)) atTop atTop :=
    Tendsto.const_mul_atTop hc horbit
  refine tendsto_atTop_mono' atTop ?_ hlower
  filter_upwards [horbit.eventually_ge_atTop 1] with n hn
  exact reporterWork_linear_lower hq0 hq1 hn

/-- Uniform boundedness of work on the full source-generated scale orbit. -/
def BoundedScaleWork (q d u : ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, reporterWork q (d ^ n * u) ≤ B

/-- Global properness/selection: bounded scale-orbit work is equivalent to neutral formation. -/
theorem boundedScaleWork_iff {q d u : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hd : 1 < d) (hu : 0 ≤ u) :
    BoundedScaleWork q d u ↔ u = 0 := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hne
    have htop := reporterWork_scale_tendsto hq0 hq1 hd (lt_of_le_of_ne hu (Ne.symm hne))
    have hevent := htop.eventually_gt_atTop B
    rcases hevent.exists with ⟨n, hn⟩
    linarith [hB n]
  · rintro rfl
    exact ⟨0, fun n => by simp [reporterWork_zero]⟩

/-- Literal least-mode source specialization of global properness. -/
theorem leastMode_boundedScaleWork_iff (θ : AbelianZetaParameters) {d u : ℝ}
    (hd : 1 < d) (hu : 0 ≤ u) :
    BoundedScaleWork (θ.ratio leastMode) d u ↔ u = 0 :=
  boundedScaleWork_iff (θ.ratio_pos leastMode) (θ.ratio_lt_one leastMode) hd hu

/-- Any globally bounded work which dominates the canonical reporter selects neutrality.

This is the conservation interface: a target need not make work vanish.  A uniform bound on the
source-generated orbit, together with reporter domination, is enough. -/
theorem bounded_dominating_work_selects (θ : AbelianZetaParameters) {d u : ℝ}
    (hd : 1 < d) (hu : 0 ≤ u) (work : ℕ → ℝ)
    (hdom : ∀ n : ℕ, reporterWork (θ.ratio leastMode) (d ^ n * u) ≤ work n)
    (hbounded : ∃ B : ℝ, ∀ n : ℕ, work n ≤ B) :
    u = 0 := by
  apply (leastMode_boundedScaleWork_iff θ hd hu).mp
  obtain ⟨B, hB⟩ := hbounded
  exact ⟨B, fun n => (hdom n).trans (hB n)⟩

/-- Capstone: formation scaling, endogenous genesis, and global selection hold simultaneously. -/
theorem globalFormationProperness_capstone (θ : AbelianZetaParameters) {d u : ℝ}
    (hd : 1 < d) (hu : 0 ≤ u) :
    (∀ x : ℝ × ℝ,
      depthScale d (AbelianZetaGas.tempTranslate u x) =
        AbelianZetaGas.tempTranslate (d * u) (depthScale d x)) ∧
      (⁅AbelianZetaGas.socleTilt, AbelianZetaGas.tempTranslate u⁆ =
        AbelianZetaGas.fugacityTranslate u) ∧
      (BoundedScaleWork (θ.ratio leastMode) d u ↔ u = 0) := by
  exact ⟨depthScale_tempTranslate d u,
    AbelianZetaGas.commutator_socleTilt_tempTranslate u,
    leastMode_boundedScaleWork_iff θ hd hu⟩

end

end GaloisForLFunctions.HTGeometry
