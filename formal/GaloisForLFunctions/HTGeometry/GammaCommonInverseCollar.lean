import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# A common analytic inverse collar for the Gamma pole microscopes

The normalized reciprocal-Gamma maps

`Aₙ(X) = -1 / Gamma(-n + sₙ X)`,  `sₙ = (-1)^(n+1) / n!`,

converge locally uniformly to the identity.  Their derivatives therefore converge locally
uniformly to `1`.  On one fixed disk, every sufficiently late `Aₙ` is a quantitative perturbation
of the identity.  Mathlib's quantitative inverse theorem then supplies inverse branches on one
fixed target disk, with a common Lipschitz bound.

The terminal declaration `gammaCommonInverseCollar` is unconditional: its fields are proved from
the Euler Gamma function and contain no assumed analytic input.
-/

namespace GaloisForLFunctions

open Complex Filter Function Metric Set Topology
open scoped NNReal

noncomputable section

/-- The reciprocal-Gamma microscope normalized to converge to the identity. -/
def gammaPoleMicroscope (n : ℕ) (x : ℂ) : ℂ :=
  -reciprocalGammaEntire
    (-(n : ℂ) + reciprocalGammaFactorialScale n * x)

@[simp]
theorem gammaPoleMicroscope_zero (n : ℕ) : gammaPoleMicroscope n 0 = 0 := by
  simp [gammaPoleMicroscope, reciprocalGammaEntire, Complex.Gamma_neg_nat_eq_zero]

theorem differentiable_gammaPoleMicroscope (n : ℕ) :
    Differentiable ℂ (gammaPoleMicroscope n) := by
  intro x
  have hrec : DifferentiableAt ℂ reciprocalGammaEntire
      (-(n : ℂ) + reciprocalGammaFactorialScale n * x) :=
    (contDiff_reciprocalGammaEntire.differentiable (by simp)) _
  exact (hrec.comp x <|
    (differentiableAt_const (c := -(n : ℂ))).add
      (differentiableAt_id.const_mul (reciprocalGammaFactorialScale n))).neg

/-- The pole microscopes converge to the identity on every compact set. -/
theorem tendsto_gammaPoleMicroscope_locallyUniformly :
    TendstoLocallyUniformly gammaPoleMicroscope id atTop := by
  have hconst : TendstoLocallyUniformly
      (fun (_n : ℕ) (_x : ℂ) => (-1 : ℂ)) (fun _x : ℂ => -1) atTop :=
    tendstoLocallyUniformly_const_sequence (fun _x : ℂ => (-1 : ℂ))
  have h := hconst.mul₀ tendsto_reciprocalGammaFactorialBlowUp_locallyUniformly
    continuous_const continuous_neg
  convert h using 1
  · funext n x
    simp [gammaPoleMicroscope]
  · funext x
    simp

/-- The derivatives of the pole microscopes converge locally uniformly to `1`. -/
theorem tendsto_deriv_gammaPoleMicroscope_locallyUniformly :
    TendstoLocallyUniformly
      (fun n => deriv (gammaPoleMicroscope n)) (fun _ : ℂ => 1) atTop := by
  have hloc : TendstoLocallyUniformlyOn gammaPoleMicroscope id atTop Set.univ := by
    simpa [tendstoLocallyUniformlyOn_univ] using
      tendsto_gammaPoleMicroscope_locallyUniformly
  have hder := hloc.deriv
    (Filter.Eventually.of_forall fun n =>
      (differentiable_gammaPoleMicroscope n).differentiableOn)
    isOpen_univ
  rw [← tendstoLocallyUniformlyOn_univ]
  simpa [Function.comp_def] using hder

private def gammaPoleIdentity : ℂ ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.refl ℂ ℂ

private def GammaPoleCollarGood (n : ℕ) : Prop :=
  ApproximatesLinearOn (gammaPoleMicroscope n)
      (gammaPoleIdentity : ℂ →L[ℂ] ℂ)
      (Metric.ball (0 : ℂ) (1 : ℝ)) (1 / 2 : ℝ≥0) ∧
    ∀ x ∈ Metric.ball (0 : ℂ) 1,
      dist (deriv (gammaPoleMicroscope n) x) 1 < 1 / 2

/-- Eventually every Gamma pole microscope is a `1/2`-perturbation of the identity on the same
unit disk. -/
private theorem eventually_gammaPoleCollarGood :
    ∀ᶠ n : ℕ in atTop, GammaPoleCollarGood n := by
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) 1) := isCompact_closedBall 0 1
  have huniform : TendstoUniformlyOn
      (fun n => deriv (gammaPoleMicroscope n)) (fun _ : ℂ => 1) atTop
      (Metric.closedBall 0 1) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp
      tendsto_deriv_gammaPoleMicroscope_locallyUniformly)
      (Metric.closedBall 0 1) hcompact
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [huniform (1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  have hderiv : ∀ x ∈ Metric.ball (0 : ℂ) 1,
      dist (deriv (gammaPoleMicroscope n) x) 1 < 1 / 2 := by
    intro x hx
    simpa [dist_comm] using hn x (Metric.ball_subset_closedBall hx)
  refine ⟨?_, hderiv⟩
  apply LipschitzOnWith.approximatesLinearOn
  have hlip : LipschitzOnWith (1 / 2 : ℝ≥0)
      (fun x : ℂ => gammaPoleMicroscope n x - x)
      (Metric.ball (0 : ℂ) (1 : ℝ)) := by
    apply (convex_ball (0 : ℂ) (1 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
    · intro x hx
      exact (differentiable_gammaPoleMicroscope n x).sub differentiableAt_id
    · intro x hx
      have hder : deriv (fun z : ℂ => gammaPoleMicroscope n z - z) x =
          deriv (gammaPoleMicroscope n) x - 1 :=
        ((differentiable_gammaPoleMicroscope n x).hasDerivAt.sub
          (hasDerivAt_id x)).deriv
      rw [hder]
      exact_mod_cast (le_of_lt (by simpa [dist_eq_norm] using hderiv x hx) :
        ‖deriv (gammaPoleMicroscope n) x - 1‖ ≤ (1 / 2 : ℝ))
  simpa [gammaPoleIdentity] using hlip

private theorem gammaPoleApproximation_small :
    Subsingleton ℂ ∨
      (1 / 2 : ℝ≥0) <
        ‖((gammaPoleIdentity).symm : ℂ →L[ℂ] ℂ)‖₊⁻¹ := by
  right
  simpa [gammaPoleIdentity] using (show (1 / 2 : ℝ≥0) < 1 by norm_num)

private noncomputable def gammaPolePartialHomeomorph
    (n : ℕ) (h : GammaPoleCollarGood n) : OpenPartialHomeomorph ℂ ℂ :=
  h.1.toOpenPartialHomeomorph (gammaPoleMicroscope n)
    (Metric.ball (0 : ℂ) (1 : ℝ))
    gammaPoleApproximation_small isOpen_ball

private theorem gammaPole_closedBall_target
    (n : ℕ) (h : GammaPoleCollarGood n) :
    Metric.closedBall (0 : ℂ) (1 / 4) ⊆
      (gammaPolePartialHomeomorph n h).target := by
  have ht := h.1.closedBall_subset_target gammaPoleApproximation_small isOpen_ball
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show Metric.closedBall (0 : ℂ) (1 / 2) ⊆ Metric.ball 0 1 by
      exact Metric.closedBall_subset_ball (by norm_num))
  convert ht using 1
  norm_num [gammaPolePartialHomeomorph, gammaPoleIdentity,
    gammaPoleMicroscope_zero]

/-- Unconditional common-collar data for all sufficiently late negative Gamma poles. -/
structure GammaCommonInverseCollar where
  /-- All pole labels at or beyond this threshold share the collar. -/
  threshold : ℕ
  threshold_ge_five : 5 ≤ threshold
  /-- The selected analytic inverse branches of the normalized pole microscopes. -/
  branch : ℕ → ℂ → ℂ
  branch_maps : ∀ {n : ℕ}, threshold ≤ n →
    MapsTo (branch n) (Metric.closedBall (0 : ℂ) (1 / 4)) (Metric.ball 0 1)
  rightInverse : ∀ {n : ℕ}, threshold ≤ n →
    Set.RightInvOn (branch n) (gammaPoleMicroscope n)
      (Metric.closedBall (0 : ℂ) (1 / 4))
  leftInverse : ∀ {n : ℕ}, threshold ≤ n →
    Set.LeftInvOn (branch n) (gammaPoleMicroscope n) (Metric.ball (0 : ℂ) 1)
  lipschitzOn : ∀ {n : ℕ}, threshold ≤ n →
    LipschitzOnWith 2 (branch n) (Metric.closedBall (0 : ℂ) (1 / 4))
  analyticOn : ∀ {n : ℕ}, threshold ≤ n →
    AnalyticOnNhd ℂ (branch n) (Metric.ball (0 : ℂ) (1 / 4))

private theorem exists_gammaCommonInverseCollar : Nonempty GammaCommonInverseCollar := by
  have hev := eventually_gammaPoleCollarGood
  rw [eventually_atTop] at hev
  obtain ⟨N₀, hN₀⟩ := hev
  let N := max N₀ 5
  have hgood : ∀ n, N ≤ n → GammaPoleCollarGood n := by
    intro n hn
    exact hN₀ n ((le_max_left N₀ 5).trans hn)
  let B : ℕ → ℂ → ℂ := fun n =>
    if hn : N ≤ n then (gammaPolePartialHomeomorph n (hgood n hn)).symm else 0
  refine ⟨{
    threshold := N
    threshold_ge_five := le_max_right N₀ 5
    branch := B
    branch_maps := ?_
    rightInverse := ?_
    leftInverse := ?_
    lipschitzOn := ?_
    analyticOn := ?_ }⟩
  · intro n hn t ht
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    exact (gammaPolePartialHomeomorph n (hgood n hn)).symm.map_source
      (gammaPole_closedBall_target n (hgood n hn) ht)
  · intro n hn t ht
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    have htarget := gammaPole_closedBall_target n (hgood n hn) ht
    simpa [gammaPolePartialHomeomorph] using
      (gammaPolePartialHomeomorph n (hgood n hn)).right_inv htarget
  · intro n hn x hx
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    have hsource : x ∈ (gammaPolePartialHomeomorph n (hgood n hn)).source := by
      simpa [gammaPolePartialHomeomorph] using hx
    simpa [gammaPolePartialHomeomorph] using
      (gammaPolePartialHomeomorph n (hgood n hn)).left_inv hsource
  · intro n hn
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    let P := gammaPolePartialHomeomorph n (hgood n hn)
    have hxt : x ∈ P.target := gammaPole_closedBall_target n (hgood n hn) hx
    have hyt : y ∈ P.target := gammaPole_closedBall_target n (hgood n hn) hy
    have hanti := (hgood n hn).1.antilipschitz gammaPoleApproximation_small
    have hdist := hanti.le_mul_dist
      ⟨P.symm x, P.symm.map_source hxt⟩ ⟨P.symm y, P.symm.map_source hyt⟩
    change dist (P.symm x) (P.symm y) ≤ _ at hdist
    have hxinv : gammaPoleMicroscope n (P.symm x) = x := by
      simpa [P, gammaPolePartialHomeomorph] using P.right_inv hxt
    have hyinv : gammaPoleMicroscope n (P.symm y) = y := by
      simpa [P, gammaPolePartialHomeomorph] using P.right_inv hyt
    simp [gammaPoleIdentity, hxinv, hyinv] at hdist
    norm_num at hdist
    simpa [P] using hdist
  · intro n hn t ht
    rw [show B n = (gammaPolePartialHomeomorph n (hgood n hn)).symm by simp [B, hn]]
    let P := gammaPolePartialHomeomorph n (hgood n hn)
    have htarget : t ∈ P.target :=
      gammaPole_closedBall_target n (hgood n hn) (Metric.ball_subset_closedBall ht)
    have hsource : P.symm t ∈ Metric.ball (0 : ℂ) 1 := by
      simpa [P, gammaPolePartialHomeomorph] using P.symm.map_source htarget
    have hderiv_ne : deriv (gammaPoleMicroscope n) (P.symm t) ≠ 0 := by
      intro hz
      have hlt := (hgood n hn).2 (P.symm t) hsource
      rw [hz] at hlt
      norm_num [dist_eq_norm] at hlt
    let i : ℂ ≃L[ℂ] ℂ :=
      ContinuousLinearEquiv.unitsEquivAut ℂ
        (Units.mk0 (deriv (gammaPoleMicroscope n) (P.symm t)) hderiv_ne)
    have han : AnalyticAt ℂ P (P.symm t) := by
      simpa [P, gammaPolePartialHomeomorph] using
        (differentiable_gammaPoleMicroscope n).analyticAt (P.symm t)
    have hfder : fderiv ℂ P (P.symm t) = i := by
      apply ContinuousLinearMap.ext
      intro z
      simp [P, gammaPolePartialHomeomorph, i]
    exact P.analyticAt_symm htarget han hfder

/-- The selected common inverse collar, constructed unconditionally from Gamma. -/
noncomputable def gammaCommonInverseCollar : GammaCommonInverseCollar :=
  Classical.choice exists_gammaCommonInverseCollar

theorem gammaCommonInverseCollar_threshold_ge_five :
    5 ≤ gammaCommonInverseCollar.threshold :=
  gammaCommonInverseCollar.threshold_ge_five

theorem gammaCommonInverseCollar_rightInverse
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (1 / 4)) :
    gammaPoleMicroscope n (gammaCommonInverseCollar.branch n t) = t :=
  gammaCommonInverseCollar.rightInverse hn ht

theorem gammaCommonInverseCollar_branch_mem
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (1 / 4)) :
    gammaCommonInverseCollar.branch n t ∈ Metric.ball (0 : ℂ) 1 :=
  gammaCommonInverseCollar.branch_maps hn ht

/-- The tangent-to-identity Möbius germ that compares normalized and moving-base Gamma charts. -/
def mobiusTangentGerm (a z : ℂ) : ℂ := z / (1 - a * z)

private theorem iteratedDeriv_one_sub_inv_zero (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => (1 - z)⁻¹) 0 = (k.factorial : ℂ) := by
  have hfun : (fun z : ℂ => (1 - z)⁻¹) =
      -(fun z : ℂ => (z + (-1 : ℂ))⁻¹) := by
    funext z
    rw [show (1 - z : ℂ) = -(z + (-1 : ℂ)) by ring, inv_neg]
    simp only [Pi.neg_apply]
  rw [hfun, iteratedDeriv_neg,
    iteratedDeriv_inv_add_const (-1) k 0 (by norm_num)]
  simp only [zero_add]
  have hpow : ((-1 : ℂ) ^ (k + 1))⁻¹ = (-1 : ℂ) ^ (k + 1) := by
    rw [← inv_pow]
    norm_num
  rw [hpow, pow_succ]
  ring_nf
  rw [show (-1 : ℂ) ^ (k * 2) = 1 by
    rw [mul_comm, pow_mul]
    norm_num]
  ring

/-- Exact raw derivative profile of a tangent Möbius germ.  The factorial is the all-order wall
hidden by every fixed finite jet truncation. -/
theorem iteratedDeriv_mobiusTangentGerm_zero
    (a : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    iteratedDeriv k (mobiusTangentGerm a) 0 =
      (k.factorial : ℂ) * a ^ (k - 1) := by
  let g : ℂ → ℂ := fun z => (1 - a * z)⁻¹
  have hg : ContDiffAt ℂ k g 0 := by
    dsimp [g]
    apply ContDiffAt.inv
    · fun_prop
    · norm_num
  have hgder : iteratedDeriv (k - 1) g 0 =
      a ^ (k - 1) * ((k - 1).factorial : ℂ) := by
    dsimp [g]
    rw [iteratedDeriv_comp_mul_left_uncond (fun z : ℂ => (1 - z)⁻¹) a (k - 1) 0]
    rw [mul_zero, iteratedDeriv_one_sub_inv_zero]
  change iteratedDeriv k (fun z : ℂ => z * (1 - a * z)⁻¹) 0 = _
  change iteratedDeriv k ((fun z : ℂ => z) * g) 0 = _
  rw [iteratedDeriv_mul (f := fun z : ℂ => z) (g := g) contDiffAt_id hg]
  rw [Finset.sum_eq_single 1]
  · rw [show iteratedDeriv 1 (fun z : ℂ => z) 0 = 1 by simp]
    rw [hgder, Nat.choose_one_right]
    have hfac : (k : ℂ) * ((k - 1).factorial : ℂ) = (k.factorial : ℂ) := by
      exact_mod_cast Nat.mul_factorial_pred (Nat.ne_of_gt hk)
    calc
      (k : ℂ) * 1 * (a ^ (k - 1) * ((k - 1).factorial : ℂ)) =
          ((k : ℂ) * ((k - 1).factorial : ℂ)) * a ^ (k - 1) := by ring
      _ = (k.factorial : ℂ) * a ^ (k - 1) := by rw [hfac]
  · intro b hb hb1
    have hbid : iteratedDeriv b (fun z : ℂ => z) 0 = 0 := by
      rw [show (fun z : ℂ => z) = id from rfl, iteratedDeriv_id]
      simp [hb1]
    rw [hbid]
    ring
  · simp only [Finset.mem_range]
    omega

/-- Taylor normalization removes exactly the factorial wall: the normalized all-order profile is
the geometric sequence `a^k`. -/
theorem normalizedIteratedDeriv_mobiusTangentGerm_zero
    (a : ℂ) (k : ℕ) :
    iteratedDeriv (k + 1) (mobiusTangentGerm a) 0 /
        (((k + 1).factorial : ℕ) : ℂ) = a ^ k := by
  rw [iteratedDeriv_mobiusTangentGerm_zero a (by omega)]
  rw [Nat.add_sub_cancel]
  field_simp [show (((k + 1).factorial : ℕ) : ℂ) ≠ 0 by
    exact_mod_cast Nat.factorial_ne_zero (k + 1)]

/-- The complete critical Taylor/Gevrey jet profile of a tangent Möbius chart. -/
def mobiusCriticalJetProfile (a : ℂ) (k : ℕ) : ℂ :=
  iteratedDeriv (k + 1) (mobiusTangentGerm a) 0 /
    (((k + 1).factorial : ℕ) : ℂ)

@[simp]
theorem mobiusCriticalJetProfile_apply (a : ℂ) (k : ℕ) :
    mobiusCriticalJetProfile a k = a ^ k := by
  exact normalizedIteratedDeriv_mobiusTangentGerm_zero a k

/-- **Critical-chart completeness.**  The complete Taylor-normalized jet profile remembers the
Möbius chart exactly; its second-derivative coordinate recovers the parameter. -/
theorem mobiusCriticalJetProfile_injective :
    Function.Injective mobiusCriticalJetProfile := by
  intro a b hab
  have h := congrFun hab 1
  simpa using h

/-- A second Gevrey normalization divides the Taylor profile by one further factorial.  Unlike
the critical Taylor normalization, this profile is bounded for every finite Möbius parameter. -/
theorem gevreyTwoNorm_mobiusTangentGerm_zero
    (a : ℂ) (k : ℕ) :
    ‖iteratedDeriv (k + 1) (mobiusTangentGerm a) 0‖ /
        ((((k + 1).factorial : ℕ) : ℝ) ^ 2) =
      ‖a‖ ^ k / (((k + 1).factorial : ℕ) : ℝ) := by
  rw [iteratedDeriv_mobiusTangentGerm_zero a (by omega), Nat.add_sub_cancel]
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  field_simp [show ((((k + 1).factorial : ℕ) : ℝ)) ≠ 0 by positivity]

/-- **Supercritical Gevrey collapse.**  The twice-factorially normalized complete Möbius jet is
bounded by `exp ‖a‖` for every parameter `a`; hence it has no finite parameter wall. -/
theorem gevreyTwoNorm_mobiusTangentGerm_zero_le_exp
    (a : ℂ) (k : ℕ) :
    ‖iteratedDeriv (k + 1) (mobiusTangentGerm a) 0‖ /
        ((((k + 1).factorial : ℕ) : ℝ) ^ 2) ≤ Real.exp ‖a‖ := by
  rw [gevreyTwoNorm_mobiusTangentGerm_zero]
  calc
    ‖a‖ ^ k / (((k + 1).factorial : ℕ) : ℝ) ≤
        ‖a‖ ^ k / (k.factorial : ℝ) := by
      apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg a) k)
      · positivity
      · exact_mod_cast Nat.factorial_le (Nat.le_succ k)
    _ ≤ Real.exp ‖a‖ :=
      Real.pow_div_factorial_le_exp (x := ‖a‖) (norm_nonneg a) k

/-- Exact recurrence of the raw derivative norms.  For every nonzero `a`, its multiplier
`(k+2)‖a‖` eventually exceeds every fixed expansion factor. -/
theorem norm_iteratedDeriv_mobiusTangentGerm_zero_succ
    (a : ℂ) (k : ℕ) :
    ‖iteratedDeriv (k + 2) (mobiusTangentGerm a) 0‖ =
      ((k + 2 : ℕ) : ℝ) * ‖a‖ *
        ‖iteratedDeriv (k + 1) (mobiusTangentGerm a) 0‖ := by
  rw [iteratedDeriv_mobiusTangentGerm_zero a (by omega),
    iteratedDeriv_mobiusTangentGerm_zero a (by omega)]
  rw [show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel]
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  rw [Nat.factorial_succ]
  push_cast
  ring

/-- The factorially small shell parameter relating the normalized branch and moving-base germs. -/
def gammaMovingBaseShell (n : ℕ) : ℂ :=
  reciprocalGammaFactorialScale n / (n : ℂ)

/-- The intrinsic moving-base transition chart on the common inverse collar.  This is the exact
Möbius transform `Dₙ=Bₙ/(1-(sₙ/n)Bₙ)` of the selected normalized inverse branch. -/
def gammaMovingBaseTransition (n : ℕ) (t : ℂ) : ℂ :=
  gammaCommonInverseCollar.branch n t /
    (1 - gammaMovingBaseShell n * gammaCommonInverseCollar.branch n t)

private theorem gamma_one_sub_inv_norm_le_two_of_norm_lt_half {u : ℂ}
    (hu : ‖u‖ < (1 / 2 : ℝ)) :
    (1 - u) ≠ 0 ∧ ‖(1 - u)⁻¹‖ ≤ (2 : ℝ) := by
  have htri : ‖(1 : ℂ)‖ ≤ ‖1 - u‖ + ‖u‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      norm_add_le (1 - u) u
  have hhalf : (1 / 2 : ℝ) < ‖1 - u‖ := by
    norm_num at htri
    linarith
  have hpos : 0 < ‖1 - u‖ := by linarith
  refine ⟨norm_pos_iff.mp hpos, ?_⟩
  rw [norm_inv]
  have hhalfpos : 0 < (1 / 2 : ℝ) := by norm_num
  have hlt := (inv_lt_inv₀ hpos hhalfpos).2 hhalf
  norm_num at hlt
  exact le_of_lt hlt

/-- The intrinsic moving-base chart is uniformly close to the normalized inverse branch, with an
exact bound controlled only by the factorial shell parameter. -/
theorem gammaMovingBaseTransition_dist_branch_le
    {n : ℕ} (hn : gammaCommonInverseCollar.threshold ≤ n)
    {t : ℂ} (ht : t ∈ Metric.closedBall (0 : ℂ) (1 / 4))
    (hshell : ‖gammaMovingBaseShell n‖ < (1 / 2 : ℝ)) :
    dist (gammaMovingBaseTransition n t)
      (gammaCommonInverseCollar.branch n t) ≤
        2 * ‖gammaMovingBaseShell n‖ := by
  let a := gammaMovingBaseShell n
  let B := gammaCommonInverseCollar.branch n t
  have hBmem := gammaCommonInverseCollar_branch_mem hn ht
  have hB : ‖B‖ < 1 := by
    simpa [B, Metric.mem_ball, dist_zero_left] using hBmem
  have hu : ‖a * B‖ < (1 / 2 : ℝ) := by
    calc
      ‖a * B‖ = ‖a‖ * ‖B‖ := norm_mul _ _
      _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hB.le (norm_nonneg a)
      _ < 1 / 2 := by simpa [a] using hshell
  obtain ⟨hden, hinv⟩ := gamma_one_sub_inv_norm_le_two_of_norm_lt_half hu
  have hid : gammaMovingBaseTransition n t - B =
      a * B ^ 2 * (1 - a * B)⁻¹ := by
    rw [gammaMovingBaseTransition]
    change B / (1 - a * B) - B = _
    have hid' : B / (1 - a * B) - B =
        (a * B ^ 2) / (1 - a * B) := by
      have hden' : 1 - B * a ≠ 0 := by simpa [mul_comm] using hden
      field_simp [hden, hden']
      ring
    simpa [div_eq_mul_inv] using hid'
  have hBsq : ‖B‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg B, hB]
  rw [dist_eq_norm, show gammaCommonInverseCollar.branch n t = B from rfl, hid,
    norm_mul, norm_mul, norm_pow]
  calc
    ‖a‖ * ‖B‖ ^ 2 * ‖(1 - a * B)⁻¹‖
        ≤ ‖a‖ * 1 * 2 := by gcongr
    _ = 2 * ‖gammaMovingBaseShell n‖ := by simp [a]; ring

theorem tendsto_gammaMovingBaseShell_zero :
    Tendsto gammaMovingBaseShell atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℂ)⁻¹)) atTop (nhds 0) := by
    have hreal : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa using hreal.ofReal
  simpa [gammaMovingBaseShell, div_eq_mul_inv] using
    tendsto_reciprocalGammaFactorialScale_zero.mul hinv

/-- The moving-base and normalized-branch charts become uniformly identical on their common
collar. -/
theorem tendsto_gammaMovingBaseTransition_branch_uniformlyOn :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Metric.closedBall (0 : ℂ) (1 / 4),
      dist (gammaMovingBaseTransition n t)
        (gammaCommonInverseCollar.branch n t) < ε := by
  intro ε hε
  have hshell : Tendsto (fun n => ‖gammaMovingBaseShell n‖) atTop (nhds 0) := by
    simpa using tendsto_gammaMovingBaseShell_zero.norm
  filter_upwards [
      (tendsto_order.1 hshell).2 (1 / 2) (by norm_num),
      (tendsto_order.1 hshell).2 (ε / 2) (by linarith),
      eventually_ge_atTop gammaCommonInverseCollar.threshold]
      with n hnHalf hnε hn
  intro t ht
  have hdist := gammaMovingBaseTransition_dist_branch_le hn ht hnHalf
  exact lt_of_le_of_lt hdist (by linarith)

/-- The actual selected normalized inverse branches converge uniformly to the identity on the
common closed target collar. -/
theorem tendsto_gammaCommonInverseCollar_branch_uniformlyOn :
    TendstoUniformlyOn gammaCommonInverseCollar.branch id atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  have hcompact : IsCompact (Metric.closedBall (0 : ℂ) 1) :=
    isCompact_closedBall 0 1
  have hmicroscope : TendstoUniformlyOn gammaPoleMicroscope id atTop
      (Metric.closedBall (0 : ℂ) 1) :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp
      tendsto_gammaPoleMicroscope_locallyUniformly)
      (Metric.closedBall (0 : ℂ) 1) hcompact
  rw [Metric.tendstoUniformlyOn_iff] at hmicroscope ⊢
  intro ε hε
  filter_upwards [hmicroscope ε hε,
    eventually_ge_atTop gammaCommonInverseCollar.threshold] with n hnclose hn
  intro t ht
  have hb := gammaCommonInverseCollar_branch_mem hn ht
  have hinv := gammaCommonInverseCollar_rightInverse hn ht
  have hnear := hnclose (gammaCommonInverseCollar.branch n t)
    (Metric.ball_subset_closedBall hb)
  simpa [hinv, dist_comm] using hnear

/-- **Two-filtration analytic comparison.**  The intrinsic moving-base Gamma transition germs
converge uniformly to the identity on the same collar as the normalized inverse branches.  Hence
the two source filtrations are asymptotically identical at every finite analytic resolution. -/
theorem tendsto_gammaMovingBaseTransition_uniformlyOn :
    TendstoUniformlyOn gammaMovingBaseTransition id atTop
      (Metric.closedBall (0 : ℂ) (1 / 4)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hclose := tendsto_gammaMovingBaseTransition_branch_uniformlyOn
    (ε / 2) (by linarith)
  have hbranch := tendsto_gammaCommonInverseCollar_branch_uniformlyOn
  rw [Metric.tendstoUniformlyOn_iff] at hbranch
  filter_upwards [hclose, hbranch (ε / 2) (by linarith)] with n hnclose hnbranch
  intro t ht
  calc
    dist (id t) (gammaMovingBaseTransition n t)
        ≤ dist (id t) (gammaCommonInverseCollar.branch n t) +
          dist (gammaCommonInverseCollar.branch n t)
            (gammaMovingBaseTransition n t) := dist_triangle _ _ _
    _ < ε := by
      have hc := hnclose t ht
      rw [dist_comm] at hc
      linarith [hc, hnbranch t ht]

end

end GaloisForLFunctions
