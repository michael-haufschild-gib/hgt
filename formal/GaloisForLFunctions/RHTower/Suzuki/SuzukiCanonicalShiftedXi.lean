import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedPublishedGrowthPriorArt
import GaloisForLFunctions.RHTower.LocallyUniformZeroTransfer
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH

/-!
# Suzuki's canonical shifted-Xi family

This module formalizes the first exact theorem in Suzuki (2012), *A canonical system of
differential equations arising from the Riemann zeta-function*.  The functions `A^omega` and
`B^omega` are the paper's literal symmetric and antisymmetric horizontal shifts of completed Xi.

Suzuki's introductory proposition says RH is equivalent to real-rootedness of `A^omega` for every
positive `omega`.  The forward implication is proved through strict horizontal Xi-modulus growth:
under RH the two shifted values have unequal norms at every nonreal point, so their sum cannot
vanish.  The converse uses the explicit sequence `omega_n = 1/(n+1)`: the corresponding
`A^omega_n` converge locally uniformly to centered Xi, and the closed-zero-locus Hurwitz theorem
transfers real-rootedness to Xi.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower

/-- Suzuki's 2012 even shifted completed-Xi function `A^omega`. -/
def suzukiCanonicalA (omega : ℝ) (z : ℂ) : ℂ :=
  (xi (1 / 2 + (omega : ℂ) - z * I) +
    xi (1 / 2 - (omega : ℂ) - z * I)) / 2

/-- Suzuki's 2012 odd shifted completed-Xi function `B^omega`. -/
def suzukiCanonicalB (omega : ℝ) (z : ℂ) : ℂ :=
  I / 2 * (xi (1 / 2 + (omega : ℂ) - z * I) -
    xi (1 / 2 - (omega : ℂ) - z * I))

/-- Centered-coordinate form of Suzuki's `A^omega`. -/
theorem suzukiCanonicalA_eq_XiC_shift_average (omega : ℝ) (z : ℂ) :
    suzukiCanonicalA omega z =
      (XiC (z + (omega : ℂ) * I) + XiC (z - (omega : ℂ) * I)) / 2 := by
  have hp := XiC_even (z + (omega : ℂ) * I)
  have hm := XiC_even (z - (omega : ℂ) * I)
  rw [XiC, XiC] at hp hm
  rw [suzukiCanonicalA]
  have hp' : xi (1 / 2 + (omega : ℂ) - z * I) =
      XiC (z + (omega : ℂ) * I) := by
    rw [XiC]
    convert hp using 1
    congr 1
    simp [add_mul, mul_assoc, Complex.I_mul_I]
    ring
  have hm' : xi (1 / 2 - (omega : ℂ) - z * I) =
      XiC (z - (omega : ℂ) * I) := by
    rw [XiC]
    convert hm using 1
    congr 1
    simp [sub_mul, mul_assoc, Complex.I_mul_I]
    ring
  rw [hp', hm']

/-- Centered-coordinate form of Suzuki's `B^omega`. -/
theorem suzukiCanonicalB_eq_XiC_shift_difference (omega : ℝ) (z : ℂ) :
    suzukiCanonicalB omega z =
      I / 2 * (XiC (z + (omega : ℂ) * I) - XiC (z - (omega : ℂ) * I)) := by
  rw [suzukiCanonicalB]
  have hp := XiC_even (z + (omega : ℂ) * I)
  have hm := XiC_even (z - (omega : ℂ) * I)
  rw [XiC, XiC] at hp hm
  have hp' : xi (1 / 2 + (omega : ℂ) - z * I) =
      XiC (z + (omega : ℂ) * I) := by
    rw [XiC]
    convert hp using 1
    congr 1
    simp [add_mul, mul_assoc, Complex.I_mul_I]
    ring
  have hm' : xi (1 / 2 - (omega : ℂ) - z * I) =
      XiC (z - (omega : ℂ) * I) := by
    rw [XiC]
    convert hm using 1
    congr 1
    simp [sub_mul, mul_assoc, Complex.I_mul_I]
    ring
  rw [hp', hm']

/-- Suzuki's `A^omega` obeys Schwarz reflection. -/
theorem suzukiCanonicalA_conj (omega : ℝ) (z : ℂ) :
    suzukiCanonicalA omega ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (suzukiCanonicalA omega z) := by
  rw [suzukiCanonicalA_eq_XiC_shift_average,
    suzukiCanonicalA_eq_XiC_shift_average, map_div₀, map_ofNat, map_add]
  rw [← XiC_conj, ← XiC_conj]
  have hplus : (starRingEnd ℂ) (z + (omega : ℂ) * I) =
      (starRingEnd ℂ) z - (omega : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
      ring
  have hminus : (starRingEnd ℂ) (z - (omega : ℂ) * I) =
      (starRingEnd ℂ) z + (omega : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [hplus, hminus, add_comm]

/-- Xi modulus depends on transverse height through its absolute value. -/
theorem norm_XiC_eq_horizontal_abs (z : ℂ) :
    ‖XiC z‖ =
      ‖XiC ((z.re : ℂ) - ((|z.im| : ℝ) : ℂ) * I)‖ := by
  by_cases hz : 0 ≤ z.im
  · have hpoint : (starRingEnd ℂ) z =
        (z.re : ℂ) - ((|z.im| : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [abs_of_nonneg hz]
    rw [← hpoint, XiC_conj, norm_conj]
  · have hz' : z.im < 0 := lt_of_not_ge hz
    have hpoint : z = (z.re : ℂ) - ((|z.im| : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [abs_of_neg hz']
    exact congrArg (fun w : ℂ => ‖XiC w‖) hpoint

/-- Under RH, Suzuki's `A^omega` has no zero in the open upper half-plane. -/
theorem suzukiCanonicalA_ne_zero_upper_of_rh
    (hRH : RiemannHypothesis) {omega : ℝ} (homega : 0 < omega)
    {z : ℂ} (hz : 0 < z.im) : suzukiCanonicalA omega z ≠ 0 := by
  have hbound : XiZeroHalfPlaneBound 0 := xiZeroHalfPlaneBound_zero_of_rh hRH
  have hmono := strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound
    (alpha := 0) (by rfl) hbound z.re
  have habs : |z.im - omega| < z.im + omega := by
    rw [abs_lt]
    constructor <;> linarith
  have hminus : 0 ≤ |z.im - omega| := abs_nonneg _
  have hplus : 0 ≤ z.im + omega := by linarith
  have hstrict := hmono hminus hplus habs
  have hnormPlus :
      ‖XiC (z + (omega : ℂ) * I)‖ =
        ‖XiC ((z.re : ℂ) - ((z.im + omega : ℝ) : ℂ) * I)‖ := by
    rw [norm_XiC_eq_horizontal_abs]
    congr 3
    · simp
    · simp [abs_of_pos (by linarith : 0 < z.im + omega)]
  have hnormMinus :
      ‖XiC (z - (omega : ℂ) * I)‖ =
        ‖XiC ((z.re : ℂ) - ((|z.im - omega| : ℝ) : ℂ) * I)‖ := by
    rw [norm_XiC_eq_horizontal_abs]
    congr 3
    · simp
    · simp
  change ‖XiC ((z.re : ℂ) - ((|z.im - omega| : ℝ) : ℂ) * I)‖ <
    ‖XiC ((z.re : ℂ) - ((z.im + omega : ℝ) : ℂ) * I)‖ at hstrict
  rw [← hnormMinus, ← hnormPlus] at hstrict
  intro hzero
  rw [suzukiCanonicalA_eq_XiC_shift_average, div_eq_zero_iff] at hzero
  have hsumZero : XiC (z + (omega : ℂ) * I) +
      XiC (z - (omega : ℂ) * I) = 0 :=
    hzero.resolve_right (by norm_num)
  have hsum : XiC (z + (omega : ℂ) * I) =
      -XiC (z - (omega : ℂ) * I) := by
    exact eq_neg_of_add_eq_zero_left hsumZero
  rw [hsum, norm_neg] at hstrict
  exact lt_irrefl _ hstrict

/-- RH implies every zero of Suzuki's literal `A^omega` is real. -/
theorem suzukiCanonicalA_realZeros_of_rh
    (hRH : RiemannHypothesis) {omega : ℝ} (homega : 0 < omega) :
    ∀ z : ℂ, suzukiCanonicalA omega z = 0 → z.im = 0 := by
  intro z hzero
  rcases lt_trichotomy z.im 0 with hneg | hzeroIm | hpos
  · have hconjZero : suzukiCanonicalA omega ((starRingEnd ℂ) z) = 0 := by
      rw [suzukiCanonicalA_conj, hzero, map_zero]
    have hconjPos : 0 < ((starRingEnd ℂ) z).im := by simp; linarith
    exact False.elim ((suzukiCanonicalA_ne_zero_upper_of_rh hRH homega hconjPos) hconjZero)
  · exact hzeroIm
  · exact False.elim ((suzukiCanonicalA_ne_zero_upper_of_rh hRH homega hpos) hzero)

theorem differentiable_suzukiCanonicalA (omega : ℝ) :
    Differentiable ℂ (suzukiCanonicalA omega) := by
  rw [show suzukiCanonicalA omega = fun z =>
      (XiC (z + (omega : ℂ) * I) + XiC (z - (omega : ℂ) * I)) / 2 by
    funext z
    exact suzukiCanonicalA_eq_XiC_shift_average omega z]
  apply Differentiable.div_const
  apply Differentiable.add
  · exact XiC_differentiable.comp (by fun_prop)
  · exact XiC_differentiable.comp (by fun_prop)

/-- Suzuki's positive shifts `A^(1/(n+1))` converge locally uniformly to centered Xi. -/
theorem tendstoLocallyUniformly_suzukiCanonicalA_to_XiC :
    TendstoLocallyUniformly
      (fun n : ℕ => suzukiCanonicalA (1 / ((n : ℝ) + 1))) XiC atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro epsilon hepsilon x
  have huniform : UniformContinuousOn XiC (closedBall x 2) :=
    (isCompact_closedBall x 2).uniformContinuousOn_of_continuous
      XiC_differentiable.continuous.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huniform
  obtain ⟨delta, hdelta, hcontrol⟩ := huniform epsilon hepsilon
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num), ?_⟩
  have hscale : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmin : 0 < min delta 1 := lt_min hdelta (by norm_num)
  have hevent := hscale.eventually (ball_mem_nhds (0 : ℝ) hmin)
  filter_upwards [hevent] with n hn
  intro y hy
  let omega : ℝ := 1 / ((n : ℝ) + 1)
  have homega : 0 < omega := by
    dsimp only [omega]
    positivity
  have homegaSmall : omega < min delta 1 := by
    dsimp only [omega]
    have hpos : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hpos] using hn
  have homegaDelta : omega < delta := homegaSmall.trans_le (min_le_left _ _)
  have homegaOne : omega < 1 := homegaSmall.trans_le (min_le_right _ _)
  have hyClosed : y ∈ closedBall x 2 := by
    rw [mem_closedBall]
    exact (mem_ball.mp hy).le.trans (by norm_num)
  have hplusDist : dist y (y + (omega : ℂ) * I) = omega := by
    rw [dist_eq_norm]
    have : y - (y + (omega : ℂ) * I) = -(omega : ℂ) * I := by ring
    rw [this, norm_mul, norm_neg, norm_real, norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos homega]
  have hminusDist : dist y (y - (omega : ℂ) * I) = omega := by
    rw [dist_eq_norm]
    have : y - (y - (omega : ℂ) * I) = (omega : ℂ) * I := by ring
    rw [this, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs, abs_of_pos homega]
  have hplusClosed : y + (omega : ℂ) * I ∈ closedBall x 2 := by
    rw [mem_closedBall]
    apply LT.lt.le
    calc
      dist (y + (omega : ℂ) * I) x ≤
          dist (y + (omega : ℂ) * I) y + dist y x := dist_triangle _ _ _
      _ = omega + dist y x := by rw [dist_comm, hplusDist]
      _ < 1 + 1 := add_lt_add homegaOne (mem_ball.mp hy)
      _ = 2 := by norm_num
  have hminusClosed : y - (omega : ℂ) * I ∈ closedBall x 2 := by
    rw [mem_closedBall]
    apply LT.lt.le
    calc
      dist (y - (omega : ℂ) * I) x ≤
          dist (y - (omega : ℂ) * I) y + dist y x := dist_triangle _ _ _
      _ = omega + dist y x := by rw [dist_comm, hminusDist]
      _ < 1 + 1 := add_lt_add homegaOne (mem_ball.mp hy)
      _ = 2 := by norm_num
  have hplus := hcontrol y hyClosed (y + (omega : ℂ) * I) hplusClosed
    (hplusDist.trans_lt homegaDelta)
  have hminus := hcontrol y hyClosed (y - (omega : ℂ) * I) hminusClosed
    (hminusDist.trans_lt homegaDelta)
  rw [suzukiCanonicalA_eq_XiC_shift_average]
  rw [dist_eq_norm] at hplus hminus ⊢
  have hrewrite :
      XiC y - (XiC (y + (omega : ℂ) * I) + XiC (y - (omega : ℂ) * I)) / 2 =
        ((XiC y - XiC (y + (omega : ℂ) * I)) +
          (XiC y - XiC (y - (omega : ℂ) * I))) / 2 := by ring
  rw [hrewrite, norm_div]
  have hadd := norm_add_le
    (XiC y - XiC (y + (omega : ℂ) * I))
    (XiC y - XiC (y - (omega : ℂ) * I))
  norm_num at hadd ⊢
  nlinarith

/-- Suzuki (2012), Proposition 1, reverse implication. -/
theorem riemannHypothesis_of_suzukiCanonicalA_realZeros
    (hreal : ∀ omega : ℝ, 0 < omega →
      ∀ z : ℂ, suzukiCanonicalA omega z = 0 → z.im = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_XiC_locally_uniform_real_zero_approximants
    tendstoLocallyUniformly_suzukiCanonicalA_to_XiC
  · exact Filter.Eventually.of_forall fun n =>
      differentiable_suzukiCanonicalA (1 / ((n : ℝ) + 1))
  · exact Filter.Eventually.of_forall fun n =>
      hreal (1 / ((n : ℝ) + 1)) (by positivity)

/-- Suzuki (2012), Proposition 1 (`prop_basic`), exactly for the literal shifted-Xi family. -/
theorem riemannHypothesis_iff_forall_suzukiCanonicalA_realZeros :
    RiemannHypothesis ↔
      ∀ omega : ℝ, 0 < omega →
        ∀ z : ℂ, suzukiCanonicalA omega z = 0 → z.im = 0 := by
  constructor
  · intro hRH omega homega
    exact suzukiCanonicalA_realZeros_of_rh hRH homega
  · exact riemannHypothesis_of_suzukiCanonicalA_realZeros

end RHTower
