import GaloisForLFunctions.ExclusionOfTheCriticalState.TheForwardPrimeMinusPoleWaveIsBoundedInMeanSquare
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTiltedStateLiesInTheEnergyDomain
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyNormControlsTheValuesAtTheZeros

/-!
# The state decays past the barrier at the rate of the zeros

The comparison argument gives the critical state `F` the square moments `∫ F² e^{-bu} < ∞` for
`b < 15`: against the pointwise barrier `e^{βu}` the forward prime sum costs `e^{-(β + 1/2)u}`,
which the confinement `a e^{-8u}` absorbs only for `β < 15/2`. The barrier is an artefact of
absolute values. The forward prime sum and the forward half of the pole term cancel to the wave
with transform `-N(1/2 + p) L F(p)`, `N` the regular part of `ζ'/ζ`, and this wave is bounded
in mean square on every line to the right of the zeros.

If every centred zero has `Re z ≤ κ`, then `∫ F² e^{-bu} du < ∞` for every `b < 31/2 - κ`;
unconditionally for every `b < 15 + 3001/24000`.

Mechanism (Agmon). Test the weak equation with `G_N = ψ_N F`, `ψ_N = e^{-2c max(u, -N)}`,
`c = 4 - σ`:

  `a ∫ ψ_N F² e^{-8u} = prime(F, G_N) - pole(F, G_N) - γ(F, G_N)`.

* `γ(F, G_N)` is the jump energy of `ψ_N^{1/2} F` minus a commutator and a mass term; the
  commutator is bounded by `∫ F² e^{-4cu}`, a moment below the barrier because `4c < 15`.
* The backward halves of the prime and pole terms pair `G_N` with `F` further to the left and
  are bounded by moments below the barrier.
* The forward halves combine to the wave:
  `(forward prime - forward pole)² ≤ M ∫ G_N² e^{-2σv} ≤ M ∫ ψ_N F² e^{-8v}`, since
  `ψ_N e^{-2σv} ≤ e^{-8v}`. The mass `M` of `N(1/2 + p) L F(p)` on `Re p = σ` is finite for
  `σ > 1/4 + κ/2`: there `|N|²` grows at most like a logarithm, which the Gamma energy pays.

So `Y_N = ∫ ψ_N F² e^{-8u}` satisfies `a Y_N ≤ √(M Y_N) + K` and is bounded in `N`; Fatou's
lemma gives `∫ F² e^{-(16 - 2σ)u} < ∞`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### Moments of a decaying profile and of its weighted copies -/

/-- A square moment `∫ F² e^{-bu}` controls the absolute moments `∫ |F| e^{-mu}`, `2m < b`. -/
theorem integrable_abs_mul_exp_neg_of_decay {F : ℝ → ℝ} (hFm : Measurable F)
    (hsupp : ∀ u, 0 ≤ u → F u = 0) {b m : ℝ}
    (hb : Integrable fun u => F u ^ 2 * Real.exp (-(b * u))) (hm : 2 * m < b) :
    Integrable fun u => |F u| * Real.exp (-(m * u)) := by
  refine (integrable_abs_mul_exp_of_sq hFm hsupp hb (c := -m) (by linarith)).congr
    (Eventually.of_forall fun u => ?_)
  show |F u| * Real.exp (-m * u) = |F u| * Real.exp (-(m * u))
  rw [neg_mul]

theorem mul_truncatedTilt_mul_nonneg (c N : ℝ) (F : ℝ → ℝ) (u : ℝ) :
    0 ≤ F u * (truncatedTilt c N u * F u) := by
  have e : F u * (truncatedTilt c N u * F u) = truncatedTilt c N u * F u ^ 2 := by ring
  rw [e]
  exact mul_nonneg (truncatedTilt_pos _ _ _).le (sq_nonneg _)

theorem integrable_truncatedTilt_mul_sq_mul_exp {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc0 : 0 ≤ c) (N : ℝ) :
    Integrable fun u => truncatedTilt c N u * (F u ^ 2 * Real.exp (-(8 * u))) := by
  refine (hF.exponential.const_mul (Real.exp (c * N))).mono'
    ((continuous_truncatedTilt c N).measurable.mul
      ((hF.meas.pow_const 2).mul (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  have h0 : 0 ≤ F u ^ 2 * Real.exp (-(8 * u)) := mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [Real.norm_of_nonneg (mul_nonneg (truncatedTilt_pos _ _ _).le h0)]
  exact mul_le_mul_of_nonneg_right (truncatedTilt_le_exp hc0 N u) h0

/-- `|ψ_N F| e^{mv} ≤ |F| e^{-(c - m)v}` for the weight `ψ_N = e^{-c max(v, -N)}`. -/
theorem abs_truncatedTilt_mul_mul_exp_le {c : ℝ} (hc0 : 0 ≤ c) (N : ℝ) (F : ℝ → ℝ) (m v : ℝ) :
    |truncatedTilt c N v * F v| * Real.exp (m * v) ≤ |F v| * Real.exp (-((c - m) * v)) := by
  rw [abs_mul, abs_of_pos (truncatedTilt_pos c N v)]
  have h := truncatedTilt_le_exp_neg hc0 N v
  have e : Real.exp (-((c - m) * v)) = Real.exp (-(c * v)) * Real.exp (m * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [e]
  calc truncatedTilt c N v * |F v| * Real.exp (m * v)
      ≤ Real.exp (-(c * v)) * |F v| * Real.exp (m * v) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (abs_nonneg _))
          (Real.exp_pos _).le
    _ = |F v| * (Real.exp (-(c * v)) * Real.exp (m * v)) := by ring

theorem integrable_abs_truncatedTilt_mul_mul_exp {F : ℝ → ℝ} (hFm : Measurable F) {c : ℝ}
    (hc0 : 0 ≤ c) (N m : ℝ) (hI : Integrable fun v => |F v| * Real.exp (-((c - m) * v))) :
    Integrable (fun v => |truncatedTilt c N v * F v| * Real.exp (m * v)) ∧
      (∫ v, |truncatedTilt c N v * F v| * Real.exp (m * v)) ≤
        ∫ v, |F v| * Real.exp (-((c - m) * v)) := by
  have hpt := abs_truncatedTilt_mul_mul_exp_le hc0 N F m
  have hm : AEStronglyMeasurable (fun v => |truncatedTilt c N v * F v| * Real.exp (m * v))
      volume :=
    ((((continuous_truncatedTilt c N).measurable.mul hFm).abs).mul
      (by fun_prop : Measurable fun v : ℝ => Real.exp (m * v))).aestronglyMeasurable
  have h0 : ∀ v, 0 ≤ |truncatedTilt c N v * F v| * Real.exp (m * v) := fun v =>
    mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨hI.mono' hm (Eventually.of_forall fun v => ?_),
    integral_mono_of_nonneg (Eventually.of_forall h0) hI (Eventually.of_forall hpt)⟩
  rw [Real.norm_of_nonneg (h0 v)]
  exact hpt v

/-! ### The commutator below the barrier -/

/-- **The localization identity with its commutator bound.** For every lag `x > 0` the jump
integral of `φF` exceeds the mixed jump integral of `F` and `φ²F` by at most
`min(cx, 1)² (∫ F² e^{-4cu} + ∫ F²)/2`. -/
theorem integral_sq_jump_truncatedTilt_le_of_decay {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc0 : 0 ≤ c)
    (h4 : Integrable fun u => F u ^ 2 * Real.exp (-(4 * c * u))) (N : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
      (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
        truncatedTilt (2 * c) N (u + x) * F (u + x))) ≤
        min (c * x) 1 ^ 2 *
          (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) := by
  have h2c : (0 : ℝ) ≤ 2 * c := by positivity
  have hH := criticalHalfLineEnergyDomain_truncatedTilt_mul hF hc0 N
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hF h2c N
  have hFm := hF.memLp_real
  have hHm := hH.memLp_real
  have hGm := hG.memLp_real
  have iH : Integrable fun u =>
      (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 :=
    integrable_sq_of_memLp (hHm.sub (memLp_two_shift hHm x))
  have iM : Integrable fun u => (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
      truncatedTilt (2 * c) N (u + x) * F (u + x)) :=
    integrable_mul_of_memLp (hFm.sub (memLp_two_shift hFm x)) (hGm.sub (memLp_two_shift hGm x))
  have iS : Integrable fun u => F (u + x) ^ 2 := hF.sq.comp_add_right x
  have hshift : (∫ u, F (u + x) ^ 2) = ∫ u, F u ^ 2 :=
    integral_add_right_eq_self (fun v => F v ^ 2) x
  have hm0 : 0 ≤ min (c * x) 1 ^ 2 := sq_nonneg _
  have iB : Integrable fun u => min (c * x) 1 ^ 2 *
      ((F u ^ 2 * Real.exp (-(4 * c * u)) + F (u + x) ^ 2) / 2) :=
    ((h4.add iS).div_const 2).const_mul _
  have hpt : ∀ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 -
      (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
        truncatedTilt (2 * c) N (u + x) * F (u + x)) ≤
        min (c * x) 1 ^ 2 * ((F u ^ 2 * Real.exp (-(4 * c * u)) + F (u + x) ^ 2) / 2) := by
    intro u
    have hj := truncatedTilt_jump hc0 N u hx.le
    have s1 := truncatedTilt_sq c N u
    have s2 := truncatedTilt_sq c N (u + x)
    -- the fourth power of the weight is a moment below the barrier
    have hg : (truncatedTilt c N u ^ 2 * F u) ^ 2 ≤ F u ^ 2 * Real.exp (-(4 * c * u)) := by
      have h := truncatedTilt_le_exp_neg (by positivity : (0 : ℝ) ≤ 2 * (2 * c)) N u
      rw [show 2 * (2 * c) * u = 4 * c * u by ring] at h
      calc (truncatedTilt c N u ^ 2 * F u) ^ 2
          = F u ^ 2 * truncatedTilt (2 * (2 * c)) N u := by
            rw [mul_pow, s1, truncatedTilt_sq (2 * c) N u]
            ring
        _ ≤ F u ^ 2 * Real.exp (-(4 * c * u)) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
    have e : (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 -
        (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
          truncatedTilt (2 * c) N (u + x) * F (u + x)) =
          F u * F (u + x) * (truncatedTilt c N u - truncatedTilt c N (u + x)) ^ 2 := by
      rw [← s1, ← s2]
      ring
    rw [e]
    have h1 : F u * F (u + x) * (truncatedTilt c N u - truncatedTilt c N (u + x)) ^ 2 ≤
        |F u * F (u + x)| * (truncatedTilt c N u ^ 2 * min (c * x) 1 ^ 2) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hj (abs_nonneg _))
    have h3 : |F u * F (u + x)| * truncatedTilt c N u ^ 2 ≤
        ((truncatedTilt c N u ^ 2 * F u) ^ 2 + F (u + x) ^ 2) / 2 := by
      have e3 : |F u * F (u + x)| * truncatedTilt c N u ^ 2 =
          |truncatedTilt c N u ^ 2 * F u| * |F (u + x)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (truncatedTilt c N u))]
        ring
      rw [e3]
      nlinarith [sq_nonneg (|truncatedTilt c N u ^ 2 * F u| - |F (u + x)|),
        sq_abs (truncatedTilt c N u ^ 2 * F u), sq_abs (F (u + x))]
    calc F u * F (u + x) * (truncatedTilt c N u - truncatedTilt c N (u + x)) ^ 2
        ≤ |F u * F (u + x)| * (truncatedTilt c N u ^ 2 * min (c * x) 1 ^ 2) := h1
      _ = min (c * x) 1 ^ 2 * (|F u * F (u + x)| * truncatedTilt c N u ^ 2) := by ring
      _ ≤ min (c * x) 1 ^ 2 * (((truncatedTilt c N u ^ 2 * F u) ^ 2 + F (u + x) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left h3 hm0
      _ ≤ min (c * x) 1 ^ 2 * ((F u ^ 2 * Real.exp (-(4 * c * u)) + F (u + x) ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hm0
  have hE : (∫ u, min (c * x) 1 ^ 2 *
      ((F u ^ 2 * Real.exp (-(4 * c * u)) + F (u + x) ^ 2) / 2)) =
      min (c * x) 1 ^ 2 *
        (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) := by
    rw [integral_const_mul, integral_div, integral_add h4 iS, hshift]
  calc (∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
        (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
          truncatedTilt (2 * c) N (u + x) * F (u + x)))
      = ∫ u, ((truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 -
          (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
            truncatedTilt (2 * c) N (u + x) * F (u + x))) := (integral_sub iH iM).symm
    _ ≤ ∫ u, min (c * x) 1 ^ 2 *
          ((F u ^ 2 * Real.exp (-(4 * c * u)) + F (u + x) ^ 2) / 2) :=
        integral_mono (iH.sub iM) iB hpt
    _ = _ := hE

/-- The jump energy of `φF` exceeds the mixed jump form of `F` and `φ²F` by a commutator
bounded by moments below the barrier. -/
theorem levyEnergy_truncatedTilt_sub_levyMixed_le_of_decay {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {c : ℝ} (hc0 : 0 ≤ c)
    (h4 : Integrable fun u => F u ^ 2 * Real.exp (-(4 * c * u))) (N : ℝ) :
    (∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
      levyMixed F (fun u => truncatedTilt (2 * c) N u * F u) ≤
        (3 * c ^ 2 + 2) *
          (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
            ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2)) := by
  have hH := criticalHalfLineEnergyDomain_truncatedTilt_mul hF hc0 N
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hF (by positivity : (0 : ℝ) ≤ 2 * c) N
  have hE0 : 0 ≤ ((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2 :=
    div_nonneg (add_nonneg
      (integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      (integral_nonneg fun u => sq_nonneg _)) two_pos.le
  have i1 := hH.integrableOn_levyIntegrand
  have i2 := integrableOn_levyMixedIntegrand hF hG
  have hB : IntegrableOn (fun x : ℝ => (3 * c ^ 2 + 2) *
      (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
        Real.exp (-(x / 2))) (Ioi 0) := integrableOn_exp_neg_half.const_mul _
  have key : ∀ x ∈ Ioi (0 : ℝ),
      archLevyDensity x * (∫ u, (truncatedTilt c N u * F u -
        truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
      archLevyDensity x * (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
        truncatedTilt (2 * c) N (u + x) * F (u + x))) ≤
        (3 * c ^ 2 + 2) *
          (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
            Real.exp (-(x / 2)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hA := integral_sq_jump_truncatedTilt_le_of_decay hF hc0 h4 N hx0
    have hmin := archLevyDensity_mul_min_sq_le hc0 zero_le_one hx0
    rw [one_pow, mul_one] at hmin
    have h1 := mul_le_mul_of_nonneg_left hA (archLevyDensity_pos hx0).le
    have h2 := mul_le_mul_of_nonneg_right hmin hE0
    nlinarith [h1, h2]
  calc (∫ x in Ioi (0 : ℝ), archLevyDensity x *
        ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
        levyMixed F (fun u => truncatedTilt (2 * c) N u * F u)
      = ∫ x in Ioi (0 : ℝ), (archLevyDensity x * (∫ u, (truncatedTilt c N u * F u -
          truncatedTilt c N (u + x) * F (u + x)) ^ 2) -
          archLevyDensity x * (∫ u, (F u - F (u + x)) * (truncatedTilt (2 * c) N u * F u -
            truncatedTilt (2 * c) N (u + x) * F (u + x)))) := (integral_sub i1 i2).symm
    _ ≤ ∫ x in Ioi (0 : ℝ), (3 * c ^ 2 + 2) *
          (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
            Real.exp (-(x / 2)) := setIntegral_mono_on (i1.sub i2) hB measurableSet_Ioi key
    _ = _ := integral_const_mul _ _

/-- **The Gamma pairing of a profile with its weighted copy is bounded below**, uniformly in the
truncation, by moments below the barrier: the jump energy of `φF` is nonnegative and the
commutator is bounded. -/
theorem neg_le_gammaMixedForm_truncatedTilt {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc0 : 0 ≤ c) (h2 : Integrable fun u => F u ^ 2 * Real.exp (-(2 * c * u)))
    (h4 : Integrable fun u => F u ^ 2 * Real.exp (-(4 * c * u))) (N : ℝ) :
    -(2 * |gammaHardyPhaseRate 0| * (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
        (3 * c ^ 2 + 2) *
          (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
            ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2))) ≤
      gammaMixedForm F (fun u => truncatedTilt (2 * c) N u * F u) := by
  have h2c : (0 : ℝ) ≤ 2 * c := by positivity
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hF h2c N
  have hL := gammaMixedForm_eq_levy hF hG
  have hB := levyEnergy_truncatedTilt_sub_levyMixed_le_of_decay hF hc0 h4 N
  have hlevy0 : 0 ≤ ∫ x in Ioi (0 : ℝ), archLevyDensity x *
      ∫ u, (truncatedTilt c N u * F u - truncatedTilt c N (u + x) * F (u + x)) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioi fun x hx =>
      mul_nonneg (archLevyDensity_pos hx).le (integral_nonneg fun u => sq_nonneg _)
  have hI0 : 0 ≤ ∫ u, F u * (truncatedTilt (2 * c) N u * F u) :=
    integral_nonneg fun u => mul_truncatedTilt_mul_nonneg (2 * c) N F u
  have hI1 : (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) := by
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun u => mul_truncatedTilt_mul_nonneg (2 * c) N F u) h2
      (Eventually.of_forall fun u => ?_)
    show F u * (truncatedTilt (2 * c) N u * F u) ≤ F u ^ 2 * Real.exp (-(2 * c * u))
    have e : F u * (truncatedTilt (2 * c) N u * F u) = F u ^ 2 * truncatedTilt (2 * c) N u := by
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (truncatedTilt_le_exp_neg h2c N u) (sq_nonneg _)
  have h1 : -|gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      gammaHardyPhaseRate 0 * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) :=
    mul_le_mul_of_nonneg_right (neg_abs_le _) hI0
  have h3 : |gammaHardyPhaseRate 0| * (∫ u, F u * (truncatedTilt (2 * c) N u * F u)) ≤
      |gammaHardyPhaseRate 0| * ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) :=
    mul_le_mul_of_nonneg_left hI1 (abs_nonneg _)
  rw [hL]
  linarith

/-! ### The backward half of the prime form -/

/-- A backward shift against the weighted copy: the weight at `t + ℓ` is paid by both factors
and leaves `e^{-cℓ}`. -/
theorem abs_integral_mul_truncatedTilt_shift_le {F : ℝ → ℝ} {c : ℝ} (hc0 : 0 ≤ c)
    (h2 : Integrable fun u => F u ^ 2 * Real.exp (-(2 * c * u))) (N ℓ : ℝ) :
    |∫ t, F t * (truncatedTilt (2 * c) N (t + ℓ) * F (t + ℓ))| ≤
      Real.exp (-(c * ℓ)) * ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) := by
  have iS : Integrable fun t => F (t + ℓ) ^ 2 * Real.exp (-(2 * c * (t + ℓ))) :=
    h2.comp_add_right ℓ
  have hshift : (∫ t, F (t + ℓ) ^ 2 * Real.exp (-(2 * c * (t + ℓ)))) =
      ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) :=
    integral_add_right_eq_self (fun v => F v ^ 2 * Real.exp (-(2 * c * v))) ℓ
  have iB : Integrable fun t => Real.exp (-(c * ℓ)) *
      ((F t ^ 2 * Real.exp (-(2 * c * t)) +
        F (t + ℓ) ^ 2 * Real.exp (-(2 * c * (t + ℓ)))) / 2) :=
    ((h2.add iS).div_const 2).const_mul _
  have hpt : ∀ t, ‖F t * (truncatedTilt (2 * c) N (t + ℓ) * F (t + ℓ))‖ ≤
      Real.exp (-(c * ℓ)) * ((F t ^ 2 * Real.exp (-(2 * c * t)) +
        F (t + ℓ) ^ 2 * Real.exp (-(2 * c * (t + ℓ)))) / 2) := by
    intro t
    have hψ := truncatedTilt_le_exp_neg (by positivity : (0 : ℝ) ≤ 2 * c) N (t + ℓ)
    have hψ0 := (truncatedTilt_pos (2 * c) N (t + ℓ)).le
    have e1 : Real.exp (-(2 * c * (t + ℓ))) = Real.exp (-(c * ℓ)) *
        (Real.exp (-(c * t)) * Real.exp (-(c * (t + ℓ)))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have e2 : Real.exp (-(2 * c * t)) = Real.exp (-(c * t)) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have e3 : Real.exp (-(2 * c * (t + ℓ))) = Real.exp (-(c * (t + ℓ))) ^ 2 := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have hA : |F t| * (truncatedTilt (2 * c) N (t + ℓ) * |F (t + ℓ)|) ≤
        Real.exp (-(c * ℓ)) * ((|F t| * Real.exp (-(c * t))) *
          (|F (t + ℓ)| * Real.exp (-(c * (t + ℓ))))) := by
      have h1 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hψ (abs_nonneg (F (t + ℓ)))) (abs_nonneg (F t))
      rw [e1] at h1
      exact h1.trans_eq (by ring)
    have hB : (|F t| * Real.exp (-(c * t))) * (|F (t + ℓ)| * Real.exp (-(c * (t + ℓ)))) ≤
        (F t ^ 2 * Real.exp (-(2 * c * t)) +
          F (t + ℓ) ^ 2 * Real.exp (-(2 * c * (t + ℓ)))) / 2 := by
      have ha : (|F t| * Real.exp (-(c * t))) ^ 2 = F t ^ 2 * Real.exp (-(2 * c * t)) := by
        rw [mul_pow, sq_abs, e2]
      have hb : (|F (t + ℓ)| * Real.exp (-(c * (t + ℓ)))) ^ 2 =
          F (t + ℓ) ^ 2 * Real.exp (-(2 * c * (t + ℓ))) := by
        rw [mul_pow, sq_abs, e3]
      rw [← ha, ← hb]
      nlinarith [sq_nonneg (|F t| * Real.exp (-(c * t)) -
        |F (t + ℓ)| * Real.exp (-(c * (t + ℓ))))]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hψ0]
    exact hA.trans (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le)
  have h := norm_integral_le_of_norm_le iB (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at h
  refine h.trans_eq ?_
  rw [integral_const_mul, integral_div, integral_add h2 iS, hshift]
  ring

/-- **The prime form against the weighted copy is its forward half up to moments below the
barrier.** The backward shifts are summable with the weights `Λ(n) n^{-3/2}`. -/
theorem primeMixedForm_truncatedTilt_le {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {c : ℝ} (hc1 : 1 ≤ c) (h2 : Integrable fun u => F u ^ 2 * Real.exp (-(2 * c * u)))
    (N : ℝ) :
    primeMixedForm F (fun u => truncatedTilt (2 * c) N u * F u) ≤
      forwardPrimeForm F (fun u => truncatedTilt (2 * c) N u * F u) +
        (∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(1 * Real.log n))) *
          ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hF (by positivity : (0 : ℝ) ≤ 2 * c) N
  have hI0 : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) :=
    integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hsumΛ : Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) :=
    summable_vonMangoldt_div_threeHalves.congr fun n => by
      rw [vonMangoldtAtom_mul_exp_eq]
      norm_num
  have hsP := summable_primePairTerm hF.weighted hG.weighted
  have hBn : ∀ n : ℕ, |vonMangoldtAtom n * ∫ t, F t *
      (truncatedTilt (2 * c) N (t + Real.log n) * F (t + Real.log n))| ≤
      vonMangoldtAtom n * Real.exp (-(1 * Real.log n)) *
        ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) := by
    intro n
    have hℓ : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have h := abs_integral_mul_truncatedTilt_shift_le hc0 h2 N (Real.log n)
    have he : Real.exp (-(c * Real.log n)) ≤ Real.exp (-(1 * Real.log n)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n), mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_right he hI0))
      (vonMangoldtAtom_nonneg n)
  have hsB : Summable fun n : ℕ => vonMangoldtAtom n * ∫ t, F t *
      (truncatedTilt (2 * c) N (t + Real.log n) * F (t + Real.log n)) :=
    Summable.of_norm_bounded (hsumΛ.mul_right _) fun n => by
      simpa only [Real.norm_eq_abs] using hBn n
  have hsA : Summable fun n : ℕ => vonMangoldtAtom n * ∫ t, F t *
      (truncatedTilt (2 * c) N (t - Real.log n) * F (t - Real.log n)) :=
    (hsP.sub hsB).congr fun n => by
      show primePairTerm F (fun u => truncatedTilt (2 * c) N u * F u) n -
        vonMangoldtAtom n * (∫ t, F t *
          (truncatedTilt (2 * c) N (t + Real.log n) * F (t + Real.log n))) = _
      unfold primePairTerm
      ring
  -- the forward half, after the change of variable `t ↦ t - log n`
  have hfwd : forwardPrimeForm F (fun u => truncatedTilt (2 * c) N u * F u) =
      ∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t *
        (truncatedTilt (2 * c) N (t - Real.log n) * F (t - Real.log n)) := by
    unfold forwardPrimeForm
    refine tsum_congr fun n => ?_
    congr 1
    refine (integral_sub_right_eq_self (fun s : ℝ =>
      truncatedTilt (2 * c) N s * F s * F (s + Real.log n)) (Real.log n)).symm.trans ?_
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show truncatedTilt (2 * c) N (t - Real.log n) * F (t - Real.log n) *
        F (t - Real.log n + Real.log n) =
      F t * (truncatedTilt (2 * c) N (t - Real.log n) * F (t - Real.log n))
    rw [sub_add_cancel]
    ring
  have hsplit : primeMixedForm F (fun u => truncatedTilt (2 * c) N u * F u) =
      (∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t *
        (truncatedTilt (2 * c) N (t - Real.log n) * F (t - Real.log n))) +
      ∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t *
        (truncatedTilt (2 * c) N (t + Real.log n) * F (t + Real.log n)) := by
    rw [← hsA.tsum_add hsB]
    unfold primeMixedForm
    refine tsum_congr fun n => ?_
    unfold primePairTerm
    ring
  have hBsum : (∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t *
      (truncatedTilt (2 * c) N (t + Real.log n) * F (t + Real.log n))) ≤
      (∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(1 * Real.log n))) *
        ∫ u, F u ^ 2 * Real.exp (-(2 * c * u)) := by
    rw [← tsum_mul_right]
    exact hsB.tsum_le_tsum (fun n => (le_abs_self _).trans (hBn n)) (hsumΛ.mul_right _)
  rw [hsplit, hfwd]
  linarith

/-! ### The pole term -/

theorem integrable_mul_exp_half {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Integrable fun u => F u * Real.exp (u / 2) := by
  refine hF.integrable.norm.mono'
    (hF.meas.mul (by fun_prop : Measurable fun u : ℝ => Real.exp (u / 2))).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rcases le_or_gt 0 u with hu | hu
  · simp [hF.support u hu]
  · rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr (by linarith))

/-- The pole term is the sum of the two exponential pairings:
`2 C(F) C(G) - 2 S(F) S(G) = ∫∫ F(u) G(v) (e^{(u - v)/2} + e^{(v - u)/2})`. -/
theorem two_cosh_mul_sub_two_sinh_mul {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) :
    2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G =
      (∫ u, F u * Real.exp (u / 2)) * (∫ v, G v * Real.exp (-(v / 2))) +
        (∫ u, F u * Real.exp (-(u / 2))) * ∫ v, G v * Real.exp (v / 2) := by
  have hc : ∀ {H : ℝ → ℝ}, CriticalHalfLineEnergyDomain H → coshHalfMoment H =
      ((∫ u, H u * Real.exp (u / 2)) + ∫ u, H u * Real.exp (-(u / 2))) / 2 := by
    intro H hH
    unfold coshHalfMoment
    rw [← integral_add (integrable_mul_exp_half hH) hH.integrable_polarExponential,
      ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show H u * Real.cosh (u / 2) = (H u * Real.exp (u / 2) + H u * Real.exp (-(u / 2))) / 2
    rw [Real.cosh_eq]
    ring
  have hs : ∀ {H : ℝ → ℝ}, CriticalHalfLineEnergyDomain H → sinhHalfMoment H =
      ((∫ u, H u * Real.exp (u / 2)) - ∫ u, H u * Real.exp (-(u / 2))) / 2 := by
    intro H hH
    unfold sinhHalfMoment
    rw [← integral_sub (integrable_mul_exp_half hH) hH.integrable_polarExponential,
      ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show H u * Real.sinh (u / 2) = (H u * Real.exp (u / 2) - H u * Real.exp (-(u / 2))) / 2
    rw [Real.sinh_eq]
    ring
  rw [hc hF, hc hG, hs hF, hs hG]
  ring

theorem abs_forwardPoleWave_le {F : ℝ → ℝ} (hFe : Integrable fun u => F u * Real.exp (u / 2))
    (v : ℝ) :
    |forwardPoleWave F v| ≤ Real.exp (-(v / 2)) * ∫ u, ‖F u * Real.exp (u / 2)‖ := by
  unfold forwardPoleWave
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h1 := norm_integral_le_integral_norm (μ := volume.restrict (Ioi v))
    (fun u : ℝ => F u * Real.exp (u / 2))
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (setIntegral_le_integral hFe.norm (Eventually.of_forall fun u => norm_nonneg _))

theorem integrable_mul_forwardPoleWave {F G : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    (hG : CriticalHalfLineEnergyDomain G) : Integrable fun v => G v * forwardPoleWave F v := by
  have hFe := integrable_mul_exp_half hF
  have hfm : Measurable fun y : ℝ => F (-y) := hF.meas.comp measurable_neg
  have hf0 : ∀ y : ℝ, y ≤ 0 → F (-y) = 0 := fun y hy => hF.support (-y) (by linarith)
  have hcont := continuous_poleWaveRay (integrable_exp_neg_half_mul hfm hF.integrable.comp_neg hf0)
  -- on the support of `G` the wave is a continuous function
  have heq : (fun v => G v * forwardPoleWave F v) =
      fun v => G v * poleWaveRay (fun y : ℝ => F (-y)) (-v) := by
    funext v
    rcases le_or_gt v 0 with hv | hv
    · have h := forwardPoleWave_neg hF.support (x := -v) (by linarith)
      rw [neg_neg] at h
      rw [h]
    · rw [hG.support v hv.le, zero_mul, zero_mul]
  have hm : AEStronglyMeasurable (fun v => G v * forwardPoleWave F v) volume := by
    rw [heq]
    exact (hG.meas.mul (hcont.comp continuous_neg).measurable).aestronglyMeasurable
  refine (hG.integrable_polarExponential.norm.mul_const
    (∫ u, ‖F u * Real.exp (u / 2)‖)).mono' hm (Eventually.of_forall fun v => ?_)
  have h1 := abs_forwardPoleWave_le hFe v
  calc ‖G v * forwardPoleWave F v‖ = ‖G v‖ * |forwardPoleWave F v| := by
        rw [norm_mul, Real.norm_eq_abs (forwardPoleWave F v)]
    _ ≤ ‖G v‖ * (Real.exp (-(v / 2)) * ∫ u, ‖F u * Real.exp (u / 2)‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖G v * Real.exp (-(v / 2))‖ * ∫ u, ‖F u * Real.exp (u / 2)‖ := by
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        ring

/-- **The pole pairing is its forward half up to the backward wave.** The part `u ≤ v` of
`∫∫ G(v) e^{-v/2} F(u) e^{u/2}` is at most `∫ |F| e^{-mu} · ∫ |G| e^{mv}`. -/
theorem abs_expMoment_mul_sub_forwardPoleForm_le {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hG : CriticalHalfLineEnergyDomain G) {m : ℝ}
    (hm : 0 ≤ m) (hFm : Integrable fun u => |F u| * Real.exp (-(m * u)))
    (hGm : Integrable fun v => |G v| * Real.exp (m * v)) :
    |(∫ u, F u * Real.exp (u / 2)) * (∫ v, G v * Real.exp (-(v / 2))) - forwardPoleForm F G| ≤
      (∫ u, |F u| * Real.exp (-(m * u))) * ∫ v, |G v| * Real.exp (m * v) := by
  have hFe := integrable_mul_exp_half hF
  have hGp := hG.integrable_polarExponential
  have hGw := integrable_mul_forwardPoleWave hF hG
  have hback : ∀ v : ℝ, Real.exp (-(v / 2)) * (∫ u, F u * Real.exp (u / 2)) -
      forwardPoleWave F v = Real.exp (-(v / 2)) * ∫ u in Iic v, F u * Real.exp (u / 2) := by
    intro v
    have h := integral_add_compl (measurableSet_Iic (a := v)) hFe
    rw [compl_Iic] at h
    unfold forwardPoleWave
    rw [← h]
    ring
  have hbp : ∀ v : ℝ, |∫ u in Iic v, F u * Real.exp (u / 2)| ≤
      Real.exp ((m + 1 / 2) * v) * ∫ u, |F u| * Real.exp (-(m * u)) := by
    intro v
    have h1 := norm_integral_le_integral_norm (μ := volume.restrict (Iic v))
      (fun u : ℝ => F u * Real.exp (u / 2))
    rw [Real.norm_eq_abs] at h1
    have h2 : (∫ u in Iic v, ‖F u * Real.exp (u / 2)‖) ≤
        ∫ u in Iic v, Real.exp ((m + 1 / 2) * v) * (|F u| * Real.exp (-(m * u))) := by
      refine setIntegral_mono_on hFe.norm.integrableOn (hFm.const_mul _).integrableOn
        measurableSet_Iic fun u hu => ?_
      have hu' : u ≤ v := hu
      have he : Real.exp (u / 2) ≤ Real.exp ((m + 1 / 2) * v) * Real.exp (-(m * u)) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ m + 1 / 2) (sub_nonneg.mpr hu')])
      show ‖F u * Real.exp (u / 2)‖ ≤
        Real.exp ((m + 1 / 2) * v) * (|F u| * Real.exp (-(m * u)))
      rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
      calc |F u| * Real.exp (u / 2)
          ≤ |F u| * (Real.exp ((m + 1 / 2) * v) * Real.exp (-(m * u))) :=
            mul_le_mul_of_nonneg_left he (abs_nonneg _)
        _ = Real.exp ((m + 1 / 2) * v) * (|F u| * Real.exp (-(m * u))) := by ring
    have h3 : (∫ u in Iic v, Real.exp ((m + 1 / 2) * v) * (|F u| * Real.exp (-(m * u)))) ≤
        Real.exp ((m + 1 / 2) * v) * ∫ u, |F u| * Real.exp (-(m * u)) := by
      rw [← integral_const_mul]
      exact setIntegral_le_integral (hFm.const_mul _) (Eventually.of_forall fun u =>
        mul_nonneg (Real.exp_pos _).le (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le))
    exact h1.trans (h2.trans h3)
  have e1 : (∫ u, F u * Real.exp (u / 2)) * (∫ v, G v * Real.exp (-(v / 2))) =
      ∫ v, G v * Real.exp (-(v / 2)) * ∫ u, F u * Real.exp (u / 2) := by
    rw [integral_mul_const]
    exact mul_comm _ _
  have hEq : (∫ u, F u * Real.exp (u / 2)) * (∫ v, G v * Real.exp (-(v / 2))) -
      forwardPoleForm F G =
      ∫ v, G v * (Real.exp (-(v / 2)) * ∫ u in Iic v, F u * Real.exp (u / 2)) := by
    unfold forwardPoleForm
    rw [e1, ← integral_sub (hGp.mul_const _) hGw]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    show G v * Real.exp (-(v / 2)) * (∫ u, F u * Real.exp (u / 2)) - G v * forwardPoleWave F v =
      G v * (Real.exp (-(v / 2)) * ∫ u in Iic v, F u * Real.exp (u / 2))
    rw [← hback v]
    ring
  have hbound : ∀ v : ℝ,
      ‖G v * (Real.exp (-(v / 2)) * ∫ u in Iic v, F u * Real.exp (u / 2))‖ ≤
      (∫ u, |F u| * Real.exp (-(m * u))) * (|G v| * Real.exp (m * v)) := by
    intro v
    have h := hbp v
    have he : Real.exp (-(v / 2)) * Real.exp ((m + 1 / 2) * v) = Real.exp (m * v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [norm_mul, norm_mul, Real.norm_eq_abs (G v), Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_eq_abs]
    calc |G v| * (Real.exp (-(v / 2)) * |∫ u in Iic v, F u * Real.exp (u / 2)|)
        ≤ |G v| * (Real.exp (-(v / 2)) *
            (Real.exp ((m + 1 / 2) * v) * ∫ u, |F u| * Real.exp (-(m * u)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (Real.exp_pos _).le)
            (abs_nonneg _)
      _ = (∫ u, |F u| * Real.exp (-(m * u))) *
            (|G v| * (Real.exp (-(v / 2)) * Real.exp ((m + 1 / 2) * v))) := by ring
      _ = _ := by rw [he]
  rw [hEq]
  have h := norm_integral_le_of_norm_le
    (f := fun v : ℝ => G v * (Real.exp (-(v / 2)) * ∫ u in Iic v, F u * Real.exp (u / 2)))
    (hGm.const_mul (∫ u, |F u| * Real.exp (-(m * u)))) (Eventually.of_forall hbound)
  rw [Real.norm_eq_abs, integral_const_mul] at h
  exact h

/-! ### The mass of the wave on a line to the right of the zeros -/

/-- On `Re z = σ` the transform of a profile on the negative half-line is the Fourier transform
of its damped copy `e^{σu} F`. -/
theorem negativeHalfLineLaplace_add_mul_I_eq_paperFT {F : ℝ → ℝ}
    (hsupp : ∀ u, 0 ≤ u → F u = 0) (σ t : ℝ) :
    negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I) =
      paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ) := by
  show (∫ u : ℝ, cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ)) * cx F u) =
    ∫ u : ℝ, cx (fun u => Real.exp (σ * min u 0) * F u) u * cexp (I * (t : ℂ) * (u : ℂ))
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  show cexp (((σ : ℂ) + (t : ℂ) * I) * (u : ℂ)) * ((F u : ℝ) : ℂ) =
    ((Real.exp (σ * min u 0) * F u : ℝ) : ℂ) * cexp (I * (t : ℂ) * (u : ℂ))
  rcases le_or_gt 0 u with hu | hu
  · rw [hsupp u hu]
    simp
  · rw [min_eq_left hu.le, Complex.ofReal_mul, Complex.ofReal_exp,
      show ((σ : ℂ) + (t : ℂ) * I) * (u : ℂ) = ((σ * u : ℝ) : ℂ) + I * (t : ℂ) * (u : ℂ) by
        push_cast
        ring, Complex.exp_add]
    ring

/-- The damped copy `e^{σu} F`, `σ ≥ 0`, of a profile of the domain lies in the domain. -/
theorem criticalHalfLineEnergyDomain_exp_min_mul {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {σ : ℝ} (hσ : 0 ≤ σ) :
    CriticalHalfLineEnergyDomain (fun u => Real.exp (σ * min u 0) * F u) := by
  have hle : ∀ u : ℝ, σ * min u 0 ≤ 0 := fun u =>
    mul_nonpos_of_nonneg_of_nonpos hσ (min_le_right _ _)
  refine criticalHalfLineEnergyDomain_lipschitz_mul hF
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.min continuous_const))).measurable
    (M := 1) (Λ := σ) (fun u => ?_) (fun u v => ?_)
  · rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (hle u)
  · have h := abs_exp_sub_exp_le (hle u) (hle v)
    rw [Real.exp_zero, one_mul, ← mul_sub, abs_mul, abs_of_nonneg hσ] at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hσ)
    have h2 := abs_min_sub_min_le_max u 0 v 0
    rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _)] at h2

/-- **The transform of the wave has finite mass on every line `Re p = σ > 1/4 + κ/2`.** There
`|N(1/2 + p)|²` grows at most like `log |Im p|`, and the Gamma energy of the damped profile pays
a logarithm. -/
theorem integrable_norm_sq_zetaRegularLogDeriv_mul_laplace {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκσ : κ < σ) (hσ : 1 / 4 + κ / 2 < σ)
    {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    Integrable fun t : ℝ => ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 *
      ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  obtain ⟨C, hC, hN⟩ := exists_norm_sq_zetaRegularLogDeriv_line_le_log hκ hzero hκσ hσ
  have hH := criticalHalfLineEnergyDomain_exp_min_mul hF (hκ.trans hκσ.le)
  have hP := integrable_norm_sq_paperFT_cx hH.integrable hH.sq
  have hL := integrable_log_mul_norm_sq_paperFT hH
  have hlog : Integrable fun t : ℝ => Real.log (|t| + 4) *
      ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2 :=
    (hL.sub (hP.const_mul xiLineTwoLogDerivConstant)).congr (Eventually.of_forall fun t => by
      show (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
          ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2 -
        xiLineTwoLogDerivConstant *
          ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2 =
        Real.log (|t| + 4) * ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2
      ring)
  have hcont : Continuous fun t : ℝ =>
      ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 := by
    refine (continuous_iff_continuousAt.mpr fun t => ?_).norm.pow 2
    have h1 := differentiableAt_zetaRegularLogDeriv_half_add hκ hzero
      (p := (σ : ℂ) + (t : ℂ) * I) (by simpa using hκσ)
    have h2 : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) t := by fun_prop
    exact ContinuousAt.comp (g := fun p : ℂ => zetaRegularLogDeriv (1 / 2 + p)) h1.continuousAt h2
  have heq : ∀ t : ℝ, negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I) =
      paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ) := fun t =>
    negativeHalfLineLaplace_add_mul_I_eq_paperFT hF.support σ t
  simp only [heq]
  refine (hlog.const_mul C).mono' (hcont.aestronglyMeasurable.mul hP.aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
  calc ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2
      ≤ C * Real.log (|t| + 4) *
          ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hN t) (sq_nonneg _)
    _ = C * (Real.log (|t| + 4) *
          ‖paperFT (cx fun u => Real.exp (σ * min u 0) * F u) (t : ℂ)‖ ^ 2) := by ring

/-! ### The Agmon bound past the barrier -/

/-- **The weighted confinement masses are bounded uniformly in the truncation.** With
`c = 4 - σ` and `σ` a line to the right of the zeros and of `1/4 + κ/2`, the weak equation
against `e^{-2c max(u, -N)} F` bounds `∫ e^{-2c max(u, -N)} F² e^{-8u}`. -/
theorem exists_integral_truncatedTilt_mul_sq_mul_exp_le {κ σ c : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκσ : κ < σ) (hσ : 1 / 4 + κ / 2 < σ)
    (hσ1 : σ < 1) (hcσ : c + σ = 4) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ K : ℝ, ∀ N : ℝ,
      (∫ u, truncatedTilt (2 * c) N u * (F u ^ 2 * Real.exp (-(8 * u)))) ≤ K := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hdec := (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).2
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hc1 : (1 : ℝ) ≤ c := by linarith
  have h2c0 : (0 : ℝ) ≤ 2 * c := by linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = criticalAliasCoefficient W₀ := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [hadef]
    exact criticalAliasCoefficient_positive hW
  have h2 : Integrable fun u => F u ^ 2 * Real.exp (-(2 * c * u)) := hdec (2 * c) (by linarith)
  have h4 : Integrable fun u => F u ^ 2 * Real.exp (-(4 * c * u)) := hdec (4 * c) (by linarith)
  have hJ4 : Integrable fun u => |F u| * Real.exp (-(4 * u)) :=
    integrable_abs_mul_exp_neg_of_decay hd.meas hd.support (hdec 14 (by norm_num)) (by norm_num)
  have hJ1 : Integrable fun v => |F v| * Real.exp (-((2 * c - 4) * v)) :=
    integrable_abs_mul_exp_neg_of_decay hd.meas hd.support (hdec 14 (by norm_num)) (by linarith)
  have hJ2 : Integrable fun v => |F v| * Real.exp (-((2 * c - 1 / 2) * v)) :=
    integrable_abs_mul_exp_neg_of_decay hd.meas hd.support (hdec (15 - 2 * σ) (by linarith))
      (by linarith)
  have hB := integrable_norm_sq_zetaRegularLogDeriv_mul_laplace hκ hzero hκσ hσ hd
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = (2 * Real.pi)⁻¹ * ∫ t : ℝ,
      ‖zetaRegularLogDeriv (1 / 2 + ((σ : ℂ) + (t : ℂ) * I))‖ ^ 2 *
        ‖negativeHalfLineLaplace (cx F) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (by positivity)
      (integral_nonneg fun t => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hJ40 : 0 ≤ ∫ u, |F u| * Real.exp (-(4 * u)) :=
    integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨2 / a * (M / (2 * a) +
    (∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(1 * Real.log n))) *
      (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
    (∫ u, |F u| * Real.exp (-(4 * u))) * (∫ v, |F v| * Real.exp (-((2 * c - 4) * v))) +
    |∫ u, F u * Real.exp (-(u / 2))| * (∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v))) +
    (2 * |gammaHardyPhaseRate 0| * (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
      (3 * c ^ 2 + 2) * (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
        ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2)))), fun N => ?_⟩
  have hG := criticalHalfLineEnergyDomain_truncatedTilt_mul hd h2c0 N
  have hYint := integrable_truncatedTilt_mul_sq_mul_exp hd h2c0 N
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ,
      Y = ∫ u, truncatedTilt (2 * c) N u * (F u ^ 2 * Real.exp (-(8 * u))) := ⟨_, rfl⟩
  rw [← hYdef]
  have hY0 : 0 ≤ Y := by
    rw [hYdef]
    exact integral_nonneg fun u => mul_nonneg (truncatedTilt_pos _ _ _).le
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  -- the weak equation against the weighted copy
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hG
  unfold criticalHalfLineMixedEnergy at hw
  rw [primeMixedForm_symm (fun u => truncatedTilt (2 * c) N u * F u) F, ← hadef] at hw
  have e1 : (∫ u in Iio (0 : ℝ), F u * (truncatedTilt (2 * c) N u * F u) *
      Real.exp (-(8 * u))) =
      ∫ u, F u * (truncatedTilt (2 * c) N u * F u) * Real.exp (-(8 * u)) :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by
      rw [hd.support u (not_lt.mp hu)]
      ring
  have hconf : (∫ u in Iio (0 : ℝ), F u * (truncatedTilt (2 * c) N u * F u) *
      Real.exp (-(8 * u))) = Y := by
    rw [e1, hYdef]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show F u * (truncatedTilt (2 * c) N u * F u) * Real.exp (-(8 * u)) =
      truncatedTilt (2 * c) N u * (F u ^ 2 * Real.exp (-(8 * u)))
    ring
  rw [hconf] at hw
  -- Gamma, prime and pole terms
  have hΓ := neg_le_gammaMixedForm_truncatedTilt hd hc0 h2 h4 N
  have hP := primeMixedForm_truncatedTilt_le hd hc1 h2 N
  have hpole := two_cosh_mul_sub_two_sinh_mul hd hG
  have hG4 := integrable_abs_truncatedTilt_mul_mul_exp hd.meas h2c0 N 4 hJ1
  have hGh := integrable_abs_truncatedTilt_mul_mul_exp hd.meas h2c0 N (1 / 2) hJ2
  have hC2 := (abs_expMoment_mul_sub_forwardPoleForm_le hd hG (m := 4) (by norm_num) hJ4
    hG4.1).trans (mul_le_mul_of_nonneg_left hG4.2 hJ40)
  have hC2a := (abs_le.mp hC2).1
  have hEp : |∫ v, truncatedTilt (2 * c) N v * F v * Real.exp (v / 2)| ≤
      ∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v)) := by
    have h := norm_integral_le_of_norm_le
      (f := fun v : ℝ => truncatedTilt (2 * c) N v * F v * Real.exp (v / 2)) hGh.1
      (Eventually.of_forall fun v => le_of_eq (by
        show ‖truncatedTilt (2 * c) N v * F v * Real.exp (v / 2)‖ =
          |truncatedTilt (2 * c) N v * F v| * Real.exp (1 / 2 * v)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le,
          show v / 2 = 1 / 2 * v by ring]))
    rw [Real.norm_eq_abs] at h
    exact h.trans hGh.2
  have hEm : -(|∫ u, F u * Real.exp (-(u / 2))| *
      ∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v))) ≤
      (∫ u, F u * Real.exp (-(u / 2))) *
        ∫ v, truncatedTilt (2 * c) N v * F v * Real.exp (v / 2) := by
    have h1 := neg_abs_le ((∫ u, F u * Real.exp (-(u / 2))) *
      ∫ v, truncatedTilt (2 * c) N v * F v * Real.exp (v / 2))
    rw [abs_mul] at h1
    have h3 := mul_le_mul_of_nonneg_left hEp (abs_nonneg (∫ u, F u * Real.exp (-(u / 2))))
    linarith
  -- the forward halves combine to the wave
  have hD := sq_forwardPrimeForm_sub_forwardPoleForm_le hκ hzero hκσ hσ1 hd hG hB
  rw [← hMdef] at hD
  have hGY : (∫ v, (truncatedTilt (2 * c) N v * F v) ^ 2 * Real.exp (-(2 * σ * v))) ≤ Y := by
    rw [hYdef]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hYint
      (Eventually.of_forall fun v => ?_)
    have hψ := truncatedTilt_le_exp_neg h2c0 N v
    have hψ0 := (truncatedTilt_pos (2 * c) N v).le
    have e : Real.exp (-(2 * c * v)) * Real.exp (-(2 * σ * v)) = Real.exp (-(8 * v)) := by
      rw [← Real.exp_add]
      congr 1
      linear_combination (-2 * v) * hcσ
    show (truncatedTilt (2 * c) N v * F v) ^ 2 * Real.exp (-(2 * σ * v)) ≤
      truncatedTilt (2 * c) N v * (F v ^ 2 * Real.exp (-(8 * v)))
    calc (truncatedTilt (2 * c) N v * F v) ^ 2 * Real.exp (-(2 * σ * v))
        = truncatedTilt (2 * c) N v *
            (F v ^ 2 * (truncatedTilt (2 * c) N v * Real.exp (-(2 * σ * v)))) := by ring
      _ ≤ truncatedTilt (2 * c) N v *
            (F v ^ 2 * (Real.exp (-(2 * c * v)) * Real.exp (-(2 * σ * v)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hψ (Real.exp_pos _).le) (sq_nonneg _)) hψ0
      _ = _ := by rw [e]
  have hD' : (forwardPrimeForm F (fun u => truncatedTilt (2 * c) N u * F u) -
      forwardPoleForm F (fun u => truncatedTilt (2 * c) N u * F u)) ^ 2 ≤ M * Y :=
    hD.trans (mul_le_mul_of_nonneg_left hGY hM0)
  have hx : forwardPrimeForm F (fun u => truncatedTilt (2 * c) N u * F u) -
      forwardPoleForm F (fun u => truncatedTilt (2 * c) N u * F u) ≤
        a * Y / 2 + M / (2 * a) := by
    have hpos : 0 ≤ a * Y / 2 + M / (2 * a) :=
      add_nonneg (div_nonneg (mul_nonneg ha.le hY0) two_pos.le)
        (div_nonneg hM0 (mul_pos two_pos ha).le)
    refine le_of_not_gt fun hlt => ?_
    have h1 := pow_lt_pow_left₀ hlt hpos (n := 2) two_ne_zero
    have ha' := ha.ne'
    have e : (a * Y / 2 + M / (2 * a)) ^ 2 = (a * Y / 2 - M / (2 * a)) ^ 2 + M * Y := by
      field_simp
      ring
    rw [e] at h1
    linarith [sq_nonneg (a * Y / 2 - M / (2 * a))]
  -- absorb
  have hfin : a * Y ≤ 2 * (M / (2 * a) +
      (∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(1 * Real.log n))) *
        (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
      (∫ u, |F u| * Real.exp (-(4 * u))) * (∫ v, |F v| * Real.exp (-((2 * c - 4) * v))) +
      |∫ u, F u * Real.exp (-(u / 2))| * (∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v))) +
      (2 * |gammaHardyPhaseRate 0| * (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
        (3 * c ^ 2 + 2) * (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
          ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2)))) := by
    linarith
  calc Y = a * Y / a := (mul_div_cancel_left₀ Y ha.ne').symm
    _ ≤ 2 * (M / (2 * a) +
        (∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(1 * Real.log n))) *
          (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
        (∫ u, |F u| * Real.exp (-(4 * u))) * (∫ v, |F v| * Real.exp (-((2 * c - 4) * v))) +
        |∫ u, F u * Real.exp (-(u / 2))| * (∫ v, |F v| * Real.exp (-((2 * c - 1 / 2) * v))) +
        (2 * |gammaHardyPhaseRate 0| * (∫ u, F u ^ 2 * Real.exp (-(2 * c * u))) +
          (3 * c ^ 2 + 2) * (((∫ u, F u ^ 2 * Real.exp (-(4 * c * u))) + ∫ u, F u ^ 2) / 2) *
            ∫ x in Ioi (0 : ℝ), Real.exp (-(x / 2)))) / a :=
        div_le_div_of_nonneg_right hfin ha.le
    _ = _ := by ring

/-- **Decay on a line to the right of the zeros.** If every centred zero has `Re z ≤ κ` and
`max(κ, 1/4 + κ/2) < σ < 1`, then `∫ F² e^{-(16 - 2σ)u} du < ∞`. -/
theorem integrable_sq_mul_exp_of_right_line {κ σ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) (hκσ : κ < σ) (hσ : 1 / 4 + κ / 2 < σ)
    (hσ1 : σ < 1) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Integrable fun u => F u ^ 2 * Real.exp (-((16 - 2 * σ) * u)) := by
  obtain ⟨K, hK⟩ := exists_integral_truncatedTilt_mul_sq_mul_exp_le hκ hzero hκσ hσ hσ1
    (c := 4 - σ) (by ring) hW hthreshold hF
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hc0 : (0 : ℝ) ≤ 2 * (4 - σ) := by linarith
  have h0 : ∀ u, 0 ≤ F u ^ 2 * Real.exp (-((16 - 2 * σ) * u)) := fun u =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  refine ⟨((hd.meas.pow_const 2).mul (by fun_prop)).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall h0)).mpr ?_⟩
  have hYint : ∀ N : ℕ, Integrable fun u =>
      truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u))) := fun N =>
    integrable_truncatedTilt_mul_sq_mul_exp hd hc0 N
  -- the truncated weights increase to the full weight
  have hpt : ∀ u : ℝ, Tendsto (fun N : ℕ =>
      truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u)))) atTop
      (𝓝 (F u ^ 2 * Real.exp (-((16 - 2 * σ) * u)))) := by
    intro u
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop ⌈-u⌉₊] with N hN
    rw [truncatedTilt_eq_exp_neg (by linarith [Nat.ceil_le.mp hN])]
    have e : Real.exp (-((16 - 2 * σ) * u)) =
        Real.exp (-(2 * (4 - σ) * u)) * Real.exp (-(8 * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e]
    ring
  have hliminf : ∀ u : ℝ, liminf (fun N : ℕ => ENNReal.ofReal
      (truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u))))) atTop =
      ENNReal.ofReal (F u ^ 2 * Real.exp (-((16 - 2 * σ) * u))) := fun u =>
    ((ENNReal.continuous_ofReal.tendsto _).comp (hpt u)).liminf_eq
  -- Fatou along the truncations
  have hfat : (∫⁻ u, liminf (fun N : ℕ => ENNReal.ofReal
      (truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u))))) atTop) ≤
      liminf (fun N : ℕ => ∫⁻ u, ENNReal.ofReal
        (truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u))))) atTop :=
    lintegral_liminf_le' fun N => ENNReal.measurable_ofReal.comp_aemeasurable
      (hYint N).aestronglyMeasurable.aemeasurable
  have hN : ∀ N : ℕ, (∫⁻ u, ENNReal.ofReal
      (truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u))))) ≤
      ENNReal.ofReal K := fun N => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hYint N) (Eventually.of_forall fun u =>
      mul_nonneg (truncatedTilt_pos _ _ _).le (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal (hK N)
  calc (∫⁻ u, ENNReal.ofReal (F u ^ 2 * Real.exp (-((16 - 2 * σ) * u))))
      = ∫⁻ u, liminf (fun N : ℕ => ENNReal.ofReal
          (truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u))))) atTop :=
        lintegral_congr fun u => (hliminf u).symm
    _ ≤ liminf (fun N : ℕ => ∫⁻ u, ENNReal.ofReal
          (truncatedTilt (2 * (4 - σ)) N u * (F u ^ 2 * Real.exp (-(8 * u))))) atTop := hfat
    _ ≤ ENNReal.ofReal K := liminf_le_of_frequently_le' (Frequently.of_forall hN)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- **The state decays past the barrier at the rate of the zeros.** If every centred zero has
`Re z ≤ κ`, then the critical state has the square moments `∫ F² e^{-bu} du < ∞` for every
`b < 31/2 - κ`. -/
theorem integrable_sq_mul_exp_of_zero_abscissa {κ : ℝ} (hκ : 0 ≤ κ)
    (hzero : ∀ q : XiZeroCopy, (centredZero q).re ≤ κ) {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ} (hb : b < 31 / 2 - κ) :
    Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) := by
  rcases lt_or_ge b 15 with hb15 | hb15
  · exact (criticalHalfLineGroundState_exponential_bounds hW hthreshold hF).2 b hb15
  · have h := integrable_sq_mul_exp_of_right_line hκ hzero (σ := (16 - b) / 2) (by linarith)
      (by linarith) (by linarith) hW hthreshold hF
    refine h.congr (Eventually.of_forall fun u => ?_)
    show F u ^ 2 * Real.exp (-((16 - 2 * ((16 - b) / 2)) * u)) = F u ^ 2 * Real.exp (-(b * u))
    rw [show 16 - 2 * ((16 - b) / 2) = b by ring]

/-- **The barrier `b = 15` is not the decay rate of the critical state**: unconditionally
`∫ F² e^{-bu} du < ∞` for every `b < 15 + 3001/24000`. -/
theorem integrable_sq_mul_exp_past_barrier {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {b : ℝ}
    (hb : b < 15 + 3001 / 24000) : Integrable fun u => F u ^ 2 * Real.exp (-(b * u)) :=
  integrable_sq_mul_exp_of_zero_abscissa (κ := 8999 / 24000) (by norm_num)
    re_centredZero_le_seed hW hthreshold hF (by linarith)

end GaloisForLFunctions.ExclusionOfTheCriticalState
