import GaloisForLFunctions.RHTower.Suzuki.SuzukiOnePrimeFractionalCarrierOperator
import GaloisForLFunctions.RHTower.Suzuki.SuzukiLiteralPairedSourceAssembly
import GaloisForLFunctions.HTGeometry.ScalarSquareExponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Literal one-prime terminal pruning and its exact propagator

Below the second-prime threshold, Suzuki's canonical physical cutoff uniformly removes every
one-prime valuation site except `0` and `1`.  On the only two-site puncture channels, compression
of the literal `κ = 2/3` weighted shifts is the reciprocal off-diagonal matrix

`B = [[0, 2^(2/3)], [2^(-2/3), 0]]`.

Thus `B² = I`, so its continuous group is an exact cosine-sine pair and is uniformly bounded in
frequency.  This closes the actual one-prime propagator infrastructure without inferring a
continuous polynomial group from the previously proved discrete shift bounds.
-/

open scoped Matrix Matrix.Norms.Operator

namespace RHTower

noncomputable section

/-- The second one-prime displacement lies strictly beyond the second-prime aperture threshold. -/
theorem log_three_lt_two_mul_log_two_suzukiOnePrimeTerminalPrunedPropagator : Real.log 3 < 2 * Real.log 2 := by
  rw [← Real.log_four_eq]
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

/-- Every nonnegative one-prime valuation whose center reaches the closed aperture is `0` or `1`. -/
theorem onePrime_terminal_index (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 3) (hn0 : 0 ≤ n)
    (hn : (n : ℝ) * Real.log 2 ≤ 2 * a) : n = 0 ∨ n = 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnlt : n < 2 := by
    by_contra h
    have h2n : (2 : ℤ) ≤ n := by omega
    have h2nR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2n
    have hmul : (2 : ℝ) * Real.log 2 ≤ (n : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_right h2nR hlog2.le
    linarith [log_three_lt_two_mul_log_two_suzukiOnePrimeTerminalPrunedPropagator]
  omega

/-- A strict-interior one-prime valuation below `log 3` is exactly site `1`. -/
theorem onePrime_strictInterior_index_eq_one (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 3) (hn0 : 0 < (n : ℝ) * Real.log 2)
    (hnA : (n : ℝ) * Real.log 2 < 2 * a) : n = 1 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : 0 < (n : ℝ) := by
    by_contra h
    have : (n : ℝ) ≤ 0 := le_of_not_gt h
    have := mul_nonpos_of_nonpos_of_nonneg this hlog2.le
    linarith
  have hnZ : 0 ≤ n := by exact_mod_cast hnR.le
  rcases onePrime_terminal_index a n hA hnZ hnA.le with rfl | h
  · norm_num at hn0
  · exact h

/-- Physical displacement of the rank-one valuation `n`. -/
def onePrimeDisplacement (n : ℤ) : ℝ := (n : ℝ) * Real.log 2

/-- Center descending from the right endpoint. -/
def onePrimeRightCenter (a : ℝ) (n : ℤ) : ℝ := a - onePrimeDisplacement n

/-- Center descending from the left endpoint. -/
def onePrimeLeftCenter (a : ℝ) (n : ℤ) : ℝ := -a + onePrimeDisplacement n

/-- Closed-aperture membership for a right-rooted center. -/
theorem onePrimeRightCenter_mem_Icc_iff (a : ℝ) (n : ℤ) :
    onePrimeRightCenter a n ∈ Set.Icc (-a) a ↔
      0 ≤ onePrimeDisplacement n ∧ onePrimeDisplacement n ≤ 2 * a := by
  simp only [Set.mem_Icc]
  unfold onePrimeRightCenter
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Closed-aperture membership for a left-rooted center. -/
theorem onePrimeLeftCenter_mem_Icc_iff (a : ℝ) (n : ℤ) :
    onePrimeLeftCenter a n ∈ Set.Icc (-a) a ↔
      0 ≤ onePrimeDisplacement n ∧ onePrimeDisplacement n ≤ 2 * a := by
  simp only [Set.mem_Icc]
  unfold onePrimeLeftCenter
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- The one-prime displacement is nonnegative exactly at nonnegative valuations. -/
theorem onePrimeDisplacement_nonneg_iff (n : ℤ) :
    0 ≤ onePrimeDisplacement n ↔ 0 ≤ n := by
  unfold onePrimeDisplacement
  rw [mul_nonneg_iff_of_pos_right (Real.log_pos (by norm_num))]
  norm_cast

/-- Right-rooted closed-aperture centers are confined to sites `0,1`. -/
theorem onePrimeRightCenter_terminal_index (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 3)
    (hx : onePrimeRightCenter a n ∈ Set.Icc (-a) a) : n = 0 ∨ n = 1 := by
  rw [onePrimeRightCenter_mem_Icc_iff] at hx
  exact onePrime_terminal_index a n hA
    (onePrimeDisplacement_nonneg_iff n |>.mp hx.1) hx.2

/-- Left-rooted closed-aperture centers are confined to sites `0,1`. -/
theorem onePrimeLeftCenter_terminal_index (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 3)
    (hx : onePrimeLeftCenter a n ∈ Set.Icc (-a) a) : n = 0 ∨ n = 1 := by
  rw [onePrimeLeftCenter_mem_Icc_iff] at hx
  exact onePrime_terminal_index a n hA
    (onePrimeDisplacement_nonneg_iff n |>.mp hx.1) hx.2

/-- Uniform spatial gap between every nonterminal one-prime center and the closed aperture. -/
def onePrimeTerminalGap : ℝ :=
  min (Real.log 2) (2 * Real.log 2 - Real.log 3)

/-- The terminal pruning gap is strictly positive. -/
theorem onePrimeTerminalGap_pos : 0 < onePrimeTerminalGap := by
  rw [onePrimeTerminalGap, lt_min_iff]
  exact ⟨Real.log_pos (by norm_num), sub_pos.mpr log_three_lt_two_mul_log_two_suzukiOnePrimeTerminalPrunedPropagator⟩

/-- Every right-rooted center outside sites `0,1` stays at least the terminal gap from aperture. -/
theorem onePrimeRightCenter_outside_terminalGap (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 3) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    onePrimeRightCenter a n ≤ -a - onePrimeTerminalGap ∨
      a + onePrimeTerminalGap ≤ onePrimeRightCenter a n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgapL : onePrimeTerminalGap ≤ Real.log 2 := min_le_left _ _
  have hgapR : onePrimeTerminalGap ≤ 2 * Real.log 2 - Real.log 3 := min_le_right _ _
  rcases lt_or_ge n 0 with hnneg | hnnonneg
  · right
    have hnle : n ≤ -1 := by omega
    have hnleR : (n : ℝ) ≤ -1 := by exact_mod_cast hnle
    have hd : onePrimeDisplacement n ≤ -Real.log 2 := by
      rw [onePrimeDisplacement]
      nlinarith
    rw [onePrimeRightCenter]
    linarith
  · have hn2 : 2 ≤ n := by omega
    left
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hd : 2 * Real.log 2 ≤ onePrimeDisplacement n := by
      rw [onePrimeDisplacement]
      exact mul_le_mul_of_nonneg_right hn2R hlog2.le
    rw [onePrimeRightCenter]
    linarith

/-- Every left-rooted center outside sites `0,1` stays at least the terminal gap from aperture. -/
theorem onePrimeLeftCenter_outside_terminalGap (a : ℝ) (n : ℤ)
    (hA : 2 * a < Real.log 3) (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    onePrimeLeftCenter a n ≤ -a - onePrimeTerminalGap ∨
      a + onePrimeTerminalGap ≤ onePrimeLeftCenter a n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgapL : onePrimeTerminalGap ≤ Real.log 2 := min_le_left _ _
  have hgapR : onePrimeTerminalGap ≤ 2 * Real.log 2 - Real.log 3 := min_le_right _ _
  rcases lt_or_ge n 0 with hnneg | hnnonneg
  · left
    have hnle : n ≤ -1 := by omega
    have hnleR : (n : ℝ) ≤ -1 := by exact_mod_cast hnle
    have hd : onePrimeDisplacement n ≤ -Real.log 2 := by
      rw [onePrimeDisplacement]
      nlinarith
    rw [onePrimeLeftCenter]
    linarith
  · have hn2 : 2 ≤ n := by omega
    right
    have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hd : 2 * Real.log 2 ≤ onePrimeDisplacement n := by
      rw [onePrimeDisplacement]
      exact mul_le_mul_of_nonneg_right hn2R hlog2.le
    rw [onePrimeLeftCenter]
    linarith

/-- A center separated by the terminal gap has zero canonical cutoff on the terminal ray. -/
theorem onePrimeScaleBufferedCutoff_eq_zero_of_outside_terminalGap
    (a x o L : ℝ)
    (hx : x ≤ -a - onePrimeTerminalGap ∨ a + onePrimeTerminalGap ≤ x)
    (ho : |o| ≤ 1) (hL : Real.exp (-L) < onePrimeTerminalGap) :
    GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff a x o L = 0 := by
  by_contra hne
  have hin :=
    (GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff_ne_zero_iff a x o L).mp hne
  have he : 0 < Real.exp (-L) := Real.exp_pos _
  have hoo := abs_le.mp ho
  rcases hx with hx | hx
  · have hoe : o * Real.exp (-L) ≤ Real.exp (-L) := by
      nlinarith
    linarith
  · have hoe : -Real.exp (-L) ≤ o * Real.exp (-L) := by
      nlinarith
    linarith

/-- Right-rooted canonical cutoffs vanish uniformly away from sites `0,1`. -/
theorem onePrimeRightScaleBufferedCutoff_eq_zero_off_terminal
    (a o L : ℝ) (n : ℤ) (hA : 2 * a < Real.log 3)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (ho : |o| ≤ 1)
    (hL : Real.exp (-L) < onePrimeTerminalGap) :
    GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff
        a (onePrimeRightCenter a n) o L = 0 :=
  onePrimeScaleBufferedCutoff_eq_zero_of_outside_terminalGap a _ o L
    (onePrimeRightCenter_outside_terminalGap a n hA hn0 hn1) ho hL

/-- Left-rooted canonical cutoffs vanish uniformly away from sites `0,1`. -/
theorem onePrimeLeftScaleBufferedCutoff_eq_zero_off_terminal
    (a o L : ℝ) (n : ℤ) (hA : 2 * a < Real.log 3)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (ho : |o| ≤ 1)
    (hL : Real.exp (-L) < onePrimeTerminalGap) :
    GaloisForLFunctions.RHTower.suzukiScaleBufferedCutoff
        a (onePrimeLeftCenter a n) o L = 0 :=
  onePrimeScaleBufferedCutoff_eq_zero_of_outside_terminalGap a _ o L
    (onePrimeLeftCenter_outside_terminalGap a n hA hn0 hn1) ho hL

/-- Reciprocal weight ratio between terminal sites `0` and `1`. -/
def onePrimeTerminalRatio : ℝ := (2 : ℝ) ^ (2 / 3 : ℝ)

/-- Terminal weight ratio is strictly positive. -/
theorem onePrimeTerminalRatio_pos : 0 < onePrimeTerminalRatio := by
  unfold onePrimeTerminalRatio
  positivity

/-- Rank-one valuation embedded in the existing `Fin 1 → ℤ` carrier. -/
def onePrimeValuation (n : ℤ) : Fin 1 → ℤ := fun _ => n

/-- Positive generator of the rank-one valuation lattice. -/
def onePrimeForwardStep : Fin 1 → ℤ := onePrimeValuation 1

/-- Literal forward weighted shift ratio from site zero to site one. -/
theorem onePrimeForwardRatio_zero :
    fractionalPolynomialOrbitShiftRatio (2 / 3) onePrimeForwardStep
        (onePrimeValuation 0) = onePrimeTerminalRatio := by
  simp [fractionalPolynomialOrbitShiftRatio, fractionalPolynomialOrbitWeight,
    onePrimeForwardStep, onePrimeValuation, orbitLength, onePrimeTerminalRatio]
  norm_num

/-- Literal backward weighted shift ratio from site one to site zero. -/
theorem onePrimeBackwardRatio_one :
    fractionalPolynomialOrbitShiftRatio (2 / 3) (-onePrimeForwardStep)
        (onePrimeValuation 1) = onePrimeTerminalRatio⁻¹ := by
  simp [fractionalPolynomialOrbitShiftRatio, fractionalPolynomialOrbitWeight,
    onePrimeForwardStep, onePrimeValuation, orbitLength, onePrimeTerminalRatio]
  norm_num

/-- Exact two-site compression of the terminal weighted prime adjacency. -/
def onePrimeTerminalAdjacency : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(0 : ℂ), (onePrimeTerminalRatio : ℂ);
     ((onePrimeTerminalRatio : ℂ)⁻¹), 0]

/-- The nonnormal terminal adjacency is an exact involution. -/
theorem onePrimeTerminalAdjacency_mul_self :
    onePrimeTerminalAdjacency * onePrimeTerminalAdjacency = 1 := by
  have hr : (onePrimeTerminalRatio : ℂ) ≠ 0 := by
    exact_mod_cast onePrimeTerminalRatio_pos.ne'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [onePrimeTerminalAdjacency, Matrix.mul_apply, Fin.sum_univ_two, hr]

/-- Exact cosine-sine exponential of the terminal weighted prime adjacency. -/
theorem exp_onePrimeTerminalAdjacency (t : ℝ) :
    NormedSpace.exp (((-(t : ℂ) * Complex.I)) • onePrimeTerminalAdjacency) =
      ((Real.cos t : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((Real.sinc t : ℝ) : ℂ) •
          (((-(t : ℂ) * Complex.I)) • onePrimeTerminalAdjacency) := by
  apply HTGeometry.exp_of_mul_self_eq_neg_sq_smul_one _ t
  rw [smul_mul_smul_comm, onePrimeTerminalAdjacency_mul_self]
  congr 1
  calc
    -(t : ℂ) * Complex.I * (-(t : ℂ) * Complex.I) =
        (t : ℂ) ^ 2 * (Complex.I * Complex.I) := by ring
    _ = -(t : ℂ) ^ 2 := by rw [Complex.I_mul_I]; ring

/-- Scalar identity used to convert the cardinal-sine coefficient to the sine coefficient. -/
theorem abs_sinc_mul_abs (t : ℝ) :
    |Real.sinc t| * |t| = |Real.sin t| := by
  by_cases ht : t = 0
  · subst t
    simp
  · rw [Real.sinc_of_ne_zero ht, abs_div]
    exact div_mul_cancel₀ _ (abs_ne_zero.mpr ht)

/-- The literal terminal prime group is uniformly bounded in frequency. -/
theorem norm_exp_onePrimeTerminalAdjacency_le (t : ℝ) :
    ‖NormedSpace.exp (((-(t : ℂ) * Complex.I)) • onePrimeTerminalAdjacency)‖ ≤
      1 + ‖onePrimeTerminalAdjacency‖ := by
  rw [exp_onePrimeTerminalAdjacency]
  calc
    ‖((Real.cos t : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        ((Real.sinc t : ℝ) : ℂ) •
          (((-(t : ℂ) * Complex.I)) • onePrimeTerminalAdjacency)‖
        ≤ ‖((Real.cos t : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)‖ +
          ‖((Real.sinc t : ℝ) : ℂ) •
            (((-(t : ℂ) * Complex.I)) • onePrimeTerminalAdjacency)‖ := norm_add_le _ _
    _ = |Real.cos t| + (|Real.sinc t| * |t|) * ‖onePrimeTerminalAdjacency‖ := by
      have hcos : ‖((Real.cos t : ℝ) : ℂ)‖ = |Real.cos t| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have hsinc : ‖((Real.sinc t : ℝ) : ℂ)‖ = |Real.sinc t| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      have ht : ‖(-(t : ℂ) * Complex.I)‖ = |t| := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      rw [norm_smul, norm_one, hcos, mul_one, norm_smul, norm_smul, hsinc, ht]
      ring
    _ = |Real.cos t| + |Real.sin t| * ‖onePrimeTerminalAdjacency‖ := by
      rw [abs_sinc_mul_abs]
    _ ≤ 1 + 1 * ‖onePrimeTerminalAdjacency‖ := by
      exact add_le_add (Real.abs_cos_le_one t)
        (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one t) (norm_nonneg _))
    _ = 1 + ‖onePrimeTerminalAdjacency‖ := by ring

/-- Arbitrary real literal prime coupling does not change the uniform group bound. -/
theorem norm_exp_real_smul_onePrimeTerminalAdjacency_le (c t : ℝ) :
    ‖NormedSpace.exp (((-(t : ℂ) * Complex.I)) •
        (((c : ℝ) : ℂ) • onePrimeTerminalAdjacency))‖ ≤
      1 + ‖onePrimeTerminalAdjacency‖ := by
  have harg : ((-(t : ℂ) * Complex.I)) •
        (((c : ℝ) : ℂ) • onePrimeTerminalAdjacency) =
      ((-((t * c : ℝ) : ℂ) * Complex.I)) • onePrimeTerminalAdjacency := by
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [harg]
  exact norm_exp_onePrimeTerminalAdjacency_le (t * c)

/-- Restriction of an infinite fractional-carrier state to terminal sites `0,1`. -/
def onePrimeTerminalRestrict (f : SuzukiOnePrimeFractionalCarrier) : Fin 2 → ℂ :=
  fun i => f (onePrimeValuation (i : ℕ))

/-- The two-site matrix is exactly the coordinate compression of the literal fractional shifts. -/
theorem onePrimeTerminalAdjacency_is_literal_compression
    (f : SuzukiOnePrimeFractionalCarrier)
    (hsupp : ∀ n : ℤ, n ≠ 0 → n ≠ 1 → f (onePrimeValuation n) = 0) :
    (fun i : Fin 2 =>
        suzukiOnePrimeFractionalOrbitShiftCLM onePrimeForwardStep f
            (onePrimeValuation (i : ℕ)) +
          suzukiOnePrimeFractionalOrbitShiftCLM (-onePrimeForwardStep) f
            (onePrimeValuation (i : ℕ))) =
      onePrimeTerminalAdjacency *ᵥ onePrimeTerminalRestrict f := by
  funext i
  fin_cases i
  · change
      suzukiOnePrimeFractionalOrbitShiftCLM onePrimeForwardStep f
            (onePrimeValuation 0) +
          suzukiOnePrimeFractionalOrbitShiftCLM (-onePrimeForwardStep) f
            (onePrimeValuation 0) =
        (onePrimeTerminalAdjacency *ᵥ onePrimeTerminalRestrict f) 0
    simp only [suzukiOnePrimeFractionalOrbitShiftCLM_apply]
    rw [onePrimeForwardRatio_zero]
    have hm : onePrimeValuation 0 + -onePrimeForwardStep = onePrimeValuation (-1) := by
      funext j
      simp [onePrimeValuation, onePrimeForwardStep]
    have hp : onePrimeValuation 0 + onePrimeForwardStep = onePrimeValuation 1 := by
      funext j
      simp [onePrimeValuation, onePrimeForwardStep]
    rw [hm, hp, hsupp (-1) (by norm_num) (by norm_num)]
    simp [onePrimeTerminalAdjacency, onePrimeTerminalRestrict, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  · change
      suzukiOnePrimeFractionalOrbitShiftCLM onePrimeForwardStep f
            (onePrimeValuation 1) +
          suzukiOnePrimeFractionalOrbitShiftCLM (-onePrimeForwardStep) f
            (onePrimeValuation 1) =
        (onePrimeTerminalAdjacency *ᵥ onePrimeTerminalRestrict f) 1
    simp only [suzukiOnePrimeFractionalOrbitShiftCLM_apply]
    rw [onePrimeBackwardRatio_one]
    have hp : onePrimeValuation 1 + onePrimeForwardStep = onePrimeValuation 2 := by
      funext j
      simp [onePrimeValuation, onePrimeForwardStep]
    have hm : onePrimeValuation 1 + -onePrimeForwardStep = onePrimeValuation 0 := by
      funext j
      simp [onePrimeValuation, onePrimeForwardStep]
    rw [hp, hm, hsupp 2 (by norm_num) (by norm_num)]
    simp [onePrimeTerminalAdjacency, onePrimeTerminalRestrict, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

end

end RHTower
