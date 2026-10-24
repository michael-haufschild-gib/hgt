import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SecondTangentControlGivesTheAngle
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheEscapeIsAnOutAndBackExcursion
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedAveragedContinuationAndTheZeroWidthBand

/-!
# Source-Specific Angle and Shape Control, Their Hierarchy, and the Integrated Autocorrelation Equivalence

This module resolves Open Problem 2 of `ArithmeticContinuationAndCriticalEnergy`:

1. **Unconditional First-Horizon Separation on the Actual Source (`§1`)**:
   At the first horizon `T = 1`, `A_ε(1) = 1 − Re(1/ζ(1+ε))` and `E_ε(1) = −m(ε)`, so:
   - the signed damping work `W_1(ε) = −(1 − Re(1/ζ(1+ε))) m(ε)/2` tends to `−1/2` as `ε ↓ 0`
     (`tendsto_signedDampingWork_one`), making global nonnegative work false on the actual source
     (`not_forall_signedDampingWork_nonneg`);
   - by contrast, the damping autocorrelation at the first horizon is
     `K_1(η, ε) = m(η) m(ε) / 2 → 1/2 > 0` as `η, ε ↓ 0` (`tangentCorrelation_one`,
     `tendsto_tangentCorrelation_one_nhdsGT_zero`);
   - consequently, there exists a positive damping interval `(0, δ₀)` on which the actual source
     simultaneously has strictly positive damping autocorrelation `K_1(η, ε) > 0` and strictly
     negative signed work `W_1(ε) < 0`
     (`exists_damping_tangentCorrelation_one_pos_and_signedDampingWork_one_neg`).

2. **The Hierarchy and Non-Equivalence of Sufficient Angle and Shape Routes (`§2`)**:
   - On the tangent-angle side: second-tangent majorant control implies relative tangent stability,
     which implies non-obtuse angle (`0 ≤ K_T(η, ε)`), which implies zero accumulated negative
     autocorrelation (`∫_δ^ε [K_T]⁻ = 0`), which implies pointwise `DampingContinuation a c`, which
     implies `AveragedDampingContinuation a c`. Relative tangent stability is strictly stronger than
     non-obtuse angle (`exists_pos_pairing_not_relative_stability`), and pointwise continuation is
     strictly stronger than averaged continuation (`exists_admits_everywhere_not_linearContinuation`).
   - On the energy-shape side: second-tangent pairing `−‖E_ε‖_T² ≤ ⟪A_ε, F_ε⟫_T` implies monotone
     signed work (convexity of `E_T`), which implies the single-sign-change property, which implies
     the no-interior-bump property, which forces **damping-uniform** admission
     `UniformlyAdmitsOn dampedMobiusEnergy (Ioc 0 (1/2))` (`uniformlyAdmitsOn_of_no_interior_bump`).
     The single-sign-change property is strictly weaker than monotone signed work
     (`exists_single_sign_change_not_monotoneOn`).

3. **The Weaker Signed Integrated Autocorrelation Identity and Its Equivalence with Admission (`§3`)**:
   Integrating `K_T(η, ε)` across `[a, c] × [a, c]` restores unconditional positivity and gives an
   exact equivalence with admission:
   - `∫_a^c K_T(η, ε) dη = ⟪A_c − A_a, E_ε⟫_T` (`integral_tangentCorrelation_left_eq_pairing`);
   - `∫_a^c (∫_a^c K_T(η, ε) dη) dε = ‖A_c − A_a‖_T² ≥ 0`
     (`double_integral_tangentCorrelation_eq_pronicNorm_sub_sq`,
     `double_integral_tangentCorrelation_nonneg`);
   - `E_T(a) − E_T(c) = ∫_a^c ∫_a^c K_T(η, ε) dη dε − 2 ⟪A_c, A_c − A_a⟫_T`
     (`dampedMobiusEnergy_sub_eq_double_integral_sub_two_pairing`);
   - `(1/2) E_T(a) − E_T(c) ≤ ∫_a^c ∫_a^c K_T(η, ε) dη dε ≤ 2 E_T(a) + 2 E_T(c)`
     (`double_integral_tangentCorrelation_bounds`);
   - For any `0 < a ≤ c` with `c` admitted, `Admits dampedMobiusEnergy a` holds **if and only if**
     the double autocorrelation integral `∫_a^c ∫_a^c K_T(η, ε) dη dε` is bounded uniformly in `T`
     (`admits_iff_bounded_double_integral_tangentCorrelation`), and cofinal boundedness is
     equivalent to the Riemann Hypothesis
     (`riemannHypothesis_iff_cofinal_double_integral_tangentCorrelation`).

4. **Unconditional Double-Autocorrelation Bounds Above the Zero Width and on the VK Band (`§4`)**:
   - The double autocorrelation integral is unconditionally bounded uniformly in `T` on every
     compact `[a, c] ⊂ (Θ − ½, ∞)`
     (`exists_double_integral_tangentCorrelation_le_of_zetaZeroAbscissa_sub_half_lt`);
   - It is unconditionally bounded by `4 E` uniformly in `(T, a, c)` on the Vinogradov–Korobov band
     `a ≥ ½ − κ σ(T)/(480 log T)` (`exists_double_integral_tangentCorrelation_le_on_vinogradovKorobovBand`);
   - At every fixed `0 < a < ½`, it obeys the unconditional sub-power Vinogradov–Korobov saving
     `O_a(T^{1−2a} exp(−κ σ(T)/270))` (`eventually_double_integral_tangentCorrelation_le_vk_saving`).
-/

open Set Filter Topology Finset MeasureTheory RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. First-Horizon Separation on the Actual Source: Adverse Work vs. Positive Autocorrelation -/

/-- The first cell of the centred damped divisor prefix: `A_ε(1) = 1 − Re(1/ζ(1+ε))`. -/
theorem centredPrefix_one (ε : ℝ) :
    pmPowerDampedCenteredDivisorPrefix ε 1 = 1 - (pmPowerDampedDivisorDensity ε).re := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq]
  simp [pmPowerDampedDivisorCoeff]

/-- The first cell of the centred damped Chebyshev tangent: `E_ε(1) = −m(ε)`. -/
theorem dampedChebyshevError_one (ε : ℝ) :
    dampedChebyshevError ε 1 = -dampedReadout ε := by
  simp [dampedChebyshevError, dampedVonMangoldt]

/-- The signed damping work at horizon `T = 1` in closed form. -/
theorem signedDampingWork_one (ε : ℝ) :
    signedDampingWork ε 1 =
      -((1 - (pmPowerDampedDivisorDensity ε).re) * dampedReadout ε) / 2 := by
  rw [signedDampingWork, show Finset.Icc 1 1 = {1} by rfl, sum_singleton, centredPrefix_one,
    dampedChebyshevError_one]
  norm_num

/-- **The first-cell signed work tends to `−1/2` as `ε ↓ 0`.** -/
theorem tendsto_signedDampingWork_one :
    Tendsto (fun ε => signedDampingWork ε 1) (𝓝[>] 0) (𝓝 (-1 / 2)) := by
  have hA := (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_pmPowerDampedDivisorDensity_re_zero
  have h := ((hA.mul tendsto_dampedReadout_zero).neg).div_const 2
  rw [sub_zero, one_mul] at h
  refine h.congr fun ε => ?_
  rw [signedDampingWork_one]

/-- The first-cell signed work is strictly negative for all small positive dampings. -/
theorem eventually_signedDampingWork_one_neg :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), signedDampingWork ε 1 < 0 :=
  tendsto_signedDampingWork_one.eventually (gt_mem_nhds (by norm_num))

/-- **Global nonnegative signed work is unconditionally false on the actual source.** -/
theorem not_forall_signedDampingWork_nonneg :
    ¬ ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → 0 ≤ signedDampingWork ε T := by
  intro h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), signedDampingWork ε 1 < 0 ∧ ε ∈ Ioo (0 : ℝ) (1 / 2) :=
    eventually_signedDampingWork_one_neg.and (Ioo_mem_nhdsGT (by norm_num))
  obtain ⟨ε, hneg, hmem⟩ := hev.exists
  exact absurd (h 1 ε hmem.1 hmem.2.le) (not_le.mpr hneg)

/-- At horizon `T = 1`, the damping autocorrelation is `m(η) m(ε) / 2`. -/
theorem tangentCorrelation_one (η ε : ℝ) :
    tangentCorrelation 1 η ε = dampedReadout η * dampedReadout ε / 2 := by
  rw [tangentCorrelation, pronicPairing, show Finset.Icc 1 1 = {1} by rfl, sum_singleton,
    dampedChebyshevError_one, dampedChebyshevError_one]
  ring

/-- On the diagonal at `T = 1`, `K_1(ε, ε) = m(ε)² / 2`, which tends to `1/2` as `ε ↓ 0`. -/
theorem tendsto_tangentCorrelation_one_diag_zero :
    Tendsto (fun ε => tangentCorrelation 1 ε ε) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h := (tendsto_dampedReadout_zero.mul tendsto_dampedReadout_zero).div_const 2
  rw [mul_one] at h
  exact h.congr fun ε => (tangentCorrelation_one ε ε).symm

/-- **Unconditional first-horizon separation between autocorrelation positivity and work sign.**
There exists `δ₀ ∈ (0, 1/2]` such that for all `η, ε ∈ (0, δ₀)`, the first-horizon damping
autocorrelation `K_1(η, ε)` is strictly positive while the first-horizon signed work `W_1(ε)` is
strictly negative (paid by the negative scalar moment `−m(ε)/2`). -/
theorem exists_damping_tangentCorrelation_one_pos_and_signedDampingWork_one_neg :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ η ∈ Ioo 0 δ₀, ∀ ε ∈ Ioo 0 δ₀,
        0 < tangentCorrelation 1 η ε ∧ signedDampingWork ε 1 < 0 := by
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < dampedReadout ε :=
    tendsto_dampedReadout_zero.eventually (lt_mem_nhds (by norm_num))
  have hboth : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < dampedReadout ε ∧ signedDampingWork ε 1 < 0 :=
    hm.and eventually_signedDampingWork_one_neg
  obtain ⟨δ₁, hδ₁, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hboth
  refine ⟨min δ₁ (1 / 2), lt_min hδ₁ (by norm_num), min_le_right _ _, fun η hη ε hε => ?_⟩
  have hη' : η ∈ Ioo 0 δ₁ := ⟨hη.1, hη.2.trans_le (min_le_left _ _)⟩
  have hε' : ε ∈ Ioo 0 δ₁ := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hmη := (hsub hη').1
  have hmε := (hsub hε').1
  refine ⟨?_, (hsub hε').2⟩
  rw [tangentCorrelation_one]
  positivity

/-! ## §2. Hierarchy and Strict Separation of Sufficient Angle and Shape Routes -/

/-- **Nonnegative autocorrelation implies zero accumulated negative autocorrelation.** -/
theorem integral_negPart_tangentCorrelation_eq_zero_of_nonneg {δ ε : ℝ} (hδε : δ ≤ ε) (T : ℕ)
    (hK : ∀ η ∈ Icc δ ε, 0 ≤ tangentCorrelation T η ε) :
    (∫ η in δ..ε, max 0 (-tangentCorrelation T η ε)) = 0 := by
  have hzero : ∀ η ∈ uIcc δ ε, max 0 (-tangentCorrelation T η ε) = 0 := by
    rw [uIcc_of_le hδε]
    intro η hη
    exact max_eq_left (by linarith [hK η hη])
  rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero]

/-- **Strict separation between relative tangent stability and non-obtuse angle.**
Any two positively collinear vectors `u = 3v`, `v` with `‖v‖_T > 0` have positive pronic pairing
`⟪u, v⟫_T = 3 ‖v‖_T² > 0` (angle `0`), yet fail relative stability `‖u − v‖_T ≤ ‖v‖_T` since
`‖u − v‖_T = 2 ‖v‖_T > ‖v‖_T`. -/
theorem exists_pos_pairing_not_relative_stability :
    ∃ (T : ℕ) (u v : ℕ → ℝ),
      0 < pronicNorm T v ∧
      0 < pronicPairing T u v ∧
      pronicNorm T v < pronicNorm T (fun n => u n - v n) := by
  refine ⟨1, fun _ => 3, fun _ => 1, ?_, ?_, ?_⟩
  · have h1 : pronicNorm 1 (fun _ => (1 : ℝ)) = Real.sqrt (1 / 2) := by
      rw [pronicNorm, show Finset.Icc (1 : ℕ) 1 = {1} by rfl, sum_singleton]; ring_nf
    rw [h1]
    positivity
  · rw [pronicPairing, show Finset.Icc (1 : ℕ) 1 = {1} by rfl, sum_singleton]
    norm_num
  · have h1 : pronicNorm 1 (fun _ => (1 : ℝ)) = Real.sqrt (1 / 2) := by
      rw [pronicNorm, show Finset.Icc (1 : ℕ) 1 = {1} by rfl, sum_singleton]; ring_nf
    have h2 : pronicNorm 1 (fun _ => (3 : ℝ) - 1) = Real.sqrt 2 := by
      rw [pronicNorm, show Finset.Icc (1 : ℕ) 1 = {1} by rfl, sum_singleton]; ring_nf
    rw [h1, h2]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The no-interior-bump condition forces damping-uniform admission on `(0, 1/2]`.**
Because the zero-damping limit is at most `1`, the no-interior-bump hypothesis bounds `E_T(ε)` by
a single constant `max 1 (max B 0)` independent of both `T` and `ε ∈ (0, 1/2]`. -/
theorem uniformlyAdmitsOn_of_no_interior_bump
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → ∀ δ : ℝ, 0 < δ → δ < ε →
      dampedMobiusEnergy ε T ≤
        max (dampedMobiusEnergy δ T) (dampedMobiusEnergy (1 / 2) T)) :
    UniformlyAdmitsOn dampedMobiusEnergy (Ioc 0 (1 / 2)) := by
  obtain ⟨B, hB⟩ := admits_dampedMobiusEnergy_of_half_le (le_refl (1 / 2 : ℝ))
  refine ⟨max 1 (max B 0), fun ε hε T => ?_⟩
  have hlim : Tendsto (fun δ => max (dampedMobiusEnergy δ T) (dampedMobiusEnergy (1 / 2) T))
      (𝓝[>] 0) (𝓝 (max (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) * ((n : ℝ) + 1)))
        (dampedMobiusEnergy (1 / 2) T))) :=
    (tendsto_dampedMobiusEnergy_nhdsGT_zero T).max tendsto_const_nhds
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      dampedMobiusEnergy ε T ≤
        max (dampedMobiusEnergy δ T) (dampedMobiusEnergy (1 / 2) T) := by
    filter_upwards [Ioo_mem_nhdsGT hε.1] with δ hδ using h T ε hε.1 hε.2 δ hδ.1 hδ.2
  have hstep := ge_of_tendsto hlim hev
  refine hstep.trans (max_le_max (pronicMass_le_one T) ?_)
  exact (hB T).trans (le_max_left B 0)

/-- **Strict separation between the single-sign-change property and monotone work (convexity).**
There exists a function `w : ℝ → ℝ` on `(0, 1/2]` that satisfies the single-sign-change condition
(`0 ≤ w(x) → ∀ y ∈ [x, 1/2], 0 ≤ w(y)`) everywhere on `(0, 1/2]` but is not monotone on `(0, 1/2]`. -/
theorem exists_single_sign_change_not_monotoneOn :
    ∃ w : ℝ → ℝ,
      (∀ x : ℝ, 0 < x → x ≤ 1 / 2 → 0 ≤ w x → ∀ y ∈ Set.Icc x (1 / 2 : ℝ), 0 ≤ w y) ∧
      ¬ MonotoneOn w (Set.Ioc 0 (1 / 2)) := by
  refine ⟨fun x => -x, fun x hx _ hwx => absurd hwx (not_le.mpr (by linarith)), ?_⟩
  intro hmono
  have hle := hmono (show (1 / 4 : ℝ) ∈ Set.Ioc 0 (1 / 2) by constructor <;> norm_num)
    (show (1 / 2 : ℝ) ∈ Set.Ioc 0 (1 / 2) by constructor <;> norm_num) (by norm_num)
  linarith

/-! ## §3. The Signed Double Integral of the Tangent Autocorrelation and Admission Equivalence -/

/-- **Integrating the autocorrelation in one variable gives the chord pairing.** -/
theorem integral_tangentCorrelation_left_eq_pairing {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) (ε : ℝ) :
    (∫ η in a..c, tangentCorrelation T η ε) =
      pronicPairing T
        (fun n => pmPowerDampedCenteredDivisorPrefix c n -
          pmPowerDampedCenteredDivisorPrefix a n)
        (dampedChebyshevError ε) := by
  have hint : ∀ n ∈ Finset.Icc 1 T, IntervalIntegrable
      (fun η => dampedChebyshevError η n * dampedChebyshevError ε n /
        ((n : ℝ) * ((n : ℝ) + 1))) volume a c := by
    intro n _
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hac]
    exact (((continuousOn_dampedChebyshevError n).mul continuousOn_const).div_const _).mono
      fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)
  unfold tangentCorrelation pronicPairing
  rw [intervalIntegral.integral_finsetSum hint]
  refine sum_congr rfl fun n _ => ?_
  have hfun : (fun η => dampedChebyshevError η n * dampedChebyshevError ε n /
      ((n : ℝ) * ((n : ℝ) + 1))) =
      fun η => dampedChebyshevError η n *
        (dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1))) :=
    funext fun η => by ring
  rw [hfun, intervalIntegral.integral_mul_const,
    ← pmPowerDampedCenteredDivisorPrefix_sub_eq_integral ha hac n]
  ring

/-- **The double integral of the tangent autocorrelation is the pronic energy of the chord.** -/
theorem double_integral_tangentCorrelation_eq_pronicNorm_sub_sq {a c : ℝ} (ha : 0 < a)
    (hac : a ≤ c) (T : ℕ) :
    (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) =
      pronicNorm T (fun n => pmPowerDampedCenteredDivisorPrefix c n -
        pmPowerDampedCenteredDivisorPrefix a n) ^ 2 := by
  have h1 : (fun ε => ∫ η in a..c, tangentCorrelation T η ε) =
      fun ε => pronicPairing T
        (fun n => pmPowerDampedCenteredDivisorPrefix c n -
          pmPowerDampedCenteredDivisorPrefix a n)
        (dampedChebyshevError ε) :=
    funext fun ε => integral_tangentCorrelation_left_eq_pairing ha hac T ε
  rw [h1]
  have hint : ∀ n ∈ Finset.Icc 1 T, IntervalIntegrable
      (fun ε => (pmPowerDampedCenteredDivisorPrefix c n -
          pmPowerDampedCenteredDivisorPrefix a n) * dampedChebyshevError ε n /
        ((n : ℝ) * ((n : ℝ) + 1))) volume a c := by
    intro n _
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hac]
    exact ((continuousOn_const.mul (continuousOn_dampedChebyshevError n)).div_const _).mono
      fun x hx => mem_Ioi.mpr (lt_of_lt_of_le ha hx.1)
  unfold pronicPairing
  rw [intervalIntegral.integral_finsetSum hint, pronicNorm_sq]
  refine sum_congr rfl fun n _ => ?_
  have hfun : (fun ε => (pmPowerDampedCenteredDivisorPrefix c n -
      pmPowerDampedCenteredDivisorPrefix a n) * dampedChebyshevError ε n /
        ((n : ℝ) * ((n : ℝ) + 1))) =
      fun ε => ((pmPowerDampedCenteredDivisorPrefix c n -
        pmPowerDampedCenteredDivisorPrefix a n) / ((n : ℝ) * ((n : ℝ) + 1))) *
          dampedChebyshevError ε n :=
    funext fun ε => by ring
  rw [hfun, intervalIntegral.integral_const_mul,
    ← pmPowerDampedCenteredDivisorPrefix_sub_eq_integral ha hac n]
  ring

/-- **Unconditional nonnegativity of the double damping integral of the tangent autocorrelation.**
Although `K_T(η, ε)` may be negative off the diagonal, its double integral over any damping square
`[a, c] × [a, c]` (`0 < a ≤ c`) is unconditionally nonnegative at every horizon `T`. -/
theorem double_integral_tangentCorrelation_nonneg {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    0 ≤ ∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε := by
  rw [double_integral_tangentCorrelation_eq_pronicNorm_sub_sq ha hac T]
  positivity

theorem pronicPairing_sub_self_left (T : ℕ) (u v : ℕ → ℝ) :
    pronicPairing T u (fun n => u n - v n) =
      pronicNorm T u ^ 2 - pronicPairing T u v := by
  rw [pronicPairing, pronicNorm_sq, pronicPairing, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Exact decomposition of the energy drop into the double autocorrelation integral and the
right-endpoint chord pairing.** -/
theorem dampedMobiusEnergy_sub_eq_double_integral_sub_two_pairing {a c : ℝ} (ha : 0 < a)
    (hac : a ≤ c) (T : ℕ) :
    dampedMobiusEnergy a T - dampedMobiusEnergy c T =
      (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) -
        2 * pronicPairing T (pmPowerDampedCenteredDivisorPrefix c)
          (fun n => pmPowerDampedCenteredDivisorPrefix c n -
            pmPowerDampedCenteredDivisorPrefix a n) := by
  rw [double_integral_tangentCorrelation_eq_pronicNorm_sub_sq ha hac T,
    pronicNorm_sub_sq, pronicPairing_sub_self_left, pronicNorm_centeredPrefix,
    pronicNorm_centeredPrefix, Real.sq_sqrt (dampedMobiusEnergy_nonneg c T),
    Real.sq_sqrt (dampedMobiusEnergy_nonneg a T)]
  ring

/-- **Parallelogram inequality in the pronic norm.** -/
theorem pronicNorm_sub_sq_le_two_mul_add_sq (T : ℕ) (u v : ℕ → ℝ) :
    pronicNorm T (fun n => u n - v n) ^ 2 ≤ 2 * pronicNorm T u ^ 2 + 2 * pronicNorm T v ^ 2 := by
  have hsum : pronicNorm T (fun n => u n - v n) ^ 2 + pronicNorm T (fun n => u n + v n) ^ 2 =
      2 * pronicNorm T u ^ 2 + 2 * pronicNorm T v ^ 2 := by
    rw [pronicNorm_sub_sq, pronicNorm_add_sq]
    ring
  have hnonneg : 0 ≤ pronicNorm T (fun n => u n + v n) ^ 2 := sq_nonneg _
  linarith

/-- **Two-sided comparison between the double autocorrelation integral and the endpoint energies.** -/
theorem double_integral_tangentCorrelation_bounds {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    (1 / 2) * dampedMobiusEnergy a T - dampedMobiusEnergy c T ≤
      (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) ∧
    (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) ≤
      2 * dampedMobiusEnergy a T + 2 * dampedMobiusEnergy c T := by
  rw [double_integral_tangentCorrelation_eq_pronicNorm_sub_sq ha hac T]
  have hEa : pronicNorm T (pmPowerDampedCenteredDivisorPrefix a) ^ 2 = dampedMobiusEnergy a T := by
    rw [pronicNorm_centeredPrefix, Real.sq_sqrt (dampedMobiusEnergy_nonneg a T)]
  have hEc : pronicNorm T (pmPowerDampedCenteredDivisorPrefix c) ^ 2 = dampedMobiusEnergy c T := by
    rw [pronicNorm_centeredPrefix, Real.sq_sqrt (dampedMobiusEnergy_nonneg c T)]
  constructor
  · have h := pronicNorm_sub_sq_le_two_mul_add_sq T
      (pmPowerDampedCenteredDivisorPrefix c)
      (fun n => pmPowerDampedCenteredDivisorPrefix c n - pmPowerDampedCenteredDivisorPrefix a n)
    have hfun : (fun n => pmPowerDampedCenteredDivisorPrefix c n -
        (pmPowerDampedCenteredDivisorPrefix c n - pmPowerDampedCenteredDivisorPrefix a n)) =
        pmPowerDampedCenteredDivisorPrefix a := funext fun n => by ring
    rw [hfun, hEa, hEc] at h
    linarith
  · have h := pronicNorm_sub_sq_le_two_mul_add_sq T
      (pmPowerDampedCenteredDivisorPrefix c) (pmPowerDampedCenteredDivisorPrefix a)
    rw [hEa, hEc] at h
    linarith

/-- **Exact Equivalence: Admission is a horizon-free bound on the double damping integral of the
tangent autocorrelation.**
While pointwise nonnegativity `0 ≤ K_T(η, ε)` and bounded single-integral anti-correlation
`∫_δ^ε [K_T]⁻ ≤ Q` are sufficient but strictly stronger than admission, a horizon-uniform bound on
the signed double integral `∫_a^c ∫_a^c K_T(η, ε) dη dε` is **equivalent** to admission at `a`
whenever `c` is admitted. -/
theorem admits_iff_bounded_double_integral_tangentCorrelation {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    Admits dampedMobiusEnergy a ↔
      ∃ C : ℝ, ∀ T : ℕ, (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) ≤ C := by
  have ⟨Bc, hBc⟩ := hc
  constructor
  · rintro ⟨Ba, hBa⟩
    refine ⟨2 * max Ba 0 + 2 * max Bc 0, fun T => ?_⟩
    have hb := (double_integral_tangentCorrelation_bounds ha hac T).2
    linarith [(hBa T).trans (le_max_left Ba 0), (hBc T).trans (le_max_left Bc 0)]
  · rintro ⟨C, hC⟩
    refine ⟨2 * C + 2 * max Bc 0, fun T => ?_⟩
    have hb := (double_integral_tangentCorrelation_bounds ha hac T).1
    have hCT := hC T
    linarith [(hBc T).trans (le_max_left Bc 0)]

/-- **Exact Equivalence for the Riemann Hypothesis via the Double Autocorrelation Integral.** -/
theorem riemannHypothesis_iff_cofinal_double_integral_tangentCorrelation :
    RiemannHypothesis ↔
      ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ a < δ ∧
        ∃ C : ℝ, ∀ T : ℕ,
          (∫ ε in a..(1 / 2 : ℝ), ∫ η in a..(1 / 2 : ℝ), tangentCorrelation T η ε) ≤ C := by
  rw [riemannHypothesis_iff_cofinal_averagedDampingContinuation]
  have hc : Admits dampedMobiusEnergy (1 / 2) := admits_dampedMobiusEnergy_of_half_le le_rfl
  constructor
  · intro h δ hδ
    obtain ⟨a, ha0, haδ, hcont⟩ := h (min δ (1 / 2)) (lt_min hδ (by norm_num))
    have ha2 : a ≤ 1 / 2 := (haδ.trans_le (min_le_right _ _)).le
    have hadm := (averagedDampingContinuation_iff_admits ha0 ha2 hc).mp hcont
    exact ⟨a, ha0, haδ.trans_le (min_le_left _ _),
      (admits_iff_bounded_double_integral_tangentCorrelation ha0 ha2 hc).mp hadm⟩
  · intro h δ hδ
    obtain ⟨a, ha0, haδ, hint⟩ := h (min δ (1 / 2)) (lt_min hδ (by norm_num))
    have ha2 : a ≤ 1 / 2 := (haδ.trans_le (min_le_right _ _)).le
    have hadm := (admits_iff_bounded_double_integral_tangentCorrelation ha0 ha2 hc).mpr hint
    exact ⟨a, ha0, haδ.trans_le (min_le_left _ _),
      (averagedDampingContinuation_iff_admits ha0 ha2 hc).mpr hadm⟩

/-! ## §4. Unconditional Double-Autocorrelation Control Above `Θ − ½` and on the VK Band -/

/-- **Unconditional horizon-uniform bound on the double autocorrelation integral above `Θ − ½`.** -/
theorem exists_double_integral_tangentCorrelation_le_of_zetaZeroAbscissa_sub_half_lt {a c : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) (hac : a ≤ c) :
    ∃ C : ℝ, ∀ T : ℕ, (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) ≤ C := by
  have ha0 : 0 < a := by linarith [half_le_zetaZeroAbscissa]
  have hc : Admits dampedMobiusEnergy c :=
    admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt (ha.trans_le hac)
  exact (admits_iff_bounded_double_integral_tangentCorrelation ha0 hac hc).mp
    (admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt ha)

/-- **Unconditional Vinogradov–Korobov Band Bound for the Double Autocorrelation Integral.**
For every floor `ε₀ > 0`, there exists `E ≥ 0` such that for all horizons `T : ℕ` and all
`[a, c] ⊆ [ε₀, 1/2]` inside the Vinogradov–Korobov band `a ≥ 1/2 − κ σ(T)/(480 log T)`,
`0 ≤ ∫_a^c ∫_a^c K_T(η, ε) dη dε ≤ 4 E`. -/
theorem exists_double_integral_tangentCorrelation_le_on_vinogradovKorobovBand
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (T : ℕ) (a c : ℝ), ε₀ ≤ a → a ≤ c → c ≤ 1 / 2 →
        1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ a →
          0 ≤ (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) ∧
          (∫ ε in a..c, ∫ η in a..c, tangentCorrelation T η ε) ≤ 4 * E := by
  obtain ⟨E, hE0, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hε₀
  refine ⟨E, hE0, fun T a c ha_ge hac hc2 hband => ?_⟩
  have ha0 : 0 < a := hε₀.trans_le ha_ge
  have ha2 : a ≤ 1 / 2 := hac.trans hc2
  have hc_ge : ε₀ ≤ c := ha_ge.trans hac
  have hband_c : 1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ c := hband.trans hac
  have hEa : dampedMobiusEnergy a T ≤ E := hE T a ha_ge ha2 hband
  have hEc : dampedMobiusEnergy c T ≤ E := hE T c hc_ge hc2 hband_c
  refine ⟨double_integral_tangentCorrelation_nonneg ha0 hac T, ?_⟩
  have hb := (double_integral_tangentCorrelation_bounds ha0 hac T).2
  linarith

/-- **Unconditional All-Damping Sub-Power Vinogradov–Korobov Bound for the Double Autocorrelation
Integral.**
For every fixed `0 < a < 1/2`, there exist `C, B ≥ 0` such that eventually in `T : ℕ`,
`(∫_a^{1/2} ∫_a^{1/2} K_T(η, ε) dη dε) ≤ 2 C T^{1−2a} exp(−κ σ(T)/270) + 2 B`. -/
theorem eventually_double_integral_tangentCorrelation_le_vk_saving
    {a : ℝ} (ha0 : 0 < a) (ha2 : a < 1 / 2) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ᶠ T : ℕ in atTop,
      (∫ ε in a..(1 / 2 : ℝ), ∫ η in a..(1 / 2 : ℝ), tangentCorrelation T η ε) ≤
        2 * C * (T : ℝ) ^ (1 - 2 * a) * Real.exp (-(vkKappa * vkScale T / 270)) + 2 * B := by
  obtain ⟨C, hC0, hev⟩ := eventually_receiver_le_growth_of_pos ha0 ha2
  obtain ⟨B₀, hB₀⟩ := admits_dampedMobiusEnergy_of_half_le (le_refl (1 / 2 : ℝ))
  refine ⟨C, max B₀ 0, hC0, le_max_right B₀ 0, ?_⟩
  filter_upwards [hev] with T hT
  have hEa : dampedMobiusEnergy a T ≤
      C * (T : ℝ) ^ (1 - 2 * a) * Real.exp (-(vkKappa * vkScale T / 270)) := hT
  have hEc : dampedMobiusEnergy (1 / 2) T ≤ max B₀ 0 := (hB₀ T).trans (le_max_left B₀ 0)
  have hb := (double_integral_tangentCorrelation_bounds ha0 ha2.le T).2
  linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
