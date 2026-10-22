import GaloisForLFunctions.ArithmeticCriticalityTheory.RestrictedWeilGroundEnergyCriticalAtInfinity
import GaloisForLFunctions.ArithmeticCriticalityTheory.MeanZeroProfileVariationInequalityPastPrimeTwo
import GaloisForLFunctions.ArithmeticCriticalityTheory.ParityFoldedCurvedGaugeWeilPositivity
import GaloisForLFunctions.ArithmeticCriticalityTheory.SingleShiftCompleteness
import GaloisForLFunctions.RHTower.Suzuki.SuzukiGroundEnergyContinuity
import GaloisForLFunctions.RHTower.EvenSectorBlindMinimumSmallAperturePositivity
import GaloisForLFunctions.RHTower.WeilParityPoleWeightWindows
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit
import GaloisForLFunctions.«arithmetic-positivity-theory».MarkovPoleHyperbolicCapacityAndApertureThresholds
import GaloisForLFunctions.SquareRootThreshold.ZetaWeilPositivityThroughApertureThreeTenths
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge

/-!
# The positivity routes measure one aperture

The routes that attack the Riemann hypothesis through positivity of the Weil form state their
certificates in different languages: the restricted Weil ground energy `μ(A)` of the
Connes–Consani–Moscovici operator (route RW), the single-shift variation inequality on even
profiles (route ACT), the sinh-capacity inequality on odd tests (route OWU), the even blind
minimum (route EWU), the all-profile and odd windows `Ẑ(F) ≥ c ∫ F²` (routes AIP and APT), the
complex window `Re W_ζ(f, f) ≥ 0` and the lag functional `P_v` (route SRT). This module proves
that at every aperture they are one statement, window positivity of the full zero form

`ZetaWindowPositive A :  Ẑ(F) ≥ 0  for every real C²_c test F vanishing outside [−A, A]`,

and records the direction of every reading.

* **Ground energy is window positivity.** `0 ≤ μ(A)` iff `ZetaWindowPositive A'` for every
  `0 < A' < A` (`ccmRestrictedWeilGroundEnergy_nonneg_iff_forall_lt_zetaWindowPositive`). The
  forward arrow mollifies a `C²` window test into the strict interior of the aperture, where the
  Rayleigh quotient of a smooth source is bounded below by `μ(A)`, and uses the continuity of the
  complete Weil energy under mollification; the backward arrow uses Suzuki's continuity of `μ`.
  Window positivity at the closed aperture gives `0 ≤ μ(A)` directly
  (`ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive`).
* **Parity.** `ZetaWindowPositive A` iff the even window and the odd window are both positive
  (`zetaWindowPositive_iff_even_and_odd`): `Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)`.
* **Odd window is the OWU capacity inequality.** `ZetaOddWindowPositive A` iff every odd window
  test satisfies `sinhPairing g² ≤ 2 · markovForm N g` at the prime cutoff `N = ⌈e^{2A}⌉`
  (`zetaOddWindowPositive_iff_sinhCapacity`).
* **Odd window pays the ACT single-shift inequality.** The ACT tests `Φ(ω_a u)` are odd window
  tests, and on odd tests the pole term is `−2|F̂(i/2)|² ≤ 0`, so the pole-free Markov energy is
  at least `Ẑ` (`shiftedGroundState_markovEnergy_nonneg_of_zetaOddWindowPositive`).
* **EWU.** `0 ≤ μ(A)` gives `0 ≤ evenBlindMinimum A` by the dominance chain
  (`evenBlindMinimum_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`).
* **SRT.** The real window transfers to complex tests and back
  (`re_W_nonneg_of_zetaWindowPositive`, `zetaWindowPositive_of_re_W_nonneg`), and `0 ≤ μ(v/2 + w)`
  gives `0 ≤ Re P_{w,v}` by the Rayleigh bridge
  (`re_lagPrimeWindowRHS_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg`).
* **Endpoint.** RH iff every aperture is window positive iff every ground energy is nonnegative
  (`riemannHypothesis_iff_forall_zetaWindowPositive`,
  `riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg`).

So the aperture through which `μ(A) ≥ 0` is proved for all profiles is the common unit of RW, ACT,
OWU, EWU, AIP, APT and the SRT window, and an improvement on one face counts once.
-/

open MeasureTheory Set Filter Topology
open scoped Real CompactlySupported

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.CHMDDoobGraph _root_.RHTower.WeilMarkovPole
  _root_.RHTower.ArchimedeanAnomaly
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.HTGeometry

/-! ### 1. The window predicates -/

/-- Window positivity of the full zero form at aperture `A`: `Ẑ(F) ≥ 0` for every real `C²_c`
test vanishing outside `[−A, A]`. -/
def ZetaWindowPositive (A : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, A < |x| → F x = 0) →
    0 ≤ fullZeroForm F

/-- The even sector of the window. -/
def ZetaEvenWindowPositive (A : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = F x) →
    (∀ x, A < |x| → F x = 0) → 0 ≤ fullZeroForm F

/-- The odd sector of the window. -/
def ZetaOddWindowPositive (A : ℝ) : Prop :=
  ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F → (∀ x, F (-x) = -F x) →
    (∀ x, A < |x| → F x = 0) → 0 ≤ fullZeroForm F

/-- A smaller aperture inherits window positivity. -/
theorem zetaWindowPositive_antitone {A B : ℝ} (hAB : A ≤ B) (h : ZetaWindowPositive B) :
    ZetaWindowPositive A :=
  fun F hF hFc hv => h F hF hFc fun x hx => hv x (lt_of_le_of_lt hAB hx)

/-- **Parity split of the window.** `Ẑ(F) = Ẑ(F_e) + Ẑ(F_o)`, and the even and odd parts of a
window test are window tests. -/
theorem zetaWindowPositive_iff_even_and_odd (A : ℝ) :
    ZetaWindowPositive A ↔ ZetaEvenWindowPositive A ∧ ZetaOddWindowPositive A := by
  constructor
  · intro h
    exact ⟨fun F hF hFc _ hv => h F hF hFc hv, fun F hF hFc _ hv => h F hF hFc hv⟩
  · rintro ⟨he, ho⟩ F hF hFc hv
    rw [fullZeroForm_eq_even_add_odd hF hFc]
    have hve : ∀ x, A < |x| → evenPartReal F x = 0 := fun x hx => by
      unfold evenPartReal
      rw [hv x hx, hv (-x) (by rwa [abs_neg])]
      ring
    have hvo : ∀ x, A < |x| → oddPartReal F x = 0 := fun x hx => by
      unfold oddPartReal
      rw [hv x hx, hv (-x) (by rwa [abs_neg])]
      ring
    exact add_nonneg
      (he _ (contDiff_evenPartReal hF) (hasCompactSupport_evenPartReal hFc) (evenPartReal_neg F) hve)
      (ho _ (contDiff_oddPartReal hF) (hasCompactSupport_oddPartReal hFc) (oddPartReal_neg F) hvo)

/-! ### 2. The odd window is the OWU sinh-capacity inequality -/

/-- The prime cutoff of a window of aperture `A`: every `n` beyond it has `log n > 2A`. -/
def windowPrimeCutoff (A : ℝ) : ℕ := ⌈Real.exp (2 * A)⌉₊

theorem two_mul_lt_log_of_windowPrimeCutoff_lt {A : ℝ} {n : ℕ} (hn : windowPrimeCutoff A < n) :
    2 * A < Real.log n := by
  have h1 : Real.exp (2 * A) ≤ (windowPrimeCutoff A : ℝ) := Nat.le_ceil _
  have h2 : (windowPrimeCutoff A : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt ((Real.exp_pos _).le.trans h1) h2
  rw [Real.lt_log_iff_exp_lt hn0]
  linarith

/-- Beyond the prime cutoff, a window test and its translate by `log n` have disjoint supports. -/
theorem window_mul_translate_eq_zero {A : ℝ} {g : ℝ → ℝ} (hv : ∀ x, A < |x| → g x = 0)
    {n : ℕ} (hn : windowPrimeCutoff A < n) (u : ℝ) : g u * g (u + Real.log n) = 0 := by
  by_cases hu : A < |u|
  · rw [hv u hu, zero_mul]
  · have hu' : |u| ≤ A := not_lt.mp hu
    have hlog := two_mul_lt_log_of_windowPrimeCutoff_lt hn
    have hA : 0 ≤ A := (abs_nonneg u).trans hu'
    have hmem : A < |u + Real.log n| := by
      have := (abs_le.mp hu').1
      rw [abs_of_pos (by linarith)]
      linarith
    rw [hv _ hmem, mul_zero]

/-- **The odd window is the sinh-capacity inequality of route OWU.** -/
theorem zetaOddWindowPositive_iff_sinhCapacity (A : ℝ) :
    ZetaOddWindowPositive A ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∀ x, g (-x) = -g x) → (∀ x, A < |x| → g x = 0) →
        sinhPairing g ^ 2 ≤ 2 * markovForm (windowPrimeCutoff A) g := by
  constructor
  · intro h g hg hgc hodd hv
    have hN : ∀ n : ℕ, windowPrimeCutoff A < n → ∀ u, g u * g (u + Real.log n) = 0 :=
      fun n hn u => window_mul_translate_eq_zero hv hn u
    rw [← weil_odd_nonneg_iff_sinh_sq_le_two_markovForm hg hgc hodd hN,
      ← fullZeroForm_eq_re_weilFullFunctional hg.continuous hgc]
    exact h g hg hgc hodd hv
  · intro h g hg hgc hodd hv
    have hN : ∀ n : ℕ, windowPrimeCutoff A < n → ∀ u, g u * g (u + Real.log n) = 0 :=
      fun n hn u => window_mul_translate_eq_zero hv hn u
    rw [fullZeroForm_eq_re_weilFullFunctional hg.continuous hgc,
      weil_odd_nonneg_iff_sinh_sq_le_two_markovForm hg hgc hodd hN]
    exact h g hg hgc hodd hv

/-! ### 3. The odd window pays the ACT single-shift inequality -/

/-- The ACT test `Φ(ω_a u)` of an even window profile is an odd window test; on odd tests the
pole term is `−2|F̂(i/2)|² ≤ 0`, so its pole-free Markov energy dominates `Ẑ`. -/
theorem shiftedGroundState_markovEnergy_nonneg_of_zetaOddWindowPositive {A : ℝ}
    (h : ZetaOddWindowPositive A) (a : ℝ) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) (hv : ∀ x, A < |x| → u x = 0) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  set F : ℝ → ℝ := phiDoobTest (fun y => shiftedGroundState a y * u y) with hF_def
  have hF : ContDiff ℝ 2 F := contDiff_phiDoobTest ((contDiff_shiftedGroundState a).mul hu)
  have hFc : HasCompactSupport F := hasCompactSupport_phiDoobTest huc.mul_left
  have hodd : ∀ x, F (-x) = -F x := fun x => by
    simp only [hF_def, phiDoobTest, riemannKernelReal_neg', shiftedGroundState_neg, heven]
    ring
  have hvF : ∀ x, A < |x| → F x = 0 := fun x hx => by
    simp [hF_def, phiDoobTest, hv x hx]
  have hf : ContDiff ℝ 2 fun x => (F x : ℂ) := Complex.ofRealCLM.contDiff.comp hF
  have hfc : HasCompactSupport fun x => (F x : ℂ) := hFc.comp_left Complex.ofReal_zero
  have hoddC : ∀ x, (fun x => (F x : ℂ)) (-x) = -(fun x => (F x : ℂ)) x := fun x => by
    simp [hodd x]
  rw [markovEnergy_eq_W_sub hf hfc, re_weilPoleTerm_weilTest_of_odd hf.continuous hfc hoddC,
    zeta_W_eq_weilFullFunctional hf hfc, ← fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
  have hZ := h F hF hFc hodd hvF
  linarith [sq_nonneg ‖paperFT (fun x => (F x : ℂ)) (Complex.I / 2)‖]

/-! ### 4. Window positivity and the restricted Weil ground energy -/

/-- **Window positivity at aperture `A` gives `μ(A) ≥ 0`.** Every Rayleigh quotient of a smooth
strict-interior source is `(Ẑ(Re u) + Ẑ(Im u)) / ‖u‖²` with both parts window tests. -/
theorem ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive (A : SuzukiPositiveAperture)
    (h : ZetaWindowPositive A.1) : 0 ≤ ccmRestrictedWeilGroundEnergy A := by
  rw [← suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy]
  refine (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).2 ?_
  rintro r ⟨u, -, rfl⟩
  unfold suzukiWeilIntervalFormRayleigh suzukiWeilIntervalFormMass
  refine div_nonneg ?_ (sq_nonneg _)
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℂ) := u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  have hvan : ∀ x, A.1 < |x| → (u : ℝ → ℂ) x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have hm := u.tsupport_subset hmem
      rw [mem_Ioo] at hm
      exact absurd (abs_lt.mpr hm) (not_lt.mpr hx.le)
  rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil,
    zeta_W_re_eq_fullZeroForm_re_add_im hu2 u.hasCompactSupport]
  exact add_nonneg
    (h _ (Complex.reCLM.contDiff.comp hu2) (u.hasCompactSupport.comp_left Complex.zero_re)
      fun x hx => by simp [hvan x hx])
    (h _ (Complex.imCLM.contDiff.comp hu2) (u.hasCompactSupport.comp_left Complex.zero_im)
      fun x hx => by simp [hvan x hx])

/-- **`μ(A) ≥ 0` gives `Ẑ ≥ 0` on smooth sources compactly inside the aperture**, since their
Rayleigh quotients lie above the greatest lower bound `μ(A)`. -/
theorem fullZeroForm_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg {A : SuzukiPositiveAperture}
    (hμ : 0 ≤ ccmRestrictedWeilGroundEnergy A) {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ Ioo (-A.1) A.1) : 0 ≤ fullZeroForm F := by
  by_cases hF0 : F = fun _ => 0
  · rw [hF0]
    exact fullZeroForm_zero.ge
  · have hmass : 0 < ∫ x, F x ^ 2 := by
      obtain ⟨x₀, hx₀⟩ : ∃ x, F x ≠ 0 := by
        by_contra hcon
        exact hF0 (funext fun x => by_contra fun hx => hcon ⟨x, hx⟩)
      exact (hF.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (GaloisForLFunctions.ArithmeticCriticalityTheory.hasCompactSupport_sq hFc)
        (fun x => sq_nonneg (F x)) (pow_ne_zero 2 hx₀)
    obtain ⟨u, hu⟩ : ∃ u, u = realInteriorSource A hF hFc hFs := ⟨_, rfl⟩
    have hQ := ccmRestrictedWeilSourceQuadratic_realInteriorSource A hF hFc hFs
    have hN := norm_sq_realInteriorSource A hF hFc hFs
    rw [← hu] at hQ hN
    have hmass' : suzukiWeilIntervalFormMass A u.toCCMFormVector = ∫ x, F x ^ 2 := by
      unfold suzukiWeilIntervalFormMass
      rw [norm_suzukiWeilIntervalFormEmbedding, hN]
    have hne : suzukiWeilIntervalFormEmbedding A u.toCCMFormVector ≠ 0 := fun h0 => by
      have : suzukiWeilIntervalFormMass A u.toCCMFormVector = 0 := by
        unfold suzukiWeilIntervalFormMass
        rw [h0, norm_zero]
        ring
      linarith
    have hglb := (isGLB_suzukiSmoothInteriorRayleighSet_groundEnergy A).1 ⟨u, hne, rfl⟩
    rw [suzukiWeilIntervalGroundEnergy_eq_ccmRestrictedWeilGroundEnergy] at hglb
    unfold suzukiWeilIntervalFormRayleigh at hglb
    rw [hQ, hmass'] at hglb
    by_contra hneg
    have hlt : fullZeroForm F / ∫ x, F x ^ 2 < 0 := div_neg_of_neg_of_pos (not_le.mp hneg) hmass
    linarith

/-- The mollification `η_k ⋆ F` of a test vanishing outside `[−R, R]` vanishes outside
`[−R − r_k, R + r_k]`, `r_k = 1/(4(k+1))` the radius of the bump. -/
theorem smooth_eq_zero_of_radius_lt_abs {F : ℝ → ℝ} {R : ℝ} (hF : ∀ x, R < |x| → F x = 0)
    (k : ℕ) {x : ℝ} (hx : R + 1 / (4 * ((k : ℝ) + 1)) < |x|) : smooth F k x = 0 := by
  change (∫ t, CHMDDoobGraph.mollifier k t * F (x - t)) = 0
  have h0 : ∀ t, CHMDDoobGraph.mollifier k t * F (x - t) = 0 := fun t => by
    by_cases ht : 1 / (4 * ((k : ℝ) + 1)) ≤ |t|
    · have hm : CHMDDoobGraph.mollifier k t = 0 := by
        apply Function.notMem_support.mp
        change t ∉ Function.support ((_root_.RHTower.WeilOneSided.narrowBump k).normed volume)
        rw [(_root_.RHTower.WeilOneSided.narrowBump k).support_normed_eq, Metric.mem_ball,
          dist_zero_right, Real.norm_eq_abs]
        exact not_lt.mpr ht
      rw [hm, zero_mul]
    · have ht' : |t| < 1 / (4 * ((k : ℝ) + 1)) := not_le.mp ht
      have hfar : R < |x - t| := by
        have := abs_sub_abs_le_abs_sub x t
        linarith
      rw [hF _ hfar, mul_zero]
  simp only [h0, integral_zero]

/-- The mollification of a compactly supported continuous test is smooth. -/
theorem contDiff_top_smooth {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smooth F k) :=
  (mollifier_compact k).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (_root_.RHTower.WeilOneSided.narrowBump k).contDiff_normed
    ((hF.memLp_of_hasCompactSupport (p := 2) hFc).locallyIntegrable (by norm_num))

/-- **`μ(A) ≥ 0` gives window positivity at every smaller aperture.** A `C²` window test of
aperture `A' < A` is the limit of its mollifications, which are smooth sources compactly inside
`(−A, A)` with nonnegative `Ẑ`; the complete Weil energy is continuous under mollification. -/
theorem zetaWindowPositive_of_ccmRestrictedWeilGroundEnergy_nonneg {A : SuzukiPositiveAperture}
    {A' : ℝ} (hA' : A' < A.1) (hμ : 0 ≤ ccmRestrictedWeilGroundEnergy A) :
    ZetaWindowPositive A' := by
  intro F hF hFc hv
  have hsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (smooth F k) := contDiff_top_smooth hF.continuous hFc
  have hsc : ∀ k, HasCompactSupport (smooth F k) := smooth_compact hFc
  obtain ⟨fc, hfc⟩ : ∃ fc : C_c(ℝ, ℝ), (fc : ℝ → ℝ) = F := ⟨⟨⟨F, hF.continuous⟩, hFc⟩, rfl⟩
  have hJ : IntegrableOn (fun x => (autocorr fc 0 - autocorr fc x) * archLevySinhWeight x)
      (Ioi 0) := by
    rw [hfc]
    exact integrableOn_biScaleLevyIntegrand hF hFc
  have hlim := re_weilFullFunctional_smooth_tendsto fc hJ
  rw [hfc] at hlim
  have hZ : Tendsto (fun k => fullZeroForm (smooth F k)) atTop (𝓝 (fullZeroForm F)) := by
    rw [fullZeroForm_eq_re_weilFullFunctional hF.continuous hFc]
    refine hlim.congr fun k => ?_
    exact (fullZeroForm_eq_re_weilFullFunctional (hsm k).continuous (hsc k)).symm
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt (sub_pos.mpr hA')
  refine ge_of_tendsto hZ (Filter.eventually_atTop.mpr ⟨K, fun k hk => ?_⟩)
  have hrad : A' + 1 / (4 * ((k : ℝ) + 1)) < A.1 := by
    have h1 : 1 / (4 * ((k : ℝ) + 1)) ≤ 1 / ((K : ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (K : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    linarith
  apply fullZeroForm_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg hμ (hsm k) (hsc k)
  have hsub : tsupport (smooth F k) ⊆
      Icc (-(A' + 1 / (4 * ((k : ℝ) + 1)))) (A' + 1 / (4 * ((k : ℝ) + 1))) := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    rw [Function.mem_support] at hx
    exact abs_le.mp (not_lt.mp fun hgt => hx (smooth_eq_zero_of_radius_lt_abs hv k hgt))
  exact hsub.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **The aperture dictionary.** `0 ≤ μ(A)` iff every aperture `0 < A' < A` is window positive.
The backward arrow approaches `A` from the left and uses the continuity of `μ`. -/
theorem ccmRestrictedWeilGroundEnergy_nonneg_iff_forall_lt_zetaWindowPositive
    (A : SuzukiPositiveAperture) :
    0 ≤ ccmRestrictedWeilGroundEnergy A ↔
      ∀ A' : ℝ, 0 < A' → A' < A.1 → ZetaWindowPositive A' := by
  constructor
  · intro hμ A' _ hA'
    exact zetaWindowPositive_of_ccmRestrictedWeilGroundEnergy_nonneg hA' hμ
  · intro h
    let a : ℕ → SuzukiPositiveAperture := fun n => ⟨A.1 * (1 - 1 / ((n : ℝ) + 2)), by
      have hn : (1 : ℝ) / ((n : ℝ) + 2) < 1 := by
        rw [div_lt_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact mul_pos A.2 (by linarith)⟩
    have hT : Tendsto a atTop (𝓝 A) := by
      rw [tendsto_subtype_rng]
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        refine (h0.comp (tendsto_add_atTop_nat 1)).congr fun n => ?_
        simp only [Function.comp]
        push_cast
        ring_nf
      have h2 : Tendsto (fun n : ℕ => A.1 * (1 - 1 / ((n : ℝ) + 2))) atTop
          (𝓝 (A.1 * (1 - 0))) :=
        tendsto_const_nhds.mul (tendsto_const_nhds.sub h1)
      simp only [sub_zero, mul_one] at h2
      exact h2
    have hmem : ∀ n, 0 ≤ ccmRestrictedWeilGroundEnergy (a n) := fun n => by
      apply ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive
      apply h _ (a n).2
      show A.1 * (1 - 1 / ((n : ℝ) + 2)) < A.1
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      nlinarith [A.2]
    exact ge_of_tendsto' ((continuous_ccmRestrictedWeilGroundEnergy.tendsto A).comp hT) hmem

/-! ### 5. The readings of the other routes -/

/-- **EWU.** The even blind minimum is nonnegative wherever the ground energy is. -/
theorem evenBlindMinimum_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg
    {A : SuzukiPositiveAperture} (hμ : 0 ≤ ccmRestrictedWeilGroundEnergy A) :
    0 ≤ RHTower.EvenSector.evenBlindMinimum A :=
  hμ.trans (RHTower.EvenSector.ccmRestrictedWeilGroundEnergy_le_evenBlindMinimum A)

/-- **EWU from the window.** -/
theorem evenBlindMinimum_nonneg_of_zetaWindowPositive (A : SuzukiPositiveAperture)
    (h : ZetaWindowPositive A.1) : 0 ≤ RHTower.EvenSector.evenBlindMinimum A :=
  evenBlindMinimum_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg
    (ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive A h)

/-- **SRT, complex tests.** The real window transfers to complex `C²` tests of the same aperture. -/
theorem re_W_nonneg_of_zetaWindowPositive {A : ℝ} (h : ZetaWindowPositive A) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-A) A) : 0 ≤ (zetaZeroConfig.W f f).re := by
  have := zetaZeroConfig_re_W_ge_of_window (A := A) (c := 0)
    (fun F hF hFc hv => by simpa using h F hF hFc hv) hf hfs
  simpa using this

/-- **SRT, complex tests, converse.** -/
theorem zetaWindowPositive_of_re_W_nonneg {A : ℝ}
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
      0 ≤ (zetaZeroConfig.W f f).re) : ZetaWindowPositive A := by
  intro F hF hFc hv
  have hf : ContDiff ℝ 2 fun x => (F x : ℂ) := Complex.ofRealCLM.contDiff.comp hF
  have hfs : tsupport (fun x => (F x : ℂ)) ⊆ Icc (-A) A := by
    refine closure_minimal (fun x hx => ?_) isClosed_Icc
    rw [Function.mem_support] at hx
    have hFx : F x ≠ 0 := fun h0 => hx (by simp [h0])
    exact abs_le.mp (not_lt.mp fun hgt => hFx (hv x hgt))
  have hW := h _ hf hfs
  rw [zeta_W_re_eq_fullZeroForm_re_add_im hf (hFc.comp_left Complex.ofReal_zero)] at hW
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hW
  rwa [fullZeroForm_zero, add_zero] at hW

/-- **SRT, the lag family.** `0 ≤ μ(v/2 + w)` gives `0 ≤ Re P_{w,v}` by the Rayleigh bridge. -/
theorem re_lagPrimeWindowRHS_nonneg_of_ccmRestrictedWeilGroundEnergy_nonneg {w v : ℝ}
    (hw : 0 < w) (hw2 : 2 * w < Real.log 2) (hv : 2 * w < v)
    (hμ : 0 ≤ ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩) :
    0 ≤ (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1)))).re :=
  le_trans (mul_nonneg (mul_nonneg zero_le_two (integral_nonneg fun _ => sq_nonneg _)) hμ)
    (two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS hw hw2 hv)

/-! ### 6. The endpoint -/

/-- Under RH the full zero form is nonnegative on every real `C²_c` test. -/
theorem fullZeroForm_nonneg_of_riemannHypothesis (hRH : RiemannHypothesis) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) : 0 ≤ fullZeroForm F := by
  have h := riemannHypothesis_iff_forall_fullZeroForm_nonneg.mp hRH
    (fun x => F x / riemannKernelReal x)
    (hF.div contDiff_riemannKernelReal fun x => (riemannKernelReal_pos x).ne')
    (hFc.mono' fun x hx => subset_tsupport F fun h0 => hx (by simp [h0]))
  have e : phiDoobTest (fun x => F x / riemannKernelReal x) = F := funext fun x => by
    unfold phiDoobTest
    field_simp [(riemannKernelReal_pos x).ne']
  rwa [e] at h

/-- **RH is window positivity at every aperture.** -/
theorem riemannHypothesis_iff_forall_zetaWindowPositive :
    RiemannHypothesis ↔ ∀ A : ℝ, 0 < A → ZetaWindowPositive A := by
  constructor
  · intro hRH A _ F hF hFc _
    exact fullZeroForm_nonneg_of_riemannHypothesis hRH hF hFc
  · intro h
    rw [riemannHypothesis_iff_forall_fullZeroForm_nonneg]
    intro v hv hvc
    obtain ⟨R, hR0, hR⟩ :=
      exists_vanishing_radius_of_hasCompactSupport (hasCompactSupport_phiDoobTest hvc)
    exact h (R + 1) (by linarith) _ (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc)
      fun x hx => hR x (by linarith)

/-- **RH is nonnegativity of the ground energy at every aperture.** -/
theorem riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg :
    RiemannHypothesis ↔ ∀ A : SuzukiPositiveAperture, 0 ≤ ccmRestrictedWeilGroundEnergy A := by
  constructor
  · exact fun hRH A => ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH A
  · intro h
    by_contra hRH
    obtain ⟨B, hB⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hRH
    exact absurd (h B) (not_le.mpr hB)

/-- **The positivity routes measure one aperture.** At every aperture `A`: the restricted Weil
ground energy is nonnegative iff every smaller aperture is window positive; the window splits into
its even and odd sectors; the odd sector is the OWU capacity inequality; and at the endpoint all of
them, the EWU blind minimum and the SRT lag functional included, are the Riemann hypothesis. -/
theorem theRoutesMeasureOneAperture (A : SuzukiPositiveAperture) :
    (0 ≤ ccmRestrictedWeilGroundEnergy A ↔
      ∀ A' : ℝ, 0 < A' → A' < A.1 → ZetaWindowPositive A') ∧
    (ZetaWindowPositive A.1 ↔ ZetaEvenWindowPositive A.1 ∧ ZetaOddWindowPositive A.1) ∧
    (ZetaOddWindowPositive A.1 ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∀ x, g (-x) = -g x) → (∀ x, A.1 < |x| → g x = 0) →
        sinhPairing g ^ 2 ≤ 2 * markovForm (windowPrimeCutoff A.1) g) ∧
    (ZetaWindowPositive A.1 → 0 ≤ RHTower.EvenSector.evenBlindMinimum A) ∧
    (RiemannHypothesis ↔ ∀ B : ℝ, 0 < B → ZetaWindowPositive B) ∧
    (RiemannHypothesis ↔ ∀ B : SuzukiPositiveAperture, 0 ≤ ccmRestrictedWeilGroundEnergy B) :=
  ⟨ccmRestrictedWeilGroundEnergy_nonneg_iff_forall_lt_zetaWindowPositive A,
    zetaWindowPositive_iff_even_and_odd A.1, zetaOddWindowPositive_iff_sinhCapacity A.1,
    evenBlindMinimum_nonneg_of_zetaWindowPositive A, riemannHypothesis_iff_forall_zetaWindowPositive,
    riemannHypothesis_iff_forall_ccmRestrictedWeilGroundEnergy_nonneg⟩

end GaloisForLFunctions.SquareRootThreshold

end
