import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.RetainedVarianceAndHalfWindowBandBelowLogFour
import GaloisForLFunctions.ArithmeticCriticalityTheory.PrimitiveHyperplaneCriticality
import GaloisForLFunctions.ArithmeticIncidencePositivity.AnExplicitLargerApertureRetainsAWeilFloor

/-!
# Collective Prime-Power Sliver Payment and Signed Line-Exact Theta Gauges

On any half-window `[m - c, m]` (`c > 0`), the reflection pair `(f, collarReflect m f)` splits the
discrepancy `W(f) - |𝒞_m(f)|` between the Weil self-energy and the ordered collar coupling into the
even and odd reflection sectors on `[-c, c]`, while truncating the prime-power series in `𝒞_m(f)`
identically to the finite set of acting prime powers `2 ≤ n ≤ ⌊e^{2c}⌋₊` (`log n ≤ 2c`).

1. **Finite collective sliver truncation and arbitrary-centre reflection-pair identity**
   (`orderedCoupling_collarReflect_eq_finsetSum`, `weilQuad_sub_abs_orderedCoupling_eq_half_min`).
   For `f ∈ C²_c(ℝ)` vanishing outside `[m - c, m]`, `selfConv f (2m - log n) = 0` for all
   `n > ⌊e^{2c}⌋₊`, and `W(f) - |𝒞_m(f)| = (1/2) min(W(G_+), W(G_-))` where
   `G_±(u) = f(u + m) ± f(-u + m)` are supported in `[-c, c]`.

2. **Impossibility of a window-independent nonsingular even theta gauge with nonnegative pole charge**
   (`no_windowIndependent_evenThetaGauge_nonneg_poleCharge`). For any single even theta gauge
   `ω = translateSpan s α b` whose profile `M = Φ ω` is nonsingular on `ℝ`, either `M < 0`
   everywhere or `M > 0` everywhere with strictly positive outside cosh deficit
   `A/2 - coshCharge ω (-c, c) > 0` (hence strictly negative pole-charge coefficient) on every
   window `(-c, c)`.

3. **Window-adapted signed line-exact theta-gauge family with retained variance and nonnegative
   pole charges** (`signedEvenThetaGauge`, `exists_signedEvenThetaGauge_pos_and_nonneg_poleCharge`,
   `even_nonneg_iff_signedEvenThetaGauge`, `reflectionPair_signedThetaGauge_representation`).
   Perturbing the negated even harmonic pair `-evenNullCoeff b` on `evenNullShift b = ![b, -b, 0]`
   by `α₀ τ_0` yields a 3-translate even theta gauge `ω_{b, α₀}^+` that is exact on the line,
   strictly positive on `[-(c + 1), c + 1]` for large `b`, and carries nonnegative pole charge
   `2(coshCharge ω_{b, α₀}^+ (-c, c) - α₀/2) ≥ 0` across `0 ≤ α₀ ≤ α₀^*(b, c)` — strictly positive
   for `0 ≤ α₀ < α₀^*(b, c)` and identically zero at `α₀ = α₀^*(b, c)`. Together with the odd
   shifted ground state `shiftedGroundState a` (`a > 0`), both parity sectors express the window
   form as a line-exact signed Dirichlet form with retained pole variance plus nonnegative pole
   charges.

4. **Unconditional super-`log 2` floor and global equivalence**
   (`weilQuad_sub_abs_orderedCoupling_ge_of_le_enlargedWeilFloorAperture`,
   `collectiveSliverPayment_global_equivalence`). Across all `m ∈ ℝ` and
   `0 < c ≤ enlargedWeilFloorAperture` (`2c` exceeding `181/250 > log 2`, where `p = 2` acts in the
   sliver sum), `W(f) - |𝒞_m(f)| ≥ (1/8000) ∫ f²`. Globally across all `c > 0`, nonnegativity of
   the two-sector signed theta-gauge representation on all reflection pairs is equivalent to
   `∀ c > 0, ZetaWindowPositive c` and `RiemannHypothesis`.
-/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

private lemma fullZeroForm_eq_weilQuad_of_cont {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) : fullZeroForm F = weilQuad F :=
  GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF hFc

/-! ### 1. Collective prime-power sliver truncation and arbitrary-centre reflection-pair identity -/

/-- A function vanishing left of `m - c` and right of `m` has compact support in `[m - c, m]`. -/
theorem hasCompactSupport_of_collarWindow {m c : ℝ} {f : ℝ → ℝ}
    (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_Icc (a := m - c) (b := m)) fun u hu => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with h | h
    · exact hleft u h
    · exact hm u h

/-- On a collar window of width `c ≥ 0` left of `m`, all shifts `y > 2c` miss the reflected
self-convolution `selfConv f (2m - y)`. -/
theorem selfConv_eq_zero_of_two_mul_lt {m c y : ℝ} (_hc : 0 ≤ c) {f : ℝ → ℝ}
    (hleft : ∀ u, u < m - c → f u = 0) (hy : 2 * c < y) :
    selfConv f (2 * m - y) = 0 := by
  unfold selfConv
  refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
  dsimp only [Pi.zero_apply]
  rcases lt_or_ge u (m - c) with hu | hu
  · rw [hleft u hu, zero_mul]
  · rw [hleft (2 * m - y - u) (by linarith), mul_zero]

/-- **Finite collective prime-power sliver truncation.** For `f ∈ C²_c(ℝ)` supported in
`[m - c, m]` (`c ≥ 0`), the ordered reflection coupling truncates identically to the acting prime
powers `2 ≤ n ≤ ⌊e^{2c}⌋₊`. -/
theorem orderedCoupling_collarReflect_eq_finsetSum {m c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    orderedCoupling f (collarReflect m f) =
      collarHankel m f -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * c)⌋₊,
          vonMangoldtAtom n * selfConv f (2 * m - Real.log n) := by
  have hfc := hasCompactSupport_of_collarWindow hm hleft
  rw [orderedCoupling_collarReflect hf hfc hm]
  congr 1
  refine tsum_eq_sum fun n hn => ?_
  simp only [Finset.mem_Icc, not_and_or] at hn
  rcases hn with hlt2 | hgt
  · simp [vonMangoldtAtom, hlt2]
  · rcases lt_or_ge n 2 with hlt2' | hge2
    · simp [vonMangoldtAtom, not_le.mpr hlt2']
    · have hexp : Real.exp (2 * c) < (n : ℝ) := by
        by_contra hle
        exact hgt (Nat.le_floor (not_lt.mp hle))
      have hn0 : (0 : ℝ) < n := by positivity
      have hlog : 2 * c < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hexp
      rw [selfConv_eq_zero_of_two_mul_lt hc hleft hlog, mul_zero]

/-- Shifting a test `f` on `[m - c, m]` by `m` identifies `selfConv f (2m - y)` with the origin
reflection `selfConv (fun u => f (u + m)) (-y)`. -/
theorem selfConv_shift_centre (m y : ℝ) (f : ℝ → ℝ) :
    selfConv f (2 * m - y) = selfConv (fun u => f (u + m)) (-y) := by
  unfold selfConv
  rw [← integral_add_right_eq_self (fun u => f u * f (2 * m - y - u)) m]
  exact integral_congr_ae (Eventually.of_forall fun u => by dsimp only; congr 2; ring)

/-- The centred even reflection-pair profile `G_+(u) = f(u + m) + f(-u + m)`. -/
def reflectionEvenProfile (m : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  f (u + m) + f (-u + m)

/-- The centred odd reflection-pair profile `G_-(u) = f(u + m) - f(-u + m)`. -/
def reflectionOddProfile (m : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  f (u + m) - f (-u + m)

theorem reflectionEvenProfile_neg (m : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    reflectionEvenProfile m f (-u) = reflectionEvenProfile m f u := by
  unfold reflectionEvenProfile
  rw [neg_neg, add_comm]

theorem reflectionOddProfile_neg (m : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    reflectionOddProfile m f (-u) = -reflectionOddProfile m f u := by
  unfold reflectionOddProfile
  rw [neg_neg]
  ring

theorem contDiff_reflectionEvenProfile {m : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (reflectionEvenProfile m f) :=
  (hf.comp (contDiff_id.add contDiff_const)).add
    (hf.comp (contDiff_id.neg.add contDiff_const))

theorem contDiff_reflectionOddProfile {m : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (reflectionOddProfile m f) :=
  (hf.comp (contDiff_id.add contDiff_const)).sub
    (hf.comp (contDiff_id.neg.add contDiff_const))

theorem supportedIn_reflectionEvenProfile {m c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ}
    (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    SupportedIn c (reflectionEvenProfile m f) := fun u hu => by
  unfold reflectionEvenProfile
  rcases lt_abs.mp hu with hgt | hlt
  · rw [hm (u + m) (by linarith), hleft (-u + m) (by linarith), add_zero]
  · rw [hleft (u + m) (by linarith), hm (-u + m) (by linarith), add_zero]

theorem supportedIn_reflectionOddProfile {m c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ}
    (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    SupportedIn c (reflectionOddProfile m f) := fun u hu => by
  unfold reflectionOddProfile
  rcases lt_abs.mp hu with hgt | hlt
  · rw [hm (u + m) (by linarith), hleft (-u + m) (by linarith), sub_zero]
  · rw [hleft (u + m) (by linarith), hm (-u + m) (by linarith), sub_zero]

/-- **Arbitrary-centre reflection-pair discrepancy identity.** For every `f ∈ C²_c(ℝ)` vanishing
right of `m`, `W(f) - |𝒞_m(f)| = (1/2) min(W(G_+), W(G_-))`. -/
theorem weilQuad_sub_abs_orderedCoupling_eq_half_min {m : ℝ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hm : ∀ u, m < u → f u = 0) :
    weilQuad f - |orderedCoupling f (collarReflect m f)| =
      (1 / 2) * min (weilQuad (reflectionEvenProfile m f))
        (weilQuad (reflectionOddProfile m f)) := by
  have hev : (fun u => f u + collarReflect m f u) =
      fun u => reflectionEvenProfile m f (u - m) := by
    funext u; simp only [collarReflect, reflectionEvenProfile]; congr 1 <;> congr 1 <;> ring
  have hod : (fun u => f u + -collarReflect m f u) =
      fun u => reflectionOddProfile m f (u - m) := by
    funext u; simp only [collarReflect, reflectionOddProfile, sub_eq_add_neg]
    congr 1; · congr 1; ring
    · congr 2; ring
  have h1 := weilQuad_add_collarReflect hf hfc hm
  have h2 := weilQuad_sub_collarReflect hf hfc hm
  rw [← orderedCoupling_collarReflect hf hfc hm, hev, weilQuad_comp_sub] at h1
  rw [← orderedCoupling_collarReflect hf hfc hm, hod, weilQuad_comp_sub] at h2
  rw [h1, h2]
  set A := weilQuad f
  set B := orderedCoupling f (collarReflect m f)
  rcases le_total 0 B with hB | hB
  · rw [abs_of_nonneg hB, min_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos hB, min_eq_left (by linarith)]; ring

/-! ### 2. Impossibility of a window-independent nonsingular even theta gauge with nonnegative pole charge -/

/-- **Window-independent even theta-gauge obstruction.** Let `ω = translateSpan s α b` be a single
even theta gauge (`M = Φ ω` even, `B = 0`) that is nonsingular everywhere on `ℝ` (as required to
serve as a global nonvanishing coordinate across all windows `(-c, c)`). Either `M < 0` everywhere
on `ℝ`, or `M > 0` everywhere on `ℝ` and on **every** window `(-c, c)` (`c ≥ 0`) the outside cosh
deficit `A/2 - coshCharge ω (-c, c)` is strictly positive — making the even pole-charge coefficient
`-2(A/2 - coshCharge ω (-c, c))` strictly negative. -/
theorem no_windowIndependent_evenThetaGauge_nonneg_poleCharge {ι : Type*} (s : Finset ι)
    (α b : ι → ℝ)
    (_hMeven : ∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
      riemannKernelReal x * translateSpan s α b x)
    (_hB : translateSinhCoefficient s α b = 0)
    (hMnz : ∀ x : ℝ, riemannKernelReal x * translateSpan s α b x ≠ 0) :
    (∀ x : ℝ, riemannKernelReal x * translateSpan s α b x < 0) ∨
      ((∀ x : ℝ, 0 < riemannKernelReal x * translateSpan s α b x) ∧
        ∀ c : ℝ, 0 ≤ c →
          0 < translateCoshCoefficient s α b / 2 -
            coshCharge (translateSpan s α b) (Ioo (-c) c)) := by
  set M : ℝ → ℝ := fun x => riemannKernelReal x * translateSpan s α b x
  have hMcont : Continuous M :=
    continuous_riemannKernelReal.mul (contDiff_translateSpan s α b).continuous
  rcases lt_or_gt_of_ne (hMnz 0) with hM0 | hM0
  · refine Or.inl fun x => ?_
    rcases lt_or_gt_of_ne (hMnz x) with hx | hx
    · exact hx
    · exfalso
      have hconn : IsPreconnected (M '' univ) := isConnected_univ.isPreconnected.image M hMcont.continuousOn
      obtain ⟨z, _, hz⟩ := hconn.Icc_subset (mem_image_of_mem M (mem_univ 0))
        (mem_image_of_mem M (mem_univ x)) ⟨hM0.le, hx.le⟩
      exact hMnz z hz
  · have hMpos : ∀ x : ℝ, 0 < M x := fun x => by
      rcases lt_or_gt_of_ne (hMnz x) with hx | hx
      · exfalso
        have hconn : IsPreconnected (M '' univ) := isConnected_univ.isPreconnected.image M hMcont.continuousOn
        obtain ⟨z, _, hz⟩ := hconn.Icc_subset (mem_image_of_mem M (mem_univ x))
          (mem_image_of_mem M (mem_univ 0)) ⟨hx.le, hM0.le⟩
        exact hMnz z hz
      · exact hx
    refine Or.inr ⟨hMpos, fun c hc => ?_⟩
    have hint : Integrable fun x => M x * Real.cosh (x / 2) := by
      have hsum : (fun x => M x * Real.cosh (x / 2)) =
          fun x => ∑ j ∈ s, α j * (riemannKernelReal (x - b j) * Real.cosh (x / 2)) := by
        funext x; dsimp only [M]; rw [thetaGauge_coordinate, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsum]
      exact integrable_finsetSum _ fun j _ =>
        (integrable_riemannKernelReal_sub_mul_cosh_half (b j)).const_mul (α j)
    have htot := integral_thetaGauge_mul_cosh s α b
    have hsplit := integral_add_compl (s := Ioo (-c) c) measurableSet_Ioo hint
    have hdef : translateCoshCoefficient s α b / 2 -
        coshCharge (translateSpan s α b) (Ioo (-c) c) =
        ∫ x in (Ioo (-c) c)ᶜ, M x * Real.cosh (x / 2) := by
      unfold coshCharge
      change translateCoshCoefficient s α b / 2 - ∫ x in Ioo (-c) c, M x * Real.cosh (x / 2) = _
      linarith
    rw [hdef]
    have hsub : Icc c (c + 1) ⊆ (Ioo (-c) c)ᶜ := fun x hx hmem => by
      linarith [hx.1, hmem.2]
    have hmono : (∫ x in Icc c (c + 1), M x * Real.cosh (x / 2)) ≤
        ∫ x in (Ioo (-c) c)ᶜ, M x * Real.cosh (x / 2) :=
      setIntegral_mono_set (hint.integrableOn)
        (Eventually.of_forall fun x => mul_nonneg (hMpos x).le (Real.cosh_pos _).le)
        (Eventually.of_forall hsub)
    have hIcc : 0 < ∫ x in Icc c (c + 1), M x * Real.cosh (x / 2) := by
      have hci : Continuous fun x => M x * Real.cosh (x / 2) :=
        hMcont.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      exact intervalIntegral.intervalIntegral_pos_of_pos_on (hci.intervalIntegrable c (c + 1))
        (fun x _ => mul_pos (hMpos x) (Real.cosh_pos _)) (by linarith)
    linarith

/-- Ground-state (`M = Φ`) outside cosh deficit `1/2 - ∫_{-c}^c Φ(x) cosh(x/2) dx` is strictly
positive for every `c ≥ 0`. -/
theorem groundState_outsideCoshDeficit_pos {c : ℝ} (hc : 0 ≤ c) :
    0 < 1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2) := by
  set s0 : Finset Unit := {()}
  set α0 : Unit → ℝ := fun _ => 1
  set b0 : Unit → ℝ := fun _ => 0
  have hcoord : ∀ x, riemannKernelReal x * translateSpan s0 α0 b0 x = riemannKernelReal x :=
    fun x => by rw [thetaGauge_coordinate]; simp [s0, α0, b0]
  have hMeven : ∀ x, riemannKernelReal (-x) * translateSpan s0 α0 b0 (-x) =
      riemannKernelReal x * translateSpan s0 α0 b0 x := fun x => by
    rw [hcoord, hcoord, riemannKernelReal_neg']
  have hB : translateSinhCoefficient s0 α0 b0 = 0 := by
    unfold translateSinhCoefficient; simp [s0, α0, b0]
  have hMnz : ∀ x, riemannKernelReal x * translateSpan s0 α0 b0 x ≠ 0 := fun x => by
    rw [hcoord]; exact (riemannKernelReal_pos x).ne'
  rcases no_windowIndependent_evenThetaGauge_nonneg_poleCharge s0 α0 b0 hMeven hB hMnz with
    hneg | ⟨_, hpos⟩
  · exfalso; have := hneg 0; rw [hcoord] at this; linarith [riemannKernelReal_pos 0]
  · have hp := hpos c hc
    have hA : translateCoshCoefficient s0 α0 b0 = 1 := by
      unfold translateCoshCoefficient; simp [s0, α0, b0]
    have hcc : coshCharge (translateSpan s0 α0 b0) (Ioo (-c) c) =
        ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2) := by
      unfold coshCharge
      exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by rw [hcoord]
    rwa [hA, hcc] at hp

/-! ### 3. Signed line-exact even theta gauges with retained variance and nonnegative pole charges -/

/-- Coefficients `![-1, -1, α₀ + 2 cosh(b/2)]` of the signed 3-translate even theta gauge on
`evenNullShift b = ![b, -b, 0]`. -/
def signedEvenThetaCoeff (b α₀ : ℝ) : Fin 3 → ℝ :=
  ![-1, -1, α₀ + 2 * Real.cosh (b / 2)]

/-- The signed even theta gauge `ω_{b, α₀}^+ = translateSpan univ (signedEvenThetaCoeff b α₀) (evenNullShift b)`. -/
def signedEvenThetaGauge (b α₀ : ℝ) : ℝ → ℝ :=
  translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b)

/-- The test coordinate `M_{b, α₀}^+(x) = Φ(x) ω_{b, α₀}^+(x)`. -/
def signedEvenThetaProfile (b α₀ x : ℝ) : ℝ :=
  riemannKernelReal x * signedEvenThetaGauge b α₀ x

theorem signedEvenThetaProfile_eq (b α₀ x : ℝ) :
    signedEvenThetaProfile b α₀ x =
      (α₀ + 2 * Real.cosh (b / 2)) * riemannKernelReal x -
        riemannKernelReal (x - b) - riemannKernelReal (x + b) := by
  unfold signedEvenThetaProfile signedEvenThetaGauge
  rw [riemannKernelReal_mul_translateSpan]
  simp [Fin.sum_univ_three, signedEvenThetaCoeff, evenNullShift, sub_neg_eq_add]
  ring

theorem signedEvenThetaProfile_eq_add_mul (b α₀ x : ℝ) :
    signedEvenThetaProfile b α₀ x =
      signedEvenThetaProfile b 0 x + α₀ * riemannKernelReal x := by
  rw [signedEvenThetaProfile_eq, signedEvenThetaProfile_eq]
  ring

theorem signedEvenThetaProfile_neg (b α₀ x : ℝ) :
    signedEvenThetaProfile b α₀ (-x) = signedEvenThetaProfile b α₀ x := by
  rw [signedEvenThetaProfile_eq, signedEvenThetaProfile_eq, riemannKernelReal_neg',
    show -x - b = -(x + b) by ring, show -x + b = -(x - b) by ring,
    riemannKernelReal_neg', riemannKernelReal_neg']
  ring

theorem translateSinhCoefficient_signedEvenTheta (b α₀ : ℝ) :
    translateSinhCoefficient Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) = 0 := by
  simp [translateSinhCoefficient, Fin.sum_univ_three, signedEvenThetaCoeff, evenNullShift,
    show -b / 2 = -(b / 2) by ring, Real.sinh_neg]

theorem translateCoshCoefficient_signedEvenTheta (b α₀ : ℝ) :
    translateCoshCoefficient Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) = α₀ := by
  simp [translateCoshCoefficient, Fin.sum_univ_three, signedEvenThetaCoeff, evenNullShift,
    show -b / 2 = -(b / 2) by ring, Real.cosh_neg]
  ring

/-- **Line-exactness of `signedEvenThetaGauge`.** On the whole line `ℝ`, every signed even theta
gauge has zero residual potential: `Ẑ(Φ ω_{b, α₀}^+ u) = J_{M^+}(u) - 2 V_c^ℝ(u)` on even `u`. -/
theorem fullZeroForm_signedEvenTheta_univ (b α₀ : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    fullZeroForm (phiDoobTest fun y => signedEvenThetaGauge b α₀ y * u y) =
      signedJumpEnergy (signedEvenThetaProfile b α₀) u -
        2 * chargeVariance (fun x => signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) univ u := by
  unfold signedEvenThetaProfile signedEvenThetaGauge
  rw [fullZeroForm_thetaGauge_eq_univ Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) hu huc]
  have hsodd : ∀ x, riemannKernelReal (-x) *
      translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) (-x) *
      Real.sinh (-x / 2) =
      -(riemannKernelReal x *
        translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x *
        Real.sinh (x / 2)) := fun x => by
    have hm := signedEvenThetaProfile_neg b α₀ x
    unfold signedEvenThetaProfile signedEvenThetaGauge at hm
    rw [hm, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]; ring
  have h1 : (∫ x in univ, riemannKernelReal x *
      translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x *
      Real.sinh (x / 2)) = 0 := by
    rw [Measure.restrict_univ]; exact integral_eq_zero_of_odd hsodd
  have h2 : (∫ x, u x ^ 2 * (riemannKernelReal x *
      translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x *
      Real.sinh (x / 2))) = 0 :=
    integral_eq_zero_of_odd fun x => by rw [heven, hsodd]; ring
  have h3 : (∫ x, u x * (riemannKernelReal x *
      translateSpan Finset.univ (signedEvenThetaCoeff b α₀) (evenNullShift b) x *
      Real.sinh (x / 2))) = 0 :=
    integral_eq_zero_of_odd fun x => by rw [heven, hsodd]; ring
  unfold chargeVariance
  rw [h1, h2, h3]
  ring

/-- **Exact window identity for `signedEvenThetaGauge`.** On any symmetric window `(-c, c)` (`c ≥ 0`),
the pole-charge term has coefficient `2(coshCharge ω_{b, α₀}^+ (-c, c) - α₀ / 2)`. -/
theorem fullZeroForm_signedEvenTheta_window {c : ℝ} (hc : 0 ≤ c) (b α₀ : ℝ)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    fullZeroForm (phiDoobTest fun y => signedEvenThetaGauge b α₀ y * u y) =
      signedJumpEnergy (signedEvenThetaProfile b α₀) u -
        2 * chargeVariance
          (fun x => signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) (Ioo (-c) c) u +
        2 * (coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2) *
          ∫ x, u x ^ 2 * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) := by
  have hid := fullZeroForm_evenThetaGauge_window Finset.univ (signedEvenThetaCoeff b α₀)
    (evenNullShift b) hc
    (fun x => by simpa only [signedEvenThetaProfile, signedEvenThetaGauge] using
      signedEvenThetaProfile_neg b α₀ x)
    (translateSinhCoefficient_signedEvenTheta b α₀) hu huc heven
  rw [translateCoshCoefficient_signedEvenTheta] at hid
  unfold signedEvenThetaProfile signedEvenThetaGauge
  linarith

/-- For every compact radius `R ≥ 0`, choosing `b > 0` sufficiently large makes
`signedEvenThetaProfile b α₀` strictly positive on `[-R, R]` for all `α₀ ≥ 0`. -/
theorem exists_shift_signedEvenThetaProfile_pos {R : ℝ} (hR : 0 ≤ R) :
    ∃ b : ℝ, 0 < b ∧ ∀ α₀ : ℝ, 0 ≤ α₀ → ∀ x ∈ Icc (-R) R, 0 < signedEvenThetaProfile b α₀ x := by
  obtain ⟨x₀, hx₀I, hx₀min⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : -R ≤ R)) continuous_riemannKernelReal.continuousOn
  have hΦ0 := riemannKernelReal_pos x₀
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * riemannKernelReal 0 / riemannKernelReal x₀)
  refine ⟨(n : ℝ) + 1, by positivity, fun α₀ hα₀ x hx => ?_⟩
  set b : ℝ := (n : ℝ) + 1
  have hb_gt : 2 * riemannKernelReal 0 / riemannKernelReal x₀ < b :=
    hn.trans (by dsimp only [b]; linarith)
  have hmul : 2 * riemannKernelReal 0 < b * riemannKernelReal x₀ := by
    rwa [div_lt_iff₀ hΦ0] at hb_gt
  have hcosh : b / 2 ≤ Real.cosh (b / 2) := by
    have := Real.self_le_sinh_iff.mpr (show (0 : ℝ) ≤ b / 2 by positivity)
    linarith [(Real.sinh_lt_cosh (b / 2)).le]
  have hΦx : riemannKernelReal x₀ ≤ riemannKernelReal x := hx₀min hx
  have h1 := riemannKernelReal_le_zero_point (x - b)
  have h2 := riemannKernelReal_le_zero_point (x + b)
  have hαΦ : 0 ≤ α₀ * riemannKernelReal x := mul_nonneg hα₀ (riemannKernelReal_pos x).le
  rw [signedEvenThetaProfile_eq]
  nlinarith [mul_le_mul_of_nonneg_right hcosh (riemannKernelReal_pos x).le]

/-- The unique parameter `α₀^*(b, c)` at which the outside cosh deficit of
`signedEvenThetaGauge b α₀` on `(-c, c)` vanishes identically. -/
def neutralEvenThetaParam (b c : ℝ) : ℝ :=
  coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) /
    (1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2))

theorem coshCharge_signedEvenTheta_sub_half (b α₀ c : ℝ) :
    coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2 =
      coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) -
        α₀ * (1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)) := by
  have hcont0 : Continuous fun x => signedEvenThetaProfile b 0 x * Real.cosh (x / 2) :=
    (continuous_riemannKernelReal.mul
      (contDiff_translateSpan Finset.univ (signedEvenThetaCoeff b 0) (evenNullShift b)).continuous).mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hcontΦ : Continuous fun x => riemannKernelReal x * Real.cosh (x / 2) :=
    continuous_riemannKernelReal.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))
  have hi0 : IntegrableOn (fun x => signedEvenThetaProfile b 0 x * Real.cosh (x / 2)) (Ioo (-c) c) :=
    integrableOn_Ioo_of_continuous hcont0
  have hiΦ : IntegrableOn (fun x => riemannKernelReal x * Real.cosh (x / 2)) (Ioo (-c) c) :=
    integrableOn_Ioo_of_continuous hcontΦ
  have hcc : coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) =
      coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) +
        α₀ * ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2) := by
    unfold coshCharge
    have hpt : (fun x => riemannKernelReal x * signedEvenThetaGauge b α₀ x * Real.cosh (x / 2)) =
        fun x => signedEvenThetaProfile b 0 x * Real.cosh (x / 2) +
          α₀ * (riemannKernelReal x * Real.cosh (x / 2)) := by
      funext x
      change signedEvenThetaProfile b α₀ x * Real.cosh (x / 2) = _
      rw [signedEvenThetaProfile_eq_add_mul]; ring
    rw [hpt, integral_add hi0 (hiΦ.const_mul α₀), integral_const_mul]
    rfl
  rw [hcc]
  ring

/-- **Existence of positive-on-window, nonnegative-pole-charge (and zero-deficit) even theta gauges.**
For every `c > 0`, there exist `b > 0` such that `α₀^*(b, c) > 0`, `M_{b, α₀}^+ > 0` on
`[-(c + 1), c + 1]` for all `α₀ ≥ 0`, the pole-charge coefficient
`2(coshCharge ω_{b, α₀}^+ (-c, c) - α₀/2)` is strictly positive for `0 ≤ α₀ < α₀^*(b, c)` and
identically zero at `α₀ = α₀^*(b, c)`. -/
theorem exists_signedEvenThetaGauge_pos_and_nonneg_poleCharge {c : ℝ} (hc : 0 < c) :
    ∃ b : ℝ, 0 < b ∧ 0 < neutralEvenThetaParam b c ∧
      (∀ α₀ : ℝ, 0 ≤ α₀ → ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) ∧
      (∀ α₀ : ℝ, 0 ≤ α₀ → α₀ < neutralEvenThetaParam b c →
        0 < 2 * (coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2)) ∧
      coshCharge (signedEvenThetaGauge b (neutralEvenThetaParam b c)) (Ioo (-c) c) -
        neutralEvenThetaParam b c / 2 = 0 := by
  obtain ⟨b, hb0, hbpos⟩ := exists_shift_signedEvenThetaProfile_pos (R := c + 1) (by linarith)
  have hden := groundState_outsideCoshDeficit_pos hc.le
  have hnum : 0 < coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) := by
    unfold coshCharge
    have hci : Continuous fun x => signedEvenThetaProfile b 0 x * Real.cosh (x / 2) :=
      (continuous_riemannKernelReal.mul
        (contDiff_translateSpan Finset.univ (signedEvenThetaCoeff b 0) (evenNullShift b)).continuous).mul
        (Real.continuous_cosh.comp (continuous_id.div_const 2))
    change 0 < ∫ x in Ioo (-c) c, signedEvenThetaProfile b 0 x * Real.cosh (x / 2)
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith)]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hci.intervalIntegrable (-c) c)
      (fun x hx => mul_pos (hbpos 0 le_rfl x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        (Real.cosh_pos _)) (by linarith)
  have hαpos : 0 < neutralEvenThetaParam b c := div_pos hnum hden
  refine ⟨b, hb0, hαpos, hbpos, fun α₀ _ hlt => ?_, ?_⟩
  · rw [coshCharge_signedEvenTheta_sub_half]
    have hmul : α₀ * (1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)) <
        coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) :=
      (lt_div_iff₀ hden).mp hlt
    linarith
  · rw [coshCharge_signedEvenTheta_sub_half]
    unfold neutralEvenThetaParam
    rw [div_mul_cancel₀ _ hden.ne', sub_self]

/-- Smooth globally positive extension of `signedEvenThetaProfile b α₀` outside `[-(c + 1), c + 1]`
agreeing with `signedEvenThetaProfile b α₀` on `[-c, c]`. -/
def regularizedEvenThetaProfile (c b α₀ x : ℝ) : ℝ :=
  signedEvenThetaProfile b α₀ x * smoothPlateau c x + (1 - smoothPlateau c x)

theorem regularizedEvenThetaProfile_pos {c b α₀ : ℝ}
    (hpos : ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) (x : ℝ) :
    0 < regularizedEvenThetaProfile c b α₀ x := by
  unfold regularizedEvenThetaProfile
  by_cases hx : |x| < c + 1
  · have hxI : x ∈ Icc (-(c + 1)) (c + 1) := abs_le.mp hx.le
    have hM := hpos x hxI
    have hp0 := smoothPlateau_nonneg c x
    have hp1 := smoothPlateau_le_one c x
    rcases eq_or_lt_of_le hp0 with hpz | hpp
    · rw [← hpz]; norm_num
    · have : 0 < signedEvenThetaProfile b α₀ x * smoothPlateau c x := mul_pos hM hpp
      linarith
  · rw [smoothPlateau_eq_zero (not_lt.mp hx)]
    norm_num

theorem regularizedEvenThetaProfile_eq_of_abs_le {c b α₀ x : ℝ} (hx : |x| ≤ c) :
    regularizedEvenThetaProfile c b α₀ x = signedEvenThetaProfile b α₀ x := by
  unfold regularizedEvenThetaProfile
  rw [smoothPlateau_eq_one hx]
  ring

theorem regularizedEvenThetaProfile_neg (c b α₀ x : ℝ) :
    regularizedEvenThetaProfile c b α₀ (-x) = regularizedEvenThetaProfile c b α₀ x := by
  unfold regularizedEvenThetaProfile
  rw [signedEvenThetaProfile_neg, smoothPlateau_neg]

theorem contDiff_regularizedEvenThetaProfile (c b α₀ : ℝ) :
    ContDiff ℝ 2 (regularizedEvenThetaProfile c b α₀) := by
  unfold regularizedEvenThetaProfile signedEvenThetaProfile signedEvenThetaGauge
  exact ((contDiff_riemannKernelReal.mul (contDiff_translateSpan _ _ _)).mul
    (contDiff_smoothPlateau c)).add (contDiff_const.sub (contDiff_smoothPlateau c))

/-- **Even-sector signed certificate in a window-positive signed theta gauge.** Whenever
`signedEvenThetaProfile b α₀ > 0` on `[-(c + 1), c + 1]` (`c ≥ 0`), even-sector nonnegativity on
`[-c, c]` is unconditionally equivalent to nonnegativity of the signed Dirichlet form with retained
pole variance plus the pole-charge term `2(coshCharge ω_{b, α₀}^+ (-c, c) - α₀/2) ∫ u² M^+ cosh`. -/
theorem even_nonneg_iff_signedEvenThetaGauge {c b α₀ : ℝ} (hc : 0 ≤ c)
    (hpos : ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn c F → 0 ≤ weilQuad F) ↔
      ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        0 ≤ signedJumpEnergy (signedEvenThetaProfile b α₀) u -
          2 * chargeVariance
            (fun x => signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) (Ioo (-c) c) u +
          2 * (coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2) *
            ∫ x, u x ^ 2 * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) := by
  have hM_diff : ContDiff ℝ 2 (signedEvenThetaProfile b α₀) :=
    contDiff_riemannKernelReal.mul (contDiff_translateSpan _ _ _)
  constructor
  · intro heven u hu hue huc
    have hucs := hasCompactSupport_of_supportedIn huc
    set F := phiDoobTest fun y => signedEvenThetaGauge b α₀ y * u y
    have hF_eq : ∀ x, F x = signedEvenThetaProfile b α₀ x * u x := fun x => by
      simp only [F, signedEvenThetaProfile, phiDoobTest, ← mul_assoc]
    have hF_diff : ContDiff ℝ 2 F := by
      rw [show F = fun x => signedEvenThetaProfile b α₀ x * u x from funext hF_eq]
      exact hM_diff.mul hu
    have hF_even : ∀ x, F (-x) = F x := fun x => by
      rw [hF_eq, hF_eq, signedEvenThetaProfile_neg, hue]
    have hF_supp : SupportedIn c F := fun x hx => by
      rw [hF_eq, huc x hx, mul_zero]
    have hF_cs := hasCompactSupport_of_supportedIn hF_supp
    have hnn := heven F hF_diff hF_even hF_supp
    rw [← fullZeroForm_eq_weilQuad_of_cont hF_diff.continuous hF_cs,
      fullZeroForm_signedEvenTheta_window hc b α₀ hu hucs hue] at hnn
    exact hnn
  · intro hcert F hF hFe hFc
    set u : ℝ → ℝ := fun x => F x / regularizedEvenThetaProfile c b α₀ x
    have hu_diff : ContDiff ℝ 2 u :=
      hF.div (contDiff_regularizedEvenThetaProfile c b α₀)
        fun x => (regularizedEvenThetaProfile_pos hpos x).ne'
    have hu_even : ∀ x, u (-x) = u x := fun x => by
      dsimp only [u]; rw [hFe x, regularizedEvenThetaProfile_neg]
    have hu_supp : SupportedIn c u := fun x hx => by
      dsimp only [u]; rw [hFc x hx, zero_div]
    have hu_cs := hasCompactSupport_of_supportedIn hu_supp
    have hF_cs := hasCompactSupport_of_supportedIn hFc
    have hphi : (phiDoobTest fun y => signedEvenThetaGauge b α₀ y * u y) = F := funext fun x => by
      simp only [phiDoobTest, u, ← mul_assoc]
      change signedEvenThetaProfile b α₀ x * (F x / regularizedEvenThetaProfile c b α₀ x) = F x
      by_cases hx : |x| ≤ c
      · rw [regularizedEvenThetaProfile_eq_of_abs_le hx]
        exact mul_div_cancel₀ (F x)
          (hpos x (abs_le.mp (hx.trans (by linarith)))).ne'
      · rw [hFc x (not_le.mp hx), zero_div, mul_zero]
    have hineq := hcert u hu_diff hu_even hu_supp
    have hid := fullZeroForm_signedEvenTheta_window hc b α₀ hu_diff hu_cs hu_even
    rw [hphi, fullZeroForm_eq_weilQuad_of_cont hF.continuous hF_cs] at hid
    linarith

/-- **Neutral signed even theta-gauge specialization (`α₀ = neutralEvenThetaParam b c`).** At the
neutral parameter `α₀^*(b, c)`, the outside cosh deficit vanishes identically, reducing even-sector
window positivity to `2 V_c^{(-c, c)}(u) ≤ J_{M^+}(u)` with zero pole-charge remainder. -/
theorem even_nonneg_iff_neutralSignedEvenThetaGauge {c : ℝ} (hc : 0 < c) {b : ℝ}
    (hpos : ∀ α₀ : ℝ, 0 ≤ α₀ → ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn c F → 0 ≤ weilQuad F) ↔
      ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        2 * chargeVariance
          (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
          (Ioo (-c) c) u ≤
          signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c)) u := by
  have hden := groundState_outsideCoshDeficit_pos hc.le
  have hnum_nn : 0 ≤ coshCharge (signedEvenThetaGauge b 0) (Ioo (-c) c) := by
    unfold coshCharge
    refine setIntegral_nonneg measurableSet_Ioo fun x hx => mul_nonneg ?_ (Real.cosh_pos _).le
    exact (hpos 0 le_rfl x ⟨by linarith [hx.1], by linarith [hx.2]⟩).le
  have hα_nn : 0 ≤ neutralEvenThetaParam b c := div_nonneg hnum_nn hden.le
  have hzero : coshCharge (signedEvenThetaGauge b (neutralEvenThetaParam b c)) (Ioo (-c) c) -
      neutralEvenThetaParam b c / 2 = 0 := by
    rw [coshCharge_signedEvenTheta_sub_half]
    unfold neutralEvenThetaParam
    rw [div_mul_cancel₀ _ hden.ne', sub_self]
  rw [even_nonneg_iff_signedEvenThetaGauge hc.le (hpos _ hα_nn)]
  refine forall_congr' fun u => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  rw [hzero]
  constructor <;> intro h <;> linarith

/-- **Exact reflection-pair representation in the signed line-exact theta-gauge family.** For every
centre `m ∈ ℝ`, half-width `c > 0`, and collar bump `f ∈ C²_c(ℝ)` supported in `[m - c, m]`:
1. `orderedCoupling f (collarReflect m f)` equals `collarHankel m f` minus the finite collective
   sliver sum over `2 ≤ n ≤ ⌊e^{2c}⌋₊`;
2. `W(f) - |𝒞_m(f)| = (1/2) min(W(G_+), W(G_-))`;
3. `W(G_+)` is expressed directly in `signedEvenThetaGauge b α₀` (`0 ≤ α₀ ≤ α₀^*(b, c)`) as
   `J_{M^+}(u_+) - 2 V_c^{(-c, c)}(u_+) + 2 τ_+ ∫ u_+² M^+ cosh` with `τ_+ ≥ 0`;
4. whenever `f` vanishes on `[m - ε, m]` (`ε > 0`), `W(G_-)` is expressed directly in
   `shiftedGroundState a` (`a > 0`) as `2 S_a(u_-) - D_a(u_-) + 8 V_s^{(0, c)}(u_-) +
   8 outsideCharge a c ∫_{x > 0} u_-² m_a sinh` with `outsideCharge a c > 0`. -/
theorem reflectionPair_signedThetaGauge_representation {m c a : ℝ} (hc : 0 < c) (ha : 0 < a)
    {b α₀ : ℝ}
    (hbpos : ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x)
    (hτ : 0 ≤ coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hm : ∀ u, m < u → f u = 0)
    (hleft : ∀ u, u < m - c → f u = 0) :
    orderedCoupling f (collarReflect m f) =
        collarHankel m f -
          ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * c)⌋₊,
            vonMangoldtAtom n * selfConv f (2 * m - Real.log n) ∧
      weilQuad f - |orderedCoupling f (collarReflect m f)| =
        (1 / 2) * min (weilQuad (reflectionEvenProfile m f))
          (weilQuad (reflectionOddProfile m f)) ∧
      (∃ u_pos : ℝ → ℝ, ContDiff ℝ 2 u_pos ∧ (∀ x, u_pos (-x) = u_pos x) ∧
        SupportedIn c u_pos ∧
        weilQuad (reflectionEvenProfile m f) =
          signedJumpEnergy (signedEvenThetaProfile b α₀) u_pos -
            2 * chargeVariance
              (fun x => signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) (Ioo (-c) c) u_pos +
            2 * (coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2) *
              ∫ x, u_pos x ^ 2 * (signedEvenThetaProfile b α₀ x * Real.cosh (x / 2)) ∧
        0 ≤ 2 * (coshCharge (signedEvenThetaGauge b α₀) (Ioo (-c) c) - α₀ / 2)) ∧
      (∀ ε : ℝ, 0 < ε → (∀ u, m - ε ≤ u → f u = 0) →
        ∃ u_neg : ℝ → ℝ, ContDiff ℝ 2 u_neg ∧ (∀ x, u_neg (-x) = u_neg x) ∧
          SupportedIn c u_neg ∧
          weilQuad (reflectionOddProfile m f) =
            2 * sameSideEnergy (shiftedGroundState a) u_neg -
                reflectedDifferenceEnergy (shiftedGroundState a) u_neg +
              8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
                  (∫ x in Ioi (0 : ℝ), u_neg x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
                (∫ x in Ioi (0 : ℝ), u_neg x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
              8 * outsideCharge a c *
                ∫ x in Ioi (0 : ℝ), u_neg x ^ 2 * shiftDifference a x * Real.sinh (x / 2) ∧
          0 < 8 * outsideCharge a c) := by
  have hfc := hasCompactSupport_of_collarWindow hm hleft
  refine ⟨orderedCoupling_collarReflect_eq_finsetSum hc.le hf hm hleft,
    weilQuad_sub_abs_orderedCoupling_eq_half_min hf hfc hm, ?_, ?_⟩
  · set Gp := reflectionEvenProfile m f
    have hGp_diff := contDiff_reflectionEvenProfile (m := m) hf
    have hGp_supp := supportedIn_reflectionEvenProfile hc.le hm hleft
    have hGp_cs := hasCompactSupport_of_supportedIn hGp_supp
    set u_pos : ℝ → ℝ := fun x => Gp x / regularizedEvenThetaProfile c b α₀ x
    have hu_diff : ContDiff ℝ 2 u_pos :=
      hGp_diff.div (contDiff_regularizedEvenThetaProfile c b α₀)
        fun x => (regularizedEvenThetaProfile_pos hbpos x).ne'
    have hu_even : ∀ x, u_pos (-x) = u_pos x := fun x => by
      dsimp only [u_pos, Gp]; rw [reflectionEvenProfile_neg, regularizedEvenThetaProfile_neg]
    have hu_supp : SupportedIn c u_pos := fun x hx => by
      dsimp only [u_pos, Gp]; rw [hGp_supp x hx, zero_div]
    have hu_cs := hasCompactSupport_of_supportedIn hu_supp
    have hphi : (phiDoobTest fun y => signedEvenThetaGauge b α₀ y * u_pos y) = Gp :=
      funext fun x => by
        simp only [phiDoobTest, u_pos, ← mul_assoc]
        change signedEvenThetaProfile b α₀ x *
          (Gp x / regularizedEvenThetaProfile c b α₀ x) = Gp x
        by_cases hx : |x| ≤ c
        · rw [regularizedEvenThetaProfile_eq_of_abs_le hx]
          exact mul_div_cancel₀ (Gp x)
            (hbpos x (abs_le.mp (hx.trans (by linarith)))).ne'
        · dsimp only [Gp]; rw [hGp_supp x (not_le.mp hx), zero_div, mul_zero]
    have hid := fullZeroForm_signedEvenTheta_window hc.le b α₀ hu_diff hu_cs hu_even
    rw [hphi, fullZeroForm_eq_weilQuad_of_cont hGp_diff.continuous hGp_cs] at hid
    exact ⟨u_pos, hu_diff, hu_even, hu_supp, hid, by linarith⟩
  · intro ε hε hgap
    set Gm := reflectionOddProfile m f
    have hGm_diff := contDiff_reflectionOddProfile (m := m) hf
    have hGm_supp := supportedIn_reflectionOddProfile hc.le hm hleft
    have hGm_cs := hasCompactSupport_of_supportedIn hGm_supp
    have hGm_zero : ∀ x, |x| ≤ ε → Gm x = 0 := fun x hx => by
      unfold Gm reflectionOddProfile
      obtain ⟨h1, h2⟩ := abs_le.mp hx
      rw [hgap (x + m) (by linarith), hgap (-x + m) (by linarith), sub_zero]
    have hM_diff : ContDiff ℝ 2 (shiftDifference a) := by
      rw [show shiftDifference a = fun x => riemannKernelReal x * shiftedGroundState a x from
        funext fun x => (riemannKernelReal_mul_shiftedGroundState a x).symm]
      exact contDiff_riemannKernelReal.mul (contDiff_shiftedGroundState a)
    have hMnz : ∀ x ∈ Ioo (-(c + 1)) (c + 1), x ≠ 0 → shiftDifference a x ≠ 0 :=
      fun x _ hx0 => by
        rcases lt_trichotomy x 0 with hlt | rfl | hgt
        · have hp := shiftDifference_pos ha (neg_pos.mpr hlt)
          rw [shiftDifference_neg] at hp; linarith
        · exact absurd rfl hx0
        · exact (shiftDifference_pos ha hgt).ne'
    have hc1 : c < c + 1 := by linarith
    set u_neg := windowGaugeQuotient ε c (c + 1) (shiftDifference a) Gm
    have hu_diff : ContDiff ℝ 2 u_neg :=
      contDiff_windowGaugeQuotient hε hc1 hM_diff hMnz hGm_diff hGm_zero hGm_supp
    have hu_even : ∀ x, u_neg (-x) = u_neg x :=
      windowGaugeQuotient_even hc1 (fun x _ => shiftDifference_neg a x)
        (reflectionOddProfile_neg m f)
    have hu_supp : SupportedIn c u_neg := fun x hx => by
      unfold u_neg windowGaugeQuotient
      split_ifs
      · rfl
      · dsimp only [Gm]; rw [hGm_supp x hx, zero_div]
    have hu_cs := hasCompactSupport_of_supportedIn hu_supp
    have hphi : (phiDoobTest fun y => shiftedGroundState a y * u_neg y) = Gm := funext fun x => by
      simp only [phiDoobTest, ← mul_assoc, riemannKernelReal_mul_shiftedGroundState]
      exact windowGaugeQuotient_mul hε hc1 hMnz hGm_zero hGm_supp x
    have hid := fullZeroForm_shiftedGroundState_window ha c hu_diff hu_cs hu_even
    rw [hphi, fullZeroForm_eq_weilQuad_of_cont hGm_diff.continuous hGm_cs] at hid
    exact ⟨u_neg, hu_diff, hu_even, hu_supp, hid, mul_pos (by norm_num) (outsideCharge_pos ha hc)⟩

/-! ### 4. Unconditional super-`log 2` floor and global equivalence -/

/-- Twice `enlargedWeilFloorAperture` strictly exceeds `log 2`: at `c = enlargedWeilFloorAperture`,
the prime `p = 2` already acts inside the collective sliver sum. -/
theorem log_two_lt_two_mul_enlargedWeilFloorAperture :
    Real.log 2 < 2 * enlargedWeilFloorAperture := by
  have hlog := Real.log_two_lt_d9
  have hbound := enlargedWeilFloorAperture_bounds.1
  linarith

/-- On a collar window `[m - c, m]` (`0 ≤ c`), both reflection profiles `G_±` have `L²` norm square
equal to `2 ∫ f²`, since `f(u + m)` and `f(-u + m)` have disjoint open supports. -/
theorem integral_reflectionProfile_sq {m c : ℝ} (hc : 0 ≤ c) {f : ℝ → ℝ}
    (hf : Continuous f) (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    (∫ u, reflectionEvenProfile m f u ^ 2) = 2 * (∫ u, f u ^ 2) ∧
      (∫ u, reflectionOddProfile m f u ^ 2) = 2 * (∫ u, f u ^ 2) := by
  have hf₀_cont : Continuous fun u => f (u + m) :=
    hf.comp (continuous_id.add continuous_const)
  have hf₀_right : ∀ u, 0 < u → f (u + m) = 0 := fun u hu => hm (u + m) (by linarith)
  have hf₀_left : ∀ u, u < -c → f (u + m) = 0 := fun u hu => hleft (u + m) (by linarith)
  obtain ⟨hf₀_nonpos, _⟩ := halfWindow_eq_zero_of_nonpos_or_le hc hf₀_cont hf₀_right hf₀_left
  have hcross : ∀ u, f (u + m) * f (-u + m) = 0 := fun u => by
    rcases le_or_gt 0 u with hu | hu
    · rw [hf₀_nonpos u hu, zero_mul]
    · rw [hf₀_right (-u) (by linarith), mul_zero]
  have hi_pos : Integrable fun u => f (u + m) ^ 2 :=
    Continuous.integrable_of_hasCompactSupport (hf₀_cont.pow 2)
      (hasCompactSupport_of_collarWindow (m := 0) (c := c) (f := fun u => f (u + m) ^ 2)
        (fun u hu => by rw [hf₀_right u hu, sq, mul_zero])
        (fun u hu => by rw [hf₀_left u (by linarith), sq, mul_zero]))
  have hi_neg : Integrable fun u => f (-u + m) ^ 2 :=
    Continuous.integrable_of_hasCompactSupport
      ((hf.comp (continuous_neg.add continuous_const)).pow 2)
      (hasCompactSupport_of_collarWindow (m := c) (c := c) (f := fun u => f (-u + m) ^ 2)
        (fun u hu => by rw [hleft (-u + m) (by linarith), sq, mul_zero])
        (fun u hu => by rw [hm (-u + m) (by linarith), sq, mul_zero]))
  have hint_shift : (∫ u, f (u + m) ^ 2) = ∫ u, f u ^ 2 :=
    integral_add_right_eq_self (fun u => f u ^ 2) m
  have hint_neg : (∫ u, f (-u + m) ^ 2) = ∫ u, f (u + m) ^ 2 :=
    integral_neg_eq_self (fun u => f (u + m) ^ 2) volume
  have hpt_even : (fun u => reflectionEvenProfile m f u ^ 2) =
      fun u => f (u + m) ^ 2 + f (-u + m) ^ 2 := funext fun u => by
    dsimp only [reflectionEvenProfile]
    linear_combination 2 * hcross u
  have hpt_odd : (fun u => reflectionOddProfile m f u ^ 2) =
      fun u => f (u + m) ^ 2 + f (-u + m) ^ 2 := funext fun u => by
    dsimp only [reflectionOddProfile]
    linear_combination -2 * hcross u
  refine ⟨?_, ?_⟩
  · rw [hpt_even, integral_add hi_pos hi_neg, hint_neg, hint_shift]; ring
  · rw [hpt_odd, integral_add hi_pos hi_neg, hint_neg, hint_shift]; ring

/-- **Unconditional super-`log 2` collective sliver floor.** For every centre `m ∈ ℝ`, every
half-width `0 < c ≤ enlargedWeilFloorAperture`, and every `f ∈ C²_c(ℝ)` supported in `[m - c, m]`,
`W(f) - |𝒞_m(f)| ≥ (1/8000) ∫ f²`. -/
theorem weilQuad_sub_abs_orderedCoupling_ge_of_le_enlargedWeilFloorAperture {m c : ℝ}
    (hc0 : 0 < c) (hc : c ≤ enlargedWeilFloorAperture) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hm : ∀ u, m < u → f u = 0) (hleft : ∀ u, u < m - c → f u = 0) :
    (1 / 8000) * (∫ u, f u ^ 2) ≤ weilQuad f - |orderedCoupling f (collarReflect m f)| := by
  have hfc := hasCompactSupport_of_collarWindow hm hleft
  rw [weilQuad_sub_abs_orderedCoupling_eq_half_min hf hfc hm]
  have hGp_diff := contDiff_reflectionEvenProfile (m := m) hf
  have hGm_diff := contDiff_reflectionOddProfile (m := m) hf
  have hGp_supp := supportedIn_reflectionEvenProfile hc0.le hm hleft
  have hGm_supp := supportedIn_reflectionOddProfile hc0.le hm hleft
  have hGp_cs := hasCompactSupport_of_supportedIn hGp_supp
  have hGm_cs := hasCompactSupport_of_supportedIn hGm_supp
  have hGp_floor := fullZeroForm_ge_of_support_le_enlargedWeilFloorAperture hGp_diff hGp_cs
    fun u hu => hGp_supp u (hc.trans_lt hu)
  have hGm_floor := fullZeroForm_ge_of_support_le_enlargedWeilFloorAperture hGm_diff hGm_cs
    fun u hu => hGm_supp u (hc.trans_lt hu)
  rw [fullZeroForm_eq_weilQuad_of_cont hGp_diff.continuous hGp_cs] at hGp_floor
  rw [fullZeroForm_eq_weilQuad_of_cont hGm_diff.continuous hGm_cs] at hGm_floor
  obtain ⟨hGp_L2, hGm_L2⟩ := integral_reflectionProfile_sq hc0.le hf.continuous hm hleft
  rw [hGp_L2] at hGp_floor
  rw [hGm_L2] at hGm_floor
  have hmin : (1 / 4000) * (∫ u, f u ^ 2) ≤
      min (weilQuad (reflectionEvenProfile m f)) (weilQuad (reflectionOddProfile m f)) :=
    le_min (by linarith only [hGp_floor]) (by linarith only [hGm_floor])
  linarith only [hmin]

/-- **Global equivalence of collective sliver payment across all reflection pairs.** For every
odd shift `a > 0`, the following are unconditionally equivalent:
1. on every collar window `[m - c, m]` (`m ∈ ℝ`, `c > 0`), `0 ≤ W(f) - |𝒞_m(f)|`;
2. on every window `(-c, c)` (`c > 0`), there exists `b > 0` such that `M_{b, α₀}^+ > 0` on
   `[-(c + 1), c + 1]` (`0 ≤ α₀`), `α₀^*(b, c) > 0`, and both the neutral signed even theta-gauge
   form `J_{M^+}(u) - 2 V_c^{(-c, c)}(u)` and the odd shifted ground-state form of `ω_a` are
   nonnegative on all even `u ∈ C²_c` supported in `[-c, c]`;
3. `∀ c > 0, ZetaWindowPositive c`;
4. `RiemannHypothesis`. -/
theorem collectiveSliverPayment_global_equivalence {a : ℝ} (ha : 0 < a) :
    ((∀ m c : ℝ, 0 < c → ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
        (∀ u, m < u → f u = 0) → (∀ u, u < m - c → f u = 0) →
        0 ≤ weilQuad f - |orderedCoupling f (collarReflect m f)|) ↔
      (∀ c : ℝ, 0 < c → ∃ b : ℝ, 0 < b ∧ 0 < neutralEvenThetaParam b c ∧
        (∀ α₀ : ℝ, 0 ≤ α₀ → ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          2 * chargeVariance
            (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
            (Ioo (-c) c) u ≤
            signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c)) u) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          0 ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
              reflectedDifferenceEnergy (shiftedGroundState a) u +
            8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
                (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
              (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
            8 * outsideCharge a c *
              ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)))) ∧
    ((∀ c : ℝ, 0 < c → ∃ b : ℝ, 0 < b ∧ 0 < neutralEvenThetaParam b c ∧
        (∀ α₀ : ℝ, 0 ≤ α₀ → ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          2 * chargeVariance
            (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
            (Ioo (-c) c) u ≤
            signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c)) u) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          0 ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
              reflectedDifferenceEnergy (shiftedGroundState a) u +
            8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
                (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
              (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
            8 * outsideCharge a c *
              ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) ↔
      (∀ c : ℝ, 0 < c → ZetaWindowPositive c)) ∧
    ((∀ c : ℝ, 0 < c → ZetaWindowPositive c) ↔ RiemannHypothesis) := by
  have h23 :
      (∀ c : ℝ, 0 < c → ∃ b : ℝ, 0 < b ∧ 0 < neutralEvenThetaParam b c ∧
        (∀ α₀ : ℝ, 0 ≤ α₀ → ∀ x ∈ Icc (-(c + 1)) (c + 1), 0 < signedEvenThetaProfile b α₀ x) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          2 * chargeVariance
            (fun x => signedEvenThetaProfile b (neutralEvenThetaParam b c) x * Real.cosh (x / 2))
            (Ioo (-c) c) u ≤
            signedJumpEnergy (signedEvenThetaProfile b (neutralEvenThetaParam b c)) u) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
          0 ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
              reflectedDifferenceEnergy (shiftedGroundState a) u +
            8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
                (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
              (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
            8 * outsideCharge a c *
              ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) ↔
      (∀ c : ℝ, 0 < c → ZetaWindowPositive c) := by
    refine forall_congr' fun c => imp_congr_right fun hc => ?_
    rw [zetaWindowPositive_iff_even_and_odd_sectors c,
      odd_nonneg_iff_retainedVariance_shiftedGroundState ha hc]
    constructor
    · rintro ⟨b, _, _, hbpos, hev, hod⟩
      exact ⟨(even_nonneg_iff_neutralSignedEvenThetaGauge hc hbpos).mpr hev, hod⟩
    · rintro ⟨hev, hod⟩
      obtain ⟨b, hb0, hα0, hbpos, _, _⟩ := exists_signedEvenThetaGauge_pos_and_nonneg_poleCharge hc
      exact ⟨b, hb0, hα0, hbpos,
        (even_nonneg_iff_neutralSignedEvenThetaGauge hc hbpos).mp hev, hod⟩
  have h13 :
      (∀ m c : ℝ, 0 < c → ∀ f : ℝ → ℝ, ContDiff ℝ 2 f →
        (∀ u, m < u → f u = 0) → (∀ u, u < m - c → f u = 0) →
        0 ≤ weilQuad f - |orderedCoupling f (collarReflect m f)|) ↔
      (∀ c : ℝ, 0 < c → ZetaWindowPositive c) := by
    constructor
    · intro hall c hc
      rw [zetaWindowPositive_iff_abs_centreCoupling_le hc]
      intro f hf h0 hfc
      have hm0 : ∀ u, (0 : ℝ) < u → f u = 0 := h0
      have hleft0 : ∀ u, u < 0 - c → f u = 0 := fun u hu => hfc u (by linarith)
      have hfcs := hasCompactSupport_of_collarWindow hm0 hleft0
      have hnn := hall 0 c hc f hf hm0 hleft0
      have hcc : orderedCoupling f (collarReflect 0 f) = centreCoupling f := by
        rw [orderedCoupling_collarReflect hf hfcs hm0]
        rfl
      rw [hcc] at hnn
      linarith
    · intro hzw m c hc f hf hm hleft
      have hfc := hasCompactSupport_of_collarWindow hm hleft
      rw [weilQuad_sub_abs_orderedCoupling_eq_half_min hf hfc hm]
      obtain ⟨hev, hod⟩ := (zetaWindowPositive_iff_even_and_odd_sectors c).mp (hzw c hc)
      have h1 := hev (reflectionEvenProfile m f) (contDiff_reflectionEvenProfile hf)
        (reflectionEvenProfile_neg m f) (supportedIn_reflectionEvenProfile hc.le hm hleft)
      have h2 := hod (reflectionOddProfile m f) (contDiff_reflectionOddProfile hf)
        (reflectionOddProfile_neg m f) (supportedIn_reflectionOddProfile hc.le hm hleft)
      have hmin : 0 ≤ min (weilQuad (reflectionEvenProfile m f))
          (weilQuad (reflectionOddProfile m f)) := le_min h1 h2
      linarith
  exact ⟨h13.trans h23.symm, h23, riemannHypothesis_iff_forall_zetaWindowPositive.symm⟩

#print axioms orderedCoupling_collarReflect_eq_finsetSum
#print axioms weilQuad_sub_abs_orderedCoupling_eq_half_min
#print axioms no_windowIndependent_evenThetaGauge_nonneg_poleCharge
#print axioms exists_signedEvenThetaGauge_pos_and_nonneg_poleCharge
#print axioms even_nonneg_iff_signedEvenThetaGauge
#print axioms reflectionPair_signedThetaGauge_representation
#print axioms weilQuad_sub_abs_orderedCoupling_ge_of_le_enlargedWeilFloorAperture
#print axioms collectiveSliverPayment_global_equivalence

end GaloisForLFunctions.SignedWindowCriticality

end
