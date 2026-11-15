import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheMarginOfTheWindowMatricesSinksAtTheRateOfTheWidth

/-!
# Weil's form is continuous in the logarithmic energy

The bound `|W(u, u)| ≤ 160 · L(a, w) (E(u) + ∫|u|²)` makes the logarithmic energy norm
`E(u) + ∫|u|²` the form domain of Weil's form on sources of aperture `a`. This module proves the
continuity that goes with it, with no hypothesis on the zeros:

* **Continuity** (`abs_sourceQuadratic_sub_le`): for smooth sources `u₁, u₂` of aperture `a`, the
  difference `d = u₁ − u₂` and every `s > 0`,
  `|W(u₁, u₁) − W(u₂, u₂)| ≤ 160 · L(a, w) ((1 + 1/s)(E(d) + ∫|d|²) + s (E(u₂) + ∫|u₂|²))`.

The zero term of a source is `Φ(−z) conj Φ(−z̄)` and the transform is additive, so the difference
of two zero terms is `Φ_d conj Φ₂' + Φ₂ conj Φ_d' + Φ_d conj Φ_d'`. The cross terms are split with
the weight `s`, and the samples of `d` and of `u₂` at the zero copies are bounded by their
logarithmic energies.

* **Packets** (`abs_packetForm_sub_le`): the same estimate for Weil's form `𝔚_Q` of two bounded
  real packets supported in a common interval of length below `2A` and below `log(Q + 1)`, with
  the logarithmic energy in the coordinate of the autocorrelation. Smoothing lowers the energy of
  the difference and of the second packet at every displacement, and the forms of the smoothed
  packets converge.

The estimate transfers a statement about Weil's form from a packet to every approximation of it
that is close in the logarithmic energy, at a cost that is polynomial in the aperture.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.HTGeometry _root_.Zeta23 _root_.RHTower _root_.RHTower.CCMParityQuartet
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-- The transform of a difference of continuous compactly supported functions. -/
theorem testTransform_sub_fun {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (z : ℂ) :
    testTransform (fun x => f x - g x) z = testTransform f z - testTransform g z := by
  unfold testTransform
  rw [← integral_sub (integrable_testTransform_integrand hf hfc z)
    (integrable_testTransform_integrand hg hgc z)]
  refine integral_congr_ae (Eventually.of_forall fun L => ?_)
  show (f L - g L) * Complex.exp (Complex.I * z * (L : ℂ)) =
    f L * Complex.exp (Complex.I * z * (L : ℂ)) - g L * Complex.exp (Complex.I * z * (L : ℂ))
  ring

/-- `x y ≤ y²/(2s) + s x²/2`. -/
theorem mul_le_weighted {s : ℝ} (hs : 0 < s) (x y : ℝ) :
    x * y ≤ 1 / s * y ^ 2 / 2 + s * x ^ 2 / 2 := by
  have h : 0 ≤ (s * x - y) ^ 2 / (2 * s) := div_nonneg (sq_nonneg _) (by positivity)
  have e : 1 / s * y ^ 2 / 2 + s * x ^ 2 / 2 - x * y = (s * x - y) ^ 2 / (2 * s) := by
    field_simp
    ring
  linarith

/-- **The zero terms of two functions differ by the cross terms of their samples**: for `s > 0`,
`|Re T_q(f) − Re T_q(g)| ≤ (1 + 1/s) S_q(f − g) + s S_q(g)`, where `T_q` is the zero term and
`S_q` the sample at the zero copy `q`. -/
theorem abs_re_zeroSumTerm_sub_le {f g : ℝ → ℂ}
    (hlin : ∀ z, testTransform f z = testTransform g z + testTransform (fun x => f x - g x) z)
    {s : ℝ} (hs : 0 < s) (q : XiZeroCopy) :
    |(zeroSumTerm f (xiSpectralPoint q)).re - (zeroSumTerm g (xiSpectralPoint q)).re| ≤
      (1 + 1 / s) * zeroSample (fun x => f x - g x) q + s * zeroSample g q := by
  obtain ⟨P, hP⟩ : ∃ P, P = testTransform g (-xiSpectralPoint q) := ⟨_, rfl⟩
  obtain ⟨P', hP'⟩ : ∃ P', P' = testTransform g (-(starRingEnd ℂ) (xiSpectralPoint q)) :=
    ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = testTransform (fun x => f x - g x) (-xiSpectralPoint q) := ⟨_, rfl⟩
  obtain ⟨D', hD'⟩ : ∃ D', D' =
      testTransform (fun x => f x - g x) (-(starRingEnd ℂ) (xiSpectralPoint q)) := ⟨_, rfl⟩
  have hdiff : zeroSumTerm f (xiSpectralPoint q) - zeroSumTerm g (xiSpectralPoint q) =
      P * (starRingEnd ℂ) D' + D * (starRingEnd ℂ) P' + D * (starRingEnd ℂ) D' := by
    unfold CCMParityQuartet.zeroSumTerm
    rw [hlin (-xiSpectralPoint q), hlin (-(starRingEnd ℂ) (xiSpectralPoint q)), ← hP, ← hP',
      ← hD, ← hD', map_add]
    ring
  have hre : |(zeroSumTerm f (xiSpectralPoint q)).re - (zeroSumTerm g (xiSpectralPoint q)).re| ≤
      ‖P‖ * ‖D'‖ + ‖D‖ * ‖P'‖ + ‖D‖ * ‖D'‖ := by
    rw [← Complex.sub_re, hdiff]
    refine (Complex.abs_re_le_norm _).trans (norm_add₃_le.trans (le_of_eq ?_))
    simp only [norm_mul, Complex.norm_conj]
  have h1 := mul_le_weighted hs ‖P‖ ‖D'‖
  have h2 := mul_le_weighted hs ‖P'‖ ‖D‖
  have h3 : ‖D‖ * ‖D'‖ ≤ (‖D‖ ^ 2 + ‖D'‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖D‖ - ‖D'‖)]
  have e : (1 + 1 / s) * ((‖D‖ ^ 2 + ‖D'‖ ^ 2) / 2) + s * ((‖P‖ ^ 2 + ‖P'‖ ^ 2) / 2) =
      (1 / s * ‖D'‖ ^ 2 / 2 + s * ‖P‖ ^ 2 / 2) + (1 / s * ‖D‖ ^ 2 / 2 + s * ‖P'‖ ^ 2 / 2) +
        (‖D‖ ^ 2 + ‖D'‖ ^ 2) / 2 := by ring
  unfold zeroSample
  rw [← hP, ← hP', ← hD, ← hD', e]
  linarith [mul_comm ‖D‖ ‖P'‖]

/-- A smooth source is Lipschitz. -/
theorem exists_lipschitzWith_source {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) : ∃ K : NNReal, LipschitzWith K (u : ℝ → ℂ) := by
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℂ) := u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  exact hu2.lipschitzWith_of_hasCompactSupport u.hasCompactSupport (by norm_num)

/-- The difference of two smooth sources is a source of the same aperture. -/
theorem intervalSource_sub {a : SuzukiPositiveAperture} (u₁ u₂ : CCMComplexSmoothInteriorSource a) :
    IntervalSource a.1 (fun x => u₁ x - u₂ x) where
  continuous := u₁.continuous.sub u₂.continuous
  hasCompactSupport :=
    HasCompactSupport.intro (isCompact_Icc (a := -a.1) (b := a.1)) fun x hx => by
      show u₁ x - u₂ x = 0
      rw [(smoothSource_intervalSource u₁).vanish x hx,
        (smoothSource_intervalSource u₂).vanish x hx, sub_zero]
  vanish := fun x hx => by
    show u₁ x - u₂ x = 0
    rw [(smoothSource_intervalSource u₁).vanish x hx,
      (smoothSource_intervalSource u₂).vanish x hx, sub_zero]

/-- The difference of two smooth sources is Lipschitz. -/
theorem exists_lipschitzWith_source_sub {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) :
    ∃ K : NNReal, LipschitzWith K (fun x => u₁ x - u₂ x) := by
  obtain ⟨K₁, hK₁⟩ := exists_lipschitzWith_source u₁
  obtain ⟨K₂, hK₂⟩ := exists_lipschitzWith_source u₂
  exact ⟨K₁ + K₂, hK₁.sub hK₂⟩

/-- The density of the logarithmic energy of a difference of smooth sources is integrable. -/
theorem intervalIntegrable_logEnergy_source_sub {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) :
    IntervalIntegrable
      (fun t => (∫ x, ‖(u₁ (x + t) - u₂ (x + t)) - (u₁ x - u₂ x)‖ ^ 2) / t) volume 0 1 := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_source_sub u₁ u₂
  have h := intervalIntegrable_logEnergy_of_lipschitz (f := fun x => u₁ x - u₂ x) a.2.le
    (intervalSource_sub u₁ u₂) hK
  exact h

/-- The samples of a difference of smooth sources at the zero copies are summable, with sum
bounded by the logarithmic energy norm of the difference. -/
theorem zeroSample_source_sub {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) :
    Summable (zeroSample (fun x => u₁ x - u₂ x)) ∧
      ∑' q, zeroSample (fun x => u₁ x - u₂ x) q ≤
        160 * (logSamplingConst a.1 zetaZeroWidth *
          (logEnergy (fun x => u₁ x - u₂ x) + ∫ x, ‖u₁ x - u₂ x‖ ^ 2)) := by
  have hId := intervalSource_sub u₁ u₂
  have hGd := intervalIntegrable_logEnergy_source_sub u₁ u₂
  exact ⟨summable_zeroSample a.2 hId hGd, tsum_zeroSample_le a.2 hId hGd⟩

/-- The difference of the forms of two smooth sources as a difference of sums over the zero
copies. -/
theorem sourceQuadratic_sub_eq_tsum {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u₁.toCCMFormVector -
        ccmRestrictedWeilSourceQuadratic a u₂.toCCMFormVector =
      ∑' q : XiZeroCopy, (zeroSumTerm u₁ (xiSpectralPoint q)).re -
        ∑' q : XiZeroCopy, (zeroSumTerm u₂ (xiSpectralPoint q)).re := by
  rw [sourceQuadratic_eq_re_tsum, sourceQuadratic_eq_re_tsum,
    Complex.re_tsum (CCMParityQuartet.summable_zeroSumTerm u₁),
    Complex.re_tsum (CCMParityQuartet.summable_zeroSumTerm u₂)]

/-- The zero terms of two smooth sources differ by the cross terms of their samples. -/
theorem abs_re_zeroSumTerm_source_sub_le {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) {s : ℝ} (hs : 0 < s) (q : XiZeroCopy) :
    |(zeroSumTerm u₁ (xiSpectralPoint q)).re - (zeroSumTerm u₂ (xiSpectralPoint q)).re| ≤
      (1 + 1 / s) * zeroSample (fun x => u₁ x - u₂ x) q + s * zeroSample u₂ q := by
  refine abs_re_zeroSumTerm_sub_le (f := u₁) (g := u₂) (fun z => ?_) hs q
  rw [testTransform_sub_fun u₁.continuous u₁.hasCompactSupport u₂.continuous
    u₂.hasCompactSupport z]
  ring

/-- Summation of a pointwise comparison of two real series against two nonnegative series. -/
theorem abs_tsum_sub_le_of_pointwise {ι : Type*} {T₁ T₂ S₁ S₂ : ι → ℝ} {c₁ c₂ B₁ B₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hT₁ : Summable T₁) (hT₂ : Summable T₂) (hS₁ : Summable S₁)
    (hS₂ : Summable S₂) (hB₁ : ∑' q, S₁ q ≤ B₁) (hB₂ : ∑' q, S₂ q ≤ B₂)
    (hpt : ∀ q, |T₁ q - T₂ q| ≤ c₁ * S₁ q + c₂ * S₂ q) :
    |∑' q, T₁ q - ∑' q, T₂ q| ≤ c₁ * B₁ + c₂ * B₂ := by
  have hb : Summable fun q => c₁ * S₁ q + c₂ * S₂ q := (hS₁.mul_left c₁).add (hS₂.mul_left c₂)
  have hsum : ∑' q, (c₁ * S₁ q + c₂ * S₂ q) ≤ c₁ * B₁ + c₂ * B₂ := by
    rw [(hS₁.mul_left c₁).tsum_add (hS₂.mul_left c₂), tsum_mul_left, tsum_mul_left]
    exact add_le_add (mul_le_mul_of_nonneg_left hB₁ hc₁) (mul_le_mul_of_nonneg_left hB₂ hc₂)
  have hd : Summable fun q => T₁ q - T₂ q := hT₁.sub hT₂
  rw [← hT₁.tsum_sub hT₂, abs_le]
  constructor
  · have h1 : ∑' q, -(c₁ * S₁ q + c₂ * S₂ q) ≤ ∑' q, (T₁ q - T₂ q) :=
      hb.neg.tsum_le_tsum (fun q => (abs_le.mp (hpt q)).1) hd
    rw [tsum_neg] at h1
    linarith
  · exact (hd.tsum_le_tsum (fun q => (abs_le.mp (hpt q)).2) hb).trans hsum

/-- The summation of a pointwise comparison, with both bounds of the form `160 κ E`. -/
theorem abs_tsum_sub_le_scaled {ι : Type*} {T₁ T₂ S₁ S₂ : ι → ℝ} {c₁ c₂ κ E₁ E₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hT₁ : Summable T₁) (hT₂ : Summable T₂) (hS₁ : Summable S₁)
    (hS₂ : Summable S₂) (hB₁ : ∑' q, S₁ q ≤ 160 * (κ * E₁))
    (hB₂ : ∑' q, S₂ q ≤ 160 * (κ * E₂))
    (hpt : ∀ q, |T₁ q - T₂ q| ≤ c₁ * S₁ q + c₂ * S₂ q) :
    |∑' q, T₁ q - ∑' q, T₂ q| ≤ 160 * (κ * (c₁ * E₁ + c₂ * E₂)) :=
  (abs_tsum_sub_le_of_pointwise hc₁ hc₂ hT₁ hT₂ hS₁ hS₂ hB₁ hB₂ hpt).trans
    (le_of_eq (by ring))

/-- The real parts of the zero terms of a smooth source are summable. -/
theorem summable_re_zeroSumTerm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Summable fun q : XiZeroCopy => (zeroSumTerm u (xiSpectralPoint q)).re := by
  have hsumm : Summable fun q : XiZeroCopy => zeroSumTerm u (xiSpectralPoint q) :=
    summable_zeroSumTerm u
  exact Complex.reCLM.summable hsumm

/-- The samples of a smooth source at the zero copies are summable, with sum bounded by its
logarithmic energy norm. -/
theorem zeroSample_source {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    Summable (zeroSample u) ∧
      ∑' q, zeroSample u q ≤
        160 * (logSamplingConst a.1 zetaZeroWidth * (logEnergy u + ∫ x, ‖u x‖ ^ 2)) := by
  have hI := smoothSource_intervalSource u
  have hG := intervalIntegrable_logEnergy_source u
  exact ⟨summable_zeroSample a.2 hI hG, tsum_zeroSample_le a.2 hI hG⟩

/-- The sums over the zero copies of two smooth sources differ by at most the logarithmic
energy norms of the difference and of the second source, weighted by `1 + 1/s` and `s`. -/
theorem abs_tsum_zeroSumTerm_sub_le {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) {s : ℝ} (hs : 0 < s) :
    |∑' q : XiZeroCopy, (zeroSumTerm u₁ (xiSpectralPoint q)).re -
        ∑' q : XiZeroCopy, (zeroSumTerm u₂ (xiSpectralPoint q)).re| ≤
      160 * (logSamplingConst a.1 zetaZeroWidth *
        ((1 + 1 / s) * (logEnergy (fun x => u₁ x - u₂ x) + ∫ x, ‖u₁ x - u₂ x‖ ^ 2) +
          s * (logEnergy u₂ + ∫ x, ‖u₂ x‖ ^ 2))) := by
  obtain ⟨hSd, hBd⟩ := zeroSample_source_sub u₁ u₂
  obtain ⟨hS₂, hB₂⟩ := zeroSample_source u₂
  have h1s : (0 : ℝ) ≤ 1 + 1 / s := add_nonneg zero_le_one (one_div_pos.mpr hs).le
  have h := abs_tsum_sub_le_scaled
    (T₁ := fun q : XiZeroCopy => (zeroSumTerm u₁ (xiSpectralPoint q)).re)
    (T₂ := fun q : XiZeroCopy => (zeroSumTerm u₂ (xiSpectralPoint q)).re)
    (S₁ := zeroSample (fun x => u₁ x - u₂ x)) (S₂ := zeroSample u₂)
    (c₁ := 1 + 1 / s) (c₂ := s) (κ := logSamplingConst a.1 zetaZeroWidth)
    (E₁ := logEnergy (fun x => u₁ x - u₂ x) + ∫ x, ‖u₁ x - u₂ x‖ ^ 2)
    (E₂ := logEnergy u₂ + ∫ x, ‖u₂ x‖ ^ 2)
    h1s hs.le (summable_re_zeroSumTerm u₁) (summable_re_zeroSumTerm u₂) hSd hS₂ hBd hB₂
    (abs_re_zeroSumTerm_source_sub_le u₁ u₂ hs)
  exact h

/-- **Weil's form is continuous in the logarithmic energy.** For smooth sources `u₁, u₂` of
aperture `a`, `d = u₁ − u₂` and `s > 0`,
`|W(u₁, u₁) − W(u₂, u₂)| ≤ 160 · L(a, w) ((1 + 1/s)(E(d) + ∫|d|²) + s (E(u₂) + ∫|u₂|²))` with `w`
the zero width. -/
theorem abs_sourceQuadratic_sub_le {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) {s : ℝ} (hs : 0 < s) :
    |ccmRestrictedWeilSourceQuadratic a u₁.toCCMFormVector -
        ccmRestrictedWeilSourceQuadratic a u₂.toCCMFormVector| ≤
      160 * (logSamplingConst a.1 zetaZeroWidth *
        ((1 + 1 / s) * (logEnergy (fun x => u₁ x - u₂ x) + ∫ x, ‖u₁ x - u₂ x‖ ^ 2) +
          s * (logEnergy u₂ + ∫ x, ‖u₂ x‖ ^ 2))) := by
  rw [sourceQuadratic_sub_eq_tsum u₁ u₂]
  exact abs_tsum_zeroSumTerm_sub_le u₁ u₂ hs

/-- The continuity for the Weil form of the zeros of `ζ`. -/
theorem abs_zetaZeroConfig_re_W_sub_le {a : SuzukiPositiveAperture}
    (u₁ u₂ : CCMComplexSmoothInteriorSource a) {s : ℝ} (hs : 0 < s) :
    |(zetaZeroConfig.W u₁ u₁).re - (zetaZeroConfig.W u₂ u₂).re| ≤
      160 * (logSamplingConst a.1 zetaZeroWidth *
        ((1 + 1 / s) * (logEnergy (fun x => u₁ x - u₂ x) + ∫ x, ‖u₁ x - u₂ x‖ ^ 2) +
          s * (logEnergy u₂ + ∫ x, ‖u₂ x‖ ^ 2))) := by
  rw [← ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil u₁,
    ← ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil u₂]
  exact abs_sourceQuadratic_sub_le u₁ u₂ hs

/-! ### Packets -/

/-- The zero sum of a smooth packet is Weil's form of its centred source. -/
theorem re_W_centredSource {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {l r : ℝ}
    (hGs : ∀ u, G u ≠ 0 → l ≤ u ∧ u ≤ r) {A : SuzukiPositiveAperture} (hA : r - l < 2 * A.1) :
    (zetaZeroConfig.W (centredSource hG hGs hA) (centredSource hG hGs hA)).re = zeroSum G :=
  zeroSum_translate (hG.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)))
    (hasCompactSupport_of_support_le hGs) (-((l + r) / 2))

/-- The mass of the centred source of a packet. -/
theorem integral_norm_sq_centredSource {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {l r : ℝ}
    (hGs : ∀ u, G u ≠ 0 → l ≤ u ∧ u ≤ r) {A : SuzukiPositiveAperture} (hA : r - l < 2 * A.1) :
    (∫ x, ‖centredSource hG hGs hA x‖ ^ 2) = packetAutocorr G 0 := by
  show (∫ x, ‖((G (x - -((l + r) / 2)) : ℝ) : ℂ)‖ ^ 2) = packetAutocorr G 0
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [integral_sub_right_eq_self (fun u => G u ^ 2) (-((l + r) / 2))]
  simp only [packetAutocorr, add_zero, pow_two]

/-- The logarithmic energy of the centred source of a packet. -/
theorem logEnergy_centredSource {G : ℝ → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {M l r : ℝ}
    (hGb : ∀ u, |G u| ≤ M) (hGs : ∀ u, G u ≠ 0 → l ≤ u ∧ u ≤ r) {A : SuzukiPositiveAperture}
    (hA : r - l < 2 * A.1) : logEnergy (centredSource hG hGs hA) = packetLogEnergy G := by
  unfold logEnergy packetLogEnergy
  congr 1
  funext t
  rw [← integral_norm_sq_translate_sub hG.continuous.measurable hGb hGs (-((l + r) / 2)) t]
  rfl

/-- The difference of two packets supported in an interval is supported there. -/
theorem support_sub {g₁ g₂ : ℝ → ℝ} {l r : ℝ} (hs₁ : ∀ u, g₁ u ≠ 0 → l ≤ u ∧ u ≤ r)
    (hs₂ : ∀ u, g₂ u ≠ 0 → l ≤ u ∧ u ≤ r) : ∀ u, g₁ u - g₂ u ≠ 0 → l ≤ u ∧ u ≤ r := fun u hu => by
  by_cases h1 : g₁ u = 0
  · exact hs₂ u fun h2 => hu (by rw [h1, h2, sub_zero])
  · exact hs₁ u h1

/-- The logarithmic energy and the mass of the difference of two centred sources are those of
the difference of the packets. -/
theorem logEnergy_centredSource_sub {G₁ G₂ : ℝ → ℝ} (hG₁ : ContDiff ℝ (⊤ : ℕ∞) G₁)
    (hG₂ : ContDiff ℝ (⊤ : ℕ∞) G₂) {M₁ M₂ l r : ℝ} (hb₁ : ∀ u, |G₁ u| ≤ M₁)
    (hb₂ : ∀ u, |G₂ u| ≤ M₂) (hs₁ : ∀ u, G₁ u ≠ 0 → l ≤ u ∧ u ≤ r)
    (hs₂ : ∀ u, G₂ u ≠ 0 → l ≤ u ∧ u ≤ r) {A : SuzukiPositiveAperture} (hA : r - l < 2 * A.1) :
    logEnergy (fun x => centredSource hG₁ hs₁ hA x - centredSource hG₂ hs₂ hA x) =
        packetLogEnergy (fun u => G₁ u - G₂ u) ∧
      (∫ x, ‖centredSource hG₁ hs₁ hA x - centredSource hG₂ hs₂ hA x‖ ^ 2) =
        packetAutocorr (fun u => G₁ u - G₂ u) 0 := by
  have hdm : Measurable fun u => G₁ u - G₂ u := (hG₁.continuous.sub hG₂.continuous).measurable
  have hdb : ∀ u, |G₁ u - G₂ u| ≤ M₁ + M₂ := fun u =>
    (abs_sub _ _).trans (add_le_add (hb₁ u) (hb₂ u))
  have hds := support_sub hs₁ hs₂
  have hpt : ∀ x : ℝ, centredSource hG₁ hs₁ hA x - centredSource hG₂ hs₂ hA x =
      (((G₁ (x - -((l + r) / 2)) - G₂ (x - -((l + r) / 2)) : ℝ)) : ℂ) := fun x =>
    (Complex.ofReal_sub _ _).symm
  constructor
  · unfold logEnergy packetLogEnergy
    congr 1
    funext t
    rw [← integral_norm_sq_translate_sub hdm hdb hds (-((l + r) / 2)) t]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show ‖(centredSource hG₁ hs₁ hA (x + t) - centredSource hG₂ hs₂ hA (x + t)) -
        (centredSource hG₁ hs₁ hA x - centredSource hG₂ hs₂ hA x)‖ ^ 2 = _
    rw [hpt (x + t), hpt x]
  · simp only [hpt, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [integral_sub_right_eq_self (fun u => (G₁ u - G₂ u) ^ 2) (-((l + r) / 2))]
    simp only [packetAutocorr, add_zero, pow_two]

/-- **Continuity on smooth real packets** supported in a common interval of length below
`2A`. -/
theorem abs_zeroSum_sub_le_of_smooth {G₁ G₂ : ℝ → ℝ} (hG₁ : ContDiff ℝ (⊤ : ℕ∞) G₁)
    (hG₂ : ContDiff ℝ (⊤ : ℕ∞) G₂) {M₁ M₂ l r : ℝ} (hb₁ : ∀ u, |G₁ u| ≤ M₁)
    (hb₂ : ∀ u, |G₂ u| ≤ M₂) (hs₁ : ∀ u, G₁ u ≠ 0 → l ≤ u ∧ u ≤ r)
    (hs₂ : ∀ u, G₂ u ≠ 0 → l ≤ u ∧ u ≤ r) {A : SuzukiPositiveAperture} (hA : r - l < 2 * A.1)
    {s : ℝ} (hs : 0 < s) :
    |zeroSum G₁ - zeroSum G₂| ≤
      160 * (logSamplingConst A.1 zetaZeroWidth *
        ((1 + 1 / s) * (packetLogEnergy (fun u => G₁ u - G₂ u) +
            packetAutocorr (fun u => G₁ u - G₂ u) 0) +
          s * (packetLogEnergy G₂ + packetAutocorr G₂ 0))) := by
  obtain ⟨hLEd, hmd⟩ := logEnergy_centredSource_sub hG₁ hG₂ hb₁ hb₂ hs₁ hs₂ hA
  have h := abs_zetaZeroConfig_re_W_sub_le (centredSource hG₁ hs₁ hA) (centredSource hG₂ hs₂ hA)
    hs
  rwa [re_W_centredSource, re_W_centredSource, hLEd, hmd, logEnergy_centredSource hG₂ hb₂ hs₂ hA,
    integral_norm_sq_centredSource] at h

/-- **Weil's form of bounded packets is continuous in the logarithmic energy.** For bounded
packets `g₁, g₂` supported in a common interval of length below `2A` and below `log(Q + 1)`, with
integrable jump densities and integrable densities of the logarithmic energy of `g₁ − g₂` and of
`g₂`, and every `s > 0`,
`|𝔚_Q(g₁) − 𝔚_Q(g₂)| ≤ 160 · L(A, w) ((1 + 1/s)(E(g₁ − g₂) + ∫(g₁ − g₂)²) + s (E(g₂) + ∫g₂²))`. -/
theorem abs_packetForm_sub_le {g₁ g₂ : ℝ → ℝ} (hm₁ : Measurable g₁) (hm₂ : Measurable g₂)
    {M₁ M₂ l r : ℝ} (hb₁ : ∀ u, |g₁ u| ≤ M₁) (hb₂ : ∀ u, |g₂ u| ≤ M₂)
    (hs₁ : ∀ u, g₁ u ≠ 0 → l ≤ u ∧ u ≤ r) (hs₂ : ∀ u, g₂ u ≠ 0 → l ≤ u ∧ u ≤ r)
    {A : SuzukiPositiveAperture} (hA : r - l < 2 * A.1) {Q : ℕ}
    (hQ : r - l < Real.log ((Q : ℝ) + 1))
    (hJ₁ : IntegrableOn (levyJump g₁) (Set.Ioi 0)) (hJ₂ : IntegrableOn (levyJump g₂) (Set.Ioi 0))
    (hEd : IntervalIntegrable (fun t => 2 * (packetAutocorr (fun u => g₁ u - g₂ u) 0 -
      packetAutocorr (fun u => g₁ u - g₂ u) t) / t) volume 0 1)
    (hE₂ : IntervalIntegrable
      (fun t => 2 * (packetAutocorr g₂ 0 - packetAutocorr g₂ t) / t) volume 0 1)
    {s : ℝ} (hs : 0 < s) :
    |packetForm Q g₁ - packetForm Q g₂| ≤
      160 * (logSamplingConst A.1 zetaZeroWidth *
        ((1 + 1 / s) * (packetLogEnergy (fun u => g₁ u - g₂ u) +
            packetAutocorr (fun u => g₁ u - g₂ u) 0) +
          s * (packetLogEnergy g₂ + packetAutocorr g₂ 0))) := by
  have hL := logSamplingConst_nonneg (σ := zetaZeroWidth) A.2.le
  have hdm : Measurable fun u => g₁ u - g₂ u := hm₁.sub hm₂
  have hdb : ∀ u, |g₁ u - g₂ u| ≤ M₁ + M₂ := fun u =>
    (abs_sub _ _).trans (add_le_add (hb₁ u) (hb₂ u))
  have hds := support_sub hs₁ hs₂
  have h1s : (0 : ℝ) ≤ 1 + 1 / s := by positivity
  have hradius : ∀ᶠ i : ℕ in atTop, (shrinkingBump i).rOut ≤ (A.1 - (r - l) / 2) / 2 :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Iic_mem_nhds (by linarith only [hA]))
  have hbound : ∀ᶠ i : ℕ in atTop,
      |zeroSum (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g₁) - zeroSum (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g₂)| ≤
        160 * (logSamplingConst A.1 zetaZeroWidth *
          ((1 + 1 / s) * (packetLogEnergy (fun u => g₁ u - g₂ u) +
              packetAutocorr (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) fun u => g₁ u - g₂ u) 0) +
            s * (packetLogEnergy g₂ + packetAutocorr (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g₂) 0))) := by
    filter_upwards [hradius] with i hi
    have hsm : ∀ {g : ℝ → ℝ}, (∀ u, g u ≠ 0 → l ≤ u ∧ u ≤ r) →
        ∀ u, AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g u ≠ 0 →
          l - (shrinkingBump i).rOut ≤ u ∧ u ≤ r + (shrinkingBump i).rOut := fun {g} hg u hu =>
      ⟨(mollify_ne_zero (shrinkingBump i) hg u hu).1.le,
        (mollify_ne_zero (shrinkingBump i) hg u hu).2.le⟩
    have hA' : r + (shrinkingBump i).rOut - (l - (shrinkingBump i).rOut) < 2 * A.1 := by
      linarith only [hA, hi]
    have hmd : (fun u => AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g₁ u - AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g₂ u) =
        AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) fun u => g₁ u - g₂ u :=
      (mollify_sub_bounded (shrinkingBump i) hm₁ hm₂ hb₁ hb₂).symm
    have h := abs_zeroSum_sub_le_of_smooth
      (contDiff_top_mollify (shrinkingBump i) hm₁ hb₁ hs₁)
      (contDiff_top_mollify (shrinkingBump i) hm₂ hb₂ hs₂)
      (abs_mollify_le (shrinkingBump i) hb₁) (abs_mollify_le (shrinkingBump i) hb₂)
      (hsm hs₁) (hsm hs₂) (A := A) hA' hs
    rw [hmd] at h
    have hintd := (neg_packetLogEnergy_le_zeroSum_of_smooth
      (contDiff_top_mollify (shrinkingBump i) hdm hdb hds)
      (abs_mollify_le (shrinkingBump i) hdb) (hsm hds) (A := A) hA').1
    have hint₂ := (neg_packetLogEnergy_le_zeroSum_of_smooth
      (contDiff_top_mollify (shrinkingBump i) hm₂ hb₂ hs₂)
      (abs_mollify_le (shrinkingBump i) hb₂) (hsm hs₂) (A := A) hA').1
    have hmonod : packetLogEnergy (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) fun u => g₁ u - g₂ u) ≤
        packetLogEnergy fun u => g₁ u - g₂ u := by
      unfold packetLogEnergy
      exact intervalIntegral.integral_mono_on zero_le_one hintd hEd fun t ht =>
        div_le_div_of_nonneg_right (by
          linarith only [packetAutocorr_mollify_sub_le (shrinkingBump i) hdm hdb hds t]) ht.1
    have hmono₂ : packetLogEnergy (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g₂) ≤ packetLogEnergy g₂ := by
      unfold packetLogEnergy
      exact intervalIntegral.integral_mono_on zero_le_one hint₂ hE₂ fun t ht =>
        div_le_div_of_nonneg_right (by
          linarith only [packetAutocorr_mollify_sub_le (shrinkingBump i) hm₂ hb₂ hs₂ t]) ht.1
    refine h.trans ?_
    have e1 := mul_le_mul_of_nonneg_left (add_le_add_right hmonod
      (packetAutocorr (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) fun u => g₁ u - g₂ u) 0)) h1s
    have e2 := mul_le_mul_of_nonneg_left (add_le_add_right hmono₂
      (packetAutocorr (AbsoluteGeometryOfSpecZ.mollify (shrinkingBump i) g₂) 0)) hs.le
    have e3 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hL
    linarith only [e3]
  exact le_of_tendsto_of_tendsto
    (((tendsto_zeroSum_mollify hm₁ hb₁ hs₁ hQ hJ₁).sub
      (tendsto_zeroSum_mollify hm₂ hb₂ hs₂ hQ hJ₂)).abs)
    ((((((tendsto_packetAutocorr_mollify hdm hdb hds 0).const_add
        (packetLogEnergy fun u => g₁ u - g₂ u)).const_mul (1 + 1 / s)).add
      (((tendsto_packetAutocorr_mollify hm₂ hb₂ hs₂ 0).const_add
        (packetLogEnergy g₂)).const_mul s)).const_mul _).const_mul 160)
    hbound

#print axioms abs_sourceQuadratic_sub_le
#print axioms abs_packetForm_sub_le

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
