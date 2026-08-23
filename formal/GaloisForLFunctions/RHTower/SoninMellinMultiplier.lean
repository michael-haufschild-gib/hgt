import GaloisForLFunctions.RHTower.SoninMellinFunctional
import GaloisForLFunctions.RHTower.SoninDilationAverage
import GaloisForLFunctions.RHTower.SoninLPropertyTheorem
import GaloisForLFunctions.HTGeometry.ExpMultiplierEntire

/-!
# The Mellin transform of a multiplicative smoothing

A dilation multiplies the Mellin transform by the character `r^{s-1/2}`
(`mellin_coe_dilation`), so averaging the dilates `U_{e^x}f` against a weight `k` multiplies it by

`K(s) = ∫_ℝ k(x) e^{(s-1/2)x} dx`,

the two-sided Laplace transform of `k`.  For a smooth compactly supported `k` this multiplier is
entire and decreases faster than every power of the height on every vertical strip
(`HTGeometry/ExpMultiplierRapidDecay`), while the Mellin transform of a vector of `L_b` only grows
polynomially there (Theorem 4.8).  The product therefore lies in Burnol's class `𝓛¹`.

## Main results

* `integral_cpow_dilation` — the dilation character
* `mellinFunctional_dilationAverage` — the multiplier identity
* `HasRapidMellin` — Burnol's Definition 12
* `hasRapidMellin_dilationAverage` — a smoothing of a vector of `L_b` (`b ≥ e^R`) lies in `𝓛¹`
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- **The dilation character.**  Dilating multiplies the Mellin transform by `r^{s-1/2}`. -/
theorem integral_cpow_dilation (r : ℝ) (hr : 0 < r) (f : SoninL2) (s : ℂ) :
    (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * ((dilation r hr f : SoninL2) : ℝ → ℂ) t)
      = ((r : ℝ) : ℂ) ^ (s - 1 / 2)
        * ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  have h := mellin_coe_dilation r hr f (1 - s)
  rw [mellin, mellin] at h
  have hexp : (1 : ℂ) - s - 1 = -s := by ring
  rw [hexp] at h
  have hpow : ((r : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - (1 - s)) = ((r : ℝ) : ℂ) ^ (s - 1 / 2) := by
    congr 1
    ring
  rw [hpow] at h
  simpa only [smul_eq_mul] using h

/-- **The multiplier identity.** -/
theorem mellinFunctional_dilationAverage {k : ℝ → ℝ} (hk : Continuous k)
    (hks : HasCompactSupport k) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s.re < 1) {f : SoninL2}
    (hmem : ∀ x : ℝ, k x ≠ 0 → rayDilate (Real.exp x) f ∈ centralSoninExtendedCarrier 1) :
    mellinFunctional 1 one_pos hs (dilationAverage k f)
      = logSmoothMultiplier k (s - 1 / 2)
        * ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  rw [apply_dilationAverage hk hks f (mellinFunctional 1 one_pos hs), logSmoothMultiplier,
    ← MeasureTheory.integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show ((k x : ℝ) : ℂ) * (mellinFunctional 1 one_pos hs) (rayDilate (Real.exp x) f)
      = ((k x : ℝ) : ℂ) * Complex.exp ((s - 1 / 2) * (x : ℂ))
        * ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t
  by_cases hx : k x = 0
  · rw [hx]
    simp
  · have hmemx := hmem x hx
    rw [rayDilate_of_pos (Real.exp_pos x)] at hmemx ⊢
    have hexp : ((Real.exp x : ℝ) : ℂ) ^ (s - 1 / 2) = Complex.exp ((s - 1 / 2) * (x : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_ne_zero x)),
        ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
      ring_nf
    rw [mellinFunctional_apply_eq one_pos hs hs1 hmemx, integral_cpow_dilation, hexp]
    ring

/-- The smoothing of a vector all of whose relevant dilates lie in `L_1` lies in `L_1`. -/
theorem dilationAverage_mem_extended {k : ℝ → ℝ} (hk : Continuous k) (hks : HasCompactSupport k)
    {f : SoninL2}
    (hmem : ∀ x : ℝ, k x ≠ 0 → rayDilate (Real.exp x) f ∈ centralSoninExtendedCarrier 1) :
    dilationAverage k f ∈ centralSoninExtendedCarrier 1 :=
  dilationAverage_mem_orthogonal (S := meanZeroBand 1 ⊔ centralMeanZeroFourier 1) hk hks hmem

/-! ## The two growth classes -/

theorem HasLProperty.stripPolyGrowthOffReal {F : ℂ → ℂ} (hF : HasLProperty F) :
    HasStripPolyGrowthOffReal F := by
  intro a b
  obtain ⟨T, C, hC, hb⟩ := hF a b 1 one_pos
  refine ⟨max T 1, ⌈max (1 / 2 - a) 0 + 1⌉₊, C, hC, fun s h1 h2 h3 => ?_⟩
  have hT : T ≤ |s.im| := le_trans (le_max_left _ _) h3
  have hbase : (1 : ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hval := hb s h1 h2 hT
  refine hval.trans (mul_le_mul_of_nonneg_left ?_ hC)
  have hle : max (1 / 2 - a) 0 + 1 ≤ ((⌈max (1 / 2 - a) 0 + 1⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hmono := Real.rpow_le_rpow_of_exponent_le hbase hle
  rwa [Real.rpow_natCast] at hmono

theorem hasStripRapidDecrease_logSmoothMultiplier {k : ℝ → ℝ} (hkC : ContDiff ℝ (⊤ : ℕ∞) k)
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) :
    HasStripRapidDecrease (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2)) := by
  intro A B N
  obtain ⟨C, hC0, hC⟩ :=
    exists_bound_norm_logSmoothMultiplier_strip hkC hR hsupp N (A - 1 / 2) (B - 1 / 2)
  refine ⟨1, C, hC0, fun s h1 h2 h3 => ?_⟩
  have hre : ((s : ℂ) - 1 / 2).re = s.re - 1 / 2 := by simp
  have him : ((s : ℂ) - 1 / 2).im = s.im := by simp
  have hval := hC (s - 1 / 2) (by rw [hre]; linarith) (by rw [hre]; linarith)
    (by rw [him]; exact h3)
  rwa [him] at hval

/-! ## Burnol's class `𝓛¹` -/

/-- **Burnol's Definition 12.**  A vector of `L_a` whose continued Mellin transform decreases
faster than every power of the height on every vertical strip. -/
def HasRapidMellin (a : ℝ) (f : SoninL2) : Prop :=
  ∃ c d : ℂ,
    (∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c) ∧
    (∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) ∧
    HasStripRapidDecrease (extendedMellinContinuation a c d f)

theorem hasCompactSupport_of_vanishing {k : ℝ → ℝ} {R : ℝ}
    (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) : HasCompactSupport k := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) ?_
  intro x hx
  refine hsupp x ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with h | h
  · rcases le_or_gt x 0 with hx0 | hx0
    · rw [abs_of_nonpos hx0]; linarith
    · rw [abs_of_pos hx0]; linarith
  · exact le_trans (le_of_lt h) (le_abs_self x)

/-- Every dilate that the weight actually sees stays inside `L_1`. -/
theorem rayDilate_mem_extended_one {b R : ℝ} (hRb : Real.exp R ≤ b) {k : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) {f : SoninL2}
    (hf : f ∈ centralSoninExtendedCarrier b) :
    ∀ x : ℝ, k x ≠ 0 → rayDilate (Real.exp x) f ∈ centralSoninExtendedCarrier 1 := by
  intro x hx
  have hxR : |x| < R := by
    by_contra hcon
    exact hx (hsupp x (not_lt.1 hcon))
  have hex : Real.exp x ≤ b := le_trans (Real.exp_le_exp.2 (le_of_lt
    (lt_of_le_of_lt (le_abs_self x) hxR))) hRb
  have hexn : Real.exp (-x) ≤ b := le_trans (Real.exp_le_exp.2 (le_of_lt
    (lt_of_le_of_lt (neg_le_abs x) hxR))) hRb
  have hpos : (0 : ℝ) < Real.exp x := Real.exp_pos x
  rw [rayDilate_of_pos hpos]
  refine dilation_mem_centralSoninExtendedCarrier hpos hf ?_ ?_
  · rw [le_div_iff₀ hpos, one_mul]
    exact hex
  · have hinv : Real.exp (-x) = (Real.exp x)⁻¹ := by
      rw [Real.exp_neg]
    rw [hinv] at hexn
    rw [inv_le_iff_one_le_mul₀ hpos] at hexn
    linarith [hexn]

/-- **The multiplier identity for the entire numerators.**  The smoothing multiplies the whole
continued Mellin transform by the entire multiplier `logSmoothMultiplier k (s − 1/2)`, on all of
`ℂ` — the identity theorem propagates it from the strip where the integrals converge. -/
theorem extendedMellinNumerator_dilationAverage {b : ℝ} {k : ℝ → ℝ}
    (hkC : ContDiff ℝ (⊤ : ℕ∞) k) {R : ℝ} (hR : 0 < R) (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0)
    (hRb : Real.exp R ≤ b) {f : SoninL2} (hev : f ∈ evenSubspace)
    (hf : f ∈ centralSoninExtendedCarrier b) {c d c' d' : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (f : ℝ → ℂ) t = d)
    (hc' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval 1 →
      ((fourierUnitary (dilationAverage k f) : SoninL2) : ℝ → ℂ) u = c')
    (hd' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 →
      ((dilationAverage k f : SoninL2) : ℝ → ℂ) t = d') (s : ℂ) :
    extendedMellinNumerator 1 c' d' (dilationAverage k f) s
      = logSmoothMultiplier k (s - 1 / 2) * extendedMellinNumerator b c d f s := by
  have hk : Continuous k := hkC.continuous
  have hks : HasCompactSupport k := hasCompactSupport_of_vanishing hsupp
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le (Real.exp_pos R) hRb
  have hmem : ∀ x : ℝ, k x ≠ 0 → rayDilate (Real.exp x) f ∈ centralSoninExtendedCarrier 1 :=
    rayDilate_mem_extended_one hRb hsupp hf
  set g : SoninL2 := dilationAverage k f with hgdef
  have hgmem : g ∈ centralSoninExtendedCarrier 1 := dilationAverage_mem_extended hk hks hmem
  have hgev : g ∈ evenSubspace := dilationAverage_mem_evenSubspace hk hks hev
  obtain ⟨hnumg, hvalg⟩ := differentiable_extendedMellinNumerator one_pos hgev hc' hd'
  obtain ⟨hnumf, hvalf⟩ := differentiable_extendedMellinNumerator hb0 hev hc hd
  have hKdiff : Differentiable ℂ (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2)) := by
    exact (differentiable_logSmoothMultiplier hk hR hsupp).comp
      (differentiable_id.sub (differentiable_const _))
  have hprodDiff : Differentiable ℂ
      (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2) * extendedMellinNumerator b c d f s) :=
    hKdiff.mul hnumf
  have hstrip : IsOpen {v : ℂ | 1 / 2 < v.re ∧ v.re < 1} := by
    refine IsOpen.inter (isOpen_lt continuous_const Complex.continuous_re)
      (isOpen_lt Complex.continuous_re continuous_const)
  have hz₀ : ((3 : ℂ) / 4) ∈ {v : ℂ | 1 / 2 < v.re ∧ v.re < 1} := by
    constructor <;> · simp; norm_num
  have hev₀ : extendedMellinNumerator 1 c' d' g
      =ᶠ[𝓝 ((3 : ℂ) / 4)] fun s : ℂ =>
        logSmoothMultiplier k (s - 1 / 2) * extendedMellinNumerator b c d f s := by
    filter_upwards [hstrip.mem_nhds hz₀] with w hw
    have hw1 : 1 / 2 < w.re := hw.1
    have hw2 : w.re < 1 := hw.2
    have hgint : (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-w) * (g : ℝ → ℂ) t)
        = logSmoothMultiplier k (w - 1 / 2)
          * ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-w) * (f : ℝ → ℂ) t := by
      rw [← mellinFunctional_apply_eq one_pos hw1 hw2 hgmem, hgdef,
        mellinFunctional_dilationAverage hk hks hw1 hw2 hmem]
    rw [← hvalg w hw1 hw2, ← hvalf w hw1 hw2, hgint]
    ring
  have hA : AnalyticOnNhd ℂ (extendedMellinNumerator 1 c' d' g) univ :=
    hnumg.differentiableOn.analyticOnNhd isOpen_univ
  have hB : AnalyticOnNhd ℂ
      (fun s : ℂ => logSmoothMultiplier k (s - 1 / 2) * extendedMellinNumerator b c d f s)
      univ := hprodDiff.differentiableOn.analyticOnNhd isOpen_univ
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (mem_univ _) hev₀
    (mem_univ s)

/-- The smoothing multiplies the continued Mellin transform by an entire multiplier. -/
theorem extendedMellinContinuation_dilationAverage {b : ℝ} {k : ℝ → ℝ}
    (hkC : ContDiff ℝ (⊤ : ℕ∞) k) {R : ℝ} (hR : 0 < R) (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0)
    (hRb : Real.exp R ≤ b) {f : SoninL2} (hev : f ∈ evenSubspace)
    (hf : f ∈ centralSoninExtendedCarrier b) {c d c' d' : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval b →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval b → (f : ℝ → ℂ) t = d)
    (hc' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval 1 →
      ((fourierUnitary (dilationAverage k f) : SoninL2) : ℝ → ℂ) u = c')
    (hd' : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval 1 →
      ((dilationAverage k f : SoninL2) : ℝ → ℂ) t = d') :
    extendedMellinContinuation 1 c' d' (dilationAverage k f)
      = fun s : ℂ => logSmoothMultiplier k (s - 1 / 2)
          * extendedMellinContinuation b c d f s := by
  funext s
  rw [extendedMellinContinuation, extendedMellinContinuation,
    extendedMellinNumerator_dilationAverage hkC hR hsupp hRb hev hf hc hd hc' hd' s,
    mul_div_assoc]

/-- **The smoothing of a vector of `L_b` lies in `𝓛¹`.** -/
theorem hasRapidMellin_dilationAverage {b : ℝ} {k : ℝ → ℝ} (hkC : ContDiff ℝ (⊤ : ℕ∞) k)
    {R : ℝ} (hR : 0 < R) (hsupp : ∀ x : ℝ, R ≤ |x| → k x = 0) (hRb : Real.exp R ≤ b)
    {f : SoninL2} (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninExtendedCarrier b) :
    HasRapidMellin 1 (dilationAverage k f) := by
  have hk : Continuous k := hkC.continuous
  have hks : HasCompactSupport k := hasCompactSupport_of_vanishing hsupp
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le (Real.exp_pos R) hRb
  have hb1 : (1 : ℝ) ≤ b := le_trans (Real.one_le_exp hR.le) hRb
  -- every relevant dilate stays in `L_1`
  have hmem : ∀ x : ℝ, k x ≠ 0 → rayDilate (Real.exp x) f ∈ centralSoninExtendedCarrier 1 :=
    rayDilate_mem_extended_one hRb hsupp hf
  set g : SoninL2 := dilationAverage k f with hgdef
  have hgmem : g ∈ centralSoninExtendedCarrier 1 := dilationAverage_mem_extended hk hks hmem
  have hgev : g ∈ evenSubspace := dilationAverage_mem_evenSubspace hk hks hev
  obtain ⟨c', hc'⟩ := ae_fourier_eq_of_mem_extended hgmem
  obtain ⟨d', hd'⟩ := ae_eq_of_mem_extended hgmem
  obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hf
  obtain ⟨d, hd⟩ := ae_eq_of_mem_extended hf
  refine ⟨c', d', hc', hd', ?_⟩
  have hcont : extendedMellinContinuation 1 c' d' g
      = fun s : ℂ => logSmoothMultiplier k (s - 1 / 2)
          * extendedMellinContinuation b c d f s :=
    extendedMellinContinuation_dilationAverage hkC hR hsupp hRb hev hf hc hd hc' hd'
  rw [hcont]
  exact (hasStripRapidDecrease_logSmoothMultiplier hkC hR hsupp).mul_stripPolyGrowth
    (hasLProperty_extendedMellinContinuation hb0 hev hc hd).stripPolyGrowthOffReal

end RHTower

end
