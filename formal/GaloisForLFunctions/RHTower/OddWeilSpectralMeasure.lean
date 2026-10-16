import GaloisForLFunctions.RHTower.OddWeilLineKernel
import GaloisForLFunctions.RHTower.OddWeilHerglotzTransfer
import GaloisForLFunctions.RHTower.WeilFunctionalLineIntegral
import GaloisForLFunctions.RHTower.WeilAtomicExplicitFormula

/-!
# The odd Weil functional is the spectral integral of its Nevanlinna measure

Let `Ψ` be a slit continuation of the Weil function of `lam` with the squared-variable sign law
(the conclusion of `exists_weilFunction_slit_continuation`), and let `(ν, c)` be the Nevanlinna
data of `g(z) = aΨ(½ + a)`, `z = a²` (`exists_nevanlinna_measure_of_slit`).

**Theorem** (`re_weilFullFunctional_eq_integral_oddSpectralWeight`).  For every odd `C²`
compactly supported `f`,
`Re W_lam(f ⋆ f̃) = ∫ Θ_f(e^{iθ}) dν(θ)`, `Θ_f(ζ) = Re[(1/2π) ∫ F(t) K_ζ(5/4 + it) dt]`,
with `F(t) = H(5/4 + it) + H(1 − 5/4 − it)`, `H = Hfn(f ⋆ f̃)`, and the kernel `K_ζ` of
`OddWeilLineKernel`.  The constant `c` and the point `ζ = 1` do not contribute to odd tests.

**Evaluation** (`oddSpectralWeight_eq_of_pos`, `oddSpectralWeight_eq_of_neg`).  With
`γ = circleOrd ζ`: on the critical ordinates `Θ_f(ζ) = (1 + γ²)|f̂(√γ)|²/γ` (`γ > 0`); on the
cut `Θ_f(ζ) = (1 + γ²)|f̂(i√(−γ))|²/(−γ)` (`−¼ ≤ γ < 0`); `Θ_f(1) = 0`; `Θ_f(−1) ≥ 0` by
continuity.  So `Θ_f ≥ 0` on the support of `ν` (`oddSpectralWeight_nonneg`).

**Corollary** (`weilPositiveOdd_of_slit_sign_law`, `weilPositiveOdd_iff_exists_slit`).  Odd
Weil positivity is equivalent to absolute convergence on `Re s > 1` together with a holomorphic
slit continuation satisfying the sign law.

Mechanism.  On the line `w = 5/4 + it`, `t ≠ 0`, the representation reads
`Ψ(w) = ∫ K_ζ(w) dν − c/(w − ½)` (first quadrant by the chart, fourth by real coefficients).
The line-integral form of the Weil functional, Fubini (uniform kernel bound `44(1 + t²)` on the
support, `|F| ≤ 2D/(1 + t²)²`), and the two-line residue identity `two_line_pair` evaluate each
`ζ`: `K_ζ(w) = −(1/γ)/(w − ½) + ((1 + γ²)/(2γ)) g_{½+ρ}(w)` with `ρ² = −γ`, and
`H(½) = |f̂(0)|² = 0` for odd `f`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open Zeta23 Zeta23.WeilEF GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.OddResolvent
open WeilHerglotz RHTower.AtomDomination RHTower.WeilLineIntegral RHTower.WeilAtomic

/-! ## The Nevanlinna data of a slit continuation -/

/-- The Nevanlinna measure of a slit continuation with the sign law. -/
theorem exists_nevanlinna_measure_of_slit {lam : ℕ → ℝ} {Ψ : ℂ → ℂ}
    (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    (hΨs : ∀ s : ℂ, 1 / 2 < s.re → s.im ≠ 0 → 0 ≤ s.im * (((s - 1 / 2) * Ψ s).im)) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∃ c : ℝ,
      ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0 ∧
      ∀ a : ℂ, 0 < a.re → 0 < a.im →
        a * Ψ (1 / 2 + a) =
          (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c := by
  set F : ℂ → ℂ := fun a => Ψ (1 / 2 + a) with hF
  set D : Set ℂ := {a : ℂ | 1 / 2 + a ∈ oddWeilSlitDomain} with hD
  have hDo : IsOpen D := isOpen_oddWeilSlitDomain.preimage (by fun_prop)
  have hFd : DifferentiableOn ℂ F D := by
    intro a ha
    exact ((hΨd.differentiableAt (isOpen_oddWeilSlitDomain.mem_nhds ha)).comp a
      (by fun_prop)).differentiableWithinAt
  have hQD : {a : ℂ | 0 < a.re ∧ 0 < a.im} ⊆ D := by
    intro a ha
    show 1 / 2 + a ∈ oddWeilSlitDomain
    refine ⟨?_, Or.inl ?_⟩
    · simp only [Complex.add_re]; norm_num; linarith [ha.1]
    · simp only [Complex.add_im]; norm_num; exact ha.2.ne'
  have hFQ : DifferentiableOn ℂ F {a : ℂ | 0 < a.re ∧ 0 < a.im} := hFd.mono hQD
  have hsign : ∀ a : ℂ, 0 < a.re → 0 < a.im → 0 ≤ (a * F a).im := by
    intro a ha hai
    have h := hΨs (1 / 2 + a) (by simp; linarith) (by simp; exact hai.ne')
    have e : (1 / 2 + a - 1 / 2 : ℂ) = a := by ring
    rw [e] at h
    have hi : (1 / 2 + a : ℂ).im = a.im := by simp
    rw [hi] at h
    exact (mul_nonneg_iff_of_pos_left hai).mp h
  obtain ⟨ν, hfin, hpois, c, hrep⟩ :=
    exists_hrKernel_representation (differentiableOn_oddChart hFQ) (re_oddChart_nonneg hsign)
  refine ⟨ν, hfin, c, ?_, ?_⟩
  · refine measure_ordinate_open_eq_zero_of_poisson hpois isOpen_Iio fun t ht => ?_
    have ht' : 1 / 4 < -t := by
      have : t < -(1 / 4) := ht
      linarith
    have hx : 0 < -t := by linarith
    have hz : zPt ((1 / 2 : ℂ) + t * I) = ((-t : ℝ) : ℂ) := by
      unfold zPt
      push_cast
      ring_nf
      rw [I_sq]
      ring
    have hsq : sqrtQ ((-t : ℝ) : ℂ) = (Real.sqrt (-t) : ℂ) := sqrtQ_ofReal hx.le
    have hsqrt_gt : 1 / 2 < Real.sqrt (-t) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) ht'
    have hmem : sqrtQ ((-t : ℝ) : ℂ) ∈ D := by
      rw [hsq]
      show 1 / 2 + (Real.sqrt (-t) : ℂ) ∈ oddWeilSlitDomain
      refine ⟨?_, Or.inr ?_⟩
      · simp only [Complex.add_re, Complex.ofReal_re]; norm_num; linarith
      · simp only [Complex.add_re, Complex.ofReal_re]; norm_num; linarith
    have hgcont : ContinuousAt (sqNev F) ((-t : ℝ) : ℂ) :=
      (differentiableAt_sqNev hDo hFd (mem_slitPlane_of_re_pos (by simpa using hx))
        hmem).continuousAt
    have hgreal : (sqNev F ((-t : ℝ) : ℂ)).im = 0 := by
      unfold sqNev
      rw [hsq, Complex.im_ofReal_mul]
      have hre1 : 1 < ((1 / 2 : ℂ) + (Real.sqrt (-t) : ℂ)).re := by
        simp only [Complex.add_re, Complex.ofReal_re]; norm_num; linarith
      have hval : F (Real.sqrt (-t) : ℂ) =
          weilFunction lam (((1 / 2 + Real.sqrt (-t) : ℝ)) : ℂ) := by
        simp only [hF]
        rw [hΨe _ hre1]
        push_cast
        rfl
      rw [hval, weilFunction_ofReal_im, mul_zero]
    have hcont : ContinuousAt (fun s => (oddChart F s).re) ((1 / 2 : ℂ) + t * I) := by
      simp only [re_oddChart]
      have hg : ContinuousAt (sqNev F) (zPt ((1 / 2 : ℂ) + t * I)) := by
        rw [hz]
        exact hgcont
      exact Complex.continuous_im.continuousAt.comp
        (hg.comp differentiable_zPt.continuous.continuousAt)
    have hval : (oddChart F ((1 / 2 : ℂ) + t * I)).re = 0 := by
      rw [re_oddChart, hz]
      exact hgreal
    rw [← hval]
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  · intro a ha hai
    have hs : 1 / 2 < (1 / 2 - I * a ^ 2).re := by
      rw [re_half_sub_I_mul]
      have : 0 < (a ^ 2).im := by simp [pow_two, Complex.mul_im]; positivity
      linarith
    have h := hrep _ hs
    rw [oddChart, zPt_half_sub, sqNev_sq ha] at h
    rw [integral_const_mul]
    have e : a * Ψ (1 / 2 + a) = I * (-I * (a * F a)) := by
      simp only [hF]; ring_nf; rw [I_sq]; ring
    rw [e, h]
    ring_nf
    rw [I_sq]
    ring

/-- A slit continuation has real coefficients: `Ψ(s̄) = conj Ψ(s)` on the slit domain. -/
theorem slit_conj {lam : ℕ → ℝ} {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s) {s : ℂ} (hs : s ∈ oddWeilSlitDomain) :
    Ψ (conj s) = conj (Ψ s) := by
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ 0 < z.im} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)
  have hUc : IsPreconnected U :=
    ((convex_halfSpace_re_gt (1 / 2)).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hUsub : ∀ z ∈ U, z ∈ oddWeilSlitDomain := fun z hz => ⟨hz.1, Or.inl hz.2.ne'⟩
  have hUsub' : ∀ z ∈ U, conj z ∈ oddWeilSlitDomain := fun z hz =>
    ⟨by simpa using hz.1, Or.inl (by simp; exact hz.2.ne')⟩
  set G : ℂ → ℂ := fun z => conj (Ψ (conj z)) with hG
  have hΨU : DifferentiableOn ℂ Ψ U := hΨd.mono hUsub
  have hGU : DifferentiableOn ℂ G U := by
    intro z hz
    have h := ((hΨd.differentiableAt (isOpen_oddWeilSlitDomain.mem_nhds (hUsub' z hz)))).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have heq : Ψ =ᶠ[𝓝 (2 + I : ℂ)] G := by
    have hm : {z : ℂ | 1 < z.re ∧ 0 < z.im} ∈ 𝓝 (2 + I : ℂ) :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds (by norm_num)
    filter_upwards [hm] with z hz
    simp only [hG]
    rw [hΨe z hz.1, hΨe _ (by simpa using hz.1), WeilSpectral.weilFunction_conj,
      Complex.conj_conj]
  have hEq := (hΨU.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hGU.analyticOnNhd hUo) hUc (show (2 + I : ℂ) ∈ U from ⟨by simp; norm_num, by simp⟩) heq
  -- the upper half
  have hup : ∀ z ∈ U, Ψ (conj z) = conj (Ψ z) := by
    intro z hz
    have := hEq hz
    simp only [hG] at this
    rw [this, Complex.conj_conj]
  rcases lt_trichotomy 0 s.im with hpos | hzero | hneg
  · exact hup s ⟨hs.1, hpos⟩
  · have hre : 1 < s.re := hs.2.resolve_left (by simp [← hzero])
    have hcs : conj s = s := by
      apply Complex.ext
      · simp
      · rw [Complex.conj_im, ← hzero, neg_zero]
    have hw := WeilSpectral.weilFunction_conj lam s
    rw [hcs] at hw
    rw [hcs, hΨe s hre]
    exact hw
  · have hcs : conj s ∈ U := ⟨by simpa using hs.1, by simpa using hneg⟩
    have h := hup (conj s) hcs
    rw [Complex.conj_conj] at h
    rw [h, Complex.conj_conj]

/-! ## The representation on the line -/

theorem linePt_mem_slit (t : ℝ) : linePt t ∈ oddWeilSlitDomain := by
  refine ⟨?_, Or.inr ?_⟩ <;> simp [linePt] <;> norm_num

theorem half_add_lineA (t : ℝ) : (1 / 2 : ℂ) + lineA t = linePt t := by
  unfold lineA linePt; ring

/-- `Ψ(5/4 + it) = ∫ K_ζ(5/4 + it) dν − c/(¾ + it)` for `t ≠ 0`. -/
theorem slit_eq_integral_oddLineKernel {lam : ℕ → ℝ} {Ψ : ℂ → ℂ}
    (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s) {ν : Measure ℝ} {c : ℝ}
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    {t : ℝ} (ht : t ≠ 0) :
    Ψ (linePt t) = (∫ θ, oddLineKernel (circleMap 0 1 θ) (linePt t) ∂ν) - c / lineA t := by
  have key : ∀ t : ℝ, 0 < t →
      Ψ (linePt t) = (∫ θ, oddLineKernel (circleMap 0 1 θ) (linePt t) ∂ν) - c / lineA t := by
    intro t ht
    have ha : 0 < (lineA t).re := by rw [lineA_re]; norm_num
    have hai : 0 < (lineA t).im := by rw [lineA_im]; exact ht
    have h := hrep (lineA t) ha hai
    rw [half_add_lineA] at h
    have hne := lineA_ne_zero t
    have hK : ∀ θ, oddLineKernel (circleMap 0 1 θ) (linePt t) =
        I * hrKernel (1 / 2 - I * lineA t ^ 2) (circleMap 0 1 θ) / lineA t := by
      intro θ
      unfold oddLineKernel
      rw [linePt_sub_half]
    simp_rw [hK]
    rw [integral_div]
    have : Ψ (linePt t) = (lineA t * Ψ (linePt t)) / lineA t := by field_simp
    rw [this, h]
    field_simp
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · have hpos' : 0 < -t := by linarith
    have h := key (-t) hpos'
    have hc : Ψ (linePt t) = conj (Ψ (linePt (-t))) := by
      rw [linePt_neg, slit_conj hΨd hΨe (linePt_mem_slit t), Complex.conj_conj]
    rw [hc, h, map_sub, map_div₀, Complex.conj_ofReal, ← integral_conj, lineA_neg,
      Complex.conj_conj]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    show conj (oddLineKernel (circleMap 0 1 θ) (linePt (-t))) =
      oddLineKernel (circleMap 0 1 θ) (linePt t)
    rw [← oddLineKernel_neg hpos'.ne' (norm_circleMap_one θ), neg_neg]
  · exact key t hpos

/-! ## The line transform of an odd test -/

/-- `F(t) = H(5/4 + it) + H(1 − 5/4 − it)`, `H = Hfn(f ⋆ f̃)`. -/
def lineTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  Hfn (EF.weilTest f f) (((5 / 4 : ℝ) : ℂ) + t * I) +
    Hfn (EF.weilTest f f) (1 - ((5 / 4 : ℝ) : ℂ) - t * I)

theorem linePt_eq (t : ℝ) : linePt t = ((5 / 4 : ℝ) : ℂ) + t * I := by
  simp [linePt]

theorem exists_norm_lineTransform_le {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖lineTransform f t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
  obtain ⟨D, hD0, hD⟩ := norm_Hfn_weilTest_le hf hfc
  refine ⟨D, hD0, fun t => ?_⟩
  have e : (1 : ℂ) - ((5 / 4 : ℝ) : ℂ) - t * I = ((1 - 5 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
    push_cast; ring
  unfold lineTransform
  refine (norm_add_le _ _).trans ?_
  rw [e]
  have h1 := hD (5 / 4) t (by norm_num) (by norm_num)
  have h2 := hD (1 - 5 / 4) (-t) (by norm_num) (by norm_num)
  rw [neg_sq] at h2
  rw [two_mul, add_div]
  exact add_le_add h1 h2

theorem continuous_lineTransform {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (lineTransform f) := by
  have hkd : ContDiff ℝ 2 (EF.weilTest f f) := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hm : ∀ t : ℝ, Hfn (EF.weilTest f f) (1 - ((5 / 4 : ℝ) : ℂ) - t * I) =
      Hfn (fun u => EF.weilTest f f (-u)) (((5 / 4 : ℝ) : ℂ) + t * I) :=
    fun t => Hfn_mirror (EF.weilTest f f) (5 / 4) t
  unfold lineTransform
  simp only [hm]
  exact (continuous_Hfn_line hkd hkc (5 / 4)).add
    (continuous_Hfn_line (hkd.comp contDiff_neg) (hkc.comp_homeomorph (Homeomorph.neg ℝ)) (5 / 4))

theorem integrable_lineTransform {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (lineTransform f) := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_lineTransform_le hf hfc
  refine (integrable_inv_one_add_sq.const_mul (2 * D)).mono'
    (continuous_lineTransform hf hfc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  calc ‖lineTransform f t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := hD t
    _ ≤ 2 * D / (1 + t ^ 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg t])
    _ = 2 * D * (1 + t ^ 2)⁻¹ := by ring

/-- The spectral weight `Θ_f(ζ) = Re[(1/2π) ∫ F(t) K_ζ(5/4 + it) dt]`. -/
def oddSpectralWeight (f : ℝ → ℂ) (ζ : ℂ) : ℝ :=
  ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, lineTransform f t * oddLineKernel ζ (linePt t)).re

/-! ## Measurability and the Fubini bound -/

theorem continuous_linePt : Continuous linePt := by
  unfold linePt; fun_prop

theorem continuous_lineA : Continuous lineA := by
  unfold lineA; fun_prop

theorem measurable_oddLineKernel_prod :
    Measurable fun p : ℝ × ℝ => oddLineKernel (circleMap 0 1 p.2) (linePt p.1) := by
  have hζ : Measurable fun p : ℝ × ℝ => circleMap 0 1 p.2 :=
    (continuous_circleMap 0 1).measurable.comp measurable_snd
  have hw : Measurable fun p : ℝ × ℝ => linePt p.1 := continuous_linePt.measurable.comp measurable_fst
  have hs : Measurable fun p : ℝ × ℝ => (1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2 := by
    exact measurable_const.sub (measurable_const.mul ((hw.sub measurable_const).pow_const 2))
  have hd : Measurable fun p : ℝ × ℝ => discPt ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2) := by
    have e : (fun p : ℝ × ℝ => discPt ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2)) =
        fun p => (2 * ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2) - 3) /
          (2 * ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2) + 1) := rfl
    rw [e]
    exact ((measurable_const.mul hs).sub measurable_const).div
      ((measurable_const.mul hs).add measurable_const)
  have hk : Measurable fun p : ℝ × ℝ =>
      hrKernel ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2) (circleMap 0 1 p.2) := by
    have e : (fun p : ℝ × ℝ =>
        hrKernel ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2) (circleMap 0 1 p.2)) =
        fun p => (circleMap 0 1 p.2 + discPt ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2)) /
          (circleMap 0 1 p.2 - discPt ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2)) := rfl
    rw [e]
    exact (hζ.add hd).div (hζ.sub hd)
  have e : (fun p : ℝ × ℝ => oddLineKernel (circleMap 0 1 p.2) (linePt p.1)) =
      fun p => I * hrKernel ((1 / 2 : ℂ) - I * (linePt p.1 - 1 / 2) ^ 2) (circleMap 0 1 p.2) /
        (linePt p.1 - 1 / 2) := rfl
  rw [e]
  exact (measurable_const.mul hk).div (hw.sub measurable_const)

theorem ae_support_of_measure_eq_zero {ν : Measure ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0) :
    ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 ∨ -(1 / 4) ≤ circleOrd (circleMap 0 1 θ) := by
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) hsupp
  simp only [Set.mem_setOf_eq, not_or, not_le] at hθ
  exact ⟨hθ.1, hθ.2⟩

/-- **The spectral representation of the odd Weil functional.**  For odd `f`,
`Re W_lam(f ⋆ f̃) = ∫ Θ_f(e^{iθ}) dν(θ)`. -/
theorem re_weilFullFunctional_eq_integral_oddSpectralWeight {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {c : ℝ}
    (hsupp : ν {θ | circleMap 0 1 θ ≠ 1 ∧ angleOrd θ ∈ Iio (-(1 / 4 : ℝ))} = 0)
    (hrep : ∀ a : ℂ, 0 < a.re → 0 < a.im →
      a * Ψ (1 / 2 + a) =
        (∫ θ, I * hrKernel (1 / 2 - I * a ^ 2) (circleMap 0 1 θ) ∂ν) - c)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) :
    (weilFullFunctional lam (EF.weilTest f f)).re =
      ∫ θ, oddSpectralWeight f (circleMap 0 1 θ) ∂ν := by
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨D, hD0, hD⟩ := exists_norm_lineTransform_le hf hfc
  have hFc : Continuous (lineTransform f) := continuous_lineTransform hf hfc
  have hFi : Integrable (lineTransform f) := integrable_lineTransform hf hfc
  have hae : ∀ᵐ θ ∂ν, circleMap 0 1 θ = 1 ∨ -(1 / 4) ≤ circleOrd (circleMap 0 1 θ) :=
    ae_support_of_measure_eq_zero hsupp
  set g : ℝ × ℝ → ℂ := fun p => lineTransform f p.1 * oddLineKernel (circleMap 0 1 p.2) (linePt p.1)
    with hg
  have hgm : Measurable g := (hFc.measurable.comp measurable_fst).mul measurable_oddLineKernel_prod
  set M : ℝ := ν.real univ with hM
  have hM0 : 0 ≤ M := by positivity
  -- integrability on the product
  have hpt : ∀ t : ℝ, t ≠ 0 →
      ∀ᵐ θ ∂ν, ‖g (t, θ)‖ ≤ ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) := by
    intro t ht
    filter_upwards [hae] with θ hθ
    simp only [hg, norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_oddLineKernel_le ht (norm_circleMap_one θ) hθ)
      (norm_nonneg _)
  have hint : ∀ t : ℝ, t ≠ 0 → Integrable (fun θ => g (t, θ)) ν := fun t ht =>
    Integrable.mono' (integrable_const (‖lineTransform f t‖ * (44 * (1 + t ^ 2))))
      (hgm.comp measurable_prodMk_left).aestronglyMeasurable (hpt t ht)
  have hgi : Integrable g (volume.prod ν) := by
    rw [integrable_prod_iff hgm.aestronglyMeasurable]
    constructor
    · filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      exact hint t ht
    · refine (integrable_inv_one_add_sq.const_mul (2 * D * 44 * M)).mono'
        hgm.aestronglyMeasurable.norm.integral_prod_right' ?_
      filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      rw [Real.norm_of_nonneg (integral_nonneg fun θ => norm_nonneg _)]
      calc ∫ θ, ‖g (t, θ)‖ ∂ν ≤ ∫ _θ, ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) ∂ν :=
            integral_mono_ae (hint t ht).norm (integrable_const _) (hpt t ht)
        _ = ‖lineTransform f t‖ * (44 * (1 + t ^ 2)) * M := by
            rw [integral_const, smul_eq_mul, hM]; ring
        _ ≤ 2 * D / (1 + t ^ 2) ^ 2 * (44 * (1 + t ^ 2)) * M := by gcongr; exact hD t
        _ = 2 * D * 44 * M * (1 + t ^ 2)⁻¹ := by field_simp
  -- the line integral form
  rw [weilFullFunctional_eq_line_integral hsl hkd hkc (c := 5 / 4) (by norm_num) (by norm_num)]
  have hline : ∀ t : ℝ, (Hfn k (((5 / 4 : ℝ) : ℂ) + t * I) + Hfn k (1 - ((5 / 4 : ℝ) : ℂ) - t * I)) *
      weilFunction lam (((5 / 4 : ℝ) : ℂ) + t * I) = lineTransform f t * Ψ (linePt t) := by
    intro t
    rw [linePt_eq, ← hΨe _ (by simp; norm_num)]
    rfl
  simp_rw [hline]
  -- substitute the representation
  have hsub : ∀ᵐ t ∂volume, lineTransform f t * Ψ (linePt t) =
      (∫ θ, g (t, θ) ∂ν) - c * (lineTransform f t / lineA t) := by
    filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
    rw [slit_eq_integral_oddLineKernel hΨd hΨe hrep ht, mul_sub, ← integral_const_mul]
    simp only [hg]
    ring
  have hci : Integrable fun t => c * (lineTransform f t / lineA t) := by
    refine (hFi.norm.const_mul (|c| * (4 / 3))).mono'
      ((hFc.div continuous_lineA fun t => lineA_ne_zero t).const_mul (c : ℂ)).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
    have h34 := norm_lineA_ge t
    have : ‖lineTransform f t‖ / ‖lineA t‖ ≤ ‖lineTransform f t‖ * (4 / 3) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [norm_nonneg (lineTransform f t)]
    calc |c| * (‖lineTransform f t‖ / ‖lineA t‖) ≤ |c| * (‖lineTransform f t‖ * (4 / 3)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg c)
      _ = |c| * (4 / 3) * ‖lineTransform f t‖ := by ring
  have hswap : (∫ t, ∫ θ, g (t, θ) ∂ν) = ∫ θ, (∫ t, g (t, θ)) ∂ν :=
    integral_integral_swap (f := fun t θ => g (t, θ)) hgi
  rw [integral_congr_ae hsub, integral_sub hgi.integral_prod_left hci, hswap, integral_const_mul]
  -- the `c`-term vanishes: `(1/2π) ∫ F/(w − ½) = H(½) = |f̂(0)|² = 0`
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hkd hkc
  have hH := differentiable_Hfn hkd hkc
  have hpair := two_line_pair hH (c := 5 / 4) (C := C)
    (fun σ t h1 h2 => hC σ t (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith))
    (z₀ := 1 / 2) (by norm_num) (by norm_num)
  have hH0 : Hfn k (1 / 2) = 0 := by
    unfold Hfn
    rw [sub_self, zero_div, hk, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc,
      paperFT_zero_of_odd hodd, zero_mul]
  have hgp : ∀ t : ℝ, lineTransform f t / lineA t =
      (lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I)) / 2 := by
    intro t
    unfold gPair
    rw [← linePt_eq, linePt_sub_half, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, linePt_sub_half]
    have := lineA_ne_zero t
    field_simp
    ring
  have hcterm : (1 / (2 * Real.pi) : ℂ) * ∫ t, lineTransform f t / lineA t = 0 := by
    simp_rw [hgp]
    rw [integral_div, ← mul_div_assoc]
    have e : (1 / (2 * Real.pi) : ℂ) *
        ∫ t, lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I) =
        Hfn k (1 / 2) + Hfn k (1 - 1 / 2) := by
      rw [← hpair]
      rfl
    rw [e, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hH0]
    simp
  rw [mul_sub, mul_left_comm, hcterm, mul_zero, sub_zero]
  -- real part of the `ν`-integral
  have hJi : Integrable (fun θ => ∫ t, g (t, θ)) ν := hgi.integral_prod_right
  have hre : (∫ θ, (∫ t, g (t, θ)) ∂ν).re = ∫ θ, (∫ t, g (t, θ)).re ∂ν := by
    have h := integral_re hJi
    simp only [RCLike.re_to_complex] at h
    exact h.symm
  rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, hre, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
  simp only [oddSpectralWeight]
  rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-! ## Evaluation of the spectral weight -/

/-- `Θ_f(1) = 0`: the linear term has purely imaginary line integral. -/
theorem oddSpectralWeight_one {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    oddSpectralWeight f 1 = 0 := by
  unfold oddSpectralWeight
  have h : ∀ t : ℝ, lineTransform f t * oddLineKernel 1 (linePt t) =
      lineTransform f t * (((5 / 4 : ℝ) : ℂ) + t * I - 1 / 2) := by
    intro t
    rw [oddLineKernel_one, ← linePt_sub_half, linePt_eq]
  simp_rw [h]
  rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]
  unfold lineTransform
  rw [re_integral_line_weilTest_linear hf hfc, mul_zero]

/-- Partial fractions: `K_ζ(w) = −(1/γ) g_{½}(w)/2 + ((1 + γ²)/(2γ)) g_{½+ρ}(w)`, `ρ² = −γ`. -/
theorem oddLineKernel_eq_gPair {t : ℝ} (ht : t ≠ 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : circleOrd ζ ≠ 0) {ρ : ℂ} (hρ : ρ ^ 2 = -(circleOrd ζ : ℂ)) :
    oddLineKernel ζ (linePt t) =
      -(1 / (circleOrd ζ : ℂ)) * (gPair (1 / 2) (linePt t) / 2) +
        ((1 + (circleOrd ζ : ℂ) ^ 2) / (2 * circleOrd ζ)) * gPair (1 / 2 + ρ) (linePt t) := by
  rw [oddLineKernel_eq ht hζ h1]
  have ha0 : lineA t ≠ 0 := lineA_ne_zero t
  have hγ0 : (circleOrd ζ : ℂ) ≠ 0 := by rwa [Ne, Complex.ofReal_eq_zero]
  have hu : lineA t ^ 2 + (circleOrd ζ : ℂ) ≠ 0 := lineA_sq_add_ne_zero ht _
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at hρ
    simp at hρ
    exact hγ0 (by rw [hρ])
  have hfac : (lineA t - ρ) * (lineA t + ρ) = lineA t ^ 2 + (circleOrd ζ : ℂ) := by
    rw [← neg_neg (circleOrd ζ : ℂ), ← hρ]; ring
  have hm : lineA t - ρ ≠ 0 := left_ne_zero_of_mul (hfac ▸ hu)
  have hp : lineA t + ρ ≠ 0 := right_ne_zero_of_mul (hfac ▸ hu)
  unfold gPair
  rw [linePt_sub_half, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, linePt_sub_half,
    show linePt t - (1 / 2 + ρ) = lineA t - ρ by rw [← linePt_sub_half]; ring,
    show linePt t - (1 - (1 / 2 + ρ)) = lineA t + ρ by rw [← linePt_sub_half]; ring]
  have hγρ : (circleOrd ζ : ℂ) = -ρ ^ 2 := by linear_combination -hρ
  rw [hγρ] at hu ⊢
  field_simp
  ring

/-- Integrability of `F · g_{z₀}` on the line for `1 − 5/4 < Re z₀ < 5/4`. -/
theorem integrable_lineTransform_mul_gPair {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {z₀ : ℂ} (h1 : 1 - 5 / 4 < z₀.re) (h2 : z₀.re < 5 / 4) :
    Integrable fun t : ℝ => lineTransform f t * gPair z₀ (((5 / 4 : ℝ) : ℂ) + t * I) := by
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  set kn : ℝ → ℂ := fun u => k (-u) with hkn
  have hknd : ContDiff ℝ 2 kn := hkd.comp contDiff_neg
  have hknc : HasCompactSupport kn := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  obtain ⟨C, -, hC⟩ := norm_Hfn_le hkd hkc
  obtain ⟨Cn, -, hCn⟩ := norm_Hfn_le hknd hknc
  have hH := differentiable_Hfn hkd hkc
  have hHn := differentiable_Hfn hknd hknc
  have hCs : ∀ σ t : ℝ, 1 - 5 / 4 ≤ σ → σ ≤ 5 / 4 → ‖Hfn k (σ + t * I)‖ ≤ C / (1 + t ^ 2) :=
    fun σ t h1 h2 => hC σ t (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  have hCsn : ∀ σ t : ℝ, 1 - 5 / 4 ≤ σ → σ ≤ 5 / 4 → ‖Hfn kn (σ + t * I)‖ ≤ Cn / (1 + t ^ 2) :=
    fun σ t h1 h2 => hCn σ t (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  have hle : 1 - 5 / 4 ≤ (5 / 4 : ℝ) := by norm_num
  have hne0 : (5 / 4 : ℝ) ≠ z₀.re := ne_of_gt h2
  have hne1 : (5 / 4 : ℝ) ≠ (1 - z₀).re := by simp; linarith
  have i1 := integrable_line_div hH hCs hle le_rfl hne0
  have i2 := integrable_line_div hH hCs hle le_rfl hne1
  have i3 := integrable_line_div hHn hCsn hle le_rfl hne0
  have i4 := integrable_line_div hHn hCsn hle le_rfl hne1
  refine (((i1.add i2).add i3).add i4).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, lineTransform, gPair, hk]
  rw [Hfn_mirror (EF.weilTest f f) (5 / 4) t]
  ring

/-- **Evaluation at a point with `γ ≠ 0`.**  With `ρ² = −γ` and the pole `½ + ρ` in the strip,
`Θ_f(ζ) = Re[((1 + γ²)/(2γ))(H(½ + ρ) + H(½ − ρ))]`. -/
theorem oddSpectralWeight_eq_of_ne {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : circleOrd ζ ≠ 0) {ρ : ℂ} (hρ : ρ ^ 2 = -(circleOrd ζ : ℂ))
    (hρ1 : 1 - 5 / 4 < (1 / 2 + ρ).re) (hρ2 : (1 / 2 + ρ).re < 5 / 4) :
    oddSpectralWeight f ζ =
      (((1 + (circleOrd ζ : ℂ) ^ 2) / (2 * circleOrd ζ)) *
        (Hfn (EF.weilTest f f) (1 / 2 + ρ) + Hfn (EF.weilTest f f) (1 - (1 / 2 + ρ)))).re := by
  set k : ℝ → ℂ := EF.weilTest f f with hk
  have hkd : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  obtain ⟨C, -, hC⟩ := norm_Hfn_le hkd hkc
  have hH := differentiable_Hfn hkd hkc
  have hCs : ∀ σ t : ℝ, 1 - 5 / 4 ≤ σ → σ ≤ 5 / 4 → ‖Hfn k (σ + t * I)‖ ≤ C / (1 + t ^ 2) :=
    fun σ t h1 h2 => hC σ t (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith)
  have hpair₀ := two_line_pair hH (c := 5 / 4) hCs (z₀ := 1 / 2) (by norm_num) (by norm_num)
  have hpairρ := two_line_pair hH (c := 5 / 4) hCs (z₀ := 1 / 2 + ρ) hρ1 hρ2
  have hH0 : Hfn k (1 / 2) = 0 := by
    unfold Hfn
    rw [sub_self, zero_div, hk, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc,
      paperFT_zero_of_odd hodd, zero_mul]
  have hi₀ := integrable_lineTransform_mul_gPair hf hfc (z₀ := 1 / 2) (by norm_num) (by norm_num)
  have hiρ := integrable_lineTransform_mul_gPair hf hfc hρ1 hρ2
  set A : ℂ := -(1 / (circleOrd ζ : ℂ)) / 2 with hA
  set B : ℂ := (1 + (circleOrd ζ : ℂ) ^ 2) / (2 * circleOrd ζ) with hB
  have hsplit : ∀ᵐ t ∂volume, lineTransform f t * oddLineKernel ζ (linePt t) =
      A * (lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I)) +
        B * (lineTransform f t * gPair (1 / 2 + ρ) (((5 / 4 : ℝ) : ℂ) + t * I)) := by
    filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
    rw [oddLineKernel_eq_gPair ht hζ h1 hγ hρ, ← linePt_eq, hA, hB]
    ring
  unfold oddSpectralWeight
  rw [integral_congr_ae hsplit, integral_add (hi₀.const_mul A) (hiρ.const_mul B),
    integral_const_mul, integral_const_mul, mul_add, mul_left_comm, mul_left_comm (1 / (2 * Real.pi : ℂ))]
  have e₀ : (1 / (2 * Real.pi) : ℂ) *
      ∫ t, lineTransform f t * gPair (1 / 2) (((5 / 4 : ℝ) : ℂ) + t * I) =
      Hfn k (1 / 2) + Hfn k (1 - 1 / 2) := by rw [← hpair₀]; rfl
  have eρ : (1 / (2 * Real.pi) : ℂ) *
      ∫ t, lineTransform f t * gPair (1 / 2 + ρ) (((5 / 4 : ℝ) : ℂ) + t * I) =
      Hfn k (1 / 2 + ρ) + Hfn k (1 - (1 / 2 + ρ)) := by rw [← hpairρ]; rfl
  rw [e₀, eρ, show (1 : ℂ) - 1 / 2 = 1 / 2 by norm_num, hH0, add_zero, mul_zero, zero_add]

/-- The transform of an odd autocorrelation at a real shift of the centre:
`H(½ + r) = −|f̂(ir)|²`. -/
theorem Hfn_weilTest_half_add_ofReal {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hodd : ∀ x, f (-x) = -f x) (r : ℝ) :
    Hfn (EF.weilTest f f) ((1 / 2 : ℂ) + r) = -((‖paperFT f (I * r)‖ ^ 2 : ℝ) : ℂ) := by
  unfold Hfn
  have e : ((1 / 2 : ℂ) + r - 1 / 2) / I = -(I * r) := by
    rw [add_sub_cancel_left, div_eq_mul_inv, Complex.inv_I]; ring
  rw [e, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, map_neg, map_mul, Complex.conj_I,
    Complex.conj_ofReal, neg_mul, neg_neg, paperFT_neg_of_odd hodd, neg_mul, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **On the critical ordinates** (`γ > 0`): `Θ_f(ζ) = (1 + γ²)|f̂(√γ)|²/γ`. -/
theorem oddSpectralWeight_eq_of_pos {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : 0 < circleOrd ζ) :
    oddSpectralWeight f ζ =
      (1 + circleOrd ζ ^ 2) * ‖paperFT f (Real.sqrt (circleOrd ζ))‖ ^ 2 / circleOrd ζ := by
  set γ := circleOrd ζ with hγdef
  set r := Real.sqrt γ with hr
  have hr2 : r ^ 2 = γ := Real.sq_sqrt hγ.le
  have hρ : ((r : ℂ) * I) ^ 2 = -(γ : ℂ) := by
    rw [mul_pow, I_sq, ← Complex.ofReal_pow, hr2]; ring
  rw [oddSpectralWeight_eq_of_ne hf hfc hodd hζ h1 hγ.ne' hρ (by simp; norm_num) (by simp; norm_num)]
  have ha : (1 / 2 : ℂ) + (r : ℂ) * I = ((1 / 2 : ℝ) : ℂ) + r * I := by push_cast; ring
  have hb : (1 : ℂ) - (1 / 2 + (r : ℂ) * I) = ((1 / 2 : ℝ) : ℂ) - r * I := by push_cast; ring
  rw [ha, hb, Hfn_weilTest_critical hf.continuous hfc, Hfn_weilTest_critical_neg hf.continuous hfc,
    paperFT_neg_of_odd hodd, norm_neg]
  have e : ((1 + (γ : ℂ) ^ 2) / (2 * γ)) *
      (((‖paperFT f r‖ ^ 2 : ℝ) : ℂ) + ((‖paperFT f r‖ ^ 2 : ℝ) : ℂ)) =
      (((1 + γ ^ 2) * ‖paperFT f r‖ ^ 2 / γ : ℝ) : ℂ) := by
    have hγ0 : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    push_cast
    field_simp
    ring
  rw [e, Complex.ofReal_re]

/-- **On the cut** (`−¼ ≤ γ < 0`): `Θ_f(ζ) = (1 + γ²)|f̂(i√(−γ))|²/(−γ)`. -/
theorem oddSpectralWeight_eq_of_neg {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1)
    (hγ : -(1 / 4) ≤ circleOrd ζ) (hγ' : circleOrd ζ < 0) :
    oddSpectralWeight f ζ =
      (1 + circleOrd ζ ^ 2) * ‖paperFT f (I * Real.sqrt (-circleOrd ζ))‖ ^ 2 / (-circleOrd ζ) := by
  set γ := circleOrd ζ with hγdef
  set r := Real.sqrt (-γ) with hr
  have hr2 : r ^ 2 = -γ := Real.sq_sqrt (by linarith)
  have hρ : ((r : ℂ)) ^ 2 = -(γ : ℂ) := by rw [← Complex.ofReal_pow, hr2]; push_cast; ring
  have hr12 : r ≤ 1 / 2 := by
    rw [hr, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  rw [oddSpectralWeight_eq_of_ne hf hfc hodd hζ h1 hγ'.ne hρ (by simp; linarith)
    (by simp; linarith)]
  have hb : (1 : ℂ) - (1 / 2 + (r : ℂ)) = (1 / 2 : ℂ) + ((-r : ℝ) : ℂ) := by push_cast; ring
  rw [hb, Hfn_weilTest_half_add_ofReal hf hfc hodd, Hfn_weilTest_half_add_ofReal hf hfc hodd]
  have hneg : paperFT f (I * ((-r : ℝ) : ℂ)) = -paperFT f (I * r) := by
    rw [← paperFT_neg_of_odd hodd]; congr 1; push_cast; ring
  rw [hneg, norm_neg]
  have e : ((1 + (γ : ℂ) ^ 2) / (2 * γ)) *
      (-((‖paperFT f (I * r)‖ ^ 2 : ℝ) : ℂ) + -((‖paperFT f (I * r)‖ ^ 2 : ℝ) : ℂ)) =
      (((1 + γ ^ 2) * ‖paperFT f (I * r)‖ ^ 2 / (-γ) : ℝ) : ℂ) := by
    have hγ0 : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ'.ne
    push_cast
    field_simp
    ring
  rw [e, Complex.ofReal_re]

/-! ## The centre `ζ = −1` by continuity -/

theorem circleOrd_bdryPt (γ : ℝ) : circleOrd (bdryPt γ) = γ := by
  unfold circleOrd bdryPt discPt
  have hd : (2 * ((1 / 2 : ℂ) + γ * I) + 1) ≠ 0 := bdry_two_mul_add_one_ne_zero γ
  have e : (1 + (2 * ((1 / 2 : ℂ) + γ * I) - 3) / (2 * ((1 / 2 : ℂ) + γ * I) + 1)) /
      (1 - (2 * ((1 / 2 : ℂ) + γ * I) - 3) / (2 * ((1 / 2 : ℂ) + γ * I) + 1)) = γ * I := by
    field_simp
    ring
  rw [e]
  simp

theorem bdryPt_ne_one (γ : ℝ) : bdryPt γ ≠ 1 := by
  intro h
  have hd : (2 * ((1 / 2 : ℂ) + γ * I) + 1) ≠ 0 := bdry_two_mul_add_one_ne_zero γ
  unfold bdryPt discPt at h
  rw [div_eq_one_iff_eq hd] at h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem bdryPt_zero : bdryPt 0 = -1 := by
  unfold bdryPt discPt
  norm_num

theorem continuous_bdryPt : Continuous bdryPt := by
  have heq : bdryPt = fun γ : ℝ => (2 * ((1 / 2 : ℂ) + γ * I) - 3) / (2 * ((1 / 2 : ℂ) + γ * I) + 1) :=
    rfl
  rw [heq]
  exact Continuous.div (by fun_prop) (by fun_prop) fun γ => bdry_two_mul_add_one_ne_zero γ

theorem measurable_oddLineKernel_linePt (ζ : ℂ) :
    Measurable fun t : ℝ => oddLineKernel ζ (linePt t) := by
  have hw : Measurable linePt := continuous_linePt.measurable
  have hs : Measurable fun t : ℝ => (1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2 :=
    measurable_const.sub (measurable_const.mul ((hw.sub measurable_const).pow_const 2))
  have hd : Measurable fun t : ℝ => discPt ((1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2) := by
    have e : (fun t : ℝ => discPt ((1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2)) =
        fun t => (2 * ((1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2) - 3) /
          (2 * ((1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2) + 1) := rfl
    rw [e]
    exact ((measurable_const.mul hs).sub measurable_const).div
      ((measurable_const.mul hs).add measurable_const)
  have e : (fun t : ℝ => oddLineKernel ζ (linePt t)) =
      fun t => I * ((ζ + discPt ((1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2)) /
        (ζ - discPt ((1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2))) / (linePt t - 1 / 2) := rfl
  rw [e]
  exact (measurable_const.mul ((measurable_const.add hd).div (measurable_const.sub hd))).div
    (hw.sub measurable_const)

/-- The kernel is continuous in `ζ` at `ζ = −1` for `t ≠ 0`. -/
theorem continuousAt_oddLineKernel_neg_one {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (fun ζ : ℂ => oddLineKernel ζ (linePt t)) (-1) := by
  set w : ℂ := discPt ((1 / 2 : ℂ) - I * (linePt t - 1 / 2) ^ 2) with hw
  have hne : (-1 : ℂ) - w ≠ 0 := by
    intro h
    have hw1 : w = -1 := by linear_combination -h
    have hs0 := two_mul_chart_add_one_ne_zero t
    rw [linePt_sub_half] at hs0
    have := congrArg halfPt hw1
    rw [hw, linePt_sub_half, halfPt_discPt hs0] at this
    have h2 := congrArg Complex.re this
    have h3 := congrArg Complex.im this
    simp [halfPt, lineA_sq_re, lineA_sq_im] at h2 h3
    norm_num at h2 h3
    nlinarith [sq_nonneg t]
  have e : (fun ζ : ℂ => oddLineKernel ζ (linePt t)) =
      fun ζ => I * ((ζ + w) / (ζ - w)) / (linePt t - 1 / 2) := rfl
  rw [e]
  refine ContinuousAt.div (continuousAt_const.mul (ContinuousAt.div ?_ ?_ hne)) continuousAt_const
    (by rw [linePt_sub_half]; exact lineA_ne_zero t)
  · exact continuousAt_id.add continuousAt_const
  · exact continuousAt_id.sub continuousAt_const

/-- `Θ_f(−1) ≥ 0`: limit of the values on the critical ordinates `γ = 1/(n+1)`. -/
theorem oddSpectralWeight_neg_one_nonneg {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hodd : ∀ x, f (-x) = -f x) :
    0 ≤ oddSpectralWeight f (-1) := by
  set ζn : ℕ → ℂ := fun n => bdryPt (1 / ((n : ℝ) + 1)) with hζn
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hseq : Tendsto ζn atTop (𝓝 (-1)) := by
    rw [← bdryPt_zero]
    exact continuous_bdryPt.continuousAt.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hval : ∀ n, 0 ≤ oddSpectralWeight f (ζn n) := by
    intro n
    rw [oddSpectralWeight_eq_of_pos hf hfc hodd (norm_bdryPt _) (bdryPt_ne_one _)
      (by rw [circleOrd_bdryPt]; exact hpos n)]
    rw [circleOrd_bdryPt]
    positivity
  obtain ⟨D, hD0, hD⟩ := exists_norm_lineTransform_le hf hfc
  have hFc := continuous_lineTransform hf hfc
  have hlim : Tendsto (fun n => oddSpectralWeight f (ζn n)) atTop
      (𝓝 (oddSpectralWeight f (-1))) := by
    unfold oddSpectralWeight
    refine (Complex.continuous_re.tendsto _).comp (Tendsto.const_mul _ ?_)
    refine tendsto_integral_of_dominated_convergence
      (fun t => 2 * D / (1 + t ^ 2) ^ 2 * (44 * (1 + t ^ 2))) ?_ ?_ ?_ ?_
    · intro n
      exact (hFc.measurable.mul (measurable_oddLineKernel_linePt _)).aestronglyMeasurable
    · have : Integrable fun t : ℝ => 2 * D * 44 * (1 + t ^ 2)⁻¹ :=
        integrable_inv_one_add_sq.const_mul _
      refine this.congr (Eventually.of_forall fun t => ?_)
      field_simp
    · intro n
      filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      rw [norm_mul]
      exact mul_le_mul (hD t) (norm_oddLineKernel_le ht (norm_bdryPt _)
        (Or.inr (by rw [circleOrd_bdryPt]; linarith [hpos n]))) (norm_nonneg _) (by positivity)
    · filter_upwards [WeilHerglotz.ae_ne_real 0] with t ht
      exact Tendsto.const_mul _ ((continuousAt_oddLineKernel_neg_one ht).tendsto.comp hseq)
  exact ge_of_tendsto' hlim hval

/-- **The spectral weight is nonnegative on the support.** -/
theorem oddSpectralWeight_nonneg {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hodd : ∀ x, f (-x) = -f x) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hs : ζ = 1 ∨ -(1 / 4) ≤ circleOrd ζ) : 0 ≤ oddSpectralWeight f ζ := by
  by_cases h1 : ζ = 1
  · rw [h1, oddSpectralWeight_one hf hfc]
  · have hγ : -(1 / 4) ≤ circleOrd ζ := hs.resolve_left h1
    by_cases h0 : circleOrd ζ = 0
    · have : ζ = -1 := by rw [eq_bdryPt_circleOrd hζ h1, h0, bdryPt_zero]
      rw [this]
      exact oddSpectralWeight_neg_one_nonneg hf hfc hodd
    · rcases lt_or_gt_of_ne h0 with hneg | hpos
      · rw [oddSpectralWeight_eq_of_neg hf hfc hodd hζ h1 hγ hneg]
        exact div_nonneg (by positivity) (by linarith)
      · rw [oddSpectralWeight_eq_of_pos hf hfc hodd hζ h1 hpos]
        positivity

/-! ## The odd Herglotz bridge -/

/-- **A slit continuation with the sign law makes the weights odd Weil-positive.** -/
theorem weilPositiveOdd_of_slit {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    {Ψ : ℂ → ℂ} (hΨd : DifferentiableOn ℂ Ψ oddWeilSlitDomain)
    (hΨe : ∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s)
    (hΨs : ∀ s : ℂ, 1 / 2 < s.re → s.im ≠ 0 → 0 ≤ s.im * (((s - 1 / 2) * Ψ s).im)) :
    WeilPositiveOdd lam := by
  obtain ⟨ν, hfin, c, hsupp, hrep⟩ := exists_nevanlinna_measure_of_slit hΨd hΨe hΨs
  intro f hf hfc hodd
  rw [re_weilFullFunctional_eq_integral_oddSpectralWeight hsl hΨd hΨe hsupp hrep hf hfc hodd]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_support_of_measure_eq_zero hsupp] with θ hθ
  exact oddSpectralWeight_nonneg hf hfc hodd (norm_circleMap_one θ) hθ

/-- **The odd Weil cone is the set of weights with a slit continuation obeying the
squared-variable sign law.** -/
theorem weilPositiveOdd_iff_exists_slit {lam : ℕ → ℝ} :
    WeilPositiveOdd lam ↔
      (∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) ∧
      ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ oddWeilSlitDomain ∧
        (∀ s : ℂ, 1 < s.re → Ψ s = weilFunction lam s) ∧
        ∀ s : ℂ, 1 / 2 < s.re → s.im ≠ 0 → 0 ≤ s.im * (((s - 1 / 2) * Ψ s).im) := by
  constructor
  · intro hW
    refine ⟨fun σ hσ => OddSector.summable_abs_div_rpow_of_weilPositiveOddAt_anyWeight
      (weilPositiveOddAt_one_iff.mpr hW) hσ, ?_⟩
    obtain ⟨Ψ, hΨd, hΨe, hΨs⟩ := exists_weilFunction_slit_continuation hW
    exact ⟨Ψ, hΨd, hΨe, hΨs⟩
  · rintro ⟨hsl, Ψ, hΨd, hΨe, hΨs⟩
    exact weilPositiveOdd_of_slit hsl hΨd hΨe hΨs

end RHTower.OddResolvent
