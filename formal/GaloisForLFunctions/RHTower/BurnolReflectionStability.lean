import GaloisForLFunctions.RHTower.MellinReflectionEquation
import GaloisForLFunctions.RHTower.SoninMellinMultiplier
import GaloisForLFunctions.RHTower.ZetaChiStripGrowth
import GaloisForLFunctions.RHTower.SoninMixedPhysicalBlockNonvanishing
import GaloisForLFunctions.RHTower.SoninBandLimitedShellVanishing

/-!
# Burnol's Lemma 4.10: `𝓛¹` is stable under `F₊`

The reflection `M(f) ↦ M(F₊f)` is multiplication by `χ` composed with `s ↦ 1−s`:

`M(F₊f)(w) = χ(w)·M(f)(1−w)` for every `w` off the real axis.

Left of the critical line this is the definitional functional equation of the numerators; right of
it, it follows from the same identity read at `1−w` together with `χ(w)χ(1−w) = 1`; on the line
itself, by continuity.  Since `χ` has polynomial vertical growth on every strip
(`ZetaChiStripGrowth`), quick decrease is preserved: **the dense subspace of Definition 12 is stable
under the Fourier transform**.

## Main results

* `burnolChiFactor_mul_one_sub`
* `extendedMellinContinuation_reflect_of_im_ne`
* `hasStripRapidDecrease_reflect` — **Lemma 4.10**.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem im_one_sub_ne_zero {s : ℂ} (hs : s.im ≠ 0) : ((1 : ℂ) - s).im ≠ 0 := by
  simp only [Complex.sub_im, Complex.one_im, zero_sub, neg_ne_zero]
  exact hs

/-- **The `χ`-cocycle.**  Off the real axis `χ(s)χ(1−s) = 1`. -/
theorem burnolChiFactor_mul_one_sub {s : ℂ} (hs : s.im ≠ 0) :
    burnolChiFactor s * burnolChiFactor (1 - s) = 1 := by
  have h1 : ((1 : ℂ) - s).im ≠ 0 := im_one_sub_ne_zero hs
  rw [burnolChiFactor_eq_zetaChi hs, burnolChiFactor_eq_zetaChi h1]
  exact zetaChi_mul_one_sub (gammaR_ne_zero_of_im_ne hs) (gammaR_ne_zero_of_im_ne h1)

/-- `χ` is continuous off the real axis. -/
theorem continuousAt_burnolChiFactor {s : ℂ} (hs : s.im ≠ 0) :
    ContinuousAt burnolChiFactor s := by
  have hΓ : ContinuousAt (fun z : ℂ => Complex.Gamma (1 - z)) s := by
    have hne : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n hn
      have := congrArg Complex.im hn
      simp at this
      exact hs this
    have hd : DifferentiableAt ℂ Complex.Gamma (1 - s) := Complex.differentiableAt_Gamma _ hne
    exact ContinuousAt.comp (g := Complex.Gamma) (f := fun z : ℂ => 1 - z) (x := s)
      hd.continuousAt (by fun_prop)
  have hpow : ContinuousAt (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (z - 1)) s := by
    have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
    exact (continuousAt_const_cpow (a := ((2 * Real.pi : ℝ) : ℂ)) hne).comp (by fun_prop)
  have hcos : ContinuousAt (fun z : ℂ => 2 * Complex.cos ((Real.pi : ℂ) * (z - 1) / 2)) s := by
    fun_prop
  have : ContinuousAt (fun z : ℂ => Complex.Gamma (1 - z) * ((2 * Real.pi : ℝ) : ℂ) ^ (z - 1)
      * (2 * Complex.cos ((Real.pi : ℂ) * (z - 1) / 2))) s := (hΓ.mul hpow).mul hcos
  exact this

/-! ## The reflection off the real axis -/

theorem extendedMellinContinuation_reflect_of_im_ne {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {w : ℂ} (hw : w.im ≠ 0) :
    extendedMellinContinuation a d c (fourierUnitary f) w
      = burnolChiFactor w * extendedMellinContinuation a c d f (1 - w) := by
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hleft : ∀ v : ℂ, v.re < 1 / 2 →
      extendedMellinContinuation a d c (fourierUnitary f) v
        = burnolChiFactor v * extendedMellinContinuation a c d f (1 - v) := by
    intro v hv
    have h := extendedMellinContinuation_reflect a d c (fourierUnitary f) hv
    rw [hff] at h
    exact h
  rcases lt_trichotomy w.re (1 / 2) with hlt | heq | hgt
  · exact hleft w hlt
  · -- the critical line, by continuity from the left
    have hev' : fourierUnitary f ∈ evenSubspace := fourierUnitary_mem_evenSubspace hev
    have hc' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
        ((fourierUnitary (fourierUnitary f) : SoninL2) : ℝ → ℂ) u = d := by
      rw [hff]; exact hd
    have hnum' := (differentiable_extendedMellinNumerator ha hev' hc' hc).1
    have hnum := (differentiable_extendedMellinNumerator ha hev hc hd).1
    have hw0 : w ≠ 0 := by
      intro h; rw [h] at hw; simp at hw
    have hw1 : w ≠ 1 := by
      intro h; rw [h] at hw; simp at hw
    have hden : w * (1 - w) ≠ 0 := mul_ne_zero hw0 (sub_ne_zero.2 fun h => hw1 h.symm)
    have hden' : (1 - w) * (1 - (1 - w)) ≠ 0 := by
      have h1 : (1 : ℂ) - w ≠ 0 := sub_ne_zero.2 fun h => hw1 h.symm
      have h2 : (1 : ℂ) - (1 - w) = w := by ring
      rw [h2]
      exact mul_ne_zero h1 hw0
    -- both sides are continuous at `w`
    have hFc : ContinuousAt (extendedMellinContinuation a d c (fourierUnitary f)) w := by
      have hq : ContinuousAt (fun v : ℂ => extendedMellinNumerator a d c (fourierUnitary f) v
          / (v * (1 - v))) w := by
        refine ContinuousAt.div (hnum'.continuous.continuousAt) ?_ hden
        fun_prop
      exact hq
    have hGc : ContinuousAt (fun v : ℂ => burnolChiFactor v
        * extendedMellinContinuation a c d f (1 - v)) w := by
      refine (continuousAt_burnolChiFactor hw).mul ?_
      have hq : ContinuousAt (fun v : ℂ => extendedMellinNumerator a c d f (1 - v)
          / ((1 - v) * (1 - (1 - v)))) w := by
        refine ContinuousAt.div ?_ (by fun_prop) hden'
        exact ContinuousAt.comp (g := extendedMellinNumerator a c d f)
          (f := fun v : ℂ => 1 - v) (x := w) hnum.continuous.continuousAt (by fun_prop)
      exact hq
    -- approach `w` from the left
    set u : ℕ → ℂ := fun n => w - ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hudef
    have hu : Tendsto u atTop (𝓝 w) := by
      have hreal : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 (0:ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hcx : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 (0:ℂ)) := by
        have hcont : Continuous (fun x : ℝ => (x : ℂ)) := Complex.continuous_ofReal
        have hcomp := (hcont.tendsto (0:ℝ)).comp hreal
        simpa [Function.comp_def] using hcomp
      have hsub := (tendsto_const_nhds (x := w) (f := (atTop : Filter ℕ))).sub hcx
      simpa [hudef] using hsub
    have hure : ∀ n : ℕ, (u n).re < 1 / 2 := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have : (u n).re = w.re - 1 / ((n : ℝ) + 1) := by
        rw [hudef]
        simp only [Complex.sub_re, Complex.ofReal_re]
      rw [this, heq]
      linarith
    have hlim1 := hFc.tendsto.comp hu
    have hlim2 := hGc.tendsto.comp hu
    refine tendsto_nhds_unique hlim1 ?_
    refine hlim2.congr fun n => ?_
    exact (hleft (u n) (hure n)).symm
  · -- right of the critical line
    have h1s : ((1 : ℂ) - w).re < 1 / 2 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have h := extendedMellinContinuation_reflect a c d f h1s
    have hback : (1 : ℂ) - (1 - w) = w := by ring
    rw [hback] at h
    have hcocycle := burnolChiFactor_mul_one_sub hw
    calc extendedMellinContinuation a d c (fourierUnitary f) w
        = 1 * extendedMellinContinuation a d c (fourierUnitary f) w := by ring
      _ = (burnolChiFactor w * burnolChiFactor (1 - w))
            * extendedMellinContinuation a d c (fourierUnitary f) w := by rw [hcocycle]
      _ = burnolChiFactor w * (burnolChiFactor (1 - w)
            * extendedMellinContinuation a d c (fourierUnitary f) w) := by ring
      _ = burnolChiFactor w * extendedMellinContinuation a c d f (1 - w) := by rw [← h]

/-! ## Lemma 4.10 -/

/-- **Burnol's Lemma 4.10.**  Quick decrease in vertical strips is preserved by `F₊`. -/
theorem hasStripRapidDecrease_reflect {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    (hrapid : HasStripRapidDecrease (extendedMellinContinuation a c d f)) :
    HasStripRapidDecrease (extendedMellinContinuation a d c (fourierUnitary f)) := by
  intro α β N
  obtain ⟨T₁, N₁, C₁, hC₁, hbound₁⟩ := hasStripPolyGrowthOffReal_zetaChi α β
  obtain ⟨T₂, C₂, hC₂, hbound₂⟩ := hrapid (1 - β) (1 - α) (N + N₁)
  refine ⟨max (max T₁ T₂) 2, C₁ * C₂, by positivity, ?_⟩
  intro s hα hβ hT
  have hT1 : T₁ ≤ |s.im| := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ |s.im| := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT0 : (2 : ℝ) ≤ |s.im| := le_trans (le_max_right _ _) hT
  have hsim : s.im ≠ 0 := by
    intro h
    rw [h] at hT0
    simp at hT0
    linarith
  have hone : ((1 : ℂ) - s).re = 1 - s.re := by simp
  have honeim : |((1 : ℂ) - s).im| = |s.im| := by
    have h : ((1 : ℂ) - s).im = -s.im := by simp
    rw [h, abs_neg]
  have hχ : ‖burnolChiFactor s‖ ≤ C₁ * (1 + |s.im|) ^ N₁ := by
    rw [burnolChiFactor_eq_zetaChi hsim]
    exact hbound₁ s hα hβ hT1
  have hM : ‖extendedMellinContinuation a c d f (1 - s)‖
      ≤ C₂ * (1 + |s.im|) ^ (-((N + N₁ : ℕ) : ℝ)) := by
    have h := hbound₂ (1 - s) (by rw [hone]; linarith) (by rw [hone]; linarith)
      (by rw [honeim]; exact hT2)
    rwa [honeim] at h
  rw [extendedMellinContinuation_reflect_of_im_ne ha hev hc hd hsim, norm_mul]
  have hbase : (0 : ℝ) < 1 + |s.im| := by positivity
  have hsplit : (1 + |s.im|) ^ N₁ * (1 + |s.im|) ^ (-((N + N₁ : ℕ) : ℝ))
      = (1 + |s.im|) ^ (-(N : ℝ)) := by
    rw [← Real.rpow_natCast (1 + |s.im|) N₁, ← Real.rpow_add hbase]
    congr 1
    push_cast
    ring
  calc ‖burnolChiFactor s‖ * ‖extendedMellinContinuation a c d f (1 - s)‖
      ≤ (C₁ * (1 + |s.im|) ^ N₁) * (C₂ * (1 + |s.im|) ^ (-((N + N₁ : ℕ) : ℝ))) := by
        refine mul_le_mul hχ hM (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * ((1 + |s.im|) ^ N₁ * (1 + |s.im|) ^ (-((N + N₁ : ℕ) : ℝ))) := by ring
    _ = C₁ * C₂ * (1 + |s.im|) ^ (-(N : ℝ)) := by rw [hsplit]

/-- **Definition 12's class is stable under `F₊`** — Lemma 4.10 in the form actually used. -/
theorem hasRapidMellin_fourierUnitary {a : ℝ} (ha : 0 < a) {f : SoninL2} (hev : f ∈ evenSubspace)
    (hf : HasRapidMellin a f) : HasRapidMellin a (fourierUnitary f) := by
  obtain ⟨c, d, hc, hd, hrapid⟩ := hf
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  refine ⟨d, c, ?_, hc, hasStripRapidDecrease_reflect ha hev hc hd hrapid⟩
  rw [hff]
  exact hd

end

end RHTower
