import GaloisForLFunctions.RHTower.SoninExtendedFunctionalEquation
import GaloisForLFunctions.RHTower.SoninEntireMellin

/-!
# Burnol's Proposition 2.2

For a vector `f` of the extended Sonine space `L_a` the Mellin transform `M(f)` is meromorphic on
the whole plane with at most simple poles, and those poles can only be at `s = 0` and `s = 1`.  The
statement is packaged as: `s(1-s)·M(f)(s)` extends to an **entire** function.

Right of the critical line the continuation is the tail continuation plus the explicit head
`d·a^{1-s}/(1-s)` (`d` the physical head of `f`); left of it the functional equation replaces
`M(f)(s)` by `χ(s)·[c·a^s/s + (tail of F₊f at 1-s)]` (`c` the Fourier head), which is holomorphic on
`Re s < 1` except for the simple pole of `1/s`.  The two agree on `0 < Re s < 1/2` by the extended
functional equation, so `glueVert` assembles them.

## Main results

* `exists_entire_extendedMellin` — **Burnol's Proposition 2.2**
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The numerator of the continued Mellin transform, right of the critical line. -/
def extendedMellinNumeratorRight (a : ℝ) (c d : ℂ) (f : SoninL2) (s : ℂ) : ℂ :=
  s * (1 - s) * extendedTailMellin a c f s + s * (d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s))

/-- The numerator of the continued Mellin transform, left of the critical line. -/
def extendedMellinNumeratorLeft (a : ℝ) (c d : ℂ) (f : SoninL2) (s : ℂ) : ℂ :=
  (1 - s) * burnolChiFactor s
    * (c * ((a : ℝ) : ℂ) ^ s + s * extendedTailMellin a d (fourierUnitary f) (1 - s))

/-- The numerator `s(1-s)·M(f)(s)` of the continued Mellin transform. -/
def extendedMellinNumerator (a : ℝ) (c d : ℂ) (f : SoninL2) : ℂ → ℂ :=
  glueVert (extendedMellinNumeratorLeft a c d f) (extendedMellinNumeratorRight a c d f) (1 / 2)

/-- **Burnol's Proposition 2.2, with the heads named.**  The numerator `s(1-s)·M(f)(s)` is entire. -/
theorem differentiable_extendedMellinNumerator {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    Differentiable ℂ (extendedMellinNumerator a c d f) ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        s * (1 - s) * (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
          = extendedMellinNumerator a c d f s := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hdF : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary (fourierUnitary f) : SoninL2) : ℝ → ℂ) u = d := by
    rw [hff]
    exact hd
  set R : ℂ → ℂ := extendedMellinNumeratorRight a c d f with hRdef
  set L : ℂ → ℂ := extendedMellinNumeratorLeft a c d f with hLdef
  -- holomorphy of the right piece
  have hRdiff : DifferentiableOn ℂ R {v : ℂ | 0 < v.re} := by
    have h1 : DifferentiableOn ℂ (fun s : ℂ => s * (1 - s)) {v : ℂ | 0 < v.re} :=
      (differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)).differentiableOn
    have h2 : DifferentiableOn ℂ (fun s : ℂ => s * (d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)))
        {v : ℂ | 0 < v.re} := by
      intro s _
      refine DifferentiableAt.differentiableWithinAt ?_
      refine differentiableAt_id.mul ?_
      refine (differentiableAt_const d).mul ?_
      exact DifferentiableAt.const_cpow
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) (Or.inl hane)
    exact (h1.mul (differentiableOn_extendedTailMellin ha hc)).add h2
  -- holomorphy of the left piece
  have hLdiff : DifferentiableOn ℂ L {v : ℂ | v.re < 1} := by
    intro s hs
    have hs1 : s.re < 1 := hs
    refine DifferentiableAt.differentiableWithinAt ?_
    have hchi : DifferentiableAt ℂ burnolChiFactor s := differentiableAt_burnolChiFactor hs1
    have hpow : DifferentiableAt ℂ (fun z : ℂ => ((a : ℝ) : ℂ) ^ z) s :=
      DifferentiableAt.const_cpow differentiableAt_id (Or.inl hane)
    have hsub : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
      (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
    have hre : (0 : ℝ) < ((1 : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    have htail : DifferentiableAt ℂ
        (fun z : ℂ => extendedTailMellin a d (fourierUnitary f) (1 - z)) s := by
      have hbase : DifferentiableAt ℂ (extendedTailMellin a d (fourierUnitary f)) (1 - s) :=
        (differentiableOn_extendedTailMellin ha hdF).differentiableAt (hopen.mem_nhds hre)
      simpa [Function.comp_def] using hbase.comp s hsub
    exact (hsub.mul hchi).mul (((differentiableAt_const c).mul hpow).add
      (differentiableAt_id.mul htail))
  -- the two agree on the strip
  have hagree : ∀ v : ℂ, 0 < v.re → v.re < 1 / 2 → L v = R v := by
    intro s hs0 hs
    have hs1 : s.re < 1 := by linarith
    have hne : (1 : ℂ) - s ≠ 0 := by
      intro h
      have hre : ((1 : ℂ) - s).re = 0 := by rw [h]; simp
      rw [Complex.sub_re, Complex.one_re] at hre
      linarith
    have hsne : s ≠ 0 := by
      intro h
      rw [h] at hs0
      simp at hs0
    have hzre : 1 / 2 < ((1 : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hzre1 : ((1 : ℂ) - s).re < 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    -- the right-hand side of the functional equation
    have hsplit := integral_split_extendedMellin (f := fourierUnitary f) ha hc hzre hzre1
    have hone : (1 : ℂ) - ((1 : ℂ) - s) = s := by ring
    rw [hone] at hsplit
    have htail := extendedTailMellin_eq (f := fourierUnitary f) ha hdF hzre
    have hRHS : soninMellinIntegral (fourierUnitary f) (1 - s)
        = c * ((a : ℝ) : ℂ) ^ s / s + extendedTailMellin a d (fourierUnitary f) (1 - s) := by
      rw [soninMellinIntegral, htail]
      exact hsplit
    -- the extended functional equation
    have hFE := extendedFullMellin_functional_equation ha hev hc hs0 hs
    rw [hRHS] at hFE
    -- the near-zero head of `f`
    have hhead : (∫ t in Set.Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t)
        = d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s) := by
      rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo]
      exact integral_head_of_mem_extended ha hd hs1
    rw [extendedFullMellin, hhead] at hFE
    field_simp at hFE
    rw [hRdef, hLdef, extendedMellinNumeratorRight, extendedMellinNumeratorLeft]
    linear_combination -hFE
  refine ⟨?_, ?_⟩
  · rw [extendedMellinNumerator, ← hLdef, ← hRdef]
    refine differentiable_glueVert (c₁ := 0) (c₂ := 1 / 2) (by norm_num)
      (hLdiff.mono ?_) hRdiff hagree
    intro v hv
    have : v.re < 1 / 2 := hv
    exact lt_trans this (by norm_num)
  · intro s hs hs1
    have hglue : extendedMellinNumerator a c d f s = R s := by
      rw [extendedMellinNumerator, hRdef, glueVert,
        if_neg (by exact not_lt.2 (le_of_lt hs))]
    rw [hglue, hRdef, extendedMellinNumeratorRight]
    have hne : (1 : ℂ) - s ≠ 0 := by
      intro h
      have hre : ((1 : ℂ) - s).re = 0 := by rw [h]; simp
      rw [Complex.sub_re, Complex.one_re] at hre
      linarith
    rw [integral_split_extendedMellin ha hd hs hs1, extendedTailMellin_eq ha hc hs]
    field_simp
    ring

/-- **Burnol's Proposition 2.2.**  `s(1-s)·M(f)(s)` is entire for every vector of `L_a`, so `M(f)`
is meromorphic on `ℂ` with at most simple poles, and only at `s = 0` and `s = 1`. -/
theorem exists_entire_extendedMellin {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninExtendedCarrier a) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
        s * (1 - s) * (∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t) = G s := by
  obtain ⟨d, hd⟩ := ae_eq_of_mem_extended hf
  obtain ⟨c, hc⟩ := ae_fourier_eq_of_mem_extended hf
  obtain ⟨h1, h2⟩ := differentiable_extendedMellinNumerator ha hev hc hd
  exact ⟨extendedMellinNumerator a c d f, h1, h2⟩

end RHTower

end
