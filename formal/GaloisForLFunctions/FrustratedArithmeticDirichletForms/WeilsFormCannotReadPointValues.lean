import GaloisForLFunctions.FrustratedArithmeticDirichletForms.TheWindowEnergyHasNoTrace
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.WeilsFormIsContinuousInTheLevyNorm

/-!
# Weil's form cannot read point values

`TheWindowEnergyHasNoTrace` shows that point evaluation is unbounded in the energy norm: a `C²` spike
of height `1` can have arbitrarily small `L²` norm, `L¹` norm and Lévy energy. Weil's form is
continuous in exactly these norms (SSHA, `weilQuad_add_le`). Hence (`exists_spike_weilQuad_close`):
for every test `f` supported in `[−R, R]`, every point `x₀` of the open window and every `ε > 0` there
is a `C²` test `g` supported in `[−R, R]` with `g(x₀) = 1` and `|W(f + g) − W(f)| ≤ ε`.

So no statement about Weil's form on a window can depend on the value of a test at a point — at the
window edge or anywhere else. A window certificate, an extremal, a critical gauge are determined by
the form only up to such spikes; the boundary data the form sees are the logarithmically weighted edge
masses of `TheWindowEnergyHasNoTrace` (review §2.7 Q5).
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.FrustratedArithmeticDirichletForms

open _root_.RHTower
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis (weilQuad SupportedIn primeMass)

/-- The perturbation bound of SSHA's `weilQuad_add_le`, as a function of the norms of the two tests:
`a = ‖f‖₂²`, `L = 𝒥(f)`, `m = |C(f)| + |S(f)|`, `x = ‖d‖₂²`, `y = 𝒥(d)`, `z = ‖d‖₁`. -/
def perturbBound (R a L m x y z : ℝ) : ℝ :=
  2 * |gammaHardyPhaseRate 0| * (2 * (Real.sqrt a * Real.sqrt x) + x) +
    (2 * (Real.sqrt L * Real.sqrt y) + y) +
    2 * primeMass R * (2 * (Real.sqrt a * Real.sqrt x) + x) +
    4 * Real.cosh (R / 2) * m * z + 4 * Real.cosh (R / 2) ^ 2 * z ^ 2

/-- `W(f + d) ≤ W(f) + perturbBound`. -/
theorem weilQuad_add_le_perturbBound {f d : ℝ → ℝ} {R : ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hd : ContDiff ℝ 2 d) (hdc : HasCompactSupport d)
    (hfR : SupportedIn R f) (hdR : SupportedIn R d) :
    weilQuad (fun u => f u + d u) ≤ weilQuad f +
      perturbBound R (∫ u, f u ^ 2) (levyEnergy f) (|coshHalfMoment f| + |sinhHalfMoment f|)
        (∫ u, d u ^ 2) (levyEnergy d) (∫ u, |d u|) := by
  have h := SpacingScaleHarmonicAnalysis.weilQuad_add_le hf hfc hd hdc hfR hdR
  unfold perturbBound
  linarith

/-- The perturbation bound is monotone in every norm and, at small perturbations, is
`√δ M₁ + δ M₂`. -/
theorem perturbBound_le {R a L m x y z δ a' L' m' : ℝ} (ha : 0 ≤ a) (hL : 0 ≤ L) (hm : 0 ≤ m)
    (haa : a ≤ a') (hLL : L ≤ L') (hmm : m ≤ m') (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxδ : x ≤ δ) (hyδ : y ≤ δ) (hzδ : z ≤ δ) (hδ1 : δ ≤ 1) :
    perturbBound R a L m x y z ≤
      Real.sqrt δ * (4 * |gammaHardyPhaseRate 0| * Real.sqrt a' + 2 * Real.sqrt L' +
          4 * primeMass R * Real.sqrt a') +
        δ * (2 * |gammaHardyPhaseRate 0| + 1 + 2 * primeMass R + 4 * Real.cosh (R / 2) * m' +
          4 * Real.cosh (R / 2) ^ 2) := by
  have hP := SpacingScaleHarmonicAnalysis.primeMass_nonneg R
  have hθ := abs_nonneg (gammaHardyPhaseRate 0)
  have hch : 0 ≤ Real.cosh (R / 2) := (Real.cosh_pos _).le
  have hsa : Real.sqrt a ≤ Real.sqrt a' := Real.sqrt_le_sqrt haa
  have hsL : Real.sqrt L ≤ Real.sqrt L' := Real.sqrt_le_sqrt hLL
  have hsx : Real.sqrt x ≤ Real.sqrt δ := Real.sqrt_le_sqrt hxδ
  have hsy : Real.sqrt y ≤ Real.sqrt δ := Real.sqrt_le_sqrt hyδ
  have hz2 : z ^ 2 ≤ δ := by nlinarith
  have h0a := Real.sqrt_nonneg a
  have h0L := Real.sqrt_nonneg L
  have h0x := Real.sqrt_nonneg x
  have h0y := Real.sqrt_nonneg y
  have h0a' := Real.sqrt_nonneg a'
  have h0δ := Real.sqrt_nonneg δ
  have e1 : Real.sqrt a * Real.sqrt x ≤ Real.sqrt a' * Real.sqrt δ := mul_le_mul hsa hsx h0x h0a'
  have e2 : Real.sqrt L * Real.sqrt y ≤ Real.sqrt L' * Real.sqrt δ :=
    mul_le_mul hsL hsy h0y (Real.sqrt_nonneg _)
  have e3 : m * z ≤ m' * δ := mul_le_mul hmm hzδ hz (hm.trans hmm)
  unfold perturbBound
  have t1 := mul_le_mul_of_nonneg_left (show 2 * (Real.sqrt a * Real.sqrt x) + x ≤
    2 * (Real.sqrt a' * Real.sqrt δ) + δ by linarith) (by positivity : 0 ≤ 2 * |gammaHardyPhaseRate 0|)
  have t2 := mul_le_mul_of_nonneg_left (show 2 * (Real.sqrt a * Real.sqrt x) + x ≤
    2 * (Real.sqrt a' * Real.sqrt δ) + δ by linarith) (by positivity : 0 ≤ 2 * primeMass R)
  have t3 : 4 * Real.cosh (R / 2) * m * z ≤ 4 * Real.cosh (R / 2) * (m' * δ) := by
    have := mul_le_mul_of_nonneg_left e3 (by positivity : 0 ≤ 4 * Real.cosh (R / 2))
    linarith
  have t4 := mul_le_mul_of_nonneg_left hz2 (by positivity : 0 ≤ 4 * Real.cosh (R / 2) ^ 2)
  nlinarith

theorem levyEnergy_neg (g : ℝ → ℝ) : levyEnergy (fun u => -g u) = levyEnergy g := by
  unfold levyEnergy
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have e : (fun u => (-g u - -g (u + x)) ^ 2) = fun u => (g u - g (u + x)) ^ 2 := by
    funext u; ring
  simp only [e]

theorem integral_sq_add_le {f g : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∫ u, (f u + g u) ^ 2 ≤ 2 * (∫ u, f u ^ 2) + 2 * ∫ u, g u ^ 2 := by
  have i1 := SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous hf hfc
  have i2 := SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous hg hgc
  have i3 := SpacingScaleHarmonicAnalysis.integrable_sq_of_continuous (hf.add hg) (hfc.add hgc)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
  exact integral_mono i3 ((i1.const_mul 2).add (i2.const_mul 2)) fun u => by
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (f u - g u)]

/-- **Weil's form cannot read point values.** For a `C²` test `f` supported in `[−R, R]`, a point
`x₀` with `|x₀| < R` and `ε > 0`, some `C²` test `g` supported in `[−R, R]` has `g(x₀) = 1` and
`|W(f + g) − W(f)| ≤ ε`. -/
theorem exists_spike_weilQuad_close {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {R x₀ : ℝ} (hfR : SupportedIn R f) (hx₀ : |x₀| < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g x₀ = 1 ∧ SupportedIn R g ∧
      |weilQuad (fun u => f u + g u) - weilQuad f| ≤ ε := by
  set θ := |gammaHardyPhaseRate 0|
  set P := primeMass R
  set ch := Real.cosh (R / 2)
  set a := ∫ u, f u ^ 2
  set L := levyEnergy f
  set m := |coshHalfMoment f| + |sinhHalfMoment f|
  have ha : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  have hL : 0 ≤ L := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' f
  have hm : 0 ≤ m := by positivity
  have hθ : 0 ≤ θ := abs_nonneg _
  have hP : 0 ≤ P := SpacingScaleHarmonicAnalysis.primeMass_nonneg R
  have hch : 0 ≤ ch := (Real.cosh_pos _).le
  set M₁ := 4 * θ * Real.sqrt (2 * a + 2) + 2 * Real.sqrt (2 * L + 2) +
    4 * P * Real.sqrt (2 * a + 2)
  set M₂ := 2 * θ + 1 + 2 * P + 4 * ch * (m + 2 * ch) + 4 * ch ^ 2
  have hM₁ : 0 ≤ M₁ := by positivity
  have hM₂ : 0 ≤ M₂ := by positivity
  set δ := min (R - |x₀|) (min 1 (min ((ε / (2 * (M₁ + 1))) ^ 2) (ε / (2 * (M₂ + 1)))))
  have hδ0 : 0 < δ := lt_min (by linarith) (lt_min one_pos (lt_min (by positivity) (by positivity)))
  have hδR : δ ≤ R - |x₀| := min_le_left _ _
  have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ (ε / (2 * (M₁ + 1))) ^ 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ3 : δ ≤ ε / (2 * (M₂ + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the final estimate `√δ M₁ + δ M₂ ≤ ε`
  have hfinal : Real.sqrt δ * M₁ + δ * M₂ ≤ ε := by
    have hs : Real.sqrt δ ≤ ε / (2 * (M₁ + 1)) := by
      calc Real.sqrt δ ≤ Real.sqrt ((ε / (2 * (M₁ + 1))) ^ 2) := Real.sqrt_le_sqrt hδ2
        _ = ε / (2 * (M₁ + 1)) := Real.sqrt_sq (by positivity)
    have h1 : Real.sqrt δ * M₁ ≤ ε / 2 := by
      calc Real.sqrt δ * M₁ ≤ ε / (2 * (M₁ + 1)) * M₁ :=
            mul_le_mul_of_nonneg_right hs hM₁
        _ ≤ ε / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have h2 : δ * M₂ ≤ ε / 2 := by
      calc δ * M₂ ≤ ε / (2 * (M₂ + 1)) * M₂ := mul_le_mul_of_nonneg_right hδ3 hM₂
        _ ≤ ε / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    linarith
  obtain ⟨g, hg, hgc, hg1, hgs, hg2, hg1n, hgL⟩ := exists_spike x₀ hδ0
  have hgR : SupportedIn R g := fun u hu => hgs u (by
    have := abs_sub_abs_le_abs_sub u x₀
    linarith)
  refine ⟨g, hg, hgc, hg1, hgR, abs_le.mpr ⟨?_, ?_⟩⟩
  · -- lower side: `W(f) = W((f + g) + (−g))`
    have hfg : ContDiff ℝ 2 (fun u => f u + g u) := hf.add hg
    have hfgc : HasCompactSupport (fun u => f u + g u) := hfc.add hgc
    have hfgR : SupportedIn R (fun u => f u + g u) := SpacingScaleHarmonicAnalysis.supportedIn_add hfR hgR
    have hng : ContDiff ℝ 2 (fun u => -g u) := hg.neg
    have hngc : HasCompactSupport (fun u => -g u) := hgc.neg
    have hngR : SupportedIn R (fun u => -g u) := fun u hu => by simp [hgR u hu]
    have h := weilQuad_add_le_perturbBound hfg hfgc hng hngc hfgR hngR
    have heq : (fun u => (f u + g u) + -g u) = f := by funext u; ring
    rw [heq] at h
    -- norms of `f + g` and of `−g`
    have hsq : ∫ u, (f u + g u) ^ 2 ≤ 2 * a + 2 := by
      have := integral_sq_add_le hf.continuous hfc hg.continuous hgc
      linarith
    have hlev : levyEnergy (fun u => f u + g u) ≤ 2 * L + 2 := by
      have h1 := SpacingScaleHarmonicAnalysis.levyEnergy_add_le hf hfc hg hgc
      have hgL0 := SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' g
      have hmul : 2 * (Real.sqrt L * Real.sqrt (levyEnergy g)) ≤ L + levyEnergy g := by
        nlinarith [sq_nonneg (Real.sqrt L - Real.sqrt (levyEnergy g)), Real.sq_sqrt hL,
          Real.sq_sqrt hgL0]
      linarith
    have hmom : |coshHalfMoment (fun u => f u + g u)| + |sinhHalfMoment (fun u => f u + g u)| ≤
        m + 2 * ch := by
      have hCg := SpacingScaleHarmonicAnalysis.abs_moment_le hg.continuous hgc hgR
        (φ := fun u => Real.cosh (u / 2)) (by fun_prop)
        fun u hu => SpacingScaleHarmonicAnalysis.abs_cosh_half_le hu
      have hSg := SpacingScaleHarmonicAnalysis.abs_moment_le hg.continuous hgc hgR
        (φ := fun u => Real.sinh (u / 2)) (by fun_prop)
        fun u hu => SpacingScaleHarmonicAnalysis.abs_sinh_half_le hu
      have hfi : Integrable fun u => f u * Real.cosh (u / 2) :=
        (hf.continuous.mul (by fun_prop : Continuous fun u => Real.cosh (u / 2))).integrable_of_hasCompactSupport hfc.mul_right
      have hgi : Integrable fun u => g u * Real.cosh (u / 2) :=
        (hg.continuous.mul (by fun_prop : Continuous fun u => Real.cosh (u / 2))).integrable_of_hasCompactSupport hgc.mul_right
      have hfs : Integrable fun u => f u * Real.sinh (u / 2) :=
        (hf.continuous.mul (by fun_prop : Continuous fun u => Real.sinh (u / 2))).integrable_of_hasCompactSupport hfc.mul_right
      have hgs' : Integrable fun u => g u * Real.sinh (u / 2) :=
        (hg.continuous.mul (by fun_prop : Continuous fun u => Real.sinh (u / 2))).integrable_of_hasCompactSupport hgc.mul_right
      have eC : coshHalfMoment (fun u => f u + g u) = coshHalfMoment f + coshHalfMoment g := by
        unfold coshHalfMoment
        rw [← integral_add hfi hgi]
        exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)
      have eS : sinhHalfMoment (fun u => f u + g u) = sinhHalfMoment f + sinhHalfMoment g := by
        unfold sinhHalfMoment
        rw [← integral_add hfs hgs']
        exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring)
      have hC' : |coshHalfMoment g| ≤ ch * ∫ u, |g u| := hCg
      have hS' : |sinhHalfMoment g| ≤ ch * ∫ u, |g u| := hSg
      have h1n : ch * ∫ u, |g u| ≤ ch := by
        calc ch * ∫ u, |g u| ≤ ch * 1 := mul_le_mul_of_nonneg_left (hg1n.trans hδ1) hch
          _ = ch := mul_one _
      rw [eC, eS]
      have hmdef : m = |coshHalfMoment f| + |sinhHalfMoment f| := rfl
      have := abs_add_le (coshHalfMoment f) (coshHalfMoment g)
      have := abs_add_le (sinhHalfMoment f) (sinhHalfMoment g)
      linarith
    have hx : (∫ u, (-g u) ^ 2) = ∫ u, g u ^ 2 := by simp only [neg_sq]
    have hz : (∫ u, |-g u|) = ∫ u, |g u| := by simp only [abs_neg]
    rw [hx, hz, levyEnergy_neg] at h
    have hb := perturbBound_le (R := R) (integral_nonneg fun _ => sq_nonneg _)
      (SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' _) (by positivity) hsq hlev hmom
      (integral_nonneg fun _ => sq_nonneg _) (SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' g)
      (integral_nonneg fun _ => abs_nonneg _) hg2 hgL hg1n hδ1
    have hb' : Real.sqrt δ * (4 * θ * Real.sqrt (2 * a + 2) + 2 * Real.sqrt (2 * L + 2) +
        4 * P * Real.sqrt (2 * a + 2)) + δ * (2 * θ + 1 + 2 * P + 4 * ch * (m + 2 * ch) +
          4 * ch ^ 2) = Real.sqrt δ * M₁ + δ * M₂ := rfl
    linarith
  · -- upper side
    have h := weilQuad_add_le_perturbBound hf hfc hg hgc hfR hgR
    have hb := perturbBound_le (R := R) ha hL hm (show a ≤ 2 * a + 2 by linarith)
      (show L ≤ 2 * L + 2 by linarith) (show m ≤ m + 2 * ch by linarith)
      (integral_nonneg fun _ => sq_nonneg _) (SpacingScaleHarmonicAnalysis.levyEnergy_nonneg' g)
      (integral_nonneg fun _ => abs_nonneg _) hg2 hgL hg1n hδ1
    have hb' : Real.sqrt δ * (4 * θ * Real.sqrt (2 * a + 2) + 2 * Real.sqrt (2 * L + 2) +
        4 * P * Real.sqrt (2 * a + 2)) + δ * (2 * θ + 1 + 2 * P + 4 * ch * (m + 2 * ch) +
          4 * ch ^ 2) = Real.sqrt δ * M₁ + δ * M₂ := rfl
    linarith

end GaloisForLFunctions.FrustratedArithmeticDirichletForms
