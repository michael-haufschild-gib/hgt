import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWRetardedTriangle
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRetardedTriangleGeometry
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceSmooth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularGreen

/-!
# Smoothness of the literal full retarded response

The two compact source triangles admit a fixed parameter square. The smooth
logarithmic radius resolves its characteristic edges before parameter integration.
This gives regularity of the original event integral, including its image term.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.D4BMPWRetardedRegularity
open D4BMModularCore D4BMJointSource D4BMFullAngularCircle
open D4BMFullAngularCausalPeierls D4BMPWRetardedTriangle
open D4BMRetardedTriangleGeometry D4BMNativeResponse

noncomputable section
set_option autoImplicit false

private def chartIntegrand (image : Bool) (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (z : Event × (ℝ × ℝ × ℝ)) : ℂ :=
  let p := Real.exp z.1.1
  let r := p + Real.exp z.1.2
  let alpha := Real.sin z.2.1 ^ (2 : ℕ)
  let beta := Real.sin z.2.2.1 ^ (2 : ℕ)
  let A := p * alpha
  let B := sourceB image p r alpha beta
  ((p * ((if image then p else r) - A) : ℝ) : ℂ) *
    angularMean q branch
      (logarithmicRadius image ![z.1.1, z.1.2, z.2.1, z.2.2.1]) X k *
    timeReducedCoefficient (physicalRate q b) a ((A + B) / 2) ((A - B) / 2)

private theorem chartIntegrand_smooth (image : Bool) (q : XiZeroCopy)
    (branch b : Bool) (a : ℂ) (X k : ℝ) :
    ContDiff ℝ ∞ (chartIntegrand image q branch b a X k) := by
  have hg : ContDiff ℝ ∞ (fun z : Event × (ℝ × ℝ × ℝ) =>
      ![z.1.1, z.1.2, z.2.1, z.2.2.1]) := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  have hr := (logarithmicRadius_smooth image).comp hg
  have hm := (angularMean_smooth q branch X k).comp hr
  have hA : ContDiff ℝ ∞ (fun z : Event × (ℝ × ℝ × ℝ) =>
      Real.exp z.1.1 * Real.sin z.2.1 ^ (2 : ℕ)) := by fun_prop
  have hB : ContDiff ℝ ∞ (fun z : Event × (ℝ × ℝ × ℝ) =>
      sourceB image (Real.exp z.1.1) (Real.exp z.1.1 + Real.exp z.1.2)
        (Real.sin z.2.1 ^ (2 : ℕ)) (Real.sin z.2.2.1 ^ (2 : ℕ))) := by
    cases image <;> unfold sourceB <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals fun_prop
  have hs := (timeReducedCoefficient_smooth (physicalRate q b) a).comp
    (((hA.add hB).div_const 2).prodMk ((hA.sub hB).div_const 2))
  have hE : ContDiff ℝ ∞ (fun z : Event × (ℝ × ℝ × ℝ) => Real.exp z.1.1) := by fun_prop
  have hR : ContDiff ℝ ∞ (fun z : Event × (ℝ × ℝ × ℝ) =>
      if image then Real.exp z.1.1 else Real.exp z.1.1 + Real.exp z.1.2) := by
    cases image
    · exact hE.add (by fun_prop)
    · exact hE
  have hw : ContDiff ℝ ∞ (fun z : Event × (ℝ × ℝ × ℝ) =>
      ((Real.exp z.1.1 * ((if image then Real.exp z.1.1
        else Real.exp z.1.1 + Real.exp z.1.2) -
        Real.exp z.1.1 * Real.sin z.2.1 ^ (2 : ℕ)) : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (hE.mul (hR.sub hA))
  exact (hw.mul hm).mul hs

private def angleChart (z : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (angleMap z.1, angleMap z.2.1, z.2.2)

private theorem angleChart_continuous : Continuous angleChart :=
  (angleMap_continuous.comp continuous_fst).prodMk
    ((angleMap_continuous.comp (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd))

private def chartResponse (q : XiZeroCopy) (branch b : Bool) (a : ℂ)
    (X k : ℝ) (z : Event) : ℂ :=
  ((∫ alpha in (0 : ℝ)..1, ∫ beta in (0 : ℝ)..1, ∫ c in (0 : ℝ)..1,
    chartIntegrand false q branch b a X k (z, angleChart (alpha, beta, c))) -
   (∫ alpha in (0 : ℝ)..1, ∫ beta in (0 : ℝ)..1, ∫ c in (0 : ℝ)..1,
    chartIntegrand true q branch b a X k (z, angleChart (alpha, beta, c)))) / 4

private theorem chartResponse_smooth (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) : ContDiff ℝ ∞ (chartResponse q branch b a X k) :=
  ((unitCube_integral_smooth (chartIntegrand_smooth false q branch b a X k)
      angleChart angleChart_continuous).sub
    (unitCube_integral_smooth (chartIntegrand_smooth true q branch b a X k)
      angleChart angleChart_continuous)).div_const 4

private theorem affine_integral (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b, f x) = ∫ t in (0 : ℝ)..1, ((b - a : ℝ) : ℂ) * f (a + (b - a) * t) := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [mul_zero, mul_one, add_zero, show a + (b - a) = b by ring,
    Complex.real_smul] using
    (intervalIntegral.smul_integral_comp_add_mul (a := (0 : ℝ)) (b := 1) f (b - a) a).symm

private theorem triangle_rescale (f : ℝ → ℝ → ℂ) (p r : ℝ) :
    (∫ u in (0 : ℝ)..p, ∫ v in u..r, f u v) =
      ∫ alpha in (0 : ℝ)..1, ∫ beta in (0 : ℝ)..1,
        ((p * (r - p * alpha) : ℝ) : ℂ) *
          f (p * alpha) (p * alpha + (r - p * alpha) * beta) := by
  rw [affine_integral]
  simp only [sub_zero, zero_add]
  apply intervalIntegral.integral_congr
  intro alpha _
  dsimp only
  rw [affine_integral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro beta _
  dsimp only
  push_cast
  ring

private theorem chartIntegrand_eq (image : Bool) (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (p r X k alpha beta c : ℝ) (hp : 0 < p) (hpr : p < r)
    (ha : alpha ∈ Icc (0 : ℝ) 1) (hb : beta ∈ Icc (0 : ℝ) 1) :
    chartIntegrand image q branch b a X k
      ((Real.log p, Real.log (r - p)), angleChart (alpha, beta, c)) =
      ((p * ((if image then p else r) - p * alpha) : ℝ) : ℂ) *
        triangleDensity q branch b a image p r X k
          (p * alpha, sourceB image p r alpha beta) := by
  dsimp only [chartIntegrand, angleChart]
  rw [Real.exp_log hp, Real.exp_log (sub_pos.mpr hpr),
    show p + (r - p) = r by ring, angleMap_sine_square ha, angleMap_sine_square hb,
    logarithmicRadius_eq image hp hpr ha hb]
  unfold triangleDensity triangleInvariant
  cases image <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_div]
  all_goals ring

private theorem chartResponse_eq (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (p r X k : ℝ) (hp : 0 < p) (hpr : p < r) :
    chartResponse q branch b a X k (Real.log p, Real.log (r - p)) =
      fullRetardedResponse q branch b a ((p + r) / 2) ((p - r) / 2) X k := by
  rw [fullRetardedResponse_eq_triangles q branch b a p r X k hp.le hpr.le]
  unfold chartResponse
  congr 2
  all_goals
    rw [triangle_rescale]
    apply intervalIntegral.integral_congr
    intro alpha ha
    apply intervalIntegral.integral_congr
    intro beta hb
    have ha' : alpha ∈ Icc (0 : ℝ) 1 := by simpa using ha
    have hb' : beta ∈ Icc (0 : ℝ) 1 := by simpa using hb
    simp_rw [chartIntegrand_eq _ q branch b a p r X k alpha beta _ hp hpr ha' hb']
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    rfl

/-- The actual retarded event integral is smooth throughout the physical onset wedge. -/
theorem fullRetardedResponse_contDiffAt (q : XiZeroCopy) (branch b : Bool)
    (a : ℂ) (X k : ℝ) (z : Event) (hp : 0 < z.1 + z.2) (hx : z.2 < 0) :
    ContDiffAt ℝ ∞ (fun w : Event => fullRetardedResponse q branch b a w.1 w.2 X k) z := by
  have hlog : ContDiffAt ℝ ∞ (fun w : Event =>
      (Real.log (w.1 + w.2), Real.log (-2 * w.2))) z := by
    exact ((contDiffAt_fst.add contDiffAt_snd).log hp.ne').prodMk
      ((contDiffAt_const.mul contDiffAt_snd).log (mul_ne_zero (by norm_num) hx.ne))
  have hs := (chartResponse_smooth q branch b a X k).contDiffAt.comp z hlog
  apply hs.congr_of_eventuallyEq
  have hn : ∀ᶠ w : Event in 𝓝 z, 0 < w.1 + w.2 ∧ w.2 < 0 :=
    ((isOpen_lt continuous_const (continuous_fst.add continuous_snd)).inter
      (isOpen_lt continuous_snd continuous_const)).mem_nhds ⟨hp, hx⟩
  filter_upwards [hn] with w hw
  have h := chartResponse_eq q branch b a (w.1 + w.2) (w.1 - w.2) X k hw.1
    (by linarith [hw.2])
  rw [show (w.1 + w.2 + (w.1 - w.2)) / 2 = w.1 by ring,
    show (w.1 + w.2 - (w.1 - w.2)) / 2 = w.2 by ring,
    show w.1 - w.2 - (w.1 + w.2) = -2 * w.2 by ring] at h
  exact h.symm

end
end RHTower.D4BMPWRetardedRegularity
