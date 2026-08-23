import GaloisForLFunctions.RHTower.SoninFunctionalEquation
import GaloisForLFunctions.HTGeometry.CauchyTransformGluingVertical
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The Mellin transform of an even Sonine vector is entire

The Mellin transform of `f ∈ K_a` is holomorphic on `Re s > 0`, and the `χ`-side of its functional
equation is holomorphic on `Re s < 1`.  The two agree on the strip `0 < Re s < 1/2`, so they glue
to an entire function: Burnol's Theorem 2.1 (arXiv:math/0203120).

The identity theorem on the half-plane `Re s < 1` then upgrades the strip functional equation to
the whole of that half-plane.

## Main results

* `soninEntireMellin`
* `differentiable_soninEntireMellin`
* `soninEntireMellin_eq_soninChiSide`
-/

noncomputable section

open MeasureTheory Set Complex Real Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Burnol's `χ`-factor is holomorphic left of `Re s = 1`. -/
theorem differentiableAt_burnolChiFactor {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ burnolChiFactor s := by
  have h2pi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast ne_of_gt hp
  have hsub : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
    (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  have hne : ∀ m : ℕ, (1 - s) ≠ -(m : ℂ) := by
    intro m hm
    have hre : (1 - s).re = (-(m : ℂ)).re := by rw [hm]
    rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGam : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (1 - z)) s := by
    simpa [Function.comp_def] using (Complex.differentiableAt_Gamma (1 - s) hne).comp s hsub
  have hcpow : DifferentiableAt ℂ (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (z - 1)) s :=
    (differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).const_cpow (Or.inl h2pi)
  have hinner : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) * (z - 1) / 2) s := by
    exact (((differentiableAt_const _).mul
      (differentiableAt_id.sub (differentiableAt_const (1 : ℂ)))).div_const 2)
  have hcos : DifferentiableAt ℂ
      (fun z : ℂ => 2 * Complex.cos ((Real.pi : ℂ) * (z - 1) / 2)) s := by
    have := (Complex.differentiable_cos ((Real.pi : ℂ) * (s - 1) / 2)).comp s hinner
    simpa [Function.comp_def] using this.const_mul (2 : ℂ)
  have hdef : burnolChiFactor = fun z : ℂ => Complex.Gamma (1 - z)
      * ((2 * Real.pi : ℝ) : ℂ) ^ (z - 1)
      * (2 * Complex.cos ((Real.pi : ℂ) * (z - 1) / 2)) := rfl
  rw [hdef]
  exact (hGam.mul hcpow).mul hcos

/-- The `χ`-side of the functional equation. -/
def soninChiSide (f : SoninL2) (a : ℝ) (s : ℂ) : ℂ :=
  burnolChiFactor s * soninMellinExtension (fourierUnitary f) a (1 - s)

/-- The `χ`-side is holomorphic left of `Re s = 1`. -/
theorem differentiableOn_soninChiSide {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninCarrier a) :
    DifferentiableOn ℂ (soninChiSide f a) {v : ℂ | v.re < 1} := by
  have hgcar : fourierUnitary f ∈ centralSoninCarrier a :=
    fourierUnitary_mem_centralSoninCarrier hev hf
  have hopen : IsOpen {v : ℂ | (0 : ℝ) < v.re} := isOpen_lt continuous_const Complex.continuous_re
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have hs1 : s.re < 1 := hs
  have hre : (0 : ℝ) < (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hd : DifferentiableAt ℂ (soninMellinExtension (fourierUnitary f) a) (1 - s) :=
    (differentiableOn_soninMellinExtension ha hgcar.2).differentiableAt (hopen.mem_nhds hre)
  have hsub : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
    (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  have hcomp : DifferentiableAt ℂ
      (fun z : ℂ => soninMellinExtension (fourierUnitary f) a (1 - z)) s := by
    simpa [Function.comp_def] using hd.comp s hsub
  exact (differentiableAt_burnolChiFactor hs1).mul hcomp

/-- **The entire Mellin transform of an even Sonine vector.** -/
def soninEntireMellin (f : SoninL2) (a : ℝ) : ℂ → ℂ :=
  glueVert (soninChiSide f a) (soninMellinExtension f a) (1 / 2)

/-- **Burnol's Theorem 2.1:** the Mellin transform of an even Sonine vector is entire. -/
theorem differentiable_soninEntireMellin {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninCarrier a) :
    Differentiable ℂ (soninEntireMellin f a) := by
  refine differentiable_glueVert (c₁ := 0) (c₂ := 1 / 2) (by norm_num)
    ((differentiableOn_soninChiSide ha hev hf).mono ?_)
    (differentiableOn_soninMellinExtension ha hf.2) ?_
  · intro v hv
    have : v.re < 1 / 2 := hv
    exact lt_trans this (by norm_num)
  · intro v h0 h1
    exact (soninMellinExtension_functional_equation ha hev hf h0 h1).symm

/-- On the physical half-plane the entire transform is the holomorphic continuation. -/
theorem soninEntireMellin_eq_soninMellinExtension {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : 0 < s.re) :
    soninEntireMellin f a s = soninMellinExtension f a s :=
  glueVert_eqOn_right (c₁ := 0)
    (fun _ h0 h1 => (soninMellinExtension_functional_equation ha hev hf h0 h1).symm) hs

/-- Beyond the Mellin abscissa the entire transform is the absolutely convergent integral. -/
theorem soninEntireMellin_eq_soninMellinIntegral {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : 1 / 2 < s.re) :
    soninEntireMellin f a s = soninMellinIntegral f s := by
  rw [soninEntireMellin_eq_soninMellinExtension ha hev hf (by linarith),
    soninMellinExtension_eq_soninMellinIntegral ha hf hs]

/-- The open half-plane `Re s < 1` is preconnected. -/
theorem isPreconnected_re_lt_one : IsPreconnected {v : ℂ | v.re < 1} :=
  (convex_halfSpace_lt ⟨Complex.add_re, fun c z => Complex.smul_re c z⟩ 1).isPreconnected

/-- **The functional equation on the whole half-plane `Re s < 1`.**  The identity theorem
propagates the strip identity `0 < Re s < 1/2` across `Re s < 1`. -/
theorem soninEntireMellin_eq_soninChiSide {a : ℝ} (ha : 0 < a) {f : SoninL2}
    (hev : f ∈ evenSubspace) (hf : f ∈ centralSoninCarrier a) {s : ℂ} (hs : s.re < 1) :
    soninEntireMellin f a s = soninChiSide f a s := by
  have hopen : IsOpen {v : ℂ | v.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have hopenHalf : IsOpen {v : ℂ | v.re < 1 / 2} :=
    isOpen_lt Complex.continuous_re continuous_const
  have hA : AnalyticOnNhd ℂ (soninEntireMellin f a) {v : ℂ | v.re < 1} :=
    (differentiable_soninEntireMellin ha hev hf).differentiableOn.analyticOnNhd hopen
  have hB : AnalyticOnNhd ℂ (soninChiSide f a) {v : ℂ | v.re < 1} :=
    (differentiableOn_soninChiSide ha hev hf).analyticOnNhd hopen
  have hz₀ : (0 : ℂ) ∈ {v : ℂ | v.re < 1} := by
    simp only [Set.mem_setOf_eq, Complex.zero_re]
    norm_num
  have hev₀ : soninEntireMellin f a =ᶠ[𝓝 (0 : ℂ)] soninChiSide f a := by
    have hmem : (0 : ℂ) ∈ {v : ℂ | v.re < 1 / 2} := by
      simp only [Set.mem_setOf_eq, Complex.zero_re]
      norm_num
    filter_upwards [hopenHalf.mem_nhds hmem] with w hw
    exact glueVert_of_lt hw
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_re_lt_one hz₀ hev₀ hs

end RHTower

end
