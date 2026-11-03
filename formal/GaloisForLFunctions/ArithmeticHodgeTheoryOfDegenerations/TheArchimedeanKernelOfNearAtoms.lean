import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRowsOfANearPairSum
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheNearAtomsHaveALogarithmicPairing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheArchimedeanFinitePartIsMinusLogTwoPi

/-!
# The archimedean kernel of near atoms

Two atoms of width `w` at log-distance `wℓ`, `0 ≤ ℓ ≤ 2`, pair through

`Arch(n, j)/(w∫φ²) = (log(1/w) G(ℓ) + K_near(ℓ))/∫φ² + O(w)`
(`abs_atomArchPair_sub_nearKernel_le`),

`K_near(ℓ) = G(ℓ)(κ₀ − log(1 + ℓ)) + ∫_0^{1+ℓ} (2G(ℓ) − G(y − ℓ) − G(y + ℓ))/(2y) dy`,

where `G = φ ⋆ φ` and `κ₀ = 2θ′(0) + c_∞ = −log 2π − γ` (`nearConstant_eq`). The expansion is the
mixed Robin expansion on the common window `w(1 + ℓ)`; the shape term scales with the width and
polarizes into the second difference of `G`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis
open _root_.RHTower (gammaHardyPhaseRate)

/-- The archimedean constant of the near pairing, `κ₀ = 2θ′(0) + c_∞`. -/
def nearConstant : ℝ := 2 * gammaHardyPhaseRate 0 + archRobinConstant

/-- `κ₀ = −log 2π − γ`. -/
theorem nearConstant_eq : nearConstant = -Real.log (2 * π) - Real.eulerMascheroniConstant := by
  have h := finitePart_profileRobin_eq (fun _ : ℝ => (0 : ℝ))
  simp only [profileRobin] at h
  rw [nearConstant]
  linarith

/-- The pair shape: `∫_0^{1+ℓ} (2G(ℓ) − G(y − ℓ) − G(y + ℓ))/(2y) dy`. -/
def nearShape (φ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  ∫ y in Ioc 0 (1 + ℓ),
    (2 * shellAutocorr φ ℓ - shellAutocorr φ (y - ℓ) - shellAutocorr φ (y + ℓ)) / (2 * y)

/-- The near archimedean kernel `K_near(ℓ) = G(ℓ)(κ₀ − log(1 + ℓ)) + shape(ℓ)`. -/
def nearKernel (φ : ℝ → ℝ) (ℓ : ℝ) : ℝ :=
  shellAutocorr φ ℓ * (nearConstant - Real.log (1 + ℓ)) + nearShape φ ℓ

/-! ### The shape term in closed form -/

/-- The product of two shifted increments integrates to the second difference of `G`. -/
theorem integral_increment_mul_increment {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (ℓ y : ℝ) :
    ∫ u, (φ u - φ (u + y)) * (φ (u - ℓ) - φ (u - ℓ + y)) =
      2 * shellAutocorr φ ℓ - shellAutocorr φ (y - ℓ) - shellAutocorr φ (y + ℓ) := by
  have hint : ∀ a b : ℝ, Integrable fun u => φ (u + a) * φ (u + b) := fun a b =>
    ((hφ.comp (continuous_id.add continuous_const)).mul
      (hφ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      ((hφc.comp_homeomorph (Homeomorph.addRight a)).mul_right)
  have hshift : ∀ a b : ℝ, ∫ u, φ (u + a) * φ (u + b) = shellAutocorr φ (b - a) := fun a b => by
    simp only [shellAutocorr, RHTower.ArchimedeanAnomaly.autocorr]
    rw [← integral_add_right_eq_self (fun u => φ u * φ (u + (b - a))) a]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only; ring_nf)
  have e : (fun u => (φ u - φ (u + y)) * (φ (u - ℓ) - φ (u - ℓ + y))) = fun u =>
      φ (u + 0) * φ (u + -ℓ) - φ (u + 0) * φ (u + (y - ℓ)) - φ (u + y) * φ (u + -ℓ) +
        φ (u + y) * φ (u + (y - ℓ)) := by
    funext u; simp only [add_zero, ← sub_eq_add_neg]; ring_nf
  have i1 : Integrable fun u => φ (u + 0) * φ (u + -ℓ) - φ (u + 0) * φ (u + (y - ℓ)) :=
    (hint 0 (-ℓ)).sub (hint 0 (y - ℓ))
  have i2 : Integrable fun u => φ (u + 0) * φ (u + -ℓ) - φ (u + 0) * φ (u + (y - ℓ)) -
      φ (u + y) * φ (u + -ℓ) := i1.sub (hint y (-ℓ))
  rw [e, integral_add i2 (hint y (y - ℓ)), integral_sub i1 (hint y (-ℓ)),
    integral_sub (hint 0 (-ℓ)) (hint 0 (y - ℓ)), hshift, hshift, hshift, hshift]
  have h1 : shellAutocorr φ (-ℓ - 0) = shellAutocorr φ ℓ := by rw [sub_zero, shellAutocorr_neg]
  have h2 : shellAutocorr φ (-ℓ - y) = shellAutocorr φ (y + ℓ) := by
    rw [show -ℓ - y = -(y + ℓ) by ring, shellAutocorr_neg]
  have h3 : shellAutocorr φ (y - ℓ - y) = shellAutocorr φ ℓ := by
    rw [show y - ℓ - y = -ℓ by ring, shellAutocorr_neg]
  rw [h1, h2, h3, sub_zero]
  ring

/-- **Polarization of the shape term.** -/
theorem mixedBumpRobin_eq_integral {f d : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hd : Continuous d) (hdc : HasCompactSupport d) {W : ℝ}
    (hp : IntegrableOn (fun y => (∫ u, ((f u + d u) - (f (u + y) + d (u + y))) ^ 2) / (2 * y))
      (Ioc 0 W))
    (hm : IntegrableOn (fun y => (∫ u, ((-f u + d u) - (-f (u + y) + d (u + y))) ^ 2) / (2 * y))
      (Ioc 0 W)) :
    mixedBumpRobin f d W =
      ∫ y in Ioc 0 W, (∫ u, (f u - f (u + y)) * (d u - d (u + y))) / (2 * y) := by
  have hsq : ∀ y : ℝ, ∀ g : ℝ → ℝ, Continuous g → HasCompactSupport g →
      Integrable fun u => (g u - g (u + y)) ^ 2 := by
    intro y g hg hgc
    have h1 : HasCompactSupport fun u => g (u + y) := hgc.comp_homeomorph (Homeomorph.addRight y)
    have h2 : HasCompactSupport fun u => g u - g (u + y) := hgc.sub h1
    have h3 : HasCompactSupport fun u => (g u - g (u + y)) * (g u - g (u + y)) := h2.mul_left
    have hc : Continuous fun u => g u - g (u + y) :=
      hg.sub (hg.comp (continuous_id.add continuous_const))
    have h4 : Integrable fun u => (g u - g (u + y)) * (g u - g (u + y)) :=
      (hc.mul hc).integrable_of_hasCompactSupport h3
    simpa only [pow_two] using h4
  have hkey : ∀ y : ℝ, (∫ u, ((f u + d u) - (f (u + y) + d (u + y))) ^ 2) -
      (∫ u, ((-f u + d u) - (-f (u + y) + d (u + y))) ^ 2) =
      4 * ∫ u, (f u - f (u + y)) * (d u - d (u + y)) := by
    intro y
    have hP : Integrable fun u => ((f u + d u) - (f (u + y) + d (u + y))) ^ 2 :=
      hsq y (fun u => f u + d u) (hf.add hd) (hfc.add hdc)
    have hM : Integrable fun u => ((-f u + d u) - (-f (u + y) + d (u + y))) ^ 2 :=
      hsq y (fun u => -f u + d u) (hf.neg.add hd) (hfc.neg.add hdc)
    rw [← integral_sub hP hM, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun u => by ring)
  unfold mixedBumpRobin bumpRobin
  rw [← integral_sub hp hm, ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  rw [← sub_div, hkey y]
  ring

section Profile

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

omit hφ hsupp in
/-- The shape integrand of a `C²` function supported in `[0, R]` is integrable near zero. -/
theorem integrableOn_shape_of_support {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) {R : ℝ} (hR : 0 < R)
    (hψs : ∀ u, u ∉ Set.Icc 0 R → ψ u = 0) (W : ℝ) :
    IntegrableOn (fun y => (∫ u, (ψ u - ψ (u + y)) ^ 2) / (2 * y)) (Ioc 0 W) := by
  set χ : ℝ → ℝ := fun v => ψ (R * v) with hχ
  have hχc : ContDiff ℝ 2 χ := hψ.comp (contDiff_const.mul contDiff_id)
  have hχs : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → χ u = 0 := by
    intro u hu
    apply hψs
    intro h
    apply hu
    constructor
    · by_contra hneg; push Not at hneg; nlinarith [h.1]
    · by_contra hneg; push Not at hneg; nlinarith [h.2]
  have hdil : atomDilate χ R = ψ := by
    funext u; simp only [atomDilate, hχ, mul_div_cancel₀ u hR.ne']
  have h := integrableOn_shape_atomDilate hχc hχs (W := W) hR
  rwa [hdil] at h

/-- The shape term of a profile and its translate is the explicit pair shape. -/
theorem mixedBumpRobin_translate_eq_nearShape {ℓ : ℝ} (hℓ : 0 ≤ ℓ) :
    mixedBumpRobin φ (fun u => φ (u - ℓ)) (1 + ℓ) = nearShape φ ℓ := by
  have hc := hφ.continuous
  have hcs : HasCompactSupport φ := hasCompactSupport_profile hsupp
  have hd : Continuous fun u => φ (u - ℓ) := hc.comp (continuous_id.sub continuous_const)
  have hds : HasCompactSupport fun u => φ (u - ℓ) :=
    hcs.comp_homeomorph (Homeomorph.subRight ℓ)
  have hR : (0 : ℝ) < 1 + ℓ := by linarith
  have hsuppR : ∀ a : ℝ, ∀ u, u ∉ Set.Icc 0 (1 + ℓ) → a * φ u + φ (u - ℓ) = 0 := by
    intro a u hu
    have h1 : φ u = 0 := hsupp u (fun h => hu ⟨h.1, by linarith [h.2]⟩)
    have h2 : φ (u - ℓ) = 0 := hsupp (u - ℓ) (fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩)
    rw [h1, h2]; ring
  have hdC : ContDiff ℝ 2 fun u => φ (u - ℓ) := hφ.comp (contDiff_id.sub contDiff_const)
  have hp := integrableOn_shape_of_support (ψ := fun u => φ u + φ (u - ℓ)) (hφ.add hdC) hR
    (fun u hu => by simpa using hsuppR 1 u hu) (1 + ℓ)
  have hm := integrableOn_shape_of_support (ψ := fun u => -φ u + φ (u - ℓ)) (hφ.neg.add hdC)
    hR (fun u hu => by simpa using hsuppR (-1) u hu) (1 + ℓ)
  rw [mixedBumpRobin_eq_integral hc hcs hd hds hp hm, nearShape]
  refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
  congr 1
  rw [← integral_increment_mul_increment hc hcs ℓ y]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring_nf

omit hφ hsupp in
/-- The shape term of two dilated atoms scales with the width. -/
theorem mixedBumpRobin_atomDilate_translate {w : ℝ} (hw : 0 < w) {s : ℝ} (hs : 0 ≤ s) :
    mixedBumpRobin (atomDilate φ w) (fun u => atomDilate φ w (u - s)) (w + s) =
      w * mixedBumpRobin φ (fun u => φ (u - s / w)) (1 + s / w) := by
  have hR : (0 : ℝ) ≤ 1 + s / w := by positivity
  have ep : (fun u => atomDilate φ w u + atomDilate φ w (u - s)) =
      atomDilate (fun v => φ v + φ (v - s / w)) w := by
    funext u; simp only [atomDilate, sub_div]
  have em : (fun u => -atomDilate φ w u + atomDilate φ w (u - s)) =
      atomDilate (fun v => -φ v + φ (v - s / w)) w := by
    funext u; simp only [atomDilate, sub_div]
  have hW : w + s = w * (1 + s / w) := by field_simp
  unfold mixedBumpRobin
  rw [ep, em, hW, bumpRobin_atomDilate_window hw hR, bumpRobin_atomDilate_window hw hR]
  ring

/-- **The near archimedean pairing.** Two atoms at log-distance `s = log(j/n) ∈ [0, 2w]` pair
through `(log(1/w) G(s/w) + K_near(s/w))/∫φ²`, up to `3w`. -/
theorem abs_atomArchPair_sub_nearKernel_le (hM : 0 < ∫ u, φ u ^ 2) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w ≤ 1 / 3) {n j : ℕ} (hs0 : 0 ≤ Real.log j - Real.log n)
    (hs2 : Real.log j - Real.log n ≤ 2 * w) :
    |atomArchPair (atomDilate φ w) n j / (∫ u, atomDilate φ w u ^ 2) -
      (Real.log (1 / w) * shellAutocorr φ ((Real.log j - Real.log n) / w) +
        nearKernel φ ((Real.log j - Real.log n) / w)) / (∫ u, φ u ^ 2)| ≤ 3 * w := by
  set M := ∫ u, φ u ^ 2 with hMdef
  set s := Real.log j - Real.log n with hs
  obtain ⟨hg, hgsupp, -⟩ := atomDilate_facts hφ hsupp hw0
  set g := atomDilate φ w with hgdef
  set d : ℝ → ℝ := fun u => g (u - s) with hd
  set W := w + s with hW
  have hW0 : 0 < W := by linarith
  have hW1 : W ≤ 1 := by linarith
  have hwM : 0 < w * M := mul_pos hw0 hM
  have hdsupp : ∀ u, u ∉ Set.Icc 0 W → d u = 0 := fun u hu =>
    hgsupp _ fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  have hgsuppW : ∀ u, u ∉ Set.Icc 0 W → g u = 0 := fun u hu =>
    hgsupp _ fun h => hu ⟨h.1, by linarith [h.2]⟩
  have hdC : ContDiff ℝ 2 d := hg.comp (contDiff_id.sub contDiff_const)
  have hrobin := abs_mixed_levy_sub_robin_le hg hgsuppW hdC hdsupp hW0 hW1
  have hgM : (∫ u, g u ^ 2) = w * M := integral_atomDilate_sq φ hw0
  have hdM : (∫ u, d u ^ 2) = w * M := by
    rw [← hgM]; exact integral_sub_right_eq_self (fun u => g u ^ 2) s
  have hfd : (∫ u, g u * d u) = w * shellAutocorr φ (s / w) :=
    integral_atomDilate_mul_shift hw0 s
  have hmix : mixedBumpRobin g d W = w * nearShape φ (s / w) := by
    rw [hgdef, hd, hW, mixedBumpRobin_atomDilate_translate hw0 hs0,
      mixedBumpRobin_translate_eq_nearShape hφ hsupp (div_nonneg hs0 hw0.le)]
  have hWlog : Real.log (1 / W) = Real.log (1 / w) - Real.log (1 + s / w) := by
    have : W = w * (1 + s / w) := by rw [hW]; field_simp
    rw [this, one_div, one_div, Real.log_inv, Real.log_inv,
      Real.log_mul hw0.ne' (by positivity : (1 : ℝ) + s / w ≠ 0)]
    ring
  set E := (∫ y in Ioi 0, levyMixed g d y) -
    ((Real.log (1 / W) + archRobinConstant) * (∫ u, g u * d u) + mixedBumpRobin g d W) with hE
  have he : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.abs_exp_sub_one_le (x := 1 / 2) (by norm_num)
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at h
    linarith [le_abs_self (Real.exp (1 / 2) - 1)]
  have hEb : |E| ≤ 3 * w * (w * M) := by
    have h := hrobin
    rw [hgM, hdM] at h
    calc |E| ≤ Real.exp (1 / 2) / 4 * W * (w * M + w * M) := h
      _ ≤ 2 / 4 * (3 * w) * (w * M + w * M) := by
          gcongr
          linarith
      _ = 3 * w * (w * M) := by ring
  have hpair : atomArchPair g n j = 2 * gammaHardyPhaseRate 0 * (∫ u, g u * d u) +
      ∫ y in Ioi 0, levyMixed g d y := by
    rw [atomArchPair_eq_translate g n j]
  have hexpand : atomArchPair g n j = w * (Real.log (1 / w) * shellAutocorr φ (s / w) +
      nearKernel φ (s / w)) + E := by
    rw [hpair, hE, hfd, hmix, hWlog, nearKernel, nearConstant]
    ring
  rw [hexpand, hgM]
  have e : (w * (Real.log (1 / w) * shellAutocorr φ (s / w) + nearKernel φ (s / w)) + E) / (w * M) -
      (Real.log (1 / w) * shellAutocorr φ (s / w) + nearKernel φ (s / w)) / M = E / (w * M) := by
    field_simp; ring
  rw [e, abs_div, abs_of_pos hwM, div_le_iff₀ hwM]
  linarith

end Profile

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
