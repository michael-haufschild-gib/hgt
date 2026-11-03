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

/-! ### The kernel on the window `[0, 2]` -/

/-- The second difference `2G(ℓ) − G(y − ℓ) − G(y + ℓ)`. -/
def secondDiff (φ : ℝ → ℝ) (ℓ y : ℝ) : ℝ :=
  2 * shellAutocorr φ ℓ - shellAutocorr φ (y - ℓ) - shellAutocorr φ (y + ℓ)

theorem abs_secondDiff_le {φ : ℝ → ℝ} {K : NNReal} (hK : LipschitzWith K (shellAutocorr φ))
    (ℓ y : ℝ) : |secondDiff φ ℓ y| ≤ 2 * K * |y| := by
  have h1 := hK.dist_le_mul ℓ (ℓ - y)
  have h2 := hK.dist_le_mul ℓ (ℓ + y)
  rw [Real.dist_eq, Real.dist_eq] at h1 h2
  have e1 : |ℓ - (ℓ - y)| = |y| := by ring_nf
  have e2 : |ℓ - (ℓ + y)| = |y| := by rw [show ℓ - (ℓ + y) = -y by ring, abs_neg]
  rw [e1] at h1; rw [e2] at h2
  have hneg : shellAutocorr φ (y - ℓ) = shellAutocorr φ (ℓ - y) := by
    rw [← shellAutocorr_neg, neg_sub]
  have e : secondDiff φ ℓ y = (shellAutocorr φ ℓ - shellAutocorr φ (ℓ - y)) +
      (shellAutocorr φ ℓ - shellAutocorr φ (ℓ + y)) := by
    rw [secondDiff, hneg, add_comm y ℓ]; ring
  rw [e]
  calc _ ≤ |shellAutocorr φ ℓ - shellAutocorr φ (ℓ - y)| +
        |shellAutocorr φ ℓ - shellAutocorr φ (ℓ + y)| := abs_add_le _ _
    _ ≤ K * |y| + K * |y| := add_le_add h1 h2
    _ = 2 * K * |y| := by ring

theorem abs_secondDiff_div_le {φ : ℝ → ℝ} {K : NNReal} (hK : LipschitzWith K (shellAutocorr φ))
    (ℓ y : ℝ) : |secondDiff φ ℓ y / (2 * y)| ≤ K := by
  rcases eq_or_ne y 0 with h | h
  · subst h; simp
  · rw [abs_div, abs_mul, abs_two, div_le_iff₀ (by positivity)]
    have := abs_secondDiff_le hK ℓ y
    linarith

/-- The second difference is Lipschitz in `ℓ`, uniformly at small `y`: it vanishes at `y = 0` by
symmetry, and its `y`-derivative changes by at most twice the Lipschitz constant of `G′`. -/
theorem abs_secondDiff_sub_le {φ : ℝ → ℝ} (hG : Differentiable ℝ (shellAutocorr φ)) {K₂ : NNReal}
    (hK₂ : LipschitzWith K₂ (deriv (shellAutocorr φ))) (ℓ₁ ℓ₂ : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    |secondDiff φ ℓ₁ y - secondDiff φ ℓ₂ y| ≤ 2 * K₂ * |ℓ₁ - ℓ₂| * y := by
  set G := shellAutocorr φ
  set D : ℝ → ℝ := fun t => secondDiff φ ℓ₁ t - secondDiff φ ℓ₂ t with hD
  set D' : ℝ → ℝ := fun t => (-deriv G (t - ℓ₁) - deriv G (t + ℓ₁)) -
    (-deriv G (t - ℓ₂) - deriv G (t + ℓ₂)) with hD'
  have hsd : ∀ ℓ t : ℝ, HasDerivAt (fun t => secondDiff φ ℓ t)
      (-deriv G (t - ℓ) - deriv G (t + ℓ)) t := by
    intro ℓ t
    have hs : HasDerivAt (fun t => G (t - ℓ)) (deriv G (t - ℓ)) t := by
      have h := HasDerivAt.comp_add_const t (-ℓ) (hG (t + -ℓ)).hasDerivAt
      simpa only [← sub_eq_add_neg] using h
    have ha : HasDerivAt (fun t => G (t + ℓ)) (deriv G (t + ℓ)) t :=
      HasDerivAt.comp_add_const t ℓ (hG (t + ℓ)).hasDerivAt
    have h := ((hasDerivAt_const t (2 * G ℓ)).sub hs).sub ha
    exact (h.congr_deriv (by ring)).congr_of_eventuallyEq
      (Eventually.of_forall fun x => by simp only [secondDiff, Pi.sub_apply, G])
  have hderiv : ∀ t, HasDerivAt D (D' t) t := fun t => (hsd ℓ₁ t).sub (hsd ℓ₂ t)
  have hD0 : D 0 = 0 := by
    have hz : ∀ ℓ : ℝ, secondDiff φ ℓ 0 = 0 := fun ℓ => by
      rw [secondDiff, zero_sub, zero_add]
      have : G (-ℓ) = G ℓ := shellAutocorr_neg ℓ
      simp only [G] at this ⊢
      rw [this]; ring
    simp only [hD, hz, sub_self]
  have hbound : ∀ t ∈ Ico 0 y, ‖D' t‖ ≤ 2 * K₂ * |ℓ₁ - ℓ₂| := by
    intro t _
    have h1 := hK₂.dist_le_mul (t - ℓ₂) (t - ℓ₁)
    have h2 := hK₂.dist_le_mul (t + ℓ₂) (t + ℓ₁)
    rw [Real.dist_eq, Real.dist_eq] at h1 h2
    have e1 : |t - ℓ₂ - (t - ℓ₁)| = |ℓ₁ - ℓ₂| := by ring_nf
    have e2 : |t + ℓ₂ - (t + ℓ₁)| = |ℓ₁ - ℓ₂| := by
      rw [show t + ℓ₂ - (t + ℓ₁) = -(ℓ₁ - ℓ₂) by ring, abs_neg]
    rw [e1] at h1; rw [e2] at h2
    rw [Real.norm_eq_abs]
    have e : D' t = (deriv G (t - ℓ₂) - deriv G (t - ℓ₁)) + (deriv G (t + ℓ₂) - deriv G (t + ℓ₁)) := by
      rw [hD']; ring
    rw [e]
    calc _ ≤ |deriv G (t - ℓ₂) - deriv G (t - ℓ₁)| + |deriv G (t + ℓ₂) - deriv G (t + ℓ₁)| :=
          abs_add_le _ _
      _ ≤ K₂ * |ℓ₁ - ℓ₂| + K₂ * |ℓ₁ - ℓ₂| := add_le_add h1 h2
      _ = 2 * K₂ * |ℓ₁ - ℓ₂| := by ring
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := D) (a := 0) (b := y)
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound y ⟨hy, le_rfl⟩
  rw [hD0, sub_zero, sub_zero, Real.norm_eq_abs] at hmv
  exact hmv

section Kernel

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u : ℝ, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
include hφ hsupp

theorem integrableOn_secondDiff_div (ℓ a W : ℝ) :
    IntegrableOn (fun y => secondDiff φ ℓ y / (2 * y)) (Ioc a W) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  have hG := continuous_shellAutocorr hφ hsupp
  have hnum : Continuous fun y => secondDiff φ ℓ y :=
    (continuous_const.sub (hG.comp (continuous_id.sub continuous_const))).sub
      (hG.comp (continuous_id.add continuous_const))
  have hmeas : AEStronglyMeasurable (fun y => secondDiff φ ℓ y / (2 * y)) volume :=
    (hnum.measurable.div (measurable_const.mul measurable_id)).aestronglyMeasurable
  exact Measure.integrableOn_of_bounded (M := K) measure_Ioc_lt_top.ne hmeas
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_secondDiff_div_le hK ℓ y)

/-- On `[0, 2]` the kernel reads the fixed window `(0, 3]`:
`K_near(ℓ) = G(ℓ)(κ₀ − log 3) + ∫_0^3 (2G(ℓ) − G(y − ℓ) − G(y + ℓ))/(2y) dy`. -/
theorem nearKernel_eq_window {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ2 : ℓ ≤ 2) :
    nearKernel φ ℓ = shellAutocorr φ ℓ * (nearConstant - Real.log 3) +
      ∫ y in Ioc 0 3, secondDiff φ ℓ y / (2 * y) := by
  have hsplit : Ioc (0 : ℝ) 3 = Ioc 0 (1 + ℓ) ∪ Ioc (1 + ℓ) 3 :=
    (Set.Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) (1 + ℓ)) (Ioc (1 + ℓ) 3) :=
    Set.Ioc_disjoint_Ioc_of_le le_rfl
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioc
    (integrableOn_secondDiff_div hφ hsupp ℓ _ _) (integrableOn_secondDiff_div hφ hsupp ℓ _ _)]
  have htail : ∫ y in Ioc (1 + ℓ) 3, secondDiff φ ℓ y / (2 * y) =
      shellAutocorr φ ℓ * (Real.log 3 - Real.log (1 + ℓ)) := by
    have hpt : ∀ y ∈ Ioc (1 + ℓ) 3, secondDiff φ ℓ y / (2 * y) = shellAutocorr φ ℓ * y⁻¹ := by
      intro y hy
      have hy0 : 0 < y := by linarith [hy.1]
      rw [secondDiff, shellAutocorr_eq_zero_of_one_le hφ hsupp (x := y - ℓ) (by linarith [hy.1]),
        shellAutocorr_eq_zero_of_one_le hφ hsupp (x := y + ℓ) (by linarith [hy.1])]
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hpt, ← intervalIntegral.integral_of_le
      (by linarith), intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by linarith) (by norm_num), Real.log_div (by norm_num) (by linarith)]
  rw [htail, nearKernel, nearShape]
  simp only [secondDiff]
  ring

theorem hasCompactSupport_shellAutocorr : HasCompactSupport (shellAutocorr φ) := by
  apply HasCompactSupport.intro (show IsCompact (Set.Icc (-1 : ℝ) 1) from isCompact_Icc)
  intro t ht
  apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
  by_contra h
  exact ht (abs_le.mp (lt_of_not_ge h).le)

theorem abs_shellAutocorr_le' (t : ℝ) : |shellAutocorr φ t| ≤ ∫ u, φ u ^ 2 :=
  abs_bumpCorr_le hφ.continuous (hasCompactSupport_profile hsupp) t

/-- `G′` is Lipschitz. -/
theorem exists_lipschitz_deriv_shellAutocorr :
    ∃ K₂ : NNReal, LipschitzWith K₂ (deriv (shellAutocorr φ)) := by
  have h2 := contDiff_shellAutocorr hφ hsupp
  have h1 : ContDiff ℝ 1 (deriv (shellAutocorr φ)) := h2.deriv'
  exact ContDiff.lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_shellAutocorr hφ hsupp).deriv h1 (by norm_num)

/-- **The near kernel is bounded and Lipschitz on `[0, 2]`.** -/
theorem exists_nearKernel_bounds : ∃ A L : ℝ, 0 ≤ L ∧
    (∀ ℓ ∈ Icc (0 : ℝ) 2, |nearKernel φ ℓ| ≤ A) ∧
    ∀ x ∈ Icc (0 : ℝ) 2, ∀ y ∈ Icc (0 : ℝ) 2, |nearKernel φ x - nearKernel φ y| ≤ L * |x - y| := by
  obtain ⟨K, hK⟩ := exists_lipschitz_shellAutocorr hφ hsupp
  obtain ⟨K₂, hK₂⟩ := exists_lipschitz_deriv_shellAutocorr hφ hsupp
  have hGd : Differentiable ℝ (shellAutocorr φ) :=
    (contDiff_shellAutocorr hφ hsupp).differentiable (by norm_num)
  set M := ∫ u, φ u ^ 2
  set κ := nearConstant - Real.log 3
  have hvol : volume.real (Ioc (0 : ℝ) 3) = 3 := by simp
  refine ⟨M * |κ| + 3 * K, K * |κ| + 3 * K₂, by positivity, ?_, ?_⟩
  · intro ℓ hℓ
    rw [nearKernel_eq_window hφ hsupp hℓ.1 hℓ.2]
    have hI : ‖∫ y in Ioc 0 3, secondDiff φ ℓ y / (2 * y)‖ ≤ K * volume.real (Ioc (0 : ℝ) 3) :=
      norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top fun y _ => by
        rw [Real.norm_eq_abs]; exact abs_secondDiff_div_le hK ℓ y
    rw [Real.norm_eq_abs, hvol] at hI
    calc _ ≤ |shellAutocorr φ ℓ * κ| + |∫ y in Ioc 0 3, secondDiff φ ℓ y / (2 * y)| :=
          abs_add_le _ _
      _ ≤ M * |κ| + K * 3 := by
          rw [abs_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right (abs_shellAutocorr_le' hφ hsupp ℓ)
            (abs_nonneg _)) hI
      _ = M * |κ| + 3 * K := by ring
  · intro x hx y hy
    rw [nearKernel_eq_window hφ hsupp hx.1 hx.2, nearKernel_eq_window hφ hsupp hy.1 hy.2]
    have hdiff : (∫ z in Ioc 0 3, secondDiff φ x z / (2 * z)) -
        (∫ z in Ioc 0 3, secondDiff φ y z / (2 * z)) =
        ∫ z in Ioc 0 3, (secondDiff φ x z - secondDiff φ y z) / (2 * z) := by
      rw [← integral_sub (integrableOn_secondDiff_div hφ hsupp x 0 3)
        (integrableOn_secondDiff_div hφ hsupp y 0 3)]
      refine setIntegral_congr_fun measurableSet_Ioc fun z _ => by ring
    have hI : ‖∫ z in Ioc 0 3, (secondDiff φ x z - secondDiff φ y z) / (2 * z)‖ ≤
        K₂ * |x - y| * volume.real (Ioc (0 : ℝ) 3) := by
      refine norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top fun z hz => ?_
      have hz0 : 0 < z := hz.1
      have h := abs_secondDiff_sub_le hGd hK₂ x y hz0.le
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * z),
        div_le_iff₀ (by positivity)]
      nlinarith
    rw [Real.norm_eq_abs, hvol] at hI
    have hG := hK.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq] at hG
    have e : shellAutocorr φ x * κ + (∫ z in Ioc 0 3, secondDiff φ x z / (2 * z)) -
        (shellAutocorr φ y * κ + ∫ z in Ioc 0 3, secondDiff φ y z / (2 * z)) =
        (shellAutocorr φ x - shellAutocorr φ y) * κ +
          ∫ z in Ioc 0 3, (secondDiff φ x z - secondDiff φ y z) / (2 * z) := by
      rw [← hdiff]; ring
    rw [e]
    calc _ ≤ |(shellAutocorr φ x - shellAutocorr φ y) * κ| +
          |∫ z in Ioc 0 3, (secondDiff φ x z - secondDiff φ y z) / (2 * z)| := abs_add_le _ _
      _ ≤ K * |x - y| * |κ| + K₂ * |x - y| * 3 := by
          rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_right hG (abs_nonneg _)) hI
      _ = (K * |κ| + 3 * K₂) * |x - y| := by ring

/-! ### The integral of the kernel -/

theorem integral_shellAutocorr_neg_one_one :
    ∫ t in (-1 : ℝ)..1, shellAutocorr φ t = (∫ u, φ u) ^ 2 := by
  have h : ∫ t, shellAutocorr φ t = (∫ u, φ u) ^ 2 :=
    integral_bumpAutocorr hφ.continuous (hasCompactSupport_profile hsupp)
  rw [← h, intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_
  apply shellAutocorr_eq_zero_of_one_le_abs hφ hsupp
  by_contra hlt
  push Not at hlt
  exact ht ⟨by linarith [(abs_lt.mp hlt).1], (abs_lt.mp hlt).2.le⟩

theorem integral_shellAutocorr_eq_zero_of_one_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∫ t in a..b, shellAutocorr φ t = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => by
    have : 1 ≤ t := by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at ht; linarith [ht.1]
      · rw [uIcc_of_ge h] at ht; linarith [ht.1]
    exact shellAutocorr_eq_zero_of_one_le hφ hsupp this]
  simp

theorem integral_zero_two_shellAutocorr :
    ∫ t in (0 : ℝ)..2, shellAutocorr φ t = (∫ u, φ u) ^ 2 / 2 := by
  have hcont := continuous_shellAutocorr hφ hsupp
  have hii : ∀ a b : ℝ, IntervalIntegrable (shellAutocorr φ) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have h12 := integral_shellAutocorr_eq_zero_of_one_le hφ hsupp (a := 1) (b := 2) le_rfl
    (by norm_num)
  have hneg : ∫ t in (-1 : ℝ)..0, shellAutocorr φ t = ∫ t in (0 : ℝ)..1, shellAutocorr φ t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1) (shellAutocorr φ)
    simp only [neg_zero] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun t _ => (shellAutocorr_neg t).symm
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hii (-1) 0) (hii 0 1)
  rw [integral_shellAutocorr_neg_one_one hφ hsupp, hneg] at hsum
  rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 1) (hii 1 2), h12, add_zero]
  linarith

/-- The kernel's second difference integrates over `ℓ ∈ [0, 2]` to `∫_{−1}^{y−2} G`. -/
theorem integral_secondDiff_eq {y : ℝ} (hy : 0 ≤ y) :
    ∫ ℓ in (0 : ℝ)..2, secondDiff φ ℓ y = ∫ t in (-1 : ℝ)..(y - 2), shellAutocorr φ t := by
  have hcont := continuous_shellAutocorr hφ hsupp
  have hii : ∀ a b : ℝ, IntervalIntegrable (shellAutocorr φ) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hi1 : IntervalIntegrable (fun ℓ => 2 * shellAutocorr φ ℓ) volume 0 2 :=
    (continuous_const.mul hcont).intervalIntegrable 0 2
  have hi2 : IntervalIntegrable (fun ℓ => shellAutocorr φ (y - ℓ)) volume 0 2 :=
    (hcont.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 2
  have hi3 : IntervalIntegrable (fun ℓ => shellAutocorr φ (y + ℓ)) volume 0 2 :=
    (hcont.comp (continuous_const.add continuous_id)).intervalIntegrable 0 2
  have e : (fun ℓ => secondDiff φ ℓ y) = fun ℓ =>
      2 * shellAutocorr φ ℓ - shellAutocorr φ (y - ℓ) - shellAutocorr φ (y + ℓ) := by
    funext ℓ
    rw [secondDiff, add_comm y ℓ, ← shellAutocorr_neg (y - ℓ), neg_sub]
    ring_nf
  rw [e, intervalIntegral.integral_sub (hi1.sub hi2) hi3, intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, integral_zero_two_shellAutocorr hφ hsupp,
    intervalIntegral.integral_comp_sub_left (shellAutocorr φ) y,
    intervalIntegral.integral_comp_add_left (shellAutocorr φ) y, sub_zero, add_zero]
  have hA := intervalIntegral.integral_add_adjacent_intervals (hii (y - 2) y) (hii y (y + 2))
  have hB := intervalIntegral.integral_add_adjacent_intervals (hii (y - 2) 1) (hii 1 (y + 2))
  have hC := intervalIntegral.integral_add_adjacent_intervals (hii (-1) (y - 2)) (hii (y - 2) 1)
  have hz := integral_shellAutocorr_eq_zero_of_one_le hφ hsupp (a := 1) (b := y + 2) le_rfl
    (by linarith)
  rw [integral_shellAutocorr_neg_one_one hφ hsupp] at hC
  linarith

end Kernel

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
