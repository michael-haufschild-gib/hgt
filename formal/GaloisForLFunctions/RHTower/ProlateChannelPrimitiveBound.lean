import GaloisForLFunctions.RHTower.ProlateAllChannelLeftEndpoint
import GaloisForLFunctions.RHTower.ProlateMeanZeroSource
import GaloisForLFunctions.RHTower.PoissonAbelChannelSplit

/-!
# The channel primitives of the mean-zero prolate source

The Fourier samples of the mean-zero source are the mode itself at two radial scales.  The
exponential substitution turns each channel primitive into a radial primitive of the mode from a
left endpoint that can be pushed out past `2`, where the all-channel estimate applies with no
endpoint term.  The result is a bound on the summed channel primitives, uniform in the endpoint.
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform Real

namespace RHTower

variable {a lamDil lamR mu C : ℝ} {Φ : ℝ → ℝ}

/-- The real part of the source's Fourier transform is the mode at two radial scales. -/
theorem re_fourier_prolateMeanZeroSource (ha : 0 < a) (hlamDil : 0 < lamDil)
    (hΦ : Continuous Φ) (heven : Function.Even Φ)
    (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C)
    (hmu : ∀ x : ℝ, realFourierBandTransform (2 * Real.pi * a ^ 2) Φ x = mu * Φ x) (w : ℝ) :
    (𝓕 (fun y => ((prolateMeanZeroSource a lamDil Φ y : ℝ) : ℂ)) w).re
      = a * mu * (Φ (w / a) - Φ (lamDil * (w / a))) := by
  have hax : a * (w / a) = w := by field_simp
  have h := fourier_prolateMeanZeroSource ha hlamDil hΦ heven hC hC0 (w / a)
  rw [hax] at h
  have hT : ∀ x : ℝ, fourierBandTransform (2 * Real.pi * a ^ 2) (fun t => ((Φ t : ℝ) : ℂ)) x
      = ((mu * Φ x : ℝ) : ℂ) := by
    intro x
    rw [fourierBandTransform_ofReal_even hΦ heven x, hmu x]
  rw [hT, hT] at h
  rw [h]
  push_cast
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im]
  ring

/-- The exponential substitution turns a channel primitive into a radial primitive. -/
theorem integral_comp_scale (hbeta : 0 < lamR) (g : ℝ → ℝ) (X : ℝ) :
    (∫ x in (1 : ℝ)..X, g (lamR * x)) = lamR⁻¹ * ∫ u in (lamR * 1)..(lamR * X), g u := by
  have h := intervalIntegral.integral_comp_mul_left (a := (1 : ℝ)) (b := X) g hbeta.ne'
  rw [h, smul_eq_mul]

/-- **The channel primitive of the mean-zero source is a pair of radial primitives.** -/
theorem channelPrimitive_prolateMeanZeroSource (ha : 0 < a) (hlamDil : 0 < lamDil)
    (hlamR : 0 < lamR) (hΦ : Continuous Φ) (heven : Function.Even Φ)
    (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C)
    (hmu : ∀ x : ℝ, realFourierBandTransform (2 * Real.pi * a ^ 2) Φ x = mu * Φ x)
    (n : ℕ) (t : ℝ) :
    channelPrimitive (prolateMeanZeroSource a lamDil Φ) lamR n t
      = a ^ 2 * mu * (∫ u in (lamR / a * 1)..(lamR / a * Real.exp t), Φ (((n : ℝ) + 1) * u))
        - a ^ 2 * mu / lamDil *
          (∫ u in (lamDil * (lamR / a) * 1)..(lamDil * (lamR / a) * Real.exp t),
            Φ (((n : ℝ) + 1) * u)) := by
  have hf : Integrable (prolateMeanZeroSource a lamDil Φ) :=
    integrable_prolateMeanZeroSource ha hlamDil hΦ hC hC0
  rw [channelPrimitive_eq_integral hf n t]
  set β : ℝ := lamR / a with hβ
  have hβ0 : (0 : ℝ) < β := by rw [hβ]; positivity
  have hlb0 : (0 : ℝ) < lamDil * β := by positivity
  set g : ℝ → ℝ := fun u => Φ (((n : ℝ) + 1) * u) with hg
  have hgc : Continuous g := by
    rw [hg]
    exact hΦ.comp (continuous_const.mul continuous_id)
  have hpt : ∀ x : ℝ, lamR * (𝓕 (fun y => ((prolateMeanZeroSource a lamDil Φ y : ℝ) : ℂ))
        (lamR * x * ((n : ℝ) + 1))).re
      = lamR * a * mu * g (β * x) - lamR * a * mu * g (lamDil * β * x) := by
    intro x
    rw [re_fourier_prolateMeanZeroSource ha hlamDil hΦ heven hC hC0 hmu]
    have h1 : lamR * x * ((n : ℝ) + 1) / a = ((n : ℝ) + 1) * (β * x) := by
      rw [hβ]
      field_simp
    show lamR * (a * mu * (Φ (lamR * x * ((n : ℝ) + 1) / a)
        - Φ (lamDil * (lamR * x * ((n : ℝ) + 1) / a))))
      = lamR * a * mu * Φ (((n : ℝ) + 1) * (β * x))
        - lamR * a * mu * Φ (((n : ℝ) + 1) * (lamDil * β * x))
    rw [h1, show lamDil * (((n : ℝ) + 1) * (β * x)) = ((n : ℝ) + 1) * (lamDil * β * x) by ring]
    ring
  have hi1 : IntervalIntegrable (fun x : ℝ => lamR * a * mu * g (β * x)) volume 1 (Real.exp t) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (hgc.comp (continuous_const.mul continuous_id))
  have hi2 : IntervalIntegrable (fun x : ℝ => lamR * a * mu * g (lamDil * β * x))
      volume 1 (Real.exp t) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (hgc.comp (continuous_const.mul continuous_id))
  rw [intervalIntegral.integral_congr (g := fun x : ℝ =>
      lamR * a * mu * g (β * x) - lamR * a * mu * g (lamDil * β * x)) fun x _ => hpt x,
    intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_comp_scale hβ0 g (Real.exp t), integral_comp_scale hlb0 g (Real.exp t)]
  have hane : a ≠ 0 := ha.ne'
  have hlne : lamDil ≠ 0 := hlamDil.ne'
  have hrne : lamR ≠ 0 := hlamR.ne'
  rw [hβ]
  field_simp

/-- **The summed channel primitives of the mean-zero source are bounded, uniformly in the
endpoint.** -/
theorem tsum_abs_channelPrimitive_prolateMeanZeroSource
    {s cc : ℝ} {R DR DDR : ℝ → ℝ}
    (ha : 0 < a) (hlamDil : 1 ≤ lamDil) (hlamR : 0 < lamR)
    (hΦ : Continuous Φ) (heven : Function.Even Φ)
    (hC : ∀ x : ℝ, |Φ x| ≤ C) (hC0 : 0 ≤ C)
    (hmu : ∀ x : ℝ, realFourierBandTransform (2 * Real.pi * a ^ 2) Φ x = mu * Φ x)
    (hΦR : ∀ u : ℝ, Φ u = Φ 1 * R u)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hcc : 1 ≤ cc)
    (hR : ∀ u : ℝ, HasDerivAt R (DR u) u) (hDR : ∀ u : ℝ, HasDerivAt DR (DDR u) u)
    (hode : ∀ u : ℝ, (u ^ 2 - 1) * DDR u + 2 * u * DR u
      - (s * cc ^ 2 - cc ^ 2 * u ^ 2) * R u = 0)
    (hbeta : 2 ≤ lamR / a) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun n : ℕ => |channelPrimitive (prolateMeanZeroSource a lamDil Φ) lamR n t|) ∧
      ∑' n : ℕ, |channelPrimitive (prolateMeanZeroSource a lamDil Φ) lamR n t|
        ≤ 2 * (a ^ 2 * |mu| * |Φ 1| *
            (2 * (4500 * GaloisForLFunctions.RHTower.exactEnergyBudget s cc R DR 2 /
              (Real.sqrt cc * cc * (lamR / a))))) := by
  have hlamDil0 : (0 : ℝ) < lamDil := by linarith
  set β : ℝ := lamR / a with hβ
  have hβ0 : (0 : ℝ) < β := by linarith
  have hX : (1 : ℝ) ≤ Real.exp t := Real.one_le_exp ht
  have hle1 : β * 1 ≤ β * Real.exp t := by nlinarith
  have hle2 : lamDil * β * 1 ≤ lamDil * β * Real.exp t := by nlinarith
  have hL1 : (2 : ℝ) ≤ β * 1 := by linarith
  have hL2 : (2 : ℝ) ≤ lamDil * β * 1 := by nlinarith
  obtain ⟨hsum1, hbnd1⟩ := tsum_abs_integral_radialProlate_left_le hs0 hs1 hcc hR hDR hode
    hL1 hle1
  obtain ⟨hsum2, hbnd2⟩ := tsum_abs_integral_radialProlate_left_le hs0 hs1 hcc hR hDR hode
    hL2 hle2
  set M : ℝ := GaloisForLFunctions.RHTower.exactEnergyBudget s cc R DR 2 with hMdef
  have hM : (0 : ℝ) ≤ M := Real.sqrt_nonneg _
  have hcc0 : (0 : ℝ) < cc := by linarith
  have hsc : (0 : ℝ) < Real.sqrt cc := Real.sqrt_pos.mpr hcc0
  set A : ℝ := a ^ 2 * |mu| * |Φ 1| with hA
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  set Bnd : ℝ := 2 * (4500 * M / (Real.sqrt cc * cc * β)) with hBnd
  have hBnd0 : (0 : ℝ) ≤ Bnd := by rw [hBnd]; positivity
  -- pointwise bound
  have hterm : ∀ n : ℕ,
      |channelPrimitive (prolateMeanZeroSource a lamDil Φ) lamR n t|
        ≤ A * |∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u)|
          + A * |∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u)| := by
    intro n
    rw [channelPrimitive_prolateMeanZeroSource ha hlamDil0 hlamR hΦ heven hC hC0 hmu n t, ← hβ]
    have hrw : ∀ L X : ℝ, (∫ u in L..X, Φ (((n : ℝ) + 1) * u))
        = Φ 1 * ∫ u in L..X, R (((n : ℝ) + 1) * u) := by
      intro L X
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun u _ => hΦR _
    rw [hrw, hrw]
    have h1 : |a ^ 2 * mu * (Φ 1 * ∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u))
        - a ^ 2 * mu / lamDil *
          (Φ 1 * ∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u))|
        ≤ |a ^ 2 * mu * (Φ 1 * ∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u))|
          + |a ^ 2 * mu / lamDil *
            (Φ 1 * ∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t),
              R (((n : ℝ) + 1) * u))| := abs_sub _ _
    refine le_trans h1 ?_
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_div]
    have habs : |a ^ 2| = a ^ 2 := abs_of_nonneg (sq_nonneg a)
    have habsl : |lamDil| = lamDil := abs_of_pos hlamDil0
    have h2abs : |a ^ 2 * mu| = a ^ 2 * |mu| := by rw [abs_mul, habs]
    rw [habs, habsl, h2abs, hA]
    have hinv : a ^ 2 * |mu| / lamDil ≤ a ^ 2 * |mu| := by
      rw [div_le_iff₀ hlamDil0]
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg a) (abs_nonneg mu))
        (by linarith : (0 : ℝ) ≤ lamDil - 1)]
    have hI2nn : (0 : ℝ) ≤ |Φ 1| *
        |∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u)| := by
      positivity
    nlinarith [hinv, hI2nn]
  have hmajsum : Summable fun n : ℕ =>
      A * |∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u)|
        + A * |∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u)| :=
    (hsum1.mul_left A).add (hsum2.mul_left A)
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ |channelPrimitive (prolateMeanZeroSource a lamDil Φ) lamR n t| :=
    fun n => abs_nonneg _
  have hsummable : Summable fun n : ℕ =>
      |channelPrimitive (prolateMeanZeroSource a lamDil Φ) lamR n t| :=
    hmajsum.of_nonneg_of_le hnn hterm
  refine ⟨hsummable, ?_⟩
  have hstep := hsummable.tsum_le_tsum hterm hmajsum
  have hexp : (∑' n : ℕ, (A * |∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u)|
      + A * |∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u)|))
      = A * (∑' n : ℕ, |∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u)|)
        + A * ∑' n : ℕ,
          |∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u)| := by
    rw [(hsum1.mul_left A).tsum_add (hsum2.mul_left A), tsum_mul_left, tsum_mul_left]
  rw [hexp] at hstep
  have hb2' : (∑' n : ℕ,
      |∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u)|) ≤ Bnd := by
    refine le_trans hbnd2 ?_
    rw [hBnd]
    have hmono : Real.sqrt cc * cc * β ≤ Real.sqrt cc * cc * (lamDil * β * 1) := by
      have hb : β ≤ lamDil * β * 1 := by nlinarith
      have hpos : (0 : ℝ) < Real.sqrt cc * cc := by positivity
      nlinarith [hb, hpos]
    have hpos : (0 : ℝ) < Real.sqrt cc * cc * β := by positivity
    have := div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ 4500 * M) hpos hmono
    linarith [this]
  have hb1' : (∑' n : ℕ, |∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u)|) ≤ Bnd := by
    refine le_trans hbnd1 ?_
    rw [hBnd]
    have hmono : Real.sqrt cc * cc * β ≤ Real.sqrt cc * cc * (β * 1) := by nlinarith
    have hpos : (0 : ℝ) < Real.sqrt cc * cc * β := by positivity
    have := div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ 4500 * M) hpos hmono
    linarith [this]
  calc ∑' n : ℕ, |channelPrimitive (prolateMeanZeroSource a lamDil Φ) lamR n t|
      ≤ A * (∑' n : ℕ, |∫ u in (β * 1)..(β * Real.exp t), R (((n : ℝ) + 1) * u)|)
        + A * ∑' n : ℕ,
          |∫ u in (lamDil * β * 1)..(lamDil * β * Real.exp t), R (((n : ℝ) + 1) * u)| := hstep
    _ ≤ A * Bnd + A * Bnd := by
        have hx1 := mul_le_mul_of_nonneg_left hb1' hA0
        have hx2 := mul_le_mul_of_nonneg_left hb2' hA0
        linarith [hx1, hx2]
    _ = 2 * (A * Bnd) := by ring

end RHTower
