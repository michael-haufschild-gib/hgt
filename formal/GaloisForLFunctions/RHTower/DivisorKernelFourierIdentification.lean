import GaloisForLFunctions.RHTower.CosDilationKernelMellinInversion
import GaloisForLFunctions.RHTower.DivisorTransferAbscissa

/-!
# The divisor kernel of a multiplier is a Fourier transform

Let `h` be an even integrable function on `ℝ` with integrable Fourier transform `𝓕h`, and with
`∫_0^∞ |h(t)| t^{−1/2} dt`, `∫_0^∞ |𝓕h(t)| t^{−1/2} dt` finite.

* **Mellin form of the archimedean functional equation** (`mellin_fourier_of_re_eq_half`): on the
  critical line `𝓜[𝓕h](s) = (Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜h(1−s)`.
* **Inversion at any abscissa** (`mellinInv_eq_fourier_of_strip`): if `G` is holomorphic on
  `½ ≤ Re s ≤ c`, decays like `1/(1+t²)` there, and equals `(Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜h(1−s)` on the
  critical line, then `𝓜^{−1}_c[G](x) = 𝓕h(x)` for every `x > 0` at which `𝓕h` is continuous.
  Shift the line of integration to `Re s = ½`, recognise `𝓜[𝓕h]`, and invert.

With `G = Ξ`'s archimedean factor squared times a multiplier `R` this identifies the divisor kernel
`Ψ_{R,c} = 𝓜^{−1}_c[G² R]` of `DivisorTransferAbscissa` with `𝓕h`
(`certKernelAt_eq_fourier`), and the blindness of the test with spectral density `Ξ² R` at every
`log n`, `n ≥ 2`, follows from `𝓕h(n) = 0` for every integer `n ≥ 2`
(`logNode_blind_of_fourier_vanishes`).  For a self-reciprocal `h`
(`h(1/x) = |x| h(x)`, so `𝓜h(1−s) = 𝓜h(s)`) the multiplier is `R = 𝓜h/(G(s)G(1−s))` and the
spectral density on the critical line is `|ζ(½+it)|² 𝓜h(½+it)`.
-/

open Complex MeasureTheory Set
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- **The archimedean functional equation in Mellin form**, on the critical line. -/
theorem mellin_fourier_of_re_eq_half {h : ℝ → ℂ} (hi : Integrable h) (hFi : Integrable (𝓕 h))
    (heven : ∀ t : ℝ, h (-t) = h t)
    (h1 : IntegrableOn (fun t : ℝ => ‖h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    (h2 : IntegrableOn (fun t : ℝ => ‖𝓕 h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0)) {s : ℂ}
    (hs : s.re = 1 / 2) :
    mellin (𝓕 h) s = Gammaℝ s / Gammaℝ (1 - s) * mellin h (1 - s) := by
  have hs1 : (1 - s).re = 1 / 2 := by rw [Complex.sub_re, Complex.one_re, hs]; norm_num
  have hFE := soninMellinEvaluation_fourier (w := s) (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    hi hFi heven (by rw [hs]; exact h1) (by rw [hs1]; exact h2)
  unfold soninMellinEvaluation soninMellinKernel at hFE
  rw [mellinCompletionFactor_eq_Gammaℝ, mellinCompletionFactor_eq_Gammaℝ,
    integral_mul_cpow_neg_eq_mellin, integral_mul_cpow_neg_eq_mellin,
    show 1 - (1 - s) = s by ring] at hFE
  have hG : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs1]; norm_num)
  field_simp
  rw [mul_comm, ← hFE]

/-- **Mellin inversion at any abscissa to the right of the critical line.** -/
theorem mellinInv_eq_fourier_of_strip {h : ℝ → ℂ} (hi : Integrable h) (hFi : Integrable (𝓕 h))
    (heven : ∀ t : ℝ, h (-t) = h t)
    (h1 : IntegrableOn (fun t : ℝ => ‖h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    (h2 : IntegrableOn (fun t : ℝ => ‖𝓕 h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    {c : ℝ} (hc : 1 / 2 ≤ c) {G : ℂ → ℂ}
    (hGd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ G s)
    {C : ℝ} (hGb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → ‖G s‖ ≤ C / (1 + s.im ^ 2))
    (hGline : ∀ s : ℂ, s.re = 1 / 2 → G s = Gammaℝ s / Gammaℝ (1 - s) * mellin h (1 - s))
    {x : ℝ} (hx : 0 < x) (hcont : ContinuousAt (𝓕 h) x) :
    mellinInv c G x = 𝓕 h x := by
  -- shift the line of integration to `Re s = ½`
  set B : ℝ := max (x ^ (-(1 / 2 : ℝ))) (x ^ (-c)) with hB
  have hxs : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → ‖(x : ℂ) ^ (-s)‖ ≤ B := by
    intro s hs1 hs2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
    rcases le_total 1 x with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans (le_max_right _ _)
  have hB0 : 0 ≤ B := le_max_of_le_left (Real.rpow_nonneg hx.le _)
  have hstrip : ∀ s : ℂ, s.re ∈ uIcc (1 / 2 : ℝ) c → 1 / 2 ≤ s.re ∧ s.re ≤ c := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    exact hs
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hd : ∀ s : ℂ, s.re ∈ uIcc (1 / 2 : ℝ) c →
      DifferentiableAt ℂ (fun s => (x : ℂ) ^ (-s) * G s) s := by
    intro s hs
    obtain ⟨h1', h2'⟩ := hstrip s hs
    exact ((differentiableAt_id.neg).const_cpow (Or.inl hx0)).mul (hGd s h1' h2')
  have hb : ∀ s : ℂ, s.re ∈ uIcc (1 / 2 : ℝ) c →
      ‖(fun s => (x : ℂ) ^ (-s) * G s) s‖ ≤ B * C / (1 + s.im ^ 2) := by
    intro s hs
    obtain ⟨h1', h2'⟩ := hstrip s hs
    simp only [norm_mul]
    calc ‖(x : ℂ) ^ (-s)‖ * ‖G s‖ ≤ B * (C / (1 + s.im ^ 2)) :=
          mul_le_mul (hxs s h1' h2') (hGb s h1' h2') (norm_nonneg _) hB0
      _ = B * C / (1 + s.im ^ 2) := by ring
  have hshift := GaloisForLFunctions.HTGeometry.integral_vertical_line_shift_of_decay hd hb
  have hinv : mellinInv c G x = mellinInv (1 / 2) G x := by
    unfold mellinInv
    congr 1
    simp only [smul_eq_mul]
    exact hshift.symm
  -- on the critical line `G` is the Mellin transform of `𝓕h`
  have hline : mellinInv (1 / 2) G x = mellinInv (1 / 2) (mellin (𝓕 h)) x := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hre : (((1 / 2 : ℝ) : ℂ) + y * I).re = 1 / 2 := by simp
    simp only
    rw [hGline _ hre, mellin_fourier_of_re_eq_half hi hFi heven h1 h2 hre]
  rw [hinv, hline]
  refine mellinInv_mellin_eq (1 / 2) (𝓕 h) hx ?_ ?_ hcont
  · -- `MellinConvergent (𝓕 h) ½`
    unfold MellinConvergent
    have hc' : ContinuousOn (fun t : ℝ => (t : ℂ) ^ ((((1 / 2 : ℝ) : ℂ)) - 1)) (Ioi 0) := by
      intro t ht
      exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht))).continuousWithinAt)
    refine (h2.mono' ?_ ?_)
    · exact (hc'.aestronglyMeasurable measurableSet_Ioi).smul
        hFi.aestronglyMeasurable.restrict
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
      have : ((((1 / 2 : ℝ) : ℂ)) - 1).re = -(1 / 2 : ℝ) := by simp; norm_num
      rw [this, mul_comm]
  · -- `VerticalIntegrable (mellin (𝓕 h)) ½`
    have hcontG : Continuous fun y : ℝ => G (((1 / 2 : ℝ) : ℂ) + y * I) := by
      rw [continuous_iff_continuousAt]
      intro y
      exact (hGd _ (by simp) (by simpa using hc)).continuousAt.comp (by fun_prop)
    have hint : Integrable fun y : ℝ => G (((1 / 2 : ℝ) : ℂ) + y * I) := by
      refine (integrable_inv_one_add_sq.const_mul C).mono' hcontG.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      have := hGb (((1 / 2 : ℝ) : ℂ) + y * I) (by simp) (by simpa using hc)
      simpa [div_eq_mul_inv] using this
    refine hint.congr (Filter.Eventually.of_forall fun y => ?_)
    have hre : (((1 / 2 : ℝ) : ℂ) + y * I).re = 1 / 2 := by simp
    simp only
    rw [hGline _ hre, mellin_fourier_of_re_eq_half hi hFi heven h1 h2 hre]

/-- **The divisor kernel is the Fourier transform of the multiplier's line profile.** -/
theorem certKernelAt_eq_fourier {h : ℝ → ℂ} (hi : Integrable h) (hFi : Integrable (𝓕 h))
    (heven : ∀ t : ℝ, h (-t) = h t)
    (h1 : IntegrableOn (fun t : ℝ => ‖h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    (h2 : IntegrableOn (fun t : ℝ => ‖𝓕 h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    {c : ℝ} (hc : 1 < c) {R : ℂ → ℂ}
    (hRd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ R s)
    {C : ℝ} (hGb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c →
      ‖ExactNullDivisorTransfer.archXi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    (hGline : ∀ s : ℂ, s.re = 1 / 2 →
      ExactNullDivisorTransfer.archXi s ^ 2 * R s = Gammaℝ s / Gammaℝ (1 - s) * mellin h (1 - s))
    {x : ℝ} (hx : 0 < x) (hcont : ContinuousAt (𝓕 h) x) :
    ExactNullDivisorTransfer.certKernelAt c R x = 𝓕 h x := by
  unfold ExactNullDivisorTransfer.certKernelAt
  refine mellinInv_eq_fourier_of_strip hi hFi heven h1 h2 (by linarith) (fun s hs1 hs2 => ?_)
    hGb hGline hx hcont
  have hre : 0 < s.re := by linarith
  exact ((ExactNullDivisorTransfer.differentiableAt_archXi hre).pow 2).mul (hRd s hs1 hs2)

/-- **Blindness from the integer zeros of `𝓕h`.**  The test with spectral density `Ξ² R` vanishes at
every `log n`, `n ≥ 2`, when `𝓕h` vanishes at every integer `n ≥ 2`. -/
theorem logNode_blind_of_fourier_vanishes {h : ℝ → ℂ} (hi : Integrable h)
    (hFi : Integrable (𝓕 h)) (heven : ∀ t : ℝ, h (-t) = h t)
    (h1 : IntegrableOn (fun t : ℝ => ‖h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    (h2 : IntegrableOn (fun t : ℝ => ‖𝓕 h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    (hFc : Continuous (𝓕 h)) {c : ℝ} (hc : 1 < c) {R : ℂ → ℂ}
    (hRd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ R s)
    {C : ℝ} (hC : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → ‖xi s ^ 2 * R s‖ ≤ C / (1 + s.im ^ 2))
    {C' : ℝ} (hGb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c →
      ‖ExactNullDivisorTransfer.archXi s ^ 2 * R s‖ ≤ C' / (1 + s.im ^ 2))
    (hGline : ∀ s : ℂ, s.re = 1 / 2 →
      ExactNullDivisorTransfer.archXi s ^ 2 * R s = Gammaℝ s / Gammaℝ (1 - s) * mellin h (1 - s))
    (hblind : ∀ n : ℕ, 2 ≤ n → 𝓕 h n = 0) (n : ℕ) (hn : 2 ≤ n) :
    ∫ t : ℝ, xi (1 / 2 + t * I) ^ 2 * R (1 / 2 + t * I) * (n : ℂ) ^ (-((t : ℂ) * I)) = 0 := by
  refine ExactNullDivisorTransfer.logNode_blind_of_certKernelAt_vanishes R hc hRd hC
    (fun t => by simpa using hGb ((c : ℂ) + t * I) (by simp; linarith) (by simp))
    (fun m hm => ?_) n hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  rw [certKernelAt_eq_fourier hi hFi heven h1 h2 hc hRd hGb hGline hm0 hFc.continuousAt]
  exact hblind m hm

end RHTower
