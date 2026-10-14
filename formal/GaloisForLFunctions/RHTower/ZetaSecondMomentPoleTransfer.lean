import GaloisForLFunctions.RHTower.DivisorKernelFourierIdentification
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# The divisor transfer through the pole of `ζ²`, and the mass of a blind self-dual test

Let `h` be an even function on `ℝ` and `M(s) = (Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜h(1−s)` (`fourierMultiplier`).
On the critical line `M = 𝓜[𝓕h]`, and `ζ(s)² M(s) = ζ(s) ζ(1−s) 𝓜h(1−s)` by the functional
equation.  The multiplier vanishes at `s = 1` (`Γ_ℝ` has a pole at `0`), so `ζ² M` has a simple
pole there, with residue `−½ 𝓜h(0)` (`tendsto_sub_one_mul_zeta_sq_mul_fourierMultiplier`).

* `integral_zeta_sq_mul_fourierMultiplier_mul_cpow`: shifting `∫ ζ² M n^{−s}` from `Re s = ½` to
  `Re s = c > 1` past the pole and expanding `ζ² = Σ d(m) m^{−s}`,
  `∫ ζ(½+it)² M(½+it) n^{−(½+it)} dt = 2π Σ_m d(m) 𝓕h(mn) + π 𝓜h(0)/n`.
* `integral_normSq_zeta_mul_mellin_eq`: for `n = 1` and `𝓜h(1−s) = 𝓜h(s)` (self-reciprocal `h`),
  `∫ |ζ(½+it)|² 𝓜h(½+it) dt = 2π Σ_m d(m) 𝓕h(m) + π 𝓜h(0)`.

The mass term `π 𝓜h(0) = π ∫_0^∞ h` is what a pole-free (mean-zero) test does not see.
Consequences for blind tests (`𝓕h(m) = 0` for `m ≥ 2`) with positive Mellin transform on the
critical line:

* `mellin_zero_pos_of_allInteger_blind`: blindness at every `m ≥ 1` forces `∫_0^∞ h > 0`;
* `fourier_one_pos_of_blind_of_mellin_zero_eq_zero`: a mean-zero test blind at every `m ≥ 2` has
  `𝓕h(1) = (1/2π) ∫ |ζ(½+it)|² 𝓜h(½+it) dt > 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped FourierTransform

noncomputable section

namespace RHTower.ZetaSecondMomentPole

open RHTower.ExactNullDivisorTransfer

/-- The multiplier `M(s) = (Γ_ℝ(s)/Γ_ℝ(1−s)) 𝓜h(1−s)`. -/
def fourierMultiplier (h : ℝ → ℂ) (s : ℂ) : ℂ := Gammaℝ s / Gammaℝ (1 - s) * mellin h (1 - s)

/-! ### The residue at `s = 1` -/

theorem mul_Gammaℝ_eq {w : ℂ} (hw : w ≠ 0) :
    w * Gammaℝ w = 2 * ((Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2 + 1)) := by
  rw [Gammaℝ_def, Gamma_add_one _ (div_ne_zero hw two_ne_zero)]
  ring

/-- `w Γ_ℝ(w) → 2` as `w → 0`. -/
theorem tendsto_mul_Gammaℝ : Tendsto (fun w : ℂ => w * Gammaℝ w) (𝓝[≠] 0) (𝓝 2) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : ContinuousAt (fun w : ℂ => 2 * ((Real.pi : ℂ) ^ (-w / 2) * Gamma (w / 2 + 1))) 0 := by
    have hg : ContinuousAt (fun w : ℂ => Gamma (w / 2 + 1)) 0 := by
      have hd : DifferentiableAt ℂ Gamma ((fun w : ℂ => w / 2 + 1) 0) :=
        differentiableAt_Gamma _ (fun m h => by
          have := congrArg Complex.re h
          simp at this
          linarith [Nat.cast_nonneg (α := ℝ) m])
      exact hd.continuousAt.comp (x := 0) (by fun_prop)
    have hp : ContinuousAt (fun w : ℂ => (Real.pi : ℂ) ^ (-w / 2)) 0 :=
      (continuous_const.cpow (by fun_prop) fun _ => Or.inl (by simp [Real.pi_pos])).continuousAt
    exact continuousAt_const.mul (hp.mul hg)
  have hv : (2 : ℂ) * ((Real.pi : ℂ) ^ (-(0 : ℂ) / 2) * Gamma (0 / 2 + 1)) = 2 := by
    simp
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact (mul_Gammaℝ_eq hw).symm

/-- `Γ_ℝ(w)⁻¹/w → ½` as `w → 0`. -/
theorem tendsto_inv_Gammaℝ_div : Tendsto (fun w : ℂ => (Gammaℝ w)⁻¹ / w) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have h := tendsto_mul_Gammaℝ.inv₀ two_ne_zero
  rw [show (2 : ℂ)⁻¹ = 1 / 2 by norm_num] at h
  refine h.congr fun w => ?_
  rw [mul_inv, div_eq_mul_inv, mul_comm]

/-- **The residue of `ζ² M` at `s = 1`** is `−½ 𝓜h(0)`. -/
theorem tendsto_sub_one_mul_zeta_sq_mul_fourierMultiplier {h : ℝ → ℂ}
    (h0 : ContinuousAt (mellin h) 0) {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun s : ℂ => (s - 1) * (riemannZeta s ^ 2 * fourierMultiplier h s * (n : ℂ) ^ (-s)))
      (𝓝[≠] 1) (𝓝 (-(1 / 2) * mellin h 0 / n)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hz := riemannZeta_residue_one
  have hw : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [mem_compl_iff, mem_singleton_iff, sub_eq_zero] at hs ⊢
      exact fun h => hs h.symm
  have hG : Tendsto (fun s : ℂ => (Gammaℝ (1 - s))⁻¹ / (s - 1)) (𝓝[≠] 1) (𝓝 (-(1 / 2))) := by
    have := (tendsto_inv_Gammaℝ_div.comp hw).neg
    refine this.congr fun s => ?_
    simp only [Function.comp_apply]
    rw [show s - 1 = -(1 - s) by ring, div_neg]
  have hR : Tendsto (fun s : ℂ => Gammaℝ s) (𝓝[≠] 1) (𝓝 1) := by
    have hd : DifferentiableAt ℂ Gammaℝ 1 := by
      have h1 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) 1 :=
        (differentiableAt_id.neg.div_const 2).const_cpow
          (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
      have h2 : DifferentiableAt ℂ (fun s : ℂ => Gamma (s / 2)) 1 :=
        (differentiableAt_Gamma ((1 : ℂ) / 2) (fun m h => by
          have := congrArg Complex.re h
          simp at this
          linarith [Nat.cast_nonneg (α := ℝ) m])).comp 1 (differentiableAt_id.div_const 2)
      have : Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Gamma (s / 2) :=
        funext Gammaℝ_def
      rw [this]
      exact h1.mul h2
    have := hd.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {1}ᶜ))
    rwa [Gammaℝ_one] at this
  have hM : Tendsto (fun s : ℂ => mellin h (1 - s)) (𝓝[≠] 1) (𝓝 (mellin h 0)) :=
    h0.tendsto.comp (tendsto_nhdsWithin_iff.mp hw).1
  have hcp : Tendsto (fun s : ℂ => (n : ℂ) ^ (-s)) (𝓝[≠] 1) (𝓝 ((n : ℂ) ^ (-(1 : ℂ)))) :=
    ((continuous_const.cpow continuous_neg fun _ => Or.inl (by simp; omega)).tendsto 1).mono_left
      nhdsWithin_le_nhds
  have hlim := (((hz.pow 2).mul hR).mul hG).mul hM |>.mul hcp
  have hval : (1 : ℂ) ^ 2 * 1 * (-(1 / 2)) * mellin h 0 * (n : ℂ) ^ (-(1 : ℂ)) =
      -(1 / 2) * mellin h 0 / n := by
    rw [cpow_neg_one]; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold fourierMultiplier
  field_simp

/-! ### The right line -/

/-- **The divisor expansion on `Re s = c > 1`.**  For `K` holomorphic near the line with
`C/(1+t²)` decay, `∫ ζ(c+it)² K(c+it) n^{−(c+it)} dt = 2π Σ_m d(m) 𝓜^{−1}_c[K](mn)`. -/
theorem integral_zeta_sq_mul_cpow_line_eq_tsum {K : ℂ → ℂ} {c : ℝ} (hc : 1 < c)
    (hKc : ∀ t : ℝ, ContinuousAt K ((c : ℂ) + t * I))
    {C : ℝ} (hKb : ∀ t : ℝ, ‖K ((c : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2)) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, riemannZeta ((c : ℂ) + t * I) ^ 2 * K ((c : ℂ) + t * I) *
        (n : ℂ) ^ (-((c : ℂ) + t * I)) =
      2 * Real.pi * ∑' m : ℕ, divisorCard m * mellinInv c K ((m * n : ℕ) : ℝ) := by
  set L : ℝ → ℂ := fun t => K ((c : ℂ) + t * I) with hL
  set F : ℕ → ℝ → ℂ := fun m t =>
    divisorCard m * (((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) * L t) with hF
  have hre : ∀ t : ℝ, 1 < ((c : ℂ) + t * I).re := fun t => by simpa using hc
  have hser : ∀ t : ℝ, riemannZeta ((c : ℂ) + t * I) ^ 2 * K ((c : ℂ) + t * I) *
      (n : ℂ) ^ (-((c : ℂ) + t * I)) = ∑' m, F m t := by
    intro t
    simp only [hF, hL]
    rw [riemannZeta_sq_eq_tsum (hre t), ← tsum_mul_right, ← tsum_mul_right]
    refine tsum_congr fun m => ?_
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have hLcont : Continuous L := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hKc t).comp (f := fun t : ℝ => (c : ℂ) + t * I) (by fun_prop)
  have hLint : Integrable L := by
    refine (integrable_inv_one_add_sq.const_mul C).mono' hLcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    simpa [hL, div_eq_mul_inv] using hKb t
  have hnorm_cpow : ∀ m : ℕ, ∀ t : ℝ, 1 ≤ m →
      ‖((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I))‖ = ((m * n : ℕ) : ℝ) ^ (-c) := by
    intro m t hm
    have hpos : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
      have : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    rw [show (((m * n : ℕ) : ℂ)) = ((((m * n : ℕ) : ℝ)) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp
  have hFint : ∀ m : ℕ, Integrable (F m) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorCard]
    have hcp : Continuous fun t : ℝ => ((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) := by
      have hb0 : ((m * n : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mp (Nat.one_le_iff_ne_zero.mpr (by positivity)))
      exact Continuous.const_cpow (by fun_prop) (Or.inl hb0)
    have hbound : ∀ t, ‖F m t‖ ≤ ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c) * ‖L t‖ := by
      intro t
      simp only [hF, norm_mul, hnorm_cpow m t hm]
      ring_nf; rfl
    exact ((hLint.norm.const_mul (‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c)))).mono'
      ((continuous_const.mul (hcp.mul hLcont)).aestronglyMeasurable)
      (Filter.Eventually.of_forall hbound)
  have hFnorm : ∀ m : ℕ, ∫ t, ‖F m t‖ =
      ‖divisorCard m‖ * ((m * n : ℕ) : ℝ) ^ (-c) * ∫ t, ‖L t‖ := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [hF, divisorCard]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF, norm_mul, hnorm_cpow m t hm]
    ring
  have hFsum : Summable fun m => ∫ t, ‖F m t‖ := by
    simp_rw [hFnorm]
    exact (summable_norm_divisorCard_mul_rpow hc hn).mul_right _
  rw [show (∫ t : ℝ, riemannZeta ((c : ℂ) + t * I) ^ 2 * K ((c : ℂ) + t * I) *
      (n : ℂ) ^ (-((c : ℂ) + t * I))) = ∫ t : ℝ, ∑' m, F m t from
    integral_congr_ae (Filter.Eventually.of_forall hser),
    ← integral_tsum_of_summable_integral_norm hFint hFsum, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hI : (∫ y : ℝ, (((m * n : ℕ) : ℝ) : ℂ) ^ (-((c : ℂ) + y * I)) • K ((c : ℂ) + y * I)) =
      ∫ t : ℝ, ((m * n : ℕ) : ℂ) ^ (-((c : ℂ) + t * I)) * L t := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hL, smul_eq_mul]
    push_cast
    ring_nf
  simp only [hF]
  rw [integral_const_mul, mellinInv, hI, Complex.real_smul]
  push_cast
  field_simp
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [mul_comm I]

/-! ### The transfer through the pole -/

/-- **Divisor transfer through the pole of `ζ²`.**
`∫ ζ(½+it)² M(½+it) n^{−(½+it)} dt = 2π Σ_m d(m) 𝓕h(mn) + π 𝓜h(0)/n`. -/
theorem integral_zeta_sq_mul_fourierMultiplier_mul_cpow {h : ℝ → ℂ} (hi : Integrable h)
    (hFi : Integrable (𝓕 h)) (heven : ∀ t : ℝ, h (-t) = h t)
    (h1 : IntegrableOn (fun t : ℝ => ‖h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    (h2 : IntegrableOn (fun t : ℝ => ‖𝓕 h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    {c : ℝ} (hc : 1 < c)
    (hMd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ (fourierMultiplier h) s)
    {C : ℝ} (hMb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c →
      ‖fourierMultiplier h s‖ ≤ C / (1 + s.im ^ 2))
    {T₀ C' : ℝ} (hZb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → T₀ ≤ |s.im| →
      ‖riemannZeta s ^ 2 * fourierMultiplier h s‖ ≤ C' * (1 + s.im ^ 2)⁻¹)
    (h0 : ContinuousAt (mellin h) 0) {n : ℕ} (hn : 1 ≤ n) :
    ∫ t : ℝ, riemannZeta (1 / 2 + t * I) ^ 2 * fourierMultiplier h (1 / 2 + t * I) *
        (n : ℂ) ^ (-(1 / 2 + t * I)) =
      2 * Real.pi * ∑' m : ℕ, divisorCard m * 𝓕 h ((m * n : ℕ) : ℝ) +
        Real.pi * mellin h 0 / n := by
  set M := fourierMultiplier h with hMdef
  set F : ℂ → ℂ := fun s => riemannZeta s ^ 2 * M s * (n : ℂ) ^ (-s) with hF
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hFd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → s ≠ 1 → DifferentiableAt ℂ F s := by
    intro s hs1 hs2 hs
    exact (((differentiableAt_riemannZeta hs).pow 2).mul (hMd s hs1 hs2)).mul
      ((differentiableAt_id.neg).const_cpow (Or.inl hn0))
  have hFb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → T₀ ≤ |s.im| →
      ‖F s‖ ≤ C' * (1 + s.im ^ 2)⁻¹ := by
    intro s hs1 hs2 hT
    have hcp := norm_natCast_cpow_neg_re_le_one hn (s := s) (by linarith)
    have hb := hZb s hs1 hs2 hT
    rw [hF, norm_mul]
    calc ‖riemannZeta s ^ 2 * M s‖ * ‖(n : ℂ) ^ (-s)‖ ≤ (C' * (1 + s.im ^ 2)⁻¹) * 1 :=
          mul_le_mul hb hcp (norm_nonneg _) ((norm_nonneg _).trans hb)
      _ = C' * (1 + s.im ^ 2)⁻¹ := mul_one _
  have hres := tendsto_sub_one_mul_zeta_sq_mul_fourierMultiplier h0 hn
  have hshift := GaloisForLFunctions.HTGeometry.integral_line_sub_integral_line_eq
    (F := F) (a := 1 / 2) (b := c) (p := 1) (by norm_num) (by simpa using hc)
    (fun s hs1 hs2 hs => hFd s hs1 hs2 hs) hres hFb
  -- the right line
  have hMc : ∀ t : ℝ, ContinuousAt M ((c : ℂ) + t * I) := fun t =>
    (hMd _ (by simp; linarith) (by simp)).continuousAt
  have hMcb : ∀ t : ℝ, ‖M ((c : ℂ) + t * I)‖ ≤ C / (1 + t ^ 2) := fun t => by
    simpa using hMb ((c : ℂ) + t * I) (by simp; linarith) (by simp)
  have hright := integral_zeta_sq_mul_cpow_line_eq_tsum hc hMc hMcb hn
  have hFc : Continuous (𝓕 h) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hi
  have hker : ∀ m : ℕ, 1 ≤ m → mellinInv c M ((m * n : ℕ) : ℝ) = 𝓕 h ((m * n : ℕ) : ℝ) := by
    intro m hm
    have hpos : (0 : ℝ) < ((m * n : ℕ) : ℝ) := by
      have : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    exact mellinInv_eq_fourier_of_strip hi hFi heven h1 h2 (by linarith) hMd hMb
      (fun s _ => rfl) hpos hFc.continuousAt
  have htsum : ∑' m : ℕ, divisorCard m * mellinInv c M ((m * n : ℕ) : ℝ) =
      ∑' m : ℕ, divisorCard m * 𝓕 h ((m * n : ℕ) : ℝ) := by
    refine tsum_congr fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [divisorCard]
    · rw [hker m hm]
  have hleft : (∫ t : ℝ, riemannZeta (1 / 2 + t * I) ^ 2 * M (1 / 2 + t * I) *
      (n : ℂ) ^ (-(1 / 2 + t * I))) = ∫ t : ℝ, F (((1 / 2 : ℝ) : ℂ) + t * I) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hF]; push_cast; ring_nf
  have hrt : (∫ t : ℝ, F ((c : ℂ) + t * I)) = 2 * Real.pi *
      ∑' m : ℕ, divisorCard m * 𝓕 h ((m * n : ℕ) : ℝ) := by
    rw [← htsum, ← hright]
  rw [hleft]
  rw [hrt] at hshift
  linear_combination -hshift

/-! ### The critical line -/

/-- On the critical line, `ζ(s)² M(s) = ζ(s) ζ(1−s) 𝓜h(1−s)` (functional equation). -/
theorem zeta_sq_mul_fourierMultiplier_line (h : ℝ → ℂ) (t : ℝ) :
    riemannZeta (1 / 2 + t * I) ^ 2 * fourierMultiplier h (1 / 2 + t * I) =
      riemannZeta (1 / 2 + t * I) * riemannZeta (1 / 2 - t * I) * mellin h (1 / 2 - t * I) := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hs0 : s ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have h1s : 1 - s = 1 / 2 - t * I := by rw [hs]; ring
  have h1s0 : 1 - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp [hre] at this; norm_num at this
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
  have hG' : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [hre]; norm_num)
  have hz : riemannZeta s * Gammaℝ s = riemannZeta (1 - s) * Gammaℝ (1 - s) := by
    rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero h1s0,
      completedRiemannZeta_one_sub]
    field_simp
  unfold fourierMultiplier
  rw [← h1s]
  field_simp
  linear_combination riemannZeta s * mellin h (1 - s) * hz

/-- **The second moment with its mass term.**  For an even `h` with the regularity of
`integral_zeta_sq_mul_fourierMultiplier_mul_cpow`,
`∫ ζ(½+it) ζ(½−it) 𝓜h(½−it) dt = 2π Σ_m d(m) 𝓕h(m) + π 𝓜h(0)`. -/
theorem integral_zeta_mul_zeta_mul_mellin_eq {h : ℝ → ℂ} (hi : Integrable h)
    (hFi : Integrable (𝓕 h)) (heven : ∀ t : ℝ, h (-t) = h t)
    (h1 : IntegrableOn (fun t : ℝ => ‖h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    (h2 : IntegrableOn (fun t : ℝ => ‖𝓕 h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0))
    {c : ℝ} (hc : 1 < c)
    (hMd : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ (fourierMultiplier h) s)
    {C : ℝ} (hMb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c →
      ‖fourierMultiplier h s‖ ≤ C / (1 + s.im ^ 2))
    {T₀ C' : ℝ} (hZb : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → T₀ ≤ |s.im| →
      ‖riemannZeta s ^ 2 * fourierMultiplier h s‖ ≤ C' * (1 + s.im ^ 2)⁻¹)
    (h0 : ContinuousAt (mellin h) 0) :
    ∫ t : ℝ, riemannZeta (1 / 2 + t * I) * riemannZeta (1 / 2 - t * I) *
        mellin h (1 / 2 - t * I) =
      2 * Real.pi * ∑' m : ℕ, divisorCard m * 𝓕 h (m : ℝ) + Real.pi * mellin h 0 := by
  have hT := integral_zeta_sq_mul_fourierMultiplier_mul_cpow hi hFi heven h1 h2 hc hMd hMb hZb h0
    (n := 1) le_rfl
  simp only [Nat.cast_one, one_cpow, mul_one, div_one] at hT
  rw [← hT]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  exact (zeta_sq_mul_fourierMultiplier_line h t).symm

theorem zeta_mul_zeta_line_eq_normSq (t : ℝ) :
    riemannZeta (1 / 2 + t * I) * riemannZeta (1 / 2 - t * I) =
      ((‖riemannZeta (1 / 2 + t * I)‖ ^ 2 : ℝ) : ℂ) := by
  have hc : (1 / 2 - t * I : ℂ) = (starRingEnd ℂ) (1 / 2 + t * I) := by
    apply Complex.ext <;> simp
  rw [hc, riemannZeta_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A nonnegative continuous integrable `‖ζ(½+it)‖² P(t)` with `P > 0` has positive integral. -/
theorem integral_normSq_zeta_mul_pos {P : ℝ → ℝ} (hPc : Continuous P) (hP : ∀ t, 0 < P t)
    (hint : Integrable fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t) :
    0 < ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t := by
  have hzc : Continuous fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t := by
    have : Continuous fun t : ℝ => riemannZeta (1 / 2 + t * I) := by
      rw [continuous_iff_continuousAt]
      intro t
      have hne : (1 / 2 + t * I : ℂ) ≠ 1 := fun h => by
        have := congrArg Complex.re h; simp at this
      exact (differentiableAt_riemannZeta hne).continuousAt.comp (x := t)
        (f := fun t : ℝ => (1 / 2 : ℂ) + t * I) (by fun_prop)
    exact (this.norm.pow 2).mul hPc
  have h0 : riemannZeta (1 / 2 + (0 : ℝ) * I) ≠ 0 := by
    have := riemannZeta_real_strip_ne_zero (σ := 1 / 2) (by norm_num) (by norm_num)
    simpa using this
  have hpos0 : 0 < ‖riemannZeta (1 / 2 + (0 : ℝ) * I)‖ ^ 2 * P 0 :=
    mul_pos (pow_pos (norm_pos_iff.mpr h0) 2) (hP 0)
  refine (integral_pos_iff_support_of_nonneg (fun t => mul_nonneg (by positivity) (hP t).le)
    hint).mpr ?_
  have hopen : IsOpen (Function.support fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t) :=
    isOpen_ne_fun hzc continuous_const
  exact hopen.measure_pos volume ⟨0, hpos0.ne'⟩

/-! ### Blind tests -/

/-- The regularity hypotheses of the transfer, on the strip `½ ≤ Re s ≤ c`. -/
structure SecondMomentRegular (h : ℝ → ℂ) (c : ℝ) : Prop where
  integrable : Integrable h
  integrable_fourier : Integrable (𝓕 h)
  even : ∀ t : ℝ, h (-t) = h t
  integrableOn_half : IntegrableOn (fun t : ℝ => ‖h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0)
  integrableOn_fourier_half : IntegrableOn (fun t : ℝ => ‖𝓕 h t‖ * t ^ (-(1 / 2 : ℝ))) (Ioi 0)
  differentiableAt : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c →
    DifferentiableAt ℂ (fourierMultiplier h) s
  bound : ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c →
    ‖fourierMultiplier h s‖ ≤ C / (1 + s.im ^ 2)
  zeta_bound : ∃ T₀ C' : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → T₀ ≤ |s.im| →
    ‖riemannZeta s ^ 2 * fourierMultiplier h s‖ ≤ C' * (1 + s.im ^ 2)⁻¹
  continuousAt_mellin_zero : ContinuousAt (mellin h) 0

variable {h : ℝ → ℂ} {c : ℝ} {P : ℝ → ℝ}

theorem SecondMomentRegular.integral_eq (hR : SecondMomentRegular h c) (hc : 1 < c) :
    ∫ t : ℝ, riemannZeta (1 / 2 + t * I) * riemannZeta (1 / 2 - t * I) *
        mellin h (1 / 2 - t * I) =
      2 * Real.pi * ∑' m : ℕ, divisorCard m * 𝓕 h (m : ℝ) + Real.pi * mellin h 0 := by
  obtain ⟨C, hMb⟩ := hR.bound
  obtain ⟨T₀, C', hZb⟩ := hR.zeta_bound
  exact integral_zeta_mul_zeta_mul_mellin_eq hR.integrable hR.integrable_fourier hR.even
    hR.integrableOn_half hR.integrableOn_fourier_half hc hR.differentiableAt hMb hZb
    hR.continuousAt_mellin_zero

theorem SecondMomentRegular.integrable_normSq (hR : SecondMomentRegular h c) (hc : 1 < c)
    (hP : ∀ t, 0 < P t) (hPm : ∀ t : ℝ, mellin h (1 / 2 - t * I) = P t) :
    Integrable fun t : ℝ => ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t := by
  obtain ⟨T₀, C', hZb⟩ := hR.zeta_bound
  set F : ℂ → ℂ := fun s => riemannZeta s ^ 2 * fourierMultiplier h s with hF
  have hFc : ∀ t : ℝ, ContinuousAt F (((1 / 2 : ℝ) : ℂ) + t * I) := by
    intro t
    have hne : (((1 / 2 : ℝ) : ℂ) + t * I) ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this
    exact (((differentiableAt_riemannZeta hne).pow 2).mul
      (hR.differentiableAt _ (by simp) (by simp; linarith))).continuousAt
  have hint := GaloisForLFunctions.HTGeometry.integrable_line_of_bound (F := F) (x := 1 / 2)
    (T₀ := T₀) (C := C') hFc (fun t ht => by
      have him : (((1 / 2 : ℝ) : ℂ) + t * I).im = t := by simp
      have := hZb (((1 / 2 : ℝ) : ℂ) + t * I) (by simp) (by simp; linarith) (by rw [him]; exact ht)
      rw [him] at this
      exact this)
  refine hint.norm.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [hF]
  have := zeta_sq_mul_fourierMultiplier_line h t
  push_cast at this ⊢
  rw [this, zeta_mul_zeta_line_eq_normSq, hPm t, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_pos (hP t)]

/-- **The blind identity.**  If `𝓕h(m) = 0` for every `m ≥ 2` and `𝓜h(½−it) = P(t)` is real, then
`π 𝓜h(0) + 2π 𝓕h(1) = ∫ ‖ζ(½+it)‖² P(t) dt`. -/
theorem SecondMomentRegular.mass_add_fourier_one_eq (hR : SecondMomentRegular h c) (hc : 1 < c)
    (hPm : ∀ t : ℝ, mellin h (1 / 2 - t * I) = P t)
    (hblind : ∀ m : ℕ, 2 ≤ m → 𝓕 h (m : ℝ) = 0) :
    Real.pi * mellin h 0 + 2 * Real.pi * 𝓕 h 1 =
      ((∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t : ℝ) : ℂ) := by
  have hI := hR.integral_eq hc
  have hsum : ∑' m : ℕ, divisorCard m * 𝓕 h (m : ℝ) = 𝓕 h 1 := by
    rw [tsum_eq_single 1]
    · simp [divisorCard]
    · intro m hm
      rcases Nat.lt_or_ge m 2 with h2 | h2
      · interval_cases m
        · simp [divisorCard]
        · exact absurd rfl hm
      · rw [hblind m h2, mul_zero]
  rw [hsum] at hI
  rw [← integral_complex_ofReal, show Real.pi * mellin h 0 + 2 * Real.pi * 𝓕 h 1 =
    2 * Real.pi * 𝓕 h 1 + Real.pi * mellin h 0 by ring, ← hI]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [zeta_mul_zeta_line_eq_normSq, hPm t]
  push_cast
  ring

/-- **All-integer blindness forces positive mass.**  If `𝓕h(m) = 0` for every `m ≥ 1` and the
Mellin transform is positive on the critical line, then `𝓜h(0) = (1/π) ∫ ‖ζ(½+it)‖² P(t) dt > 0`;
for self-reciprocal `h`, `𝓜h(0) = 𝓜h(1) = ∫_0^∞ h`. -/
theorem SecondMomentRegular.mellin_zero_pos_of_allInteger_blind (hR : SecondMomentRegular h c)
    (hc : 1 < c) (hPc : Continuous P) (hP : ∀ t, 0 < P t)
    (hPm : ∀ t : ℝ, mellin h (1 / 2 - t * I) = P t)
    (hblind : ∀ m : ℕ, 1 ≤ m → 𝓕 h (m : ℝ) = 0) :
    ∃ r : ℝ, 0 < r ∧ mellin h 0 = r := by
  have hE := hR.mass_add_fourier_one_eq hc hPm fun m hm => hblind m (by omega)
  have h1 : 𝓕 h 1 = 0 := by simpa using hblind 1 le_rfl
  have hpos := integral_normSq_zeta_mul_pos hPc hP (hR.integrable_normSq hc hP hPm)
  set I0 := ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t
  refine ⟨I0 / Real.pi, div_pos hpos Real.pi_pos, ?_⟩
  rw [h1, mul_zero, add_zero] at hE
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [← hE]
  field_simp

/-- **A mean-zero blind test activates the first mode.**  If `𝓕h(m) = 0` for every `m ≥ 2`,
`𝓜h(0) = 0`, and the Mellin transform is positive on the critical line, then
`𝓕h(1) = (1/2π) ∫ ‖ζ(½+it)‖² P(t) dt > 0`. -/
theorem SecondMomentRegular.fourier_one_pos_of_blind_of_mellin_zero_eq_zero
    (hR : SecondMomentRegular h c) (hc : 1 < c) (hPc : Continuous P) (hP : ∀ t, 0 < P t)
    (hPm : ∀ t : ℝ, mellin h (1 / 2 - t * I) = P t)
    (hblind : ∀ m : ℕ, 2 ≤ m → 𝓕 h (m : ℝ) = 0) (hmass : mellin h 0 = 0) :
    ∃ r : ℝ, 0 < r ∧ 𝓕 h 1 = r := by
  have hE := hR.mass_add_fourier_one_eq hc hPm hblind
  have hpos := integral_normSq_zeta_mul_pos hPc hP (hR.integrable_normSq hc hP hPm)
  set I0 := ∫ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ^ 2 * P t
  refine ⟨I0 / (2 * Real.pi), div_pos hpos (by positivity), ?_⟩
  rw [hmass, mul_zero, zero_add] at hE
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  rw [← hE]
  field_simp

end RHTower.ZetaSecondMomentPole
