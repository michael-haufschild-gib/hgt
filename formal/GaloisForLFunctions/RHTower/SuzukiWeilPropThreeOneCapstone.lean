import GaloisForLFunctions.RHTower.SuzukiWeilPropThreeOneDeterminacy

/-!
# Suzuki's Proposition 3.1

This module upgrades the almost-everywhere identity `𝔓_t(z) = P_t(z)` of
`SuzukiWeilPropThreeOneDeterminacy` to the pointwise statement of Suzuki,
*On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3), Proposition 3.1:

**`suzukiFrakP_eq_suzukiPtZeroSum`** — for every `t > 0` and every `z ≠ 0` off the Xi divisor with
`Im z > -1/2` and `1/2 - iz ≠ 1`, the prime--archimedean expression of eq. (1.6) equals the
multiplicity-exact Xi-zero series of eq. (3.2).

Both sides are continuous in `t` on `(0,∞)`.  For `P_t` this is a locally uniform Weierstrass bound
on the divisor sum; for `𝔓_t` the only nontrivial block is the finite prime block, and the key point
is that its `n`-th ray can be written as `Λ(n) n^{-1/2} · φ(max(t - log n, 0))` with `φ(0) = 0`, so
each ray is continuous through its own atom and only finitely many rays are active on a bounded
window.

The excluded points are exactly the poles of the *printed* decomposition (1.6), not of the function:
`z = 0` and `1/2 - iz = 1` are the two places where individual blocks blow up while the total is
regular.

Everything here is unconditional.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## Continuity of the Xi-zero series in the time variable -/

theorem continuousAt_suzukiPtZeroSum (z : ℂ) (t₀ : ℝ) :
    ContinuousAt (fun t : ℝ => suzukiPtZeroSum t z) t₀ := by
  set T : ℝ := |t₀| + 1 with hT
  have hTnn : (0 : ℝ) ≤ T := by rw [hT]; positivity
  set c : ℝ → ℝ := fun t => max (-T) (min t T) with hc
  have hcc : Continuous c := by fun_prop
  have hcb : ∀ t : ℝ, |c t| ≤ T := by
    intro t
    rw [abs_le]
    constructor
    · exact le_max_left _ _
    · rcases le_total t T with h | h
      · rw [hc]
        simp only
        rw [min_eq_left h]
        exact max_le (by linarith) h
      · rw [hc]
        simp only
        rw [min_eq_right h]
        exact max_le (by linarith) le_rfl
  have hFc : ∀ q : XiZeroCopy, Continuous (fun t : ℝ => suzukiPtZeroTerm (c t) z q) := by
    intro q
    have : Continuous (fun s : ℝ => suzukiPtZeroTerm s z q) := by
      show Continuous fun s : ℝ =>
        (Complex.exp (-(I * xiSpectralPoint q * (s : ℂ))) - 1) /
          (xiSpectralPoint q * (z - xiSpectralPoint q))
      fun_prop
    exact this.comp hcc
  have hFb : ∀ q : XiZeroCopy, ∀ t : ℝ,
      ‖suzukiPtZeroTerm (c t) z q‖
        ≤ (Real.exp (T / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖ := by
    intro q t
    refine (norm_suzukiPtZeroTerm_le (c t) z q).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have : Real.exp (|c t| / 2) ≤ Real.exp (T / 2) :=
      Real.exp_le_exp.mpr (by linarith [hcb t])
    linarith
  have hsum : Summable (fun q : XiZeroCopy =>
      (Real.exp (T / 2) + 1) * ‖(xiSpectralPoint q * (xiSpectralPoint q - z))⁻¹‖) :=
    (summable_xiResolventProduct_norm z).mul_left _
  have hcont : Continuous (fun t : ℝ => ∑' q : XiZeroCopy, suzukiPtZeroTerm (c t) z q) :=
    continuous_tsum hFc hsum hFb
  refine hcont.continuousAt.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ (by norm_num : (0 : ℝ) < 1)] with t ht
  have habs : |t| ≤ T := by
    rw [Metric.mem_ball, Real.dist_eq] at ht
    have := abs_sub_abs_le_abs_sub t t₀
    rw [hT]
    linarith
  have hct : c t = t := by
    rw [hc]
    simp only
    rw [min_eq_left (le_trans (le_abs_self t) habs),
      max_eq_right (by linarith [neg_abs_le t, habs])]
  rw [hct]
  rfl


/-! ## Continuity of `𝔓_t` in the time variable -/

/-- The prime ray in manifestly continuous form: the entering atom contributes `0` at `t = log n`. -/
theorem suzukiPrimeRayTerm_eq_max (z : ℂ) (n : ℕ) (t : ℝ) :
    suzukiPrimeRayTerm z n t
      = (screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((max (t - Real.log n) 0 : ℝ) : ℂ))) - 1) / (I * z)) := by
  rw [suzukiPrimeRayTerm]
  by_cases h : Real.log n ≤ t
  · rw [if_pos h, max_eq_left (by linarith)]
    congr 4
    push_cast
    ring
  · rw [if_neg h, max_eq_right (by linarith)]
    simp

theorem continuous_suzukiPrimeRayTerm (z : ℂ) (n : ℕ) :
    Continuous (fun t : ℝ => suzukiPrimeRayTerm z n t) := by
  have hfun : (fun t : ℝ => suzukiPrimeRayTerm z n t)
      = fun t : ℝ => (screwPrimeWeight n : ℂ) *
          ((Complex.exp (-(I * z * ((max (t - Real.log n) 0 : ℝ) : ℂ))) - 1) / (I * z)) := by
    funext t
    exact suzukiPrimeRayTerm_eq_max z n t
  rw [hfun]
  fun_prop

theorem norm_suzukiPrimeRayTerm_le_window {z : ℂ} {T s : ℝ} (_hs0 : 0 ≤ s) (hsT : s ≤ T)
    (n : ℕ) :
    ‖suzukiPrimeRayTerm z n s‖
      ≤ |screwPrimeWeight n| * ((Real.exp (T * max z.im 0) + 1) / ‖z‖) := by
  have hnn : (0 : ℝ) ≤ |screwPrimeWeight n| * ((Real.exp (T * max z.im 0) + 1) / ‖z‖) := by
    positivity
  rw [suzukiPrimeRayTerm]
  split_ifs with hif
  · rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
      have hcast : ((s : ℂ) - ((Real.log n : ℝ) : ℂ)) = (((s - Real.log n : ℝ)) : ℂ) := by
        push_cast; ring
      have hexpz : ‖Complex.exp (-(I * z * ((s : ℂ) - ((Real.log n : ℝ) : ℂ))))‖
          = Real.exp ((s - Real.log n) * z.im) := by
        rw [hcast, Complex.norm_exp, re_neg_I_mul_ofReal]
      have hlogn : (0 : ℝ) ≤ Real.log n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · exact Real.log_nonneg (by exact_mod_cast hn)
      have hsl : (0 : ℝ) ≤ s - Real.log n := by linarith
      have hbnd : Real.exp ((s - Real.log n) * z.im) ≤ Real.exp (T * max z.im 0) := by
        apply Real.exp_le_exp.mpr
        rcases le_total 0 z.im with him | him
        · rw [max_eq_left him]
          nlinarith
        · rw [max_eq_right him, mul_zero]
          nlinarith
      rw [norm_mul, norm_div, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [div_le_div_iff_of_pos_right hzpos]
      calc ‖Complex.exp (-(I * z * ((s : ℂ) - ((Real.log n : ℝ) : ℂ)))) - 1‖
          ≤ ‖Complex.exp (-(I * z * ((s : ℂ) - ((Real.log n : ℝ) : ℂ))))‖ + ‖(1 : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ Real.exp (T * max z.im 0) + 1 := by rw [hexpz, norm_one]; linarith
  · simpa using hnn

theorem suzukiPrimeRayTerm_eq_zero_of_lt {z : ℂ} {s : ℝ} {n : ℕ} (h : s < Real.log n) :
    suzukiPrimeRayTerm z n s = 0 := by
  rw [suzukiPrimeRayTerm, if_neg (by linarith)]


theorem continuousAt_suzukiFrakPPrime {z : ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousAt (fun t : ℝ => suzukiFrakPPrime t z) t₀ := by
  set T : ℝ := t₀ + 1 with hT
  have hTpos : (0 : ℝ) < T := by rw [hT]; linarith
  set c : ℝ → ℝ := fun t => max 0 (min t T) with hc
  have hcc : Continuous c := by fun_prop
  have hc0 : ∀ t : ℝ, 0 ≤ c t := fun t => le_max_left _ _
  have hcT : ∀ t : ℝ, c t ≤ T := fun t => max_le hTpos.le (min_le_right _ _)
  set u : ℕ → ℝ := fun n => if Real.log n ≤ T then
      |screwPrimeWeight n| * ((Real.exp (T * max z.im 0) + 1) / ‖z‖) else 0 with hu
  have husum : Summable u := by
    refine summable_of_ne_finset_zero (s := Finset.range (⌊Real.exp T⌋₊ + 1)) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have hfloor : Real.exp T < (n : ℝ) := by
      have h1 : Real.exp T < (⌊Real.exp T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h2 : ((⌊Real.exp T⌋₊ : ℝ) + 1) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos T) hfloor
    have hlog : T < Real.log n := by
      rw [← Real.log_exp T]
      exact Real.log_lt_log (Real.exp_pos T) hfloor
    rw [hu]
    simp only
    rw [if_neg (by linarith)]
  have hFb : ∀ n : ℕ, ∀ t : ℝ, ‖suzukiPrimeRayTerm z n (c t)‖ ≤ u n := by
    intro n t
    rw [hu]
    simp only
    by_cases hif : Real.log n ≤ T
    · rw [if_pos hif]
      exact norm_suzukiPrimeRayTerm_le_window (hc0 t) (hcT t) n
    · rw [if_neg hif]
      rw [suzukiPrimeRayTerm_eq_zero_of_lt (by linarith [hcT t, not_le.mp hif]), norm_zero]
  have hcont : Continuous (fun t : ℝ => ∑' n : ℕ, suzukiPrimeRayTerm z n (c t)) :=
    continuous_tsum (fun n => (continuous_suzukiPrimeRayTerm z n).comp hcc) husum hFb
  refine hcont.continuousAt.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ (lt_min ht₀ (by norm_num : (0 : ℝ) < 1))] with t ht
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
  have hlt : t < T := by
    have := ht.2
    have hm : min t₀ (1 : ℝ) ≤ 1 := min_le_right _ _
    rw [hT]
    linarith
  have hgt : (0 : ℝ) < t := by
    have := ht.1
    have hm : min t₀ (1 : ℝ) ≤ t₀ := min_le_left _ _
    linarith
  have hct : c t = t := by
    rw [hc]
    simp only
    rw [min_eq_left hlt.le, max_eq_right hgt.le]
  rw [hct]
  exact (suzukiFrakPPrime_eq_tsum t z).symm

theorem continuousAt_suzukiLerchDiff {w : ℂ} (hw : 0 < w.re) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ContinuousAt (fun t : ℝ => suzukiLerchDiff t w) t₀ := by
  set T : ℝ := t₀ + 1 with hT
  have hTpos : (0 : ℝ) < T := by rw [hT]; linarith
  set c : ℝ → ℝ := fun t => max 0 (min t T) with hc
  have hcc : Continuous c := by fun_prop
  have hc0 : ∀ t : ℝ, 0 ≤ c t := fun t => le_max_left _ _
  have hFc : ∀ n : ℕ, Continuous (fun t : ℝ => suzukiLerchDiffTerm (c t) w n) := by
    intro n
    have h : Continuous (fun s : ℝ => suzukiLerchDiffTerm s w n) := by
      show Continuous fun s : ℝ => (Real.exp (-(2 * (n : ℝ) * s)) : ℂ) *
        (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹)
      fun_prop
    exact h.comp hcc
  have hFb : ∀ n : ℕ, ∀ t : ℝ,
      ‖suzukiLerchDiffTerm (c t) w n‖ ≤ ‖((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹‖ := by
    intro n t
    rw [suzukiLerchDiffTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos _).le]
    have hle : Real.exp (-(2 * (n : ℝ) * c t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : (0 : ℝ) ≤ 2 * (n : ℝ) * c t := by
        have := hc0 t
        positivity
      linarith
    nlinarith [norm_nonneg (((n : ℂ) + w)⁻¹ - ((n : ℂ) + 1 / 4)⁻¹)]
  have hcont : Continuous (fun t : ℝ => ∑' n : ℕ, suzukiLerchDiffTerm (c t) w n) :=
    continuous_tsum hFc (summable_norm_iff.mpr (summable_lerchCoeff hw)) hFb
  refine hcont.continuousAt.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ (lt_min ht₀ (by norm_num : (0 : ℝ) < 1))] with t ht
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
  have hlt : t < T := by
    have hm : min t₀ (1 : ℝ) ≤ 1 := min_le_right _ _
    rw [hT]
    linarith [ht.2]
  have hgt : (0 : ℝ) < t := by
    have hm : min t₀ (1 : ℝ) ≤ t₀ := min_le_left _ _
    linarith [ht.1]
  have hct : c t = t := by
    rw [hc]
    simp only
    rw [min_eq_left hlt.le, max_eq_right hgt.le]
  rw [hct]
  rfl


theorem continuousAt_suzukiFrakP {z : ℂ} (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) {t₀ : ℝ}
    (ht₀ : 0 < t₀) : ContinuousAt (fun t : ℝ => suzukiFrakP t z) t₀ := by
  have hfun : (fun t : ℝ => suzukiFrakP t z)
      = fun t : ℝ => suzukiFrakPPolar t z + suzukiFrakPZeta t z + suzukiFrakPPrime t z
        + suzukiFrakPDigamma z + suzukiFrakPLerch t z := by
    funext t
    exact suzukiFrakP_eq_blocks t z
  rw [hfun]
  have h1 : ContinuousAt (fun t : ℝ => suzukiFrakPPolar t z) t₀ := by
    show ContinuousAt (fun t : ℝ =>
      4 * ((Real.exp (t / 2) : ℂ) - 1) / (1 + 2 * I * z)
        + 4 * ((Real.exp (-(t / 2)) : ℂ) - 1) / (1 - 2 * I * z)) t₀
    fun_prop
  have h2 : ContinuousAt (fun t : ℝ => suzukiFrakPZeta t z) t₀ := by
    show ContinuousAt (fun t : ℝ =>
      (Complex.exp (-(I * z * (t : ℂ))) - 1) / (I * z) *
        logDeriv riemannZeta (1 / 2 - I * z)) t₀
    fun_prop
  have h5 : ContinuousAt (fun t : ℝ => suzukiFrakPLerch t z) t₀ := by
    have hA : ContinuousAt (fun t : ℝ => ((Real.exp (-(t / 2)) : ℝ) : ℂ)) t₀ := by fun_prop
    show ContinuousAt (fun t : ℝ =>
      -(((Real.exp (-(t / 2)) : ℝ) : ℂ) * suzukiLerchDiff t ((1 : ℂ) / 4 - I * z / 2)
        / (2 * I * z))) t₀
    exact ((hA.mul (continuousAt_suzukiLerchDiff hw ht₀)).div_const _).neg
  exact (((h1.add h2).add (continuousAt_suzukiFrakPPrime ht₀)).add continuousAt_const).add h5

/-- A function continuous on `(0,∞)` that vanishes almost everywhere there vanishes everywhere
there. -/
theorem eq_zero_of_ae_eq_zero_of_continuousAt {h : ℝ → ℂ}
    (hc : ∀ t : ℝ, 0 < t → ContinuousAt h t)
    (hae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), h t = 0) {t₀ : ℝ} (ht₀ : 0 < t₀) :
    h t₀ = 0 := by
  by_contra hne
  have hev : ∀ᶠ t in 𝓝 t₀, h t ≠ 0 := (hc t₀ ht₀).eventually_ne hne
  have hev2 : ∀ᶠ t in 𝓝 t₀, (0 : ℝ) < t := isOpen_Ioi.eventually_mem ht₀
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (hev.and hev2)
  have hsub : Metric.ball t₀ δ ⊆ {t : ℝ | ¬ h t = 0} := by
    intro t htb
    rw [Metric.mem_ball] at htb
    exact (hδ htb).1
  have hsub2 : Metric.ball t₀ δ ⊆ Ioi (0 : ℝ) := by
    intro t htb
    rw [Metric.mem_ball] at htb
    exact (hδ htb).2
  have hnull : volume.restrict (Ioi (0 : ℝ)) {t : ℝ | ¬ h t = 0} = 0 := ae_iff.mp hae
  have hball : volume.restrict (Ioi (0 : ℝ)) (Metric.ball t₀ δ) = 0 :=
    measure_mono_null hsub hnull
  rw [Measure.restrict_apply' measurableSet_Ioi,
    Set.inter_eq_left.mpr hsub2, Real.volume_ball] at hball
  have : ENNReal.ofReal (2 * δ) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    linarith
  exact this hball

/-- **Suzuki, Proposition 3.1.**  For every `t > 0` and every base point `z ≠ 0` off the Xi divisor
with `Im z > -1/2` and `1/2 - iz ≠ 1`, the prime--archimedean expression `𝔓_t(z)` of eq. (1.6)
equals the multiplicity-exact Xi-zero series `P_t(z)` of eq. (3.2). -/
theorem suzukiFrakP_eq_suzukiPtZeroSum {z : ℂ} (hz0 : z ≠ 0)
    (hw : 0 < ((1 : ℂ) / 4 - I * z / 2).re) (hs1 : (1 : ℂ) / 2 - I * z ≠ 1) (hXi : XiC z ≠ 0)
    {t : ℝ} (ht : 0 < t) : suzukiFrakP t z = suzukiPtZeroSum t z := by
  have hc : ∀ s : ℝ, 0 < s →
      ContinuousAt (fun r : ℝ => suzukiFrakP r z - suzukiPtZeroSum r z) s := by
    intro s hs
    exact (continuousAt_suzukiFrakP hw hs).sub ((continuousAt_suzukiPtZeroSum z s))
  have hae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      suzukiFrakP s z - suzukiPtZeroSum s z = 0 := by
    filter_upwards [suzukiFrakP_ae_eq_suzukiPtZeroSum hz0 hw hs1 hXi] with s hs
    rw [hs, sub_self]
  have := eq_zero_of_ae_eq_zero_of_continuousAt hc hae ht
  linear_combination this

end
end RHTower
