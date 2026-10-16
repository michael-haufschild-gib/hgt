import GaloisForLFunctions.RHTower.CHMDKleinGordonCramerContinuation

/-!
# CHMD: the exact boundary singularity of the Klein–Gordon causal wave

At a prime point `p = log n + i` (`Λ(n) ≠ 0`) the massless wave has a simple pole,
`Φ₀(w) = R/(w − p) + O(1)` with `R = (2i/π)Λ(n)/√n`.  The Klein–Gordon causal wave
`Φ = L[Φ₀]` samples `Φ₀` along the whole segment `[0, z]`, and the Bessel tail turns the pole into a
logarithmic branch.  Along the approach `z = p − iε` from inside the time strip
(`exists_kgZeroWave_boundary_expansion`):

`Φ(z) = R/(z − p) − z R log(z − p) + O(1)`.

The tail contributes `z R (Log(z − p) − Log(−p))` exactly, from `∫_0^1 z dt/(zt − p) = Log(z − p) − Log(−p)`;
the remaining pieces are bounded, using `|B(w) − 1| ≤ (|w|/4) e^{|w|/4}`
(`norm_lightConeBessel_sub_one_le`) against `|zt − p| ≥ (1 − t) log n`, and the bounded polar remainder
`D(u) − (−2i/π)/(u − i)` of the d'Alembert kernel (`exists_dAlembertKernel_sub_polar_le`).

Consequently the causal wave has **no meromorphic continuation** at any prime point
(`not_meromorphicAt_kgZeroWave`, `not_meromorphicAt_kgZeroWave_four`): a pole of finite order is
excluded by the simple-pole rate `ε Φ(p − iε) → −(2/π)Λ(n)/√n`, and a simple pole by the logarithmic
term, whose coefficient `−pR` does not vanish.  The singular structure at the primes is exactly
"simple pole with residue `(2i/π)Λ(n)/√n` plus a logarithmic branch with coefficient `−pR`".

`kgZeroWave_cramer` collects the continuation, the simple-pole rate at all four families
`±log n ± i`, the singular expansion and the absence of a meromorphic continuation.
-/

open Complex MeasureTheory Set Filter Topology Metric Zeta23
open scoped Real ComplexConjugate Nat
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.CHMDLightCone

open RHTower.CHMDGrowthCollapse

/-! ## The polar remainder of the d'Alembert kernel at `i` -/

theorem sinhSlope_I : sinhSlope I = 0 :=
  (sinhSlope_eq_zero_iff I).mpr ⟨1, one_ne_zero, by simp⟩

/-- `D(u) − (−2i/π)/(u − i)` is bounded near `u = i`. -/
theorem exists_dAlembertKernel_sub_polar_le :
    ∃ δ > 0, ∃ M : ℝ, ∀ u : ℂ, ‖u - I‖ < δ →
      ‖dAlembertKernel u - (-2 * I / π) / (u - I)‖ ≤ M := by
  set q : ℂ → ℂ := dslope sinhSlope I with hq
  have hqd : Differentiable ℂ q := fun u =>
    ((Complex.differentiableOn_dslope (f := sinhSlope) (c := I) (s := Set.univ) Filter.univ_mem).mpr
      differentiable_sinhSlope.differentiableOn u (mem_univ _)).differentiableAt Filter.univ_mem
  have hsplit : ∀ u, u ≠ I → sinhSlope u = (u - I) * q u := by
    intro u hu
    simp only [hq]
    rw [dslope_of_ne _ hu, slope_def_field, sinhSlope_I, sub_zero]
    field_simp [sub_ne_zero.mpr hu]
  have hc : (-2 * I / π : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, I_ne_zero]
  -- `2/q(u) = (u − i) D(u) → −2i/π`, so `q(i) = πi ≠ 0`
  have hlim : Tendsto (fun u => 2 / q u) (𝓝[≠] I) (𝓝 (-2 * I / π)) := by
    refine tendsto_sub_I_mul_dAlembertKernel.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu' : u - I ≠ 0 := sub_ne_zero.mpr hu
    rw [dAlembertKernel, hsplit u hu]
    by_cases hq0 : q u = 0
    · simp [hq0]
    · field_simp
  have hqI : q I = 2 / (-2 * I / π) := by
    have h1 : Tendsto (fun u => (2 / q u)⁻¹ * 2) (𝓝[≠] I) (𝓝 ((-2 * I / π)⁻¹ * 2)) :=
      (hlim.inv₀ hc).mul_const 2
    have h2 : (fun u => (2 / q u)⁻¹ * 2) = q := by
      funext u; rw [inv_div, div_mul_cancel₀ _ two_ne_zero]
    rw [h2] at h1
    have h3 : Tendsto q (𝓝[≠] I) (𝓝 (q I)) := (hqd I).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [tendsto_nhds_unique h3 h1, inv_div, div_mul_eq_mul_div, mul_comm]
    field_simp
  have hqI0 : q I ≠ 0 := by
    rw [hqI]; exact div_ne_zero two_ne_zero hc
  set g : ℂ → ℂ := fun u => 2 / q u with hg
  have hgI : g I = -2 * I / π := by
    simp only [hg, hqI]; field_simp
  have hgd : DifferentiableAt ℂ g I := (differentiableAt_const _).div (hqd I) hqI0
  obtain ⟨L, hL⟩ := hgd.isBigO_sub.bound
  obtain ⟨δ, hδ, hδL⟩ := Metric.eventually_nhds_iff.mp hL
  refine ⟨δ, hδ, max L 0, fun u hu => ?_⟩
  by_cases huI : u = I
  · subst huI; simp [dAlembertKernel, sinhSlope_I]
  have hu' : u - I ≠ 0 := sub_ne_zero.mpr huI
  have hD : dAlembertKernel u = g u / (u - I) := by
    rw [dAlembertKernel, hsplit u huI]
    simp only [hg]
    by_cases hq0 : q u = 0
    · simp [hq0]
    · field_simp
  rw [hD, ← hgI, ← sub_div, norm_div, div_le_iff₀ (norm_pos_iff.mpr hu')]
  have := hδL (by rw [dist_eq_norm]; exact hu)
  exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-! ## The Bessel kernel near zero -/

/-- `‖B(w) − 1‖ ≤ (‖w‖/4) e^{‖w‖/4}`. -/
theorem norm_lightConeBessel_sub_one_le (w : ℂ) :
    ‖lightConeBessel w - 1‖ ≤ ‖w‖ / 4 * Real.exp (‖w‖ / 4) := by
  have hs := (summable_norm_lightConeBesselTerm w).of_norm
  have h0 : lightConeBesselTerm w 0 = 1 := by simp [lightConeBesselTerm]
  rw [lightConeBessel, hs.tsum_eq_zero_add, h0, add_sub_cancel_left]
  refine tsum_of_norm_bounded ((hasSum_real_exp_series (‖w‖ / 4)).mul_left (‖w‖ / 4))
    fun k => (norm_lightConeBesselTerm_le w (k + 1)).trans ?_
  have hk : (k ! : ℝ) ≤ (k + 1)! := by exact_mod_cast Nat.factorial_le (Nat.le_succ k)
  have hk0 : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
  calc (‖w‖ / 4) ^ (k + 1) / ((k + 1)! : ℝ) ≤ (‖w‖ / 4) ^ (k + 1) / (k ! : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hk0 hk
    _ = ‖w‖ / 4 * ((‖w‖ / 4) ^ k / k !) := by rw [pow_succ]; ring

/-! ## The logarithmic integral -/

/-- `∫_0^1 z/(zt − p) dt = Log(z − p) − Log(−p)` when `zt − p` stays off the real axis. -/
theorem integral_div_mul_sub_eq_log {z p : ℂ} (hz : ∀ t ∈ Icc (0 : ℝ) 1, (z * t - p).im ≠ 0) :
    ∫ t in (0 : ℝ)..1, z / (z * t - p) = Complex.log (z - p) - Complex.log (-p) := by
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, z * t - p ≠ 0 := fun t ht h => hz t ht (by rw [h]; simp)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ => Complex.log (z * t - p))]
  · simp
  · intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : HasDerivAt (fun t : ℝ => z * (t : ℂ) - p) z t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.const_mul z).sub_const p
    exact h1.clog_real (mem_slitPlane_iff.mpr (Or.inr (hz t ht)))
  · refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact (continuousAt_const.div ((continuous_const.mul continuous_ofReal).sub
      continuous_const).continuousAt (hne t ht)).continuousWithinAt

/-! ## The massless wave near a prime point -/

/-- **The massless wave near `log n + i`**: `Φ₀(w) − R/(w − p)` is bounded on a half-disc below `p`. -/
theorem exists_masslessZeroWave_sub_polar_le {n₀ : ℕ} (hw : chmdPrimeWeight n₀ ≠ 0) :
    ∃ δ > 0, δ ≤ 1 / 2 ∧ ∃ M : ℝ, ∀ v : ℂ, dist v ((Real.log n₀ : ℂ) + I) < δ → v.im < 1 →
      ‖masslessZeroWave v - 2 * I / π * chmdPrimeWeight n₀ / (v - ((Real.log n₀ : ℂ) + I))‖ ≤ M := by
  set p : ℂ := (Real.log n₀ : ℂ) + I with hp
  have hlog := half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)
  obtain ⟨δD, hδD, MD, hMD⟩ := exists_dAlembertKernel_sub_polar_le
  set H := masslessRegularPart (1 / 2) n₀
  have hHc : ContinuousAt H p :=
    (differentiableAt_masslessRegularPart (by norm_num) le_rfl hw).continuousAt
  obtain ⟨δH, hδH, hHb⟩ := Metric.continuousAt_iff.mp hHc 1 one_pos
  set δ := min (min δD δH) (min (Real.log n₀ - 1 / 2) (1 / 2))
  have hδ : 0 < δ := lt_min (lt_min hδD hδH) (lt_min (by linarith) (by norm_num))
  refine ⟨δ, hδ, (min_le_right _ _).trans (min_le_right _ _), ‖H p‖ + 1 +
    ‖(chmdPrimeWeight n₀ : ℂ)‖ * MD, fun v hv hvim => ?_⟩
  have hpre : p.re = Real.log n₀ := by rw [hp, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
  have hpim : p.im = 1 := by rw [hp, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
  have hn : ‖v - p‖ < δ := by rw [← dist_eq_norm]; exact hv
  have h1 := (Complex.abs_re_le_norm (v - p)).trans_lt hn
  have h2 := (Complex.abs_im_le_norm (v - p)).trans_lt hn
  rw [Complex.sub_re, hpre] at h1
  rw [Complex.sub_im, hpim] at h2
  have hδ1 : δ ≤ Real.log n₀ - 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hvre : 1 / 2 < v.re := by linarith [(abs_lt.mp h1).1]
  have hvim1 : -1 / 2 < v.im := by linarith [(abs_lt.mp h2).1]
  rw [masslessZeroWave_eq_masslessContinuation (by norm_num) le_rfl hvre hvim1 hvim,
    masslessContinuation_eq_regular_sub_polar (1 / 2) n₀ (by linarith)]
  have hu : (v - (Real.log n₀ : ℂ)) - I = v - p := by rw [hp]; ring
  have hδD' : δ ≤ δD := (min_le_left _ _).trans (min_le_left _ _)
  have hδH' : δ ≤ δH := (min_le_left _ _).trans (min_le_right _ _)
  have hD := hMD (v - (Real.log n₀ : ℂ)) (by rw [hu]; exact lt_of_lt_of_le hn hδD')
  rw [hu] at hD
  have hHv : ‖H v‖ ≤ ‖H p‖ + 1 := by
    have := hHb (lt_of_lt_of_le hv hδH')
    rw [dist_eq_norm] at this
    linarith [norm_sub_norm_le (H v) (H p)]
  have heq : H v - (chmdPrimeWeight n₀ : ℂ) * dAlembertKernel (v - Real.log n₀) -
      2 * I / π * chmdPrimeWeight n₀ / (v - p) =
      H v - (chmdPrimeWeight n₀ : ℂ) * (dAlembertKernel (v - Real.log n₀) - -2 * I / π / (v - p)) := by
    ring
  rw [heq]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  linarith [mul_le_mul_of_nonneg_left hD (norm_nonneg ((chmdPrimeWeight n₀ : ℂ)))]

/-! ## The singular expansion -/

/-- The Bessel difference against the light-cone denominator: for `Re z = Re p = L > 0` and
`t ∈ [0,1]`, `‖(B(2z²(1−t²)) − 1)/(zt − p)‖ ≤ ‖z‖² e^{‖z‖²/2}/L`. -/
theorem norm_lightConeBessel_sub_one_div_le {z p : ℂ} {L : ℝ} (hL : 0 < L) (hz : z.re = L)
    (hp : p.re = L) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1) * (1 / (z * t - p))‖ ≤
      ‖z‖ ^ 2 * Real.exp (‖z‖ ^ 2 / 2) / L := by
  rcases ht1.lt_or_eq with ht1 | rfl
  · have hpos : 0 < (1 - t) * L := by nlinarith
    have hnorm : (1 - t) * L ≤ ‖z * t - p‖ := by
      have := Complex.abs_re_le_norm (z * t - p)
      rw [Complex.sub_re, Complex.mul_re, hz, hp, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero, abs_of_nonpos (by nlinarith)] at this
      linarith
    have hw : ‖2 * z ^ 2 * (1 - (t : ℂ) ^ 2)‖ = ‖z‖ ^ 2 * (2 * (1 - t ^ 2)) := by
      rw [show (1 - (t : ℂ) ^ 2) = ((1 - t ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_mul, norm_mul,
        norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by nlinarith),
        show ‖(2 : ℂ)‖ = 2 by norm_num]
      ring
    have hB := norm_lightConeBessel_sub_one_le (2 * z ^ 2 * (1 - (t : ℂ) ^ 2))
    rw [hw] at hB
    have h1t : 2 * (1 - t ^ 2) / 4 ≤ 1 - t := by nlinarith
    have h1t' : 2 * (1 - t ^ 2) / 4 ≤ 1 / 2 := by nlinarith
    have hz2 := sq_nonneg ‖z‖
    have hB' : ‖lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1‖ ≤
        ‖z‖ ^ 2 * (1 - t) * Real.exp (‖z‖ ^ 2 / 2) := by
      refine hB.trans ?_
      rw [show ‖z‖ ^ 2 * (2 * (1 - t ^ 2)) / 4 = ‖z‖ ^ 2 * (2 * (1 - t ^ 2) / 4) by ring]
      exact mul_le_mul (mul_le_mul_of_nonneg_left h1t hz2)
        (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by nlinarith)
    rw [norm_mul, norm_div, norm_one, ← div_eq_mul_one_div, div_le_iff₀ (hpos.trans_le hnorm)]
    calc ‖lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1‖
        ≤ ‖z‖ ^ 2 * (1 - t) * Real.exp (‖z‖ ^ 2 / 2) := hB'
      _ = ‖z‖ ^ 2 * Real.exp (‖z‖ ^ 2 / 2) / L * ((1 - t) * L) := by field_simp
      _ ≤ ‖z‖ ^ 2 * Real.exp (‖z‖ ^ 2 / 2) / L * ‖z * t - p‖ :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
  · simp only [ofReal_one, one_pow, sub_self, mul_zero, lightConeBessel_zero, zero_mul, norm_zero]
    positivity

/-- **The massless wave along the light-cone segments below a prime point**:
`Φ₀(w) − R/(w − p)` is bounded on every segment `[0, p − iε]`, `0 < ε < 1`. -/
theorem exists_masslessZeroWave_sub_polar_segment_le {n₀ : ℕ} (hw : chmdPrimeWeight n₀ ≠ 0) :
    ∃ M : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖masslessZeroWave (((Real.log n₀ : ℂ) + I - ε * I) * t) -
        2 * I / π * chmdPrimeWeight n₀ / (((Real.log n₀ : ℂ) + I - ε * I) * t -
          ((Real.log n₀ : ℂ) + I))‖ ≤ M := by
  set p : ℂ := (Real.log n₀ : ℂ) + I with hp
  set R : ℂ := 2 * I / π * chmdPrimeWeight n₀ with hR
  have hlog := half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)
  have hlog0 : 0 < Real.log n₀ := by linarith
  have hpre : p.re = Real.log n₀ := by rw [hp, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
  have hpim : p.im = 1 := by rw [hp, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
  obtain ⟨δ, hδ, hδ2, MH, hMH⟩ := exists_masslessZeroWave_sub_polar_le hw
  have hη1 : δ / (Real.log n₀ + 2) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hηpos : 0 < δ / (Real.log n₀ + 2) := by positivity
  have hKc : IsCompact (Icc (0 : ℝ) (Real.log n₀) ×ℂ Icc (0 : ℝ) (1 - δ / (Real.log n₀ + 2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hKcs : Icc (0 : ℝ) (Real.log n₀) ×ℂ Icc (0 : ℝ) (1 - δ / (Real.log n₀ + 2)) ⊆
      causalTimeStrip := fun v hv => by
    have := (Complex.mem_reProdIm.mp hv).2
    show |v.im| < 1
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn
    (differentiableOn_masslessZeroWave.continuousOn.mono hKcs)
  refine ⟨max MH (M₂ + ‖R‖ / δ), fun ε hε0 hε1 t ht0 ht1 => ?_⟩
  set v := (p - ε * I) * t
  have hvre : v.re = t * Real.log n₀ := by
    simp only [v, Complex.mul_re, Complex.sub_re, Complex.sub_im, hpre, hpim, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hvim : v.im = t * (1 - ε) := by
    simp only [v, Complex.mul_im, Complex.sub_re, Complex.sub_im, hpre, hpim, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hvim1 : v.im < 1 := by rw [hvim]; nlinarith
  by_cases hnear : dist v p < δ
  · exact (hMH v hnear hvim1).trans (le_max_left _ _)
  · have hfar : δ ≤ ‖v - p‖ := by rw [← dist_eq_norm]; exact not_lt.mp hnear
    have hvK : v ∈ Icc (0 : ℝ) (Real.log n₀) ×ℂ Icc (0 : ℝ) (1 - δ / (Real.log n₀ + 2)) := by
      refine Complex.mem_reProdIm.mpr ⟨⟨by rw [hvre]; positivity, by rw [hvre]; nlinarith⟩,
        ⟨by rw [hvim]; nlinarith, ?_⟩⟩
      rw [hvim]
      by_contra hcon'
      have hcon := not_le.mp hcon'
      have hd : ‖v - p‖ ≤ (1 - t) * Real.log n₀ + (1 - t * (1 - ε)) := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [Complex.sub_re, Complex.sub_im, hvre, hvim, hpre, hpim]
        rw [abs_of_nonpos (by nlinarith), abs_of_nonpos (by nlinarith)]
        linarith
      have h2 : 1 - t < δ / (Real.log n₀ + 2) := by nlinarith
      have : ‖v - p‖ < δ := by
        calc ‖v - p‖ ≤ (1 - t) * Real.log n₀ + (1 - t * (1 - ε)) := hd
          _ ≤ δ / (Real.log n₀ + 2) * Real.log n₀ + δ / (Real.log n₀ + 2) := by nlinarith
          _ < δ := by field_simp; nlinarith
      linarith
    have hRb : ‖R / (v - p)‖ ≤ ‖R‖ / δ := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hδ hfar
    calc ‖masslessZeroWave v - R / (v - p)‖ ≤ ‖masslessZeroWave v‖ + ‖R / (v - p)‖ :=
          norm_sub_le _ _
      _ ≤ M₂ + ‖R‖ / δ := add_le_add (hM₂ v hvK) hRb
      _ ≤ max MH (M₂ + ‖R‖ / δ) := le_max_right _ _

/-- **The singular expansion of the causal wave at `p = log n + i`.**  Along `z = p − iε`,
`Φ(z) = R/(z − p) − z R Log(z − p) + O(1)` with `R = (2i/π) Λ(n)/√n`. -/
theorem exists_kgZeroWave_boundary_expansion {n₀ : ℕ} (hw : chmdPrimeWeight n₀ ≠ 0) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖kgZeroWave ((Real.log n₀ : ℂ) + I - ε * I) -
          2 * I / π * chmdPrimeWeight n₀ / (-(ε * I)) +
        ((Real.log n₀ : ℂ) + I - ε * I) * (2 * I / π * chmdPrimeWeight n₀) *
          Complex.log (-(ε * I))‖ ≤ C := by
  obtain ⟨Mh, hMh⟩ := exists_masslessZeroWave_sub_polar_segment_le hw
  set p : ℂ := (Real.log n₀ : ℂ) + I with hp
  set R : ℂ := 2 * I / π * chmdPrimeWeight n₀ with hR
  have hlog := half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)
  have hlog0 : 0 < Real.log n₀ := by linarith
  have hpre : p.re = Real.log n₀ := by rw [hp, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
  have hpim : p.im = 1 := by rw [hp, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
  have hMh0 : 0 ≤ Mh := (norm_nonneg _).trans (hMh (1 / 2) (by norm_num) (by norm_num) 0 le_rfl
    zero_le_one)
  set Cp := ‖p‖ + 1 with hCp
  have hCp0 : 0 ≤ Cp := by positivity
  set CB := Real.exp (Cp ^ 2 / 2) with hCB
  refine ⟨Mh + Cp * ‖R‖ * ‖Complex.log (-p)‖ + Cp ^ 2 * ‖R‖ * (Cp ^ 2 * CB / Real.log n₀) +
    Cp ^ 2 * (CB * Mh), fun ε hε0 hε1 => ?_⟩
  set z := p - ε * I with hz
  have hzre : z.re = Real.log n₀ := by
    rw [hz, Complex.sub_re, hpre, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have hzim : z.im = 1 - ε := by
    rw [hz, Complex.sub_im, hpim, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]; ring
  have hzn : ‖z‖ ≤ Cp := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hε0]
    linarith
  have hzn2 : ‖z‖ ^ 2 ≤ Cp ^ 2 := by gcongr
  have hEz : Real.exp (‖z‖ ^ 2 / 2) ≤ CB := Real.exp_le_exp.mpr (by linarith)
  have hz0 : z ≠ 0 := fun h0 => by rw [h0, Complex.zero_re] at hzre; linarith
  have hzs : |z.im| < 1 := by rw [hzim, abs_lt]; constructor <;> linarith
  have hzp : z - p = -(ε * I) := by rw [hz]; ring
  have hims : ∀ t ∈ Icc (0 : ℝ) 1, (z * t - p).im ≠ 0 := by
    intro t ht
    rw [Complex.sub_im, Complex.mul_im, hzre, hzim, hpim, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith [ht.1, ht.2]
  have hden : ∀ t ∈ Icc (0 : ℝ) 1, z * t - p ≠ 0 := fun t ht h0 => hims t ht (by rw [h0]; simp)
  have hstrip : ∀ t ∈ Icc (0 : ℝ) 1, z * t ∈ causalTimeStrip := by
    intro t ht
    show |(z * t).im| < 1
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, hzim, abs_mul,
      abs_of_pos (by linarith : (0 : ℝ) < 1 - ε), abs_of_nonneg ht.1]
    nlinarith [ht.2]
  have hcB : Continuous fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) :=
    differentiable_lightConeBessel.continuous.comp (by fun_prop)
  have hcinv : ContinuousOn (fun t : ℝ => 1 / (z * t - p)) (Icc 0 1) := fun t ht =>
    (continuousAt_const.div ((continuous_const.mul continuous_ofReal).sub
      continuous_const).continuousAt (hden t ht)).continuousWithinAt
  have hcΦ : ContinuousOn (fun t : ℝ => masslessZeroWave (z * t)) (Icc 0 1) := fun t ht =>
    (ContinuousAt.comp (f := fun t : ℝ => z * t) (g := masslessZeroWave)
      ((differentiableOn_masslessZeroWave.differentiableAt
        (isOpen_causalTimeStrip.mem_nhds (hstrip t ht))).continuousAt)
      (continuous_const.mul continuous_ofReal).continuousAt).continuousWithinAt
  have hcR : ContinuousOn (fun t : ℝ => R / (z * t - p)) (Icc 0 1) := fun t ht =>
    (continuousAt_const.div ((continuous_const.mul continuous_ofReal).sub
      continuous_const).continuousAt (hden t ht)).continuousWithinAt
  have hII : ∀ (f : ℝ → ℂ), ContinuousOn f (Icc 0 1) → IntervalIntegrable f volume 0 1 :=
    fun f hf => ContinuousOn.intervalIntegrable (by rwa [Set.uIcc_of_le zero_le_one])
  -- the three pieces of the tail
  have hsplit : (∫ t in (0 : ℝ)..1,
        lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * masslessZeroWave (z * t)) =
      R * (∫ t in (0 : ℝ)..1, 1 / (z * t - p)) +
        R * (∫ t in (0 : ℝ)..1, (lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1) *
          (1 / (z * t - p))) +
        ∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
          (masslessZeroWave (z * t) - R / (z * t - p)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add
        (hII (fun t : ℝ => R * (1 / (z * t - p))) (continuousOn_const.mul hcinv))
        (hII (fun t : ℝ => R * ((lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1) *
          (1 / (z * t - p)))) (continuousOn_const.mul
            ((hcB.continuousOn.sub continuousOn_const).mul hcinv))),
      ← intervalIntegral.integral_add
        (hII (fun t : ℝ => R * (1 / (z * t - p)) +
          R * ((lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1) * (1 / (z * t - p))))
          ((continuousOn_const.mul hcinv).add (continuousOn_const.mul
            ((hcB.continuousOn.sub continuousOn_const).mul hcinv))))
        (hII (fun t : ℝ => lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
          (masslessZeroWave (z * t) - R / (z * t - p))) (hcB.continuousOn.mul (hcΦ.sub hcR)))]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hlogint : (∫ t in (0 : ℝ)..1, 1 / (z * t - p)) =
      (Complex.log (z - p) - Complex.log (-p)) / z := by
    rw [← integral_div_mul_sub_eq_log hims, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t _ => ?_
    field_simp
  -- bounds on the pieces
  have hJb : ‖∫ t in (0 : ℝ)..1, (lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1) *
      (1 / (z * t - p))‖ ≤ Cp ^ 2 * CB / Real.log n₀ := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := Cp ^ 2 * CB / Real.log n₀)
      fun t ht => ?_).trans (by norm_num)
    rw [Set.uIoc_of_le zero_le_one] at ht
    refine (norm_lightConeBessel_sub_one_div_le hlog0 hzre hpre ht.1.le ht.2).trans ?_
    gcongr
  have hKb : ‖∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      (masslessZeroWave (z * t) - R / (z * t - p))‖ ≤ CB * Mh := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := CB * Mh)
      fun t ht => ?_).trans (by norm_num)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    rw [norm_mul]
    exact mul_le_mul ((norm_lightConeBessel_light_cone_le z hta).trans hEz)
      (hMh ε hε0 hε1 t ht.1.le ht.2) (norm_nonneg _) (Real.exp_pos _).le
  have hhz : ‖masslessZeroWave z - R / (z - p)‖ ≤ Mh := by
    have h1 := hMh ε hε0 hε1 1 zero_le_one le_rfl
    simp only [Complex.ofReal_one, mul_one] at h1
    exact h1
  -- assemble
  have hmain : kgZeroWave z = masslessZeroWave z - z ^ 2 * (∫ t in (0 : ℝ)..1,
      lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) * masslessZeroWave (z * t)) := by
    rw [kgZeroWave_eq_lightConeTransmuteC hzs, lightConeTransmuteC]
  rw [hmain, hsplit, hlogint, ← hzp]
  set J := ∫ t in (0 : ℝ)..1, (lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) - 1) *
      (1 / (z * t - p))
  set K := ∫ t in (0 : ℝ)..1, lightConeBessel (2 * z ^ 2 * (1 - (t : ℂ) ^ 2)) *
      (masslessZeroWave (z * t) - R / (z * t - p))
  have hid : masslessZeroWave z - z ^ 2 *
      (R * ((Complex.log (z - p) - Complex.log (-p)) / z) + R * J + K) - R / (z - p) +
      z * R * Complex.log (z - p) =
      (masslessZeroWave z - R / (z - p)) + z * R * Complex.log (-p) - z ^ 2 * R * J -
        z ^ 2 * K := by
    rw [show z ^ 2 * (R * ((Complex.log (z - p) - Complex.log (-p)) / z) + R * J + K) =
      z * R * (Complex.log (z - p) - Complex.log (-p)) + z ^ 2 * R * J + z ^ 2 * K by
        field_simp]
    ring
  rw [hid]
  calc ‖(masslessZeroWave z - R / (z - p)) + z * R * Complex.log (-p) - z ^ 2 * R * J -
        z ^ 2 * K‖
      ≤ ‖masslessZeroWave z - R / (z - p)‖ + ‖z‖ * ‖R‖ * ‖Complex.log (-p)‖ +
          ‖z‖ ^ 2 * ‖R‖ * ‖J‖ + ‖z‖ ^ 2 * ‖K‖ := by
        have e1 := norm_sub_le ((masslessZeroWave z - R / (z - p)) + z * R * Complex.log (-p) -
          z ^ 2 * R * J) (z ^ 2 * K)
        have e2 := norm_sub_le ((masslessZeroWave z - R / (z - p)) + z * R * Complex.log (-p))
          (z ^ 2 * R * J)
        have e3 := norm_add_le (masslessZeroWave z - R / (z - p)) (z * R * Complex.log (-p))
        have n1 : ‖z * R * Complex.log (-p)‖ = ‖z‖ * ‖R‖ * ‖Complex.log (-p)‖ := by
          rw [norm_mul, norm_mul]
        have n2 : ‖z ^ 2 * R * J‖ = ‖z‖ ^ 2 * ‖R‖ * ‖J‖ := by rw [norm_mul, norm_mul, norm_pow]
        have n3 : ‖z ^ 2 * K‖ = ‖z‖ ^ 2 * ‖K‖ := by rw [norm_mul, norm_pow]
        linarith
    _ ≤ Mh + Cp * ‖R‖ * ‖Complex.log (-p)‖ + Cp ^ 2 * ‖R‖ * (Cp ^ 2 * CB / Real.log n₀) +
          Cp ^ 2 * (CB * Mh) := by
        gcongr

/-! ## No meromorphic continuation at the prime points -/

/-- Along `z = p − iε` the causal wave minus its polar part is unbounded: this is the logarithmic
branch `−z R Log(z − p)`, whose modulus is at least `log n · |R| · |log ε|`. -/
theorem tendsto_norm_kgZeroWave_sub_polar_atTop {n₀ : ℕ} (hw : chmdPrimeWeight n₀ ≠ 0) :
    Tendsto (fun ε : ℝ => ‖kgZeroWave ((Real.log n₀ : ℂ) + I - ε * I) -
      2 * I / π * chmdPrimeWeight n₀ / (-(ε * I))‖) (𝓝[>] 0) atTop := by
  obtain ⟨C, hC⟩ := exists_kgZeroWave_boundary_expansion hw
  have hlog := half_lt_log_of_two_le (two_le_of_chmdPrimeWeight_ne_zero hw)
  have hR0 : (2 * I / π * chmdPrimeWeight n₀ : ℂ) ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) (ofReal_ne_zero.mpr hw)
  have hc : 0 < Real.log n₀ * ‖(2 * I / π * chmdPrimeWeight n₀ : ℂ)‖ :=
    mul_pos (by linarith) (norm_pos_iff.mpr hR0)
  have hlim : Tendsto (fun ε : ℝ =>
      Real.log n₀ * ‖(2 * I / π * chmdPrimeWeight n₀ : ℂ)‖ * (-Real.log ε) + -C) (𝓝[>] 0) atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).const_mul_atTop hc)
  refine tendsto_atTop_mono' _ ?_ hlim
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  have h := hC ε hε.1 hε.2
  set R : ℂ := 2 * I / π * chmdPrimeWeight n₀ with hR
  set z : ℂ := (Real.log n₀ : ℂ) + I - ε * I with hz
  have hzre : z.re = Real.log n₀ := by
    rw [hz, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
  have hzn : Real.log n₀ ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hzre, abs_of_pos (by linarith)] at this
    exact this
  have hwn : ‖-((ε : ℂ) * I)‖ = ε := by
    rw [norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hε.1]
  have hLn : -Real.log ε ≤ ‖Complex.log (-((ε : ℂ) * I))‖ := by
    have h1 := Complex.abs_re_le_norm (Complex.log (-((ε : ℂ) * I)))
    rw [Complex.log_re, hwn] at h1
    exact (neg_le_abs _).trans h1
  have hY : Real.log n₀ * ‖R‖ * (-Real.log ε) ≤ ‖z * R * Complex.log (-((ε : ℂ) * I))‖ := by
    rw [norm_mul (z * R), norm_mul z R]
    have hneg : 0 ≤ -Real.log ε := neg_nonneg.mpr (Real.log_nonpos hε.1.le hε.2.le)
    exact mul_le_mul (mul_le_mul_of_nonneg_right hzn (norm_nonneg _)) hLn hneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have htri := norm_sub_le (kgZeroWave z - R / -((ε : ℂ) * I) +
    z * R * Complex.log (-((ε : ℂ) * I))) (kgZeroWave z - R / -((ε : ℂ) * I))
  rw [add_sub_cancel_left] at htri
  linarith

/-- **No meromorphic continuation at a prime point.**  No function meromorphic at
`p = log n + i` (`Λ(n) ≠ 0`) agrees with the causal wave on the part of a neighbourhood of `p` inside
the time strip.  A pole of order other than one is excluded by the leading law
`(z − p) Φ(z) → R ≠ 0` along `z = p − iε`; a simple pole with residue `R` would make
`Φ(z) − R/(z − p)` bounded, contradicting the logarithmic branch. -/
theorem not_meromorphicAt_kgZeroWave {n₀ : ℕ} (hw : chmdPrimeWeight n₀ ≠ 0) {G : ℂ → ℂ}
    (hG : ∀ᶠ z in 𝓝 ((Real.log n₀ : ℂ) + I), |z.im| < 1 → G z = kgZeroWave z) :
    ¬ MeromorphicAt G ((Real.log n₀ : ℂ) + I) := by
  rintro ⟨n, hA⟩
  have hR0 : (2 * I / π * chmdPrimeWeight n₀ : ℂ) ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero two_ne_zero I_ne_zero)
      (ofReal_ne_zero.mpr Real.pi_ne_zero)) (ofReal_ne_zero.mpr hw)
  have hfar := tendsto_norm_kgZeroWave_sub_polar_atTop hw
  have hlead := tendsto_kgZeroWave_boundary hw
  set p : ℂ := (Real.log n₀ : ℂ) + I with hp
  set R : ℂ := 2 * I / π * chmdPrimeWeight n₀ with hR
  set f : ℝ → ℂ := fun ε => p - ε * I with hf
  have hfp : ∀ ε : ℝ, f ε - p = -((ε : ℂ) * I) := fun ε => by simp only [hf]; ring
  have hw0 : ∀ ε : ℝ, 0 < ε → -((ε : ℂ) * I) ≠ 0 := fun ε hε =>
    neg_ne_zero.mpr (mul_ne_zero (ofReal_ne_zero.mpr hε.ne') I_ne_zero)
  have hft : Tendsto f (𝓝[>] 0) (𝓝 p) := by
    have hc : Continuous f := continuous_const.sub (continuous_ofReal.mul continuous_const)
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [hf, Complex.ofReal_zero, zero_mul, sub_zero] using h
  have hwt : Tendsto (fun ε : ℝ => -((ε : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => -((ε : ℂ) * I)) := (continuous_ofReal.mul continuous_const).neg
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa only [Complex.ofReal_zero, zero_mul, neg_zero] using h
  have hpos : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, ε ∈ Ioo 0 1 := Ioo_mem_nhdsGT zero_lt_one
  have hGΦ : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, G (f ε) = kgZeroWave (f ε) := by
    filter_upwards [hft.eventually hG, hpos] with ε h1 h2
    refine h1 ?_
    have him : (f ε).im = 1 - ε := by
      simp only [hf, hp]
      rw [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]; ring
    rw [him, abs_lt]; constructor <;> linarith [h2.1, h2.2]
  have hu : Tendsto (fun ε : ℝ => -((ε : ℂ) * I) * kgZeroWave (f ε)) (𝓝[>] 0) (𝓝 R) := by
    have h := hlead.const_mul (-I)
    have hval : -I * (-2 / (π : ℂ) * chmdPrimeWeight n₀) = R := by rw [hR]; ring
    rw [hval] at h
    refine h.congr fun ε => ?_
    simp only [hf]; ring
  by_cases hz : ∀ᶠ z in 𝓝 p, (z - p) ^ n • G z = 0
  · have h0 : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, (0 : ℂ) = -((ε : ℂ) * I) * kgZeroWave (f ε) := by
      filter_upwards [hft.eventually hz, hGΦ, hpos] with ε h1 h2 h3
      rw [smul_eq_mul, hfp] at h1
      rw [← h2, (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ (hw0 ε h3.1)), mul_zero]
    exact hR0 (tendsto_nhds_unique (tendsto_const_nhds.congr' h0) hu).symm
  obtain ⟨k, g, hg, hgp, hAg⟩ := (hA.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hz
  have hv : Tendsto (fun ε => g (f ε)) (𝓝[>] 0) (𝓝 (g p)) := hg.continuousAt.tendsto.comp hft
  have hkey : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, (-((ε : ℂ) * I)) ^ n * (-((ε : ℂ) * I) * kgZeroWave (f ε)) =
      (-((ε : ℂ) * I)) ^ (k + 1) * g (f ε) := by
    filter_upwards [hft.eventually hAg, hGΦ] with ε h1 h2
    rw [smul_eq_mul, smul_eq_mul, hfp, h2] at h1
    rw [mul_left_comm, h1]; ring
  rcases lt_trichotomy (k + 1) n with hlt | heq | hgt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have h1 : ∀ᶠ (ε : ℝ) in 𝓝[>] 0,
        (-((ε : ℂ) * I)) ^ (d + 1) * (-((ε : ℂ) * I) * kgZeroWave (f ε)) = g (f ε) := by
      filter_upwards [hkey, hpos] with ε h1 h2
      apply mul_left_cancel₀ (pow_ne_zero (k + 1) (hw0 ε h2.1))
      rw [← h1]; ring
    have h2 := (hwt.pow (d + 1)).mul hu
    rw [zero_pow (Nat.succ_ne_zero d), zero_mul] at h2
    exact hgp (tendsto_nhds_unique hv (h2.congr' h1))
  · subst heq
    have hug : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, -((ε : ℂ) * I) * kgZeroWave (f ε) = g (f ε) := by
      filter_upwards [hkey, hpos] with ε h1 h2
      exact mul_left_cancel₀ (pow_ne_zero _ (hw0 ε h2.1)) h1
    have hgR : g p = R := tendsto_nhds_unique hv (hu.congr' hug)
    have hd : Tendsto (fun ε => ‖dslope g p (f ε)‖) (𝓝[>] 0) (𝓝 ‖dslope g p p‖) :=
      ((continuousAt_dslope_same.mpr hg.differentiableAt).tendsto.comp hft).norm
    have hrem : ∀ᶠ (ε : ℝ) in 𝓝[>] 0,
        ‖dslope g p (f ε)‖ = ‖kgZeroWave (f ε) - R / (-((ε : ℂ) * I))‖ := by
      filter_upwards [hug, hpos] with ε h1 h2
      have hne : f ε ≠ p := fun h => hw0 ε h2.1 (by rw [← hfp, h, sub_self])
      have hε : (ε : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2.1.ne'
      rw [dslope_of_ne _ hne, slope_def_field, hfp, ← hgR, ← h1]
      congr 1
      field_simp
      ring
    exact (hd.congr' hrem).not_tendsto (disjoint_nhds_atTop _) hfar
  · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hgt
    have h1 : ∀ᶠ (ε : ℝ) in 𝓝[>] 0,
        (-((ε : ℂ) * I)) ^ (d + 1) * g (f ε) = -((ε : ℂ) * I) * kgZeroWave (f ε) := by
      filter_upwards [hkey, hpos] with ε h1 h2
      apply mul_left_cancel₀ (pow_ne_zero n (hw0 ε h2.1))
      rw [h1, hd]; ring
    have h2 := (hwt.pow (d + 1)).mul hv
    rw [zero_pow (Nat.succ_ne_zero d), zero_mul] at h2
    exact hR0 (tendsto_nhds_unique hu (h2.congr' h1))

/-- The absence of a meromorphic continuation transfers along `z ↦ −z`, by `Φ(−z) = Φ(z)`. -/
theorem not_meromorphicAt_kgZeroWave_neg {q : ℂ}
    (h : ∀ G : ℂ → ℂ, (∀ᶠ z in 𝓝 q, |z.im| < 1 → G z = kgZeroWave z) → ¬ MeromorphicAt G q)
    {G : ℂ → ℂ} (hG : ∀ᶠ z in 𝓝 (-q), |z.im| < 1 → G z = kgZeroWave z) :
    ¬ MeromorphicAt G (-q) := by
  intro hM
  refine h (fun z => G (-z)) ?_ (hM.comp_analyticAt (g := fun z : ℂ => -z) analyticAt_id.neg)
  have ht : Tendsto (fun z : ℂ => -z) (𝓝 q) (𝓝 (-q)) := continuous_neg.tendsto q
  filter_upwards [ht.eventually hG] with z hz hzi
  rw [hz (by rwa [Complex.neg_im, abs_neg]), kgZeroWave_neg]

/-- The absence of a meromorphic continuation transfers along `z ↦ z̄`, by `Φ(z̄) = conj Φ(z)`. -/
theorem not_meromorphicAt_kgZeroWave_conj {q : ℂ}
    (h : ∀ G : ℂ → ℂ, (∀ᶠ z in 𝓝 q, |z.im| < 1 → G z = kgZeroWave z) → ¬ MeromorphicAt G q)
    {G : ℂ → ℂ} (hG : ∀ᶠ z in 𝓝 (conj q), |z.im| < 1 → G z = kgZeroWave z) :
    ¬ MeromorphicAt G (conj q) := by
  rintro ⟨n, hA⟩
  refine h (fun z => conj (G (conj z))) ?_ ⟨n, ?_⟩
  · have ht : Tendsto (fun z : ℂ => conj z) (𝓝 q) (𝓝 (conj q)) :=
      Complex.continuous_conj.tendsto q
    filter_upwards [ht.eventually hG] with z hz hzi
    rw [hz (by rwa [Complex.conj_im, abs_neg]), kgZeroWave_conj, Complex.conj_conj]
  · refine (analyticAt_conj_comp_conj (f := fun z => (z - conj q) ^ n • G z) hA).congr
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [smul_eq_mul, map_mul, map_pow, map_sub, Complex.conj_conj]

/-- **No meromorphic continuation at any of the four prime points** `±log n ± i`. -/
theorem not_meromorphicAt_kgZeroWave_four {n : ℕ} (hw : chmdPrimeWeight n ≠ 0) :
    ∀ q ∈ ({(Real.log n : ℂ) + I, (Real.log n : ℂ) - I, -(Real.log n : ℂ) + I,
        -(Real.log n : ℂ) - I} : Set ℂ),
      ∀ G : ℂ → ℂ, (∀ᶠ z in 𝓝 q, |z.im| < 1 → G z = kgZeroWave z) → ¬ MeromorphicAt G q := by
  have h1 : ∀ G : ℂ → ℂ, (∀ᶠ z in 𝓝 ((Real.log n : ℂ) + I), |z.im| < 1 → G z = kgZeroWave z) →
      ¬ MeromorphicAt G ((Real.log n : ℂ) + I) := fun G hG => not_meromorphicAt_kgZeroWave hw hG
  have hc : (Real.log n : ℂ) - I = conj ((Real.log n : ℂ) + I) := by
    rw [map_add, Complex.conj_ofReal, Complex.conj_I]; ring
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact h1
  · rw [hc]; exact fun G hG => not_meromorphicAt_kgZeroWave_conj h1 hG
  · rw [show -(Real.log n : ℂ) + I = -conj ((Real.log n : ℂ) + I) by rw [← hc]; ring]
    exact fun G hG => not_meromorphicAt_kgZeroWave_neg
      (fun G' hG' => not_meromorphicAt_kgZeroWave_conj h1 hG') hG
  · rw [show -(Real.log n : ℂ) - I = -((Real.log n : ℂ) + I) by ring]
    exact fun G hG => not_meromorphicAt_kgZeroWave_neg h1 hG

/-! ## Cramér's theorem for the causal wave -/

/-- **Cramér's theorem for the Klein–Gordon causal wave.**  The causal wave `Φ = L[Φ₀]`, holomorphic
on the time strip `|Im z| < 1`, continues to a function `F` holomorphic at every point whose
light-cone segment `[0, z]` avoids the singularities of the massless wave; in particular at every
boundary point `x ± i` with `x ≠ 0` other than the prime points.  At each prime point
`s₁ log n + s₂ i` (`Λ(n) ≠ 0`) the wave blows up at the simple-pole rate
`ε Φ → −(2/π) Λ(n)/√n`, has the exact singular expansion
`Φ(z) = R/(z − p) − z R Log(z − p) + O(1)` along `z = p − iε`, `R = (2i/π) Λ(n)/√n`, and admits no
meromorphic continuation there. -/
theorem kgZeroWave_cramer :
    ∃ F : ℂ → ℂ,
      (∀ z : ℂ, |z.im| < 1 → kgZeroWave z = F z) ∧
      (∀ z : ℂ, LightConeRegular z → AnalyticAt ℂ F z) ∧
      (∀ x : ℝ, x ≠ 0 → ∀ s : ℝ, |s| = 1 → AvoidsPrimePoints ((x : ℂ) + s * I) →
        AnalyticAt ℂ F ((x : ℂ) + s * I)) ∧
      ∀ n : ℕ, chmdPrimeWeight n ≠ 0 →
        (Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave ((Real.log n : ℂ) + I - ε * I)) (𝓝[>] 0)
            (𝓝 (-2 / π * chmdPrimeWeight n)) ∧
          Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave ((Real.log n : ℂ) - I + ε * I)) (𝓝[>] 0)
            (𝓝 (-2 / π * chmdPrimeWeight n)) ∧
          Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave (-(Real.log n : ℂ) + I - ε * I)) (𝓝[>] 0)
            (𝓝 (-2 / π * chmdPrimeWeight n)) ∧
          Tendsto (fun ε : ℝ => (ε : ℂ) * kgZeroWave (-(Real.log n : ℂ) - I + ε * I)) (𝓝[>] 0)
            (𝓝 (-2 / π * chmdPrimeWeight n))) ∧
        (∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
          ‖kgZeroWave ((Real.log n : ℂ) + I - ε * I) -
              2 * I / π * chmdPrimeWeight n / (-(ε * I)) +
            ((Real.log n : ℂ) + I - ε * I) * (2 * I / π * chmdPrimeWeight n) *
              Complex.log (-(ε * I))‖ ≤ C) ∧
        ∀ q ∈ ({(Real.log n : ℂ) + I, (Real.log n : ℂ) - I, -(Real.log n : ℂ) + I,
            -(Real.log n : ℂ) - I} : Set ℂ),
          ∀ G : ℂ → ℂ, (∀ᶠ z in 𝓝 q, |z.im| < 1 → G z = kgZeroWave z) → ¬ MeromorphicAt G q :=
  ⟨kgBoundaryWave, fun _ hz => kgZeroWave_eq_kgBoundaryWave hz,
    fun _ hz => analyticAt_kgBoundaryWave hz,
    fun _ hx _ hs hav => analyticAt_kgBoundaryWave_boundary hx hs hav,
    fun _ hw => ⟨tendsto_kgZeroWave_boundary_four hw, exists_kgZeroWave_boundary_expansion hw,
      not_meromorphicAt_kgZeroWave_four hw⟩⟩

end RHTower.CHMDLightCone
