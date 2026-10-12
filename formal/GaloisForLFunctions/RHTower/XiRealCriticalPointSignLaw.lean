import GaloisForLFunctions.RHTower.XiLogDerivRePositiveStrict
import GaloisForLFunctions.RHTower.XiCosineShiftUniformLosslessHeights

/-!
# The real-axis sign law for critical points of Ξ

For `Ξ(t) = ξ(½ + it)`, RH is equivalent to the conjunction of two conditions:
- (A) `ξ' ≠ 0` on `Re s > ½`;
- (B') every real critical point `t` of `Ξ` with `Ξ(t) ≠ 0` has `Ξ(t)Ξ''(t) < 0`.

This module proves (B') unconditionally away from the off-line zeros, with a measure bound.

**Theorem** (`re_deriv_deriv_xi_div_xi_pos_of_cone`). Let `ξ'(½ + it₀) = 0` and `ξ(½ + it₀) ≠ 0`.
If every zero `ρ` satisfies `(Re ρ − ½)² ≤ (Im ρ − t₀)²`, then `Re(ξ''/ξ)(½ + it₀) > 0`, that is,
`Ξ(t₀)Ξ''(t₀) < 0`.

**Corollaries.**
- `exists_cone_of_re_deriv_deriv_xi_div_xi_nonpos`: a sign failure lies strictly inside the cone
  `|Im ρ − t₀| < |Re ρ − ½|` of an off-line zero.
- `volume_signFailureHeight_le`: the heights in `[20, V]` carrying a sign failure have measure at
  most `2·offLineMoment(V + 1)`.
- `eventually_volume_signFailureHeight_le`: with Selberg's weights, this measure is at most
  `67(V + 1)/500`. So (B') holds at every critical point over at least `86.6%` of heights.

**Proof.**
- Put `g(ε) = (ξ'/ξ)(½ + ε + it₀)`. Then `g(0) = 0` and `g'(0) = ξ''/ξ(½ + it₀)`.
- Outside the cones every pair of zeros `ρ, 1 − ρ̄` contributes nonnegatively to `Re g(ε)` for
  `ε > 0`, the strict disk criterion of `re_logDeriv_xi_pos_of_disk_bound`.
- One on-line zero `½ + it₁` (Hardy) contributes `ε/(ε² + (t₀ − t₁)²)`.
- Hence `Re g(ε)/ε ≥ 1/(1 + (t₀ − t₁)²)` for `0 < ε ≤ 1`, and the slope limit gives
  `Re g'(0) > 0`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

noncomputable section

/-- Hardy's theorem gives a divisor copy on the critical line. -/
theorem exists_xiZeroCopy_re_eq_half : ∃ q : XiZeroCopy, ((q.1 : ℂ)).re = 1 / 2 := by
  obtain ⟨t, -, ht⟩ := exists_Xi_zero_gt 0
  have hXiC : XiC (t : ℂ) = 0 := by rw [XiC_ofReal, ht, Complex.ofReal_zero]
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp hXiC
  refine ⟨q, ?_⟩
  have h := congrArg Complex.im hq
  simp [xiSpectralPoint, Complex.mul_im] at h
  linarith

/-- **One on-line zero bounds the criterion from below.** If every zero is strictly inside its disk
relative to `s`, then `Re (ξ'/ξ)(s) ≥ Re (s − ρ₀)⁻¹` for every on-line zero `ρ₀`. -/
theorem re_inv_sub_le_re_logDeriv_xi {s : ℂ} (hs : 1 / 2 < s.re) (hxi : xi s ≠ 0)
    (hzeros : ∀ q : XiZeroCopy, (((q.1 : ℂ)).re - 1 / 2) ^ 2 <
      (s.re - 1 / 2) ^ 2 + (s.im - ((q.1 : ℂ)).im) ^ 2)
    (q₀ : XiZeroCopy) (hq₀ : ((q₀.1 : ℂ)).re = 1 / 2) :
    ((s - (q₀.1 : ℂ))⁻¹).re ≤ (logDeriv xi s).re := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  have hpairkey : ∀ q : XiZeroCopy,
      0 < ((((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹) +
        ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹ +
          (s - (((xiZeroCopyLineConjEquiv q).1 : ℂ)))⁻¹)).re := by
    intro q
    have hq := hzeros q
    have hρ' := xiZero_lineConj_eq q
    have hcenter : (((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) =
        -((starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2)) := by
      rw [hρ', map_sub, hhalf]; ring
    have hconst : ((((xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹).re =
        -((((q.1 : ℂ)) - 1 / 2)⁻¹).re := by
      rw [hcenter, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
    have h1 : s - (q.1 : ℂ) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      rw [hcon] at hq
      simp at hq
    have h2 : s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) ≠ 0 := by
      refine sub_ne_zero.mpr ?_
      intro hcon
      have hre : s.re = 1 - ((q.1 : ℂ)).re := by rw [hcon]; simp
      have him : s.im = ((q.1 : ℂ)).im := by rw [hcon]; simp
      rw [hre, him] at hq
      nlinarith
    have hpos := re_inv_add_re_inv_lineConj_pos (s := s) (ρ := (q.1 : ℂ)) h1 h2 hs hq
    have hrw : s - (((xiZeroCopyLineConjEquiv q).1 : ℂ)) =
        s - (1 - (starRingEnd ℂ) ((q.1 : ℂ))) := by rw [hρ']
    simp only [Complex.add_re]
    rw [hconst, hrw]
    linarith [hpos]
  set f : XiZeroCopy → ℂ := fun q => ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ with hf
  have hsum : Summable f := by
    have h := XiAtlasFinitePart.summable_logDerivTerm hxi
    refine h.congr (fun q => ?_)
    show (XiAtlasFinitePart.xiZero q - 1 / 2)⁻¹ - (XiAtlasFinitePart.xiZero q - s)⁻¹ =
      ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
    rw [XiAtlasFinitePart.xiZero, show ((q.1 : ℂ) - s) = -(s - (q.1 : ℂ)) by ring, inv_neg]
    ring
  have hsumJ : Summable (fun q : XiZeroCopy => f (xiZeroCopyLineConjEquiv q)) :=
    (xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  have hpairs := hsum.add hsumJ
  have hident : (∑' q : XiZeroCopy, (f q + f (xiZeroCopyLineConjEquiv q)).re) =
      2 * (∑' q : XiZeroCopy, f q).re := by
    rw [← Complex.re_tsum hpairs, hsum.tsum_add hsumJ, xiZeroCopyLineConjEquiv.tsum_eq f,
      Complex.add_re]
    ring
  have hsumRe : Summable (fun q : XiZeroCopy => (f q + f (xiZeroCopyLineConjEquiv q)).re) :=
    hpairs.mapL Complex.reCLM
  have hle := hsumRe.le_tsum q₀ (fun q _ => (hpairkey q).le)
  have hJ : ((xiZeroCopyLineConjEquiv q₀).1 : ℂ) = (q₀.1 : ℂ) := by
    rw [xiZero_lineConj_eq]
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]; linarith
    · simp
  have hre0 : ((((q₀.1 : ℂ)) - 1 / 2)⁻¹).re = 0 := by
    rw [Complex.inv_re]
    have : (((q₀.1 : ℂ)) - 1 / 2).re = 0 := by simp [hq₀]
    rw [this, zero_div]
  have hval : (f q₀ + f (xiZeroCopyLineConjEquiv q₀)).re = 2 * ((s - (q₀.1 : ℂ))⁻¹).re := by
    simp only [hf, hJ, Complex.add_re, hre0]
    ring
  rw [logDeriv_xi_eq_partialFraction hxi]
  have e : (∑' q : XiZeroCopy, (((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹)) = ∑' q, f q := rfl
  rw [e]
  linarith [hle, hident, hval]

/-- **The real-axis sign law outside the cones.** Let `t₀` be real with `ξ'(½ + it₀) = 0` and
`ξ(½ + it₀) ≠ 0`. If every zero `ρ` of `ξ` satisfies `(Re ρ − ½)² ≤ (Im ρ − t₀)²`, then
`Re(ξ''/ξ)(½ + it₀) > 0`. On the critical line `ξ` and `ξ''` are real, so for `Ξ(t) = ξ(½ + it)`
this is `Ξ(t₀)Ξ''(t₀) < 0`: the critical point is a strict extremum of `|Ξ|` away from zero. -/
theorem re_deriv_deriv_xi_div_xi_pos_of_cone {t₀ : ℝ}
    (hd : deriv xi (1 / 2 + t₀ * I) = 0) (hxi : xi (1 / 2 + t₀ * I) ≠ 0)
    (hcone : ∀ q : XiZeroCopy, (((q.1 : ℂ)).re - 1 / 2) ^ 2 ≤ (((q.1 : ℂ)).im - t₀) ^ 2) :
    0 < (deriv (deriv xi) (1 / 2 + t₀ * I) / xi (1 / 2 + t₀ * I)).re := by
  set s₀ : ℂ := 1 / 2 + t₀ * I with hs₀
  set c : ℂ := deriv (deriv xi) s₀ / xi s₀ with hc
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_re_eq_half
  set t₁ : ℝ := ((q₀.1 : ℂ)).im with ht₁
  have hq₀eq : (q₀.1 : ℂ) = 1 / 2 + t₁ * I := by
    apply Complex.ext <;> simp [hq₀, ht₁]
  have hdt : t₀ - t₁ ≠ 0 := by
    intro h
    apply hxi
    have : s₀ = (q₀.1 : ℂ) := by
      rw [hq₀eq, hs₀, show t₀ = t₁ by linarith]
    rw [this]
    exact XiAtlasFinitePart.xi_xiZero q₀
  have hxid : Differentiable ℂ xi := xi_differentiable
  have hdd : Differentiable ℂ (deriv xi) := fun z => (hxid.analyticAt z).deriv.differentiableAt
  have hG : HasDerivAt (fun w : ℂ => logDeriv xi (s₀ + w)) c 0 := by
    have h1 : HasDerivAt (fun w : ℂ => deriv xi (s₀ + w)) (deriv (deriv xi) s₀) 0 := by
      have := ((hdd (s₀ + 0)).hasDerivAt).comp_const_add s₀ 0
      rwa [add_zero] at this
    have h2 : HasDerivAt (fun w : ℂ => xi (s₀ + w)) (deriv xi s₀) 0 := by
      have := ((hxid (s₀ + 0)).hasDerivAt).comp_const_add s₀ 0
      rwa [add_zero] at this
    have h3 := h1.div h2 (by simpa using hxi)
    have e : (fun w : ℂ => logDeriv xi (s₀ + w)) = fun w => deriv xi (s₀ + w) / xi (s₀ + w) := by
      funext w; rfl
    rw [e]
    refine h3.congr_deriv ?_
    rw [hc]
    simp only [add_zero, hd, mul_zero, sub_zero]
    field_simp
  have hGr : HasDerivAt (fun ε : ℝ => logDeriv xi (s₀ + ε)) c 0 := by
    have hG' : HasDerivAt (fun w : ℂ => logDeriv xi (s₀ + w)) c ((0 : ℝ) : ℂ) := by
      rw [Complex.ofReal_zero]; exact hG
    exact hG'.comp_ofReal
  have hG0 : logDeriv xi s₀ = 0 := by
    rw [logDeriv_apply, hd, zero_div]
  have hslope := hasDerivAt_iff_tendsto_slope.mp hGr
  have htend : Tendsto (fun ε : ℝ => ε⁻¹ * (logDeriv xi (s₀ + ε)).re) (𝓝[>] 0) (𝓝 c.re) := by
    have h := ((Complex.continuous_re.tendsto c).comp
      (hslope.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)))
    refine h.congr fun ε => ?_
    simp only [Function.comp, slope_def_module, sub_zero, Complex.ofReal_zero, add_zero, hG0,
      Complex.smul_re, smul_eq_mul]
  have hlow : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      1 / (1 + (t₀ - t₁) ^ 2) ≤ ε⁻¹ * (logDeriv xi (s₀ + ε)).re := by
    intro ε hε hε1
    set s : ℂ := s₀ + ε with hs
    have hsre : s.re = 1 / 2 + ε := by simp [hs, hs₀]
    have hsim : s.im = t₀ := by simp [hs, hs₀]
    have hxis : xi s ≠ 0 := by
      intro h0
      obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
      have := hcone q
      rw [hq, hsre, hsim] at this
      nlinarith
    have hdisk : ∀ q : XiZeroCopy, (((q.1 : ℂ)).re - 1 / 2) ^ 2 <
        (s.re - 1 / 2) ^ 2 + (s.im - ((q.1 : ℂ)).im) ^ 2 := by
      intro q
      have := hcone q
      rw [hsre, hsim]
      nlinarith
    have hA := re_inv_sub_le_re_logDeriv_xi (by rw [hsre]; linarith) hxis hdisk q₀ hq₀
    have hz : s - (q₀.1 : ℂ) = (ε : ℂ) + ((t₀ - t₁ : ℝ) : ℂ) * I := by
      rw [hq₀eq, hs, hs₀]; push_cast; ring
    rw [hz, Complex.inv_re, Complex.normSq_add_mul_I] at hA
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hA
    have hpos : 0 < ε ^ 2 + (t₀ - t₁) ^ 2 := by positivity
    have h1 : 1 / (1 + (t₀ - t₁) ^ 2) ≤ 1 / (ε ^ 2 + (t₀ - t₁) ^ 2) := by
      apply one_div_le_one_div_of_le hpos
      nlinarith
    have h2 : ε⁻¹ * (ε / (ε ^ 2 + (t₀ - t₁) ^ 2)) = 1 / (ε ^ 2 + (t₀ - t₁) ^ 2) := by
      field_simp
    calc 1 / (1 + (t₀ - t₁) ^ 2) ≤ 1 / (ε ^ 2 + (t₀ - t₁) ^ 2) := h1
      _ = ε⁻¹ * (ε / (ε ^ 2 + (t₀ - t₁) ^ 2)) := h2.symm
      _ ≤ ε⁻¹ * (logDeriv xi s).re := by gcongr
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      1 / (1 + (t₀ - t₁) ^ 2) ≤ ε⁻¹ * (logDeriv xi (s₀ + (ε : ℂ))).re := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact hlow ε hε.1 hε.2
  have hge := ge_of_tendsto htend hev
  exact lt_of_lt_of_le (by positivity) hge

/-- **Localization of the real-axis sign failures.** A real critical point `t₀` of `Ξ` off its zero
set with `Re(ξ''/ξ)(½ + it₀) ≤ 0` (i.e. `Ξ(t₀)Ξ''(t₀) ≥ 0`) lies strictly inside the cone of some
zero: `|Im ρ − t₀| < |Re ρ − ½|`. In particular `ρ` is off the critical line. -/
theorem exists_cone_of_re_deriv_deriv_xi_div_xi_nonpos {t₀ : ℝ}
    (hd : deriv xi (1 / 2 + t₀ * I) = 0) (hxi : xi (1 / 2 + t₀ * I) ≠ 0)
    (hsign : (deriv (deriv xi) (1 / 2 + t₀ * I) / xi (1 / 2 + t₀ * I)).re ≤ 0) :
    ∃ q : XiZeroCopy, (((q.1 : ℂ)).im - t₀) ^ 2 < (((q.1 : ℂ)).re - 1 / 2) ^ 2 := by
  by_contra h
  push Not at h
  exact absurd (re_deriv_deriv_xi_div_xi_pos_of_cone hd hxi h) (not_lt.mpr hsign)

/-- **Sign failures sit in the off-line shadows, with measure bounded by the off-line moment.**
The heights `t ∈ [20, V]` at which `Ξ` has a critical point with `Ξ(t) ≠ 0` and `Ξ(t)Ξ''(t) ≥ 0`
have measure at most `2·offLineMoment(V + 1)`. -/
theorem volume_signFailureHeight_le (V : ℝ) :
    volume {t : ℝ | t ∈ Icc 20 V ∧ deriv xi (1 / 2 + t * I) = 0 ∧ xi (1 / 2 + t * I) ≠ 0 ∧
        (deriv (deriv xi) (1 / 2 + t * I) / xi (1 / 2 + t * I)).re ≤ 0}
      ≤ ENNReal.ofReal (2 * offLineMoment (V + 1)) := by
  classical
  set F := boxFinsetLe (V + 1) with hF
  have hsub : {t : ℝ | t ∈ Icc 20 V ∧ deriv xi (1 / 2 + t * I) = 0 ∧ xi (1 / 2 + t * I) ≠ 0 ∧
      (deriv (deriv xi) (1 / 2 + t * I) / xi (1 / 2 + t * I)).re ≤ 0} ⊆
      ⋃ w ∈ F, Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2)) := by
    rintro t ⟨ht, hd, hxi, hsign⟩
    obtain ⟨q, hq⟩ := exists_cone_of_re_deriv_deriv_xi_div_xi_nonpos hd hxi hsign
    set ρ : ℂ := (q.1 : ℂ) with hρdef
    have hρ : xi ρ = 0 := XiAtlasFinitePart.xi_xiZero q
    have hlt1 : ρ.re < 1 := by
      by_contra hc; push Not at hc; exact xi_ne_zero_of_one_le_re hc hρ
    have hgt0 : 0 < ρ.re := by
      by_contra hc
      push Not at hc
      apply xi_ne_zero_of_one_le_re (ρ := 1 - ρ) (by simp; linarith)
      rw [xi_one_sub]; exact hρ
    have hcone : |t - ρ.im| < |ρ.re - 1 / 2| := by
      rw [abs_sub_comm]
      exact sq_lt_sq.mp hq
    obtain ⟨w, hw, hwre, hwim⟩ : ∃ w : ℂ, xi w = 0 ∧ w.re = 1 / 2 + |ρ.re - 1 / 2| ∧
        w.im = ρ.im := by
      rcases le_or_gt (1 / 2) ρ.re with hc | hc
      · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
      · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ, map_zero], ?_, by simp⟩
        rw [abs_of_neg (by linarith)]; simp; ring
    have hrhalf : |ρ.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
    have htw : |t - w.im| ≤ w.re - 1 / 2 := by rw [hwim, hwre]; linarith
    have htw' := abs_le.mp htw
    have hpos : 0 < |ρ.re - 1 / 2| := lt_of_le_of_lt (abs_nonneg _) hcone
    have hwmem : w ∈ F := by
      rw [hF, mem_boxFinsetLe]
      refine ⟨by rw [hwre]; linarith, xi_zero_re_lt_one hw, ?_, ?_, hw⟩
      · linarith [ht.1]
      · linarith [ht.2]
    exact Set.mem_iUnion₂.mpr ⟨w, hwmem, by linarith, by linarith⟩
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hterm : ∀ w ∈ F, volume (Icc (w.im - (w.re - 1 / 2)) (w.im + (w.re - 1 / 2))) ≤
      ENNReal.ofReal (2 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2))) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    obtain ⟨hw1, -, -, -, hw0⟩ := hw
    have hm := DeBruijn.one_le_toNat_analyticOrderAt_xi hw0
    have hm' : (1 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := by exact_mod_cast hm
    rw [Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  have hnn : ∀ w ∈ F, 0 ≤ 2 * (((analyticOrderAt xi w).toNat : ℝ) * (w.re - 1 / 2)) := by
    intro w hw
    rw [hF, mem_boxFinsetLe] at hw
    have := hw.1
    have : (0 : ℝ) ≤ ((analyticOrderAt xi w).toNat : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [← ENNReal.ofReal_sum_of_nonneg hnn]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  rfl

/-- **The real-axis sign law holds on at least `86.6%` of heights.** For all large `V`, the heights
`t ∈ [20, V]` carrying a critical point of `Ξ` with `Ξ(t) ≠ 0` and `Ξ(t)Ξ''(t) ≥ 0` have measure at
most `67(V + 1)/500`. -/
theorem eventually_volume_signFailureHeight_le :
    ∀ᶠ V in atTop,
      volume {t : ℝ | t ∈ Icc 20 V ∧ deriv xi (1 / 2 + t * I) = 0 ∧ xi (1 / 2 + t * I) ≠ 0 ∧
          (deriv (deriv xi) (1 / 2 + t * I) / xi (1 / 2 + t * I)).re ≤ 0}
        ≤ ENNReal.ofReal (67 / 500 * (V + 1)) := by
  have hshift : Tendsto (fun V : ℝ => V + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  filter_upwards [hshift.eventually ZetaGateProductAFE.eventually_offLineMoment_le_selberg_upper]
    with V hV
  refine (volume_signFailureHeight_le V).trans (ENNReal.ofReal_le_ofReal ?_)
  linarith

end

end RHTower
