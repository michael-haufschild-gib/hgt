import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheLatticeSchurDataCoalesce
import GaloisForLFunctions.RHTower.WeilPositivityConductorObstruction
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity

/-!
# The first margin is born quadratically

Fixed-scale lattice data of a bump coalesce as the step shrinks (`tendsto_levinsonErr_one`,
`contMargin_eq_zero`). The continuum invariant is the rate: under RH the first margin is born at
order `h²`, with coefficient the **second zero moment**

`M₂(φ) = Σ_ρ m_ρ γ_ρ² |φ̂(γ_ρ)|²` (`zeroSecondMoment`),

the zero energy of the derivative `φ'` (`zeroSecondMoment_eq_deriv`, from `(φ')^(γ) = −iγφ̂(γ)`).

* **Summability** (`summable_zeroTerm_mul_sq`): a `C²` bump has `|φ̂(γ)| ≤ K/(1 + |γ|)²`, so
  `m_ργ_ρ²|φ̂(γ_ρ)|² ≤ K² m_ρ/(1 + γ_ρ²)`, which is summable over the zeros.
* **The birth law** (`tendsto_levinsonErr_one_div_sq`): `E_1(φ, h)/h² → M₂(φ)` as `h → 0`. Indeed
  `E_1 = (c(0) − c(h))(c(0) + c(h))/c(0)`, the defect `c(0) − c(h) = Σ_ρ w_ρ(1 − cos γ_ρh)` is a cosine
  series with weights `w_ρ = m_ρ|φ̂(γ_ρ)|²`, and `(1 − cos γh)/h² ↑ γ²/2` under the summable majorant
  `w_ργ_ρ²/2` (dominated convergence), while `(c(0) + c(h))/c(0) → 2`.

So the continuum limit of the lattice canonical system is a jet system: the first rescaled margin
`h⁻²E_1` converges to the zero energy of `φ'`, the variance of the zero measure `w` of `φ`.
-/

noncomputable section

open Filter Topology Set Complex

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open ArithmeticCastelnuovoSeveri SpacingScaleHarmonicAnalysis Zeta23 RHTower.WeilConditional

variable {φ : ℝ → ℝ}

/-- The **second zero moment** `M₂(φ) = Σ_ρ m_ρ γ_ρ² |φ̂(γ_ρ)|²`. -/
def zeroSecondMoment (φ : ℝ → ℝ) : ℝ := ∑' ρ, zeroTerm (cx φ) ρ * (ρ : ℂ).im ^ 2

/-- **The second zero moment converges** for a `C²` bump (under RH, where `γ_ρ` is the ordinate). -/
theorem summable_zeroTerm_mul_sq (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) :
    Summable fun ρ : zetaZeroConfig.carrier => zeroTerm (cx φ) ρ * (ρ : ℂ).im ^ 2 := by
  obtain ⟨a, -, ha⟩ := SquareRootThreshold.exists_radius_of_hasCompactSupport
    (cx_hasCompactSupport hφ.2)
  have hsupp : ∀ u, cx φ u ≠ 0 → |u| ≤ a := fun u hu => by
    by_contra h
    exact hu (ha u (not_le.mp h))
  set K := 4 * ((∫ u, ‖cx φ u‖) + ∫ u, ‖deriv (deriv (cx φ)) u‖)
  refine (RHTower.summable_zetaZeroConfig.mul_left (K ^ 2)).of_nonneg_of_le
    (fun ρ => mul_nonneg (zeroTerm_nonneg _ _) (sq_nonneg _)) fun ρ => ?_
  set γ := (ρ : ℂ).im
  have hdec := RHTower.norm_paperFT_le_decay (cx_contDiff hφ.1) hsupp ((γ : ℝ) : ℂ)
  simp only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
    Complex.ofReal_re] at hdec
  rw [gammaOf_carrier_eq hRH ρ, Complex.normSq_ofReal]
  set F := ‖paperFT (cx φ) ((γ : ℝ) : ℂ)‖
  have hF0 : 0 ≤ F := norm_nonneg _
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hA : 0 < 1 + |γ| := by positivity
  have hFK : F * (1 + |γ|) ^ 2 ≤ K := by rwa [le_div_iff₀ (by positivity)] at hdec
  -- `γ²(1 + γ²) ≤ (1 + |γ|)⁴`
  have hγ : γ ^ 2 * (1 + γ * γ) ≤ ((1 + |γ|) ^ 2) ^ 2 := by
    have h1 : γ ^ 2 ≤ (1 + |γ|) ^ 2 := by nlinarith [sq_abs γ, abs_nonneg γ]
    have h2 : 1 + γ * γ ≤ (1 + |γ|) ^ 2 := by nlinarith [sq_abs γ, abs_nonneg γ]
    calc γ ^ 2 * (1 + γ * γ) ≤ (1 + |γ|) ^ 2 * (1 + |γ|) ^ 2 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hkey : F ^ 2 * γ ^ 2 * (1 + γ * γ) ≤ K ^ 2 := by
    calc F ^ 2 * γ ^ 2 * (1 + γ * γ) = F ^ 2 * (γ ^ 2 * (1 + γ * γ)) := by ring
      _ ≤ F ^ 2 * ((1 + |γ|) ^ 2) ^ 2 := mul_le_mul_of_nonneg_left hγ (sq_nonneg F)
      _ = (F * (1 + |γ|) ^ 2) ^ 2 := by ring
      _ ≤ K ^ 2 := pow_le_pow_left₀ (by positivity) hFK 2
  simp only [zeroTerm]
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  calc (zetaZeroConfig.mult ρ : ℝ) * F ^ 2 * γ ^ 2 * (1 + γ * γ) =
        (zetaZeroConfig.mult ρ : ℝ) * (F ^ 2 * γ ^ 2 * (1 + γ * γ)) := by ring
    _ ≤ (zetaZeroConfig.mult ρ : ℝ) * K ^ 2 := mul_le_mul_of_nonneg_left hkey hm
    _ = _ := by ring

/-- **The second zero moment is the zero energy of the derivative**:
`M₂(φ) = Σ_ρ m_ρ|(φ')^(γ_ρ)|²`. -/
theorem zeroSecondMoment_eq_deriv (hφ : φ ∈ realTests) :
    zeroSecondMoment φ = ∑' ρ, zeroTerm (deriv (cx φ)) ρ := by
  refine tsum_congr fun ρ => ?_
  simp only [zeroTerm]
  rw [RHTower.EvenSector.paperFT_deriv_of_compact ((cx_contDiff hφ.1).of_le (by norm_num))
    (cx_hasCompactSupport hφ.2), norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- `(1 − cos γh)/h² → γ²/2` as `h → 0`. -/
theorem tendsto_one_sub_cos_div_sq (γ : ℝ) :
    Tendsto (fun h : ℝ => (1 - Real.cos (γ * h)) / h ^ 2) (𝓝[≠] 0) (𝓝 (γ ^ 2 / 2)) := by
  -- `|(1 − cos γh)/h² − γ²/2| ≤ (5/96)γ⁴h²` once `|γh| ≤ 1`
  have hsmall : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |γ * h| ≤ 1 := by
    have hc : Tendsto (fun h : ℝ => |γ * h|) (𝓝 0) (𝓝 0) := by
      have := ((continuous_const.mul continuous_id).abs).tendsto (0 : ℝ)
      simpa using this
    exact (hc.eventually (ge_mem_nhds one_pos)).filter_mono nhdsWithin_le_nhds
  have hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ‖(1 - Real.cos (γ * h)) / h ^ 2 - γ ^ 2 / 2‖ ≤ 5 / 96 * γ ^ 4 * h ^ 2 := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hne
    have hne' : h ≠ 0 := hne
    have hb := Real.cos_bound hh
    have hh2 : 0 < h ^ 2 := by positivity
    have heq : (1 - Real.cos (γ * h)) / h ^ 2 - γ ^ 2 / 2 =
        -(Real.cos (γ * h) - (1 - (γ * h) ^ 2 / 2)) / h ^ 2 := by
      field_simp; ring
    rw [heq, Real.norm_eq_abs, abs_div, abs_neg, abs_of_pos hh2, div_le_iff₀ hh2]
    calc |Real.cos (γ * h) - (1 - (γ * h) ^ 2 / 2)| ≤ |γ * h| ^ 4 * (5 / 96) := hb
      _ = 5 / 96 * γ ^ 4 * h ^ 2 * h ^ 2 := by
        rw [abs_mul, mul_pow, mul_pow, show |h| ^ 4 = (h ^ 2) ^ 2 by rw [← sq_abs h]; ring,
          show |γ| ^ 4 = (γ ^ 2) ^ 2 by rw [← sq_abs γ]; ring]
        ring
  have hlim : Tendsto (fun h : ℝ => 5 / 96 * γ ^ 4 * h ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have := ((continuous_const.mul (continuous_id.pow 2)).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℝ)))
    simpa using this
  have := squeeze_zero_norm' hbound hlim
  simpa using this.add_const (γ ^ 2 / 2)

/-- **The first margin is born quadratically** (under RH): for every nonzero bump `φ`,
`E_1(φ, h)/h² → M₂(φ)` as `h → 0`. -/
theorem tendsto_levinsonErr_one_div_sq (hRH : RiemannHypothesis) (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) :
    Tendsto (fun h => levinsonErr (weilSeq φ h) 1 / h ^ 2) (𝓝[≠] 0) (𝓝 (zeroSecondMoment φ)) := by
  set q := weilQuad φ
  have hq : 0 < q := by
    have := riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 1 one_pos 0
    rwa [levinsonErr_zero, weilSeq, latticeTranslate_zero] at this
  set w : zetaZeroConfig.carrier → ℝ := zeroTerm (cx φ)
  -- the defect `c(0) − c(h)` as a cosine series
  have hdefect : ∀ h, (q - weilOrbitCorr φ h) / h ^ 2 =
      ∑' ρ, w ρ * ((1 - Real.cos ((ρ : ℂ).im * h)) / h ^ 2) := fun h => by
    have h2 := two_mul_weilSeq_sub hφ h 1
    rw [weilQuad_frobeniusDiff_eq hRH hφ h 1, weilSeq_one] at h2
    have h0 : weilSeq φ h 0 = q := by rw [weilSeq, latticeTranslate_zero]; rfl
    rw [h0] at h2
    have hs : q - weilOrbitCorr φ h = ∑' ρ, w ρ * (1 - Real.cos ((ρ : ℂ).im * h)) := by
      have : ∑' ρ, w ρ * (2 * (1 - Real.cos ((ρ : ℂ).im * (((1 : ℤ) : ℝ) * h)))) =
          2 * ∑' ρ, w ρ * (1 - Real.cos ((ρ : ℂ).im * h)) := by
        rw [← tsum_mul_left]
        refine tsum_congr fun ρ => ?_
        push_cast; ring
      linarith
    rw [hs, ← tsum_div_const]
    refine tsum_congr fun ρ => ?_
    ring
  -- dominated convergence for the defect
  have hsum := summable_zeroTerm_mul_sq hRH hφ
  have hdom : Tendsto (fun h => ∑' ρ, w ρ * ((1 - Real.cos ((ρ : ℂ).im * h)) / h ^ 2)) (𝓝[≠] 0)
      (𝓝 (∑' ρ, w ρ * ((ρ : ℂ).im ^ 2 / 2))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun ρ => w ρ * (ρ : ℂ).im ^ 2 / 2)
      (hsum.div_const 2) (fun ρ => (tendsto_one_sub_cos_div_sq _).const_mul (w ρ)) ?_
    refine Eventually.of_forall fun h ρ => ?_
    have hw : 0 ≤ w ρ := zeroTerm_nonneg _ _
    have hc0 : 0 ≤ 1 - Real.cos ((ρ : ℂ).im * h) := by linarith [Real.cos_le_one ((ρ : ℂ).im * h)]
    have hc1 : 1 - Real.cos ((ρ : ℂ).im * h) ≤ ((ρ : ℂ).im * h) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := (ρ : ℂ).im * h)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (div_nonneg hc0 (sq_nonneg h))),
      mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hw
    rcases eq_or_ne h 0 with rfl | hne
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero]
      positivity
    · rw [div_le_iff₀ (by positivity)]
      calc 1 - Real.cos ((ρ : ℂ).im * h) ≤ ((ρ : ℂ).im * h) ^ 2 / 2 := hc1
        _ = (ρ : ℂ).im ^ 2 / 2 * h ^ 2 := by ring
  have hM : ∑' ρ, w ρ * ((ρ : ℂ).im ^ 2 / 2) = zeroSecondMoment φ / 2 := by
    rw [zeroSecondMoment, ← tsum_div_const]
    refine tsum_congr fun ρ => ?_
    ring
  rw [hM] at hdom
  -- `(c(0) + c(h))/c(0) → 2`
  have hc := (continuous_weilOrbitCorr hφ).tendsto 0
  rw [weilOrbitCorr_zero] at hc
  have hratio : Tendsto (fun h => (q + weilOrbitCorr φ h) / q) (𝓝[≠] 0) (𝓝 2) := by
    have := ((tendsto_const_nhds (x := q)).add hc).div_const q
    rw [show (q + q) / q = 2 by field_simp; ring] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hdef : Tendsto (fun h => (q - weilOrbitCorr φ h) / h ^ 2) (𝓝[≠] 0)
      (𝓝 (zeroSecondMoment φ / 2)) := hdom.congr fun h => (hdefect h).symm
  have hprod := hdef.mul hratio
  rw [show zeroSecondMoment φ / 2 * 2 = zeroSecondMoment φ by ring] at hprod
  refine hprod.congr fun h => ?_
  rw [levinsonErr_one, div_mul_eq_mul_div]
  congr 1
  field_simp
  ring

end GaloisForLFunctions.GrowingWindowsOfSpecZ
