import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.RHTower.ZetaLogDerivZeroDistance
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRemainderFourierTransform

/-!
# The narrow Lorentzian zero mass

For `0 < τ ≤ 1/2` the narrow mass at height `t` is `M_τ(t) = Σ_ρ τ²/(τ² + (t − γ)²)`, which counts the
zeros within `≍ τ` of `t`.

**Theorem** (`abs_mul_re_logDeriv_xi_sub_narrowMass_le`). If every zero with `|γ − t| ≤ D`
(`D ≥ 1`) lies on the critical line, then

`|τ Re ξ'/ξ(½ + τ + it) − M_τ(t)| ≤ 4τ Σ_ρ 1/(D² + (t − γ)²)`.

**Proof.** Pair each partial-fraction summand with its reflection `ρ ↦ 1 − ρ`. This turns
`Re ξ'/ξ(s)` into `½ Σ (Re (s − ρ)⁻¹ + Re (s − ρ̃)⁻¹)`. An on-line zero contributes exactly
`τ/(τ² + (t − γ)²)`, and a zero at distance `> D` contributes at most `4τ/(D² + (t − γ)²)` to the
difference.

**The archimedean part** (`abs_re_logDeriv_xi_sub_zeta_sub_log_le`). For `t ≥ 8` and `0 < τ ≤ ½`:
`|Re (ξ'/ξ − ζ'/ζ)(½ + τ + it) − ½ log(t/2π)| ≤ 1`.
-/

open Complex

namespace RHTower

noncomputable section

/-- The narrow mass term `τ²/(τ² + (t − γ)²)`. -/
def narrowMassTerm (τ t : ℝ) (q : XiZeroCopy) : ℝ :=
  τ ^ 2 / (τ ^ 2 + (t - (q.1 : ℂ).im) ^ 2)

/-- The narrow Lorentzian zero mass `M_τ(t) = Σ_ρ τ²/(τ² + (t − γ)²)`. -/
def narrowMass (τ t : ℝ) : ℝ := ∑' q : XiZeroCopy, narrowMassTerm τ t q

theorem narrowMassTerm_nonneg (τ t : ℝ) (q : XiZeroCopy) : 0 ≤ narrowMassTerm τ t q := by
  unfold narrowMassTerm; positivity

theorem narrowMassTerm_le_lorentzMassTerm {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (t : ℝ)
    (q : XiZeroCopy) : narrowMassTerm τ t q ≤ lorentzMassTerm t q := by
  unfold narrowMassTerm lorentzMassTerm
  set u := t - (q.1 : ℂ).im
  rcases eq_or_lt_of_le (sq_nonneg τ) with h0 | h0
  · rw [← h0]; simp; positivity
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hτ2 : τ ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_right hτ2 (sq_nonneg u)]

theorem summable_narrowMassTerm {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (t : ℝ) :
    Summable (narrowMassTerm τ t) :=
  Summable.of_nonneg_of_le (narrowMassTerm_nonneg τ t)
    (narrowMassTerm_le_lorentzMassTerm hτ0 hτ1 t) (summable_lorentzMassTerm t)

theorem narrowMass_nonneg (τ t : ℝ) : 0 ≤ narrowMass τ t :=
  tsum_nonneg (narrowMassTerm_nonneg τ t)

theorem narrowMass_le_lorentzMass {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (t : ℝ) :
    narrowMass τ t ≤ lorentzMass t :=
  Summable.tsum_le_tsum (narrowMassTerm_le_lorentzMassTerm hτ0 hτ1 t)
    (summable_narrowMassTerm hτ0 hτ1 t) (summable_lorentzMassTerm t)

/-- The point `½ + τ + it`. -/
def narrowPoint (τ t : ℝ) : ℂ := ((1 / 2 + τ : ℝ) : ℂ) + (t : ℂ) * I

theorem narrowPoint_re (τ t : ℝ) : (narrowPoint τ t).re = 1 / 2 + τ := by simp [narrowPoint]

theorem narrowPoint_im (τ t : ℝ) : (narrowPoint τ t).im = t := by simp [narrowPoint]

/-- The difference term `τ Re (s − ρ)⁻¹ − τ²/(τ² + (t − γ)²)` at `s = ½ + τ + it`. -/
def narrowDiff (τ t : ℝ) (q : XiZeroCopy) : ℝ :=
  τ * ((narrowPoint τ t - (q.1 : ℂ))⁻¹).re - narrowMassTerm τ t q

/-- An on-line zero contributes no difference. -/
theorem narrowDiff_eq_zero {τ t : ℝ} {q : XiZeroCopy} (hq : (q.1 : ℂ).re = 1 / 2) :
    narrowDiff τ t q = 0 := by
  unfold narrowDiff narrowMassTerm
  have hre : (narrowPoint τ t - (q.1 : ℂ)).re = τ := by
    rw [Complex.sub_re, narrowPoint_re, hq]; ring
  have him : (narrowPoint τ t - (q.1 : ℂ)).im = t - (q.1 : ℂ).im := by
    rw [Complex.sub_im, narrowPoint_im]
  rw [Complex.inv_re, Complex.normSq_apply, hre, him]
  ring

/-- A zero at ordinate distance `> D ≥ 1` contributes at most `4τ/(D² + (t − γ)²)`. -/
theorem abs_narrowDiff_le {τ t D : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2) (hD : 1 ≤ D)
    {q : XiZeroCopy} (hq : D < |(q.1 : ℂ).im - t|) :
    |narrowDiff τ t q| ≤ 4 * τ * lorentzMassWTerm D t q := by
  set u := t - (q.1 : ℂ).im with hu
  have hu2 : D ^ 2 < u ^ 2 := by
    have : D < |u| := by rw [hu, abs_sub_comm]; exact hq
    nlinarith [abs_nonneg u, sq_abs u]
  have hu0 : 0 < u ^ 2 := by nlinarith
  have hβ0 := xiZeroCopy_re_pos q
  have hβ1 := xiZeroCopy_re_lt_one q
  have hre : (narrowPoint τ t - (q.1 : ℂ)).re = 1 / 2 + τ - (q.1 : ℂ).re := by
    rw [Complex.sub_re, narrowPoint_re]
  have him : (narrowPoint τ t - (q.1 : ℂ)).im = u := by
    rw [Complex.sub_im, narrowPoint_im]
  have hns : u ^ 2 ≤ Complex.normSq (narrowPoint τ t - (q.1 : ℂ)) := by
    rw [Complex.normSq_apply, hre, him]; nlinarith [sq_nonneg (1 / 2 + τ - (q.1 : ℂ).re)]
  have hns0 : 0 < Complex.normSq (narrowPoint τ t - (q.1 : ℂ)) := lt_of_lt_of_le hu0 hns
  have h1 : |((narrowPoint τ t - (q.1 : ℂ))⁻¹).re| ≤ 1 / u ^ 2 := by
    rw [Complex.inv_re, hre, abs_div, abs_of_pos hns0]
    have hnum : |1 / 2 + τ - (q.1 : ℂ).re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc |1 / 2 + τ - (q.1 : ℂ).re| / Complex.normSq (narrowPoint τ t - (q.1 : ℂ))
        ≤ 1 / Complex.normSq (narrowPoint τ t - (q.1 : ℂ)) :=
          div_le_div_of_nonneg_right hnum hns0.le
      _ ≤ 1 / u ^ 2 := one_div_le_one_div_of_le hu0 hns
  have h2 : narrowMassTerm τ t q ≤ τ / u ^ 2 := by
    unfold narrowMassTerm
    rw [← hu, div_le_div_iff₀ (by positivity) hu0]
    have h3 : τ * u ^ 2 ≤ u ^ 2 := by
      have := mul_le_mul_of_nonneg_right (show τ ≤ 1 by linarith) hu0.le
      linarith
    calc τ ^ 2 * u ^ 2 = τ * (τ * u ^ 2) := by ring
      _ ≤ τ * u ^ 2 := mul_le_mul_of_nonneg_left h3 hτ0.le
      _ ≤ τ * (τ ^ 2 + u ^ 2) := by nlinarith
  have h3 : 1 / u ^ 2 ≤ 2 / (D ^ 2 + u ^ 2) := by
    rw [div_le_div_iff₀ hu0 (by positivity)]; nlinarith
  unfold narrowDiff
  calc |τ * ((narrowPoint τ t - (q.1 : ℂ))⁻¹).re - narrowMassTerm τ t q|
      ≤ τ * |((narrowPoint τ t - (q.1 : ℂ))⁻¹).re| + narrowMassTerm τ t q := by
        rw [show τ * ((narrowPoint τ t - (q.1 : ℂ))⁻¹).re - narrowMassTerm τ t q =
          τ * ((narrowPoint τ t - (q.1 : ℂ))⁻¹).re + -narrowMassTerm τ t q by ring]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_pos hτ0, abs_neg, abs_of_nonneg (narrowMassTerm_nonneg τ t q)]
    _ ≤ τ * (1 / u ^ 2) + τ / u ^ 2 := by gcongr
    _ = 2 * τ * (1 / u ^ 2) := by ring
    _ ≤ 2 * τ * (2 / (D ^ 2 + u ^ 2)) := by gcongr
    _ = 4 * τ * lorentzMassWTerm D t q := by unfold lorentzMassWTerm; rw [← hu]; ring

/-- Under local RH the point `½ + τ + it` is not a zero of `ξ`. -/
theorem xi_narrowPoint_ne_zero {τ t D : ℝ} (hτ0 : 0 < τ) (hD : 0 ≤ D)
    (hloc : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - t| ≤ D → (q.1 : ℂ).re = 1 / 2) :
    xi (narrowPoint τ t) ≠ 0 := by
  intro h0
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero h0
  have him : (q.1 : ℂ).im = t := by rw [hq, narrowPoint_im]
  have hre := hloc q (by rw [him, sub_self, abs_zero]; exact hD)
  rw [hq, narrowPoint_re] at hre
  linarith

/-- **Narrow mass versus `τ Re ξ'/ξ` under local RH.** -/
theorem abs_mul_re_logDeriv_xi_sub_narrowMass_le {τ t D : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hD : 1 ≤ D) (hloc : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - t| ≤ D → (q.1 : ℂ).re = 1 / 2) :
    |τ * (logDeriv xi (narrowPoint τ t)).re - narrowMass τ t| ≤
      4 * τ * lorentzMassW D t := by
  set s := narrowPoint τ t with hs
  have hxi : xi s ≠ 0 := xi_narrowPoint_ne_zero hτ0 (by linarith) hloc
  have hτ1' : τ ≤ 1 := by linarith
  have hB := summable_partialFractionTerm hxi
  have hBre : Summable (fun q : XiZeroCopy => (partialFractionSummand s q).re) :=
    (Complex.hasSum_re hB.hasSum).summable
  have hNM := summable_narrowMassTerm hτ0.le hτ1' t
  set f : XiZeroCopy → ℝ := fun q => τ * (partialFractionSummand s q).re - narrowMassTerm τ t q
    with hf
  have hfs : Summable f := (hBre.mul_left τ).sub hNM
  have hfr : Summable (fun q => f (xiZeroCopyReflectEquiv q)) :=
    (xiZeroCopyReflectEquiv.summable_iff (f := f)).mpr hfs
  -- the difference is `Σ f`
  have e1 : (logDeriv xi s).re = ∑' q, (partialFractionSummand s q).re := by
    rw [logDeriv_xi_eq_partialFraction hxi, Complex.re_tsum hB]; rfl
  have hsum : τ * (logDeriv xi s).re - narrowMass τ t = ∑' q, f q := by
    rw [e1, narrowMass, ← tsum_mul_left, ← (hBre.mul_left τ).tsum_sub hNM]
  -- pairing with the reflection
  have hpair : ∀ q : XiZeroCopy, f q + f (xiZeroCopyReflectEquiv q) =
      narrowDiff τ t q + narrowDiff τ t (xiZeroCopyReflectEquiv q) := by
    intro q
    have h := partialFractionSummand_add_reflect s q
    have hre := congrArg Complex.re h
    rw [Complex.add_re, Complex.add_re] at hre
    have hrefl : s - 1 + (q.1 : ℂ) = s - ((xiZeroCopyReflectEquiv q).1 : ℂ) := by
      rw [xiZeroCopyReflectEquiv_coe]; ring
    rw [hrefl] at hre
    simp only [hf, narrowDiff]
    rw [← hs]
    linear_combination τ * hre
  -- the bound on the paired terms
  have hloc' : ∀ q : XiZeroCopy, |narrowDiff τ t q| ≤ 4 * τ * lorentzMassWTerm D t q := by
    intro q
    rcases le_or_gt |(q.1 : ℂ).im - t| D with hn | hn
    · rw [narrowDiff_eq_zero (hloc q hn), abs_zero]
      have := lorentzMassWTerm_nonneg hD t q
      positivity
    · exact abs_narrowDiff_le hτ0 hτ1 hD hn
  have hW := summable_lorentzMassWTerm hD t
  have hWr : Summable (fun q => lorentzMassWTerm D t (xiZeroCopyReflectEquiv q)) :=
    (xiZeroCopyReflectEquiv.summable_iff (f := lorentzMassWTerm D t)).mpr hW
  have hg : Summable (fun q => (f q + f (xiZeroCopyReflectEquiv q)) / 2) :=
    (hfs.add hfr).div_const 2
  have htwo : ∑' q, f q = ∑' q, (f q + f (xiZeroCopyReflectEquiv q)) / 2 := by
    rw [tsum_div_const, hfs.tsum_add hfr,
      xiZeroCopyReflectEquiv.tsum_eq (f := f)]
    ring
  rw [hsum, htwo]
  have hbound : ∀ q, |(f q + f (xiZeroCopyReflectEquiv q)) / 2| ≤
      2 * τ * (lorentzMassWTerm D t q + lorentzMassWTerm D t (xiZeroCopyReflectEquiv q)) := by
    intro q
    rw [hpair, abs_div, abs_two]
    have h1 := hloc' q
    have h2 := hloc' (xiZeroCopyReflectEquiv q)
    have := abs_add_le (narrowDiff τ t q) (narrowDiff τ t (xiZeroCopyReflectEquiv q))
    linarith
  have hbs : Summable (fun q => 2 * τ *
      (lorentzMassWTerm D t q + lorentzMassWTerm D t (xiZeroCopyReflectEquiv q))) :=
    (hW.add hWr).mul_left _
  have hn := norm_tsum_le_tsum_norm hg.norm
  simp only [Real.norm_eq_abs] at hn
  calc |∑' q, (f q + f (xiZeroCopyReflectEquiv q)) / 2|
      ≤ ∑' q, |(f q + f (xiZeroCopyReflectEquiv q)) / 2| := hn
    _ ≤ ∑' q, 2 * τ * (lorentzMassWTerm D t q + lorentzMassWTerm D t (xiZeroCopyReflectEquiv q)) :=
        Summable.tsum_le_tsum hbound hg.abs hbs
    _ = 4 * τ * lorentzMassW D t := by
        rw [tsum_mul_left, hW.tsum_add hWr,
          xiZeroCopyReflectEquiv.tsum_eq (f := lorentzMassWTerm D t), lorentzMassW]
        ring


/-- **The archimedean part of `ξ'/ξ` on `Re s = ½ + τ`.** -/
theorem abs_re_logDeriv_xi_sub_zeta_sub_log_le {τ t : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (ht : 8 ≤ t) (hζ : riemannZeta (narrowPoint τ t) ≠ 0) :
    |(logDeriv xi (narrowPoint τ t)).re - (logDeriv riemannZeta (narrowPoint τ t)).re
      - Real.log (t / (2 * Real.pi)) / 2| ≤ 1 := by
  set s := narrowPoint τ t with hs
  have hsre : s.re = 1 / 2 + τ := narrowPoint_re τ t
  have hsim : s.im = t := narrowPoint_im τ t
  have hre : 0 < s.re := by rw [hsre]; linarith
  have h1 : s ≠ 1 := fun h => by
    have := congrArg Complex.im h; rw [hsim] at this; simp at this; linarith
  have hdec := logDeriv_zeta_eq_logDeriv_xi hre h1 hζ
  have hΓ := logDeriv_Gammaℝ_digamma hre
  have hdiff : logDeriv xi s - logDeriv riemannZeta s =
      s⁻¹ + (s - 1)⁻¹ + (Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2) := by
    rw [hdec, hΓ]; ring
  -- `t ≤ ‖s‖ ≤ t + 1`
  have hns : ‖s‖ ^ 2 = (1 / 2 + τ) ^ 2 + t ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hsre, hsim]; ring
  have hn0 : 0 ≤ ‖s‖ := norm_nonneg _
  have hnl : t ≤ ‖s‖ := by nlinarith [sq_nonneg (1 / 2 + τ)]
  have hnu : ‖s‖ ≤ t + 1 := by nlinarith
  have hdig := abs_re_digamma_half_sub_log_le hre (by linarith)
  rw [hsre] at hdig
  have hdig' : |(Complex.digamma (s / 2)).re - (Real.log ‖s‖ - Real.log 2)| ≤ 21 / 64 := by
    refine hdig.trans ?_
    have hsp : 0 < ‖s‖ ^ (2 : ℕ) := pow_pos (by linarith) 2
    rw [div_le_div_iff₀ hsp (by norm_num)]
    have : (64 : ℝ) ≤ ‖s‖ ^ (2 : ℕ) := by nlinarith
    nlinarith
  -- the elementary terms
  have hinv1 : |(s⁻¹).re| ≤ 1 / 8 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_inv]
    have h8 : ‖s‖⁻¹ ≤ (8 : ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr (by linarith)
    linarith [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  have hinv2 : |((s - 1)⁻¹).re| ≤ 1 / 8 := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_inv]
    have hge : t ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [Complex.sub_im, hsim, Complex.one_im, sub_zero, abs_of_pos (by linarith)] at this
      exact this
    have h8 : ‖s - 1‖⁻¹ ≤ (8 : ℝ)⁻¹ := (inv_le_inv₀ (by linarith) (by norm_num)).mpr (by linarith)
    linarith [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  -- the logarithms
  have hlog1 : Real.log t ≤ Real.log ‖s‖ := Real.log_le_log (by linarith) hnl
  have hlog2 : Real.log ‖s‖ ≤ Real.log t + 1 / 8 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ‖s‖ / t from div_pos (by linarith) (by linarith))
    rw [Real.log_div (by linarith) (by linarith)] at h
    have : ‖s‖ / t - 1 ≤ 1 / 8 := by rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]; linarith
    linarith
  have hre_eq : (logDeriv xi s).re - (logDeriv riemannZeta s).re =
      (s⁻¹).re + ((s - 1)⁻¹).re + ((Complex.digamma (s / 2)).re / 2 - Real.log Real.pi / 2) := by
    rw [← Complex.sub_re, hdiff]
    simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re]
  have hlogt : Real.log (t / (2 * Real.pi)) = Real.log t - Real.log 2 - Real.log Real.pi := by
    rw [Real.log_div (by linarith) (by positivity), Real.log_mul (by norm_num) Real.pi_ne_zero]
    ring
  rw [hre_eq, hlogt]
  have hA := abs_le.mp hdig'
  have hB := abs_le.mp hinv1
  have hC := abs_le.mp hinv2
  rw [abs_le]
  constructor <;> nlinarith [hA.1, hA.2, hB.1, hB.2, hC.1, hC.2]

end

end RHTower
