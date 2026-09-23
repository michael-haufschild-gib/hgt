import GaloisForLFunctions.RHTower.Sieve.ZetaLandauCriticalDisc
import GaloisForLFunctions.RHTower.Sieve.ZetaZeroCount
import GaloisForLFunctions.RHTower.Sieve.ZetaPoleLogDeriv
import GaloisForLFunctions.RHTower.Sieve.LandauRealPart

/-!
# The zero count on the critical Landau disc, and the conditional `ζ'/ζ` bound

Keeping the retained zeros in Landau's inequality at the centre bounds their number: every zero of
the disc has `Re ρ ≤ 1`, so each reciprocal contributes at least `(1/8)/(5/2)² = 1/50` to the real
part, while the left side is bounded below by the von Mangoldt series and the pole bound.  Under the
Riemann hypothesis every retained zero sits on `Re = 1/2`, so a point at abscissa `σ` is at distance
at least `σ − 1/2` from all of them, and the whole logarithmic derivative is
`O(log|γ| / (σ − 1/2))` — a bound valid all the way down to the critical line.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- The reciprocal at a zero of the critical disc. -/
theorem crit_re_inv_ge {γ : ℝ} {ρ : ℂ} (hd : ‖ρ - critCentre γ‖ ≤ 5 / 2)
    (hz : riemannZeta ρ = 0) :
    (1 / 50 : ℝ) ≤ ((critCentre γ - ρ)⁻¹).re := by
  have hne : critCentre γ ≠ ρ := by
    intro hcon
    exact zeta_critCentre_ne_zero γ (by rw [hcon]; exact hz)
  have hrere : ρ.re ≤ 1 := by
    by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.mp hcon)) hz
  have hw0 : critCentre γ - ρ ≠ 0 := sub_ne_zero.mpr hne
  have hwre : (critCentre γ - ρ).re = 9 / 8 - ρ.re := by
    rw [Complex.sub_re, critCentre_re]
  have hnorm : ‖critCentre γ - ρ‖ ≤ 5 / 2 := by
    rw [← norm_neg]
    simpa using hd
  have hnormsq : Complex.normSq (critCentre γ - ρ) = ‖critCentre γ - ρ‖ ^ (2 : ℕ) :=
    Complex.normSq_eq_norm_sq _
  have hnormpos : (0 : ℝ) < ‖critCentre γ - ρ‖ := norm_pos_iff.mpr hw0
  have hsq : Complex.normSq (critCentre γ - ρ) ≤ 25 / 4 := by
    rw [hnormsq]; nlinarith [hnormpos, hnorm]
  have hsqpos : (0 : ℝ) < Complex.normSq (critCentre γ - ρ) := by
    rw [hnormsq]; positivity
  rw [Complex.inv_re, hwre, le_div_iff₀ hsqpos]
  nlinarith [hsq, hrere]

/-- **The zero count on the critical disc.** -/
theorem exists_crit_zero_count :
    ∃ E : ℝ, 0 < E ∧ ∀ γ : ℝ, 7 ≤ |γ| → ∀ (Z : Finset ℂ) (m : ℂ → ℕ) (D : ℝ),
      (∀ ρ ∈ Z, ‖ρ - critCentre γ‖ ≤ 5 / 2) →
      (∀ ρ ∈ Z, riemannZeta ρ = 0) →
      ‖logDeriv riemannZeta (critCentre γ)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (critCentre γ - ρ)‖ ≤ D * Real.log |γ| →
      ∑ ρ ∈ Z, (m ρ : ℝ) ≤ 50 * (D * Real.log |γ|) + 50 * (8 + E) := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  refine ⟨max A 0 + 1, by positivity, ?_⟩
  intro γ hγ Z m D hdist hzero hkey
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hreSum : (∑ ρ ∈ Z, (m ρ : ℂ) / (critCentre γ - ρ)).re
      = ∑ ρ ∈ Z, (m ρ : ℝ) * ((critCentre γ - ρ)⁻¹).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun ρ _ => re_natCast_div _ _
  have hsplit : -(logDeriv riemannZeta (critCentre γ)).re
      ≤ D * Real.log |γ| - ∑ ρ ∈ Z, (m ρ : ℝ) * ((critCentre γ - ρ)⁻¹).re := by
    have hd : -(logDeriv riemannZeta (critCentre γ)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (critCentre γ - ρ)).re
        ≤ ‖logDeriv riemannZeta (critCentre γ)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (critCentre γ - ρ)‖ := by
      have h := Complex.abs_re_le_norm
        (logDeriv riemannZeta (critCentre γ)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (critCentre γ - ρ))
      linarith [(abs_le.mp h).1]
    rw [Complex.sub_re, hreSum] at hd
    linarith [hkey]
  have hlow := neg_re_logDeriv_ge (σ := 9 / 8) (γ := γ) (by norm_num)
  have hpole := hA (9 / 8) (by norm_num) (by norm_num)
  rw [neg_div_re_eq_neg_logDeriv_re] at hpole
  have hpole' : -(logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ))).re ≤ 8 + A := by
    have hd : (9 : ℝ) / 8 - 1 = 1 / 8 := by norm_num
    rw [hd] at hpole
    norm_num at hpole ⊢
    linarith
  have hterm : ∀ ρ ∈ Z, (1 / 50 : ℝ) * (m ρ : ℝ)
      ≤ (m ρ : ℝ) * ((critCentre γ - ρ)⁻¹).re := by
    intro ρ hρ
    have h := crit_re_inv_ge (hdist ρ hρ) (hzero ρ hρ)
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    nlinarith [h, hm0]
  have hsum50 : (1 / 50 : ℝ) * ∑ ρ ∈ Z, (m ρ : ℝ)
      ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * ((critCentre γ - ρ)⁻¹).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hcrit : -(logDeriv riemannZeta (critCentre γ)).re
      = -(logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re := by
    rw [critCentre]
  rw [hcrit] at hsplit
  have hAle : A ≤ max A 0 := le_max_left _ _
  linarith [hsum50, hsplit, hlow, hpole', hAle]

/-- Under the Riemann hypothesis every zero with a nonzero ordinate sits on the critical line. -/
theorem re_eq_half_of_rh (hRH : RiemannHypothesis) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (him : ρ.im ≠ 0) : ρ.re = 1 / 2 := by
  refine hRH ρ hz ?_ ?_
  · rintro ⟨n, hn⟩
    apply him
    rw [hn]
    simp
  · intro hcon
    apply him
    rw [hcon]
    simp

/-- **The conditional `ζ'/ζ` bound.**  Under the Riemann hypothesis the logarithmic derivative is
`O(log|γ| / (σ − 1/2))` on the whole segment from the critical line to abscissa `9/8`. -/
theorem exists_logDeriv_zeta_bound_rh (hRH : RiemannHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ γ : ℝ, 7 ≤ |γ| → 1 / 2 < σ → σ ≤ 9 / 8 →
      ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
        ≤ C * Real.log |γ| / (σ - 1 / 2) := by
  obtain ⟨D, hD0, hdata⟩ := exists_crit_landau_data
  obtain ⟨E, hE0, hcount⟩ := exists_crit_zero_count
  refine ⟨D + 50 * D + 50 * (8 + E), by positivity, ?_⟩
  intro σ γ hγ hσ0 hσ1
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hlogγ : (1 : ℝ) ≤ Real.log |γ| := by
    have he : Real.exp 1 < 7 := by
      have := Real.exp_one_lt_d9
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ |γ|)
    rwa [Real.log_exp] at h
  have hγne : γ ≠ 0 := by
    intro h
    rw [h] at hγ
    norm_num at hγ
  set z : ℂ := (σ : ℂ) + (γ : ℂ) * Complex.I with hzdef
  have hzre : z.re = σ := by rw [hzdef]; simp
  have hzim : z.im = γ := by rw [hzdef]; simp
  have hzc : ‖z - critCentre γ‖ ≤ 5 / 8 := by
    have hdiff : z - critCentre γ = (((σ - 9 / 8 : ℝ)) : ℂ) := by
      rw [hzdef, critCentre]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hzne : riemannZeta z ≠ 0 := by
    intro hcon
    have := re_eq_half_of_rh hRH hcon (by rw [hzim]; exact hγne)
    rw [hzre] at this
    linarith
  obtain ⟨Z, m, h1, h2, _h3, _h4, h5⟩ := hdata γ hγ
  have hkeyc : ‖logDeriv riemannZeta (critCentre γ)
      - ∑ ρ ∈ Z, (m ρ : ℂ) / (critCentre γ - ρ)‖ ≤ D * Real.log |γ| := by
    refine h5 (critCentre γ) (by rw [sub_self, norm_zero]; norm_num) ?_
    exact zeta_critCentre_ne_zero γ
  have hcnt := hcount γ hγ Z m D h1 h2 hkeyc
  have hdist : ∀ ρ ∈ Z, σ - 1 / 2 ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hρim : ρ.im ≠ 0 := by
      have hd : |ρ.im - γ| ≤ ‖ρ - critCentre γ‖ := by
        have h := Complex.abs_im_le_norm (ρ - critCentre γ)
        rwa [Complex.sub_im, critCentre_im] at h
      have hb := h1 ρ hρ
      intro hcon
      rw [hcon] at hd
      simp only [zero_sub, abs_neg] at hd
      linarith
    have hre := re_eq_half_of_rh hRH (h2 ρ hρ) hρim
    have h := Complex.abs_re_le_norm (z - ρ)
    rw [Complex.sub_re, hzre, hre] at h
    exact le_trans (le_abs_self _) h
  have hsum : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖
      ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) / (σ - 1 / 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [norm_div, Complex.norm_natCast]
    have hd := hdist ρ hρ
    have hpos : (0 : ℝ) < σ - 1 / 2 := by linarith
    have hzρ : (0 : ℝ) < ‖z - ρ‖ := by linarith
    rw [div_le_div_iff₀ hzρ hpos]
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    nlinarith [hd, hm0]
  have hkeyz := h5 z hzc hzne
  have hsplit : ‖logDeriv riemannZeta z‖
      ≤ ‖logDeriv riemannZeta z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ := by
    simpa using norm_add_le (logDeriv riemannZeta z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
      (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ))
  have hpos : (0 : ℝ) < σ - 1 / 2 := by linarith
  have hδ1 : σ - 1 / 2 ≤ 1 := by linarith
  rw [le_div_iff₀ hpos]
  have hsumb : (∑ ρ ∈ Z, (m ρ : ℝ)) / (σ - 1 / 2)
      ≤ (50 * (D * Real.log |γ|) + 50 * (8 + E)) / (σ - 1 / 2) := by gcongr
  have hchain : ‖logDeriv riemannZeta z‖
      ≤ D * Real.log |γ| + (50 * (D * Real.log |γ|) + 50 * (8 + E)) / (σ - 1 / 2) := by
    linarith [hsplit, hkeyz, hsum, hsumb]
  have hmul : ‖logDeriv riemannZeta z‖ * (σ - 1 / 2)
      ≤ (D * Real.log |γ|
          + (50 * (D * Real.log |γ|) + 50 * (8 + E)) / (σ - 1 / 2)) * (σ - 1 / 2) :=
    mul_le_mul_of_nonneg_right hchain hpos.le
  have hid : (D * Real.log |γ|
        + (50 * (D * Real.log |γ|) + 50 * (8 + E)) / (σ - 1 / 2)) * (σ - 1 / 2)
      = D * Real.log |γ| * (σ - 1 / 2) + (50 * (D * Real.log |γ|) + 50 * (8 + E)) := by
    rw [add_mul, div_mul_cancel₀ _ hpos.ne']
  rw [hid] at hmul
  refine hmul.trans ?_
  nlinarith [hlogγ, hD0, hE0, hδ1, hpos,
    mul_nonneg hD0.le (by linarith : (0:ℝ) ≤ Real.log |γ|)]
