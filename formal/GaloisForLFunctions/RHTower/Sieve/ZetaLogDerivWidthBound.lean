import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegionBound
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFreeAbs
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaZeroFreeMonotonicity
import GaloisForLFunctions.RHTower.Sieve.RouteTZetaAsymptotics

/-!
# `ζ'/ζ` inside a zero-free region of arbitrary width

The corpus's Landau-disc estimate for `ζ'/ζ` was stated for a zero-free region of exponent one,
`σ > 1 - c/log|γ|`, and returned the classical `O(log²|γ|)`.  The argument does not use the shape
of the width at all: Landau's inequality on the wide disc contributes `O(log|γ|)`, the retained
zeros number `O(log|γ|)`, and each of them sits at distance at least half the width from the point.
So for *any* antitone width `w` the same proof gives

```text
‖ζ'/ζ(σ + iγ)‖  ≤  C · log|γ| / w(|γ|+1)      on   1 - w(|γ|+1)/2 ≤ σ ≤ 9/8 .
```

Evaluating the width at the top of the unit band removes every comparison between `w` at two
nearby heights: antitonicity alone suffices.

Instantiating this at the Route-T zero-free region — the Vinogradov-type region of width
`≍ (log γ)^{-9/10}(log log γ)^{-2}` produced by the Route-T exponential-sum tower — gives

```text
‖ζ'/ζ(σ + iγ)‖  ≪  log|γ| · (log|γ|)^{9/10} · (log log|γ|)² ,
```

which is the shape a contour shift to that abscissa consumes.  Nothing here is specific to the
Möbius function: the same abscissa now carries a bound for the logarithmic derivative itself,
hence for twisted von Mangoldt sums.
-/

namespace RHTower.Sieve

open Complex

/-- **Every zero near the wide centre lies left of the region**, for a zero-free region of
arbitrary antitone width.  The width is evaluated at the top of the unit band, so no comparison
between `w` at two nearby heights is needed beyond antitonicity. -/
theorem wide_zero_re_le_width {w : ℝ → ℝ} {T₀ γ : ℝ} (hT₀ : 4 ≤ T₀)
    (hwanti : ∀ s t : ℝ, T₀ ≤ s → s ≤ t → w t ≤ w s)
    (hregion : ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 → 1 - w |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0)
    (hγ : T₀ + 1 ≤ |γ|) {ρ : ℂ}
    (hd : ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40)
    (hz : riemannZeta ρ = 0) :
    ρ.re ≤ 1 - w (|γ| + 1) := by
  have hγ4 : (4 : ℝ) ≤ |γ| := by linarith
  have hrere : ρ.re ≤ 1 := by
    by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.mp hcon)) hz
  have him : |ρ.im - γ| ≤ 21 / 40 := by
    have h1 : |(ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im|
        ≤ ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ := Complex.abs_im_le_norm _
    have h2 : (ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).im = ρ.im - γ := by
      rw [Complex.sub_im, wide_centre_im]
    rw [h2] at h1
    linarith
  have habs := abs_le.mp him
  have hlow : T₀ ≤ |ρ.im| := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ]
  have hup : |ρ.im| ≤ |γ| + 1 := by
    rcases abs_cases γ with ⟨hg, _⟩ | ⟨hg, _⟩ <;>
      rcases abs_cases ρ.im with ⟨hi, _⟩ | ⟨hi, _⟩ <;> rw [hi] <;>
        linarith [habs.1, habs.2, hγ]
  by_contra hcon
  have hwle : w (|γ| + 1) ≤ w |ρ.im| := hwanti _ _ hlow hup
  have hgt : 1 - w |ρ.im| < ρ.re := by linarith [not_le.mp hcon]
  refine hregion ρ.re ρ.im hlow hrere hgt ?_
  rw [Complex.re_add_im]
  exact hz

/-- **`ζ'/ζ` inside a zero-free region of arbitrary width.**  Landau's inequality on the wide disc
contributes `O(log|γ|)`; the retained zeros number `O(log|γ|)` and each sits at distance at least
half the width, so the whole bound is `O(log|γ| / w)`.  For the exponent-one width `w = c/log|γ|`
this is the classical `O(log²|γ|)`; for a Vinogradov-type width it is correspondingly larger. -/
theorem exists_logDeriv_zeta_bound_of_width {w : ℝ → ℝ} {T₀ : ℝ} (hT₀ : 4 ≤ T₀)
    (hwpos : ∀ t : ℝ, T₀ ≤ t → 0 < w t)
    (hwsmall : ∀ t : ℝ, T₀ ≤ t → w t ≤ 1 / 80)
    (hwanti : ∀ s t : ℝ, T₀ ≤ s → s ≤ t → w t ≤ w s)
    (hregion : ∀ β γ' : ℝ, T₀ ≤ |γ'| → β ≤ 1 → 1 - w |γ'| < β →
      riemannZeta ((β : ℂ) + (γ' : ℂ) * Complex.I) ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ γ : ℝ, T₀ + 1 ≤ |γ| →
        1 - w (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| / w (|γ| + 1) := by
  obtain ⟨E, hE0, hcount⟩ := exists_wide_zero_count
  have hCpos : (0 : ℝ) < 320 / 21 * wideD / 80 + 2 * E := by
    have h1 : (0 : ℝ) < 320 / 21 * wideD / 80 := by nlinarith [wideD_pos]
    linarith
  refine ⟨320 / 21 * wideD / 80 + 2 * E, hCpos, ?_⟩
  intro σ γ hγT hσlow hσ98
  have hγ4 : (4 : ℝ) ≤ |γ| := by linarith
  have hγT₀ : T₀ ≤ |γ| := by linarith
  have hL1 := one_le_log_abs hγ4
  have hL0 : (0 : ℝ) < Real.log |γ| := by linarith
  have hTup : T₀ ≤ |γ| + 1 := by linarith
  have hw0 : 0 < w (|γ| + 1) := hwpos _ hTup
  have hwS : w (|γ| + 1) ≤ 1 / 80 := hwsmall _ hTup
  have hwγ : w (|γ| + 1) ≤ w |γ| := hwanti _ _ hγT₀ (by linarith)
  have hσ159 : (159 : ℝ) / 160 ≤ σ := by linarith
  have hzne : riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
    rcases le_or_gt σ 1 with hle | hgt
    · refine hregion σ γ hγT₀ hle ?_
      linarith
    · refine riemannZeta_ne_zero_of_one_le_re ?_
      simp
      linarith
  obtain ⟨Z, m, hZdist, hZzero, hZmem, hZmult, hZkey⟩ := zeta_landau_wide hγ4
  have hzc : ‖((σ : ℂ) + (γ : ℂ) * Complex.I)
      - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 160 := by
    have hdiff : ((σ : ℂ) + (γ : ℂ) * Complex.I) - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        = (((σ - 9 / 8 : ℝ)) : ℂ) := by push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hkeyz := hZkey ((σ : ℂ) + (γ : ℂ) * Complex.I) hzc hzne
  have hkeyc := hZkey (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
    (by rw [sub_self, norm_zero]; norm_num) (zeta_wide_centre_ne_zero γ)
  have hcnt := hcount γ hγ4 Z m hZdist hZzero hkeyc
  have hdistz : ∀ ρ ∈ Z, w (|γ| + 1) / 2 ≤ ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by
    intro ρ hρ
    have hleft := wide_zero_re_le_width hT₀ hwanti hregion hγT (hZdist ρ hρ) (hZzero ρ hρ)
    have h1 : |(((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ).re|
        ≤ ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := Complex.abs_re_le_norm _
    have h2 : (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ).re = σ - ρ.re := by
      rw [Complex.sub_re]
      simp
    rw [h2] at h1
    have h3 : w (|γ| + 1) / 2 ≤ σ - ρ.re := by linarith
    linarith [le_abs_self (σ - ρ.re)]
  have hsumz : ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
      ≤ (∑ ρ ∈ Z, (m ρ : ℝ)) * (2 / w (|γ| + 1)) := by
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [norm_div, Complex.norm_natCast]
    have hd := hdistz ρ hρ
    have hcpos : (0 : ℝ) < w (|γ| + 1) / 2 := by positivity
    have hdpos : (0 : ℝ) < ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by linarith
    rw [div_le_iff₀ hdpos]
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    have hinv : (1 : ℝ) ≤ 2 / w (|γ| + 1) * ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ‖ := by
      have hfac : (0 : ℝ) < 2 / w (|γ| + 1) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hd hfac.le
      have hone : 2 / w (|γ| + 1) * (w (|γ| + 1) / 2) = 1 := by
        field_simp
      rw [hone] at hmul
      exact hmul
    nlinarith [hm0, hinv]
  have hsplit : ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖ := by
    have h := norm_add_le
      (logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
        - ∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ))
      (∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ))
    simpa using h
  have hprod : (∑ ρ ∈ Z, (m ρ : ℝ)) * (2 / w (|γ| + 1))
      ≤ 2 * E * Real.log |γ| / w (|γ| + 1) := by
    have hfac : (0 : ℝ) ≤ 2 / w (|γ| + 1) := by positivity
    have hstep := mul_le_mul_of_nonneg_right hcnt hfac
    calc (∑ ρ ∈ Z, (m ρ : ℝ)) * (2 / w (|γ| + 1))
        ≤ (E * Real.log |γ|) * (2 / w (|γ| + 1)) := hstep
      _ = 2 * E * Real.log |γ| / w (|γ| + 1) := by field_simp
  have hlin : 320 / 21 * wideD * Real.log |γ|
      ≤ 320 / 21 * wideD / 80 * Real.log |γ| / w (|γ| + 1) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hw0]
    have hD := wideD_pos
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt hD) hL0.le) (sub_nonneg.2 hwS)]
  calc ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
        + ‖∑ ρ ∈ Z, (m ρ : ℂ) / (((σ : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖ := hsplit
    _ ≤ 320 / 21 * wideD * Real.log |γ|
          + (∑ ρ ∈ Z, (m ρ : ℝ)) * (2 / w (|γ| + 1)) := by
        linarith [hkeyz, hsumz]
    _ ≤ 320 / 21 * wideD / 80 * Real.log |γ| / w (|γ| + 1)
          + 2 * E * Real.log |γ| / w (|γ| + 1) := by
        linarith [hlin, hprod]
    _ = (320 / 21 * wideD / 80 + 2 * E) * Real.log |γ| / w (|γ| + 1) := by
        field_simp

noncomputable section

/-- Height past which the Route-T zero-free region is available with all its side conditions. -/
def routeTLogDerivThreshold : ℝ :=
  max 100000 ((2 : ℝ) ^ (routeTBandDepthRootThreshold ^ 10))

theorem routeTLogDerivThreshold_ge : (100000 : ℝ) ≤ routeTLogDerivThreshold :=
  le_max_left _ _

theorem routeTBinaryHeight_ge_of_threshold {t : ℝ} (ht : routeTLogDerivThreshold ≤ t) :
    routeTBandDepthRootThreshold ^ 10 ≤ routeTBinaryHeight t := by
  have htpow : ((2 : ℝ) ^ (routeTBandDepthRootThreshold ^ 10)) ≤ t :=
    le_trans (le_max_right _ _) ht
  have hceil : 2 ^ (routeTBandDepthRootThreshold ^ 10) ≤ ⌈t⌉₊ := by
    have hcast : ((2 ^ (routeTBandDepthRootThreshold ^ 10) : ℕ) : ℝ) ≤ (⌈t⌉₊ : ℝ) := by
      push_cast
      exact htpow.trans (Nat.le_ceil t)
    exact_mod_cast hcast
  calc routeTBandDepthRootThreshold ^ 10
      = Nat.clog 2 (2 ^ (routeTBandDepthRootThreshold ^ 10)) :=
        (Nat.clog_pow 2 _ (by norm_num)).symm
    _ ≤ Nat.clog 2 ⌈t⌉₊ := Nat.clog_mono_right 2 hceil

/-- **`ζ'/ζ` inside the Route-T zero-free region.**  The classical exponent-one estimate gives
`O(log²|γ|)`; running the same Landau argument against the Vinogradov-type Route-T width gives
`O(log|γ| / width)`, which is the shape a contour shift to that abscissa consumes. -/
theorem exists_logDeriv_zeta_bound_routeT :
    ∃ (A C : ℝ), 0 < C ∧
      ∀ σ γ : ℝ, routeTLogDerivThreshold + 1 ≤ |γ| →
        1 - routeTZeroFreeWidth A (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| / routeTZeroFreeWidth A (|γ| + 1) := by
  obtain ⟨A, hA⟩ := exists_routeT_zero_free_region_abs
  have hbase := routeTLogDerivThreshold_ge
  have hT₀4 : (4 : ℝ) ≤ routeTLogDerivThreshold := by linarith
  have hpi : (8 : ℝ) * Real.pi + 1 ≤ routeTLogDerivThreshold := by
    have hp := Real.pi_le_four
    linarith
  obtain ⟨C, hC0, hb⟩ :=
    exists_logDeriv_zeta_bound_of_width (w := fun t => routeTZeroFreeWidth A t)
      (T₀ := routeTLogDerivThreshold) hT₀4
      (fun t _ => routeTZeroFreeWidth_pos A t)
      (fun t _ => by
        have hd := routeTZeroFreeDelta_le_sixteenth A t
        show routeTZeroFreeWidth A t ≤ 1 / 80
        unfold routeTZeroFreeWidth
        linarith)
      (fun s t hs hst => routeTZeroFreeWidth_antitone (le_trans hpi hs) hst)
      (fun β γ' hγ' hβ1 hβgt =>
        hA β γ' (le_trans hbase hγ')
          (routeTBinaryHeight_ge_of_threshold hγ') hβ1 hβgt)
  exact ⟨A, C, hC0, hb⟩

/-- **The Route-T `ζ'/ζ` bound with the width replaced by its explicit polylogarithmic
envelope**: the right-hand side is `O(log|γ| · (log|γ|)^{9/10} · (log log|γ|)²)`. -/
theorem exists_logDeriv_zeta_bound_routeT_polylog :
    ∃ (A C : ℝ), 0 < C ∧
      ∀ σ γ : ℝ, routeTLogDerivThreshold + 1 ≤ |γ| →
        1 - routeTZeroFreeWidth A (|γ| + 1) / 2 ≤ σ → σ ≤ 9 / 8 →
        ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
          ≤ C * Real.log |γ| *
              (routeTLogHeightEnvelope (4 * (|γ| + 1))) ^ ((9 : ℝ) / 10) *
              (1 + Real.log (routeTLogHeightEnvelope (4 * (|γ| + 1)))) ^ 2 := by
  obtain ⟨A, C, hC0, hb⟩ := exists_logDeriv_zeta_bound_routeT
  have hK := routeTZeroFreeDeltaEnvelopeConstant_pos A
  refine ⟨A, 10 * C * routeTZeroFreeDeltaEnvelopeConstant A, by positivity, ?_⟩
  intro σ γ hγ hσlow hσ98
  have hmain := hb σ γ hγ hσlow hσ98
  have hbase := routeTLogDerivThreshold_ge
  have hγbig : (100001 : ℝ) ≤ |γ| := by linarith
  have hlogγ : 0 ≤ Real.log |γ| := Real.log_nonneg (by linarith)
  have hγ1 : (8 : ℝ) * Real.pi + 1 ≤ |γ| + 1 := by
    have hp := Real.pi_le_four
    linarith
  have hZ1 : (1 : ℝ) ≤ routeTLogHeightEnvelope (4 * (|γ| + 1)) :=
    routeTLogHeightEnvelope_one_le (by linarith)
  have hlogZ0 : 0 ≤ Real.log (routeTLogHeightEnvelope (4 * (|γ| + 1))) :=
    Real.log_nonneg hZ1
  have hDpos : 0 < routeTZeroFreeDeltaEnvelopeConstant A *
      (routeTLogHeightEnvelope (4 * (|γ| + 1))) ^ ((9 : ℝ) / 10) *
      (1 + Real.log (routeTLogHeightEnvelope (4 * (|γ| + 1)))) ^ 2 := by
    have hpow : 0 < (routeTLogHeightEnvelope (4 * (|γ| + 1))) ^ ((9 : ℝ) / 10) :=
      Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hdelta := routeTZeroFreeDelta_polylog_lower (A := A) hγ1
  have hdpos : 0 < routeTZeroFreeDelta A (|γ| + 1) := routeTZeroFreeDelta_pos A _
  have hinvD : 1 / routeTZeroFreeDelta A (|γ| + 1)
      ≤ routeTZeroFreeDeltaEnvelopeConstant A *
        (routeTLogHeightEnvelope (4 * (|γ| + 1))) ^ ((9 : ℝ) / 10) *
        (1 + Real.log (routeTLogHeightEnvelope (4 * (|γ| + 1)))) ^ 2 := by
    have hstep := one_div_le_one_div_of_le (by positivity) hdelta
    rwa [one_div_one_div] at hstep
  have hwpos : 0 < routeTZeroFreeWidth A (|γ| + 1) := routeTZeroFreeWidth_pos A _
  have hwdiv : routeTZeroFreeWidth A (|γ| + 1) = routeTZeroFreeDelta A (|γ| + 1) / 10 := rfl
  have hfrac : C * Real.log |γ| / routeTZeroFreeWidth A (|γ| + 1)
      ≤ 10 * C * routeTZeroFreeDeltaEnvelopeConstant A * Real.log |γ| *
        (routeTLogHeightEnvelope (4 * (|γ| + 1))) ^ ((9 : ℝ) / 10) *
        (1 + Real.log (routeTLogHeightEnvelope (4 * (|γ| + 1)))) ^ 2 := by
    rw [hwdiv, div_div_eq_mul_div, div_le_iff₀ hdpos]
    have hCl : 0 ≤ C * Real.log |γ| := by positivity
    have hDdelta := (div_le_iff₀ hdpos).mp hinvD
    nlinarith [mul_le_mul_of_nonneg_left hDdelta hCl, hCl]
  refine hmain.trans (hfrac.trans (le_of_eq ?_))
  ring

end

end RHTower.Sieve
