import GaloisForLFunctions.RHTower.XiLogDerivReLocality
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.ZetaLogDerivReflectedLeftEdge
import GaloisForLFunctions.RHTower.SmoothAFEZetaChiShiftDerivative
import GaloisForLFunctions.RHTower.XiShiftPrimeExposure
import GaloisForLFunctions.RHTower.CompletedLogDerivStrip
import GaloisForLFunctions.RHTower.Reflection
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.PNTPlus.ZetaConj
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros
import GaloisForLFunctions.HTGeometry.ShiftedDerivativeCoercivity

/-!
# Local form of Speiser's theorem: zeros of `ζ'` left of the line sit in off-line disks

For a zero `ρ` of `ξ`, the Speiser disk is the closed disk with centre `1/2 + i Im ρ` and radius
`|Re ρ − 1/2|`. It degenerates to a point exactly when `ρ` is on the critical line.

**Theorem** (`exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero`). If `ζ'(s) = 0` with
`0 < Re s < 1/2` and `Im s ≥ 100`, then `s` lies in the Speiser disk of some zero `ρ` of `ξ`:
`(Re s − 1/2)² + (Im s − Im ρ)² ≤ (Re ρ − 1/2)²`. In particular `ρ` is off the line, with
`|Re ρ − 1/2| ≥ 1/2 − Re s` and `|Im ρ − Im s| ≤ |Re ρ − 1/2| < 1/2`.

**Proof.**
- If `ζ(s) = 0`, take `ρ = s`.
- Otherwise put `w = 1 − s̄`, so `Re w > 1/2`. Reflection gives `ζ'/ζ(s) = χ'/χ(s) − ζ'/ζ(1 − s)`,
  and `ζ'/ζ(1 − s)` is the conjugate of `ζ'/ζ(w)`. So `ζ'(s) = 0` forces
  `Re ζ'/ζ(w) = Re χ'/χ(s) ≤ −log(Im s/2π) + 3/50` (`re_logDeriv_zetaChi_le`).
- The archimedean part of `ξ'/ξ(w)` has real part `≤ ½ log(Im s/2π) + 1/25`
  (`re_logDeriv_archFactor_le`). Hence `Re(ξ'/ξ)(w) ≤ −½ log(Im s/2π) + 1/10 < 0`.
- By the disk criterion (`re_logDeriv_xi_nonneg_of_disk_bound`), `w` lies in the disk
  `(Re ρ − 1/2)² ≥ (Re w − 1/2)² + (Im w − Im ρ)²` of some zero `ρ`. This is the claim for `s`.

The same computation run forwards gives the quantitative form: outside every Speiser disk,
`Re ζ'/ζ(s) ≤ −½ log(Im s/2π) + 1/10` (`re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk`).
Hence `σ ↦ |ζ(σ + iτ)|` is strictly decreasing on every horizontal segment of `0 < σ < 1/2`,
`τ ≥ 100`, that avoids the Speiser disks (`strictAntiOn_normSq_riemannZeta_horizontal`). This is an
unconditional pointwise form of the horizontal monotonicity that is equivalent to RH.

With RH every Speiser disk is a point on the line, so the theorem contains Speiser's direction
"RH ⇒ `ζ' ≠ 0` on `0 < Re s < 1/2`" above height 100 (`deriv_riemannZeta_ne_zero_of_re_zeros`).
With the zero-free region `1/(58 log |Im ρ|) ≤ Re ρ ≤ 1 − 1/(58 log |Im ρ|)` it gives a zero-free
region for `ζ'` next to the imaginary axis: `ζ'(s) ≠ 0` for `0 < Re s < 1/(58 log(Im s + 1/2))`,
`Im s ≥ 100` (`deriv_riemannZeta_ne_zero_of_re_lt`).
-/

noncomputable section

open Complex

namespace RHTower

/-- Two-sided real-part digamma bound on the right half-plane: `|Re ψ(z) − log ‖z‖| ≤ 3/‖z‖`. -/
theorem abs_re_digamma_sub_log_norm_le {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) :
    |(Complex.digamma z).re - Real.log ‖z‖| ≤ 3 / ‖z‖ := by
  have h := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hre hz
  have e : (Complex.digamma z).re - Real.log ‖z‖ = (Complex.digamma z - Complex.log z).re := by
    rw [Complex.sub_re, Complex.log_re]
  rw [e]
  exact (Complex.abs_re_le_norm _).trans h

/-- `Re χ'/χ(s) ≤ −log(Im s/2π) + 3/50` on the strip at height `≥ 100`. -/
theorem re_logDeriv_zetaChi_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : 100 ≤ s.im) :
    (logDeriv zetaChi s).re ≤ -Real.log (s.im / (2 * Real.pi)) + 3 / 50 := by
  set t := s.im with htdef
  have ht0 : 0 < t := by linarith
  have hp1 : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := div_two_ne_neg_nat_of_re_pos h0
  have hp2 : ∀ m : ℕ, (1 - s) / 2 ≠ -(m : ℂ) :=
    div_two_ne_neg_nat_of_re_pos (by rw [Complex.sub_re, Complex.one_re]; linarith)
  rw [logDeriv_zetaChi_off_poles hp1 hp2]
  have hre1 : 0 < (s / 2).re := by rw [Complex.div_re]; simp; positivity
  have hre2 : 0 < ((1 - s) / 2).re := by
    rw [Complex.div_re]; simp; nlinarith
  have hn1 : t / 2 ≤ ‖s / 2‖ := by
    have := Complex.abs_im_le_norm (s / 2)
    have e : (s / 2).im = t / 2 := by simp [htdef]
    rw [e, abs_of_pos (by linarith)] at this; exact this
  have hn2 : t / 2 ≤ ‖(1 - s) / 2‖ := by
    have := Complex.abs_im_le_norm ((1 - s) / 2)
    have e : ((1 - s) / 2).im = -(t / 2) := by simp [htdef]; ring
    rw [e, abs_neg, abs_of_pos (by linarith)] at this; exact this
  have hd1 := (abs_le.mp (abs_re_digamma_sub_log_norm_le hre1 (by linarith))).1
  have hd2 := (abs_le.mp (abs_re_digamma_sub_log_norm_le hre2 (by linarith))).1
  have hl1 : Real.log (t / 2) ≤ Real.log ‖s / 2‖ := Real.log_le_log (by positivity) hn1
  have hl2 : Real.log (t / 2) ≤ Real.log ‖(1 - s) / 2‖ := Real.log_le_log (by positivity) hn2
  have hi1 : 3 / ‖s / 2‖ ≤ 3 / 50 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hi2 : 3 / ‖(1 - s) / 2‖ ≤ 3 / 50 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_pos.ne']
  have hre : (-(Complex.digamma (s / 2) / 2) - Complex.digamma ((1 - s) / 2) / 2 +
      (Real.log Real.pi : ℂ)).re = -((Complex.digamma (s / 2)).re / 2) -
        (Complex.digamma ((1 - s) / 2)).re / 2 + Real.log Real.pi := by
    simp [Complex.add_re, Complex.sub_re, Complex.neg_re]
  rw [hre, hlog]
  linarith

/-- `Re archFactor'/archFactor(w) ≤ ½ log(Im w/2π) + 1/25` on the strip at height `≥ 100`. -/
theorem re_logDeriv_archFactor_le {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) (ht : 100 ≤ w.im) :
    (logDeriv archFactor w).re ≤ Real.log (w.im / (2 * Real.pi)) / 2 + 1 / 25 := by
  set t := w.im with htdef
  have ht0 : 0 < t := by linarith
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  rw [logDeriv_archFactor_closed h0 hw0 hw1, GaloisForLFunctions.gammaRealLogConnection]
  have hA : (1 / w).re ≤ 1 / 10000 := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    have hsq : 10000 ≤ w.re * w.re + w.im * w.im := by nlinarith
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; nlinarith
  have hB : (1 / (w - 1)).re ≤ 0 := by
    rw [one_div, Complex.inv_re]
    apply div_nonpos_of_nonpos_of_nonneg
    · rw [Complex.sub_re, Complex.one_re]; linarith
    · exact Complex.normSq_nonneg _
  have hre2 : 0 < (w / 2).re := by rw [Complex.div_re]; simp; positivity
  have hn : t / 2 ≤ ‖w / 2‖ := by
    have := Complex.abs_im_le_norm (w / 2)
    have e : (w / 2).im = t / 2 := by simp [htdef]
    rw [e, abs_of_pos (by linarith)] at this; exact this
  have hnu : ‖w / 2‖ ≤ (t + 1) / 2 := by
    rw [norm_div, Complex.norm_two]
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [abs_of_pos h0, abs_of_pos ht0] at this
    linarith
  have hd := (abs_le.mp (abs_re_digamma_sub_log_norm_le hre2 (by linarith))).2
  have hl : Real.log ‖w / 2‖ ≤ Real.log ((t + 1) / 2) :=
    Real.log_le_log (by linarith) hnu
  have hl2 : Real.log ((t + 1) / 2) ≤ Real.log (t / 2) + 1 / t := by
    have e : (t + 1) / 2 = (t / 2) * (1 + 1 / t) := by field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / t by positivity)
    linarith
  have hi : 3 / ‖w / 2‖ ≤ 3 / 50 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hit : 1 / t ≤ 1 / 100 := by
    rw [div_le_div_iff₀ ht0 (by norm_num)]; linarith
  have hlog : Real.log (t / (2 * Real.pi)) = Real.log (t / 2) - Real.log Real.pi := by
    rw [show t / (2 * Real.pi) = (t / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_pos.ne']
  have hre : (1 / w + 1 / (w - 1) + (-(((Real.log Real.pi : ℝ) : ℂ) / 2) +
      Complex.digamma (w / 2) / 2)).re = (1 / w).re + (1 / (w - 1)).re -
        Real.log Real.pi / 2 + (Complex.digamma (w / 2)).re / 2 := by
    simp [Complex.add_re, Complex.neg_re]
    ring
  rw [hre, hlog]
  linarith

/-- On the open strip away from the zeros of `ζ`, `ξ'/ξ = archFactor'/archFactor + ζ'/ζ`. -/
theorem logDeriv_xi_eq_archFactor_add_of_strip {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hζ : riemannZeta s ≠ 0) :
    xi s ≠ 0 ∧ logDeriv xi s = logDeriv archFactor s + logDeriv riemannZeta s := by
  have hstrip : 0 < s.re ∧ s.re < 1 := ⟨h0, h1⟩
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hxi : xi s = archFactor s * riemannZeta s :=
    xi_eq_archFactor_mul_zeta hs0 hs1 (Gammaℝ_ne_zero_of_re_pos h0)
  refine ⟨by rw [hxi]; exact mul_ne_zero (archFactor_ne_zero_strip hstrip) hζ, ?_⟩
  have hU : {z : ℂ | 0 < z.re ∧ z.re < 1} ∈ nhds s :=
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds hstrip
  have hev : xi =ᶠ[nhds s] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hU] with z hz
    exact xi_eq_archFactor_mul_zeta
      (fun h => by rw [h, Complex.zero_re] at hz; exact lt_irrefl 0 hz.1)
      (fun h => by rw [h, Complex.one_re] at hz; exact lt_irrefl 1 hz.2)
      (Gammaℝ_ne_zero_of_re_pos hz.1)
  have hlog : logDeriv xi s = logDeriv (fun z => archFactor z * riemannZeta z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hlog, logDeriv_completed_split_strip hstrip hζ]

/-- `log(t/2π) > 1/5` for `t ≥ 100`. -/
theorem one_fifth_lt_log_div_two_pi {t : ℝ} (ht : 100 ≤ t) :
    1 / 5 < Real.log (t / (2 * Real.pi)) := by
  have hπ := Real.pi_lt_d2
  have hx : 15 ≤ t / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have := Real.one_sub_inv_le_log_of_pos (show 0 < t / (2 * Real.pi) by linarith)
  have : (t / (2 * Real.pi))⁻¹ ≤ 1 / 15 := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- **Off the Speiser disks, `ζ'/ζ` points left.** If `0 < Re s < 1/2`, `Im s ≥ 100`, and `s` lies
outside the Speiser disk of every zero of `ξ` in the strip, then `ζ(s) ≠ 0` and
`Re ζ'/ζ(s) ≤ −½ log(Im s/2π) + 1/10`. -/
theorem re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1 / 2) (ht : 100 ≤ s.im)
    (hno : ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (ρ.re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2) :
    riemannZeta s ≠ 0 ∧
      (logDeriv riemannZeta s).re ≤ -Real.log (s.im / (2 * Real.pi)) / 2 + 1 / 10 := by
  have hζs : riemannZeta s ≠ 0 := by
    intro hζ
    have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl 0 h0
    have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; linarith
    have hxi : xi s = 0 := by
      rw [xi_eq_archFactor_mul_zeta hs0 hs1 (Gammaℝ_ne_zero_of_re_pos h0), hζ, mul_zero]
    have := hno s hxi h0 (by linarith)
    simp at this
  refine ⟨hζs, ?_⟩
  have him : s.im ≠ 0 := by linarith
  have h1s : riemannZeta (1 - s) ≠ 0 :=
    riemannZeta_ne_zero_of_reflect (s := 1 - s) (by rw [Complex.sub_re, Complex.one_re]; linarith)
      (by simpa using him) (by rwa [sub_sub_cancel])
  have hrefl := logDeriv_riemannZeta_add_reflect_of_strip h0 (by linarith) hζs h1s
  have hchi := logDeriv_zetaChi_off_poles (div_two_ne_neg_nat_of_re_pos h0)
    (div_two_ne_neg_nat_of_re_pos (by rw [Complex.sub_re, Complex.one_re]; linarith))
  have hL : logDeriv riemannZeta s = logDeriv zetaChi s - logDeriv riemannZeta (1 - s) := by
    rw [hchi]; linear_combination hrefl
  -- the mirrored point
  set w : ℂ := 1 - (starRingEnd ℂ) s with hw
  have hwre : w.re = 1 - s.re := by rw [hw]; simp
  have hwim : w.im = s.im := by rw [hw]; simp
  have hwc : (starRingEnd ℂ) (1 - s) = w := by rw [hw]; simp
  have hζw : riemannZeta w ≠ 0 := by
    rw [← hwc, riemannZeta_conj]; exact (map_ne_zero _).mpr h1s
  have hlw : (logDeriv riemannZeta w).re = (logDeriv riemannZeta (1 - s)).re := by
    rw [← hwc, logDeriv_riemannZeta_conj, Complex.conj_re]
  obtain ⟨hxiw, hsplit⟩ := logDeriv_xi_eq_archFactor_add_of_strip (s := w)
    (by rw [hwre]; linarith) (by rw [hwre]; linarith) hζw
  have hpos : 0 ≤ (logDeriv xi w).re := by
    refine re_logDeriv_xi_nonneg_of_disk_bound (s := w) (by rw [hwre]; linarith) hxiw
      (fun q => ?_)
    have hq := xi_divisor_support_re_mem_open_unit q.1
    have := hno (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1) hq.1 hq.2
    rw [hwre, hwim]
    nlinarith
  have hchile := re_logDeriv_zetaChi_le h0 (by linarith) ht
  have harchle := re_logDeriv_archFactor_le (w := w) (by rw [hwre]; linarith)
    (by rw [hwre]; linarith) (by rw [hwim]; exact ht)
  rw [hwim] at harchle
  rw [hsplit, Complex.add_re, hlw] at hpos
  rw [hL, Complex.sub_re]
  linarith

/-- **Local Speiser theorem.** A zero of `ζ'` in `0 < Re s < 1/2` at height `≥ 100` lies in the
Speiser disk `(Re s − 1/2)² + (Im s − Im ρ)² ≤ (Re ρ − 1/2)²` of some zero `ρ` of `ξ`. -/
theorem exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1 / 2) (ht : 100 ≤ s.im) (hd : deriv riemannZeta s = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
  by_contra hno
  push Not at hno
  obtain ⟨-, hle⟩ := re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk h0 h1 ht hno
  have hfifth := one_fifth_lt_log_div_two_pi ht
  rw [logDeriv_apply, hd, zero_div, Complex.zero_re] at hle
  linarith

/-- **Horizontal monotonicity of `|ζ|` off the Speiser disks.** On a horizontal segment
`[a, b] + iτ` with `0 < a`, `b < 1/2`, `τ ≥ 100`, avoiding the Speiser disk of every zero of `ξ`,
`σ ↦ |ζ(σ + iτ)|²` is strictly decreasing. -/
theorem strictAntiOn_normSq_riemannZeta_horizontal {a b τ : ℝ} (ha : 0 < a) (hb : b < 1 / 2)
    (hτ : 100 ≤ τ)
    (hno : ∀ σ ∈ Set.Icc a b, ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (ρ.re - 1 / 2) ^ 2 < (σ - 1 / 2) ^ 2 + (τ - ρ.im) ^ 2) :
    StrictAntiOn (fun σ : ℝ => ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * I)‖ ^ (2 : ℕ)) (Set.Icc a b) := by
  have hne1 : ∀ σ : ℝ, (σ : ℂ) + (τ : ℂ) * I ≠ 1 := fun σ h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hcurve : ∀ σ : ℝ, HasDerivAt (fun u : ℝ => riemannZeta ((u : ℂ) + (τ : ℂ) * I))
      (deriv riemannZeta ((σ : ℂ) + (τ : ℂ) * I)) σ := by
    intro σ
    have hlin : HasDerivAt (fun u : ℝ => (u : ℂ) + (τ : ℂ) * I) 1 σ := by
      simpa using (hasDerivAt_id σ).ofReal_comp.add_const ((τ : ℂ) * I)
    have h := (differentiableAt_riemannZeta (hne1 σ)).hasDerivAt.scomp σ hlin
    rw [one_smul] at h
    exact h
  have hderiv : ∀ σ : ℝ, HasDerivAt
      (fun u : ℝ => ‖riemannZeta ((u : ℂ) + (τ : ℂ) * I)‖ ^ (2 : ℕ))
      (2 * (deriv riemannZeta ((σ : ℂ) + (τ : ℂ) * I) *
        (starRingEnd ℂ) (riemannZeta ((σ : ℂ) + (τ : ℂ) * I))).re) σ :=
    fun σ => GaloisForLFunctions.HTGeometry.hasDerivAt_normSq_comp (hcurve σ)
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun σ _ => (hderiv σ).continuousAt.continuousWithinAt) ?_
  intro σ hσ
  rw [interior_Icc] at hσ
  have hre : ((σ : ℂ) + (τ : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (τ : ℂ) * I).im = τ := by simp
  obtain ⟨hζ, hle⟩ := re_logDeriv_riemannZeta_le_of_not_mem_speiserDisk
    (s := (σ : ℂ) + (τ : ℂ) * I) (by rw [hre]; linarith [hσ.1]) (by rw [hre]; linarith [hσ.2])
    (by rw [him]; exact hτ) (by rw [hre, him]; exact hno σ (Set.Ioo_subset_Icc_self hσ))
  rw [him] at hle
  have hfifth := one_fifth_lt_log_div_two_pi hτ
  set z := riemannZeta ((σ : ℂ) + (τ : ℂ) * I) with hz
  set z' := deriv riemannZeta ((σ : ℂ) + (τ : ℂ) * I) with hz'
  have hid : (z' * (starRingEnd ℂ) z).re = ‖z‖ ^ (2 : ℕ) * (z' / z).re := by
    have hnorm : ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) = (starRingEnd ℂ) z * z := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    have hval : z' * (starRingEnd ℂ) z = ((‖z‖ ^ (2 : ℕ) : ℝ) : ℂ) * (z' / z) := by
      rw [hnorm]; field_simp
    rw [hval, Complex.re_ofReal_mul]
  rw [(hderiv σ).deriv, hid]
  have hlog : (z' / z).re = (logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * I)).re := by
    rw [logDeriv_apply]
  have hpos : 0 < ‖z‖ ^ (2 : ℕ) := by
    have := norm_pos_iff.2 hζ
    positivity
  rw [hlog]
  have hneg : (logDeriv riemannZeta ((σ : ℂ) + (τ : ℂ) * I)).re < 0 := by linarith
  nlinarith

/-- **Speiser's direction, locally.** If every zero of `ξ` lies on the critical line, then `ζ'`
has no zero in `0 < Re s < 1/2` at height `≥ 100`. -/
theorem deriv_riemannZeta_ne_zero_of_re_zeros (hRH : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1 / 2) (ht : 100 ≤ s.im) :
    deriv riemannZeta s ≠ 0 := by
  intro hd
  obtain ⟨ρ, hρ, -, -, hdisk⟩ := exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero h0 h1 ht hd
  rw [hRH ρ hρ, sub_self, zero_pow two_ne_zero] at hdisk
  have : 0 < (s.re - 1 / 2) ^ 2 := by
    have : s.re - 1 / 2 ≠ 0 := by linarith
    positivity
  nlinarith [sq_nonneg (s.im - ρ.im)]

/-- **Horizontal monotonicity under RH.** If every zero of `ξ` has `Re = 1/2`, then
`σ ↦ |ζ(σ + iτ)|²` is strictly decreasing on every `[a, b] ⊂ (0, 1/2)` at height `τ ≥ 100`. -/
theorem strictAntiOn_normSq_riemannZeta_horizontal_of_re_zeros
    (hRH : ∀ ρ : ℂ, xi ρ = 0 → ρ.re = 1 / 2) {a b τ : ℝ} (ha : 0 < a) (hb : b < 1 / 2)
    (hτ : 100 ≤ τ) :
    StrictAntiOn (fun σ : ℝ => ‖riemannZeta ((σ : ℂ) + (τ : ℂ) * I)‖ ^ (2 : ℕ)) (Set.Icc a b) := by
  refine strictAntiOn_normSq_riemannZeta_horizontal ha hb hτ (fun σ hσ ρ hρ _ _ => ?_)
  rw [hRH ρ hρ, sub_self, zero_pow two_ne_zero]
  have : σ - 1 / 2 ≠ 0 := by linarith [hσ.2]
  have := pow_pos (abs_pos.mpr this) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (τ - ρ.im)]

/-- The local Speiser theorem below the real axis, by conjugation. -/
theorem exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero_of_abs {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1 / 2) (ht : 100 ≤ |s.im|) (hd : deriv riemannZeta s = 0) :
    ∃ ρ : ℂ, xi ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧
      (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by
  rcases le_or_gt 0 s.im with hs | hs
  · rw [abs_of_nonneg hs] at ht
    exact exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero h0 h1 ht hd
  · rw [abs_of_neg hs] at ht
    have hdc : deriv riemannZeta ((starRingEnd ℂ) s) = 0 := by
      rw [deriv_riemannZeta_conj, hd, map_zero]
    obtain ⟨ρ, hρ, hρ0, hρ1, hdisk⟩ := exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero
      (s := (starRingEnd ℂ) s) (by simpa using h0) (by simpa using h1) (by simpa using ht) hdc
    refine ⟨(starRingEnd ℂ) ρ, by rw [xi_conj, hρ, map_zero], by simpa using hρ0,
      by simpa using hρ1, ?_⟩
    simp only [Complex.conj_re, Complex.conj_im] at hdisk ⊢
    nlinarith [hdisk]

/-- Near the imaginary axis no Speiser disk is reached: if `0 < Re s < 1/(58 log(Im s + 1/2))` and
`Im s ≥ 100`, then `s` lies strictly outside the Speiser disk of every zero of `ξ` in the strip. The
disk of `ρ` reaches `Re s` only if `|Re ρ − 1/2| ≥ 1/2 − Re s` and `|Im ρ − Im s| < 1/2`, which the
zero-free region `1/(58 log |Im ρ|) ≤ Re ρ ≤ 1 − 1/(58 log |Im ρ|)` excludes. -/
theorem speiserDisk_strict_of_re_lt {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1 / 58 / Real.log (s.im + 1 / 2)) (ht : 100 ≤ s.im) :
    ∀ ρ : ℂ, xi ρ = 0 → 0 < ρ.re → ρ.re < 1 →
      (ρ.re - 1 / 2) ^ 2 < (s.re - 1 / 2) ^ 2 + (s.im - ρ.im) ^ 2 := by
  intro ρ hρ hρ0 hρ1
  by_contra hge
  push Not at hge
  have hL : 1 < Real.log (s.im + 1 / 2) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hsmall : s.re < 1 / 2 := by
    have : 1 / 58 / Real.log (s.im + 1 / 2) < 1 / 58 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hρne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ1; exact lt_irrefl 1 hρ1
  have hζρ : riemannZeta ρ = 0 := (xi_eq_zero_iff hρ0 hρne1).mp hρ
  have hlow := one_div_le_re_of_zeta_zero hρ0 hρ1 hζρ
  have hup := re_le_one_sub_of_zeta_zero hρ0 hρ1 hζρ
  have hγ4 := four_le_abs_im_of_zeta_zero hρ0 hρ1 hζρ
  have hsq : (s.re - 1 / 2) ^ 2 ≤ (ρ.re - 1 / 2) ^ 2 := by nlinarith [sq_nonneg (s.im - ρ.im)]
  have hγ : |ρ.im| ≤ s.im + 1 / 2 := by
    have hq : (s.im - ρ.im) ^ 2 < 1 / 4 := by
      have : (ρ.re - 1 / 2) ^ 2 < 1 / 4 := by nlinarith
      nlinarith [sq_nonneg (s.re - 1 / 2)]
    have : |s.im - ρ.im| < 1 / 2 := by
      rw [← sq_lt_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
    rw [abs_le]; constructor <;> linarith [abs_lt.mp this]
  have hlogγ : Real.log |ρ.im| ≤ Real.log (s.im + 1 / 2) :=
    Real.log_le_log (by linarith) hγ
  have hlogpos : 0 < Real.log |ρ.im| := Real.log_pos (by linarith)
  have hc : 1 / 58 / Real.log (s.im + 1 / 2) ≤ 1 / 58 / Real.log |ρ.im| :=
    div_le_div_of_nonneg_left (by norm_num) hlogpos hlogγ
  have habs : 1 / 2 - s.re ≤ |ρ.re - 1 / 2| := by
    have := sq_le_sq.mp hsq
    rw [abs_of_neg (by linarith : s.re - 1 / 2 < 0)] at this
    linarith
  rcases abs_cases (ρ.re - 1 / 2) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at habs <;> linarith

/-- **A zero-free region for `ζ'` next to the imaginary axis.** For `Im s ≥ 100`,
`ζ'(s) ≠ 0` when `0 < Re s < 1/(58 log(Im s + 1/2))`. -/
theorem deriv_riemannZeta_ne_zero_of_re_lt {s : ℂ} (h0 : 0 < s.re)
    (h1 : s.re < 1 / 58 / Real.log (s.im + 1 / 2)) (ht : 100 ≤ s.im) :
    deriv riemannZeta s ≠ 0 := by
  have hL : 1 < Real.log (s.im + 1 / 2) := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hsmall : s.re < 1 / 2 := by
    have : 1 / 58 / Real.log (s.im + 1 / 2) < 1 / 58 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  intro hd
  obtain ⟨ρ, hρ, hρ0, hρ1, hdisk⟩ :=
    exists_xi_zero_disk_of_deriv_riemannZeta_eq_zero h0 hsmall ht hd
  have := speiserDisk_strict_of_re_lt h0 h1 ht ρ hρ hρ0 hρ1
  linarith

end RHTower
