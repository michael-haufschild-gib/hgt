import GaloisForLFunctions.HTGeometry.ShiftedDigammaExpansionVertical

/-!
# Shifted digammas at complex shifts

The re-expansion of `ψ⁽ʲ⁾(s+λ)` in the unshifted coordinate `1/s` never used that `λ` was real:
the change of variable `1/(s+λ) = w/(1+λw)` is analytic at `w=0` for every complex `λ`, and the
splitting `log(s+λ) = log s + log(1+λ/s)` holds in the right half plane for every complex `λ` of
size at most half the height.  The only genuine restriction is that the shifted abscissa must stay
in the right half plane, which is exactly `0 ≤ re λ`.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A height that dominates the shift stays admissible for the unshifted expansion, and loses at
most a factor two. -/
theorem shifted_height_bounds {lam : ℂ} {t T₀ : ℝ} (hT₀ : 2 ≤ T₀)
    (ht : 2 * ‖lam‖ + 2 + 2 * T₀ ≤ t) :
    T₀ ≤ t + lam.im ∧ t / 2 ≤ t + lam.im := by
  have h1 : |lam.im| ≤ ‖lam‖ := Complex.abs_im_le_norm lam
  have h2 : -‖lam‖ ≤ lam.im := (abs_le.mp h1).1
  have h3 : (0 : ℝ) ≤ ‖lam‖ := norm_nonneg _
  constructor <;> linarith

/-- The comparison of a shifted height power with the unshifted one. -/
theorem div_pow_shift_le {C₀ t u : ℝ} (hC₀ : 0 ≤ C₀) (htpos : 0 < t) (hu : t / 2 ≤ u) (N : ℕ) :
    C₀ / u ^ (N + 1) ≤ C₀ * 2 ^ (N + 1) / t ^ (N + 1) := by
  have hupos : (0 : ℝ) < u := by linarith
  have hAge : t ^ (N + 1) / 2 ^ (N + 1) ≤ u ^ (N + 1) := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (by positivity) hu _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc C₀ * t ^ (N + 1) = C₀ * 2 ^ (N + 1) * (t ^ (N + 1) / 2 ^ (N + 1)) := by
        field_simp
    _ ≤ C₀ * 2 ^ (N + 1) * u ^ (N + 1) := mul_le_mul_of_nonneg_left hAge (by positivity)

/-- **The complex-shifted digamma jets expanded in the unshifted coordinate.** -/
theorem exists_iteratedDeriv_digamma_complexShift_expansion (lam : ℂ) (hlam : 0 ≤ lam.re)
    (j N : ℕ) :
    ∃ (Q : Polynomial ℂ) (C T : ℝ), 0 ≤ C ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, 0 < σ → T ≤ t →
        ‖iteratedDeriv (j + 1) Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + lam)
            - Q.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t ^ (N + 1) := by
  obtain ⟨Q₀, C₀, T₀, hQ₀0, hC₀, hT₀, hbound₀⟩ := exists_iteratedDeriv_digamma_expansion j N
  set H : ℂ → ℂ := fun w => Q₀.eval (w / (1 + lam * w)) with hH
  have hlin : AnalyticAt ℂ (fun w : ℂ => 1 + lam * w) 0 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hHanalytic : AnalyticAt ℂ H 0 := by
    have hquot : AnalyticAt ℂ (fun w : ℂ => w / (1 + lam * w)) 0 := by
      refine analyticAt_id.div hlin ?_
      simp
    have hbase : AnalyticAt ℂ (fun z : ℂ => Q₀.eval z) (0 : ℂ) := analyticAt_polyEval Q₀ 0
    have hcomp : AnalyticAt ℂ
        ((fun z : ℂ => Q₀.eval z) ∘ fun w : ℂ => w / (1 + lam * w)) 0 := by
      refine AnalyticAt.comp ?_ hquot
      simpa using hbase
    simpa [hH, Function.comp_def] using hcomp
  obtain ⟨P₁, g, hg, hgfac⟩ := exists_taylor_poly_of_analytic hHanalytic (N + 1)
  have hgfac' : ∀ᶠ w in nhds (0 : ℂ), (fun w : ℂ => H w - P₁.eval w) w = w ^ (N + 1) * g w := by
    filter_upwards [hgfac] with w hw
    rw [hw]
    ring
  obtain ⟨C₁, r, hC₁, hr, hbound₁⟩ := exists_bound_of_factor hg hgfac'
  refine ⟨P₁, C₀ * 2 ^ (N + 1) + C₁,
    max (max 2 T₀) (max (1 / r) (2 * ‖lam‖ + 2 + 2 * T₀)), by positivity,
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro σ t hσ ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htr : 1 / r ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htlam : 2 * ‖lam‖ + 2 + 2 * T₀ ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have htpos : (0 : ℝ) < t := by linarith
  obtain ⟨hT₀le, hhalf⟩ := shifted_height_bounds (lam := lam) hT₀ htlam
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzre : z.re = σ := by rw [hz_def]; simp
  have hzim : z.im = t := by rw [hz_def]; simp
  have hznorm : t ≤ ‖z‖ := by
    calc t = z.im := hzim.symm
      _ ≤ |z.im| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hz2 : (2 : ℝ) ≤ ‖z‖ := le_trans ht2 hznorm
  have hznormpos : (0 : ℝ) < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz2
    simp at hz2
    linarith
  have hlamle : 2 * ‖lam‖ ≤ ‖z‖ := by linarith
  have hzlamre : 0 < (z + lam).re := by
    simp only [Complex.add_re, hzre]
    linarith
  have hzlam0 : z + lam ≠ 0 := by
    intro h0
    rw [h0] at hzlamre
    simp at hzlamre
  have hshiftpt : ((σ + lam.re : ℝ) : ℂ) + ((t + lam.im : ℝ) : ℂ) * Complex.I = z + lam := by
    apply Complex.ext <;> simp [hz_def]
  have hstep₀ := hbound₀ (σ + lam.re) (t + lam.im) (by linarith) hT₀le
  rw [hshiftpt] at hstep₀
  have hden : (1 : ℂ) + lam * (1 / z) ≠ 0 := by
    have hval : (1 : ℂ) + lam * (1 / z) = (z + lam) / z := by
      field_simp
    rw [hval]
    exact div_ne_zero hzlam0 hz0
  have hquotval : 1 / (z + lam) = (1 / z) / (1 + lam * (1 / z)) := by
    field_simp
  have hHval : Q₀.eval (1 / (z + lam)) = H (1 / z) := by
    rw [hquotval, hH]
  have hwnorm : ‖1 / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
  have hwle : ‖(1 : ℂ) / z‖ ≤ r := by
    rw [hwnorm, div_le_iff₀ hznormpos]
    rw [div_le_iff₀ hr] at htr
    nlinarith [hznorm]
  have hstep₁ := hbound₁ _ hwle
  have hHminus : ‖H (1 / z) - P₁.eval (1 / z)‖ ≤ C₁ / t ^ (N + 1) := by
    refine le_trans hstep₁ ?_
    rw [hwnorm, div_pow, one_pow, mul_one_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpow : t ^ (N + 1) ≤ ‖z‖ ^ (N + 1) := pow_le_pow_left₀ (le_of_lt htpos) hznorm _
    nlinarith [pow_pos htpos (N + 1), pow_pos hznormpos (N + 1)]
  have hmain : iteratedDeriv (j + 1) Complex.digamma (z + lam) - P₁.eval (1 / z)
      = (iteratedDeriv (j + 1) Complex.digamma (z + lam) - Q₀.eval (1 / (z + lam)))
        + (H (1 / z) - P₁.eval (1 / z)) := by
    rw [hHval]
    ring
  rw [hmain]
  refine le_trans (norm_add_le _ _) ?_
  have hconv : C₀ / (t + lam.im) ^ (N + 1) ≤ C₀ * 2 ^ (N + 1) / t ^ (N + 1) :=
    div_pow_shift_le hC₀ htpos hhalf N
  calc ‖iteratedDeriv (j + 1) Complex.digamma (z + lam) - Q₀.eval (1 / (z + lam))‖
        + ‖H (1 / z) - P₁.eval (1 / z)‖
      ≤ C₀ * 2 ^ (N + 1) / t ^ (N + 1) + C₁ / t ^ (N + 1) :=
        add_le_add (le_trans hstep₀ hconv) hHminus
    _ = (C₀ * 2 ^ (N + 1) + C₁) / t ^ (N + 1) := by ring

/-- **The complex-shifted digamma expanded in the unshifted coordinate.**  For every complex shift
with nonnegative real part and every `N` there is a polynomial `P` with
`ψ(s+λ) = log s + P(1/s) + O(t^{-(N+1)})` on every vertical line in the right half plane. -/
theorem exists_digamma_complexShift_expansion (lam : ℂ) (hlam : 0 ≤ lam.re) (N : ℕ) :
    ∃ (P : Polynomial ℂ) (C T : ℝ), 0 ≤ C ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, 0 < σ → T ≤ t →
        ‖Complex.digamma (((σ : ℂ) + (t : ℂ) * Complex.I) + lam)
            - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
            - P.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t ^ (N + 1) := by
  obtain ⟨P₀, C₀, T₀, hP₀0, hC₀, hT₀, hbound₀⟩ := exists_digamma_expansion N
  set H : ℂ → ℂ := fun w => Complex.log (1 + lam * w) + P₀.eval (w / (1 + lam * w)) with hH
  have hlin : AnalyticAt ℂ (fun w : ℂ => 1 + lam * w) 0 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hHanalytic : AnalyticAt ℂ H 0 := by
    have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log (1 + lam * w)) 0 :=
      hlin.clog (by simp [Complex.mem_slitPlane_iff])
    have hquot : AnalyticAt ℂ (fun w : ℂ => w / (1 + lam * w)) 0 := by
      refine analyticAt_id.div hlin ?_
      simp
    have hPq : AnalyticAt ℂ (fun w : ℂ => P₀.eval (w / (1 + lam * w))) 0 := by
      have hbase : AnalyticAt ℂ (fun z : ℂ => P₀.eval z) (0 : ℂ) := analyticAt_polyEval P₀ 0
      have hcomp : AnalyticAt ℂ
          ((fun z : ℂ => P₀.eval z) ∘ fun w : ℂ => w / (1 + lam * w)) 0 := by
        refine AnalyticAt.comp ?_ hquot
        simpa using hbase
      simpa [Function.comp_def] using hcomp
    exact hlog.add hPq
  obtain ⟨P₁, g, hg, hgfac⟩ := exists_taylor_poly_of_analytic hHanalytic (N + 1)
  have hgfac' : ∀ᶠ w in nhds (0 : ℂ), (fun w : ℂ => H w - P₁.eval w) w = w ^ (N + 1) * g w := by
    filter_upwards [hgfac] with w hw
    rw [hw]
    ring
  obtain ⟨C₁, r, hC₁, hr, hbound₁⟩ := exists_bound_of_factor hg hgfac'
  refine ⟨P₁, C₀ * 2 ^ (N + 1) + C₁,
    max (max 2 T₀) (max (1 / r) (2 * ‖lam‖ + 2 + 2 * T₀)), by positivity,
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro σ t hσ ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htr : 1 / r ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htlam : 2 * ‖lam‖ + 2 + 2 * T₀ ≤ t :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have htpos : (0 : ℝ) < t := by linarith
  obtain ⟨hT₀le, hhalf⟩ := shifted_height_bounds (lam := lam) hT₀ htlam
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzre : z.re = σ := by rw [hz_def]; simp
  have hzim : z.im = t := by rw [hz_def]; simp
  have hznorm : t ≤ ‖z‖ := by
    calc t = z.im := hzim.symm
      _ ≤ |z.im| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hz2 : (2 : ℝ) ≤ ‖z‖ := le_trans ht2 hznorm
  have hznormpos : (0 : ℝ) < ‖z‖ := by linarith
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz2
    simp at hz2
    linarith
  have hzrepos : 0 < z.re := by rw [hzre]; exact hσ
  have hlamle : 2 * ‖lam‖ ≤ ‖z‖ := by linarith
  have hzlamre : 0 < (z + lam).re := by
    simp only [Complex.add_re, hzre]
    linarith
  have hzlam0 : z + lam ≠ 0 := by
    intro h0
    rw [h0] at hzlamre
    simp at hzlamre
  have hshiftpt : ((σ + lam.re : ℝ) : ℂ) + ((t + lam.im : ℝ) : ℂ) * Complex.I = z + lam := by
    apply Complex.ext <;> simp [hz_def]
  have hstep₀ := hbound₀ (σ + lam.re) (t + lam.im) (by linarith) hT₀le
  rw [hshiftpt] at hstep₀
  have hden : (1 : ℂ) + lam * (1 / z) ≠ 0 := by
    have hval : (1 : ℂ) + lam * (1 / z) = (z + lam) / z := by
      field_simp
    rw [hval]
    exact div_ne_zero hzlam0 hz0
  have hquotval : 1 / (z + lam) = (1 / z) / (1 + lam * (1 / z)) := by
    field_simp
  have hlogsplit : Complex.log (z + lam) = Complex.log z + Complex.log (1 + lam / z) :=
    log_add_eq _ hzrepos hz2 hlamle
  have hHval : Complex.log (z + lam) + P₀.eval (1 / (z + lam)) = Complex.log z + H (1 / z) := by
    rw [hlogsplit, hquotval, hH]
    have hlamdiv : lam / z = lam * (1 / z) := by
      field_simp
    rw [hlamdiv]
    ring
  have hwnorm : ‖1 / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
  have hwle : ‖(1 : ℂ) / z‖ ≤ r := by
    rw [hwnorm, div_le_iff₀ hznormpos]
    rw [div_le_iff₀ hr] at htr
    nlinarith [hznorm]
  have hstep₁ := hbound₁ _ hwle
  have hHminus : ‖H (1 / z) - P₁.eval (1 / z)‖ ≤ C₁ / t ^ (N + 1) := by
    refine le_trans hstep₁ ?_
    rw [hwnorm, div_pow, one_pow, mul_one_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hpow : t ^ (N + 1) ≤ ‖z‖ ^ (N + 1) := pow_le_pow_left₀ (le_of_lt htpos) hznorm _
    nlinarith [pow_pos htpos (N + 1), pow_pos hznormpos (N + 1)]
  have hmain : Complex.digamma (z + lam) - Complex.log z - P₁.eval (1 / z)
      = (Complex.digamma (z + lam) - Complex.log (z + lam) - P₀.eval (1 / (z + lam)))
        + (H (1 / z) - P₁.eval (1 / z)) := by
    linear_combination hHval
  rw [hmain]
  refine le_trans (norm_add_le _ _) ?_
  have hconv : C₀ / (t + lam.im) ^ (N + 1) ≤ C₀ * 2 ^ (N + 1) / t ^ (N + 1) :=
    div_pow_shift_le hC₀ htpos hhalf N
  calc ‖Complex.digamma (z + lam) - Complex.log (z + lam) - P₀.eval (1 / (z + lam))‖
        + ‖H (1 / z) - P₁.eval (1 / z)‖
      ≤ C₀ * 2 ^ (N + 1) / t ^ (N + 1) + C₁ / t ^ (N + 1) :=
        add_le_add (le_trans hstep₀ hconv) hHminus
    _ = (C₀ * 2 ^ (N + 1) + C₁) / t ^ (N + 1) := by ring

end

end GaloisForLFunctions.HTGeometry
