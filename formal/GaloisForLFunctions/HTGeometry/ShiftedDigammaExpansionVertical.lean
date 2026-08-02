import GaloisForLFunctions.HTGeometry.PolygammaExpansionVertical

/-!
# Shifted digammas expanded in the unshifted coordinate

The expansion of `ψ` at abscissa `σ+λ` is an expansion in powers of `1/(s+λ)`.  Re-expanding it in
powers of `1/s` costs only an analytic change of variable: `log(s+λ) = log s + log(1+λ/s)` and
`1/(s+λ) = w/(1+λw)` with `w = 1/s`, so the correction is an analytic function of `w` vanishing at
the origin, and its Taylor polynomial absorbs it to any order.

This puts every generator `ψ⁽ʲ⁾(s+λ)` of the shifted digamma field into the single coordinate `1/s`,
which is what the formal Stirling field consumes.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The logarithm splits off an arbitrary small shift in the right half plane. -/
theorem log_add_eq (lam : ℂ) {z : ℂ} (hre : 0 < z.re) (hz : 2 ≤ ‖z‖) (hlam : 2 * ‖lam‖ ≤ ‖z‖) :
    Complex.log (z + lam) = Complex.log z + Complex.log (1 + lam / z) := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz
    simp at hz
    linarith
  have hnormpos : (0 : ℝ) < ‖z‖ := by linarith
  have hw : ‖lam / z‖ ≤ 1 / 2 := by
    rw [norm_div, div_le_div_iff₀ hnormpos (by norm_num)]
    linarith
  have hwre : 0 < (1 + lam / z).re := by
    have hle : |(lam / z).re| ≤ ‖lam / z‖ := Complex.abs_re_le_norm _
    have hge : (lam / z).re ≥ -(1 / 2) := by
      have habs := abs_le.mp (le_trans hle hw)
      linarith [habs.1]
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hwne : (1 + lam / z) ≠ 0 := by
    intro h0
    rw [h0] at hwre
    simp at hwre
  have hargz : |Complex.arg z| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hargw : |Complex.arg (1 + lam / z)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwre)
  have hsum : Complex.arg z + Complex.arg (1 + lam / z) ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · have h1 := (abs_lt.mp hargz).1
      have h2 := (abs_lt.mp hargw).1
      linarith
    · have h1 := (abs_lt.mp hargz).2
      have h2 := (abs_lt.mp hargw).2
      linarith
  have hmul : z * (1 + lam / z) = z + lam := by
    field_simp
  rw [← hmul, Complex.log_mul_eq_add_log_iff hz0 hwne |>.mpr hsum]

/-- **The shifted digamma expanded in the unshifted coordinate.**  For every real shift and every
`N` there is a polynomial `P` with `ψ(s+λ) = log s + P(1/s) + O(t^{-(N+1)})` on the vertical line
through any admissible abscissa. -/
theorem exists_digamma_shift_expansion (lam : ℝ) (N : ℕ) :
    ∃ (P : Polynomial ℂ) (C T : ℝ), 0 ≤ C ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, 0 < σ → 0 < σ + lam → T ≤ t →
        ‖Complex.digamma (((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            - Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
            - P.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t ^ (N + 1) := by
  obtain ⟨P₀, C₀, T₀, hP₀0, hC₀, hT₀, hbound₀⟩ := exists_digamma_expansion N
  -- the analytic change of variable
  set H : ℂ → ℂ := fun w => Complex.log (1 + (lam : ℂ) * w) + P₀.eval (w / (1 + (lam : ℂ) * w))
    with hH
  have hlin : AnalyticAt ℂ (fun w : ℂ => 1 + (lam : ℂ) * w) 0 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hHanalytic : AnalyticAt ℂ H 0 := by
    have hlog : AnalyticAt ℂ (fun w : ℂ => Complex.log (1 + (lam : ℂ) * w)) 0 :=
      hlin.clog (by simp [Complex.mem_slitPlane_iff])
    have hquot : AnalyticAt ℂ (fun w : ℂ => w / (1 + (lam : ℂ) * w)) 0 := by
      refine analyticAt_id.div hlin ?_
      simp
    have hPq : AnalyticAt ℂ (fun w : ℂ => P₀.eval (w / (1 + (lam : ℂ) * w))) 0 := by
      have hbase : AnalyticAt ℂ (fun z : ℂ => P₀.eval z) (0 : ℂ) := analyticAt_polyEval P₀ 0
      have hcomp : AnalyticAt ℂ
          ((fun z : ℂ => P₀.eval z) ∘ fun w : ℂ => w / (1 + (lam : ℂ) * w)) 0 := by
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
  refine ⟨P₁, C₀ + C₁, max (max 2 T₀) (max (1 / r) (2 * |lam| + 2)), by positivity,
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro σ t hσ hσlam ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT₀ : T₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htr : 1 / r ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htlam : 2 * |lam| + 2 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have htpos : (0 : ℝ) < t := by linarith
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz_def
  have hzre : z.re = σ := by rw [hz_def]; simp
  have hzim : z.im = t := by rw [hz_def]; simp
  have hznorm : t ≤ ‖z‖ := by
    calc t = z.im := hzim.symm
      _ ≤ |z.im| := le_abs_self _
      _ ≤ ‖z‖ := Complex.abs_im_le_norm _
  have hz2 : (2 : ℝ) ≤ ‖z‖ := le_trans ht2 hznorm
  have hzrepos : 0 < z.re := by rw [hzre]; exact hσ
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hz2
    simp at hz2
    linarith
  have hlamnorm : ‖(lam : ℂ)‖ = |lam| := by simp
  have hlamle : 2 * ‖(lam : ℂ)‖ ≤ ‖z‖ := by
    rw [hlamnorm]
    linarith [hznorm]
  have hshiftpt : ((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I = z + (lam : ℂ) := by
    rw [hz_def]
    push_cast
    ring
  -- the expansion at the shifted abscissa
  have hstep₀ := hbound₀ (σ + lam) t hσlam htT₀
  -- the change of variable
  have hden : (1 : ℂ) + (lam : ℂ) * (1 / z) ≠ 0 := by
    have hval : (1 : ℂ) + (lam : ℂ) * (1 / z) = (z + (lam : ℂ)) / z := by
      field_simp
    rw [hval]
    refine div_ne_zero ?_ hz0
    intro h0
    have hre0 : (z + (lam : ℂ)).re = 0 := by rw [h0]; simp
    simp only [Complex.add_re, Complex.ofReal_re, hzre] at hre0
    linarith
  have hlogsplit : Complex.log (z + (lam : ℂ))
      = Complex.log z + Complex.log (1 + (lam : ℂ) / z) :=
    log_add_eq _ hzrepos hz2 hlamle
  have hquotval : 1 / (z + (lam : ℂ)) = (1 / z) / (1 + (lam : ℂ) * (1 / z)) := by
    field_simp
  have hHval : Complex.log (z + (lam : ℂ)) + P₀.eval (1 / (z + (lam : ℂ)))
      = Complex.log z + H (1 / z) := by
    rw [hlogsplit, hquotval, hH]
    have hlamdiv : (lam : ℂ) / z = (lam : ℂ) * (1 / z) := by
      field_simp
    rw [hlamdiv]
    ring
  -- the Taylor bound
  have hwnorm : ‖1 / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
  have hznormpos : (0 : ℝ) < ‖z‖ := by linarith
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
  -- assemble
  have hmain : Complex.digamma (((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      - Complex.log z - P₁.eval (1 / z)
      = (Complex.digamma (z + (lam : ℂ)) - Complex.log (z + (lam : ℂ))
          - P₀.eval (1 / (z + (lam : ℂ))))
        + (H (1 / z) - P₁.eval (1 / z)) := by
    rw [hshiftpt]
    linear_combination hHval
  rw [hmain]
  refine le_trans (norm_add_le _ _) ?_
  have hstep₀' : ‖Complex.digamma (z + (lam : ℂ)) - Complex.log (z + (lam : ℂ))
      - P₀.eval (1 / (z + (lam : ℂ)))‖ ≤ C₀ / t ^ (N + 1) := by
    rw [← hshiftpt]
    exact hstep₀
  calc ‖Complex.digamma (z + (lam : ℂ)) - Complex.log (z + (lam : ℂ))
        - P₀.eval (1 / (z + (lam : ℂ)))‖ + ‖H (1 / z) - P₁.eval (1 / z)‖
      ≤ C₀ / t ^ (N + 1) + C₁ / t ^ (N + 1) := add_le_add hstep₀' hHminus
    _ = (C₀ + C₁) / t ^ (N + 1) := by ring


/-- **The shifted digamma jets expanded in the unshifted coordinate.**  For every real shift, every
jet order and every `N` there is a polynomial `Q` with
`ψ⁽ʲ⁺¹⁾(s+λ) = Q(1/s) + O(t^{-(N+1)})`. -/
theorem exists_iteratedDeriv_digamma_shift_expansion (lam : ℝ) (j N : ℕ) :
    ∃ (Q : Polynomial ℂ) (C T : ℝ), 0 ≤ C ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, 0 < σ → 0 < σ + lam → T ≤ t →
        ‖iteratedDeriv (j + 1) Complex.digamma (((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I)
            - Q.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t ^ (N + 1) := by
  obtain ⟨Q₀, C₀, T₀, hQ₀0, hC₀, hT₀, hbound₀⟩ := exists_iteratedDeriv_digamma_expansion j N
  set H : ℂ → ℂ := fun w => Q₀.eval (w / (1 + (lam : ℂ) * w)) with hH
  have hlin : AnalyticAt ℂ (fun w : ℂ => 1 + (lam : ℂ) * w) 0 :=
    analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hHanalytic : AnalyticAt ℂ H 0 := by
    have hquot : AnalyticAt ℂ (fun w : ℂ => w / (1 + (lam : ℂ) * w)) 0 := by
      refine analyticAt_id.div hlin ?_
      simp
    have hbase : AnalyticAt ℂ (fun z : ℂ => Q₀.eval z) (0 : ℂ) := analyticAt_polyEval Q₀ 0
    have hcomp : AnalyticAt ℂ
        ((fun z : ℂ => Q₀.eval z) ∘ fun w : ℂ => w / (1 + (lam : ℂ) * w)) 0 := by
      refine AnalyticAt.comp ?_ hquot
      simpa using hbase
    simpa [hH, Function.comp_def] using hcomp
  obtain ⟨P₁, g, hg, hgfac⟩ := exists_taylor_poly_of_analytic hHanalytic (N + 1)
  have hgfac' : ∀ᶠ w in nhds (0 : ℂ), (fun w : ℂ => H w - P₁.eval w) w = w ^ (N + 1) * g w := by
    filter_upwards [hgfac] with w hw
    rw [hw]
    ring
  obtain ⟨C₁, r, hC₁, hr, hbound₁⟩ := exists_bound_of_factor hg hgfac'
  refine ⟨P₁, C₀ + C₁, max (max 2 T₀) (max (1 / r) (2 * |lam| + 2)), by positivity,
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro σ t hσ hσlam ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htT₀ : T₀ ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have htr : 1 / r ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htlam : 2 * |lam| + 2 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have htpos : (0 : ℝ) < t := by linarith
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
  have hshiftpt : ((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I = z + (lam : ℂ) := by
    rw [hz_def]
    push_cast
    ring
  have hstep₀ := hbound₀ (σ + lam) t hσlam htT₀
  have hquotval : 1 / (z + (lam : ℂ)) = (1 / z) / (1 + (lam : ℂ) * (1 / z)) := by
    field_simp
  have hHval : Q₀.eval (1 / (z + (lam : ℂ))) = H (1 / z) := by
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
  have hmain : iteratedDeriv (j + 1) Complex.digamma (((σ + lam : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      - P₁.eval (1 / z)
      = (iteratedDeriv (j + 1) Complex.digamma (z + (lam : ℂ))
          - Q₀.eval (1 / (z + (lam : ℂ))))
        + (H (1 / z) - P₁.eval (1 / z)) := by
    rw [hshiftpt]
    linear_combination hHval
  rw [hmain]
  refine le_trans (norm_add_le _ _) ?_
  have hstep₀' : ‖iteratedDeriv (j + 1) Complex.digamma (z + (lam : ℂ))
      - Q₀.eval (1 / (z + (lam : ℂ)))‖ ≤ C₀ / t ^ (N + 1) := by
    rw [← hshiftpt]
    exact hstep₀
  calc ‖iteratedDeriv (j + 1) Complex.digamma (z + (lam : ℂ))
        - Q₀.eval (1 / (z + (lam : ℂ)))‖ + ‖H (1 / z) - P₁.eval (1 / z)‖
      ≤ C₀ / t ^ (N + 1) + C₁ / t ^ (N + 1) := add_le_add hstep₀' hHminus
    _ = (C₀ + C₁) / t ^ (N + 1) := by ring

end

end GaloisForLFunctions.HTGeometry
