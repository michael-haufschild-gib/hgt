/-
# The outer decomposition law for the mollified product `ζΨ`

Let `Ψ` be a real unit-head Dirichlet polynomial (a mollifier) and write, on the critical line,
`ℓ_F(T₁,T₂) := ∫_{T₁}^{T₂} log|F(1/2+it)| dt`. Off the finitely many zeros on the segment,
`log|ζΨ| = log|ζ| + log|Ψ|`, so

  `ℓ_{ζΨ} = ℓ_ζ + ℓ_Ψ`                                     (`integral_log_norm_zeta_mul_edPoly_line`).

Two one-sided laws bound the mollifier term:
* **Littlewood's floor** `ℓ_Ψ ≥ −(C + K log Mb)` (its right-zero mass is nonnegative), giving the
  producer direction `ℓ_ζ ≤ ℓ_{ζΨ} + C + K log Mb`
  (`exists_zetaLine_logMean_le_mollifiedProduct_logMean`): any outer law `ℓ_{ζΨ}(T,2T) = o(T)`
  forces the fixed-scale zero-density law `(L)`: `∑_{β>1/2}(β−1/2) = o(T)`.
* **The torus upper law** `ℓ_Ψ(T,2T) ≤ T (J_M(ε) + η)` eventually, where
  `J_M(ε) = ½ E_χ log max(|∑ μ(h)P(h)χ(h)h^{-1/2}|², ε²)` is the Steinhaus (polydisc) Jensen mass
  of the linear mollifier, giving the receiver direction
  `ℓ_{ζΨ_M}(T,2T) ≤ ℓ_ζ(T,2T) + T (J_M(ε) + η)`
  (`eventually_window_logMean_zeta_mul_linearMollifier_le`): under `(L)` the mollified product
  is outer up to the mollifier's own torus Jensen mass.

Everything is unconditional; `(L)` itself is not asserted.
-/
import GaloisForLFunctions.RHTower.MollifierLineLogMeanFloor
import GaloisForLFunctions.RHTower.DirichletPolynomialTorusLogUpperLaw
import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget
import GaloisForLFunctions.RHTower.LevinsonShiftedLinearMollifier

open MeasureTheory intervalIntegral Filter Topology Complex Finset Set
open scoped Classical

namespace RHTower

open SteinhausModel

noncomputable section

/-- `log ‖ζ(1/2+it)‖` is interval integrable on every segment of the critical line. -/
theorem intervalIntegrable_log_norm_riemannZeta_line (T₁ T₂ : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      volume T₁ T₂ := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro t _
  have hpath : AnalyticAt ℝ (fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) t :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
  have hne : ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  exact AnalyticAt.comp (f := fun u : ℝ => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)
    (analyticAt_riemannZeta_of_ne_one hne).restrictScalars hpath |>.meromorphicAt

/-- The zeros of `ζ` on a segment of the critical line (heights `≥ 20`) are finite. -/
theorem finite_zetaLine_zeros {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ < T₂) :
    {t : ℝ | t ∈ Set.Icc T₁ T₂ ∧ riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 0}.Finite := by
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset h20 hT
  refine ((Z : Set ℂ).toFinite.image Complex.im).subset ?_
  intro t ht
  refine ⟨((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I, ?_, by simp⟩
  rw [Finset.mem_coe, hZ]
  refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, ht.2⟩
  · have h : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by simp
    rw [h]; exact left_mem_uIcc
  · have h : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im = t := by simp
    rw [h, uIcc_of_le hT.le]; exact ht.1

/-- The zeros of a nondegenerate entire Dirichlet polynomial on a segment of the line are finite. -/
theorem finite_edPolyLine_zeros (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hne : ∃ z : ℂ, edPoly b s z ≠ 0) (T₁ T₂ : ℝ) :
    {t : ℝ | t ∈ Set.Icc T₁ T₂ ∧ edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 0}.Finite := by
  have hf : AnalyticOnNhd ℂ (edPoly b s) Set.univ := analyticOnNhd_edPoly b hs
  have hfin := entire_zeros_closedRectangle_finite hf hne (((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)
    (((1 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
  refine (hfin.image Complex.im).subset ?_
  intro t ht
  refine ⟨((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I, ⟨?_, ht.2⟩, by simp⟩
  rw [Complex.mem_reProdIm]
  constructor
  · simp
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [Set.uIcc_of_le (ht.1.1.trans ht.1.2)]
    exact ht.1

/-- **The outer decomposition identity on the line**: `ℓ_{ζΨ} = ℓ_ζ + ℓ_Ψ`. -/
theorem integral_log_norm_zeta_mul_edPoly_line (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (hne : ∃ z : ℂ, edPoly b s z ≠ 0) {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ < T₂) :
    (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      = (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        + ∫ t in T₁..T₂, Real.log ‖edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  rw [← intervalIntegral.integral_add (intervalIntegrable_log_norm_riemannZeta_line T₁ T₂)
    (intervalIntegrable_log_norm_vertical_of_entire (analyticOnNhd_edPoly b hs) (1 / 2) T₁ T₂)]
  apply intervalIntegral.integral_congr_ae
  have hζ := (finite_zetaLine_zeros h20 hT).measure_zero volume
  have hΨ := (finite_edPolyLine_zeros b hs hne T₁ T₂).measure_zero volume
  rw [MeasureTheory.measure_eq_zero_iff_ae_notMem] at hζ hΨ
  filter_upwards [hζ, hΨ] with t htζ htΨ hmem
  have hIcc : t ∈ Set.Icc T₁ T₂ := by
    rw [Set.uIoc_of_le hT.le] at hmem
    exact ⟨hmem.1.le, hmem.2⟩
  have hζ0 : riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun h => htζ ⟨hIcc, h⟩
  have hΨ0 : edPoly b s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun h => htΨ ⟨hIcc, h⟩
  rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hζ0) (norm_ne_zero_iff.mpr hΨ0)]

/-- **Producer direction of the outer law.**  The log-mean of `|ζ|` on the line is at most the
log-mean of the mollified product plus `C + K log Mb`: an outer law `ℓ_{ζΨ} = o(T)` for any
bounded unit-head mollifier forces `(L)`. -/
theorem exists_zetaLine_logMean_le_mollifiedProduct_logMean :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ : ℝ, 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
          ≤ (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
                edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
            + (C + K * Real.log Mb) := by
  obtain ⟨C, K, hC, hK, hfloor⟩ := exists_edPoly_line_logMean_floor
  refine ⟨C, K, hC, hK, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ h20 hT hP1 hP2
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hne : ∃ z : ℂ, edPoly b (Finset.Icc 1 N) z ≠ 0 := by
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn (z := (7 : ℂ)) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  have hdec := integral_log_norm_zeta_mul_edPoly_line b hs hne h20 hT
  have hfl := hfloor b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ hT hP1 hP2
  linarith

/-! ## The linear mollifier -/

/-- Real coefficients of the linear (Levinson) mollifier on the critical line. -/
def linearMollifierLineCoeff (M n : ℕ) : ℝ :=
  Sieve.barbanVehovWeight M n / Real.log M * (1 / Real.sqrt n)

theorem levinsonLinearMollifierCoeff_eq_ofReal (M n : ℕ) :
    Sieve.levinsonLinearMollifierCoeff M n = ((linearMollifierLineCoeff M n : ℝ) : ℂ) := by
  unfold Sieve.levinsonLinearMollifierCoeff linearMollifierLineCoeff
  push_cast
  ring

/-- The corpus mollifier on the line is the real Dirichlet polynomial of `linearMollifierLineCoeff`. -/
theorem levinsonLinearMollifier_eq_dpoly (M : ℕ) (t : ℝ) :
    Sieve.levinsonLinearMollifier M t = dpoly (linearMollifierLineCoeff M) (Finset.Icc 1 M) t := by
  rw [Sieve.levinsonLinearMollifier_eq_sum]
  unfold dpoly cterm
  apply Finset.sum_congr rfl
  intro n _
  rw [levinsonLinearMollifierCoeff_eq_ofReal]
  congr 1
  congr 1
  push_cast
  ring

/-- The shifted entire coefficient at `σ = 0` is the plain coefficient. -/
theorem levinsonShiftedLinearMollifierCoeff_zero (M n : ℕ) :
    levinsonShiftedLinearMollifierCoeff M 0 n = Sieve.levinsonLinearMollifierCoeff M n := by
  unfold levinsonShiftedLinearMollifierCoeff
  simp

/-- The entire Dirichlet polynomial of the real coefficients is the corpus one. -/
theorem edPoly_linearMollifierLineCoeff (M : ℕ) :
    edPoly (fun n => ((linearMollifierLineCoeff M n : ℝ) : ℂ)) (Finset.Icc 1 M)
      = edPoly (levinsonShiftedLinearMollifierCoeff M 0) (Finset.Icc 1 M) := by
  funext z
  unfold edPoly
  apply Finset.sum_congr rfl
  intro n _
  rw [levinsonShiftedLinearMollifierCoeff_zero, levinsonLinearMollifierCoeff_eq_ofReal]

/-- The mollifier's torus Jensen mass (truncated at `ε`):
`J_M(ε) = ½ E_χ log max(‖∑_{h≤M} μ(h)P(h)χ(h)h^{-1/2}‖², ε²)`. -/
def linearMollifierTorusLogMean (M : ℕ) (ε : ℝ) : ℝ :=
  ∫ ω, logMaxHalf ε (‖steinhausAmp (linearMollifierLineCoeff M) (Finset.Icc 1 M) ω‖ ^ (2 : ℕ))
    ∂steinhausMeasure

/-- **Receiver direction of the outer law (linear mollifier).**  Eventually
`ℓ_{ζΨ_M}(T,2T) ≤ ℓ_ζ(T,2T) + T (J_M(ε) + η)`: under `(L)` the mollified product is outer up to
the mollifier's torus Jensen mass. -/
theorem eventually_window_logMean_zeta_mul_linearMollifier_le (M : ℕ) (hM : 1 < M)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ T in atTop,
      (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2)) (Finset.Icc 1 M)
            (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
        ≤ (∫ t in T..(2 * T), Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
          + T * (linearMollifierTorusLogMean M ε + η) := by
  set s : Finset ℕ := Finset.Icc 1 M with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hM.le⟩
  set a : ℕ → ℝ := linearMollifierLineCoeff M with ha
  -- nondegeneracy of the entire polynomials (unit head, bounded coefficients)
  have hb1 : levinsonShiftedLinearMollifierCoeff M (1 / 2) 1 = 1 :=
    levinsonShiftedLinearMollifierCoeff_one hM _
  have hbn : ∀ n ∈ s, ‖levinsonShiftedLinearMollifierCoeff M (1 / 2) n‖ ≤ 1 :=
    fun n hn => norm_levinsonShiftedLinearMollifierCoeff_le_one hM (hs n hn) le_rfl
  have hb1' : levinsonShiftedLinearMollifierCoeff M 0 1 = 1 :=
    levinsonShiftedLinearMollifierCoeff_one hM _
  have hbn' : ∀ n ∈ s, ‖levinsonShiftedLinearMollifierCoeff M 0 n‖ ≤ 1 :=
    fun n hn => norm_levinsonShiftedLinearMollifierCoeff_le_one hM (hs n hn) (by norm_num)
  have hne : ∃ z : ℂ, edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2)) s z ≠ 0 := by
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le _ hs h1 hb1 hbn (z := (7 : ℂ))
      (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  have hne' : ∃ z : ℂ, edPoly (fun n => ((a n : ℝ) : ℂ)) s z ≠ 0 := by
    rw [ha, edPoly_linearMollifierLineCoeff]
    refine ⟨(7 : ℂ), fun h0 => ?_⟩
    have h := norm_edPoly_sub_one_le_half_of_six_le _ hs h1 hb1' hbn' (z := (7 : ℂ))
      (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  have htorus := eventually_window_logMean_dpoly_le a s hs hne' hε hη
  filter_upwards [htorus, eventually_ge_atTop (20 : ℝ), eventually_gt_atTop (0 : ℝ)]
    with T hTor h20 hTpos
  have hT : T < 2 * T := by linarith
  have hdec := integral_log_norm_zeta_mul_edPoly_line
    (levinsonShiftedLinearMollifierCoeff M (1 / 2)) hs hne h20 hT
  -- the mollifier on the line is the real Dirichlet polynomial
  have hline : ∀ t : ℝ,
      edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2)) s (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        = dpoly a s t := by
    intro t
    rw [hsdef, edPoly_levinsonShiftedLinearMollifierCoeff_line M (1 / 2) t,
      levinsonLinearMollifier_eq_dpoly]
  have hΨint : (∫ t in T..(2 * T), Real.log ‖edPoly (levinsonShiftedLinearMollifierCoeff M (1 / 2)) s
      (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
      = ∫ t in T..(2 * T), Real.log ‖dpoly a s t‖ := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [hline t]
  have hbound : (∫ t in T..(2 * T), Real.log ‖dpoly a s t‖)
      ≤ T * (linearMollifierTorusLogMean M ε + η) := by
    have := hTor
    rw [inv_mul_le_iff₀ hTpos] at this
    unfold linearMollifierTorusLogMean
    exact this
  rw [hdec, hΨint]
  linarith

end

end RHTower
