import GaloisForLFunctions.RHTower.ZetaLineLogMeanLittlewoodBudget

/-!
# Littlewood's floor on displaced vertical lines

For `½ ≤ c ≤ 1`, Littlewood's lemma on the rectangle `[c, 15/2] × [T₁, T₂]` gives

  `|∫_{T₁}^{T₂} log|ζ(c + it)| dt − 2π Σ_ρ (Re ρ − c)| ≤ C + K log T₂`,

the sum running over the zeros in the rectangle with multiplicity, when the horizontal edges are
zero-free (`exists_zetaDisplacedLine_littlewood_edge_budget`). The edges are estimated as on the
critical line (`exists_zetaLine_littlewood_edge_budget`): the far-right edge by the exponential
decay of `log ζ`, the horizontal edges by the Backlund-type bound on `1/4 ≤ Re s ≤ 15/2`. The
zero sum is nonnegative, so `∫_{T₁}^{T₂} log|ζ(c + it)| dt ≥ −C − K log T₂`
(`exists_zetaDisplacedLine_logMean_floor`), uniformly in `c`.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **Littlewood's lemma on `[c, 15/2] × [T₁, T₂]`, uniformly for `½ ≤ c ≤ 1`.** -/
theorem exists_zetaDisplacedLine_littlewood_edge_budget :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ c : ℝ, 1 / 2 ≤ c → c ≤ 1 →
      ∀ T₁ T₂ : ℝ, 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc c (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        |(∫ t in T₁..T₂, Real.log ‖riemannZeta ((c : ℂ) + (t : ℂ) * I)‖)
            - 2 * Real.pi *
              (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - c))|
          ≤ C + K * Real.log T₂ := by
  classical
  obtain ⟨KG, hKG, hGhoriz⟩ := exists_horizontal_weighted_levinsonG_bound
  set α : ℝ := Real.log 2 with hα
  have hαpos : 0 < α := Real.log_pos (by norm_num)
  set Cfar : ℝ := 2 * (2 * 22 * Real.exp (-α * (15 / 2)) / α) with hCfar
  set Cfar' : ℝ := 2 * ((2 * 22 * Real.exp α) * Real.exp (-α * (15 / 2)) / α) with hCfar'
  have hCfar0 : 0 < Cfar := by rw [hCfar]; positivity
  have hCfar'0 : 0 < Cfar' := by rw [hCfar']; positivity
  refine ⟨Cfar + 7 * Cfar', 2 * KG, by positivity, by positivity, ?_⟩
  intro c hc1 hc2 T₁ T₂ h20 hT hG1' hG2' Z hZ
  have hG1 : ∀ x ∈ Set.Icc c (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 :=
    fun x hx => hG1' x ⟨by linarith [hx.1], hx.2⟩
  have hG2 : ∀ x ∈ Set.Icc c (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 :=
    fun x hx => hG2' x ⟨by linarith [hx.1], hx.2⟩
  set s : Finset ℕ := Finset.Icc 1 1 with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  have hb1 : trivialMollifierCoeff 1 = 1 := by simp [trivialMollifierCoeff]
  have hbn : ∀ n ∈ s, ‖trivialMollifierCoeff n‖ ≤ 1 := by
    intro n _
    simp only [trivialMollifierCoeff]
    split_ifs <;> simp
  have hlamC : ‖((0 : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hdet : levinsonMollifiedDetector ((0 : ℝ) : ℂ) trivialMollifierCoeff s = riemannZeta :=
    levinsonMollifiedDetector_zero_trivial
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have huIccx : uIcc c (15 / 2 : ℝ) = Set.Icc c (15 / 2 : ℝ) :=
    uIcc_of_le (by linarith)
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  -- ## far-right edge
  have hfarana : ∀ z : ℂ, (6 : ℝ) < z.re → AnalyticAt ℂ riemannZeta z := by
    intro z hz
    refine analyticAt_riemannZeta_of_ne_one ?_
    intro h
    rw [h, Complex.one_re] at hz
    linarith
  have hfardec : ∀ z : ℂ, (6 : ℝ) < z.re →
      ‖riemannZeta z - 1‖ ≤ 22 * Real.exp (-α * z.re) := by
    intro z hz
    have h := norm_levinsonMollifiedDetector_sub_one_le_exp hlamC trivialMollifierCoeff hs h1
      hb1 hbn (z := z) hz.le
    rwa [hdet] at h
  have hfarsmall : ∀ z : ℂ, (6 : ℝ) < z.re → ‖riemannZeta z - 1‖ ≤ 1 / 2 := by
    intro z hz
    have h := norm_levinsonMollifiedDetector_sub_one_le_half hlamC trivialMollifierCoeff hs h1
      hb1 hbn (z := z) hz.le
    rwa [hdet] at h
  have hfarlog : |∫ t in T₁..T₂,
      Real.log ‖riemannZeta (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ Cfar :=
    abs_integral_log_norm_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hfarld : |∫ t in T₁..T₂,
      (logDeriv riemannZeta (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ Cfar' :=
    abs_integral_re_logDeriv_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  -- ## horizontal edges
  have hfun : levinsonG ((0 : ℝ) : ℂ) = riemannZeta := funext levinsonG_zero_eq
  have hhoriz : ∀ T : ℝ, 20 ≤ T →
      (∀ x ∈ Set.Icc c (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in c..(15 / 2 : ℝ), (x - c) *
          (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im| ≤ KG * Real.log T := by
    intro T hT20 hne
    have h := hGhoriz 0 (by simp) T (by linarith) c (15 / 2) (by linarith) (by linarith)
      le_rfl (by intro x hx; rw [levinsonG_zero_eq]; exact hne x hx)
    rw [hfun] at h
    exact h
  -- ## the exact identity for the entire detector
  set F := levinsonGEntire ((0 : ℝ) : ℂ) with hFdef
  have hFan : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_levinsonGEntire _
  have hGeright : ∀ t : ℝ, F (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := fun t =>
    levinsonGEntire_ne_zero_of_four_le hlamC (by simp; norm_num)
  have hζright : ∀ t : ℝ, riemannZeta (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    rw [← levinsonG_zero_eq]
    exact levinsonG_ne_zero_of_four_le hlamC (by simp; norm_num)
  have hFne : ∃ z : ℂ, F z ≠ 0 := ⟨_, hGeright T₁⟩
  have hFbot : ∀ x ∈ uIcc c (15 / 2 : ℝ), F ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    rw [hFdef, Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ h20), levinsonG_zero_eq]
    exact hG1 x hx
  have hFtop : ∀ x ∈ uIcc c (15 / 2 : ℝ), F ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    rw [hFdef, Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith)), levinsonG_zero_eq]
    exact hG2 x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂, F (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => hGeright t
  obtain ⟨Z', hZ', hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hFan hFne
      (by linarith : c < 15 / 2) hT hFbot hFtop hFright
  have hw1 : ∀ w ∈ (uIcc c (15 / 2) ×ℂ uIcc T₁ T₂), w ≠ 1 := by
    intro w hw h
    have him := (Complex.mem_reProdIm.mp hw).2
    rw [h, Complex.one_im, huIcct] at him
    linarith [him.1]
  have hZeq : Z' = Z := by
    ext w
    rw [hZ' w, hZ w]
    constructor
    · rintro ⟨hmem, hF0⟩
      refine ⟨hmem, ?_⟩
      rwa [hFdef, levinsonGEntire_eq_zero_iff _ (hw1 w hmem), levinsonG_zero_eq] at hF0
    · rintro ⟨hmem, hζ0⟩
      refine ⟨hmem, ?_⟩
      rw [hFdef, levinsonGEntire_eq_zero_iff _ (hw1 w hmem), levinsonG_zero_eq]
      exact hζ0
  have horder : ∀ w ∈ Z, analyticOrderAt F w = analyticOrderAt riemannZeta w := by
    intro w hw
    have hwne : w ≠ 1 := hw1 w ((hZ w).mp hw).1
    have hev : F =ᶠ[nhds w] (fun z : ℂ => (z - 1) ^ (2 : ℕ)) * riemannZeta := by
      filter_upwards [isOpen_ne.mem_nhds hwne] with z hz
      rw [Pi.mul_apply, hFdef, levinsonGEntire_eq _ hz, levinsonG_zero_eq]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ (2 : ℕ)) w :=
      ((analyticAt_id.sub analyticAt_const).pow 2)
    rw [analyticOrderAt_congr hev,
      analyticOrderAt_mul hpow_an (analyticAt_riemannZeta_of_ne_one hwne),
      (hpow_an.analyticOrderAt_eq_zero).mpr (pow_ne_zero 2 (sub_ne_zero.mpr hwne)), zero_add]
  have hmass : (∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - c))
      = ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - c) := by
    rw [hZeq]
    apply Finset.sum_congr rfl
    intro w hw
    rw [horder w hw]
  -- ## pole gauge cancellation
  have hUopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hUsub : (uIcc c (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} :=
    fun z hz => hw1 z hz
  have hcongrF : weightedLittlewoodBoundary F c (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary (fun z => (z - 1) ^ (2 : ℕ) * riemannZeta z) c (15 / 2)
          T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr hUopen hUsub ?_
    intro z hz
    rw [hFdef, levinsonGEntire_eq _ hz, levinsonG_zero_eq]
  have hleftfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧
      riemannZeta ((c : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    have hinj : Set.InjOn (fun t : ℝ => (c : ℂ) + (t : ℂ) * I)
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ riemannZeta ((c : ℂ) + (t : ℂ) * I) = 0} := by
      intro x _ y _ hxy
      simpa using congrArg Complex.im hxy
    refine Set.Finite.of_finite_image (Set.Finite.subset (Z : Set ℂ).toFinite ?_) hinj
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    rw [Finset.mem_coe, hZ]
    refine ⟨?_, hz⟩
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : (((c : ℂ) + (t : ℂ) * I)).re = c := by simp
      rw [h]; exact left_mem_uIcc
    · have h : (((c : ℂ) + (t : ℂ) * I)).im = t := by simp
      rw [h]; exact ht
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ (2 : ℕ) * riemannZeta z)
      c (15 / 2) T₁ T₂ = weightedLittlewoodBoundary riemannZeta c (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul (by linarith) hT ?_ ?_ ?_ ?_ ?_ hleftfin
    · intro hmem
      exact hw1 1 hmem rfl
    · intro z hz
      exact analyticAt_riemannZeta_of_ne_one (hUsub hz)
    · intro x hx
      rw [huIccx] at hx
      exact hG1 x hx
    · intro x hx
      rw [huIccx] at hx
      exact hG2 x hx
    · intro t _
      exact hζright t
  have hkey : 2 * Real.pi *
      (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - c))
      = weightedLittlewoodBoundary riemannZeta c (15 / 2) T₁ T₂ := by
    rw [← hmass, hident, hcongrF, hgaugefree]
  rw [hkey]
  unfold weightedLittlewoodBoundary
  have hH1 := hhoriz T₁ h20 hG1
  have hH2 := hhoriz T₂ (by linarith) hG2
  have hlogT1 : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log (by linarith) hT.le
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  obtain ⟨hfl1, hfl2⟩ := abs_le.mp hfarlog
  have hX : |((15 / 2 : ℝ) - c) * ∫ t in T₁..T₂,
      (logDeriv riemannZeta (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ 7 * Cfar' := by
    rw [abs_mul, abs_of_nonneg (by linarith)]
    exact mul_le_mul (by linarith) hfarld (abs_nonneg _) (by norm_num)
  obtain ⟨hX1, hX2⟩ := abs_le.mp hX
  obtain ⟨hh11, hh12⟩ := abs_le.mp hH1
  obtain ⟨hh21, hh22⟩ := abs_le.mp hH2
  have hKl1 : KG * Real.log T₁ ≤ KG * Real.log T₂ := mul_le_mul_of_nonneg_left hlogT1 hKG.le
  rw [abs_le]
  constructor <;> linarith

/-- **Littlewood's floor on displaced lines.** Uniformly for `½ ≤ c ≤ 1`, the logarithmic
integral of `|ζ(c + it)|` over `[T₁, T₂]` is at least `−C − K log T₂` when the horizontal edges of
`[½, 15/2] × [T₁, T₂]` are zero-free. -/
theorem exists_zetaDisplacedLine_logMean_floor :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∀ c : ℝ, 1 / 2 ≤ c → c ≤ 1 →
      ∀ T₁ T₂ : ℝ, 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        -(C + K * Real.log T₂) ≤ ∫ t in T₁..T₂, Real.log ‖riemannZeta ((c : ℂ) + (t : ℂ) * I)‖ := by
  classical
  obtain ⟨C, K, hC, hK, hmain⟩ := exists_zetaDisplacedLine_littlewood_edge_budget
  refine ⟨C, K, hC, hK, ?_⟩
  intro c hc1 hc2 T₁ T₂ h20 hT hG1 hG2
  obtain ⟨Z₀, hZ₀⟩ := exists_zetaRectangleZeros_finset h20 hT
  set Z := Z₀.filter (fun w => c ≤ w.re) with hZdef
  have hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc c (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
    intro z
    rw [hZdef, Finset.mem_filter, hZ₀, uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2),
      uIcc_of_le (by linarith : c ≤ 15 / 2), Complex.mem_reProdIm, Complex.mem_reProdIm]
    constructor
    · rintro ⟨⟨⟨hre, him⟩, h0⟩, hc⟩
      exact ⟨⟨⟨hc, hre.2⟩, him⟩, h0⟩
    · rintro ⟨⟨⟨hre1, hre2⟩, him⟩, h0⟩
      exact ⟨⟨⟨⟨by linarith, hre2⟩, him⟩, h0⟩, hre1⟩
  have h := hmain c hc1 hc2 T₁ T₂ h20 hT hG1 hG2 Z hZ
  have hmass : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - c) := by
    apply Finset.sum_nonneg
    intro w hw
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [(Finset.mem_filter.mp hw).2])
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  obtain ⟨h1, _⟩ := abs_le.mp h
  nlinarith [mul_nonneg hpi hmass]

end

end RHTower
