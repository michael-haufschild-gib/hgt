import GaloisForLFunctions.RHTower.ZetaOffLineFirstMomentMollified

/-!
# Littlewood's lemma for `ζ` on the critical-line rectangle, with explicit-constant edges

The logarithmic integral of `|ζ|` along the critical line over `[T₁, T₂]` differs from `2π` times
the multiplicity-weighted first horizontal moment of the zeta zeros in `[1/2, 15/2] × [T₁, T₂]`
by at most `C + K log T₂`, with absolute constants `C, K`.  The three remaining edges of
Littlewood's rectangle are estimated exactly as in the corpus's Levinson budget, applied to the
trivial mollifier `Ψ ≡ 1`: the far-right edge by Cauchy and exponential decay of `Log ζ`, the
horizontal edges by the Backlund-type bound for `Re s ∈ [1/4, 15/2]`.

Consequences: the classical floor `∫ log|ζ(1/2+it)| dt ≥ −C − K log T₂` (Littlewood), and, with
`ZetaOffLineFirstMomentMollified`, the two-sided sandwich

```text
−C − K log T₂ ≤ ∫_{T₁}^{T₂} log|ζ(1/2+it)| dt
             ≤ ½ (T₂−T₁) log( Msq/(T₂−T₁) ) + C′ + K′ (log T₂ + log Mb)
```

for the mean square `Msq` of any admissible mollified product `ζΨ` on the line.  No RH premise
enters.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- The trivial mollifier coefficient sequence, `Ψ ≡ 1`. -/
def trivialMollifierCoeff (n : ℕ) : ℂ := if n = 1 then 1 else 0

theorem edPoly_trivialMollifierCoeff (z : ℂ) :
    edPoly trivialMollifierCoeff (Finset.Icc 1 1) z = 1 := by
  rw [edPoly, Finset.Icc_self, Finset.sum_singleton]
  simp [trivialMollifierCoeff]

theorem levinsonMollifiedDetector_zero_trivial :
    levinsonMollifiedDetector ((0 : ℝ) : ℂ) trivialMollifierCoeff (Finset.Icc 1 1) =
      riemannZeta := by
  funext z
  rw [levinsonMollifiedDetector, edPoly_trivialMollifierCoeff]
  simp [levinsonG]

theorem levinsonG_zero_eq (z : ℂ) : levinsonG ((0 : ℝ) : ℂ) z = riemannZeta z := by
  simp [levinsonG]

/-- The zeta zeros of a closed rectangle form a finset. -/
theorem exists_zetaRectangleZeros_finset {T₁ T₂ : ℝ} (h20 : 20 ≤ T₁) (hT : T₁ < T₂) :
    ∃ Z : Finset ℂ, ∀ z : ℂ, z ∈ Z ↔
      z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0 := by
  classical
  set F := levinsonGEntire ((0 : ℝ) : ℂ) with hFdef
  have hFan : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_levinsonGEntire _
  have hlamC : ‖((0 : ℝ) : ℂ)‖ ≤ 1 := by simp
  have hFne : ∃ z : ℂ, F z ≠ 0 :=
    ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I,
      levinsonGEntire_ne_zero_of_four_le hlamC (by simp; norm_num)⟩
  have hfin := entire_zeros_closedRectangle_finite hFan hFne
    (((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
  have hre1 : ((((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)).re = 1 / 2 := by simp
  have him1 : ((((1 / 2 : ℝ) : ℂ) + (T₁ : ℂ) * I)).im = T₁ := by simp
  have hre2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).re = 15 / 2 := by simp
  have him2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).im = T₂ := by simp
  rw [hre1, him1, hre2, him2] at hfin
  refine ⟨hfin.toFinset, ?_⟩
  intro z
  rw [Set.Finite.mem_toFinset, Set.mem_sep_iff]
  constructor
  · rintro ⟨hmem, hF0⟩
    refine ⟨hmem, ?_⟩
    have hz1 : z ≠ 1 := by
      intro h
      have him := (Complex.mem_reProdIm.mp hmem).2
      rw [h, Complex.one_im, uIcc_of_le hT.le] at him
      linarith [him.1]
    rwa [hFdef, levinsonGEntire_eq_zero_iff _ hz1, levinsonG_zero_eq] at hF0
  · rintro ⟨hmem, hζ0⟩
    refine ⟨hmem, ?_⟩
    have hz1 : z ≠ 1 := by
      intro h
      have him := (Complex.mem_reProdIm.mp hmem).2
      rw [h, Complex.one_im, uIcc_of_le hT.le] at him
      linarith [him.1]
    rw [hFdef, levinsonGEntire_eq_zero_iff _ hz1, levinsonG_zero_eq]
    exact hζ0

/-- **Littlewood's lemma for `ζ` on `[1/2, 15/2] × [T₁, T₂]` with explicit-constant edges.** -/
theorem exists_zetaLine_littlewood_edge_budget :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ T₁ T₂ : ℝ, 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ riemannZeta z = 0) →
        |(∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
            - 2 * Real.pi *
              (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))|
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
  intro T₁ T₂ h20 hT hG1 hG2 Z hZ
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
  have huIccx : uIcc (1 / 2 : ℝ) (15 / 2 : ℝ) = Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) :=
    uIcc_of_le (by norm_num)
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
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..(15 / 2 : ℝ), (x - 1 / 2) *
          (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im| ≤ KG * Real.log T := by
    intro T hT20 hne
    have h := hGhoriz 0 (by simp) T (by linarith) (1 / 2) (15 / 2) (by norm_num) (by norm_num)
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
  have hFbot : ∀ x ∈ uIcc (1 / 2 : ℝ) (15 / 2 : ℝ), F ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    rw [hFdef, Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ h20), levinsonG_zero_eq]
    exact hG1 x hx
  have hFtop : ∀ x ∈ uIcc (1 / 2 : ℝ) (15 / 2 : ℝ), F ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    rw [hFdef, Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith)), levinsonG_zero_eq]
    exact hG2 x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂, F (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => hGeright t
  obtain ⟨Z', hZ', hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hFan hFne
      (by norm_num : (1 / 2 : ℝ) < 15 / 2) hT hFbot hFtop hFright
  have hw1 : ∀ w ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂), w ≠ 1 := by
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
    have hev : F =ᶠ[nhds w] (fun z : ℂ => (z - 1) ^ 2) * riemannZeta := by
      filter_upwards [isOpen_ne.mem_nhds hwne] with z hz
      rw [Pi.mul_apply, hFdef, levinsonGEntire_eq _ hz, levinsonG_zero_eq]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => (z - 1) ^ 2) w :=
      ((analyticAt_id.sub analyticAt_const).pow 2)
    rw [analyticOrderAt_congr hev,
      analyticOrderAt_mul hpow_an (analyticAt_riemannZeta_of_ne_one hwne),
      (hpow_an.analyticOrderAt_eq_zero).mpr (pow_ne_zero 2 (sub_ne_zero.mpr hwne)), zero_add]
  have hmass : (∑ w ∈ Z', ((analyticOrderAt F w).toNat : ℝ) * (w.re - 1 / 2))
      = ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    rw [hZeq]
    apply Finset.sum_congr rfl
    intro w hw
    rw [horder w hw]
  -- ## pole gauge cancellation
  have hUopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hUsub : (uIcc (1 / 2 : ℝ) (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} :=
    fun z hz => hw1 z hz
  have hcongrF : weightedLittlewoodBoundary F (1 / 2) (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * riemannZeta z) (1 / 2) (15 / 2)
          T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr hUopen hUsub ?_
    intro z hz
    rw [hFdef, levinsonGEntire_eq _ hz, levinsonG_zero_eq]
  have hleftfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    have hinj : Set.InjOn (fun t : ℝ => ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) = 0} := by
      intro x _ y _ hxy
      simpa using congrArg Complex.im hxy
    refine Set.Finite.of_finite_image (Set.Finite.subset (Z : Set ℂ).toFinite ?_) hinj
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    rw [Finset.mem_coe, hZ]
    refine ⟨?_, hz⟩
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re = 1 / 2 := by simp
      rw [h]; exact left_mem_uIcc
    · have h : ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).im = t := by simp
      rw [h]; exact ht
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * riemannZeta z)
      (1 / 2) (15 / 2) T₁ T₂ = weightedLittlewoodBoundary riemannZeta (1 / 2) (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul (by norm_num) hT ?_ ?_ ?_ ?_ ?_ hleftfin
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
      (∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2))
      = weightedLittlewoodBoundary riemannZeta (1 / 2) (15 / 2) T₁ T₂ := by
    rw [← hmass, hident, hcongrF, hgaugefree]
  rw [hkey]
  unfold weightedLittlewoodBoundary
  have hH1 := hhoriz T₁ h20 hG1
  have hH2 := hhoriz T₂ (by linarith) hG2
  have hlogT1 : Real.log T₁ ≤ Real.log T₂ := Real.log_le_log (by linarith) hT.le
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have h7 : ((15 / 2 : ℝ) - 1 / 2) = 7 := by norm_num
  rw [h7]
  obtain ⟨hfl1, hfl2⟩ := abs_le.mp hfarlog
  obtain ⟨hfd1, hfd2⟩ := abs_le.mp hfarld
  obtain ⟨hh11, hh12⟩ := abs_le.mp hH1
  obtain ⟨hh21, hh22⟩ := abs_le.mp hH2
  rw [abs_le]
  constructor <;> nlinarith [hKG, hlogT1, hlogT2]

/-- **Littlewood's floor.**  The logarithmic mean of `|ζ|` on the critical line is bounded below
by `−C − K log T₂`. -/
theorem exists_zetaLine_logMean_floor :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ T₁ T₂ : ℝ, 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        -(C + K * Real.log T₂) ≤
          ∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  obtain ⟨C, K, hC, hK, hmain⟩ := exists_zetaLine_littlewood_edge_budget
  refine ⟨C, K, hC, hK, ?_⟩
  intro T₁ T₂ h20 hT hG1 hG2
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset h20 hT
  have h := hmain T₁ T₂ h20 hT hG1 hG2 Z hZ
  have hmass : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    apply Finset.sum_nonneg
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  obtain ⟨h1, _⟩ := abs_le.mp h
  nlinarith [mul_nonneg hpi hmass]

/-- **The critical-line log-mean sandwich.**  Between Littlewood's floor and the mollified
first-moment ceiling. -/
theorem exists_zetaLine_logMean_sandwich :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ Msq : ℝ, 20 ≤ T₁ → T₁ < T₂ → 0 < Msq →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          riemannZeta ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
            edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
        -(C + K * Real.log T₂) ≤
            (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖) ∧
          (∫ t in T₁..T₂, Real.log ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
            ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
                + C + K * (Real.log T₂ + Real.log Mb) := by
  obtain ⟨C₁, K₁, hC₁, hK₁, hedge⟩ := exists_zetaLine_littlewood_edge_budget
  obtain ⟨C₂, K₂, hC₂, hK₂, hmoment⟩ := exists_zetaOffLineFirstMoment_le_of_line_meanSquare
  refine ⟨C₁ + C₂, K₁ + K₂, by positivity, by positivity, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos hG1 hG2 hP1 hP2 hMsq
  have hsub : Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) ⊆ Set.Icc (1 / 4 : ℝ) (15 / 2 : ℝ) :=
    Set.Icc_subset_Icc (by norm_num) le_rfl
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset h20 hT
  have h1 := hedge T₁ T₂ h20 hT (fun x hx => hG1 x (hsub hx)) (fun x hx => hG2 x (hsub hx)) Z hZ
  have h2 := hmoment b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ Msq h20 hT hMsqpos
    hG1 hG2 hP1 hP2 hMsq Z hZ
  have hmass0 : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    apply Finset.sum_nonneg
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 15 / 2)] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hlogT2 : (0 : ℝ) ≤ Real.log T₂ := Real.log_nonneg (by linarith)
  have hlogMb : (0 : ℝ) ≤ Real.log Mb := Real.log_nonneg hMb1
  obtain ⟨h11, h12⟩ := abs_le.mp h1
  constructor
  · nlinarith [mul_nonneg hpi hmass0]
  · nlinarith

end

end RHTower
