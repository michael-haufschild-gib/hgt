/-
# Littlewood's floor for a mollifier polynomial on the critical line

For a real Dirichlet polynomial `Ψ = edPoly b (Icc 1 N)` with unit head and bounded
coefficients, Littlewood's lemma on `[1/2, 15/2] × [T₁, T₂]` reads

  `2π ∑_{Ψ(ρ)=0, Re ρ > 1/2} m_ρ (Re ρ − 1/2) = ∫_{T₁}^{T₂} log|Ψ(1/2+it)| dt + (edges)`,

and the edges are `O(1 + log Mb)` uniformly in the heights: the far-right edge is the
`O(1)` Dirichlet-series-of-`log` bound, the horizontal edges are the weighted
argument-variation bound for Dirichlet polynomials. Hence the mollifier's own right-zero mass
is nonnegative and its logarithmic mean on the line is bounded below by `−(C + K log Mb)`,
**with no dependence on `T`** — the mollifier part of the outer decomposition law.
-/
import GaloisForLFunctions.RHTower.MollifiedDetectorFarRightEdge
import GaloisForLFunctions.RHTower.EntireDirichletPolynomialHorizontalEdge
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodLeftClosure
import GaloisForLFunctions.RHTower.LevinsonMollifiedBudget

open MeasureTheory intervalIntegral Filter Topology Complex Finset Set
open scoped Classical

namespace RHTower

noncomputable section

/-- Far-right smallness of a unit-head bounded Dirichlet polynomial. -/
theorem norm_edPoly_sub_one_le_half_of_six_le (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (h1 : 1 ∈ s) (hb1 : b 1 = 1) (hbn : ∀ n ∈ s, ‖b n‖ ≤ 1) {z : ℂ} (hz : 6 ≤ z.re) :
    ‖edPoly b s z - 1‖ ≤ 1 / 2 := by
  have h := norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn (z := z) (by linarith)
  have hexp : Real.exp (-(Real.log 2) * z.re) ≤ Real.exp (-(Real.log 2) * 6) := by
    apply Real.exp_le_exp.mpr
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have h6 : Real.exp (-(Real.log 2) * 6) = 1 / 64 := by
    rw [exp_neg_log_two_eq]
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  rw [h6] at hexp
  linarith

/-- The trace at abscissa `4` of a unit-head bounded Dirichlet polynomial has norm `≥ 5/16`. -/
theorem five_sixteenth_le_norm_edPolyTrace_four (b : ℕ → ℂ) {s : Finset ℕ} (hs : ∀ n ∈ s, 1 ≤ n)
    (h1 : 1 ∈ s) (hb1 : b 1 = 1) (hbn : ∀ n ∈ s, ‖b n‖ ≤ 1) (T : ℝ) :
    (5 / 16 : ℝ) ≤ ‖edPolyTrace b s T 4‖ := by
  have hexp4 : Real.exp (-(Real.log 2) * (4 : ℝ)) = 1 / 16 := by
    rw [exp_neg_log_two_eq]
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hp : ‖edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1‖ ≤ 11 / 16 := by
    have h := norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn (z := (4 : ℂ) + (T : ℂ) * I)
      (by simp; norm_num)
    have hre : ((4 : ℂ) + (T : ℂ) * I).re = 4 := by simp
    rw [hre, hexp4] at h
    linarith
  have hm : ‖edPoly b s ((4 : ℂ) - (T : ℂ) * I) - 1‖ ≤ 11 / 16 := by
    have h := norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn (z := (4 : ℂ) - (T : ℂ) * I)
      (by simp; norm_num)
    have hre : ((4 : ℂ) - (T : ℂ) * I).re = 4 := by simp
    rw [hre, hexp4] at h
    linarith
  have htr : edPolyTrace b s T 4 - 1 =
      ((edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1) + (edPoly b s ((4 : ℂ) - (T : ℂ) * I) - 1)) / 2 := by
    unfold edPolyTrace
    ring
  have hdist : ‖edPolyTrace b s T 4 - 1‖ ≤ 11 / 16 := by
    rw [htr, norm_div, Complex.norm_ofNat]
    calc ‖(edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1) + (edPoly b s ((4 : ℂ) - (T : ℂ) * I) - 1)‖ / 2
        ≤ (‖edPoly b s ((4 : ℂ) + (T : ℂ) * I) - 1‖ + ‖edPoly b s ((4 : ℂ) - (T : ℂ) * I) - 1‖) / 2 := by
          gcongr
          exact norm_add_le _ _
      _ ≤ 11 / 16 := by linarith
  have := norm_sub_norm_le (1 : ℂ) (edPolyTrace b s T 4)
  rw [norm_one, norm_sub_rev] at this
  linarith

/-- **Littlewood's floor for a mollifier polynomial on the critical line.**
`−(C + K log Mb) ≤ ∫_{T₁}^{T₂} log ‖Ψ(1/2+it)‖ dt`, uniformly in the heights. -/
theorem exists_edPoly_line_logMean_floor :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ T₁ T₂ : ℝ, T₁ < T₂ →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        -(C + K * Real.log Mb) ≤
          ∫ t in T₁..T₂,
            Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  classical
  set α : ℝ := Real.log 2 with hα
  have hαpos : 0 < α := Real.log_pos (by norm_num)
  set Cfar : ℝ := 2 * (2 * 11 * Real.exp (-α * (15 / 2)) / α) with hCfar
  set Cfar' : ℝ := 2 * ((2 * 11 * Real.exp α) * Real.exp (-α * (15 / 2)) / α) with hCfar'
  have hCfar0 : 0 < Cfar := by rw [hCfar]; positivity
  have hCfar'0 : 0 < Cfar' := by rw [hCfar']; positivity
  set L : ℝ := Real.log (32 / 15) with hL
  have hLpos : 0 < L := Real.log_pos (by norm_num)
  set KH : ℝ := 2 * 7 * Real.pi with hKH
  have hKHpos : 0 < KH := by rw [hKH]; positivity
  refine ⟨Cfar + 7 * Cfar' + 2 * (KH * (Real.log (16 / 5) / L + 1)), 2 * (KH / L),
    by positivity, by positivity, ?_⟩
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ hT hP1 hP2
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ n ∈ s, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have h1 : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  set Ψ : ℂ → ℂ := edPoly b s with hΨdef
  have hΨan : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have huIccx : uIcc (1 / 2 : ℝ) (15 / 2 : ℝ) = Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ) :=
    uIcc_of_le (by norm_num)
  -- far-right data
  have hfarana : ∀ z : ℂ, (6 : ℝ) < z.re → AnalyticAt ℂ Ψ z := fun z _ => hΨan z (Set.mem_univ z)
  have hfardec : ∀ z : ℂ, (6 : ℝ) < z.re → ‖Ψ z - 1‖ ≤ 11 * Real.exp (-α * z.re) :=
    fun z hz => norm_edPoly_sub_one_le_exp b hs h1 hb1 hbn (z := z) (by linarith)
  have hfarsmall : ∀ z : ℂ, (6 : ℝ) < z.re → ‖Ψ z - 1‖ ≤ 1 / 2 :=
    fun z hz => norm_edPoly_sub_one_le_half_of_six_le b hs h1 hb1 hbn hz.le
  have hfarlog : |∫ t in T₁..T₂, Real.log ‖Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖| ≤ Cfar :=
    abs_integral_log_norm_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hfarld : |∫ t in T₁..T₂, (logDeriv Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re| ≤ Cfar' :=
    abs_integral_re_logDeriv_farRight_le hαpos (by norm_num) hT.le (by norm_num)
      hfarana hfardec hfarsmall
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    have h := hfarsmall (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) (by simp; norm_num)
    rw [h0] at h
    have : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [this] at h
    norm_num at h
  -- horizontal edges
  have hhoriz : ∀ T : ℝ,
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), Ψ ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..(15 / 2 : ℝ), (x - 1 / 2) *
          (logDeriv Ψ ((x : ℂ) + (T : ℂ) * I)).im| ≤
        KH * (Real.log (16 / 5) / L + 1) + (KH / L) * Real.log Mb := by
    intro T hne
    have h := abs_integral_weighted_im_logDeriv_edPoly_le b hs hbreal T
      (c := 1 / 2) (e := 15 / 2) (r := 15 / 4) (m := 5 / 16) (Mb := Mb)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hne (by norm_num)
      hMb1 (five_sixteenth_le_norm_edPolyTrace_four b hs h1 hb1 hbn T) hmass
    have hlogq : Real.log (Mb / (5 / 16)) = Real.log Mb + Real.log (16 / 5) := by
      rw [div_eq_mul_inv, Real.log_mul (by positivity) (by norm_num)]
      congr 1
      norm_num
    have hL' : Real.log (8 / (15 / 4 : ℝ)) = L := by
      rw [hL]; norm_num
    rw [hlogq, hL'] at h
    have h72 : ((15 / 2 : ℝ) - 1 / 2) = 7 := by norm_num
    rw [h72] at h
    calc |∫ x in (1 / 2 : ℝ)..(15 / 2 : ℝ), (x - 1 / 2) *
          (logDeriv Ψ ((x : ℂ) + (T : ℂ) * I)).im|
        ≤ 2 * 7 * (((Real.log Mb + Real.log (16 / 5)) / L + 1) * Real.pi) := h
      _ = KH * (Real.log (16 / 5) / L + 1) + (KH / L) * Real.log Mb := by
          rw [hKH]; field_simp; ring
  have hH1 := hhoriz T₁ hP1
  have hH2 := hhoriz T₂ hP2
  -- Littlewood's identity
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := ⟨_, hΨright T₁⟩
  have hbot : ∀ x ∈ uIcc (1 / 2 : ℝ) (15 / 2 : ℝ), Ψ ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx; exact hP1 x hx
  have htop : ∀ x ∈ uIcc (1 / 2 : ℝ) (15 / 2 : ℝ), Ψ ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx; rw [huIccx] at hx; exact hP2 x hx
  have hright : ∀ t ∈ uIcc T₁ T₂, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => hΨright t
  obtain ⟨Z, hZ, hident⟩ :=
    exists_entire_weighted_littlewood_rectangle_allow_left_zeros hΨan hΨne
      (by norm_num : (1 / 2 : ℝ) < 15 / 2) hT hbot htop hright
  have hmass0 : 0 ≤ ∑ w ∈ Z, ((analyticOrderAt Ψ w).toNat : ℝ) * (w.re - 1 / 2) := by
    apply Finset.sum_nonneg
    intro w hw
    have hre := (Complex.mem_reProdIm.mp ((hZ w).mp hw).1).1
    rw [huIccx] at hre
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hre.1])
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hwlb : 0 ≤ weightedLittlewoodBoundary Ψ (1 / 2) (15 / 2) T₁ T₂ := by
    rw [← hident]; exact mul_nonneg hpi hmass0
  unfold weightedLittlewoodBoundary at hwlb
  have h7 : ((15 / 2 : ℝ) - 1 / 2) = 7 := by norm_num
  rw [h7] at hwlb
  have hlogMb : 0 ≤ Real.log Mb := Real.log_nonneg hMb1
  obtain ⟨hfl1, hfl2⟩ := abs_le.mp hfarlog
  obtain ⟨hfd1, hfd2⟩ := abs_le.mp hfarld
  obtain ⟨hh11, hh12⟩ := abs_le.mp hH1
  obtain ⟨hh21, hh22⟩ := abs_le.mp hH2
  have hKL : 0 ≤ KH / L := by positivity
  nlinarith [hKL, hlogMb]

end

end RHTower
