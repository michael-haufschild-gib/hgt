/-
# Littlewood's identity for a Dirichlet polynomial on the critical line: the upper direction

`exists_edPoly_line_logMean_floor` dropped the (nonnegative) right-zero mass of `Ψ` to get the
`T`-free lower bound `−(C + K log Mb) ≤ ∫ log‖Ψ(1/2+it)‖`. Keeping it gives the upper direction:
the log-mean of the mollifier on the line is at most `2π` times its right-zero mass in
`[1/2, 15/2] × [T₁, T₂]` plus the same `T`-free budget. Together: the mollifier's line log-mean *is*
its right-zero mass, up to `O(log Mb)`.
-/
import GaloisForLFunctions.RHTower.MollifiedDetectorFarRightEdge
import GaloisForLFunctions.RHTower.EntireDirichletPolynomialHorizontalEdge
import GaloisForLFunctions.RHTower.EntireWeightedLittlewoodLeftClosure
import GaloisForLFunctions.RHTower.LevinsonMollifiedBudget
import GaloisForLFunctions.RHTower.MollifierLineLogMeanFloor

open MeasureTheory intervalIntegral Filter Topology Complex Finset Set
open scoped Classical

namespace RHTower

noncomputable section

theorem exists_edPoly_line_logMean_le_zeroMass :
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
      ∀ Z : Finset ℂ,
        (∀ z : ℂ, z ∈ Z ↔
          z ∈ (uIcc (1 / 2 : ℝ) (15 / 2) ×ℂ uIcc T₁ T₂) ∧ edPoly b (Finset.Icc 1 N) z = 0) →
        (∫ t in T₁..T₂,
            Real.log ‖edPoly b (Finset.Icc 1 N) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖)
          ≤ 2 * Real.pi * (∑ w ∈ Z,
              ((analyticOrderAt (edPoly b (Finset.Icc 1 N)) w).toNat : ℝ) * (w.re - 1 / 2))
            + (C + K * Real.log Mb) := by
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
  intro b N hN hb1 hbn hbreal Mb hMb1 hmass T₁ T₂ hT hP1 hP2 Zu hZu
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
  have hZeq : Zu = Z := by
    ext z
    rw [hZu z, hZ z]
  rw [hZeq]
  have hwlb := hident
  unfold weightedLittlewoodBoundary at hwlb
  have h7 : ((15 / 2 : ℝ) - 1 / 2) = 7 := by norm_num
  rw [h7] at hwlb
  have hlogMb : 0 ≤ Real.log Mb := Real.log_nonneg hMb1
  obtain ⟨hfl1, hfl2⟩ := abs_le.mp hfarlog
  obtain ⟨hfd1, hfd2⟩ := abs_le.mp hfarld
  obtain ⟨hh11, hh12⟩ := abs_le.mp hH1
  obtain ⟨hh21, hh22⟩ := abs_le.mp hH2
  have hKL : 0 ≤ KH / L := by positivity
  nlinarith [hKL, hlogMb, hwlb]


end

end RHTower
