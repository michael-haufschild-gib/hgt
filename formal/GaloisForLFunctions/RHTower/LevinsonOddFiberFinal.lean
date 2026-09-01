import GaloisForLFunctions.RHTower.LevinsonMollifiedBudget
import GaloisForLFunctions.RHTower.LevinsonWindowEdgeUnconditional

/-!
# Levinson's window count from the mollified mean square

The last link: the entire mollified detector `G♯·Ψ` has the same Littlewood boundary functional as
the meromorphic `G·Ψ` (the pole gauge cancels exactly), the latter is bounded by the mollified mean
square plus `O(log T + log Mb)`, and the resulting zero-mass bound feeds the window inequality.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

noncomputable section

namespace RHTower

theorem logDeriv_congr_of_eventuallyEq' {f g : ℂ → ℂ} {s : ℂ} (h : f =ᶠ[nhds s] g) :
    logDeriv f s = logDeriv g s := by
  rw [logDeriv, logDeriv]
  simp only [Pi.div_apply]
  rw [h.deriv_eq, h.eq_of_nhds]

/-- The boundary functional only sees the values on an open neighbourhood of the rectangle. -/
theorem weightedLittlewoodBoundary_congr {f g : ℂ → ℂ} {c d T₁ T₂ : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hsub : (uIcc c d ×ℂ uIcc T₁ T₂) ⊆ U) (heq : ∀ z ∈ U, f z = g z) :
    weightedLittlewoodBoundary f c d T₁ T₂ = weightedLittlewoodBoundary g c d T₁ T₂ := by
  have hmembot : ∀ x ∈ uIcc c d, ((x : ℂ) + (T₁ : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((x : ℂ) + (T₁ : ℂ) * I).re = x := by simp
      rw [h]; exact hx
    · have h : ((x : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
      rw [h]; exact left_mem_uIcc
  have hmemtop : ∀ x ∈ uIcc c d, ((x : ℂ) + (T₂ : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro x hx
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((x : ℂ) + (T₂ : ℂ) * I).re = x := by simp
      rw [h]; exact hx
    · have h : ((x : ℂ) + (T₂ : ℂ) * I).im = T₂ := by simp
      rw [h]; exact right_mem_uIcc
  have hmemright : ∀ t ∈ uIcc T₁ T₂, ((d : ℂ) + (t : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((d : ℂ) + (t : ℂ) * I).re = d := by simp
      rw [h]; exact right_mem_uIcc
    · have h : ((d : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [h]; exact ht
  have hmemleft : ∀ t ∈ uIcc T₁ T₂, ((c : ℂ) + (t : ℂ) * I) ∈ (uIcc c d ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
      rw [h]; exact left_mem_uIcc
    · have h : ((c : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [h]; exact ht
  have hld : ∀ z ∈ (uIcc c d ×ℂ uIcc T₁ T₂), logDeriv f z = logDeriv g z := by
    intro z hz
    refine logDeriv_congr_of_eventuallyEq' ?_
    filter_upwards [hU.mem_nhds (hsub hz)] with w hw using heq w hw
  unfold weightedLittlewoodBoundary
  have e1 : (∫ t in T₁..T₂, Real.log ‖f ((c : ℂ) + (t : ℂ) * I)‖)
      = ∫ t in T₁..T₂, Real.log ‖g ((c : ℂ) + (t : ℂ) * I)‖ :=
    intervalIntegral.integral_congr fun t ht => by rw [heq _ (hsub (hmemleft t ht))]
  have e2 : (∫ t in T₁..T₂, Real.log ‖f ((d : ℂ) + (t : ℂ) * I)‖)
      = ∫ t in T₁..T₂, Real.log ‖g ((d : ℂ) + (t : ℂ) * I)‖ :=
    intervalIntegral.integral_congr fun t ht => by rw [heq _ (hsub (hmemright t ht))]
  have e3 : (∫ t in T₁..T₂, (logDeriv f ((d : ℂ) + (t : ℂ) * I)).re)
      = ∫ t in T₁..T₂, (logDeriv g ((d : ℂ) + (t : ℂ) * I)).re :=
    intervalIntegral.integral_congr fun t ht => by rw [hld _ (hmemright t ht)]
  have e4 : (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + (T₁ : ℂ) * I)).im)
      = ∫ x in c..d, (x - c) * (logDeriv g ((x : ℂ) + (T₁ : ℂ) * I)).im :=
    intervalIntegral.integral_congr fun x hx => by rw [hld _ (hmembot x hx)]
  have e5 : (∫ x in c..d, (x - c) * (logDeriv f ((x : ℂ) + (T₂ : ℂ) * I)).im)
      = ∫ x in c..d, (x - c) * (logDeriv g ((x : ℂ) + (T₂ : ℂ) * I)).im :=
    intervalIntegral.integral_congr fun x hx => by rw [hld _ (hmemtop x hx)]
  rw [e1, e2, e3, e4, e5]

/-- The detector zero mass in `[½,4] × [T₁,T₂]`, bounded by the Littlewood boundary of the
mollified detector on the wider rectangle `[σ₀,d] × [T₁,T₂]`. -/
theorem levinsonGEntire_zeroMass_le_boundary
    {lam : ℂ} (hlam : lam ≠ 0) {Ψ : ℂ → ℂ} (hΨ : AnalyticOnNhd ℂ Ψ Set.univ)
    (hΨne : ∃ z : ℂ, Ψ z ≠ 0)
    {σ₀ d T₁ T₂ : ℝ} (hσ₀ : σ₀ < 1 / 2) (hd : 4 ≤ d) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc σ₀ d,
      levinsonGEntire lam ((x : ℂ) + (T₁ : ℂ) * I) * Ψ ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc σ₀ d,
      levinsonGEntire lam ((x : ℂ) + (T₂ : ℂ) * I) * Ψ ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0)
    (hrightne : ∀ t ∈ uIcc T₁ T₂,
      levinsonGEntire lam ((d : ℂ) + (t : ℂ) * I) * Ψ ((d : ℂ) + (t : ℂ) * I) ≠ 0)
    (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) 4 ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire lam z = 0) :
    2 * Real.pi * ((1 / 2 - σ₀) *
        (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ)))
      ≤ weightedLittlewoodBoundary (fun z => levinsonGEntire lam z * Ψ z) σ₀ d T₁ T₂ := by
  classical
  set F : ℂ → ℂ := fun z => levinsonGEntire lam z * Ψ z with hF
  have hGan : AnalyticOnNhd ℂ (levinsonGEntire lam) Set.univ := analyticOnNhd_levinsonGEntire lam
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz => (hGan z hz).mul (hΨ z hz)
  obtain ⟨zg, hzg⟩ := exists_levinsonGEntire_ne_zero hlam
  obtain ⟨zp, hzp⟩ := hΨne
  have hGorder : ∀ w : ℂ, analyticOrderAt (levinsonGEntire lam) w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hGan ⟨zg, hzg⟩ w
  have hPorder : ∀ w : ℂ, analyticOrderAt Ψ w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hΨ ⟨zp, hzp⟩ w
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    by_cases hex : ∃ z : ℂ, F z ≠ 0
    · exact hex
    exfalso
    have hcon : ∀ z : ℂ, F z = 0 := by
      intro z
      by_contra hz
      exact hex ⟨z, hz⟩
    have htop0 : analyticOrderAt F 0 = ⊤ := by
      have hEq : F = fun _ => (0 : ℂ) := funext hcon
      rw [hEq]
      simpa using (analyticOrderAt_eq_top (f := fun _ : ℂ => (0 : ℂ)) (z₀ := (0 : ℂ))).mpr
        (by filter_upwards with _ using rfl)
    have hmul : analyticOrderAt F 0
        = analyticOrderAt (levinsonGEntire lam) 0 + analyticOrderAt Ψ 0 :=
      analyticOrderAt_mul (hGan 0 (Set.mem_univ _)) (hΨ 0 (Set.mem_univ _))
    rw [hmul] at htop0
    exact (WithTop.add_ne_top.mpr ⟨hGorder 0, hPorder 0⟩) htop0
  have hσ₀d : σ₀ < d := by linarith
  obtain ⟨Z', hZ', hbound⟩ :=
    exists_entire_zeroCount_le_boundary (f := F) (σ := (1 / 2 : ℝ)) hFan hFne
      hσ₀d hT hbot htop hrightne
  have hsub : Z ⊆ Z'.filter (fun w => (1 / 2 : ℝ) ≤ w.re) := by
    intro w hw
    obtain ⟨hwmem, hwzero⟩ := (hZ w).mp hw
    have hre := (Complex.mem_reProdIm.mp hwmem).1
    have him := (Complex.mem_reProdIm.mp hwmem).2
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 4)] at hre
    refine Finset.mem_filter.mpr ⟨?_, hre.1⟩
    refine (hZ' w).mpr ⟨?_, by simp [hF, hwzero]⟩
    refine Complex.mem_reProdIm.mpr ⟨?_, him⟩
    rw [uIcc_of_le hσ₀d.le]
    exact ⟨le_trans hσ₀.le hre.1, le_trans hre.2 hd⟩
  have horder : ∀ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ)
      ≤ ((analyticOrderAt F w).toNat : ℝ) := by
    intro w _
    have hmul : analyticOrderAt F w
        = analyticOrderAt (levinsonGEntire lam) w + analyticOrderAt Ψ w :=
      analyticOrderAt_mul (hGan w (Set.mem_univ _)) (hΨ w (Set.mem_univ _))
    rw [hmul, ENat.toNat_add (hGorder w) (hPorder w)]
    push_cast
    have hnn : (0 : ℝ) ≤ ((analyticOrderAt Ψ w).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hsum : (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ))
      ≤ ∑ w ∈ Z'.filter (fun w => (1 / 2 : ℝ) ≤ w.re), ((analyticOrderAt F w).toNat : ℝ) := by
    refine le_trans (Finset.sum_le_sum horder) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => Nat.cast_nonneg _)
  have hscale : (1 / 2 - σ₀) *
      (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ))
      ≤ (1 / 2 - σ₀) *
      (∑ w ∈ Z'.filter (fun w => (1 / 2 : ℝ) ≤ w.re), ((analyticOrderAt F w).toNat : ℝ)) :=
    mul_le_mul_of_nonneg_left hsum (by linarith)
  have hfinal := mul_le_mul_of_nonneg_left hscale (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  exact le_trans hfinal hbound


/-- **Levinson's window count from the mollified mean square.**  Every step from the mean square of
`(ζ+λζ′)·Ψ` on the Levinson abscissa to a lower bound for the odd-fibre count is unconditional. -/
theorem exists_le_xiOddFiberCount_of_mollified_meanSquare :
    ∃ cw C K : ℝ, 0 < cw ∧ 0 < C ∧ 0 < K ∧
      ∀ lam : ℝ, lam < 0 → |lam| ≤ 1 →
      ∀ (b : ℕ → ℂ) (N : ℕ), 1 ≤ N → b 1 = 1 →
        (∀ n ∈ Finset.Icc 1 N, ‖b n‖ ≤ 1) →
        (∀ n ∈ Finset.Icc 1 N, (starRingEnd ℂ) (b n) = b n) →
      ∀ Mb : ℝ, 1 ≤ Mb →
        (∑ n ∈ Finset.Icc 1 N, ‖b n‖ * ((n : ℝ) ^ (4 : ℝ))) ≤ Mb →
      ∀ σ₀ T₁ T₂ Msq : ℝ, 1 / 4 ≤ σ₀ → σ₀ < 1 / 2 → 20 ≤ T₁ → T₁ < T₂ →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          levinsonG ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
        (∀ x ∈ Set.Icc σ₀ (15 / 2 : ℝ),
          edPoly b (Finset.Icc 1 N) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
        (∫ t in T₁..T₂,
          ‖levinsonMollifiedDetector ((lam : ℝ) : ℂ) b (Finset.Icc 1 N)
            ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤ Msq →
      ∀ n : ℕ,
        ((n : ℝ) + 2) * Real.pi + Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2)
            + cw * Real.log T₁ + cw * Real.log T₂
            + ((T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
                + C + K * (Real.log T₂ + Real.log Mb)) / (1 / 2 - σ₀)
          ≤ gammaHardyTheta T₂ - gammaHardyTheta T₁ →
        n ≤ xiOddFiberCount T₂ := by
  classical
  obtain ⟨cw, hcw, hwin⟩ := exists_levinson_window_edge_bound_unconditional
  obtain ⟨C, K, hC, hK, hbudget⟩ := exists_levinson_mollified_budget_le
  refine ⟨cw, C, K, hcw, hC, hK, ?_⟩
  intro lam hlam0 hlam b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq hσ₀ hσ₀' h20 hT
    hG1 hG2 hP1 hP2 hMsq n hn
  set s : Finset ℕ := Finset.Icc 1 N with hsdef
  have hs : ∀ m ∈ s, 1 ≤ m := fun m hm => (Finset.mem_Icc.mp hm).1
  have h1mem : 1 ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
  have hlamC : ((lam : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_lt hlam0
  have hlamN : ‖((lam : ℝ) : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have hσ₀15 : σ₀ < 15 / 2 := by linarith
  have huIccx : uIcc σ₀ (15 / 2 : ℝ) = Set.Icc σ₀ (15 / 2 : ℝ) := uIcc_of_le hσ₀15.le
  have huIcct : uIcc T₁ T₂ = Set.Icc T₁ T₂ := uIcc_of_le hT.le
  have hwidth : (0 : ℝ) < 1 / 2 - σ₀ := by linarith
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' hEq
    have him := congrArg Complex.im hEq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  set Ψ : ℂ → ℂ := edPoly b s with hΨdef
  set g : ℂ → ℂ := levinsonMollifiedDetector ((lam : ℝ) : ℂ) b s with hgdef
  set F : ℂ → ℂ := fun z => levinsonGEntire ((lam : ℝ) : ℂ) z * Ψ z with hFdef
  have hΨana : AnalyticOnNhd ℂ Ψ Set.univ := analyticOnNhd_edPoly b hs
  have hΨne : ∃ z : ℂ, Ψ z ≠ 0 := by
    refine ⟨((15 : ℝ) : ℂ), ?_⟩
    have hre : (2 : ℝ) ≤ (((15 : ℝ) : ℂ)).re := by simp; norm_num
    have hd := norm_edPoly_sub_one_le_exp b hs h1mem hb1 hbn hre
    have hEsmall : Real.exp (-(Real.log 2) * (((15 : ℝ) : ℂ)).re) ≤ 1 / 16 := by
      rw [exp_neg_log_two_eq]
      have hle : ((2 : ℝ) ^ (4 : ℝ)) ≤ ((2 : ℝ) ^ (((15 : ℝ) : ℂ)).re) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        simp; norm_num
      have h16 : ((2 : ℝ) ^ (4 : ℝ)) = 16 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      rw [h16] at hle
      have hpos : (0 : ℝ) < (2 : ℝ) ^ (((15 : ℝ) : ℂ)).re := Real.rpow_pos_of_pos (by norm_num) _
      rw [inv_le_iff_one_le_mul₀ hpos]
      linarith
    intro h0
    rw [hΨdef] at h0
    rw [h0] at hd
    have hone : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [hone] at hd
    linarith
  -- nonvanishing on the three estimated edges of the Littlewood rectangle
  have hΨright : ∀ t : ℝ, Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t h0
    rw [hΨdef] at h0
    have hre : (2 : ℝ) ≤ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re := by simp; norm_num
    have hd := norm_edPoly_sub_one_le_exp b hs h1mem hb1 hbn hre
    have hEsmall : Real.exp (-(Real.log 2) * ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re)
        ≤ 1 / 16 := by
      rw [exp_neg_log_two_eq]
      have hle : ((2 : ℝ) ^ (4 : ℝ))
          ≤ ((2 : ℝ) ^ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        simp; norm_num
      have h16 : ((2 : ℝ) ^ (4 : ℝ)) = 16 := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      rw [h16] at hle
      have hpos : (0 : ℝ) < (2 : ℝ) ^ ((((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)).re :=
        Real.rpow_pos_of_pos (by norm_num) _
      rw [inv_le_iff_one_le_mul₀ hpos]
      linarith
    rw [h0] at hd
    have hone : ‖(0 : ℂ) - 1‖ = 1 := by simp
    rw [hone] at hd
    linarith
  have hGeright : ∀ t : ℝ,
      levinsonGEntire ((lam : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    refine levinsonGEntire_ne_zero_of_four_le hlamN ?_
    simp; norm_num
  have hGright : ∀ t : ℝ,
      levinsonG ((lam : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t
    refine levinsonG_ne_zero_of_four_le hlamN ?_
    simp; norm_num
  have hFbot : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((lam : ℝ) : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) * Ψ ((x : ℂ) + (T₁ : ℂ) * I)
        ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP1 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₁ h20)]
    exact hG1 x hx
  have hFtop : ∀ x ∈ uIcc σ₀ (15 / 2 : ℝ),
      levinsonGEntire ((lam : ℝ) : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) * Ψ ((x : ℂ) + (T₂ : ℂ) * I)
        ≠ 0 := by
    intro x hx
    rw [huIccx] at hx
    refine mul_ne_zero ?_ (hP2 x hx)
    rw [Ne, levinsonGEntire_eq_zero_iff _ (hne1 x T₂ (by linarith))]
    exact hG2 x hx
  have hFright : ∀ t ∈ uIcc T₁ T₂,
      levinsonGEntire ((lam : ℝ) : ℂ) (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I)
        * Ψ (((15 / 2 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0 :=
    fun t _ => mul_ne_zero (hGeright t) (hΨright t)
  -- the left-edge zero set is finite and not everything
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz =>
    ((analyticOnNhd_levinsonGEntire ((lam : ℝ) : ℂ)) z hz).mul (hΨana z hz)
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    obtain ⟨t, _⟩ : ∃ t : ℝ, t = T₁ := ⟨T₁, rfl⟩
    exact ⟨((15 / 2 : ℝ) : ℂ) + ((T₁ : ℝ) : ℂ) * I,
      mul_ne_zero (hGeright T₁) (hΨright T₁)⟩
  have hrectfin : {z ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) | F z = 0}.Finite := by
    have h := entire_zeros_closedRectangle_finite hFan hFne
      ((σ₀ : ℂ) + (T₁ : ℂ) * I) (((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)
    have hre1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).re = σ₀ := by simp
    have him1 : ((σ₀ : ℂ) + (T₁ : ℂ) * I).im = T₁ := by simp
    have hre2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).re = 15 / 2 := by simp
    have him2 : ((((15 / 2 : ℝ) : ℂ) + (T₂ : ℂ) * I)).im = T₂ := by simp
    rwa [hre1, him1, hre2, him2] at h
  have hmemleft : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      ((σ₀ : ℂ) + (t : ℂ) * I) ∈ (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) := by
    intro t ht
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · have h : ((σ₀ : ℂ) + (t : ℂ) * I).re = σ₀ := by simp
      rw [h]; exact left_mem_uIcc
    · have h : ((σ₀ : ℂ) + (t : ℂ) * I).im = t := by simp
      rw [h]; exact ht
  have hgFzero : ∀ t : ℝ, t ∈ uIcc T₁ T₂ →
      (g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 ↔ F ((σ₀ : ℂ) + (t : ℂ) * I) = 0) := by
    intro t ht
    rw [huIcct] at ht
    have hzne : ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 1 := hne1 σ₀ t (by linarith [ht.1])
    constructor
    · intro h0
      have : F ((σ₀ : ℂ) + (t : ℂ) * I)
          = (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) := by
        simp only [hFdef, hgdef, levinsonMollifiedDetector]
        rw [levinsonGEntire_eq _ hzne]
        ring
      rw [this, h0, mul_zero]
    · intro h0
      have hgauge : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ≠ 0 := sub_ne_zero.mpr hzne
      have heq : (((σ₀ : ℂ) + (t : ℂ) * I) - 1) ^ 2 * g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 := by
        rw [← h0]
        simp only [hFdef, hgdef, levinsonMollifiedDetector]
        rw [levinsonGEntire_eq _ hzne]
        ring
      rcases mul_eq_zero.mp heq with h | h
      · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) hgauge
      · exact h
  have hgfin : {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0}.Finite := by
    have hinj : Set.InjOn (fun t : ℝ => (σ₀ : ℂ) + (t : ℂ) * I)
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} := by
      intro x _ y _ hxy
      simpa using congrArg Complex.im hxy
    refine Set.Finite.of_finite_image (Set.Finite.subset hrectfin ?_) hinj
    rintro z ⟨t, ⟨ht, hz⟩, rfl⟩
    exact ⟨hmemleft t ht, (hgFzero t ht).mp hz⟩
  have hgex : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    by_cases hall : ∃ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) ≠ 0
    · exact hall
    exfalso
    have hcon : ∀ t ∈ Set.Ioo T₁ T₂, g ((σ₀ : ℂ) + (t : ℂ) * I) = 0 := by
      intro t ht
      by_contra h0
      exact hall ⟨t, ht, h0⟩
    have hsubset : Set.Ioo T₁ T₂ ⊆
        {t : ℝ | t ∈ uIcc T₁ T₂ ∧ g ((σ₀ : ℂ) + (t : ℂ) * I) = 0} := by
      intro t ht
      exact ⟨by rw [huIcct]; exact Set.Ioo_subset_Icc_self ht, hcon t ht⟩
    exact (Set.Ioo_infinite hT) (hgfin.subset hsubset)
  -- the budget
  have hbud := hbudget lam hlam b N hN hb1 hbn hbreal Mb hMb1 hmass σ₀ T₁ T₂ Msq
    hσ₀ hσ₀' h20 hT hG1 hG2 hP1 hP2 hgfin hgex hMsq
  -- gauge cancellation
  have hUopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
  have hUsub : (uIcc σ₀ (15 / 2 : ℝ) ×ℂ uIcc T₁ T₂) ⊆ {z : ℂ | z ≠ 1} := by
    intro z hz hEq
    have him := (Complex.mem_reProdIm.mp hz).2
    rw [huIcct] at him
    rw [hEq, Complex.one_im] at him
    linarith [him.1]
  have hcongrF : weightedLittlewoodBoundary F σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_congr hUopen hUsub ?_
    intro z hz
    simp only [hFdef, hgdef, levinsonMollifiedDetector]
    rw [levinsonGEntire_eq _ hz]
    ring
  have hgaugefree : weightedLittlewoodBoundary (fun z => (z - 1) ^ 2 * g z) σ₀ (15 / 2) T₁ T₂
      = weightedLittlewoodBoundary g σ₀ (15 / 2) T₁ T₂ := by
    refine weightedLittlewoodBoundary_poleGauge_mul hσ₀15 hT ?_ ?_ ?_ ?_ ?_ hgfin
    · intro hmem
      have him := (Complex.mem_reProdIm.mp hmem).2
      rw [huIcct, Complex.one_im] at him
      linarith [him.1]
    · intro z hz
      have hzne : z ≠ 1 := hUsub hz
      exact analyticAt_levinsonMollifiedDetector _ b hs hzne
    · intro x hx
      rw [huIccx] at hx
      exact mul_ne_zero (hG1 x hx) (hP1 x hx)
    · intro x hx
      rw [huIccx] at hx
      exact mul_ne_zero (hG2 x hx) (hP2 x hx)
    · intro t _
      exact mul_ne_zero (hGright t) (hΨright t)
  -- the zero-mass bound
  refine hwin lam hlam0 hlam T₁ T₂ h20 hT ?_ ?_ n ?_
  · intro x hx; exact hG1 x (Set.Icc_subset_Icc (by linarith) (by norm_num) hx)
  · intro x hx; exact hG2 x (Set.Icc_subset_Icc (by linarith) (by norm_num) hx)
  intro Z hZ
  have hmassbound := levinsonGEntire_zeroMass_le_boundary (lam := ((lam : ℝ) : ℂ)) hlamC
    hΨana hΨne hσ₀' (by norm_num : (4 : ℝ) ≤ 15 / 2) hT hFbot hFtop hFright Z hZ
  rw [hcongrF, hgaugefree] at hmassbound
  have hchain : 2 * Real.pi *
      (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire ((lam : ℝ) : ℂ)) w).toNat : ℝ))
      ≤ ((T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁))
          + C + K * (Real.log T₂ + Real.log Mb)) / (1 / 2 - σ₀) := by
    rw [le_div_iff₀ hwidth]
    nlinarith [hmassbound, hbud, hwidth]
  linarith [hn, hchain]

end RHTower

end

