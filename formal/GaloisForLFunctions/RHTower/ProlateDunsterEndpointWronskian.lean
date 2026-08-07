import GaloisForLFunctions.RHTower.ProlateDunsterRegularBranch
import GaloisForLFunctions.RHTower.CCMRadialProlateEndpointLayer

open Filter Set Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

theorem lgWeight_tendsto_zero_at_endpoint {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Tendsto (lgWeight s) (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact (lgWeight_pos hs0 hs1 hx).le
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact lgWeight_le hs0 hs1 hx
  · have h : ContinuousAt (fun x : ℝ => x ^ 2 - 1) 1 := by fun_prop
    simpa only [one_pow, sub_self] using h.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)

theorem xiAmplitude_log_phase {s c x : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) (hx : 1 < x) :
    Real.log (c * xiEndpointPhase s x) =
      Real.log c + 2 * Real.log (xiAmplitude s x)
        + Real.log (x ^ 2 - 1) / 2 + Real.log (x ^ 2 - s) / 2 := by
  have hd : 0 < x ^ 2 - 1 := by nlinarith
  have hn : 0 < x ^ 2 - s := by nlinarith
  have hp := xiEndpointPhase_pos hs0 hs1 hx
  have hD : 0 < (x ^ 2 - 1) * (x ^ 2 - s) := mul_pos hd hn
  rw [Real.log_mul hc.ne' hp.ne', xiAmplitude, Real.log_div
    (Real.sqrt_pos.2 hp).ne' (Real.sqrt_pos.2 (Real.sqrt_pos.2 hD)).ne',
    Real.log_sqrt hp.le, Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hD.le,
    Real.log_mul hd.ne' hn.ne']
  ring

theorem sub_one_sq_mul_log_phase_tendsto_zero {s c : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (x ^ 2 - 1) * Real.log (c * xiEndpointPhase s x))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  let l := nhdsWithin (1 : ℝ) (Ioi 1)
  have hd : Tendsto (fun x : ℝ => x ^ 2 - 1) l (nhds 0) := by
    have h : ContinuousAt (fun x : ℝ => x ^ 2 - 1) 1 := by fun_prop
    simpa only [one_pow, sub_self, l] using h.tendsto.mono_left
      (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
  have hdpos : ∀ᶠ x : ℝ in l, x ^ 2 - 1 ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 1 < x at hx
    calc
      0 < (x - 1) * (x + 1) := mul_pos (sub_pos.mpr hx) (by linarith)
      _ = x ^ 2 - 1 := by ring
  have hdwithin : Tendsto (fun x : ℝ => x ^ 2 - 1) l (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hd, hdpos⟩
  have hdlog : Tendsto (fun x : ℝ => (x ^ 2 - 1) * Real.log (x ^ 2 - 1)) l (nhds 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one).comp hdwithin
    apply h.congr'
    filter_upwards with x
    simp only [Function.comp_apply, Real.rpow_one]
    ring
  have hAlog : Tendsto (fun x : ℝ => Real.log (xiAmplitude s x)) l (nhds 0) := by
    have h := (xiAmplitude_tendsto_one_at_endpoint hs0 hs1).log one_ne_zero
    simpa [Real.log_one, l] using h
  have hn : Tendsto (fun x : ℝ => Real.log (x ^ 2 - s)) l (nhds (Real.log (1 - s))) := by
    have hbase : Tendsto (fun x : ℝ => x ^ 2 - s) l (nhds (1 - s)) := by
      have h : ContinuousAt (fun x : ℝ => x ^ 2 - s) 1 := by fun_prop
      simpa only [one_pow, l] using h.tendsto.mono_left
        (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
    exact hbase.log (by linarith)
  have h1 := hd.mul_const (Real.log c)
  have h2 := hd.mul (hAlog.const_mul 2)
  have h3 := hdlog.const_mul (1 / 2)
  have h4 := hd.mul (hn.const_mul (1 / 2))
  have hsum := ((h1.add h2).add h3).add h4
  norm_num only [zero_mul, zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [xiAmplitude_log_phase hs0 hs1 hc hx]
  ring

theorem sub_one_sq_mul_abs_log_phase_tendsto_zero {s c : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (x ^ 2 - 1) * |Real.log (c * xiEndpointPhase s x)|)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have h := (sub_one_sq_mul_log_phase_tendsto_zero hs0 hs1 hc).abs
  simpa only [abs_zero] using h.congr' (by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 1 < x at hx
    have hd : 0 < x ^ 2 - 1 := by nlinarith [sq_nonneg (x - 1)]
    rw [abs_mul, abs_of_pos hd])

theorem tendsto_zero_mul_of_eventually_abs_le
    {l : Filter ℝ} {f g : ℝ → ℝ} {C : ℝ}
    (_hC : 0 ≤ C) (hf : Tendsto f l (nhds 0)) (hg : ∀ᶠ x in l, |g x| ≤ C) :
    Tendsto (fun x => f x * g x) l (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero' (g := fun x => |f x| * C)
  · exact Eventually.of_forall fun x => abs_nonneg (f x * g x)
  · filter_upwards [hg] with x hx
    rw [Function.comp_apply, abs_mul]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · have habs : Tendsto (fun x => |f x|) l (nhds 0) := by
      simpa only [Function.comp_def] using (tendsto_zero_iff_abs_tendsto_zero f).1 hf
    simpa using habs.mul_const C

theorem lgWeight_mul_comparisonSolDeriv_tendsto_zero
    {s : ℝ} {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hRc : ContinuousAt R 1) (hDRc : ContinuousAt DR 1)
    (hR : ∀ x : ℝ, 1 < x → HasDerivAt R (DR x) x) :
    Tendsto (fun x : ℝ => lgWeight s x *
        comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  obtain ⟨C, hC, hDU⟩ := eventually_bounded_comparisonSolDeriv hs0 hs1 hRc hDRc hR
  exact tendsto_zero_mul_of_eventually_abs_le hC
    (lgWeight_tendsto_zero_at_endpoint hs0 hs1) hDU

theorem lgWeight_mul_lgBesselModelDeriv_tendsto_zero
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    Tendsto (fun x : ℝ => lgWeight s x * lgBesselModelDeriv s c x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have hu : Tendsto (fun x : ℝ => c * xiEndpointPhase s x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul (xiEndpointPhase_tendsto_zero_at_endpoint hs0 hs1)
  have hdu : Tendsto (fun x : ℝ => besselJ0Deriv (c * xiEndpointPhase s x))
      (nhdsWithin 1 (Ioi 1)) (nhds (besselJ0Deriv 0)) :=
    (hasDerivAt_besselJ0Deriv 0).continuousAt.tendsto.comp hu
  have hprod := hu.mul hdu
  norm_num only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hsp := xiSpeed_pos hs1 hx
  rw [lgWeight, lgBesselModelDeriv]
  field_simp [hsp.ne']

theorem lgWeight_mul_lgBesselModel2_tendsto_zero
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    Tendsto (fun x : ℝ => lgWeight s x * lgBesselModel2 s c x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  apply squeeze_zero' (g := fun x => (x ^ 2 - 1) *
    (2 + |Real.log (c * xiEndpointPhase s x)|))
  · exact Eventually.of_forall fun x => abs_nonneg (lgWeight s x * lgBesselModel2 s c x)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hm := lgWeight_pos hs0 hs1 hx
    have hmle := lgWeight_le hs0 hs1 hx
    have hK := (abs_lgBesselModel_le_log_envelope s c x).2
    rw [Function.comp_apply, abs_mul, abs_of_pos hm]
    exact mul_le_mul hmle hK (abs_nonneg _) (by
      have hd : 0 < x ^ 2 - 1 := by nlinarith [sq_nonneg (x - 1)]
      exact hd.le)
  · have hd : Tendsto (fun x : ℝ => x ^ 2 - 1)
        (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
      have h : ContinuousAt (fun x : ℝ => x ^ 2 - 1) 1 := by fun_prop
      simpa only [one_pow, sub_self] using h.tendsto.mono_left
        (show nhdsWithin (1 : ℝ) (Ioi 1) ≤ nhds 1 from inf_le_left)
    have h := (hd.const_mul 2).add
      (sub_one_sq_mul_abs_log_phase_tendsto_zero hs0 hs1 hc)
    norm_num only [mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards with x
    ring

theorem lgBesselWronskian_tendsto_zero_at_endpoint
    {s c : ℝ} {U DU : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hU : Tendsto U (nhdsWithin 1 (Ioi 1)) (nhds 1))
    (hmDU : Tendsto (fun x : ℝ => lgWeight s x * DU x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0)) :
    Tendsto (fun x : ℝ => lgWeight s x *
        (U x * lgBesselModelDeriv s c x - DU x * lgBesselModel s c x))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have hJ := lgBesselModel_tendsto_one_at_endpoint (s := s) (c := c) hs0 hs1
  have hJd := lgWeight_mul_lgBesselModelDeriv_tendsto_zero (s := s) (c := c) hs0 hs1
  have h := (hU.mul hJd).sub (hmDU.mul hJ)
  norm_num only [one_mul, zero_mul, sub_self] at h
  apply h.congr'
  filter_upwards with x
  ring

theorem phase_mul_besselK_tendsto_zero_at_endpoint
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    Tendsto (fun x : ℝ => (c * xiEndpointPhase s x) *
        besselK (c * xiEndpointPhase s x))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  let l := nhdsWithin (1 : ℝ) (Ioi 1)
  let u : ℝ → ℝ := fun x => c * xiEndpointPhase s x
  have hu : Tendsto u l (nhds 0) := by
    dsimp [u, l]
    simpa using tendsto_const_nhds.mul (xiEndpointPhase_tendsto_zero_at_endpoint hs0 hs1)
  have hupos : ∀ᶠ x in l, u x ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_pos hc (xiEndpointPhase_pos hs0 hs1 hx)
  have huwithin : Tendsto u l (nhdsWithin 0 (Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hu, hupos⟩
  have hulog : Tendsto (fun x => u x * Real.log (u x)) l (nhds 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) zero_lt_one).comp huwithin
    apply h.congr'
    filter_upwards with x
    simp only [Function.comp_apply, Real.rpow_one]
    ring
  have hJ : Tendsto (fun x => besselJ0 (u x)) l (nhds 1) := by
    change Tendsto (besselJ0 ∘ u) l (nhds 1)
    simpa only [besselJ0_zero] using continuous_besselJ0.continuousAt.tendsto.comp hu
  have hM : Tendsto (fun x => besselM (u x)) l (nhds (besselM 0)) :=
    (hasDerivAt_besselM 0).continuousAt.tendsto.comp hu
  have h := ((hulog.const_mul (Real.pi / 4)).mul hJ).add (hu.mul hM)
  have h' : Tendsto (fun x => u x * besselK (u x)) l (nhds 0) := by
    convert h using 1
    · funext x
      rw [besselK]
      ring
    · ring
  simpa only [u, l] using h'

theorem lgWeight_modelDeriv_mul_model2_tendsto_zero
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    Tendsto (fun x : ℝ =>
        (lgWeight s x * lgBesselModelDeriv s c x) * lgBesselModel2 s c x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have hu : Tendsto (fun x : ℝ => c * xiEndpointPhase s x)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    simpa using tendsto_const_nhds.mul (xiEndpointPhase_tendsto_zero_at_endpoint hs0 hs1)
  have hdu : Tendsto (fun x : ℝ => besselJ0Deriv (c * xiEndpointPhase s x))
      (nhdsWithin 1 (Ioi 1)) (nhds (besselJ0Deriv 0)) :=
    (hasDerivAt_besselJ0Deriv 0).continuousAt.tendsto.comp hu
  have h := hdu.mul (phase_mul_besselK_tendsto_zero_at_endpoint hs0 hs1 hc)
  norm_num only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hsp := xiSpeed_pos hs1 hx
  rw [lgWeight, lgBesselModelDeriv, lgBesselModel2]
  field_simp [hsp.ne']

theorem lgWeight_mul_lgBesselModel2Deriv_tendsto_pi_div_four
    {s c : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c) :
    Tendsto (fun x : ℝ => lgWeight s x * lgBesselModel2Deriv s c x)
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.pi / 4)) := by
  let l := nhdsWithin (1 : ℝ) (Ioi 1)
  have hJ := lgBesselModel_tendsto_one_at_endpoint (s := s) (c := c) hs0 hs1
  have hconst : Tendsto (fun _ : ℝ => Real.pi / 4) l (nhds (Real.pi / 4)) :=
    tendsto_const_nhds
  have hnum := hconst.add
    (lgWeight_modelDeriv_mul_model2_tendsto_zero hs0 hs1 hc)
  norm_num only [add_zero] at hnum
  have hdiv := hnum.div hJ (by norm_num)
  norm_num only [div_one] at hdiv
  apply hdiv.congr'
  have hJpos : ∀ᶠ x : ℝ in l, lgBesselModel s c x ∈ Ioo (1 / 2 : ℝ) 2 :=
    hJ.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hJpos] with x hx hJx
  have hJne : lgBesselModel s c x ≠ 0 := by linarith [hJx.1]
  change (Real.pi / 4 + lgWeight s x * lgBesselModelDeriv s c x *
      lgBesselModel2 s c x) / lgBesselModel s c x =
    lgWeight s x * lgBesselModel2Deriv s c x
  rw [div_eq_iff hJne]
  have hmodel := lgWronskian_model_eq (s := s) (c := c) hs0 hs1 hx hc
  rw [besselWronskian_eq_pi_div_four (mul_pos hc (xiEndpointPhase_pos hs0 hs1 hx))] at hmodel
  linarith

theorem lgBessel2Wronskian_tendsto_pi_div_four_at_endpoint
    {s c : ℝ} {U DU : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hU : Tendsto U (nhdsWithin 1 (Ioi 1)) (nhds 1))
    (hDUb : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in nhdsWithin 1 (Ioi 1), |DU x| ≤ C) :
    Tendsto (fun x : ℝ => lgWeight s x *
        (U x * lgBesselModel2Deriv s c x - DU x * lgBesselModel2 s c x))
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.pi / 4)) := by
  obtain ⟨C, hC, hDU⟩ := hDUb
  have hmDUK := tendsto_zero_mul_of_eventually_abs_le hC
    (lgWeight_mul_lgBesselModel2_tendsto_zero hs0 hs1 hc) hDU
  have hmKd := lgWeight_mul_lgBesselModel2Deriv_tendsto_pi_div_four hs0 hs1 hc
  have h := (hU.mul hmKd).sub hmDUK
  norm_num only [one_mul, sub_zero] at h
  apply h.congr'
  filter_upwards with x
  ring

/-- Endpoint-normalized radial profiles have zero weighted Wronskian against the regular
Bessel branch at the singular endpoint. -/
theorem prolateComparison_lgBesselWronskian_tendsto_zero
    {s c : ℝ} {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hRc : ContinuousAt R 1) (hDRc : ContinuousAt DR 1) (hR1 : R 1 = 1)
    (hR : ∀ x : ℝ, 1 < x → HasDerivAt R (DR x) x) :
    Tendsto (fun x : ℝ => lgWeight s x *
        (comparisonSol (prolateNormalFormSol R) s x * lgBesselModelDeriv s c x -
          comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x *
            lgBesselModel s c x))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  exact lgBesselWronskian_tendsto_zero_at_endpoint hs0 hs1
    (comparisonSol_prolateNormalForm_tendsto_one_at_endpoint hs0 hs1 hRc hR1)
    (lgWeight_mul_comparisonSolDeriv_tendsto_zero hs0 hs1 hRc hDRc hR)

/-- Endpoint-normalized radial profiles have weighted Wronskian `pi/4` against the
logarithmic Bessel branch at the singular endpoint. -/
theorem prolateComparison_lgBessel2Wronskian_tendsto_pi_div_four
    {s c : ℝ} {R DR : ℝ → ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hc : 0 < c)
    (hRc : ContinuousAt R 1) (hDRc : ContinuousAt DR 1) (hR1 : R 1 = 1)
    (hR : ∀ x : ℝ, 1 < x → HasDerivAt R (DR x) x) :
    Tendsto (fun x : ℝ => lgWeight s x *
        (comparisonSol (prolateNormalFormSol R) s x * lgBesselModel2Deriv s c x -
          comparisonSolDeriv (prolateNormalFormSol R) (prolateNormalFormSolDeriv R DR) s x *
            lgBesselModel2 s c x))
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.pi / 4)) := by
  apply lgBessel2Wronskian_tendsto_pi_div_four_at_endpoint hs0 hs1 hc
    (comparisonSol_prolateNormalForm_tendsto_one_at_endpoint hs0 hs1 hRc hR1)
  exact eventually_bounded_comparisonSolDeriv hs0 hs1 hRc hDRc hR

end GaloisForLFunctions.RHTower
