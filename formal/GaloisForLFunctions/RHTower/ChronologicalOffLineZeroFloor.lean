import GaloisForLFunctions.RHTower.ChronologicalHarmonicCharge
import GaloisForLFunctions.RHTower.ChronologicalZeroChargeTailBounds
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Off-line zeros give the chronological heat error a cutoff-independent floor

For a finite real row `a` the chronological heat error
`r(t) = e^{-t} + Σ_{k ≤ N} a_k (1/(kt) - 1/(e^{kt} - 1))` has Mellin transform `Γ(s)` at every
zeta zero `s` of the open strip (`chronologicalHeatError_mellin_at_zero`).  At a critical zero the
resulting floor decays like `1/√(log N)` (`chronologicalHeatError_logarithmic_floor`).

At an off-line zero `1/2 < Re s < 1` the weight `t^{Re s - 1}` is square integrable at `0`, so the
whole small-time part is paid by the `L²` norm itself, and the large-time part is paid by the
uniform exponential Bose bound and the `L²` control of the harmonic charge.  No coefficient-size
growth in `N` enters.  Hence for every coefficient box `[-C, C]` an off-line zero forces a positive
floor `η(s, C)` valid for **every** cutoff `N` and every row in the box.

Consequently, if bounded rows make `‖r_N‖_{L²(0,∞)}` arbitrarily small, then RH holds.  With the
corpus equivalence `tendsto_L2Norm_iff_logWindow_of_zeroCharge`, the CTF small-time energy
`N⁻¹ ∫_0^{log N} r_N(u/N)² du → 0` of Möbius-prefix rows implies RH: this is the source-to-RH
handoff of the chronological-tail route.
-/

open MeasureTheory Set Filter Complex
open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- Large-time pointwise bound: charge tail plus the uniform Bose envelope. -/
theorem abs_chronologicalHeatError_le_charge_add_exp (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) {t : ℝ} (ht : 1 ≤ t) :
    |chronologicalHeatError a N t| ≤
      |chronologicalHarmonicCharge a N| / t + (1 + 4 * C) * Real.exp (-t) := by
  have ht0 : 0 < t := by linarith
  rw [chronologicalHeatError_charge_decomposition a N ht0]
  have hB := chronologicalBoseSum_uniform_bound a N C hC ha ht
  have hc : |chronologicalHarmonicCharge a N / t| = |chronologicalHarmonicCharge a N| / t := by
    rw [abs_div, abs_of_pos ht0]
  have he : |Real.exp (-t)| = Real.exp (-t) := abs_of_pos (Real.exp_pos _)
  calc
    _ ≤ |chronologicalHarmonicCharge a N / t| + |Real.exp (-t)| +
        |chronologicalBoseSum a N t| := by
      have h1 := abs_sub (chronologicalHarmonicCharge a N / t + Real.exp (-t))
        (chronologicalBoseSum a N t)
      have h2 := abs_add_le (chronologicalHarmonicCharge a N / t) (Real.exp (-t))
      linarith
    _ ≤ _ := by rw [hc, he]; nlinarith

/-- Hölder on `(0, U]` against the square-integrable off-line weight. -/
theorem integral_abs_mul_rpow_le_of_offLine {f : ℝ → ℝ}
    (hf : MemLp f 2 chronologicalPositiveVolume) {σ U : ℝ} (hσ : 1 / 2 < σ) (hU : 0 < U) :
    (∫ t in Ioc (0 : ℝ) U, |f t| * t ^ (σ - 1)) ≤
      chronologicalL2Norm f * Real.sqrt (U ^ (2 * σ - 1) / (2 * σ - 1)) := by
  have hsub : Ioc (0 : ℝ) U ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hmeasure : volume.restrict (Ioc (0 : ℝ) U) ≤ chronologicalPositiveVolume :=
    Measure.restrict_mono hsub le_rfl
  have hf' := MemLp.mono_measure hmeasure hf
  have hgc : ContinuousOn (fun t : ℝ => t ^ (σ - 1)) (Ioc (0 : ℝ) U) :=
    fun t ht => (Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')).continuousWithinAt
  have hgm := hgc.aestronglyMeasurable (μ := volume) measurableSet_Ioc
  have hsq : ∀ t ∈ Ioc (0 : ℝ) U, (t ^ (σ - 1)) ^ (2 : ℕ) = t ^ (2 * σ - 2) := by
    intro t ht
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.1.le]
    congr 1
    push_cast
    ring
  have hrpow : IntegrableOn (fun t : ℝ => t ^ (2 * σ - 2)) (Ioc (0 : ℝ) U) := by
    have hi := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := U)
      (by linarith : (-1 : ℝ) < 2 * σ - 2)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hU.le).mp hi
  have hgi : IntegrableOn (fun t : ℝ => (t ^ (σ - 1)) ^ (2 : ℕ)) (Ioc (0 : ℝ) U) :=
    hrpow.congr_fun (fun t ht => (hsq t ht).symm) measurableSet_Ioc
  have hg : MemLp (fun t : ℝ => t ^ (σ - 1)) 2 (volume.restrict (Ioc (0 : ℝ) U)) :=
    (memLp_two_iff_integrable_sq hgm).mpr hgi
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf') (by simpa using hg)
  have hpos : ∀ t ∈ Ioc (0 : ℝ) U, 0 ≤ t ^ (σ - 1) := fun t ht => Real.rpow_nonneg ht.1.le _
  have hcs' : (∫ t in Ioc (0 : ℝ) U, |f t| * t ^ (σ - 1)) ≤
      Real.sqrt (∫ t in Ioc (0 : ℝ) U, f t ^ 2) *
        Real.sqrt (∫ t in Ioc (0 : ℝ) U, (t ^ (σ - 1)) ^ (2 : ℕ)) := by
    have hL : (∫ t in Ioc (0 : ℝ) U, |f t| * t ^ (σ - 1)) =
        ∫ t in Ioc (0 : ℝ) U, ‖f t‖ * ‖t ^ (σ - 1)‖ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp only [Real.norm_eq_abs, abs_of_nonneg (hpos t ht)]
    have hA : (∫ t in Ioc (0 : ℝ) U, ‖f t‖ ^ (2 : ℝ)) = ∫ t in Ioc (0 : ℝ) U, f t ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    have hB : (∫ t in Ioc (0 : ℝ) U, ‖t ^ (σ - 1)‖ ^ (2 : ℝ)) =
        ∫ t in Ioc (0 : ℝ) U, (t ^ (σ - 1)) ^ (2 : ℕ) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos t ht), Real.rpow_two]
    rw [hL]
    rw [hA, hB] at hcs
    simpa only [Real.sqrt_eq_rpow] using hcs
  have hval : (∫ t in Ioc (0 : ℝ) U, (t ^ (σ - 1)) ^ (2 : ℕ)) = U ^ (2 * σ - 1) / (2 * σ - 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hsq, ← intervalIntegral.integral_of_le hU.le,
      integral_rpow (Or.inl (by linarith : (-1 : ℝ) < 2 * σ - 2))]
    have he : 2 * σ - 2 + 1 = 2 * σ - 1 := by ring
    rw [he, Real.zero_rpow (by linarith : 2 * σ - 1 ≠ 0), sub_zero]
  rw [hval] at hcs'
  have hle : (∫ t in Ioc (0 : ℝ) U, f t ^ 2) ≤ ∫ t in Ioi (0 : ℝ), f t ^ 2 :=
    integral_mono_measure hmeasure (Eventually.of_forall (fun t => sq_nonneg _)) hf.integrable_sq
  rw [chronologicalL2Norm_eq_sqrt hf.1]
  exact hcs'.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _))

/-- **Off-line three-term bound.**  At a zeta zero with `1/2 < Re s < 1`, every row bounded by
`C` satisfies, for every `U ≥ 1`,
`‖Γ(s)‖ ≤ ‖r‖ √(U^{2σ-1}/(2σ-1)) + |charge| U^{σ-1}/(1-σ) + (1+4C) e^{-U}`. -/
theorem norm_Gamma_le_chronological_offLine (a : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (ha : ∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C)
    {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1) (hz : riemannZeta s = 0)
    {U : ℝ} (hU : 1 ≤ U) :
    ‖Complex.Gamma s‖ ≤
      chronologicalL2Norm (chronologicalHeatError a N) *
          Real.sqrt (U ^ (2 * s.re - 1) / (2 * s.re - 1)) +
        |chronologicalHarmonicCharge a N| * (U ^ (s.re - 1) / (1 - s.re)) +
        (1 + 4 * C) * Real.exp (-U) := by
  set σ := s.re with hσdef
  set r := chronologicalHeatError a N with hr
  have hU0 : 0 < U := by linarith
  have hstrip : s ∈ fusionMellinStrip := ⟨by linarith, hs2⟩
  have hm := chronologicalHeatError_mellinConvergent a N hstrip
  have hnormeq : ∀ t ∈ Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) • (r t : ℂ)‖ = |r t| * t ^ (σ - 1) := by
    intro t ht
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
      Real.norm_eq_abs]
    simp only [Complex.sub_re, Complex.one_re, hσdef]
    ring
  have hnorm : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) • (r t : ℂ)‖) (Ioi 0) := hm.norm
  have hw : IntegrableOn (fun t => |r t| * t ^ (σ - 1)) (Ioi 0) :=
    hnorm.congr_fun hnormeq measurableSet_Ioi
  have hg : ‖Complex.Gamma s‖ ≤ ∫ t in Ioi (0 : ℝ), |r t| * t ^ (σ - 1) := by
    rw [← chronologicalHeatError_mellin_at_zero a N hstrip hz]
    unfold mellin
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) • (r t : ℂ)‖ :=
        norm_integral_le_integral_norm _
      _ = _ := setIntegral_congr_fun measurableSet_Ioi hnormeq
  have hwU := hw.mono_set (Ioi_subset_Ioi hU0.le)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hw hwU
  rw [intervalIntegral.integral_of_le hU0.le] at hsplit
  have hlow := integral_abs_mul_rpow_le_of_offLine (chronologicalHeatError_memLp a N) hs1 hU0
  -- the large-time part
  set c := |chronologicalHarmonicCharge a N| with hc
  have hc0 : 0 ≤ c := abs_nonneg _
  have hmaj : ∀ t ∈ Ioi U, |r t| * t ^ (σ - 1) ≤
      c * t ^ (σ - 2) + (1 + 4 * C) * Real.exp (-t) := by
    intro t ht
    have ht1 : 1 ≤ t := hU.trans (le_of_lt ht)
    have ht0 : 0 < t := by linarith
    have hpt := abs_chronologicalHeatError_le_charge_add_exp a N C hC ha ht1
    have hpow1 : t ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by linarith)
    have hpow0 : 0 ≤ t ^ (σ - 1) := Real.rpow_nonneg ht0.le _
    have hsplitpow : t ^ (σ - 1) / t = t ^ (σ - 2) := by
      rw [show σ - 2 = (σ - 1) - 1 by ring, Real.rpow_sub_one ht0.ne' (σ - 1)]
    calc
      _ ≤ (c / t + (1 + 4 * C) * Real.exp (-t)) * t ^ (σ - 1) :=
        mul_le_mul_of_nonneg_right hpt hpow0
      _ = c * (t ^ (σ - 1) / t) + (1 + 4 * C) * Real.exp (-t) * t ^ (σ - 1) := by ring
      _ ≤ c * (t ^ (σ - 1) / t) + (1 + 4 * C) * Real.exp (-t) * 1 := by
        have : 0 ≤ (1 + 4 * C) * Real.exp (-t) := by positivity
        nlinarith
      _ = _ := by rw [hsplitpow, mul_one]
  have hrp : IntegrableOn (fun t : ℝ => t ^ (σ - 2)) (Ioi U) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hU0
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi U) := by
    have := (exp_neg_integrableOn_Ioi U (by norm_num : (0 : ℝ) < 1))
    simpa only [neg_mul, one_mul] using this
  have hhigh : (∫ t in Ioi U, |r t| * t ^ (σ - 1)) ≤
      c * (U ^ (σ - 1) / (1 - σ)) + (1 + 4 * C) * Real.exp (-U) := by
    calc
      _ ≤ ∫ t in Ioi U, (c * t ^ (σ - 2) + (1 + 4 * C) * Real.exp (-t)) :=
        setIntegral_mono_on hwU ((hrp.const_mul c).add (hexp.const_mul (1 + 4 * C)))
          measurableSet_Ioi hmaj
      _ = c * (∫ t in Ioi U, t ^ (σ - 2)) + (1 + 4 * C) * ∫ t in Ioi U, Real.exp (-t) := by
        rw [integral_add (hrp.const_mul c) (hexp.const_mul (1 + 4 * C)), integral_const_mul,
          integral_const_mul]
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hU0, integral_exp_neg_Ioi]
        have he : σ - 2 + 1 = σ - 1 := by ring
        rw [he]
        have hden : -U ^ (σ - 1) / (σ - 1) = U ^ (σ - 1) / (1 - σ) := by
          rw [neg_div, ← div_neg, neg_sub]
        rw [hden]
  linarith

/-- **Cutoff-independent off-line floor.**  An off-line zeta zero in `1/2 < Re s < 1` gives, for
every coefficient box `[-C, C]`, one positive constant below which no chronological heat error can
go, whatever the cutoff `N` and the row. -/
theorem chronologicalL2Norm_offLine_floor {s : ℂ} (hs1 : 1 / 2 < s.re) (hs2 : s.re < 1)
    (hz : riemannZeta s = 0) (C : ℝ) (hC : 0 ≤ C) :
    ∃ η : ℝ, 0 < η ∧ ∀ N : ℕ, ∀ a : ℕ → ℝ, (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) →
      η ≤ chronologicalL2Norm (chronologicalHeatError a N) := by
  set σ := s.re with hσdef
  set G := ‖Complex.Gamma s‖ with hGdef
  have hG : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by linarith))
  have h1σ : 0 < 1 - σ := by linarith
  have h2σ : 0 < 2 * σ - 1 := by linarith
  -- choose `U` killing the two exponential tails
  have hlim : Tendsto (fun U : ℝ => (U + 1) * Real.exp (-U)) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
    have := h1.add h0
    simp only [pow_one, pow_zero, one_mul, add_zero] at this
    refine this.congr fun U => ?_
    ring
  have hδ : 0 < G * (1 - σ) / (8 * (1 + 4 * C)) := by positivity
  obtain ⟨U, hU1, hUsmall⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (hlim.eventually (gt_mem_nhds hδ))).exists
  have hU0 : 0 < U := by linarith
  have hexpU : Real.exp (-U) ≤ (U + 1) * Real.exp (-U) := by
    have := Real.exp_pos (-U)
    nlinarith
  have hpowU : U ^ (σ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hU1 (by linarith)
  have hpowU0 : 0 ≤ U ^ (σ - 1) := Real.rpow_nonneg hU0.le _
  set K := Real.sqrt (U ^ (2 * σ - 1) / (2 * σ - 1)) with hK
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  set η := G * (1 - σ) / (8 * (K + 1) * (U + 2)) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨η, hη0, fun N a ha => ?_⟩
  by_contra hlt
  push Not at hlt
  set E := chronologicalL2Norm (chronologicalHeatError a N) with hE
  have hE0 : 0 ≤ E := chronologicalL2Norm_nonneg _
  have hmain := norm_Gamma_le_chronological_offLine a N C hC ha hs1 hs2 hz hU1
  have hcharge := chronologicalHarmonicCharge_L2_bound a N C hC ha hU1
  rw [← hσdef] at hmain
  change G ≤ E * K + |chronologicalHarmonicCharge a N| * (U ^ (σ - 1) / (1 - σ)) +
    (1 + 4 * C) * Real.exp (-U) at hmain
  change |chronologicalHarmonicCharge a N| ≤ (U + 1) * (E + (1 + 4 * C) * Real.exp (-U)) at hcharge
  -- each of the three pieces is at most a quarter of `G`
  have hA : E * K ≤ G / 8 := by
    have h1 : E * K ≤ η * K := mul_le_mul_of_nonneg_right hlt.le hK0
    have h2 : η * K ≤ G / 8 := by
      have h3 : (1 - σ) * K ≤ (K + 1) * (U + 2) := by nlinarith
      have hpos : 0 < 8 * (K + 1) * (U + 2) := by positivity
      calc η * K = G * ((1 - σ) * K) / (8 * (K + 1) * (U + 2)) := by rw [hη]; ring
        _ ≤ G * ((K + 1) * (U + 2)) / (8 * (K + 1) * (U + 2)) := by gcongr
        _ = G / 8 := by field_simp
    linarith
  have hfrac : U ^ (σ - 1) / (1 - σ) ≤ 1 / (1 - σ) :=
    div_le_div_of_nonneg_right hpowU h1σ.le
  have hB : |chronologicalHarmonicCharge a N| * (U ^ (σ - 1) / (1 - σ)) ≤ 3 * G / 8 := by
    have hfrac0 : 0 ≤ U ^ (σ - 1) / (1 - σ) := div_nonneg hpowU0 h1σ.le
    have hstep : |chronologicalHarmonicCharge a N| * (U ^ (σ - 1) / (1 - σ)) ≤
        ((U + 1) * E + (U + 1) * (1 + 4 * C) * Real.exp (-U)) * (1 / (1 - σ)) := by
      calc
        _ ≤ ((U + 1) * (E + (1 + 4 * C) * Real.exp (-U))) * (U ^ (σ - 1) / (1 - σ)) :=
          mul_le_mul_of_nonneg_right hcharge hfrac0
        _ ≤ ((U + 1) * (E + (1 + 4 * C) * Real.exp (-U))) * (1 / (1 - σ)) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
        _ = _ := by ring
    have hE1 : (U + 1) * E * (1 / (1 - σ)) ≤ G / 8 := by
      have h1 : (U + 1) * E ≤ (U + 1) * η := mul_le_mul_of_nonneg_left hlt.le (by linarith)
      have h2 : (U + 1) * η ≤ G * (1 - σ) / 8 := by
        have h3 : U + 1 ≤ (K + 1) * (U + 2) := by nlinarith
        have hpos : 0 < 8 * (K + 1) * (U + 2) := by positivity
        calc (U + 1) * η = G * (1 - σ) * (U + 1) / (8 * (K + 1) * (U + 2)) := by rw [hη]; ring
          _ ≤ G * (1 - σ) * ((K + 1) * (U + 2)) / (8 * (K + 1) * (U + 2)) := by gcongr
          _ = G * (1 - σ) / 8 := by field_simp
      have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity : 0 ≤ 1 / (1 - σ))
      have h4 : G * (1 - σ) / 8 * (1 / (1 - σ)) = G / 8 := by field_simp
      linarith
    have hT1 : (U + 1) * (1 + 4 * C) * Real.exp (-U) * (1 / (1 - σ)) ≤ G / 8 := by
      have h1 : (U + 1) * Real.exp (-U) < G * (1 - σ) / (8 * (1 + 4 * C)) := hUsmall
      have h2 : (U + 1) * (1 + 4 * C) * Real.exp (-U) ≤ G * (1 - σ) / 8 := by
        have hp : 0 < 1 + 4 * C := by linarith
        have := mul_le_mul_of_nonneg_left h1.le hp.le
        have he : (1 + 4 * C) * (G * (1 - σ) / (8 * (1 + 4 * C))) = G * (1 - σ) / 8 := by
          field_simp
        nlinarith
      have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : 0 ≤ 1 / (1 - σ))
      have h4 : G * (1 - σ) / 8 * (1 / (1 - σ)) = G / 8 := by field_simp
      linarith
    have hsum : ((U + 1) * E + (U + 1) * (1 + 4 * C) * Real.exp (-U)) * (1 / (1 - σ)) =
        (U + 1) * E * (1 / (1 - σ)) + (U + 1) * (1 + 4 * C) * Real.exp (-U) * (1 / (1 - σ)) := by
      ring
    linarith
  have hC' : (1 + 4 * C) * Real.exp (-U) ≤ G / 8 := by
    have h1 : (U + 1) * Real.exp (-U) < G * (1 - σ) / (8 * (1 + 4 * C)) := hUsmall
    have hp : 0 < 1 + 4 * C := by linarith
    have h2 : (1 + 4 * C) * Real.exp (-U) ≤ (1 + 4 * C) * ((U + 1) * Real.exp (-U)) :=
      mul_le_mul_of_nonneg_left hexpU hp.le
    have h3 := mul_le_mul_of_nonneg_left h1.le hp.le
    have he : (1 + 4 * C) * (G * (1 - σ) / (8 * (1 + 4 * C))) = G * (1 - σ) / 8 := by
      field_simp
    have h4 : G * (1 - σ) / 8 ≤ G / 8 := by nlinarith
    linarith
  linarith

/-- **Chronological Nyman–Beurling receiver.**  If rows bounded by one constant make the
chronological heat error arbitrarily small in `L²(0,∞)`, then RH holds. -/
theorem riemannHypothesis_of_forall_exists_chronologicalL2Norm_lt (C : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ a : ℕ → ℝ,
      (∀ k ∈ Finset.Ioc 0 N, |a k| ≤ C) ∧
        chronologicalL2Norm (chronologicalHeatError a N) < ε) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro s hs hxi
  have hs1 : 1 / 2 < s.re := hs
  have hsne : s ≠ 1 := by
    rintro rfl
    rw [xi_one] at hxi
    norm_num at hxi
  have hz : riemannZeta s = 0 := (xi_eq_zero_iff (by linarith) hsne).mp hxi
  by_cases hs2 : s.re < 1
  · obtain ⟨η, hη0, hfloor⟩ := chronologicalL2Norm_offLine_floor hs1 hs2 hz C hC
    obtain ⟨N, a, ha, hlt⟩ := hsmall η hη0
    exact absurd (hfloor N a ha) (not_le.mpr hlt)
  · exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hs2) hz

/-- Sequential form of the receiver. -/
theorem riemannHypothesis_of_tendsto_chronologicalL2Norm {a : ℕ → ℕ → ℝ} (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ᶠ N : ℕ in atTop, ∀ k ∈ Finset.Ioc 0 N, |a N k| ≤ C)
    (hlim : Tendsto (fun N : ℕ => chronologicalL2Norm (chronologicalHeatError (a N) N))
      atTop (𝓝 0)) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_exists_chronologicalL2Norm_lt C hC fun ε hε => ?_
  obtain ⟨N, hbound, hN⟩ := (ha.and (hlim.eventually (gt_mem_nhds hε))).exists
  exact ⟨N, a N, hbound, hN⟩

open scoped ArithmeticFunction.Moebius in
/-- **CTF handoff.**  For eventually zero-charge, unit-bounded rows with the exact half-length
Möbius prefix, decay of the small-time energy `N⁻¹ ∫_0^{log N} r_N(u/N)² du` implies RH. -/
theorem riemannHypothesis_of_tendsto_chronologicalLogWindow {a : ℕ → ℕ → ℝ}
    (hrow : ∀ᶠ N : ℕ in atTop, (∀ k : ℕ, 1 ≤ k → k ≤ N / 2 → a N k = μ k) ∧
      (∀ k ∈ Finset.Ioc 0 N, |a N k| ≤ 1) ∧ chronologicalHarmonicCharge (a N) N = 0)
    (hwin : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
        ∫ u in (0 : ℝ)..Real.log N, chronologicalHeatError (a N) N (u / N) ^ 2)
      atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_tendsto_chronologicalL2Norm 1 zero_le_one
    (hrow.mono fun _ h => h.2.1) ((tendsto_L2Norm_iff_logWindow_of_zeroCharge hrow).mpr hwin)

end RHTower
