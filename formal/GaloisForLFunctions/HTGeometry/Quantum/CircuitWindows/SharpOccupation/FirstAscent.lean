import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Affordable time on the ascent to a first robust crossing -/
open Filter Set MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

private theorem measurable_visits {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε : ℝ) :
    MeasurableSet (visitSet H s ε) := by
  have he : visitSet H s ε = {t | orbitCircuitDistance H s t ≤ ε} :=
    Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist _ _ _
  rw [he]
  exact (isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const).measurableSet

/-- Inversion identifies the negative and positive halves of the affordable times. -/
private theorem double_prefix {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε T : ℝ) :
    2*volume.real (visitSet H s ε ∩ Icc 0 T) ≤ volume.real (visitSet H s ε ∩ Icc (-T) T) := by
  let A := visitSet H s ε
  let F := A ∩ Ioc 0 T
  let R := (fun x : ℝ => -x) ⁻¹' F
  have hm : MeasurableSet F := (measurable_visits H s ε).inter measurableSet_Ioc
  have hR : volume R = volume F := volume.measurePreserving_neg.measure_preimage hm.nullMeasurableSet
  have hF : volume F ≠ ⊤ := measure_ne_top_of_subset
    (show F ⊆ Icc 0 T from fun _ hx => ⟨hx.2.1.le,hx.2.2⟩) measure_Icc_lt_top.ne
  have hd : Disjoint F R := disjoint_left.mpr fun x hx hy =>
    (not_lt_of_ge (neg_nonpos.mpr hx.2.1.le)) hy.2.1
  have hsub : F ∪ R ⊆ A ∩ Icc (-T) T := by
    rintro x (hx | hx)
    · exact ⟨hx.1,⟨by linarith only [hx.2.1,hx.2.2],hx.2.2⟩⟩
    · have hh := HasProjectiveCircuitApproximation.neg_time H hx.1
      rw [neg_neg] at hh
      exact ⟨hh,⟨by linarith only [hx.2.2],by linarith only [hx.2.1,hx.2.2]⟩⟩
  have h := measureReal_mono (μ := volume) hsub
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  rw [measureReal_union hd (hm.preimage measurable_neg) hF (hR.trans_ne hF),
    show volume.real R = volume.real F from congrArg ENNReal.toReal hR] at h
  have he : F =ᵐ[volume] (A ∩ Icc 0 T : Set ℝ) := by
    filter_upwards [Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := T)] with x hx
    exact propext (and_congr_right fun _ => iff_of_eq hx)
  rw [measureReal_congr he] at h
  simpa only [two_mul] using h

/-- A hard endpoint at u controls every identity-start prefix, even those ending
before u. Reflection excludes two cheap times whose sum is u. Translated
packing on the symmetric interval gives the second bound. -/
theorem prefix_occupation_of_hard_endpoint {n s j q : ℕ} (H : selfAdjoint (Register n))
    {ε u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T) (hε : 0 ≤ ε) (hq : 0 < q)
    (hj : 2*s*q ≤ j) (hh : 2*(q:ℝ)*ε < orbitCircuitDistance H j u) :
    let L := volume.real (visitSet H s ε ∩ Icc 0 T)
    2*L ≤ T+|T-u| ∧ 2*((q:ℝ)+1)*L ≤ 2*T+u := by
  have hfar : ProjectiveCircuitSeparated n (2*(q:ℝ)*ε) (2*s*q) (unitaryEvolution H.val u) := by
    intro z hz C hC
    by_contra! he
    exact hh.not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ j _).mp
      ⟨z,hz,C,hC.trans hj,he⟩)
  let A := visitSet H s ε
  let F := A ∩ Icc 0 T
  let R := (fun t : ℝ => u-t) ⁻¹' F
  have hm : MeasurableSet F := (measurable_visits H s ε).inter measurableSet_Icc
  have hR : volume R = volume F := (volume.measurePreserving_sub_left u).measure_preimage hm.nullMeasurableSet
  have hF : volume F ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hd : Disjoint F R := by
    apply disjoint_left.mpr
    intro t ht hr
    have hprod := LocalPatches.approx_product (unitaryEvolution_mem_unitary H.2 t) hr.1 ht.1
    rw [unitaryEvolution_sub_mul H u t] at hprod
    obtain ⟨z,hz,C,hC,he⟩ := hprod
    have he' : ε+ε ≤ 2*(q:ℝ)*ε := by
      have h1 : (1:ℝ) ≤ q := by exact_mod_cast hq
      nlinarith only [mul_le_mul_of_nonneg_right h1 hε]
    have hbudget : s+s ≤ 2*s*q := by
      simpa only [two_mul] using Nat.le_mul_of_pos_right (2*s) hq
    exact (hfar z hz C (hC.trans hbudget)).not_ge (he.trans he')
  let lo := min 0 (u-T)
  let hi := max T u
  have hsub : F ∪ R ⊆ Icc lo hi := by
    rintro x (hx | hx)
    · exact ⟨(min_le_left ..).trans hx.2.1,hx.2.2.trans (le_max_left ..)⟩
    · exact ⟨(min_le_right ..).trans (by linarith only [hx.2.2]),
        le_trans (by linarith only [hx.2.1]) (le_max_right T u)⟩
  have h := measureReal_mono (μ := volume) hsub measure_Icc_lt_top.ne
  rw [measureReal_union hd (hm.preimage (measurable_const.sub measurable_id)) hF (hR.trans_ne hF),
    show volume.real R = volume.real F from congrArg ENNReal.toReal hR,
    Real.volume_real_Icc_of_le ((min_le_left ..).trans (hT.trans (le_max_left ..)))] at h
  have hlen : hi-lo = T+|T-u| := by
    rcases le_total T u with h | h
    · simp [hi,lo,h,sub_nonneg.mpr h,abs_of_nonpos (sub_nonpos.mpr h)]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      simp only [hi,lo,max_eq_left h,min_eq_right (sub_nonpos.mpr h)]
      ring
  have hpack := affordable_occupation_of_hard_lag H hq hε u hu hfar (-T) (2*T) (by positivity)
  rw [show -T+2*T=T by ring] at hpack
  have hdouble := mul_le_mul_of_nonneg_left (double_prefix H s ε T) (show 0 ≤ (q:ℝ)+1 by positivity)
  change _ ≤ ((q:ℝ)+1)*volume.real (visitSet H s ε ∩ Icc (-T) T) at hdouble
  exact ⟨by simpa only [two_mul] using h.trans_eq hlen,by
    have hbound := hdouble.trans hpack
    change 2*((q:ℝ)+1)*volume.real F ≤ 2*T+u
    change (↑q+1)*(2*volume.real F) ≤ 2*T+u at hbound
    linarith only [hbound]⟩

/-- On one Gaussian chain, first crossings through distance 13/10 at Hilbert-scale
budget satisfy finite prefix occupation bounds, simultaneously at every horizon.
At the top crossing, q = 6 gives at most 3/14 cheap time once T ≥ σ. -/
theorem gaussian_first_ascent_occupation :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let p := (1/2 + physicalArc (7/5))^D
      ∀ j ≤ D/(32*(N+1)), ∀ η ∈ Ioc (0:ℝ) (13/10),
        ∃ σ : ℝ, 0 < σ ∧ orbitCircuitDistance H j σ = η ∧
          (∀ t ∈ Ico 0 σ, orbitCircuitDistance H j t < η) ∧
          (1-p)*σ ≤ p*(2:ℝ)^(D^c) ∧
          ∀ (s q : ℕ) (ε T : ℝ), 0 < q → 2*s*q ≤ j → 0 ≤ ε → 2*(q:ℝ)*ε < η → 0 ≤ T →
            let L := volume.real (visitSet H s ε ∩ Icc 0 T)
            2*L ≤ T+|T-σ| ∧ 2*((q:ℝ)+1)*L ≤ 2*T+σ := by
  obtain ⟨c,hc⟩ := gaussian_period_corrected_occupation
  let x := physicalArc (7/5)
  have hroot : (7/5:ℝ) < Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg 2]
  obtain ⟨hx,he⟩ := physicalArc_spec (by norm_num : (0:ℝ) < 7/5) hroot
  have htol : 13/10+1/10 ≤ zeroGateArcTolerance x := by
    change _ ≤ zeroGateArcTolerance (physicalArc (7/5))
    rw [he]
    norm_num
  let b := 1/2+x
  have hb : 0 < b := by dsimp [b]; linarith only [hx.1]
  have hb1 : b < 1 := by dsimp [b]; linarith only [hx.2]
  have hlog : Real.log x + 32*Real.log 2/(32:ℕ) < Real.log b := by
    have h := Real.log_lt_log (mul_pos hx.1 zero_lt_two)
      (show x*2 < b by dsimp [b]; linarith only [hx.2])
    rw [Real.log_mul hx.1.ne' (by norm_num)] at h
    norm_num only [Nat.cast_ofNat]
    linarith only [h]
  refine ⟨c,?_⟩
  filter_upwards [hc] with ω hw
  filter_upwards [hw 32 (by decide) x hx (13/10) b htol hb hlog] with k hk
  intro N D H p j hj η hη
  have hD : D ≠ 0 := by dsimp [D]; positivity
  obtain ⟨σ,hpos,he,hprior,hdate⟩ := dated_crossing_of_occupation (j := j) H hη.1 hη.2
    (pow_nonneg hb.le D)
    (pow_lt_one₀ hb.le hb1 hD)
    (show 0 ≤ (2:ℝ)^(D^c) by positivity)
    (fun T hT => by simpa only [zero_add] using hk j hj 0 T hT)
  exact ⟨σ,hpos,he,hprior,hdate,fun s q ε T hq hj hε hh hT =>
    prefix_occupation_of_hard_endpoint H hpos.le hT hε hq hj (hh.trans_eq he.symm)⟩

#print axioms gaussian_first_ascent_occupation
#print axioms prefix_occupation_of_hard_endpoint
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
