import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation

/-!
# Nonpolar residuals vanish in the dual collar norm

Splitting a conductor residual at a fixed fraction of the horizon combines the
small lower-collar weight with cancellation on the terminal window. Thus every
fixed nonpolar conductor vanishes in the full dual seventh-power collar norm.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open ArithmeticHodgeTheoryOfDegenerations BezoutValuationIncidence CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

/-- Split the dual collar norm at a fractional horizon. The upper weight is at most one. -/
theorem topCollarDualSeventhMass_le_truncated_add_topWindow {N M : ℕ} {δ : ℝ}
    (hN : 1 ≤ N) (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    topCollarDualSeventhMass M N u ≤
      truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u + topWindowResidualMass δ N u := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let f : ℕ → ℝ := fun n => ((n : ℝ) / N) ^ 7 * primeHorizonExtension u n ^ 2
  have hf : ∀ n, 0 ≤ f n := fun n => mul_nonneg (by positivity) (sq_nonneg _)
  have hlow : (∑ n ∈ (Ioc M N).filter (fun n => n ≤ ⌊δ * (N : ℝ)⌋₊), f n) ≤
      truncatedCollarDualSeventhMass M ⌊δ * (N : ℝ)⌋₊ N u := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hn, hcut⟩ := mem_filter.mp hn
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, hcut⟩
    · exact fun n _ _ => hf n
  have htop : (∑ n ∈ (Ioc M N).filter (fun n => ¬n ≤ ⌊δ * (N : ℝ)⌋₊), f n) ≤
      topWindowResidualMass δ N u := by
    calc
      _ ≤ ∑ n ∈ (Ioc M N).filter (fun n => ¬n ≤ ⌊δ * (N : ℝ)⌋₊),
          primeHorizonExtension u n ^ 2 := by
        refine sum_le_sum fun n hn => ?_
        have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).2
        have hw : ((n : ℝ) / N) ^ 7 ≤ 1 :=
          pow_le_one₀ (by positivity) ((div_le_one hN0).mpr hnN)
        exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_eq (one_mul _)
      _ ≤ topWindowResidualMass δ N u := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hn, hcut⟩ := mem_filter.mp hn
          exact mem_Ioc.mpr ⟨by omega, (mem_Ioc.mp hn).2⟩
        · exact fun n _ _ => sq_nonneg _
  change (∑ n ∈ Ioc M N, f n) ≤ _
  rw [← sum_filter_add_sum_filter_not (Ioc M N) (fun n => n ≤ ⌊δ * (N : ℝ)⌋₊)]
  exact add_le_add hlow htop

/-- The normalized truncated residual bound is uniformly bounded along a critical curve. -/
theorem eventually_normalized_truncated_residual_bound
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      ∀ {δ : ℝ}, 0 ≤ δ → δ ≤ 1 →
      (Real.log (N : ℝ) / c N ^ 2) *
        truncatedCollarDualSeventhMass (N / linearDefectCutoff (c N)) ⌊δ * (N : ℝ)⌋₊ N
          (conductorResidualVector (c N) m N) ≤ K * δ * (m : ℝ) ^ 2 := by
  obtain ⟨K, hK, htrunc⟩ := exists_truncated_dualSeventh_conductor_residual
  obtain ⟨_, _, htail⟩ :=
    exists_finite_conductor_cutoff_collar_dualSeventh_below_ratio (R_max := R + 1) zero_lt_one
  have hL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := (criticalCurve_pow_log_div_natCast hc hR hcrit 2 0).const_mul
    (4 * (Real.exp 1 + 3) ^ 2)
  simp only [pow_zero, mul_one, mul_zero] at hsmall
  have herr₁ := criticalCurve_pow_log_div_natCast hc hR hcrit 1 2
  simp only [pow_one] at herr₁
  have herr₂ := (criticalCurve_pow_log_div_natCast hc hR hcrit 8 3).mul
    (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
      Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0))
  simp only [mul_zero] at herr₂
  refine ⟨3 * K, by positivity, ?_⟩
  filter_upwards [htail, hL.eventually_ge_atTop 1,
    hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
    hsmall.eventually (gt_mem_nhds zero_lt_one),
    herr₁.eventually (gt_mem_nhds zero_lt_one),
    herr₂.eventually (gt_mem_nhds zero_lt_one),
    eventually_below_overlap_pair_admissible hc hR hcrit, eventually_ge_atTop 1]
    with N htailN hL1 hratio hsmallN he₁ he₂ hadm hN1
  intro m hm δ hδ0 hδ1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hratio' := (div_lt_iff₀ hL0).mp hratio
  have hstrip := (htailN (hc N) hratio'.le).1
  obtain ⟨_, _, hrad, hc4⟩ := hadm 1 1 (by simpa using hc N) (by simpa using hc N)
  have hlarge : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N := by
    have hh : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 / N < 1 := by
      simpa only [mul_div_assoc] using hsmallN
    exact (div_lt_one hN0).mp hh |>.le
  have hb := htrunc hm (hc N) hL1 hδ0 hδ1 hlarge hrad hc4 hstrip
  have hid : (Real.log (N : ℝ) / c N ^ 2) *
      (c N ^ 2 / Real.log N + c N ^ 3 * Real.log N / N +
        c N ^ 10 * (Real.log N / N) ^ 2) =
      1 + c N * Real.log N ^ 2 / N + (c N ^ 8 * Real.log N ^ 3 / N) * (1 / N) := by
    field_simp
  have hrate : (Real.log (N : ℝ) / c N ^ 2) *
      (c N ^ 2 / Real.log N + c N ^ 3 * Real.log N / N +
        c N ^ 10 * (Real.log N / N) ^ 2) ≤ 3 := by
    rw [hid]; linarith only [he₁, he₂]
  calc _ ≤ (K * δ * (m : ℝ) ^ 2) * ((Real.log (N : ℝ) / c N ^ 2) *
        (c N ^ 2 / Real.log N + c N ^ 3 * Real.log N / N +
          c N ^ 10 * (Real.log N / N) ^ 2)) :=
      (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)
    _ ≤ (K * δ * (m : ℝ) ^ 2) * 3 :=
      mul_le_mul_of_nonneg_left hrate (by positivity)
    _ = _ := by ring

/-- The full normalized collar norm stays bounded, including conductor one. -/
theorem eventually_normalized_collar_residual_bound
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ {m : ℕ}, 0 < m →
      (Real.log (N : ℝ) / c N ^ 2) *
        topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
          (conductorResidualVector (c N) m N) ≤ K * (m : ℝ) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := eventually_normalized_truncated_residual_bound hc hR hcrit
  refine ⟨K, hK, hbound.mono fun N hN m hm => ?_⟩
  simpa only [one_mul, Nat.floor_natCast, mul_one, truncatedCollarDualSeventhMass,
    topCollarDualSeventhMass] using hN hm (zero_le_one : (0 : ℝ) ≤ 1) (le_refl (1 : ℝ))

/-- Every fixed nonpolar residual vanishes in the full dual seventh-power collar norm. -/
theorem tendsto_nonpolar_collar_dualSeventh {m : ℕ} (hm : 2 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) / c N ^ 2) *
      topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
        (conductorResidualVector (c N) m N)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := eventually_normalized_truncated_residual_bound hc hR hcrit
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := min (1 / 2) (ε / (4 * K * (m : ℝ) ^ 2))
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδsmall : K * δ * (m : ℝ) ^ 2 ≤ ε / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * K * (m : ℝ) ^ 2)).mp
      (min_le_right (1 / 2) (ε / (4 * K * (m : ℝ) ^ 2)))
    change δ * (4 * K * (m : ℝ) ^ 2) ≤ ε at hh
    linarith only [hh]
  have htop := (tendsto_nonpolar_topWindow_norm_sq hm hδ0 hδ1 hc hR hcrit).eventually
    (gt_mem_nhds (show 0 < ε / 2 by positivity))
  have hev : ∀ᶠ N : ℕ in atTop,
      dist ((Real.log (N : ℝ) / c N ^ 2) *
        topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
          (conductorResidualVector (c N) m N)) 0 < ε := by
    filter_upwards [hbound, htop, eventually_ge_atTop 1] with N hb ht hN
    have hscale : 0 ≤ Real.log (N : ℝ) / c N ^ 2 :=
      div_nonneg (Real.log_natCast_nonneg N) (sq_nonneg _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg
      (mul_nonneg hscale (topCollarDualSeventhMass_nonneg _ _ _))]
    have hs := mul_le_mul_of_nonneg_left
      (topCollarDualSeventhMass_le_truncated_add_topWindow (M := N / linearDefectCutoff (c N)) hN
        (δ := δ) (conductorResidualVector (c N) m N)) hscale
    rw [mul_add] at hs
    have hl := (hb (by omega : 0 < m) hδ0.le hδ1.le).trans hδsmall
    linarith only [hs, hl, ht, hε]
  exact eventually_atTop.mp hev


/-- The inverse-energy cost of a fixed nonpolar collar residual tends to zero. -/
theorem tendsto_nonpolar_collar_schur_cost {m : ℕ} (hm : 2 ≤ m)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (c N ^ 7 / Real.log (N : ℝ)) *
      (topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
        (conductorResidualVector (c N) m N) /
          completedConductorEnergy tiltedUnitSpline (c N) m)) atTop (𝓝 0) := by
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hD := tendsto_nonpolar_collar_dualSeventh hm hc hR hcrit
  have hlim := ((hcrit.pow 2).div_const (κ * (m : ℝ) ^ 7)).mul hD
  simp only [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (div_nonneg (pow_nonneg (zero_le_one.trans (hc N)) 7)
      (Real.log_natCast_nonneg N))
      (div_nonneg (topCollarDualSeventhMass_nonneg _ _ _)
        (completedConductorEnergy_tilted_pos (zero_lt_one.trans_le (hc N)) (by omega)).le)) ?_ hlim
  filter_upwards [(criticalCurve_facts hc hR hcrit).1.eventually_ge_atTop (m : ℝ),
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
    with N hmc hL
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hE := seventh_mul_completedConductorEnergy_ge_below_overlap hc0 (by omega : 0 < m) hmc
  have hfloor : κ * (m : ℝ) ^ 7 / c N ^ 7 ≤
      completedConductorEnergy tiltedUnitSpline (c N) m := by
    exact (div_le_iff₀ (pow_pos hc0 7)).mpr (by simpa only [mul_comm] using hE)
  have hdiv := div_le_div_of_nonneg_left (topCollarDualSeventhMass_nonneg
    (N / linearDefectCutoff (c N)) N (conductorResidualVector (c N) m N))
    (by positivity : 0 < κ * (m : ℝ) ^ 7 / c N ^ 7) hfloor
  exact (mul_le_mul_of_nonneg_left hdiv (by positivity)).trans_eq (by
    field_simp [hc0.ne', hL.ne', hκ.ne', hm0.ne'])

/-- The entire nonpolar low packet has vanishing weighted collar Schur cost. -/
theorem tendsto_nonpolar_lowPacket_collar_schur_cost
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (c N ^ 7 / Real.log (N : ℝ)) *
      ∑ m ∈ Icc 2 (lowPacketCutoff N),
        topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
          (conductorResidualVector (c N) m N) /
            completedConductorEnergy tiltedUnitSpline (c N) m) atTop (𝓝 0) := by
  let q : ℕ → ℕ → ℝ := fun N m => (c N ^ 7 / Real.log (N : ℝ)) *
    (topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
      (conductorResidualVector (c N) m N) / completedConductorEnergy tiltedUnitSpline (c N) m)
  have hq : ∀ N m, 1 ≤ m → 0 ≤ q N m := fun N m hm =>
    mul_nonneg (div_nonneg (pow_nonneg (zero_le_one.trans (hc N)) 7)
      (Real.log_natCast_nonneg N))
      (div_nonneg (topCollarDualSeventhMass_nonneg _ _ _)
        (completedConductorEnergy_tilted_pos (zero_lt_one.trans_le (hc N)) hm).le)
  have hfinite : ∀ s : Finset ℕ, (∀ m ∈ s, 2 ≤ m) →
      Tendsto (fun N => ∑ m ∈ s, q N m) atTop (𝓝 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa only [sum_empty] using (tendsto_const_nhds (x := (0 : ℝ)))
    | @insert m s hms ih =>
      intro hs
      have hm := tendsto_nonpolar_collar_schur_cost (hs m (mem_insert_self _ _)) hc hR hcrit
      have ht := ih (fun l hl => hs l (mem_insert_of_mem hl))
      simpa only [sum_insert hms, add_zero] using hm.add ht
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m₀, hm₀, htail⟩ :=
    exists_finite_conductor_cutoff_collar_dualSeventh_below_ratio
      (R_max := R + 1) (show 0 < ε / 2 by positivity)
  have hhead := (hfinite (Icc 2 m₀) (fun m hm => (mem_Icc.mp hm).1)).eventually
    (gt_mem_nhds (show 0 < ε / 2 by positivity))
  have hev : ∀ᶠ N : ℕ in atTop, dist
      ((c N ^ 7 / Real.log (N : ℝ)) * ∑ m ∈ Icc 2 (lowPacketCutoff N),
        topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
          (conductorResidualVector (c N) m N) /
            completedConductorEnergy tiltedUnitSpline (c N) m) 0 < ε := by
    filter_upwards [hhead, htail,
      hcrit.eventually (gt_mem_nhds (by linarith : R < R + 1)),
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
      with N hh ht hr hL
    have hr' := (div_lt_iff₀ hL).mp hr
    have hstrip := (ht (hc N) hr'.le).1
    have htailN := ((ht (hc N) hr'.le).2 hstrip).1
    rw [mul_sum] at htailN ⊢
    change (∑ m ∈ Ioc m₀ (lowPacketCutoff N), q N m) ≤ ε / 2 at htailN
    change dist (∑ m ∈ Icc 2 (lowPacketCutoff N), q N m) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sum_nonneg fun m hm =>
      hq N m (by have := (mem_Icc.mp hm).1; omega))]
    have hsplit : (∑ m ∈ Icc 2 (lowPacketCutoff N), q N m) ≤
        (∑ m ∈ Icc 2 m₀, q N m) + ∑ m ∈ Ioc m₀ (lowPacketCutoff N), q N m := by
      rw [← sum_filter_add_sum_filter_not (Icc 2 (lowPacketCutoff N)) (fun m => m ≤ m₀)]
      apply add_le_add
      · apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨hm, hcut⟩ := mem_filter.mp hm
          exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1, hcut⟩
        · intro m hm _; exact hq N m (by have := (mem_Icc.mp hm).1; omega)
      · apply sum_le_sum_of_subset_of_nonneg
        · intro m hm
          obtain ⟨hm, hcut⟩ := mem_filter.mp hm
          exact mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hm).2⟩
        · intro m hm _; exact hq N m (by have := (mem_Ioc.mp hm).1; omega)
    linarith only [hsplit, hh, htailN]
  exact eventually_atTop.mp hev

/-- Collar Schur cancellation is uniform on every positive compact interval of critical ratios. -/
theorem eventually_uniform_nonpolar_lowPacket_collar_schur_cost
    {R₀ R_max ε : ℝ} (hR₀ : 0 < R₀) (hR_le : R₀ ≤ R_max) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      R₀ * Real.log (N : ℝ) ≤ c ^ 8 → c ^ 8 ≤ R_max * Real.log (N : ℝ) →
      (c ^ 7 / Real.log (N : ℝ)) * ∑ m ∈ Icc 2 (lowPacketCutoff N),
        topCollarDualSeventhMass (N / linearDefectCutoff c) N (conductorResidualVector c m N) /
          completedConductorEnergy tiltedUnitSpline c m ≤ ε :=
  eventually_uniform_critical_band_of_curve hR₀ hR_le fun _R hR _c hc hcrit =>
    ((tendsto_nonpolar_lowPacket_collar_schur_cost hc (hR₀.trans_le hR.1) hcrit).eventually
      (gt_mem_nhds hε)).mono fun _ h => h.le

#print axioms tendsto_nonpolar_collar_dualSeventh
#print axioms tendsto_nonpolar_lowPacket_collar_schur_cost
#print axioms eventually_uniform_nonpolar_lowPacket_collar_schur_cost

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
