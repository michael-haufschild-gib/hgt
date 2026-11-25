import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.Unequal.Geodesic
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FirstAscent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Geodesic hard-lag packing and immediate post-onset occupation -/
open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

private theorem orbitCircuitDistance_bounds {n : ℕ} (H : selfAdjoint (Register n)) (j : ℕ) (t : ℝ) :
    0 ≤ orbitCircuitDistance H j t ∧ orbitCircuitDistance H j t ≤ 2 := by
  refine ⟨Metric.infDist_nonneg, ?_⟩
  apply (hasProjectiveCircuitApproximation_iff_infDist _ j (2 : ℝ)).mp
  refine ⟨1, norm_one, TwoQubitCircuit.one n, Nat.zero_le _, ?_⟩
  rw [one_smul, TwoQubitCircuit.one_eval]
  have hnorm := norm_sub_le (unitaryEvolution H.val t) (1 : Register n)
  rw [CStarRing.norm_of_mem_unitary (unitaryEvolution_mem_unitary H.2 t), norm_one] at hnorm
  exact hnorm.trans_eq (by norm_num)

private theorem orbitCircuitDistance_antitone_budget {n i j : ℕ} (H : selfAdjoint (Register n))
    (hij : i ≤ j) (t : ℝ) : orbitCircuitDistance H j t ≤ orbitCircuitDistance H i t := by
  apply (hasProjectiveCircuitApproximation_iff_infDist _ j _).mp
  obtain ⟨z, hz, C, hC, he⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ i _).mpr
    (le_rfl : orbitCircuitDistance H i t ≤ _)
  exact ⟨z, hz, C, hC.trans hij, he⟩

private theorem measurable_visitSet {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε : ℝ) :
    MeasurableSet (visitSet H s ε) := by
  have he : visitSet H s ε = {t | orbitCircuitDistance H s t ≤ ε} :=
    Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist _ _ _
  rw [he]
  exact (isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const).measurableSet

private theorem double_prefix_visits {n : ℕ} (H : selfAdjoint (Register n)) (s : ℕ) (ε T : ℝ) :
    2 * volume.real (visitSet H s ε ∩ Icc 0 T) ≤ volume.real (visitSet H s ε ∩ Icc (-T) T) := by
  let A := visitSet H s ε
  let F := A ∩ Ioc 0 T
  let R := (fun x : ℝ => -x) ⁻¹' F
  have hm : MeasurableSet F := (measurable_visitSet H s ε).inter measurableSet_Ioc
  have hR : volume R = volume F := volume.measurePreserving_neg.measure_preimage hm.nullMeasurableSet
  have hF : volume F ≠ ⊤ := measure_ne_top_of_subset
    (show F ⊆ Icc 0 T from fun _ hx => ⟨hx.2.1.le, hx.2.2⟩) measure_Icc_lt_top.ne
  have hd : Disjoint F R := disjoint_left.mpr fun _ hx hy =>
    (not_lt_of_ge (neg_nonpos.mpr hx.2.1.le)) hy.2.1
  have hsub : F ∪ R ⊆ A ∩ Icc (-T) T := by
    rintro x (hx | hx)
    · exact ⟨hx.1, ⟨by linarith only [hx.2.1, hx.2.2], hx.2.2⟩⟩
    · have hh := HasProjectiveCircuitApproximation.neg_time H hx.1
      rw [neg_neg] at hh
      exact ⟨hh, ⟨by linarith only [hx.2.2], by linarith only [hx.2.1, hx.2.2]⟩⟩
  have h := measureReal_mono (μ := volume) hsub
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  rw [measureReal_union hd (hm.preimage measurable_neg) hF (hR.trans_ne hF),
    show volume.real R = volume.real F from congrArg ENNReal.toReal hR] at h
  have he : F =ᵐ[volume] (A ∩ Icc 0 T : Set ℝ) := by
    filter_upwards [Ioc_ae_eq_Icc (μ := volume) (a := 0) (b := T)] with x hx
    exact propext (and_congr_right fun _ => iff_of_eq hx)
  rw [measureReal_congr he] at h
  simpa only [two_mul] using h

/-- Interpolating the half-chord angle from zero to B produces q+1 disjoint
translates whenever the (2sq)-gate distance at B exceeds 2 sin(2qα). -/
theorem affordable_occupation_of_geodesic_hard_lag {n s q : ℕ} (H : selfAdjoint (Register n))
    (hq : 0 < q) {α B : ℝ} (hα : 0 ≤ α) (hqα : 2 * (q : ℝ) * α ≤ π / 2) (hB : 0 ≤ B)
    (hh : 2 * sin (2 * (q : ℝ) * α) < orbitCircuitDistance H (2 * s * q) B)
    (a T : ℝ) (hT : 0 ≤ T) :
    ((q : ℝ) + 1) * volume.real (visitSet H s (2 * sin α) ∩ Icc a (a + T)) ≤ T + B := by
  let A := visitSet H s (2 * sin α)
  let θ (j : ℕ) (t : ℝ) := arcsin (orbitCircuitDistance H j t / 2)
  have hcont (j : ℕ) : Continuous (θ j) :=
    continuous_arcsin.comp ((orbitCircuitDistance_lipschitz H j).continuous.div_const 2)
  let d := orbitCircuitDistance H (2 * s * q) B
  obtain ⟨hd0, hd2⟩ := orbitCircuitDistance_bounds H (2 * s * q) B
  have hqr : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have h2qα0 : 0 ≤ 2 * (q : ℝ) * α := by positivity
  have hΘ_gt : 2 * (q : ℝ) * α < arcsin (d / 2) := by
    have hlt := arcsin_lt_arcsin (neg_one_le_sin _)
      (show sin (2 * (q : ℝ) * α) < d / 2 by linarith only [hh]) (by linarith only [hd2])
    rwa [arcsin_sin (by linarith only [h2qα0, pi_pos]) hqα] at hlt
  let Θ := arcsin (d / 2)
  have hΘ_le : Θ ≤ π / 2 := arcsin_le_pi_div_two _
  let r := Θ / (q : ℝ)
  have hr : 2 * α < r := (lt_div_iff₀ hqr).mpr (by linarith only [hΘ_gt])
  have hr0 : 0 ≤ r := le_trans (by positivity) hr.le
  have hrd : (q : ℝ) * r = Θ := mul_div_cancel₀ Θ hqr.ne'
  have level (i : Fin (q + 1)) : ∃ t ∈ Icc 0 B, orbitCircuitDistance H (2 * s * i.val) t = 2 * sin ((i.val : ℝ) * r) := by
    let b := 2 * s * i.val
    have h0_le : orbitCircuitDistance H b 0 ≤ 0 := by
      apply (hasProjectiveCircuitApproximation_iff_infDist _ b 0).mp
      refine ⟨1, norm_one, TwoQubitCircuit.one n, Nat.zero_le _, ?_⟩
      simp [TwoQubitCircuit.one_eval, unitaryEvolution]
    have h0_eq : θ b 0 = 0 := by
      have hd0' := le_antisymm h0_le (orbitCircuitDistance_bounds H b 0).1
      simp [θ, hd0']
    have hiq : i.val ≤ q := Nat.lt_succ_iff.mp i.isLt
    have hB_ge : d ≤ orbitCircuitDistance H b B :=
      orbitCircuitDistance_antitone_budget H (Nat.mul_le_mul_left (2 * s) hiq) B
    have hB_θ : Θ ≤ θ b B := arcsin_le_arcsin (by linarith only [hB_ge])
    have hir : (i.val : ℝ) * r ≤ Θ := by
      rw [← hrd]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hiq) hr0
    obtain ⟨t, ht, heq⟩ := intermediate_value_Icc hB (hcont b).continuousOn
      ⟨by rw [h0_eq]; positivity, hir.trans hB_θ⟩
    refine ⟨t, ht, ?_⟩
    obtain ⟨ht0, ht2⟩ := orbitCircuitDistance_bounds H b t
    have hsin := congrArg (fun x => 2 * sin x) heq
    dsimp only [θ] at hsin
    rw [sin_arcsin (by linarith only [ht0]) (by linarith only [ht2])] at hsin
    linarith only [hsin]
  choose u hu heq using level
  have hforbid {i j : Fin (q + 1)} (hij : i < j) (x : ℝ) (hi : x - u i ∈ A) (hj : x - u j ∈ A) : False := by
    have h2α_pi : α + α ≤ π / 2 := by
      have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have hle : 2 * α ≤ 2 * (q : ℝ) * α := by nlinarith only [h1, hα]
      linarith only [hle, hqα]
    have hj' : HasProjectiveCircuitApproximation n (2 * sin α) s (unitaryEvolution H.val (x - u j)) := hj
    have hinc := AngularError.affordable_add_geodesic H hα hα h2α_pi hi (hj'.neg_time H)
    rw [show α + α = 2 * α by ring] at hinc
    have hstart := (hasProjectiveCircuitApproximation_iff_infDist _ (2 * s * i.val) _).mpr (heq i).le
    have hij' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast (show i.val + 1 ≤ j.val from hij)
    have hjq : (j.val : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp j.isLt
    have hsum_lt : (i.val : ℝ) * r + 2 * α < (j.val : ℝ) * r := by
      calc (i.val : ℝ) * r + 2 * α < (i.val : ℝ) * r + r := by linarith only [hr]
           _ = ((i.val : ℝ) + 1) * r := by ring
           _ ≤ (j.val : ℝ) * r := mul_le_mul_of_nonneg_right hij' hr0
    have hjr_le : (j.val : ℝ) * r ≤ π / 2 :=
      (mul_le_mul_of_nonneg_right hjq hr0).trans (hrd.le.trans hΘ_le)
    have hend := AngularError.affordable_add_geodesic H (by positivity) (by positivity)
      (hsum_lt.le.trans hjr_le) hstart hinc
    rw [show u i + (x - u i + -(x - u j)) = u j by ring] at hend
    have hbudget : 2 * s * i.val + (s + s) ≤ 2 * s * j.val := by
      have hstep := Nat.mul_le_mul_left (2 * s) (show i.val + 1 ≤ j.val from hij)
      simpa only [Nat.mul_add, Nat.mul_one, two_mul] using hstep
    obtain ⟨z, hz, C, hC, herr⟩ := hend
    have hdist := (hasProjectiveCircuitApproximation_iff_infDist _ (2 * s * j.val) _).mp
      ⟨z, hz, C, hC.trans hbudget, herr⟩
    change orbitCircuitDistance H (2 * s * j.val) (u j) ≤ _ at hdist
    rw [heq j] at hdist
    have hi0 : 0 ≤ (i.val : ℝ) * r + 2 * α := by positivity
    have hj0 : 0 ≤ (j.val : ℝ) * r := by positivity
    have hstrict := strictMonoOn_sin ⟨by linarith only [pi_pos, hi0], (hsum_lt.le.trans hjr_le)⟩
      ⟨by linarith only [pi_pos, hj0], hjr_le⟩ hsum_lt
    linarith only [hdist, hstrict]
  have hsep (i j : Fin (q + 1)) (hne : i ≠ j) (x : ℝ) (hi : x - u i ∈ A) (hj : x - u j ∈ A) : False :=
    (lt_or_gt_of_ne hne).elim (fun h => hforbid h x hi hj) (fun h => hforbid h x hj hi)
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    occupation_mul_card_le_of_disjoint_shifts (measurable_visitSet H s (2 * sin α)) u hB hu hsep a T hT

/-- From a geodesic hard endpoint B, cheap visits on [0,T] occupy at most
(2T+B)/(2(q+1)), forcing the plateau to occupy most of [B,T] for all
T > ((q+2)/(q-1)) B with zero phase-clock wait. -/
theorem post_onset_occupation_of_geodesic_endpoint {n s j q : ℕ} (H : selfAdjoint (Register n))
    {α B : ℝ} (hB : 0 ≤ B) (hq : 0 < q) (hα : 0 ≤ α) (hqα : 2 * (q : ℝ) * α ≤ π / 2)
    (hj : 2 * s * q ≤ j) (hh : 2 * sin (2 * (q : ℝ) * α) < orbitCircuitDistance H j B) :
    (∀ T : ℝ, 0 ≤ T → 2 * ((q : ℝ) + 1) * volume.real (visitSet H s (2 * sin α) ∩ Icc 0 T) ≤ 2 * T + B) ∧
    (∀ T : ℝ, B ≤ T → 2 * (q : ℝ) * (T - B) - 3 * B ≤
      2 * ((q : ℝ) + 1) * volume.real ((visitSet H s (2 * sin α))ᶜ ∩ Icc B T)) ∧
    (1 < q → ∀ T : ℝ, ((q : ℝ) + 2) / ((q : ℝ) - 1) * B < T →
      T - B < 2 * volume.real ((visitSet H s (2 * sin α))ᶜ ∩ Icc B T)) := by
  have hh' : 2 * sin (2 * (q : ℝ) * α) < orbitCircuitDistance H (2 * s * q) B :=
    hh.trans_le (orbitCircuitDistance_antitone_budget H hj B)
  have hprefix (T : ℝ) (hT : 0 ≤ T) :
      2 * ((q : ℝ) + 1) * volume.real (visitSet H s (2 * sin α) ∩ Icc 0 T) ≤ 2 * T + B := by
    have hpack := affordable_occupation_of_geodesic_hard_lag H hq hα hqα hB hh' (-T) (2 * T) (by positivity)
    rw [show -T + 2 * T = T by ring] at hpack
    have hdouble := mul_le_mul_of_nonneg_left (double_prefix_visits H s (2 * sin α) T)
      (by positivity : 0 ≤ (q : ℝ) + 1)
    linarith only [hdouble, hpack]
  have hpost (T : ℝ) (hBT : B ≤ T) :
      2 * (q : ℝ) * (T - B) - 3 * B ≤
        2 * ((q : ℝ) + 1) * volume.real ((visitSet H s (2 * sin α))ᶜ ∩ Icc B T) := by
    let V := visitSet H s (2 * sin α)
    let P := Vᶜ ∩ Icc B T
    let C := V ∩ Icc B T
    have hV : MeasurableSet V := measurable_visitSet H s (2 * sin α)
    have hP : MeasurableSet P := hV.compl.inter measurableSet_Icc
    have hC : MeasurableSet C := hV.inter measurableSet_Icc
    have hd : Disjoint P C := disjoint_left.mpr fun _ hx hy => hx.1 hy.1
    have hunion : P ∪ C = Icc B T := by
      ext x; simp only [P, C, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    have hPfin : volume P ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
    have hCfin : volume C ≠ ⊤ := measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
    have hsum : volume.real P + volume.real C = T - B := by
      rw [← measureReal_union hd hC hPfin hCfin, hunion, Real.volume_real_Icc_of_le hBT]
    have hC_le : volume.real C ≤ volume.real (V ∩ Icc 0 T) :=
      measureReal_mono (inter_subset_inter_right V (Icc_subset_Icc_left hB))
        (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
    have hpref := hprefix T (hB.trans hBT)
    have hC_scaled := mul_le_mul_of_nonneg_left hC_le (by positivity : 0 ≤ 2 * ((q : ℝ) + 1))
    nlinarith only [hsum, hpref, hC_scaled]
  refine ⟨hprefix, hpost, ?_⟩
  intro hq1 T hT
  have hq1' : 0 < (q : ℝ) - 1 := by
    have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith only [h2]
  have hBT : B ≤ T := by
    have h1 : 1 ≤ ((q : ℝ) + 2) / ((q : ℝ) - 1) := (one_le_div hq1').mpr (by linarith only [hq1'])
    exact (le_mul_of_one_le_left hB h1).trans hT.le
  have hmul : ((q : ℝ) + 2) * B < ((q : ℝ) - 1) * T := by
    have := (div_lt_iff₀ hq1').mp (by simpa only [mul_comm (((q : ℝ) + 2) / ((q : ℝ) - 1)),
      mul_div_assoc'] using hT)
    linarith only [this]
  have hp := hpost T hBT
  have hqp : 0 < (q : ℝ) + 1 := by positivity
  nlinarith only [hp, hmul, hqp]

/-- At error 1/10, fifteen double-angle steps stay strictly below the 31/32-turn
arc tolerance and below π/2 in half-angle. -/
theorem thirty_arcsin_twentieth_lt_arc :
    0 < arcsin (1 / 20) ∧ 2 * sin (arcsin (1 / 20)) = 1 / 10 ∧
      30 * arcsin (1 / 20) ≤ π / 2 ∧
      2 * sin (30 * arcsin (1 / 20)) < zeroGateArcTolerance (31 / 32) := by
  let α := arcsin (1 / 20)
  have hα_pos : 0 < α := arcsin_pos.mpr (by norm_num)
  have hsin : 2 * sin α = 1 / 10 := by
    dsimp only [α]
    rw [sin_arcsin (by norm_num) (by norm_num)]
    norm_num
  have hcube := sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1001 / 20000)
  have htwentieth : (1 / 20 : ℝ) < sin (1001 / 20000) := by linarith only [hcube]
  have hpi := pi_gt_d6
  have hα_lt : α < 1001 / 20000 := by
    have hlt := arcsin_lt_arcsin (by norm_num) htwentieth (sin_le_one _)
    rwa [arcsin_sin (by linarith only [hpi]) (by linarith only [hpi])] at hlt
  have h30 : 30 * α < π * (31 / 32) / 2 := by linarith only [hα_lt, hpi]
  have hpi2 : π * (31 / 32) / 2 ≤ π / 2 := by linarith only [hpi]
  refine ⟨hα_pos, hsin, (h30.trans_le hpi2).le, ?_⟩
  unfold zeroGateArcTolerance
  exact mul_lt_mul_of_pos_left
    (strictMonoOn_sin ⟨by linarith only [hα_pos, hpi], (h30.trans_le hpi2).le⟩
      ⟨by linarith only [hpi], hpi2⟩ h30) two_pos

#print axioms affordable_occupation_of_geodesic_hard_lag
#print axioms post_onset_occupation_of_geodesic_endpoint
#print axioms thirty_arcsin_twentieth_lt_arc
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
