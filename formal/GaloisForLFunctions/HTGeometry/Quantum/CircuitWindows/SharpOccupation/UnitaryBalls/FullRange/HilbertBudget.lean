import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.FullRange.PhysicalRates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PositiveDensityBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.GaussianMaximumQuantiles

/-! # Hilbert-scale circuit occupation and orbit maxima across all operator errors below two -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

private theorem dim_tendsto : Tendsto (fun k : ℕ => (2 : ℕ) ^ (k + 3)) atTop atTop :=
  tendsto_atTop_mono (fun k => (show k ≤ k + 3 by omega).trans (Nat.lt_two_pow_self (n := k + 3)).le) tendsto_id

private theorem exists_enlarged_arc {q : ℕ} {x b : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hl : Real.log x + 32 * Real.log 2 / q < Real.log b) :
    ∃ y ∈ Ioo (0 : ℝ) 1, x < y ∧ Real.log y + 32 * Real.log 2 / q < Real.log b := by
  have hcon : ContinuousAt (fun z : ℝ => Real.log z + 32 * Real.log 2 / q) x :=
    (Real.continuousAt_log hx.1.ne').add continuousAt_const
  obtain ⟨δ, hδ, hsub⟩ := Metric.eventually_nhds_iff.mp (hcon.eventually_lt_const hl)
  let y := x + min (1 - x) δ / 2
  have hmin : 0 < min (1 - x) δ := lt_min (sub_pos.mpr hx.2) hδ
  have hxy : x < y := by dsimp only [y]; linarith only [hmin]
  have hy1 : y < 1 := by dsimp only [y]; linarith only [min_le_left (1 - x) δ, hmin]
  have hdist : dist y x < δ := by
    rw [Real.dist_eq, show y - x = min (1 - x) δ / 2 by dsimp only [y]; ring,
      abs_of_pos (half_pos hmin)]
    linarith only [min_le_right (1 - x) δ, hmin]
  exact ⟨y, ⟨hx.1.trans hxy, hy1⟩, hxy, hsub hdist⟩

/-- Hilbert-scale budgets D/[q(N+1)] have exponentially small long-window
occupation at every angular tolerance below a full turn. -/
theorem gaussian_hilbert_budget_occupation_full :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ q : ℕ, 0 < q →
      ∀ x ∈ Ioo (0 : ℝ) 1, ∀ b : ℝ, 0 < b →
      Real.log x + 32 * Real.log 2 / q < Real.log b →
      ∀ᶠ k : ℕ in atTop,
        let N := k + 3
        let D : ℕ := 2 ^ N
        let H : selfAdjoint (Register N) :=
          ⟨pathHamiltonian (pathPauliDisorderShell ω (k + 1)), isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ j ≤ D / (q * (N + 1)),
          visitFraction H j (zeroGateArcTolerance x) a (a + T) < b ^ D := by
  filter_upwards [PhaseBoundary.gaussian_uniform_affordable_fraction] with ω hlim
  intro q hq x hx b hb hxb
  obtain ⟨y, hy, hxy, hyb⟩ := exists_enlarged_arc hx hxb
  let η := (zeroGateArcTolerance y - zeroGateArcTolerance x) / 2
  have hη : 0 < η := half_pos (sub_pos.mpr (strictMonoOn_zeroGateArcTolerance_full
    ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy))
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * Real.pi / η)
  have hm' : 0 < m := Nat.cast_pos.mp ((div_pos Real.two_pi_pos hη).trans hm)
  have hgrid : 2 * Real.pi / m ≤ η := (div_le_iff₀ (Nat.cast_pos.mpr hm')).mpr (by
    simpa only [mul_comm η] using ((div_lt_iff₀ hη).mp hm).le)
  have hprice : zeroGateArcTolerance x + η + 2 * Real.pi / m ≤ zeroGateArcTolerance y := by
    dsimp only [η] at hgrid ⊢
    linarith only [hgrid]
  have hexp := (tendsto_add_atTop_nat 3).eventually
    ((positive_budget_exponent q hq η y b hη hy.1 hb hyb).and (eventually_ge_atTop m))
  filter_upwards [hexp] with k ⟨hpos_exp, hmk⟩
  intro N D H a
  let s := D / (q * (N + 1))
  let e := (qubitConfigFin N).trans (prefixPhaseEnergyEquiv k)
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hDpos : 0 < D := Nat.two_pow_pos N
  have hmD : (m : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast hmk.trans (Nat.lt_two_pow_self (n := N)).le
  have hyD : y ^ D ≤ y ^ (D - 1) := by
    calc y ^ D = y ^ (D - 1) * y := by rw [← pow_succ, Nat.sub_add_cancel hDpos]
         _ ≤ y ^ (D - 1) * 1 := mul_le_mul_of_nonneg_left hy.2.le (pow_nonneg hy.1.le _)
         _ = _ := mul_one _
  have hmy : (m : ℝ) * y ^ D ≤ zeroGateArcDensity D y := by
    dsimp only [zeroGateArcDensity]
    exact mul_le_mul hmD hyD (pow_nonneg hy.1.le _) (Nat.cast_nonneg _)
  let E : ℝ := ((s : ℝ) + 1) * ((((N : ℝ) + 1) ^ 2) * (1 + 4 * (s : ℝ) / η) ^ 32) ^ s
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hvol := UnitaryBalls.circuit_volume_bound e V s m hm' hη ⟨hy.1.le, hy.2⟩ hprice
  have hupper : volume.real (projectiveContinuousCircuitCaptureTarget e V s (zeroGateArcTolerance x)) < b ^ D := by
    have h1 : (m : ℝ) * E * y ^ D = E * ((m : ℝ) * y ^ D) := by ring
    change _ ≤ (m : ℝ) * E * y ^ D at hvol
    exact (hvol.trans_eq h1).trans_lt ((mul_le_mul_of_nonneg_left hmy hE).trans_lt hpos_exp)
  have hhi := (hlim k s (zeroGateArcTolerance x) (fun _ => a)).eventually_lt_const hupper
  filter_upwards [hhi, eventually_ge_atTop (0 : ℝ)] with T hT hT0 j hj
  exact (visitFraction_mono H hj _ a (a + T) (le_add_of_nonneg_right hT0)).trans_lt hT

/-- Fine scalar recurrence windows transfer the full-range Hilbert-scale
occupation bound to every finite interval without coarse tolerance loss. -/
theorem gaussian_finite_hilbert_occupation_full :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ q : ℕ, 0 < q →
      ∀ ε ∈ Ioo (0 : ℝ) 2, ∀ b : ℝ, 0 < b →
      Real.log (physicalArc ε) + 32 * Real.log 2 / q < Real.log b →
      ∀ᶠ k : ℕ in atTop,
        let N := k + 3
        let D : ℕ := 2 ^ N
        let H : selfAdjoint (Register N) :=
          ⟨pathHamiltonian (pathPauliDisorderShell ω (k + 1)), isSelfAdjoint_pathHamiltonian _⟩
        let G := (2 : ℝ) ^ (D ^ c)
        ∀ j ≤ D / (q * (N + 1)), ∀ a T : ℝ, 0 ≤ T →
          volume.real (visitSet H j ε ∩ Icc a (a + T)) ≤ b ^ D * (T + G) := by
  obtain ⟨c, hclock⟩ := SpectralJets.HighPrecision.gaussian_fine_scalar_windows
  refine ⟨c, ?_⟩
  filter_upwards [hclock, gaussian_hilbert_budget_occupation_full] with ω hc ho
  intro q hq ε hε b hb hxb
  let x := physicalArc ε
  obtain ⟨hx, htol⟩ := physicalArc_full hε
  obtain ⟨z, hz, hxz, hzb⟩ := exists_enlarged_arc hx hxb
  have hgap : 0 < zeroGateArcTolerance z - ε := by
    rw [← htol]
    exact sub_pos.mpr (strictMonoOn_zeroGateArcTolerance_full ⟨hx.1.le, hx.2.le⟩ ⟨hz.1.le, hz.2.le⟩ hxz)
  have hδ : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ ((2 : ℕ) ^ (k + 3))) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp dim_tendsto
  filter_upwards [hc, ho q hq z hz b hb hzb, hδ.eventually_lt_const hgap] with k hper hocc hδz
  intro N D H G j hj a T hT
  let s := D / (q * (N + 1))
  have hclosed : IsClosed (visitSet H s ε) := by
    have he : visitSet H s ε = {v | orbitCircuitDistance H s v ≤ ε} :=
      Set.ext fun _ => hasProjectiveCircuitApproximation_iff_infDist _ _ _
    rw [he]
    exact isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const
  have hfit : ε + 1 / (2 : ℝ) ^ D ≤ zeroGateArcTolerance z := by
    rw [one_div_pow] at hδz
    change 1 / (2 : ℝ) ^ D < zeroGateArcTolerance z - ε at hδz
    linarith only [hδz]
  have hs_bound : volume.real (visitSet H s ε ∩ Icc a (a + T)) ≤ b ^ D * (T + G) := by
    apply occupation_from_periods _ (visitSet H s (zeroGateArcTolerance z)) hclosed.measurableSet
      (by dsimp only [G]; positivity) _ _ a T hT
    · intro u
      obtain ⟨τ, hτ, hzero⟩ := hper u
      refine ⟨τ, hτ, fun t ht => ?_⟩
      have hprod := LocalPatches.approx_product (unitaryEvolution_mem_unitary H.2 τ) ht hzero
      have he := unitaryEvolution_sub_mul H (t + τ) τ
      rw [show t + τ - τ = t by ring] at he
      rw [he, Nat.add_zero] at hprod
      obtain ⟨w, hw, C, hC, hd⟩ := hprod
      exact ⟨w, hw, C, hC, hd.trans hfit⟩
    · filter_upwards [hocc 0, eventually_gt_atTop (0 : ℝ)] with R hr hR
      have hh := hr s le_rfl
      rw [zero_add, visitFraction, sub_zero] at hh
      exact ((div_lt_iff₀ hR).mp hh).le
  have hsub : visitSet H j ε ∩ Icc a (a + T) ⊆ visitSet H s ε ∩ Icc a (a + T) := by
    refine inter_subset_inter_left _ ?_
    rintro t ⟨w, hw, C, hC, hd⟩
    exact ⟨w, hw, C, hC.trans hj, hd⟩
  exact (measureReal_mono hsub (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)).trans hs_bound

/-- Every fixed operator tolerance below two has an exponentially large
recurrent orbit maximum on all sufficiently long Gaussian prefixes. -/
theorem gaussian_orbit_maximum_full_range :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ η ∈ Ioo (0 : ℝ) 2, ∀ q : ℕ, 0 < q →
      Real.log (physicalArc η) + 32 * Real.log 2 / q < 0 →
      ∀ᶠ k : ℕ in atTop,
        let N := k + 3
        let D : ℕ := 2 ^ N
        let u := pathPauliDisorderShell ω (k + 1)
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian u, isSelfAdjoint_pathHamiltonian u⟩
        ∃ m > D / (q * (N + 1)), IsRecurrentOrbitCircuitMaximumAt H η m := by
  filter_upwards [gaussian_hilbert_budget_occupation_full] with ω ho
  intro η hη q hq hneg
  let r := (Real.log (physicalArc η) + 32 * Real.log 2 / q) / 2
  let b := Real.exp r
  have hb0 : 0 < b := Real.exp_pos r
  have hb1 : b < 1 := Real.exp_lt_one_iff.mpr (by dsimp only [r]; linarith only [hneg])
  have hxb : Real.log (physicalArc η) + 32 * Real.log 2 / q < Real.log b := by
    rw [Real.log_exp]; dsimp only [r]; linarith only [hneg]
  obtain ⟨hx, htol⟩ := physicalArc_full hη
  filter_upwards [ho q hq (physicalArc η) hx b hb0 hxb] with k hk
  intro N D u H
  obtain ⟨m, hm⟩ := twoLocal_exists_recurrent_maximum_at (by dsimp only [N]; omega : 2 ≤ N) H
    (hasPauliWeightAtMost_pathHamiltonian u (isSelfAdjoint_pathHamiltonian u)) η hη.1
  refine ⟨m, ?_, hm⟩
  by_contra! hle
  obtain ⟨T, hT1, hfrac⟩ := ((eventually_gt_atTop (0 : ℝ)).and (hk 0)).exists
  have hsmall := hfrac (D / (q * (N + 1))) le_rfl
  rw [htol, zero_add] at hsmall
  have hall : Icc 0 T ⊆ visitSet H (D / (q * (N + 1))) η := fun t _ =>
    let ⟨z, hz, C, hC, he⟩ := hm.1 t
    ⟨z, hz, C, hC.trans hle, he⟩
  have h1 : visitFraction H (D / (q * (N + 1))) η 0 T = 1 := by
    rw [visitFraction, inter_eq_right.mpr hall, Real.volume_real_Icc_of_le hT1.le,
      sub_zero, div_self hT1.ne']
  have hpow : b ^ D < 1 := pow_lt_one₀ hb0.le hb1 (Nat.two_pow_pos N).ne'
  linarith only [hsmall, h1, hpow]

#print axioms gaussian_hilbert_budget_occupation_full
#print axioms gaussian_finite_hilbert_occupation_full
#print axioms gaussian_orbit_maximum_full_range
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
