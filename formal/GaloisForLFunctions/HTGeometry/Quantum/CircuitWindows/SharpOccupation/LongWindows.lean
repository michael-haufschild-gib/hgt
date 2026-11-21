import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitWindows

/-! # The exponential lower waiting scale for a time-sampled observer -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- A visit in a window of length W is detected by one of the translated
unit windows. The time origin can be different for each translate. -/
private theorem window_fraction_bound {n j k : ℕ} {H : selfAdjoint (Register n)} {ε η p W : ℝ}
    (hW : 0 ≤ W) (hunit : windowHits H j ε 1 ⊆ visitSet H k η)
    (hocc : ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, visitFraction H k η a T < p) (a : ℝ) :
    ∀ᶠ T : ℝ in atTop, volume.real (windowHits H j ε W ∩ Icc a T)/(T-a) ≤ (W+1)*p := by
  classical
  let M := ⌊W⌋₊+1
  let shift (i : Fin M) := (i.val:ℝ)
  have hfin (i : Fin M) : ∀ᶠ T : ℝ in atTop,
      visitFraction H k η (a+shift i) (T+shift i) < p :=
    (tendsto_atTop_add_const_right atTop _ tendsto_id).eventually (hocc (a+shift i))
  have hclosed : IsClosed (visitSet H k η) := by
    have he : visitSet H k η = {v | orbitCircuitDistance H k v ≤ η} := Set.ext fun _ =>
      hasProjectiveCircuitApproximation_iff_infDist _ _ _
    rw [he]
    exact isClosed_le (orbitCircuitDistance_lipschitz H k).continuous continuous_const
  filter_upwards [Filter.eventually_all.mpr hfin,eventually_gt_atTop a] with T ht hT
  let A (i : Fin M) := visitSet H k η ∩ Icc (a+shift i) (T+shift i)
  let B (i : Fin M) := (fun u : ℝ => u+shift i) ⁻¹' (A i)
  have hlen (i : Fin M) : volume.real (B i) = volume.real (A i) :=
    congrArg ENNReal.toReal ((measurePreserving_add_right volume (shift i)).measure_preimage
      (hclosed.measurableSet.inter measurableSet_Icc).nullMeasurableSet)
  have hsub : windowHits H j ε W ∩ Icc a T ⊆ ⋃ i : Fin M, B i := by
    rintro u ⟨⟨v,hv,hcheap⟩,hu⟩
    let i : Fin M := ⟨⌊v-u⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (by linarith only [hv.2]))⟩
    have hlow : shift i ≤ v-u := Nat.floor_le (sub_nonneg.mpr hv.1)
    have hupp : v-u < shift i+1 := Nat.lt_floor_add_one _
    exact mem_iUnion.mpr ⟨i,hunit ⟨v,⟨by linarith only [hlow],by linarith only [hupp]⟩,hcheap⟩,
      add_le_add hu.1 le_rfl,add_le_add hu.2 le_rfl⟩
  have hI : (⋃ i : Fin M, B i) ⊆ Icc a T := by
    intro u hu
    obtain ⟨i,hi⟩ := mem_iUnion.mp hu
    have hh : u+shift i ∈ Icc (a+shift i) (T+shift i) := hi.2
    exact ⟨by linarith only [hh.1],by linarith only [hh.2]⟩
  have htot := (measureReal_mono hsub (measure_ne_top_of_subset hI measure_Icc_lt_top.ne)).trans
    (measureReal_iUnion_fintype_le B)
  have heach (i : Fin M) : volume.real (B i)/(T-a) ≤ p := by
    have h := (ht i).le
    change volume.real (A i)/((T+shift i)-(a+shift i)) ≤ p at h
    rwa [add_sub_add_right_eq_sub,←hlen i] at h
  have hp : 0 ≤ p := (div_nonneg measureReal_nonneg (sub_nonneg.mpr hT.le)).trans (heach ⟨0,Nat.zero_lt_succ _⟩)
  calc
    _ ≤ (∑ i : Fin M, volume.real (B i))/(T-a) := div_le_div_of_nonneg_right htot (sub_nonneg.mpr hT.le)
    _ ≤ (M:ℝ)*p := by
      rw [Finset.sum_div]
      simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => heach i)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [M]; push_cast; linarith only [Nat.floor_le hW]) hp

/-- For x < z < b < 1, starts with an affordable visit within b⁻ᴰ
occupy at most twice (z/b)ᴰ in long intervals on the fixed chain. -/
theorem gaussian_time_sampled_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (s : ℕ → ℕ), subcriticalBudget s →
      ∀ x ∈ Ioo (0:ℝ) (1/2), ∀ z b : ℝ, x < z → z < b → b < 1 →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          volume.real (windowHits H (s N) (zeroGateArcTolerance x) (1/b^D) ∩ Icc a T)/(T-a)
            ≤ 2*(z/b)^D := by
  filter_upwards [gaussian_cheap_occupation_rate,gaussian_unit_hit_enlargement] with ω hw hsim
  intro s hs x hx z b hxz hzb hb
  obtain ⟨y,hxy,hy⟩ := exists_between (lt_min hxz hx.2)
  have hyhalf := hy.trans_le (min_le_right ..)
  have hyz := hy.trans_le (min_le_left ..)
  have hδ := sub_pos.mpr (strictMonoOn_zeroGateArcTolerance ⟨hx.1.le,hx.2.le⟩
    ⟨(hx.1.trans hxy).le,hyhalf.le⟩ hxy)
  have hwide := hw (fun n => s n+n^4) (subcritical_add_pow_four hs) y ⟨hx.1.trans hxy,hyhalf⟩
    0 z le_rfl (hx.1.trans hxy) hyz
  filter_upwards [hwide,hsim _ hδ] with k hB hsim'
  intro N D H a
  have hunit := hsim' (s N) (zeroGateArcTolerance x)
  rw [show zeroGateArcTolerance x+(zeroGateArcTolerance y-zeroGateArcTolerance x) =
    zeroGateArcTolerance y by ring] at hunit
  have hbpos := (hx.1.trans hxz).trans hzb
  have hbp := pow_pos hbpos D
  have hW : 1 ≤ 1/b^D := (le_div_iff₀ hbp).mpr (by simpa using pow_le_one₀ hbpos.le hb.le (n := D))
  filter_upwards [window_fraction_bound (zero_le_one.trans hW) hunit
    (fun a => (hB a).mono fun _ h => (h _ le_rfl).2) a] with T hT
  apply hT.trans
  calc
    _ ≤ (2*(1/b^D))*z^D := mul_le_mul_of_nonneg_right (by linarith only [hW]) (pow_nonneg (hx.1.trans hxz).le D)
    _ = _ := by rw [div_pow]; ring

#print axioms gaussian_time_sampled_wait
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
