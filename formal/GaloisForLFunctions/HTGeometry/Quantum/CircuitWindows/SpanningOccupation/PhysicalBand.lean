import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpanningOccupation.PhysicalLag

/-! # Sharp fixed-error time share of the minimum-cost band near one gate per bond -/
open Set Matrix MeasureTheory Filter Real
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.SpanningOccupation
noncomputable section
open SharpOccupation

private theorem shifted_fraction_le {N : ℕ} (H : selfAdjoint (Register N)) (α u a T : ℝ)
    (A : Set ℝ) (h : ∀ v ∈ visitSet H 0 α, v+u ∈ A) (ha : a ≤ T) :
    visitFraction H 0 α (a-u) (T-u) ≤ volume.real (A ∩ Icc a T)/(T-a) := by
  let F := visitSet H 0 α ∩ Icc (a-u) (T-u)
  have hclosed : IsClosed (visitSet H 0 α) := by
    change IsClosed {t | HasProjectiveCircuitApproximation N α 0 (unitaryEvolution H.val t)}
    simp only [hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H 0).continuous continuous_const
  have he := (measurePreserving_add_right volume (-u)).measureReal_preimage (s:=F)
    (hclosed.measurableSet.inter measurableSet_Icc).nullMeasurableSet
  change volume.real F/((T-u)-(a-u)) ≤ _
  rw [sub_sub_sub_cancel_right,←he]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ha)
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  intro w hw
  have hm : w+-u ∈ visitSet H 0 α ∧ w+-u ∈ Icc (a-u) (T-u) := hw
  exact ⟨by simpa only [neg_add_cancel_right] using h _ hm.1,
    by linarith only [hm.2.1],by linarith only [hm.2.2]⟩

/-- On a fixed Gaussian chain the sharp exponential base of occupation at
error 1/10 is attained even by dates where the least cost is arbitrarily
close to one gate per bond. The observation origin can depend on the draw. -/
theorem gaussian_physical_density_band_rate :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let q : ℝ := 1/(k+1:ℕ)
      ∀ l b : ℝ, 0 < l → l < physicalArc (1/10) → physicalArc (1/10) < b →
      ∀ᶠ n : ℕ in atTop,
        let N := n+3
        let D := 2^N
        let H : selfAdjoint (Register N) :=
          ⟨pathHamiltonian (pathPauliDisorderShell ω (n+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
          let f := volume.real (densityBand H (1/10) ((1-8*q)*(N-1:ℕ)) ∩ Icc a T)/(T-a)
          l^D < f ∧ f < b^D := by
  filter_upwards [gaussian_scalar_shift_to_density_band,gaussian_cheap_occupation_rate] with ω hshift hocc k
  intro q l b hl hlx hxb
  let x := physicalArc (1/10)
  have hsmall : (1/10:ℝ) < sqrt 2 := by
    have : (1:ℝ) ≤ sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith only [this]
  obtain ⟨hx,hε⟩ := physicalArc_spec (by norm_num : (0:ℝ) < 1/10) hsmall
  obtain ⟨y,hly,hyx⟩ := exists_between hlx
  have hy : y ∈ Ioo (0:ℝ) (1/2) := ⟨hl.trans hly,hyx.trans hx.2⟩
  let α := zeroGateArcTolerance y
  have hα : α < 1/10 := by
    rw [←hε]
    exact strictMonoOn_zeroGateArcTolerance ⟨hy.1.le,hy.2.le⟩ ⟨hx.1.le,hx.2.le⟩ hyx
  obtain ⟨A,K,hA,hK,hshift'⟩ := hshift k
  have hlower := hocc _ (polynomial_subcritical 1) y hy l b hl.le hly (hyx.trans hxb)
  have hupper := hocc _ (polynomial_subcritical 1) x hx l b hl.le hlx hxb
  obtain ⟨J,hJ⟩ := exists_nat_ge (K/(1/10-α))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hshift',hlower,hupper,eventually_ge_atTop J] with n hs hL hU hn
  intro N D H a
  let m : ℝ := ((n+1+1:ℕ):ℝ)
  let u := A/m
  have hm : 0 < m := by dsimp [m]; positivity
  have hJ' : (J:ℝ) ≤ m := by dsimp [m]; exact_mod_cast (by omega : J ≤ n+1+1)
  have herr : α ≤ 1/10-K/m := by
    have hh := (div_le_iff₀ (sub_pos.mpr hα)).mp (hJ.trans hJ')
    have hpay : K/m ≤ 1/10-α := (div_le_iff₀ hm).mpr (by linarith only [hh])
    linarith only [hpay]
  let B := densityBand H (1/10) ((1-8*q)*(N-1:ℕ))
  have hband (v : ℝ) (hv : v ∈ visitSet H 0 α) : v+u ∈ B := by
    obtain ⟨z,hz,C,hC,he⟩ := hv
    exact hs v ⟨z,hz,C,hC,he.trans herr⟩
  have hT : Tendsto (fun T : ℝ => T-u) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using (tendsto_atTop_add_const_right atTop (-u) tendsto_id)
  filter_upwards [hT.eventually (hL (a-u)),hU a,eventually_ge_atTop a] with T hL' hU' ha
  have hl' := (hL' 0 (Nat.zero_le _)).1
  have hu' := (hU' (N-1) (by simpa only [pow_one] using Nat.sub_le N 1)).2
  rw [hε] at hu'
  refine ⟨hl'.trans_le (shifted_fraction_le H α u a T B hband ha),lt_of_le_of_lt ?_ hu'⟩
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ha)
  exact measureReal_mono (inter_subset_inter_left _ (fun _ ht => ht.1))
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

#print axioms gaussian_physical_density_band_rate
end
end GaloisForLFunctions.HTGeometry.SpanningOccupation
