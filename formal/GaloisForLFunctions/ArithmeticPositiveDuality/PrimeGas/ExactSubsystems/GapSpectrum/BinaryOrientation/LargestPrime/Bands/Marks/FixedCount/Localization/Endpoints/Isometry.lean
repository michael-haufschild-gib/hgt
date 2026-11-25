import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.JointLaw
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Cuts

/-! # Norm-preserving composition detected by dispersion in one fixed-count prime band -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

open Filter Topology Set MeasureTheory
open scoped NNReal
attribute [local instance] Classical.propDecidable

private theorem dirac_read {X : Type*} [MeasurableSpace X] (x : X) {F : Set X} (hF : MeasurableSet F) :
    (diracProba x F : ℝ) = if x ∈ F then 1 else 0 := by
  classical
  rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn,Measure.real,diracProba_toMeasure_apply' x hF]
  by_cases hx : x ∈ F <;> simp [hx]

private theorem critical_cut {c b d : ℝ} (hc : 0 < c) (hcb : c < b) (hbd : b < d) (k : ℕ) :
    (orderStatistics k (draw hc (hcb.trans hbd).le 0) (allIn k (Iic b)) : ℝ) = (Real.log (b/c)/Real.log (d/c))^k := by
  have hm {t : ℝ} (ht : 0 < t) : VacuumCalibration.mass c t 0 = Real.log (t/c) := by
    simp only [VacuumCalibration.mass,neg_zero,zero_mul,Real.exp_zero,integral_one_div_of_pos hc ht]
  rw [orderStatistics_allIn _ _ measurableSet_Iic,NNReal.coe_pow,draw_cut hc hcb.le hbd.le (hcb.trans hbd),hm (hc.trans hcb),hm (hc.trans (hcb.trans hbd))]

private theorem proper_cut {c b d : ℝ} (hc : 0 < c) (hcb : c < b) (hbd : b < d) {k : ℕ} (hk : 0 < k) :
    (Real.log (b/c)/Real.log (d/c))^k ∈ Ioo (0:ℝ) 1 := by
  have hb := Real.log_pos ((one_lt_div hc).mpr hcb)
  have hd := Real.log_pos ((one_lt_div hc).mpr (hcb.trans hbd))
  have hlt := Real.log_lt_log (div_pos (hc.trans hcb) hc) (div_lt_div_of_pos_right hbd hc)
  exact ⟨pow_pos (div_pos hb hd) k,pow_lt_one₀ (div_pos hb hd).le ((div_lt_one hd).mpr hlt) hk.ne'⟩

/-- At the critical temperature, every positive count leaves genuine randomness in the spectrum. -/
theorem critical_nonDirac {c d : ℝ} (hc : 0 < c) (hcd : c < d) {k : ℕ} (hk : 0 < k) (z : Fin k → ℝ) :
    orderStatistics k (draw hc hcd.le 0) ≠ diracProba z := by
  obtain ⟨b,hcb,hbd⟩ := exists_between hcd
  let C := allIn k (Iic b)
  have hm : MeasurableSet C := MeasurableSet.univ_pi fun _ => measurableSet_Iic
  have hv := critical_cut hc hcb hbd k
  have hp := proper_cut hc hcb hbd hk
  intro he
  change (orderStatistics k (draw hc hcd.le 0) C : ℝ) = _ at hv
  rw [he,dirac_read z hm] at hv
  by_cases hz : z ∈ C
  · rw [if_pos hz] at hv
    exact hp.2.ne hv.symm
  · rw [if_neg hz] at hv
    exact hp.1.ne hv

/-- Isometric splitting is exactly the existence of a non-Dirac limit for one fixed-count band. -/
theorem split_isometric_iff_nonDirac {c d : ℝ} (hc : 0 < c) (hcd : c < d) (s : ℂ) {k : ℕ} (hk : 0 < k) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ∃ μ : ProbabilityMeasure (Fin k → ℝ),
        Tendsto (fun h => thermalLaw c d h (2*s.re) k) criticalApproach (𝓝 μ) ∧ ∀ z, μ ≠ diracProba z := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  rw [split_isometric_iff]
  constructor
  · intro hs
    rw [show 2*s.re=1 by rw [hs]; ring]
    exact ⟨_,at_one hc hcd k,critical_nonDirac hc hcd hk⟩
  · rintro ⟨μ,hμ,hnd⟩
    rcases lt_trichotomy (2*s.re) 1 with h | h | h
    · exact False.elim (hnd _ (tendsto_nhds_unique hμ (below hc hcd h hk)))
    · linarith only [h]
    · exact False.elim (hnd _ (tendsto_nhds_unique hμ (above hc hcd h hk)))

private theorem cut_from_dirac {k : ℕ} (hk : 0 < k) {z b : ℝ} (hne : z ≠ b)
    {ν : Ioi (0:ℝ) → ProbabilityMeasure (Fin k → ℝ)}
    (H : Tendsto ν criticalApproach (𝓝 (diracProba (fun _ : Fin k => z)))) :
    Tendsto (fun h => (ν h (allIn k (Iic b)) : ℝ)) criticalApproach (𝓝 (if z < b then 1 else 0)) := by
  let C := allIn k (Iic b)
  let v (_ : Fin k) := z
  have hC : IsClosed C := isClosed_set_pi fun _ _ => isClosed_Iic
  have hmem : v ∈ C ↔ z ≤ b := ⟨fun hh => hh ⟨0,hk⟩ (mem_univ _),fun hz _ _ => hz⟩
  have hf : v ∉ frontier C := by
    rw [frontier,hC.closure_eq]
    intro hv
    rcases lt_or_gt_of_ne hne with h | h
    · have hsub : allIn k (Iio b) ⊆ C := by
        intro x hx i hi
        exact (show x i < b from hx i hi).le
      have ho : IsOpen (allIn k (Iio b)) := isOpen_set_pi (Set.toFinite _) fun _ _ => isOpen_Iio
      exact hv.2 (interior_maximal hsub ho (show v ∈ allIn k (Iio b) from fun _ _ => h))
    · exact h.not_ge (hmem.mp hv.1)
  have hzero : diracProba v (frontier C) = 0 := by
    have he := dirac_read v (isClosed_frontier (s := C)).measurableSet
    rw [if_neg hf] at he
    exact_mod_cast he
  have hh := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto (E := C) H hzero
  have hh' := (NNReal.continuous_coe.tendsto _).comp hh
  change Tendsto (fun h => (ν h C : ℝ)) criticalApproach (𝓝 (diracProba v C : ℝ)) at hh'
  rw [dirac_read v hC.measurableSet] at hh'
  rcases lt_or_gt_of_ne hne with h | h
  · simpa only [if_pos (hmem.mpr h.le),if_pos h] using hh'
  · simpa only [if_neg (fun hv => h.not_ge (hmem.mp hv)),if_neg h.not_gt] using hh'

/-- A single interior maximum cut has an interior limiting probability exactly at isometric damping. -/
theorem split_isometric_iff_interior_cut {c b d : ℝ} (hc : 0 < c) (hcb : c < b) (hbd : b < d)
    (s : ℂ) {k : ℕ} (hk : 0 < k) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      ∃ p ∈ Ioo (0:ℝ) 1, Tendsto (fun h => (thermalLaw c d h (2*s.re) k (allIn k (Iic b)) : ℝ))
        criticalApproach (𝓝 p) := by
  letI : NeBot criticalApproach := criticalApproach_neBot
  rw [split_isometric_iff]
  constructor
  · intro hs
    rw [show 2*s.re=1 by rw [hs]; ring]
    refine ⟨_,proper_cut hc hcb hbd hk,?_⟩
    simpa only [conditional,thermalLaw,zero_mul,add_zero] using critical_all_below_limit hc hcb.le hbd.le (hcb.trans hbd) k
  · rintro ⟨p,hp,hP⟩
    rcases lt_trichotomy (2*s.re) 1 with h | h | h
    · have he := tendsto_nhds_unique hP (cut_from_dirac hk hbd.ne' (below hc (hcb.trans hbd) h hk))
      rw [if_neg hbd.not_gt] at he
      exact False.elim (hp.1.ne' he)
    · linarith only [h]
    · have he := tendsto_nhds_unique hP (cut_from_dirac hk hcb.ne (above hc (hcb.trans hbd) h hk))
      rw [if_pos hcb] at he
      exact False.elim (hp.2.ne he)

#print axioms split_isometric_iff_interior_cut
#print axioms critical_nonDirac
#print axioms split_isometric_iff_nonDirac

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints
