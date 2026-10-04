import GaloisForLFunctions.RHTower.RoutePNativeMassCoprimeAsymptotic
import GaloisForLFunctions.RHTower.RoutePNativeUndampedBalance

/-!
# Admission selects zero causal mass compensation

For physical damping between zero and one, the original native carrier
has an admitted complete coprime source. Every nonzero causal mass
compensation introduces a positive exponential source and loses that
admission. This concerns the single causal residual family; it makes no
claim about separately chosen zero-mass completions at each cutoff.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

private theorem weighted_source (lam eta t : ℝ) :
    Real.exp (-eta * t) * routePNativeMassCoprimeSource lam t =
      Real.exp ((1 - eta) * t) *
        (Real.exp (-t) * routePNativeMassCoprimeSource lam t) := by
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Nonzero causal compensation destroys the complete coprime-source
admission throughout the damping range needed by the native route. -/
theorem not_integrableOn_routePNativeMassCoprimeSource
    {lam eta : ℝ} (hlam : lam ≠ 0) (heta : eta ≤ 1) :
    ¬ IntegrableOn (fun t => Real.exp (-eta * t) * routePNativeMassCoprimeSource lam t)
      (Ioi 0) := by
  intro hi
  let c := routePNativeMassCoprimePole lam
  have hc : 0 < c := routePNativeMassCoprimePole_pos hlam
  have hlate := (routePNativeMassCoprimeSource_asymptotic lam).eventually
    (eventually_gt_nhds (show c / 2 < c by linarith))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hlate
  let A := max T 0
  have hA : 0 ≤ A := le_max_right _ _
  have hbound (t : ℝ) (ht : t ∈ Ioi A) :
      c / 2 ≤ ‖Real.exp (-eta * t) * routePNativeMassCoprimeSource lam t‖ := by
    have ht0 : 0 ≤ t := hA.trans ht.le
    have htT : T ≤ t := (le_max_left T 0).trans ht.le
    have hn := hT t htT
    have he : 1 ≤ Real.exp ((1 - eta) * t) :=
      Real.one_le_exp_iff.mpr (mul_nonneg (sub_nonneg.mpr heta) ht0)
    have hN : 0 ≤ Real.exp (-t) * routePNativeMassCoprimeSource lam t := by linarith
    calc
      c / 2 ≤ Real.exp (-t) * routePNativeMassCoprimeSource lam t := hn.le
      _ ≤ Real.exp ((1 - eta) * t) *
          (Real.exp (-t) * routePNativeMassCoprimeSource lam t) :=
        le_mul_of_one_le_left hN he
      _ = Real.exp (-eta * t) * routePNativeMassCoprimeSource lam t :=
        (weighted_source lam eta t).symm
      _ ≤ _ := le_abs_self _
  have ht := hi.mono_set (Ioi_subset_Ioi hA)
  have hconst : IntegrableOn (fun _ : ℝ => c / 2) (Ioi A) := by
    apply ht.norm.mono' continuous_const.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t hta
    rw [Real.norm_eq_abs, abs_of_pos (half_pos hc)]
    exact hbound t hta
  have hfilter : IntegrableAtFilter (fun _ : ℝ => c / 2) atTop volume :=
    ⟨Ioi A, Ioi_mem_atTop _, hconst⟩
  have hz : c / 2 = 0 := hfilter.eq_zero_of_tendsto (by
    intro s hs
    obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
    rw [← top_le_iff, ← Real.volume_Ici (a := b)]
    exact measure_mono hb) tendsto_const_nhds
  linarith

private theorem zero_source_balance {t : ℝ} (ht : 0 ≤ t) :
    routePNativeMassCoprimeSource 0 t =
      routePNativeCriticalProfile t ^ 2 + routePNativeCriticalCoprimeWork t := by
  rw [routePNativeMassCoprimeSource, routePNativeMassCoprimeProfile_zero,
    logarithmicCoprimeEnergy_eq_endpoint_add_cross _ ht]
  simp only [routePCoprimeNativeProfile, routePNativeCriticalProfile,
    routePNativeCriticalCoprimeWork, mul_pow, Real.sq_sqrt (Real.exp_pos (-t)).le]
  ring

private theorem zero_source_admission {eta : ℝ} (heta : 0 ≤ eta) :
    IntegrableOn (fun t => Real.exp (-eta * t) * routePNativeMassCoprimeSource 0 t) (Ioi 0) := by
  have hi : IntegrableOn (routePNativeMassCoprimeSource 0) (Ioi 0) := by
    apply IntegrableOn.congr_fun routePNativeCriticalBalance_integrable_zero.1 _ measurableSet_Ioi
    intro t ht
    exact (zero_source_balance ht.le).symm
  have he : Continuous (fun t : ℝ => Real.exp (-eta * t)) := by fun_prop
  apply hi.norm.mono' (he.aestronglyMeasurable.restrict.mul hi.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  change ‖Real.exp (-eta * t) * routePNativeMassCoprimeSource 0 t‖ ≤
    ‖routePNativeMassCoprimeSource 0 t‖
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hw : Real.exp (-eta * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht])
  exact mul_le_of_le_one_left (norm_nonneg _) hw

/-- Sharp classification on the actual causal compensation family. The
original source admission survives exactly at compensation coefficient zero. -/
theorem routePNativeMassCoprimeSource_integrable_iff_zero
    (lam : ℝ) {eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    IntegrableOn (fun t => Real.exp (-eta * t) * routePNativeMassCoprimeSource lam t)
      (Ioi 0) ↔ lam = 0 := by
  constructor
  · intro hi
    by_contra hlam
    exact not_integrableOn_routePNativeMassCoprimeSource hlam heta1 hi
  · rintro rfl
    exact zero_source_admission heta0

end RHTower
