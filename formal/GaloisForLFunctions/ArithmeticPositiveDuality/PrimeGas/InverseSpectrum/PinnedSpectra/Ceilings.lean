import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Fibers
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.Families

/-! # Physical spectra satisfying every moment ceiling at once -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

def ceilingFiber (h : ℝ) : Set (SpectralBand 1) := {b | ∀ q : GibbsExponent, momentLoss q b ≤ h^q.val}

/-- At positive resolution only a finite prefix is frozen. The remaining including endpoint choices are unrestricted within the band. -/
theorem ceilingFiber_eq_prefix {h : ℝ} (hh : 0 < h) : ∃ N, ceilingFiber h = prefixFiber N (hotEdge 1) := by
  classical
  have hex : ∃ k, occupationWeight k ≤ h := by
    obtain ⟨k,hk⟩ := (occupationWeight_tendsto.eventually_lt_const hh).exists
    exact ⟨k,hk.le⟩
  let N := Nat.find hex
  have hcut (k : ℕ) : h < occupationWeight k ↔ k < N := by
    constructor
    · intro hk
      exact lt_of_not_ge (fun hge => hk.not_ge ((occupationWeight_antitone hge).trans (Nat.find_spec hex)))
    · intro hk
      exact lt_of_not_ge (Nat.find_min hex hk)
  refine ⟨N,?_⟩
  ext b
  change (∀ q : GibbsExponent, momentLoss q b ≤ h^q.val) ↔ ∀ k < N, b k = hotEdge 1 k
  rw [all_moment_ceilings_iff b hh.le]
  exact ⟨fun hc k hk => Subtype.ext (hc k ((hcut k).mpr hk)),fun hc k hk => congrArg Subtype.val (hc k ((hcut k).mp hk))⟩

theorem closure_physical_ceilings {h : ℝ} (hh : 0 < h) : closure (physicalSpectra 1 ∩ ceilingFiber h) = ceilingFiber h := by
  obtain ⟨N,hN⟩ := ceilingFiber_eq_prefix hh
  rw [hN,closure_physical_fiber]

theorem physical_intermediate_on_ceilings {h y : ℝ} (hh : 0 < h) {b c : SpectralBand 1}
    (hb : b ∈ ceilingFiber h) (hc : c ∈ ceilingFiber h) {F : SpectralBand 1 → ℝ} (hF : Continuous F)
    (hl : F b < y) (hu : y < F c) : ∃ d ∈ physicalSpectra 1 ∩ ceilingFiber h, F d = y := by
  obtain ⟨N,hN⟩ := ceilingFiber_eq_prefix hh
  rw [hN] at hb hc ⊢
  exact physical_intermediate_on_fiber hb hc hF hl hu

/-- A strict partition response survives physical approximation while every positive order stays within its ceiling. -/
theorem physical_all_orders_probe {σ t R : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    ∃ b ∈ physicalSpectra 1 ∩ ceilingFiber (1/R),
      (highWindowFactor σ/5)*(t/R^σ) < ‖relativePartition b (⟨σ,t⟩:ℂ)‖ := by
  have hpos := (zero_lt_one.trans_le ht).trans_le hR
  obtain ⟨b,hb,hD⟩ := common_tail_profile hs ht hR
  have hmem : b ∈ closure (physicalSpectra 1 ∩ ceilingFiber (1/R)) := by
    rw [closure_physical_ceilings (one_div_pos.mpr hpos)]
    intro q
    exact (hD q).le.trans_eq (by rw [one_div R,Real.inv_rpow hpos.le,one_div])
  let U := {c : SpectralBand 1 | (highWindowFactor σ/5)*(t/R^σ) < ‖relativePartition c (⟨σ,t⟩:ℂ)‖}
  have hu : IsOpen U := isOpen_lt continuous_const (continuous_relativePartition_spectrum (z := ⟨σ,t⟩) hs 1).norm
  obtain ⟨c,hc,hphys⟩ := mem_closure_iff.mp hmem U hu hb
  exact ⟨c,hphys,hc⟩

/-- Every positive amplitude up to the uniform lower bound occurs exactly under all the moment tests. -/
theorem exact_amplitude_under_all_orders {σ t R y : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R)
    (hy : 0 < y) (hcap : y ≤ (highWindowFactor σ/5)*(t/R^σ)) :
    ∃ b ∈ physicalSpectra 1 ∩ ceilingFiber (1/R), ‖relativePartition b (⟨σ,t⟩:ℂ)‖ = y := by
  have hh := one_div_pos.mpr ((zero_lt_one.trans_le ht).trans_le hR)
  obtain ⟨b,hb,hamp⟩ := physical_all_orders_probe hs ht hR
  have hhot : hotEdge 1 ∈ ceilingFiber (1/R) := (all_moment_ceilings_iff _ hh.le).mpr (fun _ _ => rfl)
  exact physical_intermediate_on_ceilings hh hhot hb.2 (continuous_relativePartition_spectrum (z := ⟨σ,t⟩) hs 1).norm
    (by simpa only [relativePartition_hot,norm_zero] using hy) (hcap.trans_lt hamp)

#print axioms ceilingFiber_eq_prefix
#print axioms closure_physical_ceilings
#print axioms physical_all_orders_probe
#print axioms exact_amplitude_under_all_orders

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
