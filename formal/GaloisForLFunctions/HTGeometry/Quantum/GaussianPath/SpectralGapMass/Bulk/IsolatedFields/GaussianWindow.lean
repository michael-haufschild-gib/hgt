import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.Overlap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.IsolatedFields.Selection
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldDensity
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PhysicalTimes.TraceDecay

/-! # Loss of circuit overlap on the inverse-square-root time scale -/
open Matrix Real Finset MeasureTheory Filter
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- An arbitrarily small upper bound on normalized overlap holds for
all circuits of sufficiently small positive gate density, simultaneously
throughout the short-time window Nt² ≥ A, |t| ≤ 1. -/
theorem gaussian_small_gate_overlap {κ : ℝ} (hκ : 0<κ) :
    ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, A ≤ (n+2:ℕ)*t^2 → |t|≤1 → ∀ C : TwoQubitCircuit (n+2),
      (C.gateCount:ℝ) ≤ c*(n+2:ℕ) →
      ‖(C.eval.valᴴ*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t).trace‖/
        (2:ℝ)^(n+2) < κ := by
  classical
  obtain ⟨L,δ,hL,hδ,hsel⟩ := select_spin_count hκ
  obtain ⟨p,hp,h⟩ := gaussian_path_eventual_isolated_sites 1 δ hδ
  refine ⟨2*L/p,p/4,by positivity,by positivity,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  obtain ⟨S,hcard,hgood⟩ := hn
  intro t hlate htime C hsmall
  let R := S \ C.touchedSites
  have ht : t≠0 := by
    intro he
    rw [he,zero_pow (by decide : 2≠0),mul_zero] at hlate
    exact (show 0<2*L/p by positivity).not_ge hlate
  have hrem := Finset.card_sdiff_add_card_inter S C.touchedSites
  have hint := (card_le_card (inter_subset_right : S∩C.touchedSites ⊆ C.touchedSites)).trans C.card_touchedSites_le
  have hR : (p/2)*(n+2:ℕ) ≤ (R.card:ℝ) := by
    have he : (R.card:ℝ)+((S∩C.touchedSites).card:ℝ)=(S.card:ℝ) := by exact_mod_cast hrem
    have hc : ((S∩C.touchedSites).card:ℝ)≤2*(C.gateCount:ℝ) := by exact_mod_cast hint
    linarith only [he,hc,hcard,hsmall]
  have hmass : L ≤ (R.card:ℝ)*t^2 := by
    have he := (div_le_iff₀ hp).mp hlate
    nlinarith only [he,mul_le_mul_of_nonneg_right hR (sq_nonneg t)]
  obtain ⟨m,hm,hbound⟩ := hsel t (abs_pos.mpr ht) htime R.card hmass
  obtain ⟨T,hT,hsize⟩ := exists_subset_card_eq hm
  have hsub (i) (hi : i∈T) := Finset.mem_sdiff.mp (hT hi : i∈S \ C.touchedSites)
  have hfit := isolated_spin_overlap (pathPauliDisorderShell ω n) T C hδ.le
    (fun i hi => hgood i (hsub i hi).1) (disjoint_left.mpr (fun i hi => (hsub i hi).2)) t
  rw [hsize] at hfit
  exact hfit.trans_lt hbound

/-- The empty circuit detects the normalized spectral trace. -/
theorem gaussian_startup_trace {κ : ℝ} (hκ : 0<κ) :
    ∃ A > 0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, A ≤ (n+2:ℕ)*t^2 → |t|≤1 → ‖PhysicalTimes.amplitude ω n t‖ < κ := by
  obtain ⟨A,c,hA,hc,h⟩ := gaussian_small_gate_overlap hκ
  refine ⟨A,hA,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro t ht hs
  have hh := hn t ht hs (TwoQubitCircuit.one (n+2)) (show (0:ℝ) ≤ c*(n+2:ℕ) by positivity)
  simpa only [PhysicalTimes.amplitude,norm_div,norm_pow,Complex.norm_ofNat,
    TwoQubitCircuit.one_eval,OneMemClass.coe_one,Matrix.conjTranspose_one,one_mul] using hh

#print axioms gaussian_small_gate_overlap
#print axioms gaussian_startup_trace
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
