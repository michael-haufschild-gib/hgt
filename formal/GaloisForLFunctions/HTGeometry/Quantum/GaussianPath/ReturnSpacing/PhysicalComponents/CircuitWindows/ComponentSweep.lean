import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.GaussianLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondMass
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass
import GaloisForLFunctions.HTGeometry.Quantum.PathPauliSpectralWidth

/-! # One bond sweep transfers circuits across an entire scalar visit -/
open Filter MeasureTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- Any interval inside a scalar tube of width below a semicircle has
length at most A/N. A circuit affordable at its right endpoint transports
to the left endpoint with N−1 extra gates and B/N extra error. -/
theorem gaussian_component_sweep :
    ∃ A B : ℝ, 0<A ∧ 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ ρ∈Ioo (0:ℝ) (sqrt 2), ∀ u v : ℝ, u≤v → Icc u v ⊆ visitSet H 0 ρ →
        v-u≤A/N ∧ ∀ s δ, v∈visitSet H s δ → u∈visitSet H (s+(n+1)) (δ+B/N) := by
  obtain ⟨a,b,ha,hb,hm⟩ := gaussian_path_eventual_coefficient_mass
  let A := π/a
  have hA : 0<A := div_pos pi_pos ha
  refine ⟨A,84*b*A^2,hA,by positivity,?_⟩
  filter_upwards [hm] with ω hm
  filter_upwards [hm] with n hm
  intro N H ρ hρ u v huv hs
  let p := pathPauliDisorderShell ω n
  let E := H.2.isHermitian.eigenvalues
  obtain ⟨i,j,hij,_⟩ := exists_path_spectral_width_ge_onsite p
  have hgap : 2*(a*(N:ℝ))≤E i-E j := (mul_le_mul_of_nonneg_left hm.1 (by norm_num : (0:ℝ)≤2)).trans hij
  let w := fun j => -E j/(2*π)
  have hw : a*(N:ℝ)/π≤w j-w i := by
    change a*(N:ℝ)/π≤ -E j/(2*π)-(-E i/(2*π))
    rw [←sub_div]
    apply (div_le_div_iff₀ pi_pos (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right hgap pi_pos.le
    linarith only [h]
  have hx := (physicalArc_spec hρ.1 hρ.2).1
  have hh := visit_interval_width hx.1.le hx.2 huv (fun t ht => (physical_visit H hρ.1 hρ.2 t).mpr (hs ht)) j i
  have hprod : (v-u)*(a*(N:ℝ)/π)≤1 :=
    (mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr huv)).trans (hh.trans (by linarith only [hx.2]))
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hlag : v-u≤A/N := by
    apply (le_div_iff₀ hN).mpr
    apply (le_div_iff₀ ha).mpr
    have hv : (v-u)*(a*(N:ℝ))/π≤1 := by rwa [mul_div_assoc]
    have h := (div_le_iff₀ pi_pos).mp hv
    linarith only [h]
  refine ⟨hlag,?_⟩
  intro s δ hv
  obtain ⟨z,hz,C,hC,he⟩ := BondProducts.bond_sweep_error p (v-u) (sub_nonneg.mpr huv) 1 (by decide)
  have herr : (v-u)^2*(84*‖p‖^2)≤84*b*A^2/N := calc
    _ ≤ (A/N)^2*(84*(b*(N:ℝ))) := mul_le_mul
      (sq_le_sq' (by linarith only [sub_nonneg.mpr huv,div_pos hA hN]) hlag)
      (mul_le_mul_of_nonneg_left hm.2 (by norm_num)) (by positivity) (sq_nonneg _)
    _ = _ := by field_simp [hN.ne']
  simp only [Nat.cast_one,div_one] at he
  have hsim : HasProjectiveCircuitApproximation N (84*b*A^2/N) (n+1) (unitaryEvolution H.val (v-u)) :=
    ⟨z,hz,C,by simpa only [one_mul] using hC.le,he.trans herr⟩
  have h := affordable_add_time H hv (hsim.neg_time H)
  rwa [show v+ -(v-u)=u by ring] at h

#print axioms gaussian_component_sweep
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents.CircuitWindows
