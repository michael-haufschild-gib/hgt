import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.Sampling.PatchBounds

/-! # Positive density of disjoint calibrated physical triples -/
open MeasureTheory Filter Set Real Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- One finite family per prefix works simultaneously at every date and
for every circuit. The calibration uses only the local Gaussian rows. -/
theorem gaussian_guarded_family :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let u := pathPauliDisorderShell ω n
      ∃ (F : Finset ℕ) (e f : F→Fin (n+1)), c*((n+1:ℕ):ℝ)≤(F.card:ℝ) ∧
        (∀ i, (e i).succ=(f i).castSucc) ∧
        (∀ i j, i≠j → Disjoint (incidentSites (tripleSites (e i) (f i))) (incidentSites (tripleSites (e j) (f j)))) ∧
        ∀ i, let d := ‖pathHamiltonian (packetPerturbation (e i) (f i) u)‖
             let S := incidentSites (tripleSites (e i) (f i))
             let E := ∑ l∈S.biUnion pathIncidentLabels, |u l|
             4*d*(2*E+d)≤1/256 := by
  classical
  obtain ⟨c,hc,hboxes⟩ := gaussian_guarded_box_density (by norm_num : (0:ℝ)<1/10^9)
  refine ⟨c/24,by positivity,?_⟩
  have hdiv : Tendsto (fun n : ℕ => (n+1)/12) atTop atTop := by
    apply tendsto_atTop.mpr
    intro a
    filter_upwards [eventually_ge_atTop (12*a)] with n hn
    omega
  filter_upwards [hboxes] with ω hw
  filter_upwards [hdiv.eventually hw,eventually_ge_atTop (24:ℕ)] with n hn hlong
  let m := (n+1)/12
  let F := guardedBoxes (1/10^9) ω m
  have hlen (p : F) : p.val < m := mem_range.mp (mem_filter.mp p.property).1
  let e (p : F) : Fin (n+1) := ⟨4*(3*p.val+1)+1,by have := hlen p; dsimp only [m] at this; omega⟩
  let f (p : F) : Fin (n+1) := ⟨4*(3*p.val+1)+2,by have := hlen p; dsimp only [m] at this; omega⟩
  have hadj (p : F) : (e p).succ=(f p).castSucc := Fin.ext rfl
  have hdis (p q : F) (hpq : p≠q) :
      Disjoint (incidentSites (tripleSites (e p) (f p))) (incidentSites (tripleSites (e q) (f q))) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    have h₁ := guarded_site_bounds (e:=e p) (f:=f p) (k:=p.val) rfl rfl hv
    have h₂ := guarded_site_bounds (e:=e q) (f:=f q) (k:=q.val) rfl rfl hv'
    exact hpq (Subtype.ext (by omega))
  have hcal (p : F) := guarded_perturbation_bound (e:=e p) (f:=f p) (k:=p.val) rfl rfl ω
    (mem_filter.mp p.property).2
  have hN : ((n+1:ℕ):ℝ)≤24*(m:ℝ) := by
    exact_mod_cast (show n+1≤24*m by dsimp only [m]; omega)
  have hcard : c*((n+1:ℕ):ℝ)/24≤(F.card:ℝ) := by
    change c*(m:ℝ)≤(F.card:ℝ) at hn
    linarith only [mul_le_mul_of_nonneg_left hN hc.le,hn]
  refine ⟨F,e,f,?_,hadj,hdis,hcal⟩
  linarith only [hcard]

#print axioms gaussian_guarded_family
end
end GaloisForLFunctions.HTGeometry.RepeatedGates.PhysicalBlocks.CollectiveSignals
