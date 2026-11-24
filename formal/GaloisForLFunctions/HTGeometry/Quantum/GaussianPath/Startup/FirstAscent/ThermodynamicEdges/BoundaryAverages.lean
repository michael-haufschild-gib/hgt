import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BoundaryMass

/-! # Gaussian cost of separating finite blocks -/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
noncomputable section

def meanAbsoluteField := ∫ x : ℝ, |x| ∂gaussianReal 0 1

private theorem integral_coordinate {L : ℕ} (p : RowBlock L) :
    (∫ u : RowBlock L→ℝ, |u p| ∂Measure.infinitePi fun _ : RowBlock L => gaussianReal 0 1)=meanAbsoluteField := by
  let γ := gaussianReal 0 1
  let μ := Measure.infinitePi fun _ : RowBlock L => γ
  have h := measurePreserving_eval_infinitePi (fun _ : RowBlock L => γ) p
  have he : IdentDistrib (Function.eval p) id μ γ :=
    ⟨h.measurable.aemeasurable,measurable_id.aemeasurable,by rw [Measure.map_id]; exact h.map_eq⟩
  exact (he.comp measurable_abs).integral_eq

/-- Each complete seam contributes nine absolute standard Gaussians. -/
theorem gaussian_seam_average :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : ℕ, Tendsto
      (fun k : ℕ => (∑ j ∈ range k, seamMass m (readRows (m+2) ω j))/k) atTop (𝓝 (9*meanAbsoluteField)) := by
  apply ae_all_iff.mpr
  intro m
  let μ := Measure.infinitePi fun _ : RowBlock (m+2) => gaussianReal 0 1
  have hi (p : Fin 3 × Fin 3) := integrable_row_abs (L:=m+2) (Fin.last (m+1),.inr p)
  have he : (∫ u, seamMass m u ∂μ)=9*meanAbsoluteField := by
    unfold seamMass
    rw [integral_finsetSum _ (fun p _ => hi p)]
    simp only [integral_coordinate,Finset.sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul]
    norm_num
  rw [←he]
  exact block_strong_law _ _ (by unfold seamMass; fun_prop) (integrable_finsetSum _ fun p _ => hi p)

private theorem last_of_average {a : ℕ→ℝ} {c : ℝ}
    (h : Tendsto (fun k : ℕ => (∑ j ∈ range k, a j)/k) atTop (𝓝 c)) :
    Tendsto (fun k : ℕ => a k/k) atTop (𝓝 0) := by
  have hR : Tendsto (fun k : ℕ => 1+1/(k:ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x:=(1:ℝ))).add (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ))
  have hh := ((h.comp (tendsto_add_atTop_nat 1)).mul hR).sub h
  rw [mul_one,sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (k:ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
  have hk₁ : (k:ℝ)+1≠0 := by positivity
  change (∑ j ∈ range (k+1),a j)/((k+1:ℕ):ℝ)*(1+1/(k:ℝ))-(∑ j ∈ range k,a j)/(k:ℝ)=_
  rw [sum_range_succ,Nat.cast_add_one]
  field_simp [hk',hk₁]
  ring

/-- Even the entire last row block has vanishing mass per complete block. -/
theorem gaussian_last_block :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ L : ℕ, Tendsto
      (fun k : ℕ => rowMass L (readRows L ω k)/k) atTop (𝓝 0) := by
  apply ae_all_iff.mpr
  intro L
  have h := block_strong_law L (rowMass L) (by unfold rowMass; fun_prop)
    (integrable_finsetSum _ fun p _ => integrable_row_abs (L:=L) p)
  filter_upwards [h] with ω hω
  exact last_of_average hω

#print axioms gaussian_seam_average
#print axioms gaussian_last_block
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
