import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.PhysicalBlocks

/-! # Reflection of the Gaussian bonds crossing block boundaries -/

open MeasureTheory ProbabilityTheory Finset Matrix
open scoped Classical Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open SpectralGapMass.Bulk.PeriodicCuts
noncomputable section

private def crossing (L : ℕ) : ℕ × PathPauliDirections → Prop
  | (_, .inl _) => False
  | (r, .inr _) => r/L ≠ (r+1)/L

private theorem crossing_iff {n : ℕ} (L : ℕ) (l : PathLabel n) :
    crossing L (pathPauliSourceCoordinate l) ↔ owner L l=none := by
  have hc (x y : Fin (n+2)) : (if x=y then some x else none)=none ↔ x≠y := by
    by_cases h : x=y <;> simp [h]
  rw [owner,hc,ne_eq,Fin.ext_iff]
  rcases l with ⟨i,a⟩|⟨e,p⟩
  · change False ↔ ¬i.val/L=i.val/L
    simp
  · rfl

/-- Reverse only bonds joining different blocks. -/
def reflectSeams (L : ℕ) (ω : PathPauliDisorder) (i : ℕ × PathPauliDirections) : ℝ :=
  if crossing L i then -ω i else ω i

theorem reflect_preserving (L : ℕ) :
    MeasurePreserving (reflectSeams L) pathPauliDisorderLaw pathPauliDisorderLaw := by
  let f (i : ℕ × PathPauliDirections) (x : ℝ) := if crossing L i then -x else x
  have hf (i) : Measurable (f i) := by
    by_cases h : crossing L i <;> simp [f,h] <;> fun_prop
  refine ⟨measurable_pi_lambda _ (fun i => (hf i).comp (measurable_pi_apply i)),?_⟩
  change (Measure.infinitePi _).map (fun ω i => f i (ω i))=Measure.infinitePi _
  rw [Measure.infinitePi_map_pi _ hf]
  apply congrArg Measure.infinitePi
  funext i
  by_cases hi : crossing L i
  · simpa [f,hi] using (gaussianReal_map_neg 1)
  · simp [f,hi,Measure.map_id']

private theorem width_double {N : ℕ} (H : selfAdjoint (Register N)) :
    2*circuitHamiltonianSpectralWidth H ≤ circuitHamiltonianSpectralWidth (H+H) := by
  obtain ⟨c,hc,_⟩ := exists_optimal_scalarCenteredHamiltonian (H+H)
  obtain ⟨_,_,hmin⟩ := exists_optimal_scalarCenteredHamiltonian H
  have he : (scalarCenteredHamiltonian (H+H) c).val =
      (2:ℂ) • (scalarCenteredHamiltonian H (c/2)).val := by
    change H.val+H.val-(c:ℂ) • 1=(2:ℂ) • (H.val-((c/2:ℝ):ℂ) • 1)
    rw [smul_sub,smul_smul,show (2:ℂ)*((c/2:ℝ):ℂ)=(c:ℂ) by push_cast; ring,two_smul]
  rw [he,norm_smul] at hc
  norm_num only [Complex.norm_ofNat] at hc
  linarith only [hc,hmin (c/2)]

/-- The original and reflected widths dominate twice the sum of complete
block widths because their Hamiltonians average to the disconnected chain. -/
theorem reflected_full_widths (ω : PathPauliDisorder) (m n : ℕ) :
    2*(∑ j ∈ range ((n+2)/(m+2)), blockWidth m (readBlock m ω j)) ≤
      physicalWidth ω n+physicalWidth (reflectSeams (m+2) ω) n := by
  let L := m+2
  let u := pathPauliDisorderShell ω n
  let v := pathPauliDisorderShell (reflectSeams L ω) n
  let K (b) := shellOperator (piece L u b)
  have hrefl (l : PathLabel n) : v l=if owner L l=none then -u l else u l := by
    dsimp only [v,u]
    rw [pathPauliDisorderShell_apply_source,pathPauliDisorderShell_apply_source]
    simp only [reflectSeams,crossing_iff]
  have hcoeff : u+v=(∑ b, piece L u b)+(∑ b, piece L u b) := by
    ext l
    change u l+v l=(∑ b, piece L u b).ofLp l+(∑ b, piece L u b).ofLp l
    rw [WithLp.ofLp_sum,Finset.sum_apply,hrefl]
    cases h : owner L l with
    | none => simp [piece,h]
    | some b => simp [piece,h]
  have hsum : shellOperator u+shellOperator v=(∑ b,K b)+(∑ b,K b) := by
    apply Subtype.ext
    change pathHamiltonianLM n u+pathHamiltonianLM n v=(∑ b,K b).val+(∑ b,K b).val
    rw [AddSubmonoidClass.coe_finsetSum,←map_add,hcoeff,map_add,map_sum]
    rfl
  have hd := width_double (∑ b,K b)
  rw [←hsum,width_sum_disjoint univ (sites (n:=n) L) K (piece_supported L u) (disjoint_sites L)] at hd
  rw [←full_width_sum]
  apply le_trans _ (hd.trans (width_add_le _ _))
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => circuitHamiltonianSpectralWidth_nonneg _)

#print axioms reflected_full_widths
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
