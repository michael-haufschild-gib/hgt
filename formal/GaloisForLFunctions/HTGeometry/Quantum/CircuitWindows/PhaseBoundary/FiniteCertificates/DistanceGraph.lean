import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.BoundarySlice
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.Affordable
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # Polynomial equations at circuit-distance levels approached from either side -/

open Set Metric Filter Topology Polynomial Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section
variable {A X : Type*} [CommRing A] [TopologicalSpace X]

private theorem graph_boundary (d : X → ℝ) {x : X} (hx : 0<d x) :
    (x,d x)∈{z : X × ℝ | d z.1≤|z.2|} \ interior {z : X × ℝ | d z.1≤|z.2|} := by
  refine ⟨(show d x≤|d x| from le_abs_self (d x)),?_⟩
  intro hi
  have ht : Tendsto (fun u : ℝ => (x,u)) (𝓝 (d x)) (𝓝 (x,d x)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hv : ∀ᶠ u in 𝓝[<] (d x), d x≤|u| :=
    nhdsWithin_le_nhds (ht (mem_interior_iff_mem_nhds.mp hi))
  have hp : ∀ᶠ u in 𝓝[<] (d x), 0<u := nhdsWithin_le_nhds (lt_mem_nhds hx)
  have hl : ∀ᶠ u in 𝓝[<] (d x), u<d x := self_mem_nhdsWithin
  obtain ⟨u,hu,hl',hv'⟩ := (hp.and (hl.and hv)).exists
  exact hl'.not_ge (by simpa only [abs_of_pos hu] using hv')

/-- The absolute-height epigraph has finitely many local defining equations. -/
theorem distance_epigraph_certified {N : ℕ} (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a)
    (U : X → Square (Bits N)) (hU : MatrixRep ρ U) (s : ℕ) :
    let d (x : X) := infDist (U x) (phaseCircuitMatrixImageAtMost N s)
    FinitelyCertified (appendEval ρ) {z : X × ℝ | d z.1≤|z.2|} := by
  intro d
  let E := appendEval ρ
  have lift_base {f : X → ℝ} (h : Represents ρ f) : Represents E (fun z => f z.1) := by
    obtain ⟨c,hc⟩ := h
    exact ⟨C c,fun z => (eval₂_C ..).trans (hc z.1)⟩
  have hmat : MatrixRep E (fun z => U z.1) :=
    fun i j => ⟨lift_base (hU i j).1,lift_base (hU i j).2⟩
  have he : Represents E (fun z => |z.2|^2) := by
    refine ⟨Polynomial.X^2,fun z => ?_⟩
    change eval₂ (ρ z.1) z.2 (Polynomial.X^2)=|z.2|^2
    rw [eval₂_pow,eval₂_X,sq_abs]
  let S := {z : X × ℝ | d z.1≤|z.2|}
  have c := affordable_finite (continuous_appendEval ρ hc) hmat s (fun z => |z.2|) he (fun z => abs_nonneg _)
  have hset : {z : X × ℝ | HasProjectiveCircuitApproximation N |z.2| s (U z.1)}=S :=
    Set.ext fun z => hasProjectiveCircuitApproximation_iff_infDist _ _ _
  rwa [hset] at c

/-- Each distance is a root of one of finitely many nonzero polynomials in height,
including at zero. The coefficients belong to the ring representing the matrix. -/
theorem distance_graph_family [Nontrivial A] {N : ℕ} (ρ : X → A →+* ℝ)
    (hc : ∀ a, Continuous fun x => ρ x a) (U : X → Square (Bits N)) (hU : MatrixRep ρ U) (s : ℕ) :
    let d (x : X) := infDist (U x) (phaseCircuitMatrixImageAtMost N s)
    ∃ T : Finset A[X], 0∉T ∧ ∀ x, ∃ p∈T, p.eval₂ (ρ x) (d x)=0 := by
  classical
  intro d
  obtain ⟨F,hF⟩ := distance_epigraph_certified ρ hc U hU s
  refine ⟨insert Polynomial.X (F.erase 0),by simp [Ne.symm (Polynomial.X_ne_zero (R:=A))],?_⟩
  intro x
  rcases (infDist_nonneg : 0≤d x).eq_or_lt with hz|hp
  · exact ⟨Polynomial.X,Finset.mem_insert_self ..,(eval₂_X ..).trans hz.symm⟩
  obtain ⟨p,hpF,hp0,hlocal⟩ := hF (x,d x) (graph_boundary d hp).1
  have hne : p≠0 := by
    rintro rfl
    apply (graph_boundary d hp).2
    exact mem_interior_iff_mem_nhds.mpr (hlocal.mono fun z hz => hz (map_zero _))
  exact ⟨p,Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne,hpF⟩),hp0⟩

/-- A single finite family of nonzero base equations covers the whole
part of the distance level approached through nearby different positive
distances. This includes contacts at which the time derivative vanishes. -/
theorem distance_level_equations {N : ℕ} (ρ : X → A →+* ℝ) (hc : ∀ a, Continuous fun x => ρ x a)
    (U : X → Square (Bits N)) (hU : MatrixRep ρ U) (hu : Continuous U) (s : ℕ) (a : A) :
    let d (x : X) := infDist (U x) (phaseCircuitMatrixImageAtMost N s)
    ∃ B : Finset A, 0∉B ∧ ∀ x, d x=ρ x a → x∈closure {y | 0<d y ∧ d y≠ρ y a} →
      ∃ b∈B, ρ x b=0 := by
  intro d
  let S := {z : X × ℝ | d z.1≤|z.2|}
  have cert := distance_epigraph_certified ρ hc U hU s
  obtain ⟨B,hB,hzero⟩ := cert.boundary_slice hc a
  refine ⟨B,hB,?_⟩
  intro x hval hx
  apply hzero x
  rw [←hval]
  let W := closure ((S \ interior S) ∩ {z | z.2≠ρ z.1 a})
  have hd : Continuous d := (continuous_infDist_pt _).comp hu
  have hclosed : IsClosed ((fun y => (y,d y)) ⁻¹' W) := isClosed_closure.preimage (continuous_id.prodMk hd)
  apply closure_minimal _ hclosed hx
  intro y hy
  exact subset_closure ⟨graph_boundary d hy.1,hy.2⟩

#print axioms distance_graph_family
#print axioms distance_level_equations
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
