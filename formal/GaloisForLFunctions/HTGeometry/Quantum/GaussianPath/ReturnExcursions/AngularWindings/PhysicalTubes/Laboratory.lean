import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Components
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Exact laboratory circuit tubes in the physical Hamiltonian's energy basis -/

open Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open SharpOccupation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ
private abbrev phase (a : ℝ) := Complex.exp ((a:ℂ)*Complex.I)

/-- Projective operator-norm fitting dates of a single laboratory unitary. -/
def laboratoryDates (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (ε : ℝ) : Set ℝ :=
  {t | ∃ c : ℂ, ‖c‖=1 ∧ ‖unitaryEvolution H.val t-c • W.val‖≤ε}

private theorem frame_distance (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (t p : ℝ) :
    let V := H.2.isHermitian.eigenvectorUnitary
    let A (i : I) := -H.2.isHermitian.eigenvalues i/(2*π)
    ‖(anglePacket fun i => 2*π*(t*A i-p)).val-(V⁻¹*W*V).val‖=
      ‖unitaryEvolution H.val t-phase (2*π*p) • W.val‖ := by
  intro V A
  let D := Matrix.diagonal fun i => Complex.exp (-(Complex.I*((t:ℂ)*(H.2.isHermitian.eigenvalues i:ℂ))))
  let X := (anglePacket fun i => 2*π*(t*A i-p)).val
  let Y := (V⁻¹*W*V).val
  let z := phase (2*π*p)
  have hD : z • X=D := by
    change z • Matrix.diagonal _=Matrix.diagonal _
    rw [←Matrix.diagonal_smul]
    congr 1
    funext i
    change phase (2*π*p)*phase (2*π*(t*A i-p))=_
    rw [←Complex.exp_add]
    congr 1
    dsimp only [A]
    push_cast
    field_simp [pi_ne_zero]
    ring
  have hU : V.val*D*(V⁻¹).val=unitaryEvolution H.val t := (unitaryEvolution_spectral H.2.isHermitian t).symm
  have hY : V.val*Y*(V⁻¹).val=W.val := congrArg Subtype.val (show V*(V⁻¹*W*V)*V⁻¹=W by group)
  have hz : ‖z‖=1 := Complex.norm_exp_ofReal_mul_I _
  change ‖X-Y‖=_
  calc
    _ = ‖z • (X-Y)‖ := by rw [norm_smul,hz,one_mul]
    _ = ‖D-z • Y‖ := by rw [smul_sub,hD]
    _ = ‖V.val*(D-z • Y)*(V⁻¹).val‖ := by
      rw [CStarRing.norm_mul_mem_unitary _ (V⁻¹).2,CStarRing.norm_mem_unitary_mul _ V.2]
    _ = _ := by rw [mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,hU,hY]

/-- The change of basis and the real lift of the global phase preserve the error exactly. -/
theorem laboratoryDates_eq (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (ε : ℝ) :
    let V := H.2.isHermitian.eigenvectorUnitary
    laboratoryDates H W ε=circuitDates (V⁻¹*W*V) (fun i => -H.2.isHermitian.eigenvalues i/(2*π)) ε := by
  intro V
  ext t
  constructor
  · rintro ⟨c,hc,hfit⟩
    let p := c.arg/(2*π)
    refine ⟨p,?_⟩
    rw [frame_distance]
    have hp : 2*π*p=c.arg := by dsimp only [p]; field_simp
    rw [hp,show phase c.arg=c by simpa only [hc,Complex.ofReal_one,one_mul] using Complex.norm_mul_exp_arg_mul_I c]
    exact hfit
  · rintro ⟨p,hp⟩
    exact ⟨phase (2*π*p),Complex.norm_exp_ofReal_mul_I _,(frame_distance H W t p) ▸ hp⟩

/-- Each possible extremal winding carries at most one connected interval of true fits
to the specified laboratory circuit at the specified precision. Distinct bands are disjoint. -/
theorem laboratory_cells (H : selfAdjoint (Mat I)) (W : unitary (Mat I)) (l u : I) {ε : ℝ}
    (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    let A (i : I) := -H.2.isHermitian.eigenvalues i/(2*π)
    let V := H.2.isHermitian.eigenvectorUnitary
    let J := indexWindow (A u-A l) (circuitTurns (V⁻¹*W*V) u-circuitTurns (V⁻¹*W*V) l) (physicalArc ε)
    A l<A u → (∀ i, A i∈Icc (A l) (A u)) →
    laboratoryDates H W ε ⊆ (⋃ N : ℤ, J N) ∧
      Pairwise (fun M N : ℤ => Disjoint (J M) (J N)) ∧ ∀ N : ℤ, Convex ℝ (laboratoryDates H W ε ∩ J N) := by
  intro A V J hg hext
  obtain ⟨h₁,h₂,h₃⟩ := exact_circuit_cells (V⁻¹*W*V) A l u he hg hext
  rw [laboratoryDates_eq]
  exact ⟨h₁,h₂,fun N => (h₃ N).2⟩

#print axioms laboratory_cells
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
