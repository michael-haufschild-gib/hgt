import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.Width
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.PeriodicCuts

/-! # Spectral width of a path cut into contiguous blocks -/
open Finset Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
open SpectralGapMass.Bulk.PeriodicCuts
noncomputable section

/-- Full Hamiltonian for the given onsite fields and bonds. -/
def shellOperator {n : ℕ} (u : PathShell n) : selfAdjoint (Register (n+2)) :=
  ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩

private theorem supported_sum {N : ℕ} {ι : Type*} (s : Finset ι) (S : ι→Finset (Fin N))
    (H : ι→selfAdjoint (Register N)) (hs : ∀ j, IsSiteSupported (S j) (H j).val) :
    IsSiteSupported (s.biUnion S) (∑ j ∈ s, H j).val := by
  change IsSiteSupported _ (∑ j ∈ s, (H j).val)
  apply sum_induction _ (IsSiteSupported (s.biUnion S)) (fun _ _ => IsSiteSupported.add)
    (IsSiteSupported.zero _)
  exact fun j hj => IsSiteSupported.mono (fun i hi => mem_biUnion.mpr ⟨j,hj,hi⟩) (hs j)

private theorem width_zero (N : ℕ) : circuitHamiltonianSpectralWidth (0 : selfAdjoint (Register N))=0 := by
  have h := width_disjoint_sum (N:=N) (S:=∅) (T:=∅) disjoint_empty_left
    (0 : selfAdjoint (Register N)) 0 (IsSiteSupported.zero _) (IsSiteSupported.zero _)
  rw [add_zero] at h
  linarith only [h]

/-- Spectral diameters of finitely many disjoint registers add exactly. -/
theorem width_sum_disjoint {N : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (S : ι→Finset (Fin N)) (H : ι→selfAdjoint (Register N))
    (hs : ∀ j, IsSiteSupported (S j) (H j).val) (hd : ∀ i j, i≠j → Disjoint (S i) (S j)) :
    circuitHamiltonianSpectralWidth (∑ j ∈ s, H j)=∑ j ∈ s, circuitHamiltonianSpectralWidth (H j) := by
  induction s using Finset.induction_on with
  | empty => simp only [sum_empty,width_zero]
  | insert i s hi ih =>
    have hdis : Disjoint (S i) (s.biUnion S) := by
      refine disjoint_left.mpr fun x hx hy => ?_
      obtain ⟨j,hj,hx'⟩ := mem_biUnion.mp hy
      exact disjoint_left.mp (hd i j (fun h => hi (h ▸ hj))) hx hx'
    rw [sum_insert hi,sum_insert hi,width_disjoint_sum hdis _ _ (hs i) (supported_sum s S H hs),ih]

/-- Dropping the crossing bonds changes the width by at most twice the
sum of their absolute coefficients. The block widths use the same draw. -/
theorem cut_width_error {n : ℕ} (L : ℕ) (u : PathShell n) :
    |circuitHamiltonianSpectralWidth (shellOperator u)-
      ∑ b, circuitHamiltonianSpectralWidth (shellOperator (piece L u b))| ≤
        2*(∑ l ∈ labels L none, |u l|) := by
  let K (b) := shellOperator (piece L u b)
  let H := shellOperator u
  let w := u-∑ b, piece L u b
  have hw (l : PathLabel n) : w l=if owner L l=none then u l else 0 := by
    change u l-(∑ b, piece L u b).ofLp l=_
    rw [WithLp.ofLp_sum,Finset.sum_apply]
    cases h : owner L l with
    | none => simp [piece,h]
    | some b => simp [piece,h]
  have hmat : H.val-(∑ b,K b).val=pathHamiltonian w := by
    change pathHamiltonianLM n u-(∑ b,pathHamiltonianLM n (piece L u b))=pathHamiltonianLM n _
    rw [map_sub,map_sum]
  have hm : ‖H.val-(∑ b,K b).val‖ ≤ ∑ l ∈ labels L none, |u l| := by
    rw [hmat,pathHamiltonian_eq_sum,labels,sum_filter]
    apply (norm_sum_le _ _).trans_eq
    apply sum_congr rfl
    intro l _
    rw [norm_smul,norm_finitePauliMatrix,Complex.norm_real,Real.norm_eq_abs,mul_one,hw]
    split <;> simp
  have he := width_sum_disjoint univ (sites (n:=n) L) K (piece_supported L u) (disjoint_sites L)
  rw [←he]
  have h₁ := width_perturb H (∑ b,K b)
  have h₂ := width_perturb (∑ b,K b) H
  rw [norm_sub_rev] at h₁
  exact abs_le.mpr ⟨by linarith only [hm,h₁],by linarith only [hm,h₂]⟩

#print axioms cut_width_error
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
