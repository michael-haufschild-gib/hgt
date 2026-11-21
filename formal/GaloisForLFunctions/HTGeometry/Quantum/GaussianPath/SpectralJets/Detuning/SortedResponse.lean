import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Bounds.PrefixResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.SortedModes

/-! # The uniform derivative response in the sorted spectral labeling -/

open Matrix MvPolynomial Filter Topology Set
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

private theorem packet_sorted_permutation {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (θ : Fin n → ℝ) (f : Fin D → (Fin n → ℂ) → ℂ)
    (hf : ∀ j, AnalyticAt ℂ (f j) (realEmbed θ) ∧ ∀ᶠ z in 𝓝 (realEmbed θ),
      matrixCharpolyRelation (∑ i, z i • P i,f j z) = 0)
    (hi : Function.Injective (fun j => f j (realEmbed θ))) :
    Function.Injective (sortedEnsembleSpectrum hP θ) ∧ ∃ e : Equiv.Perm (Fin D), ∀ j,
      (fun y => f j (realEmbed y)) =ᶠ[𝓝 θ] fun y => (sortedEnsembleSpectrum hP y (e j) : ℂ) := by
  have hmem (j) : ∃ l, f j (realEmbed θ) = (sortedEnsembleSpectrum hP θ l : ℂ) := by
    obtain ⟨l,hl⟩ := exists_eigenvalue_eq_of_charpolyDet_eq_zero (isHermitian_spectralEnsembleMatrix hP θ)
      (hf j).2.self_of_nhds
    obtain ⟨a,ha⟩ := exists_sortedTuple_eq (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues l
    exact ⟨a,hl.trans (congrArg Complex.ofReal ha)⟩
  choose s hs using hmem
  have hinj : Function.Injective s := fun j l hj => hi ((hs j).trans ((congrArg
    (fun a => (sortedEnsembleSpectrum hP θ a : ℂ)) hj).trans (hs l).symm))
  let e := Equiv.ofBijective s hinj.bijective_of_finite
  have hsorted : Function.Injective (sortedEnsembleSpectrum hP θ) := by
    intro a b h
    obtain ⟨j,rfl⟩ := e.surjective a
    obtain ⟨l,rfl⟩ := e.surjective b
    exact congrArg e (hi ((hs j).trans ((congrArg Complex.ofReal h).trans (hs l).symm)))
  refine ⟨hsorted,e,fun j => ?_⟩
  obtain ⟨l,hl⟩ := branch_sorted_germ hP hsorted (hf j).1.continuousAt (hf j).2
  have he : l=e j := hsorted (Complex.ofReal_injective (hl.self_of_nhds.symm.trans (hs j)))
  simpa only [← he] using hl

/-- The integral Pauli characteristic polynomial extended to complex coefficients. -/
def pathCharacteristic (N : ℕ) := map GaussianInt.toComplex (characteristic (integralGenerators N))

/-- Every nonzero balanced integer mode has a common, deterministic lower
response in sorted real coordinates whenever the shared analytic packet has it. -/
theorem sorted_response_of_packet (N : ℕ) (rows : Fin (2^N) → Option (List (Coordinates N)))
    (θ : Coordinates N → ℝ) (C a : ℝ) (h : ModesAtScale N rows θ C a) :
    θ ∈ simpleEnsembleLocus (chainPauliFin_isHermitian N) ∧
    ∀ m : Fin (2^N) → ℤ, m ≠ 0 → ∑ j, m j = 0 → ∃ i w, rows i = some w ∧
      a ≤ (C*((2^N:ℕ):ℝ)*|sortedMode (chainPauliFin_isHermitian N) (pathCharacteristic N)
        (fun j => (m j:ℝ)) w θ|)^2 := by
  obtain ⟨f,hf,hi,hr⟩ := h
  let P := chainPauliFin_isHermitian N
  let A := integralGenerators N
  let φ := GaussianInt.toComplex
  have hm : (fun j => (A j).map φ) = chainPauliFin N := funext (generators_map N)
  obtain ⟨hs,e,he⟩ := packet_sorted_permutation P θ f hf hi
  have hθ : θ ∈ simpleEnsembleLocus P := (regularPacket_sorted_iff A φ hm P θ 0).mp
    ⟨Complex.ofReal_injective.comp hs,fun j => by simp⟩
  refine ⟨hθ,?_⟩
  intro m hne hbal
  let m' := m ∘ e
  have hm' : m' ≠ 0 := by
    intro heq
    apply hne
    funext i
    simpa only [m',Function.comp_apply,e.apply_symm_apply,Pi.zero_apply] using congrFun heq (e.symm i)
  obtain ⟨i,w,hw,hr'⟩ := hr m' hm' ((Equiv.sum_comp e m).trans hbal)
  refine ⟨i,w,hw,?_⟩
  have heq : ∑ j, mixed w (f j) (realEmbed θ)*(m' j : ℂ) =
      (sortedMode P (pathCharacteristic N) (fun j => (m j:ℝ)) w θ : ℂ) := by
    change _ = (sortedMode P (map φ (characteristic A)) (fun j => (m j:ℝ)) w θ : ℂ)
    rw [sortedMode_eq_real_sum A φ hm P _ w hθ,Complex.ofReal_sum]
    apply (Finset.sum_congr rfl (fun j _ => ?_)).trans (Equiv.sum_comp e (fun j =>
      (((m j:ℝ)*realMixed w (fun y => sortedEnsembleSpectrum P y j) θ:ℝ):ℂ)))
    rw [mixed_of_real_germ (hf j).1 (he j) w,Complex.ofReal_mul]
    simp [m',mul_comm]
  change a ≤ (C*((2^N:ℕ):ℝ)*‖∑ j, mixed w (f j) (realEmbed θ)*(m' j:ℂ)‖)^2 at hr'
  rw [heq,Complex.norm_real,Real.norm_eq_abs] at hr'
  exact hr'

#print axioms sorted_response_of_packet
end
end GaloisForLFunctions.HTGeometry.SpectralJets
