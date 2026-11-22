import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.Width
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.LongitudinalWord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.Semicircle

/-! # Affordability gained by correcting isolated longitudinal fields -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Near-isolated selected fields remove twice their total strength from
the residual energy width, up to twice the omitted norm. A word with one
gate per selected site leaves only the residual chord and the Duhamel error. -/
theorem isolated_field_delay {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) (q η : ℝ)
    (hη : 0≤η) (hs : ∀ s ∈ S, isolatedLongitudinalSite u q η s) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    let J : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonianOnSites Sᶜ u⟩
    let B := 21*(S.card:ℝ)*η
    circuitHamiltonianSpectralWidth J+2*(S.card:ℝ)* |q| ≤ circuitHamiltonianSpectralWidth H+2*B ∧
      ∀ t : ℝ, 0≤t → t*circuitHamiltonianSpectralWidth J≤π →
        HasProjectiveCircuitApproximation (n+2) (2*sin (t*circuitHamiltonianSpectralWidth J/4)+t*B)
          S.card (unitaryEvolution H.val t) := by
  intro H J B
  let K : selfAdjoint (Reg (n+2)) :=
    ⟨pathHamiltonian (longitudinalPacket S q),isSelfAdjoint_pathHamiltonian _⟩
  have hJ := pathHamiltonianOnSites_isSiteSupported Sᶜ u
  have hK : IsSiteSupported S K.val := by
    change IsSiteSupported S (pathHamiltonian _)
    rw [←longitudinalPacket_restriction S q]
    exact pathHamiltonianOnSites_isSiteSupported _ _
  have hmiss : ‖H.val-(J+K).val‖ ≤ B := isolated_field_replacement_error u S q η hη hs
  have hpacket : 2*(S.card:ℝ)* |q| ≤ circuitHamiltonianSpectralWidth K := by
    let E := K.2.isHermitian.eigenvalues
    obtain ⟨i,j,hh,_⟩ := exists_path_spectral_width_ge_onsite (longitudinalPacket S q)
    rw [(longitudinalPacket_mass S q).2] at hh
    have hE : E i-E j ≤ circuitHamiltonianSpectralWidth K :=
      sub_le_sub (Finset.le_sup' E (Finset.mem_univ i)) (Finset.inf'_le E (Finset.mem_univ j))
    exact (mul_assoc 2 (S.card:ℝ) |q|).le.trans (hh.trans hE)
  constructor
  · have ht := width_perturb H (J+K)
    rw [norm_sub_rev (J+K).val H.val] at ht
    linarith only [hpacket,hmiss,ht,width_disjoint_sum_lower disjoint_compl_left J K hJ hK]
  · intro t ht hw
    let e := 2*sin (t*circuitHamiltonianSpectralWidth J/4)
    have ha : HasProjectiveCircuitApproximation (n+2) e 0 (unitaryEvolution J.val t) :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr (empty_distance J ht hw).le
    have hp := LocalPatches.approx_product (unitaryEvolution_mem_unitary K.2 t) ha (longitudinal_word S q t)
    obtain ⟨z,hz,C,hc,herr⟩ := hp
    rw [zero_add] at hc
    rw [add_zero] at herr
    have hprod := unitaryEvolution_add_of_isSiteSupported_disjoint disjoint_compl_left hJ hK t
    change unitaryEvolution (J+K).val t=unitaryEvolution J.val t*unitaryEvolution K.val t at hprod
    change ‖unitaryEvolution J.val t*unitaryEvolution K.val t-z • (C.eval : Reg _)‖ ≤ e at herr
    rw [←hprod] at herr
    have hUV := norm_unitaryEvolution_sub_le _ _ H.2 (J+K).2 t
    rw [abs_of_nonneg ht] at hUV
    refine ⟨z,hz,C,hc,?_⟩
    exact (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution (J+K).val t) _).trans
      ((add_le_add (hUV.trans (mul_le_mul_of_nonneg_left hmiss ht)) herr).trans_eq (add_comm _ _))

#print axioms isolated_field_delay
end
end GaloisForLFunctions.HTGeometry.FirstAscent
