import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Diagonal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.PairRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathCoefficientMass

/-! # The qubit and dimension prefactors in the exact empty-entry flux -/
open Real Filter Set MeasureTheory Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass
open FluxOccupation EmptyVisitFlux
noncomputable section

/-- On a typical large prefix the mean gap is of order √N. The bounds
hold simultaneously for all radii, since the same pair rate multiplies
every power of the angular width. -/
theorem gaussian_pair_rate_scale :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let D := (2:ℝ)^N
      let u := pathPauliDisorderShell ω n
      let E := fun j => -(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues j
      pairTurnRate E ∈ Icc (c*D^2*sqrt N) (C*D^2*sqrt N) := by
  obtain ⟨a,b,ha,hb,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨a/(32*π),sqrt b/(2*π),by positivity,by positivity,?_⟩
  filter_upwards [hm] with ω hm
  filter_upwards [hm] with n hm
  intro N D u E
  let V := ∑ i : Fin N, (u (.inl (i,2)))^2
  have hV : 0≤V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hD : 0<D := by dsimp only [D]; positivity
  have hd : (Fintype.card (Fin N → Bool):ℝ)=D := by simp [D]
  have hmean := sq_sum_abs_le_card_mul_sum_sq (fun i : Fin N => u (.inl (i,2)))
  rw [Fintype.card_fin] at hmean
  have hfield : a*sqrt N ≤ sqrt V := by
    apply (sq_le_sq₀ (mul_nonneg ha.le (sqrt_nonneg _)) (sqrt_nonneg _)).mp
    rw [mul_pow,sq_sqrt hN.le,sq_sqrt hV]
    have hh := (sq_le_sq₀ (mul_nonneg ha.le hN.le) (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr hm.1
    have hh' := hh.trans hmean
    change (a*(N:ℝ))^2 ≤ (N:ℝ)*V at hh'
    rw [mul_pow,sq (N:ℝ),←mul_assoc] at hh'
    exact le_of_mul_le_mul_right (by simpa only [mul_comm (N:ℝ) V] using hh') hN
  have hl := longitudinal_absolute_lower u
  change D*sqrt V ≤ 8*∑ i, |(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i| at hl
  have signed : (∑ i, |E i|)=∑ i, |(isSelfAdjoint_pathHamiltonian u).isHermitian.eigenvalues i| :=
    Finset.sum_congr rfl fun i _ => abs_neg _
  rw [←signed] at hl
  obtain ⟨hcent,hvar⟩ := path_spectral_moments u
  have hzero : (∑ i, E i)=0 := by simp only [E,Finset.sum_neg_distrib,hcent,neg_zero]
  have hs : (∑ i, (E i)^2)=D*‖u‖^2 := by
    simpa only [E,neg_sq,D,N,Nat.cast_pow,Nat.cast_ofNat,EuclideanSpace.norm_sq_eq,
      Real.norm_eq_abs,sq_abs] using hvar
  have hsum := sq_sum_abs_le_card_mul_sum_sq E
  rw [hd,hs] at hsum
  have hu : (∑ i, |E i|) ≤ D*sqrt b*sqrt N := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)).mp
    rw [mul_pow,mul_pow,sq_sqrt hb.le,sq_sqrt hN.le]
    calc
      _ ≤ D*(D*‖u‖^2) := hsum
      _ ≤ D*(D*(b*(N:ℝ))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm.2 hD.le) hD.le
      _ = _ := by ring
  have hg : D*(∑ i, |E i|) ≤ 4*π*pairTurnRate E ∧
      4*π*pairTurnRate E ≤ 2*D*(∑ i, |E i|) := by
    have hh := pair_absolute_bounds E hzero
    change (Fintype.card (Fin N → Bool):ℝ)*_ ≤ _ ∧ _ ≤ 2*(Fintype.card (Fin N → Bool):ℝ)*_ at hh
    rwa [hd] at hh
  constructor
  · have hh := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hfield hD.le).trans hl) hD.le
    apply (le_of_mul_le_mul_left · (show 0<32*π by positivity))
    calc
      32*π*(a/(32*π)*D^2*sqrt N) = D*(D*(a*sqrt N)) := by field_simp
      _ ≤ D*(8*∑ i, |E i|) := hh
      _ ≤ 32*π*pairTurnRate E := by linarith only [hg.1]
  · apply (le_of_mul_le_mul_left · (show 0<2*π by positivity))
    calc
      2*π*pairTurnRate E ≤ D*∑ i, |E i| := by linarith only [hg.2]
      _ ≤ D*(D*sqrt b*sqrt N) := mul_le_mul_of_nonneg_left hu hD.le
      _ = 2*π*(sqrt b/(2*π)*D^2*sqrt N) := by field_simp

#print axioms gaussian_pair_rate_scale
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass
