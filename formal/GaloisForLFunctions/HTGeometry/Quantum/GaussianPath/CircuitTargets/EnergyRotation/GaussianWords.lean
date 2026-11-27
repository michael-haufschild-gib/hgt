import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitTargets.EnergyRotation.WeakOnsite
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitTargets.EnergyRotation.PauliFields

/-! # All-time exclusion of extensive Pauli words on one frozen chain -/
open Finset Real Filter MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section

/-- At any prescribed positive support density, two transverse
components cannot both be small at most of the active sites. -/
theorem extensive_field_mass {η : ℝ} (hη : 0 < η) :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let u := pathPauliDisorderShell ω n
      ∀ Q : Fin (n+2) → Option (Fin 3), η*(n+2:ℕ) ≤ ((labelSupport Q).card:ℝ) →
        ∃ S : Finset (Fin (n+2)), ∃ j : Fin (n+2) → Fin 3,
          (∀ i ∈ S, Q i ≠ none ∧ Q i ≠ some (j i)) ∧
          c*(n+2:ℕ) ≤ ∑ i∈S, |u (.inl (i,j i))| := by
  classical
  obtain ⟨r,hr,hw⟩ := weak_onsite_density (half_pos hη)
  refine ⟨r*(η/2),mul_pos hr (half_pos hη),?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hbad
  intro u Q hQ
  let B := univ.filter fun i : Fin (n+2) => ∃ a : Fin 3, |u (.inl (i,a))| ≤ r
  let S := labelSupport Q \ B
  let j (i : Fin (n+2)) : Fin 3 := if Q i=some 0 then 1 else 0
  have hj (i : Fin (n+2)) : Q i ≠ some (j i) := by
    by_cases hi : Q i=some 0 <;> simp [j,hi]
  refine ⟨S,j,fun i hi => ⟨mem_labelSupport.mp (mem_sdiff.mp hi).1,hj i⟩,?_⟩
  have hc : ((labelSupport Q).card:ℝ) ≤ (S.card:ℝ)+B.card := by
    exact_mod_cast card_le_card_sdiff_add_card (s:=labelSupport Q) (t:=B)
  change (B.card:ℝ) ≤ (η/2)*(n+2:ℕ) at hbad
  have hsize : (η/2)*(n+2:ℕ) ≤ (S.card:ℝ) := by linarith only [hc,hbad,hQ]
  have hs (i) (hi : i∈S) : r ≤ |u (.inl (i,j i))| := by
    apply le_of_not_ge
    intro he
    exact (mem_sdiff.mp hi).2 (mem_filter.mpr ⟨mem_univ _,j i,he⟩)
  rw [mul_assoc]
  apply (mul_le_mul_of_nonneg_left hsize hr.le).trans
  simpa only [sum_const,nsmul_eq_mul,mul_comm r] using sum_le_sum hs

/-- Uniformly over every positive-density Pauli target and every date,
the deficit of its operator distance below one is at most C/K. -/
theorem gaussian_extensive_pauli_distance {η : ℝ} (hη : 0 < η) :
    ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ Q : Fin (n+2) → Option (Fin 3), η*(n+2:ℕ) ≤ ((labelSupport Q).card:ℝ) →
        ∀ t : ℝ, ∀ z : ℂ, ‖z‖=1 →
          (1-‖unitaryEvolution H t-z • finitePauliMatrix Q‖)*(n+2:ℕ) ≤ C := by
  obtain ⟨c,hc,hfield⟩ := extensive_field_mass hη
  obtain ⟨_,b,_,hb,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨84*π^2*b/(16*c^2),by positivity,?_⟩
  filter_upwards [hfield,hm] with ω hf hm
  filter_upwards [hf,hm] with n hf hm
  intro H Q hQ t z hz
  obtain ⟨S,j,ha,hs⟩ := hf Q hQ
  let u := pathPauliDisorderShell ω n
  let d := ‖unitaryEvolution H t-z • finitePauliMatrix Q‖
  let K : ℝ := (n+2:ℕ)
  have hK : 0 < K := by dsimp only [K]; positivity
  change (1-d)*K ≤ _
  by_cases hd : 0 ≤ 1-d
  · have hsq := pow_le_pow_left₀ (mul_nonneg hc.le hK.le) hs 2
    have h := (mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) hd)).trans
      (pauli_transverse_price u Q t z hz S j ha)
    have hlast := h.trans (mul_le_mul_of_nonneg_left hm.2 (by positivity))
    change 16*(1-d)*(c*K)^2 ≤ 84*π^2*(b*K) at hlast
    apply (le_div_iff₀ (by positivity)).mpr
    apply (mul_le_mul_iff_left₀ hK).mp
    linarith only [hlast]
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hd) hK.le).trans (by positivity)

private theorem support_density {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ Q : Fin (n+2) → Option (Fin 3), ∀ t : ℝ, ∀ z : ℂ, ‖z‖=1 →
        ‖unitaryEvolution H t-z • finitePauliMatrix Q‖ ≤ 1/4 →
        ((labelSupport Q).card:ℝ) ≤ η*(n+2:ℕ) := by
  obtain ⟨C,hC,hw⟩ := gaussian_extensive_pauli_distance hη
  filter_upwards [hw] with ω hw
  have hn : ∀ᶠ n : ℕ in atTop, 2*C < (n:ℝ) := tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  filter_upwards [hw,hn] with n hw hn
  intro H Q t z hz hfit
  by_contra! h
  have hp := hw Q h.le t z hz
  have hK : (0:ℝ) ≤ (n+2:ℕ) := Nat.cast_nonneg _
  have hd := mul_le_mul_of_nonneg_right (by linarith only [hfit] :
    (3/4:ℝ) ≤ 1-‖unitaryEvolution H t-z • finitePauliMatrix Q‖) hK
  rw [Nat.cast_add,Nat.cast_ofNat] at hd hp
  linarith only [hd,hp,hn,hC]

/-- Almost surely every Pauli word that the actual evolution ever fits
at projective error one quarter has vanishing support density, uniformly
over the date, word and global phase. -/
theorem gaussian_all_time_pauli_support :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ Q : Fin (n+2) → Option (Fin 3), ∀ t : ℝ, ∀ z : ℂ, ‖z‖=1 →
        ‖unitaryEvolution H t-z • finitePauliMatrix Q‖ ≤ 1/4 →
        ((labelSupport Q).card:ℝ) ≤ η*(n+2:ℕ) := by
  have h (k : ℕ) := support_density (by positivity : 0 < 1/((k:ℝ)+1))
  filter_upwards [ae_all_iff.mpr h] with ω hw
  intro η hη
  obtain ⟨k,hk⟩ := exists_nat_gt (1/η)
  have hk' : 1/((k:ℝ)+1) ≤ η := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_lt_iff₀ hη).mp hk
    linarith only [hh,hη]
  filter_upwards [hw k] with n hn
  intro H Q t z hz hfit
  exact (hn Q t z hz hfit).trans (mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg _))

#print axioms gaussian_all_time_pauli_support
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
