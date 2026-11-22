import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.DelayScale

/-! # A sparse circuit gains arbitrarily little on an inverse-volume window -/
open Real Filter MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
open FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

/-- Given a window and an error margin, a fixed small fraction of the
sites buys at most that margin over the empty circuit on the whole window. -/
theorem gaussian_sparse_advantage (A η : ℝ) (hA : 0<A) (hη : 0<η) :
    ∃ M : ℕ, 0<M ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ s : ℕ, M*s≤N → ∀ t : ℝ, |t|≤A/N →
        orbitCircuitDistance H 0 t ≤ orbitCircuitDistance H s t+η := by
  obtain ⟨B,hB,hw⟩ := gaussian_circuit_advantage
  obtain ⟨L,hL⟩ := exists_nat_ge (336*A/η)
  obtain ⟨K,hK⟩ := exists_nat_ge B
  let M := max 42 (max K (L^2))
  have hm : 0<M := (by norm_num : 0<42).trans_le (le_max_left ..)
  refine ⟨M,hm,?_⟩
  filter_upwards [hw] with ω hh
  filter_upwards [hh] with n hn
  intro N H s hs t ht
  rcases eq_zero_or_pos s with rfl|hpos
  · exact le_add_of_nonneg_right hη.le
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hsp : 0<(s:ℝ) := Nat.cast_pos.mpr hpos
  have hcut (j : ℕ) (hj : j≤M) : j*s≤N := (Nat.mul_le_mul_right s hj).trans hs
  have hsN := (Nat.le_mul_of_pos_left s hm).trans hs
  have hk := hcut K ((le_max_left ..).trans (le_max_right ..))
  have hl := hcut (L^2) ((le_max_right ..).trans (le_max_right ..))
  have h42 := hcut 42 (le_max_left ..)
  have hcap : 42*s≤Fintype.card (PathLabel n) := h42.trans (by
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,N]; omega)
  have hf := hn s hpos hcap t
  have hscale : B ≤ (N:ℝ)/s := (le_div_iff₀ hsp).mpr
    ((mul_le_mul_of_nonneg_right hK hsp.le).trans (by exact_mod_cast hk))
  have hroot := sqrt_log_ratio hB hsp hN (by exact_mod_cast hsN) hscale
  have hbudget := budget_mass_bound (Nat.cast_nonneg L : (0:ℝ)≤L) hsp hN
    (by exact_mod_cast hsN) (by exact_mod_cast hl)
  have hcoef : 336*A ≤ η*L := by
    have h := (div_le_iff₀ hη).mp hL
    linarith only [h]
  let q := sqrt (log ((N:ℝ)/s))
  have hq : 0≤q := sqrt_nonneg _
  have hterm : 4*|t|*(42*(s:ℝ))*sqrt (log (B*N/(42*s))) ≤ η := calc
    _ ≤ 4*(A/N)*(42*(s:ℝ))*(2*q) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) (by positivity))
        hroot (sqrt_nonneg _) (by positivity)
    _ = (336*A)*((s:ℝ)/N*q) := by ring
    _ ≤ (η*L)*((s:ℝ)/N*q) := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (div_nonneg hsp.le hN.le) hq)
    _ = η*((L:ℝ)*(s/N)*q) := by ring
    _ ≤ η := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hbudget hη.le
  exact hf.trans (add_le_add_left hterm _)

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
