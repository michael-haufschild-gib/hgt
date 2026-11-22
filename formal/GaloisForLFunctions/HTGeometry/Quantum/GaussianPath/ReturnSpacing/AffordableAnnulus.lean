import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PolynomialAccuracy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PolynomialFloor

/-! # Affordable intervals separated in time from every low-budget visit -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing
noncomputable section
open LocalPatches
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

private theorem annular_lag {v t u R : ℝ} (hl : R/3 ≤ |t|) (hr : |t| ≤ 2*R/3)
    (hu : |u-(v+t)| ≤ R/4) : R/12 ≤ |u-v| ∧ |u-v| ≤ R := by
  have h₁ := abs_add_le (u-v) (v+t-u)
  have h₂ := abs_add_le (u-(v+t)) t
  rw [show u-v+(v+t-u)=t by ring,abs_sub_comm (v+t) u] at h₁
  rw [show u-(v+t)+t=u-v by ring] at h₂
  constructor <;> linarith only [hl,hr,hu,h₁,h₂]

/-- Around every accurate scalar visit there are two growing intervals on
which a quadratic budget suffices at error 1/10. Throughout their R/4-neighborhood,
every budget below c√N fails even at error 3/20, where R=N^(1/48)/4. -/
theorem gaussian_affordable_intervals_separated_from_low_visits :
    ∃ c : ℝ, ∃ J : ℕ, 0<c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      let R := (N:ℝ)^((48:ℝ)⁻¹)/4
      ∀ v η : ℝ, η+1/(N:ℝ) ≤ 1/10 → HasProjectiveCircuitApproximation N η 0 (unitaryEvolution H v) →
        ∀ t : ℝ, R/3 ≤ |t| → |t| ≤ 2*R/3 →
          HasProjectiveCircuitApproximation N (1/10:ℝ) (J*N^2) (unitaryEvolution H (v+t)) ∧
          ∀ u : ℝ, |u-(v+t)| ≤ R/4 → ∀ s : ℕ,
            HasProjectiveCircuitApproximation N (3/20:ℝ) s (unitaryEvolution H u) → c*Real.sqrt N ≤ s := by
  obtain ⟨A,c,hA,hc,hfloor⟩ := gaussian_pauli_polynomial_interval_cost_floor
  obtain ⟨J,hcompile⟩ := gaussian_inverse_size_compiler
  refine ⟨c,J,hc,?_⟩
  filter_upwards [hfloor,hcompile] with ω hf hu
  obtain ⟨m,hm⟩ := exists_nat_gt (48*A)
  filter_upwards [hf,hu,eventually_ge_atTop m] with n hf hu hn
  intro N H R v η hη hv t hlo hhi
  have hN : 2 ≤ (N:ℝ) := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  have h1 : 1 ≤ (N:ℝ)^((48:ℝ)⁻¹) := Real.one_le_rpow (by linarith only [hN]) (by norm_num)
  have hsmall : A/(N:ℝ) ≤ R/12 := by
    have hmN : (m:ℝ) ≤ N := by exact_mod_cast (show m ≤ N by dsimp [N]; omega)
    have hA' : A/(N:ℝ) ≤ 1/48 := (div_le_iff₀ (by linarith only [hN])).mpr (by linarith only [hm,hmN])
    exact hA'.trans (by dsimp [R]; linarith only [h1])
  have ht : |t|^7 ≤ N := by
    have ht' : |t| ≤ (N:ℝ)^((48:ℝ)⁻¹) := by dsimp only [R] at hhi; linarith only [hhi,h1]
    calc
      _ ≤ ((N:ℝ)^((48:ℝ)⁻¹))^7 := pow_le_pow_left₀ (abs_nonneg _) ht' 7
      _ = (N:ℝ)^((48:ℝ)⁻¹*7) := by rw [Real.rpow_mul (Nat.cast_nonneg _)]; norm_cast
      _ ≤ (N:ℝ)^((1:ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hN]) (by norm_num)
      _ = _ := Real.rpow_one _
  have hj := hu t ht
  let K : selfAdjoint (Reg N) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  have hfit := approx_product (unitaryEvolution_mem_unitary K.2 t) hv hj
  have he : unitaryEvolution H v*unitaryEvolution H t=unitaryEvolution H (v+t) := by
    simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul K (v+t) t
  rw [he,zero_add] at hfit
  refine ⟨approx_enlarge hfit hη le_rfl,?_⟩
  intro u hx s hs
  obtain ⟨hlag,hrag⟩ := annular_lag hlo hhi hx
  have hlow := (hf |u-v| (hsmall.trans hlag) hrag).1
  have hdiff := approx_product (unitaryEvolution_mem_unitary K.2 u) (hv.neg_time K) hs
  have hsub : unitaryEvolution H (-v)*unitaryEvolution H u=unitaryEvolution H (u-v) := by
    have hh := unitaryEvolution_sub_mul K (u-v) u
    rwa [show u-v-u= -v by ring] at hh
  rw [hsub,zero_add] at hdiff
  have hclose := approx_enlarge hdiff (show η+3/20 ≤ 1/4 by
    linarith only [hη,one_div_nonneg.mpr (Nat.cast_nonneg (α:=ℝ) N)]) le_rfl
  have habs : HasProjectiveCircuitApproximation N (1/4:ℝ) s (unitaryEvolution H |u-v|) := by
    rcases le_or_gt 0 (u-v) with hp | hn
    · rwa [abs_of_nonneg hp]
    · rw [abs_of_neg hn]
      exact hclose.neg_time K
  obtain ⟨z,_,C,hC,herr⟩ := habs
  exact (hlow C z herr).trans (by exact_mod_cast hC)

#print axioms gaussian_affordable_intervals_separated_from_low_visits
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing
