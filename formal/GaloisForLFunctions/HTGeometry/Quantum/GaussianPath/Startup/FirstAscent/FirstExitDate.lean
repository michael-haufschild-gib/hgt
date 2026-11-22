import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.PhysicalWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ExitInfimum

/-! # The first exit at a fixed Gaussian gate budget -/
open MeasureTheory Filter Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- The first exit at error 1/10 is delayed from the empty-circuit exit
by an amount comparable to s√log(N/s)/N², simultaneously for all positive
budgets below a fixed fraction of the prefix. -/
theorem gaussian_first_exit_date :
    ∃ c C : ℝ, ∃ M : ℕ, 0<c ∧ 0<C ∧ 0<M ∧
      ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω n),
          isSelfAdjoint_pathHamiltonian _⟩
        let W := circuitHamiltonianSpectralWidth H
        let t₀ := 4*arcsin (1/20)/W
        ∀ s : ℕ, 0<s → M*s ≤ N →
          let F := (s:ℝ)*sqrt (log ((N:ℝ)/s))/(N:ℝ)^2
          let exit := sInf {t : ℝ | 0 ≤ t ∧
            ¬HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val t)}
          exit-t₀ ∈ Icc (c*F) (C*F) := by
  obtain ⟨c,C,m,hc,hC,hm,hw⟩ := gaussian_first_ascent_window
  obtain ⟨a,b,ha,hb,hwidth⟩ := gaussian_initial_clock
  obtain ⟨L,hL⟩ := exists_nat_ge (C*b)
  let M := max m (L^2)
  have hθ := GaloisForLFunctions.arcsin_le_pi_half_mul (1/20) (by norm_num) (by norm_num)
  have hmargin : 4*arcsin (1/20)+1<π := by linarith only [hθ,pi_gt_three]
  refine ⟨c,C,M,hc,hC,hm.trans_le (le_max_left ..),?_⟩
  filter_upwards [hw,hwidth] with ω hw hh
  filter_upwards [hw,hh] with n hn hW
  intro N H W t₀ s hs hsize F exit
  have hN : 0<(N:ℝ) := by dsimp [N]; positivity
  have hs' : 0<(s:ℝ) := by exact_mod_cast hs
  have hW' : 0<W := (mul_pos ha hN).trans_le hW.1
  have hm' := (Nat.mul_le_mul_right s (le_max_left m (L^2))).trans hsize
  have hcut := (Nat.mul_le_mul_right s (le_max_right m (L^2))).trans hsize
  have hsN : s ≤ N := (Nat.le_mul_of_pos_left s hm).trans hm'
  have hnorm := budget_mass_bound (Nat.cast_nonneg L : (0:ℝ) ≤ L) hs' hN
    (by exact_mod_cast hsN) (by exact_mod_cast hcut)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hpay : (C*F)*W ≤ 1 := calc
    _ ≤ (C*F)*(b*N) := mul_le_mul_of_nonneg_left hW.2.1 (mul_nonneg hC.le hF)
    _ = (C*b)*((s:ℝ)/N)*sqrt (log ((N:ℝ)/s)) := by dsimp only [F]; field_simp
    _ ≤ (L:ℝ)*((s:ℝ)/N)*sqrt (log ((N:ℝ)/s)) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hL (div_nonneg hs'.le hN.le)) (sqrt_nonneg _)
    _ ≤ 1 := hnorm
  have hT : t₀+C*F < π/W := (lt_div_iff₀ hW').mpr (by
    rw [add_mul]
    change (4*arcsin (1/20)/W)*W+_ < π
    rw [div_mul_cancel₀ _ hW'.ne']
    linarith only [hmargin,hpay])
  have ht₀ : 0 ≤ t₀ := div_nonneg (mul_nonneg (by norm_num) (arcsin_nonneg.mpr (by norm_num))) hW'.le
  obtain ⟨hl,hu⟩ := hn s hs hm'
  have h := first_exit_bracket _ (add_nonneg ht₀ (mul_nonneg hC.le hF)) hT hl hu
  change t₀+c*F ≤ exit ∧ exit ≤ t₀+C*F at h
  exact ⟨by linarith only [h.1],by linarith only [h.2]⟩

#print axioms gaussian_first_exit_date
end
end GaloisForLFunctions.HTGeometry.FirstAscent
