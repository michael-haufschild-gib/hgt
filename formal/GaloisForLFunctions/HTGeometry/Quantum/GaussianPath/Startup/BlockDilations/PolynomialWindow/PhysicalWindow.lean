import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PolynomialWindow.UniformMesh
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.LogarithmicWindow

/-! # Extensive cost from inverse-size startup through nearly linear physical time -/

open Real Filter MeasureTheory Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section

/-- The same frozen prefixes and both signs of time obey an extensive
gate floor from inverse system size through K/(log K)². -/
theorem gaussian_polynomial_from_startup :
    ∃ τ>0, ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      ∀ t : ℝ, A≤K*|t| → |t|≤δ*K/(log K)^2 → ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) → τ*K<(s:ℝ) := by
  obtain ⟨τ,hτ,a,ha,δ,hδ,hp⟩ := gaussian_polynomial_gate_floor
  obtain ⟨A,hA,b,hb,hs⟩ := SpanningDensity.FixedHorizon.gaussian_logarithmic_from_startup
    (η:=1/2) (by norm_num)
  obtain ⟨N,hN⟩ := exists_nat_gt a
  refine ⟨min τ (1/4),lt_min hτ (by norm_num),2*A,by positivity,δ,hδ,?_⟩
  filter_upwards [hs,hp] with ω hω hw
  filter_upwards [hω,hw,eventually_ge_atTop (b^N)] with n hs hn hN'
  let K : ℝ := (n+2:ℕ)
  have hK : 0≤K := Nat.cast_nonneg _
  intro t ht hfin s hfit
  by_cases hl : |t|<a
  · have hn₀ : n≠0 := Nat.ne_of_gt ((Nat.pow_pos (by omega : 0<b)).trans_le hN')
    have hlog := (Nat.le_log_iff_pow_le hb hn₀).mpr hN'
    have hsize : K≤2*((n+1:ℕ):ℝ) := by dsimp only [K]; exact_mod_cast (show n+2≤2*(n+1) by omega)
    have htime : A≤|t|*((n+1:ℕ):ℝ) := by
      nlinarith only [ht,mul_le_mul_of_nonneg_right hsize (abs_nonneg t)]
    have h := hs t htime (hl.le.trans (hN.le.trans (Nat.cast_le.mpr hlog))) s hfit
    have hb' := mul_le_mul_of_nonneg_right (min_le_right τ (1/4:ℝ)) hK
    linarith only [hb',h,hsize]
  · have h' := hn |t| ⟨le_of_not_gt hl,hfin⟩ s
    apply (mul_le_mul_of_nonneg_right (min_le_left ..) hK).trans_lt
    apply h'
    rcases le_total 0 t with h|h
    · rwa [abs_of_nonneg h]
    · let H : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
        ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
      rw [abs_of_nonpos h]
      exact hfit.neg_time H

/-- Two low-budget visits must cluster on the inverse-size scale or
be separated by more than the full polynomial exclusion horizon. -/
theorem gaussian_polynomial_visit_spacing :
    ∃ κ>0, ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ (t w : ℝ) (r s : ℕ), (r+s:ℕ)≤κ*K →
        HasProjectiveCircuitApproximation (n+2) (1/10) r (unitaryEvolution H t) →
        HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H w) →
        |w-t|<A/K ∨ δ*K/(log K)^2<|w-t| := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,h⟩ := gaussian_polynomial_from_startup
  refine ⟨κ,hκ,A,hA,δ,hδ,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro K H t w r s hk ht hw
  let G : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  by_contra! hlag
  have hf := affordable_add_time G (x:= -t) (y:=w) (ht.neg_time G) hw
  rw [show -t+w=w-t by ring] at hf
  obtain ⟨z,hz,C,hC,he⟩ := hf
  have hK : 0<K := by dsimp only [K]; positivity
  have hstart := (div_le_iff₀ hK).mp hlag.1
  exact (hn (w-t) (by rwa [mul_comm]) hlag.2 (r+s)
    ⟨z,hz,C,hC,he.trans (by norm_num)⟩).not_ge hk

#print axioms gaussian_polynomial_from_startup
#print axioms gaussian_polynomial_visit_spacing
end
end GaloisForLFunctions.HTGeometry.BlockDilations
