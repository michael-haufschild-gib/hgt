import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.Supports.LargeDifferences
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.FirstReturn

/-! # Macroscopic spectral coherence at the first laboratory return -/

open Matrix Finset Filter
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
open AngularWindings.PhysicalTubes PrecisionReturns PhaseBoundary.FiniteCertificates.BudgetComparisons
noncomputable section

/-- On every sufficiently large prefix and every disorder realization,
every circuit at the first return carries a positive macroscopic
correlation through modes supported on more than a quarter of the levels. -/
theorem first_return_large_differences :
    ∀ᶠ k : ℕ in atTop, ∀ ω : PathPauliDisorder,
      let K := k+3
      let n := 2^(k+1)
      let H := generator (pathPauliDisorderShell ω (k+1))
      let σ := Iterated.crossing H (nearHilbertContinuousCircuitBudget K) 0
      let V := H.2.isHermitian.eigenvectorUnitary
      ∀ s : ℕ, let v := firstVisit H σ s (1/10)
        let p (i) := Complex.exp (((-v*H.2.isHermitian.eigenvalues i:ℝ):ℂ)*Complex.I)
        (∃ C : TwoQubitCircuit K, C.gateCount ≤ s ∧ v∈laboratoryDates H C.eval (1/10)) ∧
          ∀ W : TwoQubitCircuit K, v∈laboratoryDates H W.eval (1/10) →
            (1/2:ℝ)*((4*n).choose (2*n):ℝ)^2*(199/200)^(4*n) ≤
              farCorrelation (univ.powersetCard (2*n))
                (amplitude (star (V⁻¹*W.eval*V).val) p) n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp quarter_price
  filter_upwards [eventually_ge_atTop N] with k hk
  intro ω K n H σ V s v p
  have hn : N≤n := hk.trans ((Nat.le_succ k).trans (show k+1≤2^(k+1) from Nat.lt_two_pow_self.le))
  have hd : 2^K=4*n := by dsimp only [n,K]; rw [show k+3=(k+1)+2 by omega,pow_add]; ring
  have hdim : Fintype.card (Fin K → Bool)=4*n := by simpa only [Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool] using hd
  obtain ⟨⟨C,hC,hv⟩,hall⟩ := first_return_characters k ω s
  refine ⟨⟨C,hC,hv⟩,fun W hw => ?_⟩
  have hq : 2*n≤2^K := hd ▸ (by omega)
  have hh := hall W hw (2*n) hq
  change ((2^K).choose (2*n):ℝ)*(199/200)^min (2*n) (2^K-2*n) ≤
    ‖subsetCharacter (star (V⁻¹*W.eval*V).val) p (2*n)‖ at hh
  rw [hd,show 4*n-2*n=2*n by omega,min_self] at hh
  exact large_differences n (hN n hn) hdim (V⁻¹*W.eval*V)⁻¹ p
    (fun _ => Complex.norm_exp_ofReal_mul_I _) hh

#print axioms first_return_large_differences
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters
