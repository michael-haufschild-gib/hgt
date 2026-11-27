import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.EighthPower.FirstPassage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.CrossingDates.AfterVisit.CommonReturn

/-! # Common low return after an above-sweep crossing -/
open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks PrecisionReturns
noncomputable section

/-- Following any tenth-error visit, all the indicated above-sweep budgets
and crossing heights select the same next low return. This is also the
return selected by observing one time unit after the visit. -/
theorem gaussian_eighth_power_common_return :
    ∃ κ>0, ∃ δ>0, ∃ b>0, ∃ L>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let N : ℝ := (n+1:ℕ)
      let H := (⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩ :
        selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ))
      ∀ (v : ℝ) (s r : ℕ), ((s+r:ℕ):ℝ)≤κ*K →
        HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) →
        let w := firstVisit H (v+1) r (1/10)
        v+δ*K^(65/64:ℝ)<w ∧ ∀ q : ℕ, let m : ℝ := (2*s+q:ℕ)
          m≤b*N → ∀ ρ∈Icc (9/80:ℝ) (1/8),
            let τ := firstExcessAfter ω n (s+q) v ρ
            L≤K*τ^2 ∧ τ^8≤ max ((1/(prefixIndex n:ℝ))^96) (m/(b*N)) ∧
              firstVisit H (v+τ) r (1/10)=w := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,_,_,_,_,_,_,_,_,hcommon⟩ := WeakBondDeficit.gaussian_deficit_common_return
  obtain ⟨b,hb,L,hL,hpass⟩ := gaussian_eighth_power_first_passage
  refine ⟨κ,hκ,δ,hδ,b,hb,L,hL,?_⟩
  filter_upwards [hcommon,hpass] with ω hc hp
  filter_upwards [hc,hp,eventually_ge_atTop ⌈max (A^2/L) (1/δ)⌉₊] with n hc' hp' hn
  intro K N H v s r hbudget hv w
  obtain ⟨hgap,hsame,_⟩ := hc' v s r hbudget hv
  refine ⟨hgap,?_⟩
  intro q m hm ρ hρ τ
  obtain ⟨ht,hu,hl,_,_⟩ := hp' v s q hm hv ρ hρ
  have hK₁ : 1≤K := by dsimp only [K]; exact_mod_cast (by omega : 1≤n+2)
  have hK := zero_lt_one.trans_le hK₁
  have hsize : max (A^2/L) (1/δ)≤K := (Nat.le_ceil _).trans
    (Nat.cast_le.mpr (show ⌈max (A^2/L) (1/δ)⌉₊≤n+2 by omega))
  have hA₂ := (div_le_iff₀ hL).mp ((le_max_left ..).trans hsize)
  have hl' : A/K≤τ := by
    apply (div_le_iff₀ hK).mpr
    apply le_of_sq_le_sq _ (mul_nonneg ht.1 hK.le)
    change L≤K*τ^2 at hl
    linarith only [hA₂,mul_le_mul_of_nonneg_left hl hK.le]
  have ht' : 1≤δ*K^(65/64:ℝ) := calc
    1 ≤ δ*K := by have h := (div_le_iff₀ hδ).mp ((le_max_right ..).trans hsize); linarith only [h]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by simpa only [rpow_one] using
      (rpow_le_rpow_of_exponent_le hK₁ (by norm_num : (1:ℝ)≤65/64))) hδ.le
  exact ⟨hl,hu,hsame _ ⟨hl',ht.2.trans ht'⟩⟩

#print axioms gaussian_eighth_power_common_return
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
