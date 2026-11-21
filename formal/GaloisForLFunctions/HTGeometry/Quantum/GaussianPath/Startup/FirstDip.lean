import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.AfterReturn
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.FirstCrossing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # The gate count following the first low-cost dip from the robust crossing -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.IncrementClocks
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem first_visit_with_error_margin {N : ℕ} (H : selfAdjoint (Reg N))
    (a δ : ℝ) (s : ℕ) (hδ : 1/20 ≤ δ) :
    ∃ v : ℝ, IsLeast {t | a ≤ t ∧ HasProjectiveCircuitApproximation N δ s
      (unitaryEvolution H.val t)} v ∧ v ≤ (|a|+1)*(160:ℝ)^(2^N-1) := by
  let E := {t | HasProjectiveCircuitApproximation N δ s (unitaryEvolution H.val t)}
  have hclosed : IsClosed E := by
    simp only [E,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le (orbitCircuitDistance_lipschitz H s).continuous continuous_const
  let d := 2^N-1
  let e : (Fin N → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans (finCongr (by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    have : 0 < (2:ℕ)^N := by positivity
    dsimp [d]; omega))
  let B := (|a|+1)*(160:ℝ)^d
  obtain ⟨w,hw,z,hz,C,hC,he⟩ := projective_operator_zero_gate_return_after e H a 159
  have hB : w ≤ B := by norm_num at hw; exact hw.2
  have hE : w ∈ E := ⟨z,hz,C,hC.trans (Nat.zero_le _),he.trans (by
    apply le_trans _ hδ
    norm_num
    linarith only [Real.pi_lt_four])⟩
  have hne : (Icc a B ∩ E).Nonempty := ⟨w,⟨by linarith only [le_abs_self a,hw.1],hB⟩,hE⟩
  obtain ⟨v,hv,hmin⟩ := (isCompact_Icc.inter_right hclosed).exists_isMinOn hne continuous_id.continuousOn
  refine ⟨v,⟨⟨hv.1.1,hv.2⟩,?_⟩,hv.1.2⟩
  rintro t ⟨ht,heasy⟩
  by_cases h : t ≤ B
  · exact hmin (show t ∈ Icc a B ∩ E from ⟨⟨ht,h⟩,heasy⟩)
  · exact hv.1.2.trans (le_of_not_ge h)

/-- From the first robust crossing, take the very first s-gate dip at any
error δ between 1/20 and 1/10. The following interval has cost between
cN−s and JN+s at δ+1/20, and the lower bound holds at 1/10 as well. -/
theorem gaussian_path_gate_count_after_first_dip :
    ∃ A c : ℝ, ∃ J q : ℕ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      let B := crossingWidth N
      ∃ σ : ℝ, B < σ ∧ σ ≤ (2:ℝ)^((2^N:ℕ)^q) ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧ ∀ s ≤ P/2, ∀ δ ∈ Icc (1/20:ℝ) (1/10),
        ∃ v : ℝ, IsLeast {w | σ ≤ w ∧ HasProjectiveCircuitApproximation N δ s (unitaryEvolution H.val w)} v ∧
          σ+B < v ∧ v ≤ (σ+1)*(160:ℝ)^(2^N-1) ∧ ∀ t ∈ Icc (A/(N:ℝ)) (1/Real.sqrt N),
          ∃ r : ℕ, IsLeast {j | HasProjectiveCircuitApproximation N (δ+1/20) j
            (unitaryEvolution H.val (v+t))} r ∧ c*(N:ℝ) ≤ (s:ℝ)+r ∧ r ≤ s+J*N ∧
            ∀ j : ℕ, HasProjectiveCircuitApproximation N (1/10:ℝ) j (unitaryEvolution H.val (v+t)) →
              c*(N:ℝ) ≤ (s:ℝ)+j := by
  obtain ⟨A,c,J,hA,hc,hw⟩ := gaussian_path_minimum_after_accurate_return
  obtain ⟨q,hq⟩ := gaussian_path_first_crossing_near_dimension_wait
  refine ⟨A,c,J,q,hA,hc,?_⟩
  filter_upwards [hw,hq] with ω hω hf
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω,hf] with k hret hcross
  intro N u H P B
  obtain ⟨σ,hB,hG,hd,hprior,havoid,_⟩ := hcross
  have hB₀ : 0 ≤ B := by dsimp [B,crossingWidth]; positivity
  refine ⟨σ,hB,hG,hd,hprior,?_⟩
  intro s hs δ hδ
  obtain ⟨v,hfirst,hdeadline⟩ := first_visit_with_error_margin H σ δ s hδ.1
  rw [abs_of_nonneg (hB₀.trans hB.le)] at hdeadline
  have hgap : σ+B < v := by
    by_contra! h
    obtain ⟨z,hz,C,hC,he⟩ := hfirst.1.2
    exact (not_lt_of_ge (he.trans hδ.2)) (havoid v ⟨by linarith only [hfirst.1.1,hB₀],h⟩ z hz C (hC.trans hs))
  refine ⟨v,hfirst,hgap,hdeadline,?_⟩
  intro t ht
  obtain ⟨r,hr,hlo,hhi⟩ := hret v s δ (δ+1/20) le_rfl (by linarith only [hδ.2]) hfirst.1.2 t ht
  refine ⟨r,hr,hlo,hhi,?_⟩
  rintro j ⟨z,hz,C,hC,he⟩
  have hj := hr.2 (show HasProjectiveCircuitApproximation N (δ+1/20) j
      (unitaryEvolution H.val (v+t)) from ⟨z,hz,C,hC,he.trans (by linarith only [hδ.1])⟩)
  exact hlo.trans (add_le_add le_rfl (by exact_mod_cast hj))

#print axioms gaussian_path_gate_count_after_first_dip
end
end GaloisForLFunctions.HTGeometry.IncrementClocks

