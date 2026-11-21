import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncrementClocks.BinaryBudget
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.RepeatedPathCircuit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.CircuitDeadline

/-! # Nearly Hilbert-dimensional waiting time at the first robust crossing -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.IncrementClocks
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem sqrt_tendsto : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop.mpr fun n => (eventually_ge_atTop (n*n)).mono fun _ hn => Nat.le_sqrt.mpr hn

/-- On almost every infinite Gaussian path, all sufficiently long prefixes take
more than 2^(N−26 floor(sqrt N)) to reach the first robust exponential-budget
crossing. The first return from that very crossing at every budget up to half
the threshold takes at least as long and at most 2^((2^N)^c). -/
theorem gaussian_path_first_crossing_near_dimension_wait :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      let B := crossingWidth N
      let G := (2:ℝ)^(D^c)
      ∃ σ : ℝ, B < σ ∧ σ ≤ G ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (∀ t ∈ Icc (σ-B) (σ+B), ProjectiveCircuitSeparated N (1/10:ℝ) (P/2)
          (unitaryEvolution H.val t)) ∧
        ∀ s ≤ P/2, ∃ v : ℝ, σ+B < v ∧ v ≤ min (σ+G) ((σ+1)*(100:ℝ)^(D-1)) ∧
          HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v) ∧
          ∀ t ∈ Ico σ v, ProjectiveCircuitSeparated N (1/10:ℝ) s (unitaryEvolution H.val t) := by
  obtain ⟨c,K,hK,hfirst⟩ := SpectralJets.gaussian_path_double_exponential_first_return_upper
  obtain ⟨a,b,_,hb,hmass⟩ := gaussian_path_eventual_coefficient_mass
  let L := 12+b
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  have hs := sqrt_tendsto.comp hN
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).comp hs
  refine ⟨c,?_⟩
  filter_upwards [hfirst,hmass] with ω hω hm
  filter_upwards [hω,(tendsto_add_atTop_nat 1).eventually hm,hs.eventually (eventually_ge_atTop 32),
    hpow.eventually (eventually_ge_atTop (100*(1+L)))] with k hcross hcoeff hsqrt hscale
  intro N D u H P B G
  obtain ⟨σ,hstart,hupper,heq,hprior,_,hret⟩ := hcross
  have hσ : 0 ≤ σ := (by positivity : 0 ≤ (2:ℝ)^(N/2)/(K*((N:ℝ)+1)^2)).trans hstart.le
  let j := N.sqrt
  let q := stepBase N
  let C₀ := q^(j+2)*(3^j*Fintype.card (PathLabel (k+1)))
  have hbudget : 2*C₀ ≤ P := high_order_budget (k+1) hsqrt
  have hinc (t : ℝ) (ht : |t| ≤ B) :
      HasProjectiveCircuitApproximation N (1/100:ℝ) C₀ (unitaryEvolution H.val t) := by
    have hm' := path_pauli_coefficient_mass_le u b hcoeff.2
    have htime := high_order_time N L hL hsqrt hscale hm' ht
    obtain ⟨z,hz,C,hC,he⟩ := exists_high_order_path_circuit u j q t
      (by dsimp [q,stepBase]; positivity) htime
    exact ⟨z,hz,C,hC.le,he⟩
  have hfar : ProjectiveCircuitSeparated N (11/100:ℝ) P (unitaryEvolution H.val σ) := by
    intro z hz C hC
    by_contra! h
    have hd := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val σ) P (11/100:ℝ)).mp ⟨z,hz,C,hC,h⟩
    change orbitCircuitDistance H P σ ≤ 11/100 at hd
    linarith only [heq,hd]
  have hB : 0 ≤ B := by dsimp [B,crossingWidth]; positivity
  have hbefore : B < σ := by
    by_contra! h
    obtain ⟨z,hz,C,hC,he⟩ := hinc σ (by rwa [abs_of_nonneg hσ])
    have hh := hfar z hz C (hC.trans (by omega))
    linarith only [hh,he]
  have hwindow (t : ℝ) (ht : t ∈ Icc (σ-B) (σ+B)) :
      ProjectiveCircuitSeparated N (1/10:ℝ) (P/2) (unitaryEvolution H.val t) := by
    have hτ : |σ-t| ≤ B := abs_le.mpr ⟨by linarith only [ht.2],by linarith only [ht.1]⟩
    have h := projectiveCircuitSeparated_unitaryEvolution_backward_cone H (by omega : C₀ ≤ P)
      hfar (hinc (σ-t) hτ) (by norm_num : (1/10:ℝ)+1/100 ≤ 11/100)
    rw [show σ-(σ-t)=t by ring] at h
    exact h.mono_budget (by omega : P/2 ≤ P-C₀)
  refine ⟨σ,hbefore,hupper,heq,hprior,hwindow,?_⟩
  intro s hs'
  obtain ⟨v,hv,hv',hyes,hgap⟩ := hret s hs'
  refine ⟨v,?_,hv',hyes,hgap⟩
  by_contra! h
  have hσv : σ ≤ v := le_trans (le_add_of_nonneg_right (by positivity)) hv.le
  obtain ⟨z,hz,C,hC,he⟩ := hyes
  exact (not_lt_of_ge he) (hwindow v ⟨(sub_le_self _ hB).trans hσv,h⟩ z hz C (hC.trans hs'))

#print axioms gaussian_path_first_crossing_near_dimension_wait
end
end GaloisForLFunctions.HTGeometry.IncrementClocks
