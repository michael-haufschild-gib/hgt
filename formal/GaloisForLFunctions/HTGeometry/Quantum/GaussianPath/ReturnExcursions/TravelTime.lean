import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.DyadicSimulation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathMicroscopicCircuitOrder
import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline
import GaloisForLFunctions.HTGeometry.NearHilbertContinuousCircuitEntropyLaw

/-! # Time needed to travel from an affordable circuit to a robustly hard orbit point -/
open Matrix Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- A cheap circuit at either end of a time increment and a simulator for
the increment would give a cheap circuit at the robust crossing. -/
theorem dyadic_travel_time {n : ℕ} (u : PathShell n) (P s d : ℕ) (σ t : ℝ)
    (hbudget : s+2^(d+8*d.sqrt+8)*Fintype.card (PathLabel n) ≤ P)
    (hh : 9/80 ≤ orbitCircuitDistance ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩ P σ)
    (ht : HasProjectiveCircuitApproximation (n+2) (1/10:ℝ) s (unitaryEvolution (pathHamiltonian u) t)) :
    (2:ℝ)^d < 100*(1+∑ l : PathLabel n, |u l|)*|σ-t| := by
  let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let r := 2^(d+8*d.sqrt+8)*Fintype.card (PathLabel n)
  have hr : s+r ≤ P := hbudget
  have hhard : ProjectiveCircuitSeparated (n+2) (11/100:ℝ) P (unitaryEvolution H.val σ) := by
    intro z hz C hC
    by_contra! he
    have hd : orbitCircuitDistance H P σ ≤ 11/100 :=
      (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mp ⟨z,hz,C,hC,he⟩
    change 9/80 ≤ orbitCircuitDistance H P σ at hh
    linarith only [hh,hd]
  by_contra! hsmall
  have h := projectiveCircuitSeparated_unitaryEvolution_backward_cone H (show r ≤ P by omega)
    hhard (path_dyadic_nearly_linear_simulation u d (σ-t) hsmall) (by norm_num : (1/10:ℝ)+1/100 ≤ 11/100)
  rw [show σ-(σ-t)=t by ring] at h
  obtain ⟨z,hz,C,hC,he⟩ := ht
  exact (h z hz C (hC.trans (by omega))).not_ge he

private theorem polynomial_overhead {N : ℕ} (h : 128 ≤ N.sqrt) :
    524288*(N+1)^2 ≤ 2^N.sqrt := by
  have grow (s : ℕ) (hs : 128 ≤ s) : 524288*(s+1)^4 ≤ 2^s := by
    induction s,hs using Nat.le_induction with
    | base => norm_num
    | succ s hs ih =>
      have hx : (s+2)^4 ≤ 2*(s+1)^4 := by
        obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hs
        ring_nf
        omega
      calc
        _ ≤ 2*(524288*(s+1)^4) := by nlinarith only [hx]
        _ ≤ 2*2^s := Nat.mul_le_mul_left 2 ih
        _ = _ := by rw [pow_succ (2:ℕ) s,Nat.mul_comm]
  have hN : N+1 ≤ (N.sqrt+1)^2 := by
    rw [pow_two]
    exact Nat.lt_succ_sqrt N
  calc
    _ ≤ 524288*((N.sqrt+1)^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 2)
    _ = 524288*(N.sqrt+1)^4 := by ring
    _ ≤ _ := grow _ h

/-- Uniform lower travel time in both directions between every robust
point and every half-budget affordable point on the same Gaussian orbit. -/
theorem gaussian_robust_travel_time :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let x := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian x,isSelfAdjoint_pathHamiltonian x⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∀ σ t : ℝ, 9/80 ≤ orbitCircuitDistance H P σ → ∀ s ≤ P/2,
        HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val t) →
        (2:ℝ)^(N-10*N.sqrt) < |σ-t| := by
  obtain ⟨_,v,_,_,hmass⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨m,hm⟩ := exists_nat_gt (12+v)
  filter_upwards [hmass] with ω hω
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hω,eventually_ge_atTop (128*128),
    eventually_ge_atTop m] with k hcoeff hk hm'
  intro N x H P σ t hrobust s hs hcheap
  let h := N.sqrt
  let d := N-9*h
  let J := Fintype.card (PathLabel (k+1))
  have hh : 128 ≤ h := Nat.le_sqrt.mpr (by dsimp [N]; omega)
  have hbig := polynomial_overhead hh
  have hN : 10*h ≤ N :=
    (Nat.mul_le_mul_right h (show 10 ≤ h by omega)).trans (Nat.sqrt_le N)
  have hd : d.sqrt ≤ h := Nat.sqrt_le_sqrt (Nat.sub_le N (9*h))
  have hsumd : d+9*h=N := Nat.sub_add_cancel (by omega)
  have hJ : J ≤ 12*N := by
    dsimp [J,N,PathLabel]
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have overhead : 2^8*(128*(N+1)*J) ≤ 2^h := by
    apply le_trans _ hbig
    nlinarith only [Nat.mul_le_mul_left (N+1) hJ,Nat.zero_le N,Nat.zero_le (N*N)]
  have hbudget : 2*(2^(d+8*d.sqrt+8)*J) ≤ P := by
    change _ ≤ 2^N/(64*(N+1))
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    calc
      _ = 2^(d+8*d.sqrt)*(2^8*(128*(N+1)*J)) := by rw [pow_add (2:ℕ) (d+8*d.sqrt) 8]; ring
      _ ≤ 2^(d+8*d.sqrt)*2^h := Nat.mul_le_mul_left _ overhead
      _ ≤ 2^N := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have htime := dyadic_travel_time x P s d σ t (by change s+2^(d+8*d.sqrt+8)*J ≤ P; omega)
    hrobust hcheap
  have hscale : 12+v ≤ (N:ℝ) := hm.le.trans (by exact_mod_cast (show m ≤ N by dsimp [N]; omega))
  have hsum := (path_pauli_coefficient_mass_le x v hcoeff.2).trans
    (mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg N))
  have hbig' : 524288*((N:ℝ)+1)^2 ≤ (2:ℝ)^h := by exact_mod_cast hbig
  have hmass' : 100*(1+∑ l : PathLabel (k+1), |x l|) ≤ (2:ℝ)^h := by
    apply le_trans _ hbig'
    nlinarith only [hsum,Nat.cast_nonneg (α := ℝ) N,sq_nonneg (N:ℝ)]
  by_contra! ht
  have hbad := mul_le_mul hmass' ht (abs_nonneg _) (by positivity)
  rw [← pow_add,show h+(N-10*h)=d by dsimp [d]; omega] at hbad
  exact htime.not_ge hbad

#print axioms dyadic_travel_time
#print axioms gaussian_robust_travel_time
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions
