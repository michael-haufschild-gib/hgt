import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPathMicroscopicCircuitOrder
import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary

/-!
# First robust circuit threshold on Gaussian Pauli prefixes

A sparse product formula uses only the actual path interactions. Allocating
half the exponential circuit budget to short increments protects an interval
of physical duration proportional to 2^(N/2)/(N+1)^2 at the first crossing.
-/
open Matrix Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private def stepRoot (n : ℕ) := 2^(n/2)/(64*(n+1))

private theorem stepRoot_large {n : ℕ} (hn : 32 ≤ n) :
    0 < stepRoot n ∧ 2^(n/2) ≤ (128*(n+1))*stepRoot n := by
  have hpow (k : ℕ) (hk : 16 ≤ k) : 128*(2*k+2) ≤ 2^k := by
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih => rw [pow_succ]; omega
  have hF : 64*(n+1) ≤ 2^(n/2) :=
    (show 64*(n+1) ≤ 128*(2*(n/2)+2) by omega).trans (hpow _ (by omega))
  have hp : 0 < stepRoot n := Nat.div_pos hF (by positivity)
  have hnear := Nat.lt_mul_div_succ (2^(n/2)) (by positivity : 0 < 64*(n+1))
  change 2^(n/2) < 64*(n+1)*(stepRoot n+1) at hnear
  refine ⟨hp,hnear.le.trans ?_⟩
  calc
    _ ≤ 64*(n+1)*(2*stepRoot n) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring

private theorem step_budget (n : ℕ) :
    2*((stepRoot (n+2))^2 * Fintype.card (PathLabel n)) ≤ nearHilbertContinuousCircuitBudget (n+2) := by
  let N := n+2
  let F := 64*(N+1)
  let q := stepRoot N
  let m := Fintype.card (PathLabel n)
  have hm : 2*m ≤ F := by
    dsimp [m,F,N,PathLabel]
    simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hmul : q*F ≤ 2^(N/2) := Nat.div_mul_le_self _ _
  change 2*(q^2*m) ≤ 2^N/F
  apply (Nat.le_div_iff_mul_le (by dsimp [F]; positivity)).mpr
  calc
    _ = (2*m)*(q^2*F) := by ring
    _ ≤ F*(q^2*F) := Nat.mul_le_mul_right _ hm
    _ = (q*F)^2 := by ring
    _ ≤ (2^(N/2))^2 := Nat.pow_le_pow_left hmul _
    _ ≤ 2^N := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)

private theorem sparse_increment {n : ℕ} (u : PathShell n) (q : ℕ) (hq : 0 < q) (t : ℝ)
    (h : (∑ l : PathLabel n, |u l|)*|t| ≤ (q:ℝ)/10) :
    HasProjectiveCircuitApproximation (n+2) (1/100:ℝ) (q^2*Fintype.card (PathLabel n))
      (unitaryEvolution (pathHamiltonian u) t) := by
  obtain ⟨z,hz,C,hC,he⟩ := exists_sparse_path_circuit u t (q^2) (by positivity)
  refine ⟨z,hz,C,hC.le,he.trans ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have hs := pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (abs_nonneg t)) h 2
  push_cast
  linarith only [hs]

/-- On one infinite iid disorder, every sufficiently long prefix reaches
its first robust exponential budget boundary. A common constant K protects
both sides of that crossing for 2^⌊N/2⌋/(K(N+1)^2) time units; every smaller
budget up to half has an attained first return beyond this interval. -/
theorem gaussian_pauli_prefix_first_threshold_and_return :
    ∃ K : ℝ, 0 < K ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let P := nearHilbertContinuousCircuitBudget N
      let B := (2:ℝ)^(N/2)/(K*((N:ℝ)+1)^2)
      ∃ σ : ℝ, B < σ ∧ orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        (∀ t ∈ Icc (σ-B) (σ+B), ProjectiveCircuitSeparated N (1/10:ℝ) (P/2)
          (unitaryEvolution H.val t)) ∧
        ∀ s ≤ P/2, ∃ v : ℝ, σ+B < v ∧ v ≤ (σ+1)*(100:ℝ)^(2^N-1) ∧
          HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v) ∧
          ∀ t ∈ Ico σ v, ProjectiveCircuitSeparated N (1/10:ℝ) s (unitaryEvolution H.val t) := by
  obtain ⟨a,b,_,hb,hmass⟩ := gaussian_path_eventual_coefficient_mass
  let L := 12+b
  let K := 1280*L
  have hL : 0 < L := by dsimp [L]; linarith
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  filter_upwards [hmass,gaussian_path_all_prefixes_maximally_projective] with ω hm hg
  have hN : Tendsto (fun k : ℕ => k+3) atTop atTop := tendsto_add_atTop_nat 3
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hm,hN.eventually (eventually_ge_atTop 32),
    hN.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier]
    with k hω hlarge hent
  let N := k+3
  let d := 2^N-1
  let q := stepRoot N
  let u := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  let B := (2:ℝ)^(N/2)/(K*((N:ℝ)+1)^2)
  let e : (Fin N → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hpos : 0 < (2:ℕ)^N := by positivity
                  dsimp [d]; omega))
  obtain ⟨hq,hwidth⟩ := stepRoot_large hlarge
  have hwidth' : (2:ℝ)^(N/2) ≤ (128*((N:ℝ)+1))*(q:ℝ) := by exact_mod_cast hwidth
  have hm' : (∑ l, |u l|) ≤ L*(N:ℝ) := path_pauli_coefficient_mass_le u b hω.2
  have hB : 0 ≤ B := by dsimp [B,K]; positivity
  apply first_circuit_threshold_of_increment e H ((hg k).comp_equiv e.symm) hent B hB (step_budget (k+1))
  intro t ht
  apply sparse_increment u q hq t
  have hbound : L*((N:ℝ)+1)*B ≤ (q:ℝ)/10 := by
    dsimp [B,K]
    rw [← mul_div_assoc,div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [mul_le_mul_of_nonneg_left hwidth' (show 0 ≤ 10*L*((N:ℝ)+1) by positivity)]
  calc
    _ ≤ (L*((N:ℝ)+1))*B :=
      mul_le_mul (hm'.trans (mul_le_mul_of_nonneg_left (by linarith) hL.le))
        ht (abs_nonneg _) (by positivity)
    _ ≤ _ := hbound

#print axioms gaussian_pauli_prefix_first_threshold_and_return
end
end GaloisForLFunctions.HTGeometry
