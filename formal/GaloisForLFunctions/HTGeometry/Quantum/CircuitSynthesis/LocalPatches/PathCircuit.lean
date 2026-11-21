import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PrefixCircuit
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.SiteWords
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Repeated local simulation of the nearest-neighbour Pauli Hamiltonian -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section
attribute [local instance] instCStarAlgebraRegister

private theorem approx_power {N s : ℕ} {U : Register N} {ε : ℝ} (hU : U ∈ unitary (Register N))
    (h : HasProjectiveCircuitApproximation N ε s U) (r : ℕ) :
    HasProjectiveCircuitApproximation N ((r:ℝ)*ε) (r*s) (U^r) := by
  induction r with
  | zero =>
    exact ⟨1,norm_one,TwoQubitCircuit.one N,Nat.zero_le _,by simp [TwoQubitCircuit.one_eval]⟩
  | succ r ih =>
    simpa only [Nat.cast_succ,add_mul,one_mul,Nat.add_mul,pow_succ] using approx_product hU ih h

/-- A physical local circuit with an arbitrary number of timesteps.
The error involves the largest individual coupling, the number of sites,
and the order, with no power of the total interaction mass. -/
theorem path_patch_circuit {n : ℕ} (u : PathShell n) (R : ℝ) (hR : 0 ≤ R)
    (hcap : ∀ l, |u l| ≤ R) (p r : ℕ) (hr : 0 < r) (t : ℝ) (ht : 0 ≤ t) :
    let N := n+2
    let K := patchScale p (21*R)
    HasProjectiveCircuitApproximation N (14*(N:ℝ)*(K*t)*(K*t/r)^p)
      (r*(N*patchGateCost p 21)) (unitaryEvolution (pathHamiltonian u) t) := by
  intro N K
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have h := prefix_circuit (siteWords u) p 21 (21*R) (by positivity)
    (siteWords_length u) (siteWords_mass u R hR hcap) (fun i x hx => (siteWords_properties u i x hx).1)
    (fun i x hx => (siteWords_properties u i x hx).2) (siteWords_commute u)
    (t/r) (div_nonneg ht hr'.le) N
  rw [siteWords_sum] at h
  have hmem := unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) (t/r)
  have hpow := approx_power hmem h r
  change HasProjectiveCircuitApproximation N
    ((r:ℝ)*((N:ℝ)*(14*(K*(t/r))^(p+1)))) _ (exp ((t/r) • ((-Complex.I) • pathHamiltonian u))^r) at hpow
  rw [exp_real_smul_pow,show (r:ℝ)*(t/r)=t by field_simp] at hpow
  have he : (r:ℝ)*((N:ℝ)*(14*(K*(t/r))^(p+1))) = 14*(N:ℝ)*(K*t)*(K*t/r)^p := by
    rw [pow_succ,show K*(t/(r:ℝ))=K*t/r by ring]
    field_simp
  rw [he] at hpow
  exact hpow

/-- Inverting the physical circuit simulates a negative time with the same gate count. -/
theorem path_patch_circuit_abs {n : ℕ} (u : PathShell n) (R : ℝ) (hR : 0 ≤ R)
    (hcap : ∀ l, |u l| ≤ R) (p r : ℕ) (hr : 0 < r) (t : ℝ) :
    let N := n+2
    let K := patchScale p (21*R)
    HasProjectiveCircuitApproximation N (14*(N:ℝ)*(K*|t|)*(K*|t|/r)^p)
      (r*(N*patchGateCost p 21)) (unitaryEvolution (pathHamiltonian u) t) := by
  rcases le_total 0 t with ht|ht
  · simpa only [abs_of_nonneg ht] using path_patch_circuit u R hR hcap p r hr t ht
  · let H : selfAdjoint (Register (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
    have h := path_patch_circuit u R hR hcap p r hr (-t) (neg_nonneg.mpr ht)
    simpa only [abs_of_nonpos ht,neg_neg] using h.neg_time H

/-- An error criterion with the step count cleared from the denominator. -/
theorem path_patch_at_error {n : ℕ} (u : PathShell n) (R : ℝ) (hR : 0 ≤ R)
    (hcap : ∀ l, |u l| ≤ R) (p r : ℕ) (hr : 0 < r) (t ε : ℝ) (ht : 0 ≤ t)
    (he : 14*((n+2:ℕ):ℝ)*(patchScale p (21*R)*t)^(p+1) ≤ ε*(r:ℝ)^p) :
    HasProjectiveCircuitApproximation (n+2) ε (r*((n+2)*patchGateCost p 21))
      (unitaryEvolution (pathHamiltonian u) t) := by
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  apply approx_enlarge (path_patch_circuit u R hR hcap p r hr t ht) _ le_rfl
  rw [div_pow,←mul_div_assoc]
  apply (div_le_iff₀ (pow_pos hr' _)).mpr
  calc
    _ = 14*((n+2:ℕ):ℝ)*(patchScale p (21*R)*t)^(p+1) := by rw [pow_succ]; ring
    _ ≤ _ := he

#print axioms path_patch_circuit_abs
#print axioms path_patch_at_error
end
end GaloisForLFunctions.HTGeometry.LocalPatches
