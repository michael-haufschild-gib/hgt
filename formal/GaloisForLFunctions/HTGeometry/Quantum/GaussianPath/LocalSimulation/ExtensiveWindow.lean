import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Moments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PersistentCircuitFloor
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PathCircuit

/-! # Extensive minimum circuit cost on every fixed inverse-power startup window -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalPatches
noncomputable section

/-- From A/N through N^(-1/m) the minimum physical gate count is bounded
above and below by deterministic multiples of N, uniformly in time and tolerance. -/
theorem gaussian_path_extensive_inverse_power_windows (m : ℕ) (hm : 1 ≤ m) :
    ∃ A c : ℝ, ∃ J : ℕ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ t : ℝ, A/(N:ℝ) ≤ t → (N:ℝ)*t^m ≤ 1 → ∀ ε ∈ Icc (1/20:ℝ) (1/4), ∃ s : ℕ,
        IsLeast {j | HasProjectiveCircuitApproximation N ε j (unitaryEvolution H t)} s ∧
        c*(N:ℝ) ≤ s ∧ s ≤ J*N := by
  classical
  let p := 2*m-1
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hdeg : p+1 = m*2 := by dsimp [p]; omega
  let L := (8:ℝ)^(p+1)*(1+((p:ℝ)+1)*21)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  obtain ⟨A,c,hA,hc,hfloor⟩ := gaussian_pauli_persistent_circuit_floor 1 zero_lt_one
  obtain ⟨B,hB,hcap⟩ := gaussian_prefix_local_moment (p+1)
  obtain ⟨r,hr⟩ := exists_nat_gt (280*L^(p+1)*B+1)
  have hz : 0 ≤ 280*L^(p+1)*B := by positivity
  have hr1 : 1 ≤ (r:ℝ) := by linarith only [hr,hz]
  have hrp : (r:ℝ) ≤ (r:ℝ)^p := le_self_pow₀ hr1 (by omega)
  have hrpos : 0 < r := by exact_mod_cast (zero_lt_one.trans_le hr1 : (0:ℝ)<r)
  refine ⟨A,c,r*patchGateCost p 21,hA,hc,?_⟩
  filter_upwards [hfloor,hcap] with ω hw hω
  filter_upwards [hw,hω] with n hlow hR
  intro N H t hlo htm ε hε
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hN0 := zero_lt_one.trans_le hN
  have ht := (div_pos hA hN0).le.trans hlo
  have ht1 : t ≤ 1 := by
    by_contra! hh
    have hpow := one_lt_pow₀ hh (by omega : m ≠ 0)
    exact hpow.not_ge ((le_mul_of_one_le_left (pow_nonneg ht m) hN).trans htm)
  obtain ⟨R,hR,hcoeff,hmoment⟩ := hR
  have hR0 := zero_le_one.trans hR
  let K := patchScale p (21*R)
  have hK : K ≤ L*R := by
    dsimp [K,L,patchScale]
    rw [mul_assoc _ (1+_) R]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [hR]
  have hK0 : 0 ≤ K := by dsimp [K,patchScale]; positivity
  have hmass : 14*(N:ℝ)*(K*t)^(p+1) ≤ 14*L^(p+1)*B := calc
    _ ≤ 14*(N:ℝ)*((L*R)*t)^(p+1) := by gcongr
    _ = (14*L^(p+1)*(N:ℝ)*t^(p+1))*R^(p+1) := by rw [mul_pow,mul_pow]; ring
    _ ≤ (14*L^(p+1)*(N:ℝ)*t^(p+1))*(B*(N:ℝ)) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = (14*L^(p+1)*B)*((N:ℝ)*t^m)^2 := by
      rw [show t^(p+1) = (t^m)^2 by rw [hdeg,pow_mul]]
      ring
    _ ≤ (14*L^(p+1)*B)*1 := mul_le_mul_of_nonneg_left
      (by simpa using pow_le_pow_left₀ (mul_nonneg hN0.le (pow_nonneg ht m)) htm 2) (by positivity)
    _ = _ := mul_one _
  have hfit := path_patch_at_error (pathPauliDisorderShell ω n) R hR0 hcoeff p r hrpos t
    (1/20) ht (hmass.trans (by linarith only [hr,hrp]))
  let affordable (j : ℕ) := HasProjectiveCircuitApproximation N ε j (unitaryEvolution H t)
  have hfit' : affordable (r*(N*patchGateCost p 21)) := approx_enlarge hfit hε.1 le_rfl
  have hex : ∃ j, affordable j := ⟨_,hfit'⟩
  obtain ⟨z,_,C,hC,he⟩ := Nat.find_spec hex
  have hmin := (hlow t hlo ht1).1 C z (he.trans hε.2)
  exact ⟨Nat.find hex,⟨Nat.find_spec hex,fun _ hj => Nat.find_min' hex hj⟩,
    hmin.trans (by exact_mod_cast hC),
    (Nat.find_min' hex hfit').trans_eq (by ring)⟩

/-- After any accurate visit of cost s, every lag in the same inverse-power
window has cost between cN−s and JN+s at compatible approximation errors. -/
theorem gaussian_extensive_window_after_return (m : ℕ) (hm : 1 ≤ m) :
    ∃ A c : ℝ, ∃ J : ℕ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ (v : ℝ) (s : ℕ) (α ε : ℝ), α+1/20 ≤ ε → α+ε ≤ 1/4 →
        HasProjectiveCircuitApproximation N α s (unitaryEvolution H v) →
        ∀ t : ℝ, A/(N:ℝ) ≤ t → (N:ℝ)*t^m ≤ 1 → ∃ r : ℕ,
          IsLeast {j | HasProjectiveCircuitApproximation N ε j (unitaryEvolution H (v+t))} r ∧
          c*(N:ℝ) ≤ (s:ℝ)+r ∧ r ≤ s+J*N := by
  classical
  obtain ⟨A,c,J,hA,hc,hw⟩ := gaussian_path_extensive_inverse_power_windows m hm
  refine ⟨A,c,J,hA,hc,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω] with n hn
  let N := n+2
  let H : selfAdjoint (Register N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  intro _ _ v s α ε he hf hv t hlo htm
  have compose {i j : ℕ} {e f g x y : ℝ}
      (hx : HasProjectiveCircuitApproximation N e i (unitaryEvolution H.val x))
      (hy : HasProjectiveCircuitApproximation N f j (unitaryEvolution H.val y)) (h : e+f ≤ g) :
      HasProjectiveCircuitApproximation N g (i+j) (unitaryEvolution H.val (x+y)) := by
    have hh := approx_enlarge (approx_product (unitaryEvolution_mem_unitary H.2 y) hx hy) h le_rfl
    rwa [show unitaryEvolution H.val x * unitaryEvolution H.val y = unitaryEvolution H.val (x+y) by
      simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul H (x+y) y] at hh
  obtain ⟨a,ha,_,hcount⟩ := hn t hlo htm (1/20) (by constructor <;> norm_num)
  obtain ⟨b,hb,hfloor,_⟩ := hn t hlo htm (1/4) (by constructor <;> norm_num)
  let affordable (j : ℕ) := HasProjectiveCircuitApproximation N ε j (unitaryEvolution H.val (v+t))
  have hfit : affordable (s+a) := compose hv ha.1 he
  have hex : ∃ j, affordable j := ⟨_,hfit⟩
  have hr : affordable (Nat.find hex) := Nat.find_spec hex
  have hinc := compose (hv.neg_time H) hr hf
  rw [neg_add_cancel_left] at hinc
  exact ⟨Nat.find hex,⟨hr,fun _ hj => Nat.find_min' hex hj⟩,
    hfloor.trans (by exact_mod_cast hb.2 hinc),
    (Nat.find_min' hex hfit).trans (Nat.add_le_add_left hcount _)⟩

#print axioms gaussian_extensive_window_after_return
#print axioms gaussian_path_extensive_inverse_power_windows
end
end GaloisForLFunctions.HTGeometry.LocalPatches
