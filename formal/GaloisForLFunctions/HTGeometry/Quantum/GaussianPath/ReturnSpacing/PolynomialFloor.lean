import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PersistentCircuitFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.DyadicCounts
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PrefixScales

/-! # Polynomial separation of low-cost returns on one Gaussian Pauli chain -/
open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- At scale k, ck²⁴ isolated fields of strength 1/(8k) force at least ck²⁴/8
gates throughout [1,k] once the available field strength exceeds 4π. -/
private theorem floor_between_one_and_scale {n : ℕ} (u : PathShell n)
    {c k : ℝ} (hc : 0 < c) (hk : 1 ≤ k) (hlarge : 32*Real.pi ≤ c*k^23)
    (S : Finset (Fin (n+2))) (hS : c*k^24 ≤ S.card)
    (his : ∀ s ∈ S, isolatedLongitudinalSite u (1/(8*k)) ((1/(8*k))/200) s)
    (t : ℝ) (ht : 1 ≤ t) (htk : t ≤ k) (C : TwoQubitCircuit (n+2)) (z : ℂ)
    (herr : ‖unitaryEvolution (pathHamiltonian u) t-z • (C.eval : Reg (n+2))‖ ≤ 1/4) :
    c*k^24/8 ≤ C.gateCount := by
  let N : ℝ := (n+2:ℕ)
  let L := c*k^24
  let p := L/N
  let q := 1/(8*k)
  have hN : 0 < N := by dsimp [N]; positivity
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hL : 0 < L := mul_pos hc (pow_pos hkpos 24)
  have hp : 0 < p := div_pos hL hN
  have hq : 0 < q := by dsimp [q]; positivity
  have hpN : p*N = L := div_mul_cancel₀ _ hN.ne'
  have hqL : q*L = c*k^23/8 := by dsimp [q,L]; field_simp [hkpos.ne']; ring
  have hl : c*k^23 ≤ L := by
    dsimp [L]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hk (by decide : 23 ≤ 24)) hc.le
  have h8 : 8 ≤ p*N := by rw [hpN]; linarith only [hlarge,hl,Real.pi_gt_three]
  have hstart : 4*Real.pi/(q*p) ≤ N*t := by
    apply (div_le_iff₀ (mul_pos hq hp)).mpr
    calc
      _ ≤ q*L := by linarith only [hlarge,hqL]
      _ ≤ (q*L)*t := le_mul_of_one_le_right (mul_nonneg hq.le hL.le) ht
      _ = _ := by rw [← hpN]; ring
  have hend : q*t ≤ 1/8 := by
    apply (mul_le_mul_of_nonneg_left htk hq.le).trans_eq
    dsimp [q]; field_simp [hkpos.ne']
  have hf := isolated_sites_uniform_circuit_floor u q p hq hp S (hpN.le.trans hS) his h8 t
    (zero_lt_one.trans_le ht) hstart hend C z herr
  change p/8*N ≤ _ at hf
  calc
    _ = p/8*N := by change L/8 = _; rw [← hpN]; ring
    _ ≤ _ := hf

/-- Almost surely on every sufficiently long prefix, every approximation up
to scalar at error 1/4 costs at least c√N throughout [A/N,N^(1/48)/4].
The same floor applies to the combined cost of two projective approximations
at error 1/10 with this lag, simultaneously for every time origin. -/
theorem gaussian_pauli_polynomial_interval_cost_floor :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ t : ℝ, A/(N:ℝ) ≤ t → t ≤ (N:ℝ)^((48:ℝ)⁻¹)/4 →
        (∀ (C : TwoQubitCircuit N) (z : ℂ), ‖unitaryEvolution H t-z • (C.eval : Reg N)‖ ≤ 1/4 →
          c*Real.sqrt (N:ℝ) ≤ C.gateCount) ∧
        ∀ v : ℝ, ∀ s r : ℕ, HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H v) →
          HasProjectiveCircuitApproximation N (1/10:ℝ) r (unitaryEvolution H (v+t)) →
          c*Real.sqrt (N:ℝ) ≤ (s:ℝ)+r := by
  obtain ⟨A,a,hA,ha,hearly⟩ := gaussian_pauli_persistent_circuit_floor 1 zero_lt_one
  obtain ⟨b,hb,hsites⟩ := gaussian_pauli_dyadic_isolated_sites
  let c := min a (b/(8*2^25))
  have hc : 0 < c := lt_min ha (by positivity)
  refine ⟨A,c,hA,hc,?_⟩
  filter_upwards [hearly,hsites] with ω hω hsitesω
  have hkdiv : Tendsto (fun j : ℕ => (2:ℝ)^j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hbig := (hkdiv.comp tendsto_isolatedFieldScaleIndex).eventually_ge_atTop (32*Real.pi/b)
  filter_upwards [hω,tendsto_isolatedFieldScaleIndex.eventually hsitesω,hbig] with n hshort hmany hbig
  let N := n+2
  let k : ℕ := 2^isolatedFieldScaleIndex n
  have hk : 1 ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ 2^isolatedFieldScaleIndex n from Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2:ℕ)) _))
  obtain ⟨hfit,hsqrt,hroot⟩ := isolatedFieldScale_bounds n
  obtain ⟨S,hS,his⟩ := hmany n hfit
  have hlarge : 32*Real.pi ≤ b*(k:ℝ)^23 := by
    have hg : 32*Real.pi/b ≤ (k:ℝ) := by simpa [Function.comp_def,k] using hbig
    apply ((div_le_iff₀ hb).mp hg).trans
    rw [mul_comm (k:ℝ)]
    exact mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_right₀ hk (show 1 ≤ 23 by decide)) hb.le
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
  intro _ _ t ht hT
  suffices hf : ∀ (C : TwoQubitCircuit N) (z : ℂ),
      ‖unitaryEvolution H.val t-z • (C.eval : Reg N)‖ ≤ 1/4 → c*Real.sqrt (N:ℝ) ≤ C.gateCount by
    exact ⟨hf,combined_endpoint_cost_of_lag_floor H hf⟩
  intro C z herr
  by_cases ht1 : t ≤ 1
  · refine le_trans ?_ ((hshort t ht ht1).1 C z herr)
    exact mul_le_mul (min_le_left ..) (Real.sqrt_le_iff.mpr ⟨by positivity,by
      have hN : 1 ≤ (N:ℝ) := by exact_mod_cast (show 1 ≤ n+2 by omega)
      nlinarith only [hN,sq_nonneg ((N:ℝ)-1)]⟩) (Real.sqrt_nonneg _) ha.le
  · refine le_trans ?_ (floor_between_one_and_scale u hb hk hlarge S hS his t
      (le_of_not_ge ht1) (hT.trans hroot) C z herr)
    calc
      c*Real.sqrt (N:ℝ) ≤ (b/(8*2^25))*(2^25*(k:ℝ)^24) :=
        mul_le_mul (min_le_right ..) hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring

#print axioms gaussian_pauli_polynomial_interval_cost_floor
end
end GaloisForLFunctions.HTGeometry
