import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldDensity
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitInversion

/-! # Persistent circuit hardness throughout a fixed physical time horizon -/
open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Select enough untouched isolated fields to accumulate a phase of at least
π/2. Rounding the number of sites costs at most a single local phase qt. -/
private theorem persistent_floor_of_sites {n : ℕ} (u : PathShell n) (q p : ℝ) (hq : 0 < q) (hp : 0 < p)
    (S : Finset (Fin (n+2))) (hS : p*((n+2:ℕ):ℝ) ≤ S.card)
    (hiso : ∀ s ∈ S, isolatedLongitudinalSite u q (q/200) s)
    (hsize : 8 ≤ p*((n+2:ℕ):ℝ)) (t : ℝ) (ht : 0 < t)
    (hstart : 4*Real.pi/(q*p) ≤ ((n+2:ℕ):ℝ)*t) (hend : q*t ≤ 1/8)
    (C : TwoQubitCircuit (n+2)) (z : ℂ)
    (herr : ‖unitaryEvolution (pathHamiltonian u) t-z • (C.eval : Reg (n+2))‖ ≤ 1/4) :
    (p/8)*((n+2:ℕ):ℝ) ≤ C.gateCount := by
  classical
  by_contra! hcheap
  let N : ℝ := (n+2:ℕ)
  let b := Real.pi/(2*q*t)
  let m := ⌈b⌉₊
  have hb : 0 < b := div_pos Real.pi_pos (by positivity)
  have hmc : b ≤ (m:ℝ) := Nat.le_ceil b
  have hround : (m:ℝ) < b+1 := Nat.ceil_lt_add_one hb.le
  have hmpos : 0 < m := Nat.ceil_pos.mpr hb
  have hNe : b ≤ p*N/8 := by
    apply (div_le_iff₀ (show 0 < 2*q*t by positivity)).mpr
    have ha := (div_le_iff₀ (mul_pos hq hp)).mp hstart
    change 4*Real.pi ≤ N*t*(q*p) at ha
    linarith only [ha]
  let F := S \ C.touchedSites
  have htouch : (C.touchedSites.card:ℝ) ≤ 2*(C.gateCount:ℝ) := by exact_mod_cast C.card_touchedSites_le
  have hcover : S.card ≤ F.card+C.touchedSites.card := by
    apply (Finset.card_le_card (show S ⊆ F ∪ C.touchedSites from fun s hs => by
      by_cases h : s ∈ C.touchedSites
      · exact Finset.mem_union_right _ h
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs,h⟩))).trans
    exact Finset.card_union_le _ _
  have hc : (S.card:ℝ) ≤ (F.card:ℝ)+C.touchedSites.card := by exact_mod_cast hcover
  have hmF : m ≤ F.card := by
    have h : (m:ℝ) ≤ F.card := by
      change p*N ≤ S.card at hS
      change 8 ≤ p*N at hsize
      change (C.gateCount:ℝ) < p/8*N at hcheap
      linarith only [hround,hNe,hsize,hS,htouch,hc,hcheap]
    exact_mod_cast h
  obtain ⟨K,hKF,hK⟩ := Finset.exists_subset_card_eq hmF
  have hD : Disjoint K C.touchedSites := Finset.disjoint_left.mpr
    (fun s hs h => (Finset.mem_sdiff.mp (hKF hs)).2 h)
  have hg := isolated_field_circuit_deficit u q (q/200) hq (by positivity) C z K
    (by rwa [hK]) hD (fun s hs => hiso s (Finset.mem_sdiff.mp (hKF hs)).1) t
  rw [hK,abs_of_pos ht] at hg
  have hid : b*(2*q*t) = Real.pi := div_mul_cancel₀ _ (by positivity)
  have hlo := mul_le_mul_of_nonneg_right hmc (show 0 ≤ 2*q*t by positivity)
  have hhi := mul_lt_mul_of_pos_right hround (show 0 < 2*q*t by positivity)
  have hphase : 0 ≤ t*((m:ℝ)*q)-Real.pi/2 := by linarith only [hlo,hid]
  rw [abs_of_nonneg hphase] at hg
  linarith only [hg,herr,hhi,hid,hend,Real.pi_lt_four]

/-- For any fixed T>0, almost every chain eventually has an extensive gate
floor at every lag in [A/N,T]. At each such lag, circuits at any two time
origins separated by that lag must pay the same extensive total cost. -/
theorem gaussian_pauli_persistent_circuit_floor (T : ℝ) (hT : 0 < T) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ t : ℝ, A/(N:ℝ) ≤ t → t ≤ T →
        (∀ (C : TwoQubitCircuit N) (z : ℂ), ‖unitaryEvolution H t-z • (C.eval : Reg N)‖ ≤ 1/4 →
          c*(N:ℝ) ≤ C.gateCount) ∧
        ∀ v : ℝ, ∀ s r : ℕ, HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H v) →
          HasProjectiveCircuitApproximation N (1/10:ℝ) r (unitaryEvolution H (v+t)) →
          c*(N:ℝ) ≤ (s:ℝ)+r := by
  let q := 1/(8*T)
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨p,hp,hblocks⟩ := gaussian_path_eventual_isolated_sites q (q/200) (by positivity)
  let A := 4*Real.pi/(q*p)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A,p/8,hA,by positivity,?_⟩
  filter_upwards [hblocks] with ω hω
  obtain ⟨k,hk⟩ := exists_nat_gt (8/p)
  filter_upwards [hω,eventually_ge_atTop k] with n hS hlarge
  obtain ⟨S,hS,his⟩ := hS
  let N := n+2
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian _⟩
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hsize : 8 ≤ p*(N:ℝ) := by
    have h' : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast (show k ≤ N by dsimp [N]; omega)
    have h8 : 8 < (k:ℝ)*p := (div_lt_iff₀ hp).mp hk
    linarith only [h8,mul_le_mul_of_nonneg_right h' hp.le]
  intro t hlo hhi
  have ht : 0 < t := (div_pos hA hN).trans_le hlo
  have hstart : A ≤ (N:ℝ)*t := by simpa only [mul_comm t] using (div_le_iff₀ hN).mp hlo
  have hend : q*t ≤ 1/8 := by
    apply (mul_le_mul_of_nonneg_left hhi hq.le).trans_eq
    dsimp [q]; field_simp [hT.ne']
  have hf := persistent_floor_of_sites u q p hq hp S hS his hsize t ht hstart hend
  refine ⟨hf,?_⟩
  intro v s r hv he
  by_contra! hsmall
  have hh : ProjectiveCircuitSeparated N (1/4:ℝ) (r+s) (unitaryEvolution H.val t) := by
    intro z _ C hC
    by_contra! happrox
    have hc : (C.gateCount:ℝ) ≤ (r:ℝ)+s := by exact_mod_cast hC
    linarith only [hf C z happrox,hc,hsmall]
  have hx := projectiveCircuitSeparated_unitaryEvolution_backward_cone H
    (by omega : s ≤ r+s) hh (hv.neg_time H) (by norm_num : (1/10:ℝ)+1/10 ≤ 1/4)
  rw [show t-(-v) = v+t by ring,Nat.add_sub_cancel] at hx
  obtain ⟨z,hz,C,hC,heC⟩ := he
  exact (not_lt_of_ge heC) (hx z hz C hC)

/-- For every sublinear gate budget, two affordable times more than A/N
apart must eventually be farther apart than any fixed macroscopic duration.
One deterministic A works for every duration and every budget sequence. -/
theorem gaussian_pauli_sublinear_dip_spacing :
    ∃ A : ℝ, 0 < A ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ s : ℕ → ℕ,
      Tendsto (fun n => (s n:ℝ)/((n+2:ℕ):ℝ)) atTop (nhds 0) →
      ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
        let N := n+2
        let H := pathHamiltonian (pathPauliDisorderShell ω n)
        ∀ t : ℝ, A/(N:ℝ) ≤ t → ∀ v : ℝ,
          HasProjectiveCircuitApproximation N (1/10:ℝ) (s n) (unitaryEvolution H v) →
          HasProjectiveCircuitApproximation N (1/10:ℝ) (s n) (unitaryEvolution H (v+t)) → T < t := by
  have hall (k : ℕ) := gaussian_pauli_persistent_circuit_floor ((k:ℝ)+1) (by positivity)
  choose A c hA hc hw using hall
  refine ⟨A 0,hA 0,?_⟩
  filter_upwards [ae_all_iff.mpr hw] with ω hω
  intro s hsub T
  obtain ⟨k,hk⟩ := exists_nat_gt T
  obtain ⟨m,hm⟩ := exists_nat_gt (A k)
  have hsmall i := hsub.eventually_lt_const (show 0 < c i/2 by positivity)
  filter_upwards [hω 0,hω k,hsmall 0,hsmall k,eventually_ge_atTop m]
    with n hzero hwide hsmall0 hsmallk hlarge
  let N := n+2
  have hN : 0 < (N:ℝ) := by dsimp [N]; positivity
  have hcost (i : ℕ) (hs : (s n:ℝ)/(N:ℝ) < c i/2) :
      (s n:ℝ)+(s n:ℝ) < c i*(N:ℝ) := by
    linarith only [(div_lt_iff₀ hN).mp hs]
  have hone : A k/(N:ℝ) ≤ 1 := by
    apply (div_le_iff₀ hN).mpr
    rw [one_mul]
    exact hm.le.trans (by exact_mod_cast (show m ≤ N by dsimp [N]; omega))
  intro t ht v hv he
  by_contra! hT
  by_cases htone : t ≤ 1
  · have h := (hzero t ht (by simpa using htone)).2 v (s n) (s n) hv he
    exact (not_lt_of_ge h) (hcost 0 hsmall0)
  · have h := (hwide t (hone.trans (le_of_not_ge htone))
      (by linarith only [hT,hk])).2 v (s n) (s n) hv he
    exact (not_lt_of_ge h) (hcost k hsmallk)

#print axioms gaussian_pauli_persistent_circuit_floor
#print axioms gaussian_pauli_sublinear_dip_spacing
end
end GaloisForLFunctions.HTGeometry
