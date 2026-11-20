import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldApproximation

/-! # Circuit cost from the number of isolated fields -/
open MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Select enough untouched isolated fields to accumulate a phase of at least
π/2. Rounding the number of sites costs at most a single local phase qt. -/
theorem isolated_sites_uniform_circuit_floor {n : ℕ} (u : PathShell n) (q p : ℝ) (hq : 0 < q) (hp : 0 < p)
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

end
end GaloisForLFunctions.HTGeometry
