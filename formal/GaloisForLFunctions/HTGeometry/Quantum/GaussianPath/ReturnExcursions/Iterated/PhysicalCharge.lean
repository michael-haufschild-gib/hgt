import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.Occupation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.Timeline
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.TravelTime

/-! # Finite-record bounds for true near-Hilbert crossings and physical elapsed waits -/

open Set Filter MeasureTheory Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated
open PrecisionReturns
noncomputable section

/-- The bound charges the full time before each first crossing and the
terminal part of each ensuing wait to rare windows. It holds for every
finite record length, beginning with the identity. -/
theorem gaussian_cycle_windows :
    ∃ c : ℕ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let D := 2^N
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let G := (2:ℝ)^(D^c)
      ∀ s≤P/2, let v := lowDate H P s
        let σ := highDate H P s
        (∀ i : ℕ, v i<σ i ∧ orbitCircuitDistance H P (σ i)=9/80 ∧
          IsLeast {t | v i≤t ∧ 9/80≤orbitCircuitDistance H P t} (σ i) ∧
          IsLeast {t | σ i≤t ∧ HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val t)} (v (i+1)) ∧
          1<v (i+1)-σ i ∧ v (i+1)-σ i≤G) ∧
        ∀ b e n : ℕ, 16*(b+e)≤7*D →
          (2:ℝ)^e*(∑ i∈range n, ((σ i-v i)+min ((2:ℝ)^b) (v (i+1)-σ i)))≤v n+G := by
  obtain ⟨c,hwin⟩ := gaussian_full_budget_robust_windows
  refine ⟨c,?_⟩
  filter_upwards [hwin,gaussian_robust_travel_time] with ω hw ht
  filter_upwards [hw,ht] with k hk htravel
  intro N D H P G s hs v σ
  have hD : 16*(0+1)≤7*D := by
    have h : 8≤2^N := by dsimp only [N]; calc
      8 = 2^3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hard (v : ℝ) : ∃ t, v≤t ∧ 9/80≤orbitCircuitDistance H P t := by
    have h := reaches_after H P (G:=G) (by dsimp only [G]; positivity)
      (fun a T hT => by simpa only [pow_zero,pow_one] using hk.2 0 1 hD a T hT) v
    obtain ⟨t,ht,hh⟩ := h
    exact ⟨t,ht.1,hh⟩
  have hsP : s≤P := hs.trans (Nat.div_le_self ..)
  have high (i : ℕ) := high_first H P s hsP hard i
  have low (i : ℕ) := firstVisit_isLeast H (σ i) s (by norm_num : (0:ℝ)<1/10)
  have hσ (i : ℕ) : σ i≤v (i+1) := (low i).1.1
  have mono : Monotone v := monotone_nat_of_le_succ fun i => (high i).1.le.trans (hσ i)
  constructor
  · intro i
    have hgap := htravel (σ i) (v (i+1)) (high i).2.1.ge s hs (low_visit H P s (i+1))
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (hσ i))] at hgap
    obtain ⟨t,ht,z,hz,C,hC,hfit⟩ := hk.1 (σ i)
    have hend := (low i).2 (show σ i≤t ∧ HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val t) from
      ⟨ht.1,z,hz,C,hC.trans (Nat.zero_le _),hfit⟩)
    refine ⟨(high i).1,(high i).2.1,(high i).2.2.1,low i,(one_le_pow₀ (by norm_num) : 1≤(2:ℝ)^_).trans_lt hgap,?_⟩
    exact sub_le_iff_le_add.mpr ((show v (i+1)≤t from hend).trans (ht.2.trans_eq (add_comm ..)))
  · intro b e n hbe
    let W := (2:ℝ)^b
    let A := robustWindowHits H P W
    have hpre (i : ℕ) : Ico (v i) (σ i)⊆A := by
      intro t h
      exact ⟨t,⟨le_rfl,le_add_of_nonneg_right (by dsimp only [W]; positivity)⟩,
        ((high i).2.2.2 t h).le.trans (by norm_num)⟩
    have he (i : ℕ) : Ico (max (σ i) (v (i+1)-W)) (v (i+1)) ⊆ A := by
      intro t hh
      have hlo := (le_max_right ..).trans hh.1
      exact ⟨v (i+1),⟨hh.2.le,by linarith only [hlo]⟩,
        (low_at_larger_budget H P s (i+1) hsP).trans (by norm_num)⟩
    have h := charge_windows v σ (W:=W) (by dsimp only [W]; positivity)
      (fun i => (high i).1.le) hσ A hpre he n
    have hzero : v 0=0 := rfl
    rw [hzero] at h
    have hbound := hk.2 b e hbe 0 (v n) (hzero ▸ mono (Nat.zero_le n))
    rw [zero_add] at hbound
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans hbound

#print axioms gaussian_cycle_windows
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.Iterated

