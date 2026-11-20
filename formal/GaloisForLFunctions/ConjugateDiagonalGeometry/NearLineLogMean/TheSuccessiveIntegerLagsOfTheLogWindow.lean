import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.FourEnergyMeasurementsRecoverAdjacentCorrelations

/-!
# Successive integer lags in logarithmic windows

Below (K+1)/M the off-diagonal energy contains only the first K
additive lags. Grouping the Gram terms by integer difference gives
their exact signed contributions, including partially overlapping pairs.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset Filter Topology
noncomputable section

/-- Logarithmic spacing from n to n+r. -/
def logLag (r n : ℕ) := Real.log (n+r:ℕ)-Real.log n

/-- Energy from the single pair n,n+r, with its signed real Gram factor. -/
def lagPair (a : ℕ → ℂ) (d : ℝ) (r n : ℕ) :=
  gram (a (n+r)) (a n)*max (d-logLag r n) 0

/-- Contribution of the r-th lag from all complete pairs in a prefix. -/
def lagSum (a : ℕ → ℂ) (M r : ℕ) (d : ℝ) :=
  ∑ n ∈ Icc 1 (M-r), lagPair a d r n

/-- The lag divided by either endpoint brackets its logarithmic spacing. -/
theorem log_lag_bounds (r : ℕ) {n : ℕ} (hn : 0 < n) :
    (r:ℝ)/((n:ℝ)+r) ≤ logLag r n ∧ logLag r n ≤ (r:ℝ)/n := by
  have hn' : 0<(n:ℝ) := Nat.cast_pos.mpr hn
  have hp : 0<(n:ℝ)+r := add_pos_of_pos_of_nonneg hn' (Nat.cast_nonneg _)
  have ht := div_pos hp hn'
  have hlo := Real.one_sub_inv_le_log_of_pos ht
  have hhi := Real.log_le_sub_one_of_pos ht
  rw [inv_div,Real.log_div hp.ne' hn'.ne'] at hlo
  rw [Real.log_div hp.ne' hn'.ne'] at hhi
  simp only [logLag,Nat.cast_add]
  constructor
  · exact le_trans (le_of_eq (by field_simp [hp.ne']; ring)) hlo
  · exact hhi.trans_eq (by field_simp [hn'.ne']; ring)

private def newLag (a : ℕ → ℂ) (N : ℕ) (d : ℝ) (r : ℕ) :=
  if r ≤ N then lagPair a d r (N+1-r) else 0

private theorem lagSum_succ (a : ℕ → ℂ) (N r : ℕ) (d : ℝ) :
    lagSum a (N+1) r d = lagSum a N r d+newLag a N d r := by
  by_cases hr : r ≤ N
  · simp only [lagSum,newLag,if_pos hr,show N+1-r=N-r+1 by omega]
    rw [sum_Icc_succ_top (by omega)]
  · simp [lagSum,newLag,hr,show N+1-r=0 by omega,show N-r=0 by omega]

private theorem row_by_lag (a : ℕ → ℂ) (N : ℕ) (d : ℝ) :
    (∑ m ∈ Icc 1 N, gram (a (N+1)) (a m)*max (d-gap N m) 0) =
      ∑ r ∈ Icc 1 N, newLag a N d r := by
  have hmem (i : ℕ) (hi : i∈Icc 1 N) : N+1-i∈Icc 1 N := by
    obtain ⟨h,h'⟩ := mem_Icc.mp hi
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hinv (i : ℕ) (hi : i∈Icc 1 N) : N+1-(N+1-i)=i := by
    have := (mem_Icc.mp hi).2
    omega
  apply sum_nbij' (fun i => N+1-i) (fun i => N+1-i) hmem hmem hinv hinv
  intro m hm
  have hk := (mem_Icc.mp (hmem m hm)).2
  have hsum : m+(N+1-m)=N+1 := by have := (mem_Icc.mp hm).2; omega
  rw [newLag,if_pos hk,hinv m hm,lagPair,logLag,hsum,gap]

private theorem truncate_lags (a : ℕ → ℂ) (N K : ℕ) {d : ℝ}
    (hb : d*((N+1:ℕ):ℝ) ≤ (K:ℝ)+1) :
    ∑ r ∈ Icc 1 N, newLag a N d r = ∑ r ∈ Icc 1 K, newLag a N d r := by
  rcases le_total N K with h|h
  · apply sum_subset (Icc_subset_Icc le_rfl h)
    intro r hr hnot
    have hlarge : ¬r≤N := fun hl => hnot (mem_Icc.mpr ⟨(mem_Icc.mp hr).1,hl⟩)
    simp only [newLag,if_neg hlarge]
  · symm
    apply sum_subset (Icc_subset_Icc le_rfl h)
    intro r hr hnot
    obtain ⟨hr₁,hrN⟩ := mem_Icc.mp hr
    have hlarge : K+1≤r := by by_contra! ha; exact hnot (mem_Icc.mpr ⟨hr₁,by omega⟩)
    let n := N+1-r
    have hpos : 0<n := by dsimp only [n]; omega
    have he : (n:ℝ)+r=(N+1:ℕ) := by exact_mod_cast (show n+r=N+1 by dsimp only [n]; omega)
    have hg := (log_lag_bounds r hpos).1
    rw [he] at hg
    have hr' : (K:ℝ)+1 ≤ r := by exact_mod_cast hlarge
    have hd : d ≤ logLag r n := ((le_div_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos _))).mpr
      (hb.trans hr')).trans hg
    rw [newLag,if_pos hrN,lagPair,max_eq_right (sub_nonpos.mpr hd),mul_zero]

/-- At a newly appended endpoint with at least K predecessors all first
K lag pairs are present; no other pair contributes in this band. -/
theorem row_by_initial_lags (a : ℕ → ℂ) {N K : ℕ} (hK : K ≤ N) {d : ℝ} (hd : 0 ≤ d)
    (hb : d*((N+1:ℕ):ℝ) ≤ (K:ℝ)+1) :
    row a N d = ‖a (N+1)‖^2*d + 2*∑ r ∈ Icc 1 K, lagPair a d r (N+1-r) := by
  rw [row_spectrum,max_eq_left hd,row_by_lag,truncate_lags a N K hb]
  congr 2
  exact sum_congr rfl fun r hr => if_pos ((mem_Icc.mp hr).2.trans hK)

/-- Through scaled bandwidth K+1 the entire excess is twice the sum of
the first K signed lag contributions. The band endpoints are included. -/
theorem excess_energy_by_integer_lag (a : ℕ → ℂ) (M K : ℕ) {d : ℝ} (hd : 0 ≤ d)
    (hb : d*(M:ℝ) ≤ (K:ℝ)+1) :
    excessEnergy a M d = 2*∑ r ∈ Icc 1 K, lagSum a M r d := by
  induction M with
  | zero => simp [excessEnergy,energy,lagSum,_root_.RHTower.Sieve.integral_normSq_logWindowSum]
  | succ M ih =>
    have hprev : d*(M:ℝ) ≤ (K:ℝ)+1 :=
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.le_succ M)) hd).trans hb
    have hp := ih hprev
    have hrow := row_spectrum a M d
    rw [max_eq_left hd,row_by_lag,truncate_lags a M K hb] at hrow
    unfold row at hrow
    unfold excessEnergy at hp ⊢
    rw [Finset.sum_range_succ (fun j : ℕ => ‖a (j+1)‖^2) M]
    simp_rw [lagSum_succ]
    rw [sum_add_distrib]
    linarith only [hrow,hp]

end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
