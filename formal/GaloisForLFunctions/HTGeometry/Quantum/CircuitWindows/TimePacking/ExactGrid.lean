import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.IntervalCount

/-! # The exact packing count before the first low-distance recurrence -/
open Set
namespace GaloisForLFunctions.HTGeometry.TimePacking
noncomputable section

/-- Possible numbers of samples in one time interval when pairwise
distinguishability is tested by a distance depending on the time lag. -/
def sampleCounts (d : ℝ → ℝ) (e a T : ℝ) : Set ℕ :=
  {M | ∃ t : Fin M → ℝ, (∀ i, t i∈Icc a (a+T)) ∧
    ∀ i j, i≠j → e≤d |t i-t j|}

/-- If distinguishability in this window is exactly a minimum lag,
the floor bound is attained. Equality at the threshold admits the
last grid point when the span is an integer multiple of the lag. -/
theorem exact_grid_count (d : ℝ → ℝ) (e a T δ : ℝ) (hT : 0≤T) (hδ : 0<δ)
    (h : ∀ v ∈ Icc (0:ℝ) T, e≤d v ↔ δ≤v) :
    IsGreatest (sampleCounts d e a T) (⌊T/δ⌋₊+1) := by
  have span {u v : ℝ} (hu : u∈Icc a (a+T)) (hv : v∈Icc a (a+T)) : |u-v|∈Icc 0 T :=
    ⟨abs_nonneg _,abs_le.mpr ⟨by linarith only [hu.1,hv.2],by linarith only [hu.2,hv.1]⟩⟩
  let t (i : Fin (⌊T/δ⌋₊+1)) := a+(i.val:ℝ)*δ
  have ht (i) : t i∈Icc a (a+T) := by
    have hi : (i.val:ℝ)≤T/δ := (Nat.cast_le.mpr (Nat.le_of_lt_succ i.isLt)).trans
      (Nat.floor_le (div_nonneg hT hδ.le))
    exact ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ.le),
      add_le_add (le_refl a) ((le_div_iff₀ hδ).mp hi)⟩
  have apart (i j : Fin (⌊T/δ⌋₊+1)) (hij : i<j) : δ≤t j-t i := by
    have hn : i.val+1≤j.val := hij
    have hr : (i.val:ℝ)+1≤(j.val:ℝ) := by exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_right hr hδ.le
    dsimp only [t]; linarith only [hm]
  constructor
  · refine ⟨t,ht,fun i j hij => (h _ (span (ht i) (ht j))).mpr ?_⟩
    rcases lt_or_gt_of_ne hij with h' | h'
    · rw [abs_sub_comm]; exact (apart i j h').trans (le_abs_self _)
    · exact (apart j i h').trans (le_abs_self _)
  · rintro M ⟨v,hv,hsep⟩
    have hc := separated_interval_count v a T δ hT hδ hv
      (fun i j hij => (h _ (span (hv i) (hv j))).mp (hsep i j hij))
    rw [Fintype.card_fin] at hc
    cases M with
    | zero => exact Nat.zero_le _
    | succ M =>
      rw [Nat.cast_succ,add_mul,one_mul] at hc
      exact Nat.succ_le_succ (Nat.le_floor ((le_div_iff₀ hδ).mpr (by linarith only [hc])))

#print axioms exact_grid_count
end
end GaloisForLFunctions.HTGeometry.TimePacking
