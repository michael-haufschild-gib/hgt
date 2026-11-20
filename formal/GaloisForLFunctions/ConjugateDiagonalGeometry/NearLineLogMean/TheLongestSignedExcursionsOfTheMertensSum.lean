import GaloisForLFunctions.RHTower.MobiusIntegerCuspConfinement
import GaloisForLFunctions.RHTower.MobiusHilbertExponentLaw

/-!
# Depth and duration of a signed Mertens excursion

A real prefix path with steps of size at most one can lose at most one
unit of height per index. A peak of magnitude 2L therefore forces L+1
consecutive readings of its sign, all of magnitude at least L. A path
of unit positive steps attains this universal factor two.
-/
noncomputable section
open Finset
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
open _root_.RHTower

/-- A signed interval ending at k on which every reading has the same
sign and magnitude at least its horizontal length L. -/
def signedRun (u : ℕ → ℝ) (L k : ℕ) : Prop :=
  L≤k ∧ ((∀ j ∈ Icc (k-L) k, (L:ℝ)≤u j) ∨
    (∀ j ∈ Icc (k-L) k, u j≤-(L:ℝ)))

/-- Greatest depth simultaneously sustained for that many steps up
to cutoff N, with zero as the default. -/
def signedRunDepth (u : ℕ → ℝ) (N : ℕ) : ℕ := by
  classical
  exact ((range (N+1)).filter fun L => ∃ k≤N, signedRun u L k).sup id

private theorem bounded_increments {u : ℕ → ℝ} (h : ∀ j, |u (j+1)-u j|≤1)
    {k j : ℕ} (hjk : j≤k) : |u k-u j|≤(k:ℝ)-j := by
  induction k, hjk using Nat.le_induction with
  | base => simp
  | succ n hjn ih =>
    have hh := abs_add_le (u (n+1)-u n) (u n-u j)
    rw [sub_add_sub_cancel] at hh
    rw [Nat.cast_succ]
    linarith only [hh,h n,ih]

/-- Every high absolute reading forces a whole one-sided excursion. -/
theorem signed_run_of_peak {u : ℕ → ℝ} (h0 : u 0=0) (h : ∀ j, |u (j+1)-u j|≤1)
    {k L : ℕ} (hp : 2*(L:ℝ)≤|u k|) : signedRun u L k := by
  have hnorm := bounded_increments h (Nat.zero_le k)
  simp only [h0,sub_zero,Nat.cast_zero] at hnorm
  have hL : L≤k := Nat.cast_le.mp (show (L:ℝ)≤k by linarith only [hp,hnorm,Nat.cast_nonneg (α:=ℝ) L])
  have hjj {j : ℕ} (hj : j∈Icc (k-L) k) : |u k-u j|≤L := by
    have hh := bounded_increments h (mem_Icc.mp hj).2
    have hkj : k≤j+L := by have := (mem_Icc.mp hj).1; omega
    have hc : (k:ℝ)≤j+L := by exact_mod_cast hkj
    linarith only [hh,hc]
  refine ⟨hL,?_⟩
  rcases le_total 0 (u k) with hk|hk
  · rw [abs_of_nonneg hk] at hp
    exact Or.inl fun j hj => by linarith only [hp,(abs_le.mp (hjj hj)).2]
  · rw [abs_of_nonpos hk] at hp
    exact Or.inr fun j hj => by linarith only [hp,(abs_le.mp (hjj hj)).1]

/-- Every anchored unit-step path has a signed run at least half as
deep as any reading, up to rounding. -/
theorem half_peak_le_signed_depth {u : ℕ → ℝ} (h0 : u 0=0) (h : ∀ j, |u (j+1)-u j|≤1)
    {k N : ℕ} (hk : k≤N) : ⌊|u k|/2⌋₊ ≤ signedRunDepth u N := by
  classical
  let L := ⌊|u k|/2⌋₊
  have hL := Nat.floor_le (show 0≤|u k|/2 by positivity)
  have hr := signed_run_of_peak h0 h (L:=L) (k:=k) (by dsimp only [L]; linarith only [hL])
  unfold signedRunDepth
  apply Finset.le_sup (f:=id)
  exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (hr.1.trans hk)),k,hk,hr⟩

/-- The depth never exceeds an upper envelope for the prefix magnitudes. -/
theorem signed_depth_le_envelope (u : ℕ → ℝ) (N : ℕ) {B : ℝ} (hB : 0≤B)
    (h : ∀ k≤N, |u k|≤B) : (signedRunDepth u N:ℝ)≤B := by
  classical
  have hle : signedRunDepth u N ≤ ⌊B⌋₊ := by
    unfold signedRunDepth
    apply Finset.sup_le
    intro L hL
    obtain ⟨k,hk,_,hs⟩ := (mem_filter.mp hL).2
    have hin : k∈Icc (k-L) k := mem_Icc.mpr ⟨Nat.sub_le ..,le_rfl⟩
    apply Nat.le_floor
    change (L : ℝ) ≤ B
    rcases hs with hp|hn
    · exact ((hp k hin).trans (le_abs_self _)).trans (h k hk)
    · have hh := hn k hin
      linarith only [hh,neg_abs_le (u k),h k hk]
  exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hB)

/-- The factor two is attained at every cutoff by the unit ramp. -/
theorem unit_ramp_signed_depth (N : ℕ) : signedRunDepth (fun k : ℕ => (k:ℝ)) N = N/2 := by
  classical
  apply le_antisymm
  · unfold signedRunDepth
    apply Finset.sup_le
    intro L hL
    obtain ⟨k,hk,hl,hs⟩ := (mem_filter.mp hL).2
    have hin : k-L∈Icc (k-L) k := mem_Icc.mpr ⟨le_rfl,Nat.sub_le ..⟩
    rcases hs with hp|hn
    · have hh : L ≤ k - L :=
        Nat.cast_le.mp (show (L : ℝ) ≤ ((k - L : ℕ) : ℝ) from hp _ hin)
      change L≤N/2
      omega
    · have hh := hn _ hin
      change ((k - L : ℕ) : ℝ) ≤ -(L : ℝ) at hh
      have hz : (L:ℝ)=0 := by linarith only [hh,Nat.cast_nonneg (α:=ℝ) (k-L),Nat.cast_nonneg (α:=ℝ) L]
      have hzero : L=0 := by exact_mod_cast hz
      simp only [id_eq,hzero,Nat.zero_le]
  · have hr : signedRun (fun k : ℕ => (k:ℝ)) (N/2) N :=
      ⟨Nat.div_le_self ..,Or.inl fun j hj => Nat.cast_le.mpr (by have := (mem_Icc.mp hj).1; omega)⟩
    unfold signedRunDepth
    apply Finset.le_sup (f:=id)
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hr.1),N,le_rfl,hr⟩

/-- Actual Mertens peaks force intervals of same-sign Mertens prefixes,
with the exact universal factor two and all cutoffs allowed. -/
theorem mertens_half_peak_le_signed_depth {k N : ℕ} (hk : k≤N) :
    ⌊‖mobiusMertensPartialSum k‖/2⌋₊ ≤ signedRunDepth shiftedMertensReal N := by
  rw [norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal]
  apply half_peak_le_signed_depth (by simp [shiftedMertensReal]) _ hk
  intro j
  rw [shiftedMertensReal,Finset.sum_range_succ,←shiftedMertensReal,add_sub_cancel_left]
  exact abs_shiftedMobiusRealCoefficient_le_one j

#print axioms unit_ramp_signed_depth
#print axioms mertens_half_peak_le_signed_depth
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
