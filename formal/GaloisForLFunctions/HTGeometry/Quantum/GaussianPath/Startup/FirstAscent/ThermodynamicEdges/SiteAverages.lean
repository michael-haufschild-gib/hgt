import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.PhysicalBlocks
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.BoundaryAverages

/-! # Energy per site from averages over full Gaussian blocks -/

open Filter Finset MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
noncomputable section

private theorem block_ratio {L : ℕ} (hL : 0 < L) :
    Tendsto (fun n : ℕ => (((n+2)/L : ℕ) : ℝ)/((n+2 : ℕ) : ℝ)) atTop (𝓝 (1/(L : ℝ))) := by
  have hz := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 2)
  have hl : Tendsto (fun n : ℕ => 1/(L : ℝ)-1/((n+2 : ℕ) : ℝ)) atTop (𝓝 (1/(L : ℝ))) := by
    simpa only [sub_zero,Function.comp_apply] using (tendsto_const_nhds (x:=1/(L : ℝ))).sub hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · filter_upwards with n
    have hr : 0 < (L : ℝ) := by exact_mod_cast hL
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    have hd := (Nat.div_eq_iff hL).mp (rfl : (n+2)/L=(n+2)/L)
    have he : n+2 ≤ ((n+2)/L+1)*L := by rw [Nat.succ_mul]; omega
    rw [sub_le_iff_le_add,←add_div,div_le_div_iff₀ hr hN,one_mul]
    exact_mod_cast he
  · filter_upwards with n
    have hr : 0 < (L : ℝ) := by exact_mod_cast hL
    have hN : 0 < ((n+2 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ hN hr,one_mul]
    exact_mod_cast Nat.div_mul_le_self (n+2) L

/-- A block average with limit c contributes c/L per physical site. -/
private theorem per_site {L : ℕ} (hL : 0 < L) {f : ℕ→ℝ} {c : ℝ}
    (hf : Tendsto (fun k : ℕ => f k/k) atTop (𝓝 c)) :
    Tendsto (fun n : ℕ => f ((n+2)/L)/((n+2 : ℕ) : ℝ)) atTop (𝓝 (c/L)) := by
  let q (n : ℕ) := (n+2)/L
  have hq : Tendsto q atTop atTop := (Nat.tendsto_div_const_atTop hL.ne').comp (tendsto_add_atTop_nat 2)
  have ha : Tendsto (fun n : ℕ => f (q n)/(q n : ℝ)*((q n : ℝ)/((n+2 : ℕ) : ℝ))) atTop (𝓝 (c/L)) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,one_mul] using (hf.comp hq).mul (block_ratio hL)
  apply ha.congr'
  filter_upwards [hq.eventually (eventually_ge_atTop 1)] with n hn
  have h : (q n : ℝ) ≠ 0 := by exact_mod_cast (by omega : q n ≠ 0)
  change f (q n)/(q n : ℝ)*((q n : ℝ)/_)=f (q n)/_
  field_simp [h]

/-- The independent full blocks have their deterministic mean contribution per site. -/
theorem gaussian_full_width_average :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : ℕ, Tendsto
      (fun n : ℕ => (∑ j ∈ range ((n+2)/(m+2)), blockWidth m (readBlock m ω j))/((n+2 : ℕ) : ℝ))
      atTop (𝓝 (meanWidth m/((m+2 : ℕ) : ℝ))) := by
  filter_upwards [gaussian_block_width_law] with ω h
  exact fun m => per_site (by omega : 0 < m+2) (h m)

/-- On one frozen chain, each block length determines a deterministic
interval containing the lower and upper limiting physical widths per site. -/
theorem gaussian_block_trap :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ m : ℕ, ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, |physicalWidth ω n/((n+2 : ℕ) : ℝ)-meanWidth m/((m+2 : ℕ) : ℝ)| ≤
        18*meanAbsoluteField/((m+2 : ℕ) : ℝ)+δ := by
  filter_upwards [gaussian_full_width_average,gaussian_seam_average,gaussian_last_block] with ω hw hs hr
  intro m δ hδ
  let L := m+2
  let W (k : ℕ) := ∑ j ∈ range k, blockWidth m (readBlock m ω j)
  let S (k : ℕ) := ∑ j ∈ range k, seamMass m (readRows L ω j)
  let R (k : ℕ) := rowMass L (readRows L ω k)
  let q (n : ℕ) := (n+2)/L
  let N (n : ℕ) : ℝ := (n+2 : ℕ)
  have hL : 0 < L := by dsimp [L]; omega
  have hW : Tendsto (fun n => W (q n)/N n) atTop (𝓝 (meanWidth m/(L : ℝ))) := hw m
  have hS := per_site (f:=S) hL (hs m)
  have hR := per_site (f:=R) hL (hr L)
  have ha := ((hS.add hR).const_mul 2).add ((hW.sub_const (meanWidth m/(L : ℝ))).abs)
  have hlim : 2*(9*meanAbsoluteField/(L : ℝ)+0/L)+|meanWidth m/(L : ℝ)-meanWidth m/L| =
      18*meanAbsoluteField/L := by rw [sub_self,abs_zero,zero_div,add_zero,add_zero]; ring
  rw [hlim] at ha
  filter_upwards [ha.eventually_lt_const (lt_add_of_pos_right _ hδ)] with n hn
  have hN : 0 < N n := by dsimp [N]; positivity
  have hB := div_le_div_of_nonneg_right (block_approximation ω n m) hN.le
  have hd : |physicalWidth ω n/N n-W (q n)/N n| ≤ 2*(S (q n)/N n+R (q n)/N n) := by
    rw [←sub_div,abs_div,abs_of_pos hN]
    exact hB.trans_eq (by dsimp only [W,S,R,q,L,N]; ring)
  calc
    _ ≤ |physicalWidth ω n/N n-W (q n)/N n|+|W (q n)/N n-meanWidth m/(L : ℝ)| := abs_sub_le _ _ _
    _ ≤ _ := (add_le_add hd le_rfl).trans hn.le

#print axioms gaussian_block_trap
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ThermodynamicEdges
