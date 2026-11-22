import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.AllDelays
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.SummableIsolation

/-! # Almost-sure exclusion of returns at prescribed delays on one chain -/
open MeasureTheory Filter Topology Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section

private def gridSize (N : ℕ) := ⌈(N:ℝ)^(1+(96:ℝ)⁻¹)⌉₊

private theorem inverse_grid_summable : Summable (fun k : ℕ => (gridSize (k+3):ℝ)⁻¹) := by
  let p : ℝ := 1+(96:ℝ)⁻¹
  have hs := Real.summable_nat_rpow_inv.mpr (by norm_num [p] : 1 < p)
  apply ((summable_nat_add_iff 3).mpr hs).of_norm_bounded_eventually_nat
  filter_upwards with k
  have h : 0 < ((k+3:ℕ):ℝ)^p := Real.rpow_pos_of_pos (by positivity) p
  have hu : ((k+3:ℕ):ℝ)^p ≤ (gridSize (k+3):ℝ) := Nat.le_ceil _
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (h.trans_le hu).le)]
  exact (inv_le_inv₀ (h.trans_le hu) h).mpr hu

private theorem inverse_grid_scales {A : ℝ} (hA : 0 < A) :
    ∀ᶠ k : ℕ in atTop, let N := k+3
                         let w := ((N:ℝ))⁻¹
                         let g := (2*A+6)*w
                         let m := gridSize N
                         0 < m ∧ 0 ≤ g ∧ A/(N:ℝ) ≤ g/2-2*w ∧
                           16*((m:ℝ)*g) ≤ N ∧ (m:ℝ)*g+2*w ≤ (N:ℝ)^((48:ℝ)⁻¹)/4 := by
  let q := 2*A+6
  have hq : 1 ≤ q := by dsimp [q]; linarith only [hA]
  have hn : Tendsto (fun k : ℕ => ((k+3:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hu := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<(96:ℝ)⁻¹)).comp hn
  filter_upwards [hu.eventually_ge_atTop (32*q+8)] with k hk
  intro N w g m
  let u := (N:ℝ)^((96:ℝ)⁻¹)
  change 32*q+8 ≤ u at hk
  have hN : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hpos := zero_lt_one.trans_le hN
  have hw : 0 < w := inv_pos.mpr hpos
  have hw1 : w ≤ 1 := (inv_le_one₀ hpos).mpr hN
  have hu1 : 1 ≤ u := by linarith only [hk,hq]
  have hu0 := zero_le_one.trans hu1
  have he : (N:ℝ)^(1+(96:ℝ)⁻¹)=(N:ℝ)*u := by rw [Real.rpow_add hpos,Real.rpow_one]
  have hm : (m:ℝ) ≤ (N:ℝ)*u+1 := by
    change ((⌈(N:ℝ)^(1+(96:ℝ)⁻¹)⌉₊:ℕ):ℝ) ≤ _
    rw [he]
    exact (Nat.ceil_lt_add_one (mul_nonneg hpos.le hu0)).le
  have hg : 0 ≤ g := mul_nonneg (zero_le_one.trans hq) hw.le
  have hnw : (N:ℝ)*w=1 := mul_inv_cancel₀ hpos.ne'
  have hspan : (m:ℝ)*g ≤ 2*q*u := calc
    _ ≤ ((N:ℝ)*u+1)*g := mul_le_mul_of_nonneg_right hm hg
    _ = q*u+q*w := by change _*(q*w)=_; linear_combination q*u*hnw
    _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left (hw1.trans hu1) (zero_le_one.trans hq)]
  have hsq : u^2=(N:ℝ)^((48:ℝ)⁻¹) := by
    dsimp only [u]
    rw [←Real.rpow_mul_natCast hpos.le]
    norm_num
  have hsqN : u^2 ≤ N := by
    rw [hsq]
    exact (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (48:ℝ)⁻¹ ≤ 1)).trans_eq (Real.rpow_one _)
  have hmul := mul_le_mul_of_nonneg_right hk hu0
  refine ⟨Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hpos _),hg,?_,?_,?_⟩
  · change A/(N:ℝ) ≤ (2*A+6)*w/2-2*w
    rw [div_eq_mul_inv]
    change A*w ≤ _
    linarith only [hw]
  · nlinarith only [hmul,hsqN,hspan,hu0]
  · rw [←hsq]
    nlinarith only [hmul,hspan,hw1,hu1,mul_nonneg (zero_le_one.trans hq) hu0]

/-- For any delay schedule specified before the Gaussian draw, almost
every chain eventually has no visit with ⌊c√N⌋ gates in the interval
of length 1/N at that delay after its own initial near-Hilbert crossing. -/
theorem gaussian_pathwise_prescribed_delay :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ → ℝ, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      prefixPoint k ω ∉ hitWindow (k+1) (nearHilbertContinuousCircuitBudget N)
        ⌊c*sqrt N⌋₊ (max (d k) 0) (N:ℝ)⁻¹ := by
  obtain ⟨A,c,hA,hc,hgap⟩ := gaussian_distance_gap
  refine ⟨c,hc,fun d => ?_⟩
  let N (k : ℕ) := k+3
  let m (k : ℕ) := gridSize (N k)
  let w (k : ℕ) := (N k:ℝ)⁻¹
  let g (k : ℕ) := (2*A+6)*w k
  let L (k : ℕ) := max (max (d k) 0) ((N k:ℝ)^2)
  let E (k : ℕ) := hitWindow (k+1) (nearHilbertContinuousCircuitBudget (N k)) ⌊c*sqrt (N k)⌋₊ (L k) (w k)
  let a (k : ℕ) := factor (m:=m k) (g k) (L k)
  have hN (k : ℕ) : 1 ≤ (N k:ℝ) := by exact_mod_cast (show 1 ≤ N k by dsimp [N]; omega)
  have hs : ∀ᶠ k : ℕ in atTop, 0 < m k ∧ 0 ≤ g k ∧ A/(N k:ℝ) ≤ g k/2-2*w k ∧
      16*((m k:ℝ)*g k) ≤ N k ∧ (m k:ℝ)*g k+2*w k ≤ (N k:ℝ)^((48:ℝ)⁻¹)/4 := inverse_grid_scales hA
  have hp : ∀ᶠ k : ℕ in atTop, 0 < m k ∧ ∀ i, 1 ≤ a k i ∧
      (Fintype.card (PrefixIndex (k+1)):ℝ)*(a k i-1) ≤ 1 := by
    filter_upwards [hs] with k hk
    exact ⟨hk.1,(grid_price (k:=k) hk.2.1 (le_max_right ..) hk.2.2.2.1).2⟩
  have hmiss := eventually_no_isolated E (fun _ => measurable_hitWindow ..) m a inverse_grid_summable hp
  filter_upwards [hmiss,hgap,gaussian_initial_window_gap hc] with ω hm hg hi
  filter_upwards [hm,hg,hi,hs] with k hmiss hgap hstart hk
  have hn := hN k
  have hn0 := zero_lt_one.trans_le hn
  let l := max (d k) 0
  change prefixPoint k ω ∉ hitWindow (k+1) (nearHilbertContinuousCircuitBudget (N k)) ⌊c*sqrt (N k)⌋₊ l (w k)
  by_cases hlarge : (N k:ℝ)^2 ≤ l
  · intro hx
    have hE : prefixPoint k ω∈E k := by
      change prefixPoint k ω ∈ hitWindow (k+1) (nearHilbertContinuousCircuitBudget (N k)) ⌊c*sqrt (N k)⌋₊ (max l ((N k:ℝ)^2)) (w k)
      rwa [max_eq_left hlarge]
    apply hmiss
    have hL : 0 < L k := (sq_pos_of_pos hn0).trans_le (le_max_right ..)
    have hspan := (grid_price (k:=k) hk.2.1 (le_max_right l _) hk.2.2.2.1).1
    apply isolated_of_gap hk.2.1 hL hspan (inv_nonneg.mpr hn0.le) _ hE
    intro t v ht hv hl hh
    exact hgap t v ht hv (hk.2.2.1.trans hl) (hh.trans hk.2.2.2.2)
  · exact hstart l (w k) (le_max_right ..)
      (add_le_add (le_of_not_ge hlarge) (((inv_le_one₀ hn0).mpr hn).trans hn))

#print axioms gaussian_pathwise_prescribed_delay
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
