import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.RecordCount
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The mean time per record is the reciprocal of the true entry rate -/
open Set Filter Topology
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
noncomputable section

private theorem cancel_rate {v k d : ℝ} (hv : v≠0) (hk : k≠0) (hd : d≠0) :
    (v/k)/(v/d) = d/k := by field_simp

/-- Inverting the exact entry count at successive records includes the
entire elapsed time from the observation origin, including its first wait. -/
theorem record_mean (E : Set ℝ) (a : ℝ) (F : ℝ → Finset ℝ) (t : ℕ → ℝ)
    (hor : t 0 = a) (hrec : ∀ j, IsLeast {v | t j+1 ≤ v ∧ v ∈ E} (t (j+1)))
    (hunit : ∀ v ∈ E, v+1 ∉ E) (hgap : ∀ v ∈ E, ∀ w, Entry E w → v<w → 1<w-v)
    (hF : ∀ u T, u ∈ F T ↔ a<u ∧ u≤T ∧ Entry E u) {rate : ℝ} (hpos : 0<rate)
    (hflux : Tendsto (fun T => ((F T).card : ℝ)/(T-a)) atTop (𝓝 rate)) :
    Tendsto (fun j : ℕ => (t j-a)/j) atTop (𝓝 (1/rate)) := by
  let c : ℝ := (F (t 1)).card
  have hbound (j : ℕ) : a+(j:ℝ) ≤ t j := by
    induction j with
    | zero => simp only [hor,Nat.cast_zero,add_zero,le_refl]
    | succ j ih =>
      rw [Nat.cast_succ]
      linarith only [ih,(hrec j).1.1]
  have ht := tendsto_atTop_mono hbound (tendsto_atTop_add_const_left atTop a tendsto_natCast_atTop_atTop)
  have hclock := hflux.comp (ht.comp (tendsto_add_atTop_nat 1))
  have hs : Tendsto (fun j : ℕ => ((j+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim := (hs.const_div_atTop (c-1)).const_add 1
  have hc (j : ℕ) : ((F (t (j+1))).card:ℝ) = c+j := by
    rw [record_count E a F t hor hrec hunit hgap hF j,Nat.cast_add]
  have ha : Tendsto (fun j : ℕ => ((F (t (j+1))).card:ℝ)/(j+1:ℕ)) atTop (𝓝 1) := by
    rw [add_zero] at hlim
    refine hlim.congr' (Eventually.of_forall fun j => ?_)
    change 1+(c-1)/((j+1:ℕ):ℝ) = ((F (t (j+1))).card:ℝ)/((j+1:ℕ):ℝ)
    rw [hc,Nat.cast_succ]
    have hne : (j:ℝ)+1≠0 := (by positivity : 0<(j:ℝ)+1).ne'
    apply (eq_div_iff hne).mpr
    rw [add_mul,one_mul,div_mul_cancel₀ _ hne]
    ring
  apply (tendsto_add_atTop_iff_nat 1).mp
  refine (ha.div hclock hpos.ne').congr' ?_
  filter_upwards [eventually_ge_atTop 1] with j hj
  have hc' : 0 < ((F (t (j+1))).card:ℝ) := by
    rw [hc]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (Nat.cast_pos.mpr (by omega))
  have hden : 0<t (j+1)-a := by
    have hh := hbound (j+1)
    rw [Nat.cast_succ] at hh
    linarith only [hh,Nat.cast_nonneg (α:=ℝ) j]
  change (((F (t (j+1))).card:ℝ)/(j+1:ℕ))/(((F (t (j+1))).card:ℝ)/(t (j+1)-a)) = _
  exact cancel_rate hc'.ne' (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)) hden.ne'

end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.PhysicalComponents
