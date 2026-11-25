import GaloisForLFunctions.HTGeometry.ThreeFiveOrbitKorobovBound
import Mathlib.Data.Nat.Count

/-! # Densities from arithmetic-progression visit counts -/

open Filter Topology Finset
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
noncomputable section
open scoped Classical

private theorem count_sum (p : ℕ → Prop) (N : ℕ) :
    Nat.count p N=∑ j ∈ range N, if p j then 1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.count_succ,sum_range_succ,ih]

/-- Counts on complete blocks are the sum of the counts on each
residue class. The final incomplete block contributes at most L ticks. -/
theorem density_of_residue_densities (p : ℕ → Prop) {L : ℕ} (hL : 0<L) (v : ℕ → ℝ)
    (h : ∀ b<L, Tendsto (fun n : ℕ => (Nat.count (fun j => p (L*j+b)) n:ℝ)/n)
      atTop (𝓝 (v b))) :
    Tendsto (fun n : ℕ => (Nat.count p n:ℝ)/n) atTop (𝓝 ((∑ b ∈ range L, v b)/L)) := by
  have hblock (n : ℕ) : Nat.count p (L*n)=∑ b ∈ range L, Nat.count (fun j => p (L*j+b)) n := by
    rw [count_sum,ThreeFiveOrbit.sum_range_mul_eq_sum_sum]
    exact sum_congr rfl fun b _ => by simp only [count_sum,Nat.add_comm b]
  let q (n : ℕ) := n/L
  let r (n : ℕ) := n%L
  have hq : Tendsto q atTop atTop := tendsto_atTop.mpr fun m =>
    (eventually_ge_atTop (m*L)).mono fun _ hn => (Nat.le_div_iff_mul_le hL).mpr hn
  have heq (n : ℕ) : L*q n+r n=n := Nat.div_add_mod n L
  have hr (n : ℕ) : r n≤L := (Nat.mod_lt n hL).le
  have hne : ∀ᶠ n in atTop, (q n:ℝ)≠0 :=
    (hq.eventually_gt_atTop 0).mono fun _ hn => (Nat.cast_pos.mpr hn).ne'
  have hs : Tendsto (fun n : ℕ => (Nat.count p (L*q n):ℝ)/q n)
      atTop (𝓝 (∑ b ∈ range L, v b)) := by
    have hsum := tendsto_finsetSum (range L) fun b hb => (h b (mem_range.mp hb)).comp hq
    simpa only [hblock,Nat.cast_sum,sum_div,Function.comp_apply] using hsum
  have hsmall (g : ℕ → ℕ) (hg : ∀ n, g n≤L) :
      Tendsto (fun n => (g n:ℝ)/q n) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => by positivity) _ ((tendsto_const_div_atTop_nhds_zero_nat (L:ℝ)).comp hq)
    exact fun n => div_le_div_of_nonneg_right (by exact_mod_cast hg n) (by positivity)
  let tail (n : ℕ) := Nat.count (fun j => p (L*q n+j)) (r n)
  have ht := hsmall tail (fun n => (Nat.count_le _).trans (hr n))
  have hnum : Tendsto (fun n : ℕ => (Nat.count p n:ℝ)/q n) atTop (𝓝 (∑ b ∈ range L, v b)) := by
    rw [←add_zero (∑ b ∈ range L, v b)]
    apply (hs.add ht).congr
    intro n
    have hc : Nat.count p n=Nat.count p (L*q n)+tail n := by
      conv_lhs => rw [←heq n,Nat.count_add]
    rw [hc,Nat.cast_add,add_div]
  have hden : Tendsto (fun n : ℕ => (n:ℝ)/q n) atTop (𝓝 (L:ℝ)) := by
    rw [←add_zero (L:ℝ)]
    apply (tendsto_const_nhds.add (hsmall r hr)).congr'
    filter_upwards [hne] with n hn
    have hc : (L:ℝ)*(q n:ℝ)+(r n:ℝ)=n := by exact_mod_cast heq n
    rw [←hc,add_div,mul_div_cancel_right₀ _ hn]
  apply (hnum.div hden (Nat.cast_pos.mpr hL).ne').congr'
  filter_upwards [hne] with n hn
  exact div_div_div_cancel_right₀ hn _ _

#print axioms density_of_residue_densities
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.ResonantOccupation
