import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Sharp power mass of a finite arithmetic population

The cumulative right-endpoint inequality of arXiv:2603.08959 bounds
an increasing power sum below by its integral. First minimizing over
the possible positions identifies the exact finite minimizer and the
best possible coefficient uniformly in the population size.
-/
noncomputable section
open Finset Filter Set Topology
namespace GaloisForLFunctions.ArithmeticPowerMass

/-- The cheapest m distinct indices above a are a through a+m-1. -/
theorem minimum_shifted_index_mass (f : ℕ → ℝ) (hf : Monotone f) (a : ℕ) (S : Finset ℕ)
    (ha : ∀ k ∈ S, a≤k) :
    ∑ j ∈ range S.card, f (a+j) ≤ ∑ k ∈ S, f k := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert x S hx ih =>
    have hn : x∉S := fun h => (hx x h).false
    have hS := fun k (hk : k∈S) => ha k (mem_insert_of_mem hk)
    have hsub : S ⊆ Finset.Ico a x := fun k hk => mem_Ico.mpr ⟨hS k hk,hx k hk⟩
    have hc := card_le_card hsub
    rw [Nat.card_Ico] at hc
    have hax := ha x (mem_insert_self ..)
    have hlast := hf (show a+S.card≤x by omega)
    rw [card_insert_of_notMem hn,sum_range_succ,sum_insert hn]
    linarith only [ih hS,hlast]

/-- Every strictly increasing weight has the same unique minimizing
population of a given size. -/
theorem initial_segment_is_unique_minimizer (f : ℕ → ℝ) (hf : StrictMono f) (S : Finset ℕ) :
    (∑ k ∈ S, f k) = (∑ j ∈ range S.card, f j) ↔ S = range S.card := by
  constructor
  · induction S using Finset.induction_on_max with
    | empty => simp
    | insert x S hx ih =>
      intro he
      have hn : x∉S := fun h => (hx x h).false
      have hsub : S ⊆ range x := fun k hk => mem_range.mpr (hx k hk)
      have hcx : S.card≤x := by simpa only [card_range] using card_le_card hsub
      have hprev := minimum_shifted_index_mass f hf.monotone 0 S (fun _ _ => Nat.zero_le _)
      simp only [zero_add] at hprev
      rw [sum_insert hn,card_insert_of_notMem hn,sum_range_succ] at he
      have hfx := hf.monotone hcx
      have heq := hf.injective (show f x=f S.card by linarith only [he,hfx,hprev])
      have hS := ih (show (∑ k ∈ S, f k)=(∑ j ∈ range S.card, f j) by
        rw [heq] at he; linarith only [he])
      rw [card_insert_of_notMem hn,range_succ,heq]
      exact congrArg (insert S.card) hS
  · intro h; exact congrArg (fun T : Finset ℕ => ∑ k ∈ T, f k) h

private theorem sum_shifted_indices (a n : ℕ) :
    (∑ k ∈ range n, ((a+k:ℕ):ℝ)) = (n:ℝ)*a+(n:ℝ)*((n:ℝ)-1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ,ih]; push_cast; ring

/-- Displacing r members of an m-point population beyond the index
m-1 raises its first moment above the triangular minimum by at least
r squared, even when the vacated and occupied positions are chosen
after observing the population. -/
theorem square_cost_of_displaced_indices (S : Finset ℕ) :
    (S.card:ℝ)*((S.card:ℝ)-1)/2 + (((S.filter fun k => S.card≤k).card:ℝ))^2 ≤
      ∑ k ∈ S, (k:ℝ) := by
  let H := S.filter fun k => S.card≤k
  let A := S \ H
  have hs : H⊆S := filter_subset _ _
  have hA := minimum_shifted_index_mass (fun k : ℕ => (k:ℝ)) Nat.cast_mono 0 A
    (fun _ _ => Nat.zero_le _)
  have hH := minimum_shifted_index_mass (fun k : ℕ => (k:ℝ)) Nat.cast_mono S.card H
    (fun _ hk => (mem_filter.mp hk).2)
  rw [sum_shifted_indices] at hA hH
  have hc : (S.card:ℝ)=(A.card:ℝ)+(H.card:ℝ) := by
    exact_mod_cast (card_sdiff_add_card_eq_card hs).symm
  have hsum : (∑ k ∈ A, (k:ℝ)) + (∑ k ∈ H, (k:ℝ)) = ∑ k ∈ S, (k:ℝ) := sum_sdiff hs
  change (S.card:ℝ)*((S.card:ℝ)-1)/2 + (H.card:ℝ)^2 ≤ _
  rw [hc] at hH ⊢
  linarith only [hA,hH,hsum]

/-- The factor v+1 in the cardinality-to-moment inequality is sharp. -/
theorem sharp_cardinality_power_mass (S : Finset ℕ) {v : ℝ} (hv : 0≤v) :
    (S.card:ℝ)^(v+1) ≤ (v+1) * ∑ k ∈ S, ((k:ℝ)+1)^v := by
  let f (x : ℝ) := x^v
  have hm : MonotoneOn f (Set.Icc 0 (0+(S.card:ℝ))) :=
    fun x hx y _ hxy => Real.rpow_le_rpow hx.1 hxy hv
  have hi := MonotoneOn.integral_le_sum (a:=S.card) hm
  have hp : 0<v+1 := by linarith only [hv]
  simp only [f,zero_add,Nat.cast_succ,integral_rpow (Or.inl (by linarith only [hv] : -1<v)),
    Real.zero_rpow hp.ne',sub_zero] at hi
  have hsum := minimum_shifted_index_mass (fun k => ((k:ℝ)+1)^v) (fun i j hij =>
    Real.rpow_le_rpow (by positivity) (add_le_add (Nat.cast_le.mpr hij) (le_refl (1:ℝ))) hv) 0 S
    (fun _ _ => Nat.zero_le _)
  simp only [zero_add] at hsum
  exact ((div_le_iff₀ hp).mp (hi.trans hsum)).trans_eq (mul_comm _ _)

/-- The first m indices approach the universal lower coefficient as
m tends to infinity. Consequently no smaller multiplicative constant
can replace v+1 in the cardinality bound. -/
theorem normalized_initial_power_mass {v : ℝ} (hv : 0≤v) :
    Tendsto (fun n : ℕ => (∑ k ∈ range n, ((k:ℝ)+1)^v)/(n:ℝ)^(v+1))
      atTop (𝓝 (1/(v+1))) := by
  have hp : 0<v+1 := by linarith only [hv]
  have hi : Tendsto (fun n : ℕ => ((n:ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => ((n:ℝ)+1)/n) atTop (𝓝 1) := by
    apply (show Tendsto (fun n : ℕ => 1+(n:ℝ)⁻¹) atTop (𝓝 1) by simpa using hi.const_add 1).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    field_simp [(Nat.cast_pos.mpr hn : 0<(n:ℝ)).ne']
  have hu := (hr.rpow_const (p:=v+1) (Or.inl one_ne_zero)).div_const (v+1)
  rw [Real.one_rpow] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : 0<(n:ℝ) := Nat.cast_pos.mpr hn
    have h := sharp_cardinality_power_mass (range n) hv
    rw [card_range] at h
    exact (div_le_div_iff₀ hp (Real.rpow_pos_of_pos hx _)).mpr (by linarith only [h])
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hx : 0<(n:ℝ) := Nat.cast_pos.mpr hn
    have hm : MonotoneOn (fun x : ℝ => x^v) (Set.Icc 1 (1+(n:ℝ))) :=
      fun x hx' y _ hxy => Real.rpow_le_rpow (zero_le_one.trans hx'.1) hxy hv
    have h := MonotoneOn.sum_le_integral (a:=n) hm
    rw [integral_rpow (Or.inl (by linarith only [hv] : -1<v)),Real.one_rpow] at h
    simp only [add_comm (1:ℝ)] at h
    rw [Real.div_rpow (by positivity : 0≤(n:ℝ)+1) hx.le,div_div, mul_comm ((n:ℝ)^(v+1)),
      ← div_div]
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
    exact h.trans (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hp.le)

#print axioms square_cost_of_displaced_indices
#print axioms initial_segment_is_unique_minimizer
#print axioms sharp_cardinality_power_mass
#print axioms normalized_initial_power_mass
end GaloisForLFunctions.ArithmeticPowerMass
