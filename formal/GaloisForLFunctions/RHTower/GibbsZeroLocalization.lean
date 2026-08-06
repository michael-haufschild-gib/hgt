import Mathlib
import GaloisForLFunctions.RHTower.GibbsCurrentGap

/-!
# Only zeros near the parity point can cancel

Each zero contributes the cross-ratio `‖1−ζ‖/‖1+ζ‖` to the ratio of partition function to
parity current, and `‖1−ζ‖ ≤ 2 + ‖1+ζ‖`, so a zero at distance `d` from the parity point
contributes at most `1 + 2/d`.  Distant zeros are therefore inert: all cancellation is
produced by zeros close to the parity point, and

  `‖Z_S(x)‖ · ∏_ζ ‖1+ζ‖  ≤  ‖J_S(x)‖ · ∏_ζ (2 + ‖1+ζ‖)`

(division-free form, valid at every coupling and with no stability hypothesis).  Together
with the gap bound of the previous module this closes the dictionary between the parity
current and the geometry of the gas zero set.
-/

namespace RHTower.GibbsGas

open Polynomial

/-- Monotonicity of a multiset product under a pointwise bound. -/
theorem multiset_prod_map_le (s : Multiset ℂ) (f g : ℂ → ℝ)
    (hf : ∀ ζ ∈ s, 0 ≤ f ζ) (hle : ∀ ζ ∈ s, f ζ ≤ g ζ) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hfa : 0 ≤ f a := hf a (Multiset.mem_cons_self a s)
    have hlea : f a ≤ g a := hle a (Multiset.mem_cons_self a s)
    have hfs : ∀ ζ ∈ s, 0 ≤ f ζ := fun ζ hζ => hf ζ (Multiset.mem_cons_of_mem hζ)
    have hles : ∀ ζ ∈ s, f ζ ≤ g ζ := fun ζ hζ => hle ζ (Multiset.mem_cons_of_mem hζ)
    have hprod0 : (0 : ℝ) ≤ (s.map f).prod :=
      Multiset.prod_nonneg fun w hw => by
        obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hw
        exact hfs ζ hζ
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact mul_le_mul hlea (ih hfs hles) hprod0 (le_trans hfa hlea)

/-- **Per-zero localization.**  A zero at distance `d` from the parity point is at distance
at most `2 + d` from the opposite point. -/
theorem norm_one_sub_le_two_add (ζ : ℂ) : ‖1 - ζ‖ ≤ 2 + ‖1 + ζ‖ := by
  have hrw : (1 : ℂ) - ζ = 2 - (1 + ζ) := by ring
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  rw [hrw]
  refine le_trans (norm_sub_le _ _) ?_
  rw [hnorm2]

/-- **Distant zeros are inert.**  The partition function exceeds the parity current only by
the product of the per-zero localization factors: all cancellation comes from zeros near
the parity point. -/
theorem gibbs_partition_le_current_mul_localization (S : Finset ℕ) (x : ℝ) :
    ‖gibbsDiagC S x 1‖ * (((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod)
      ≤ ‖gibbsDiagC S x (-1)‖
        * (((gibbsPoly S x).roots.map (fun ζ => 2 + ‖1 + ζ‖)).prod) := by
  rw [norm_gibbs_partition_eq, norm_gibbs_current_eq]
  have hB : (0 : ℝ) ≤ ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod :=
    Multiset.prod_nonneg fun w hw => by
      obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp hw
      exact norm_nonneg _
  have hAC : ((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod
      ≤ ((gibbsPoly S x).roots.map (fun ζ => 2 + ‖1 + ζ‖)).prod :=
    multiset_prod_map_le _ _ _ (fun ζ _ => norm_nonneg _)
      (fun ζ _ => norm_one_sub_le_two_add ζ)
  have hstep : ((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod
        * ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod
      ≤ ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod
        * ((gibbsPoly S x).roots.map (fun ζ => 2 + ‖1 + ζ‖)).prod := by
    calc ((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod
          * ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod
        ≤ ((gibbsPoly S x).roots.map (fun ζ => 2 + ‖1 + ζ‖)).prod
          * ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod :=
          mul_le_mul_of_nonneg_right hAC hB
      _ = ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod
          * ((gibbsPoly S x).roots.map (fun ζ => 2 + ‖1 + ζ‖)).prod := by ring
  have hexp : (0 : ℝ) < Real.exp (-(x * ∏ p ∈ S, (p : ℝ))) := Real.exp_pos _
  calc Real.exp (-(x * ∏ p ∈ S, (p : ℝ)))
          * ((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod
        * ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod
      = Real.exp (-(x * ∏ p ∈ S, (p : ℝ)))
          * (((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod
            * ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod) := by ring
    _ ≤ Real.exp (-(x * ∏ p ∈ S, (p : ℝ)))
          * (((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod
            * ((gibbsPoly S x).roots.map (fun ζ => 2 + ‖1 + ζ‖)).prod) :=
        mul_le_mul_of_nonneg_left hstep hexp.le
    _ = Real.exp (-(x * ∏ p ∈ S, (p : ℝ)))
          * ((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod
        * ((gibbsPoly S x).roots.map (fun ζ => 2 + ‖1 + ζ‖)).prod := by ring

end RHTower.GibbsGas
