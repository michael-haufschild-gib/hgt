import Mathlib
import GaloisForLFunctions.RHTower.GibbsZeroLocalization

/-!
# Cancellation is bounded by the Coulomb potential of the zeros

Taking logarithms in the localization inequality turns the product over zeros into a sum,
which is the form that survives when the zero set is large: inert zeros contribute
essentially nothing.  Writing `d_ζ = ‖1+ζ‖` for the distance of a zero to the parity point,

  `log ‖Z_S(x)‖ − log ‖J_S(x)‖  ≤  ∑_ζ 2 / d_ζ`.

So the logarithmic cancellation of a Möbius–Laplace sum never exceeds twice the Coulomb
potential of the gas zeros at the parity point: **strong cancellation requires the zeros to
accumulate near `-1`**, quantitatively and at every coupling.
-/

namespace RHTower.GibbsGas

open Polynomial

/-- The logarithm of a multiset product of positive reals. -/
theorem multiset_log_prod (s : Multiset ℝ) (h : ∀ a ∈ s, 0 < a) :
    Real.log s.prod = (s.map Real.log).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : 0 < a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ b ∈ s, 0 < b := fun b hb => h b (Multiset.mem_cons_of_mem hb)
    have hprod : 0 < s.prod := Multiset.prod_pos hs
    rw [Multiset.prod_cons, Real.log_mul (ne_of_gt ha) (ne_of_gt hprod),
      Multiset.map_cons, Multiset.sum_cons, ih hs]

/-- Pointwise comparison of multiset sums. -/
theorem multiset_sum_map_le {α : Type*} (s : Multiset α) (f g : α → ℝ)
    (h : ∀ a ∈ s, f a ≤ g a) : (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : f a ≤ g a := h a (Multiset.mem_cons_self a s)
    have hs : ∀ b ∈ s, f b ≤ g b := fun b hb => h b (Multiset.mem_cons_of_mem hb)
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
    exact add_le_add ha (ih hs)

/-- Splitting a multiset sum of a pointwise sum. -/
theorem multiset_sum_map_add {α : Type*} (s : Multiset α) (f g : α → ℝ) :
    (s.map (fun a => f a + g a)).sum = (s.map f).sum + (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_cons, Multiset.sum_cons, ih]
    ring

/-- The partition function of the gas is a positive real. -/
theorem gibbsDiagC_one_ne_zero (S : Finset ℕ) (x : ℝ) : gibbsDiagC S x 1 ≠ 0 := by
  rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) by norm_num, gibbsDiagC_ofReal]
  rw [Ne, Complex.ofReal_eq_zero]
  refine ne_of_gt ?_
  rw [gibbsDiag]
  refine Finset.sum_pos (fun T _ => ?_) ⟨∅, by simp⟩
  positivity

/-- No zero of the gas sits at the parity point when the current is nonzero. -/
theorem norm_one_add_pos_of_root (S : Finset ℕ) (x : ℝ)
    (hJ : gibbsDiagC S x (-1) ≠ 0) {ζ : ℂ} (hζ : ζ ∈ (gibbsPoly S x).roots) :
    0 < ‖1 + ζ‖ := by
  rcases eq_or_lt_of_le (norm_nonneg (1 + ζ)) with h | h
  · exfalso
    have hz : ζ = -1 := by
      have : (1 : ℂ) + ζ = 0 := by
        rwa [eq_comm, norm_eq_zero] at h
      linear_combination this
    apply hJ
    rw [← hz, ← gibbsPoly_eval]
    exact (Polynomial.mem_roots (gibbsPoly_ne_zero S x)).mp hζ
  · exact h

/-- **The potential bound.**  The logarithmic cancellation is at most twice the Coulomb
potential of the gas zeros at the parity point. -/
theorem log_partition_sub_log_current_le (S : Finset ℕ) (x : ℝ)
    (hJ : gibbsDiagC S x (-1) ≠ 0) :
    Real.log ‖gibbsDiagC S x 1‖ - Real.log ‖gibbsDiagC S x (-1)‖
      ≤ ((gibbsPoly S x).roots.map (fun ζ => 2 / ‖1 + ζ‖)).sum := by
  classical
  set rts := (gibbsPoly S x).roots with hrts
  have hd : ∀ ζ ∈ rts, 0 < ‖1 + ζ‖ := fun ζ hζ =>
    norm_one_add_pos_of_root S x hJ hζ
  have hA : (0 : ℝ) < (rts.map (fun ζ => ‖1 + ζ‖)).prod := by
    refine Multiset.prod_pos fun w hw => ?_
    obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hw
    exact hd ζ hζ
  have hB : (0 : ℝ) < (rts.map (fun ζ => 2 + ‖1 + ζ‖)).prod := by
    refine Multiset.prod_pos fun w hw => ?_
    obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp hw
    positivity
  have hZ : (0 : ℝ) < ‖gibbsDiagC S x 1‖ :=
    norm_pos_iff.mpr (gibbsDiagC_one_ne_zero S x)
  have hJp : (0 : ℝ) < ‖gibbsDiagC S x (-1)‖ := norm_pos_iff.mpr hJ
  -- the localization inequality, then logarithms
  have hloc := gibbs_partition_le_current_mul_localization S x
  have hlog := Real.log_le_log (by positivity) hloc
  rw [Real.log_mul (ne_of_gt hZ) (ne_of_gt hA),
    Real.log_mul (ne_of_gt hJp) (ne_of_gt hB),
    multiset_log_prod _ (fun w hw => by
      obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hw
      exact hd ζ hζ),
    multiset_log_prod _ (fun w hw => by
      obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp hw
      positivity)] at hlog
  rw [Multiset.map_map, Multiset.map_map] at hlog
  -- compare the two logarithmic sums termwise
  have hterm : ∀ ζ ∈ rts,
      (Real.log ∘ fun ζ => 2 + ‖1 + ζ‖) ζ
        ≤ (Real.log ∘ fun ζ => ‖1 + ζ‖) ζ + 2 / ‖1 + ζ‖ := by
    intro ζ hζ
    have hdζ := hd ζ hζ
    simp only [Function.comp_apply]
    have hdiv : (0 : ℝ) < (2 + ‖1 + ζ‖) / ‖1 + ζ‖ := by positivity
    have hle : Real.log ((2 + ‖1 + ζ‖) / ‖1 + ζ‖)
        ≤ (2 + ‖1 + ζ‖) / ‖1 + ζ‖ - 1 := Real.log_le_sub_one_of_pos hdiv
    rw [Real.log_div (by positivity) (ne_of_gt hdζ)] at hle
    have hval : (2 + ‖1 + ζ‖) / ‖1 + ζ‖ - 1 = 2 / ‖1 + ζ‖ := by
      field_simp
      ring
    rw [hval] at hle
    linarith
  have hsum := multiset_sum_map_le rts _ _ hterm
  rw [multiset_sum_map_add rts (Real.log ∘ fun ζ => ‖1 + ζ‖)
    (fun ζ => 2 / ‖1 + ζ‖)] at hsum
  linarith

/-- No zero of the gas sits at `1`: the partition function is a positive real. -/
theorem norm_one_sub_pos_of_root (S : Finset ℕ) (x : ℝ)
    {ζ : ℂ} (hζ : ζ ∈ (gibbsPoly S x).roots) : 0 < ‖1 - ζ‖ := by
  rcases eq_or_lt_of_le (norm_nonneg (1 - ζ)) with h | h
  · exfalso
    have hz : ζ = 1 := by
      have hzero : (1 : ℂ) - ζ = 0 := by
        rwa [eq_comm, norm_eq_zero] at h
      linear_combination -hzero
    refine gibbsDiagC_one_ne_zero S x ?_
    rw [← hz, ← gibbsPoly_eval]
    exact (Polynomial.mem_roots (gibbsPoly_ne_zero S x)).mp hζ
  · exact h

/-- **The condensation law in exact logarithmic form.**  The logarithmic cancellation of a
Möbius–Laplace sum is exactly the sum, over the gas zeros, of the logarithmic cross-ratios
against the parity point.  Both the necessary and the sufficient direction are readings of
this single identity. -/
theorem log_cancellation_eq (S : Finset ℕ) (x : ℝ)
    (hJ : gibbsDiagC S x (-1) ≠ 0) :
    Real.log ‖gibbsDiagC S x 1‖ - Real.log ‖gibbsDiagC S x (-1)‖
      = ((gibbsPoly S x).roots.map
          (fun ζ => Real.log ‖1 - ζ‖ - Real.log ‖1 + ζ‖)).sum := by
  classical
  set rts := (gibbsPoly S x).roots with hrts
  have hdplus : ∀ ζ ∈ rts, 0 < ‖1 + ζ‖ := fun ζ hζ =>
    norm_one_add_pos_of_root S x hJ hζ
  have hdminus : ∀ ζ ∈ rts, 0 < ‖1 - ζ‖ := fun ζ hζ =>
    norm_one_sub_pos_of_root S x hζ
  have hexp : (0 : ℝ) < Real.exp (-(x * ∏ p ∈ S, (p : ℝ))) := Real.exp_pos _
  have hA : (0 : ℝ) < (rts.map (fun ζ => ‖1 + ζ‖)).prod := by
    refine Multiset.prod_pos fun w hw => ?_
    obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hw
    exact hdplus ζ hζ
  have hB : (0 : ℝ) < (rts.map (fun ζ => ‖1 - ζ‖)).prod := by
    refine Multiset.prod_pos fun w hw => ?_
    obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hw
    exact hdminus ζ hζ
  have hlogA : Real.log (rts.map (fun ζ => ‖1 + ζ‖)).prod
      = (rts.map (fun ζ => Real.log ‖1 + ζ‖)).sum := by
    rw [multiset_log_prod _ (fun w hw => by
      obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hw
      exact hdplus ζ hζ)]
    simp only [Multiset.map_map, Function.comp_def]
  have hlogB : Real.log (rts.map (fun ζ => ‖1 - ζ‖)).prod
      = (rts.map (fun ζ => Real.log ‖1 - ζ‖)).sum := by
    rw [multiset_log_prod _ (fun w hw => by
      obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hw
      exact hdminus ζ hζ)]
    simp only [Multiset.map_map, Function.comp_def]
  have hsplitGen : ∀ s : Multiset ℂ,
      (s.map (fun ζ => Real.log ‖1 - ζ‖ - Real.log ‖1 + ζ‖)).sum
        = (s.map (fun ζ => Real.log ‖1 - ζ‖)).sum
          - (s.map (fun ζ => Real.log ‖1 + ζ‖)).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [ih]
      ring
  have hsplit := hsplitGen rts
  rw [norm_gibbs_partition_eq, norm_gibbs_current_eq,
    Real.log_mul (ne_of_gt hexp) (ne_of_gt hB),
    Real.log_mul (ne_of_gt hexp) (ne_of_gt hA), hlogA, hlogB, hsplit]
  ring

end RHTower.GibbsGas
