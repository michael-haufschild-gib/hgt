import Mathlib
import GaloisForLFunctions.RHTower.GibbsWeakCouplingConfinement

/-!
# The parity current as a cross-ratio product over the gas zeros

The gas is a polynomial in the activity, of exact degree `|S|` with nonvanishing leading
coefficient `e^{-x·m}`, so over `ℂ` it factors completely.  Evaluating the factorization at
the two special activities `z = -1` (parity) and `z = 1` (partition function) gives the
finite-volume condensation law

  `‖J_S(x)‖ · ∏_ζ ‖1 - ζ‖ = ‖Z_S(x)‖ · ∏_ζ ‖1 + ζ‖`,

the product running over the zeros of the gas with multiplicity: **the parity current is
exactly the cross-ratio product of the gas zeros against the parity point**, at every
coupling.  Any control of the zero locations therefore transfers directly to the current;
confinement of the zeros to distance `ρ` of the parity point yields the exponential
cancellation `‖J_S‖·(2-ρ)^{|S|} ≤ ‖Z_S‖·ρ^{|S|}`.
-/

namespace RHTower.GibbsGas

open Polynomial

/-- The Boltzmann weight of a configuration, as a complex scalar. -/
noncomputable def gibbsWeight (x : ℝ) (T : Finset ℕ) : ℂ :=
  ((Real.exp (-(x * ∏ p ∈ T, (p : ℝ))) : ℝ) : ℂ)

theorem gibbsWeight_ne_zero (x : ℝ) (T : Finset ℕ) : gibbsWeight x T ≠ 0 := by
  rw [gibbsWeight, Ne, Complex.ofReal_eq_zero]
  exact ne_of_gt (Real.exp_pos _)

/-- The gas as a polynomial in the activity. -/
noncomputable def gibbsPoly (S : Finset ℕ) (x : ℝ) : Polynomial ℂ :=
  ∑ T ∈ S.powerset, Polynomial.C (gibbsWeight x T) * Polynomial.X ^ T.card

theorem gibbsPoly_eval (S : Finset ℕ) (x : ℝ) (z : ℂ) :
    (gibbsPoly S x).eval z = gibbsDiagC S x z := by
  rw [gibbsPoly, gibbsDiagC, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    gibbsWeight, mul_comm]

theorem gibbsPoly_coeff (S : Finset ℕ) (x : ℝ) (j : ℕ) :
    (gibbsPoly S x).coeff j
      = ∑ T ∈ S.powerset.filter (fun T => T.card = j), gibbsWeight x T := by
  classical
  rw [gibbsPoly, Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : T.card = j
  · rw [if_pos h, if_pos h.symm, mul_one]
  · rw [if_neg h, if_neg (fun hh : j = T.card => h hh.symm), mul_zero]

/-- The top coefficient of the gas is the Boltzmann weight of the full configuration. -/
theorem gibbsPoly_coeff_card (S : Finset ℕ) (x : ℝ) :
    (gibbsPoly S x).coeff S.card = gibbsWeight x S := by
  classical
  rw [gibbsPoly_coeff]
  have hfilter : S.powerset.filter (fun T => T.card = S.card) = {S} := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
    · rintro rfl
      exact ⟨Finset.Subset.refl _, rfl⟩
  rw [hfilter, Finset.sum_singleton]

theorem gibbsPoly_natDegree (S : Finset ℕ) (x : ℝ) :
    (gibbsPoly S x).natDegree = S.card := by
  classical
  refine le_antisymm ?_ ?_
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [gibbsPoly_coeff]
    have hempty : S.powerset.filter (fun T => T.card = m) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun T hT => ?_
      rw [Finset.mem_powerset] at hT
      have := Finset.card_le_card hT
      omega
    rw [hempty, Finset.sum_empty]
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [gibbsPoly_coeff_card]
    exact gibbsWeight_ne_zero x S

theorem gibbsPoly_ne_zero (S : Finset ℕ) (x : ℝ) : gibbsPoly S x ≠ 0 := by
  intro h
  have hc := gibbsPoly_coeff_card S x
  rw [h, Polynomial.coeff_zero] at hc
  exact gibbsWeight_ne_zero x S hc.symm

/-- Norms multiply along a multiset product. -/
theorem norm_multiset_prod_complex (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map (fun w => ‖w‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- **Complete factorization of the gas** over its zero multiset. -/
theorem gibbsDiagC_eq_prod_roots (S : Finset ℕ) (x : ℝ) (z : ℂ) :
    gibbsDiagC S x z
      = (gibbsPoly S x).leadingCoeff
        * (((gibbsPoly S x).roots.map (fun ζ => z - ζ)).prod) := by
  have hsplits : (gibbsPoly S x).Splits := IsAlgClosed.splits _
  have hfac := hsplits.eq_prod_roots
  have := congrArg (fun q => Polynomial.eval z q) hfac
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
    Multiset.map_map, Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at this
  rw [gibbsPoly_eval] at this
  exact this

/-- The gas has exactly `|S|` zeros, with multiplicity. -/
theorem gibbs_roots_card (S : Finset ℕ) (x : ℝ) :
    (gibbsPoly S x).roots.card = S.card := by
  rw [IsAlgClosed.card_roots_eq_natDegree, gibbsPoly_natDegree]

/-- **The finite-volume condensation law.**  At every coupling the parity current is the
cross-ratio product of the gas zeros against the parity point. -/
theorem gibbs_parity_cross_ratio (S : Finset ℕ) (x : ℝ) :
    ‖gibbsDiagC S x (-1)‖
        * (((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod)
      = ‖gibbsDiagC S x 1‖
        * (((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod) := by
  have hJ : ‖gibbsDiagC S x (-1)‖
      = ‖(gibbsPoly S x).leadingCoeff‖
        * (((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod) := by
    rw [gibbsDiagC_eq_prod_roots, norm_mul, norm_multiset_prod_complex,
      Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun ζ _ => ?_
    simp only [Function.comp_apply]
    rw [show (-1 : ℂ) - ζ = -(1 + ζ) from by ring, norm_neg]
  have hZ : ‖gibbsDiagC S x 1‖
      = ‖(gibbsPoly S x).leadingCoeff‖
        * (((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod) := by
    rw [gibbsDiagC_eq_prod_roots, norm_mul, norm_multiset_prod_complex,
      Multiset.map_map]
    congr 2
  rw [hJ, hZ]
  ring

/-- Confined zeros give a small cross-ratio product. -/
theorem prod_norm_one_add_le (s : Multiset ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ ζ ∈ s, ‖1 + ζ‖ ≤ ρ) :
    (s.map (fun ζ => ‖1 + ζ‖)).prod ≤ ρ ^ s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ‖1 + a‖ ≤ ρ := h a (Multiset.mem_cons_self a s)
    have hs : ∀ ζ ∈ s, ‖1 + ζ‖ ≤ ρ := fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ)
    have hp0 : (0 : ℝ) ≤ (s.map (fun ζ => ‖1 + ζ‖)).prod :=
      Multiset.prod_nonneg fun w hw => by
        obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp hw
        exact norm_nonneg _
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc ‖1 + a‖ * (s.map (fun ζ => ‖1 + ζ‖)).prod
        ≤ ρ * (s.map (fun ζ => ‖1 + ζ‖)).prod := mul_le_mul_of_nonneg_right ha hp0
      _ ≤ ρ * ρ ^ s.card := mul_le_mul_of_nonneg_left (ih hs) hρ
      _ = ρ ^ s.card * ρ := by ring

/-- Confined zeros stay far from the opposite point. -/
theorem pow_le_prod_norm_one_sub (s : Multiset ℂ) {ρ : ℝ} (hρ : ρ ≤ 2)
    (h : ∀ ζ ∈ s, ‖1 + ζ‖ ≤ ρ) :
    (2 - ρ) ^ s.card ≤ (s.map (fun ζ => ‖1 - ζ‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : (2 : ℝ) - ρ ≤ ‖1 - a‖ :=
      norm_one_sub_ge_of_norm_one_add_le a (h a (Multiset.mem_cons_self a s))
    have hs : ∀ ζ ∈ s, ‖1 + ζ‖ ≤ ρ := fun ζ hζ => h ζ (Multiset.mem_cons_of_mem hζ)
    have hρ0 : (0 : ℝ) ≤ 2 - ρ := by linarith
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    calc (2 - ρ) ^ s.card * (2 - ρ)
        ≤ (s.map (fun ζ => ‖1 - ζ‖)).prod * (2 - ρ) :=
          mul_le_mul_of_nonneg_right (ih hs) hρ0
      _ ≤ (s.map (fun ζ => ‖1 - ζ‖)).prod * ‖1 - a‖ :=
          mul_le_mul_of_nonneg_left ha
            (Multiset.prod_nonneg fun w hw => by
              obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp hw
              exact norm_nonneg _)
      _ = ‖1 - a‖ * (s.map (fun ζ => ‖1 - ζ‖)).prod := by ring

/-- **Confinement gives exponential parity cancellation.**  If every gas zero lies within
`ρ` of the parity point then the current is smaller than the partition function by the
factor `(ρ/(2-ρ))^{|S|}`. -/
theorem norm_gibbs_current_le_of_confinement (S : Finset ℕ) (x : ℝ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2)
    (hconf : ∀ ζ : ℂ, gibbsDiagC S x ζ = 0 → ‖1 + ζ‖ ≤ ρ) :
    ‖gibbsDiagC S x (-1)‖ * (2 - ρ) ^ S.card
      ≤ ‖gibbsDiagC S x 1‖ * ρ ^ S.card := by
  have hroot : ∀ ζ ∈ (gibbsPoly S x).roots, ‖1 + ζ‖ ≤ ρ := by
    intro ζ hζ
    refine hconf ζ ?_
    rw [← gibbsPoly_eval]
    exact (Polynomial.mem_roots (gibbsPoly_ne_zero S x)).mp hζ
  have hlow := pow_le_prod_norm_one_sub (gibbsPoly S x).roots hρ2 hroot
  have hhigh := prod_norm_one_add_le (gibbsPoly S x).roots hρ0 hroot
  rw [gibbs_roots_card] at hlow hhigh
  have hid := gibbs_parity_cross_ratio S x
  have hJ0 : (0 : ℝ) ≤ ‖gibbsDiagC S x (-1)‖ := norm_nonneg _
  have hZ0 : (0 : ℝ) ≤ ‖gibbsDiagC S x 1‖ := norm_nonneg _
  calc ‖gibbsDiagC S x (-1)‖ * (2 - ρ) ^ S.card
      ≤ ‖gibbsDiagC S x (-1)‖
          * (((gibbsPoly S x).roots.map (fun ζ => ‖1 - ζ‖)).prod) :=
        mul_le_mul_of_nonneg_left hlow hJ0
    _ = ‖gibbsDiagC S x 1‖
          * (((gibbsPoly S x).roots.map (fun ζ => ‖1 + ζ‖)).prod) := hid
    _ ≤ ‖gibbsDiagC S x 1‖ * ρ ^ S.card := mul_le_mul_of_nonneg_left hhigh hZ0

end RHTower.GibbsGas
