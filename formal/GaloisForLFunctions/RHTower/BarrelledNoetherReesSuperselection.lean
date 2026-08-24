import GaloisForLFunctions.HTGeometry.BarrelledSeminormBound
import GaloisForLFunctions.RHTower.ReesGradeFiltrationPrimeWoldWitness

/-!
# Barrelled Noether currents cannot cross an asymptotic-type wall

A pointwise-bounded family of continuous scalar currents on a barrelled normed source is uniformly
bounded in operator norm by Banach--Steinhaus.  It therefore has Rees grade zero on every
contracting scale.  Such a family cannot carry an all-orders-flat source history to a nonflat
finite-grade charge history.

This is the topology-sensitive bridge between the corpus's null-orbit Noether mechanism and its
Rees/Hawking/modular superselection mechanism.  It introduces no vanishing, RH, divisor, or
arithmetic premise.  Arithmetic applications must still construct the completed source and prove
pointwise boundedness of the fixed current family.
-/

open Set Filter Asymptotics

namespace RHTower

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Banach--Steinhaus upgrades pointwise bounded scalar currents on a barrelled normed source to
one uniform operator-norm bound along any filter. -/
theorem barrelledPointwiseBounded_opNorm_isBigO_one
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [BarrelledSpace ℝ E]
    (l : Filter ι) (F : ι → E →L[ℝ] ℝ)
    (hpointwise : ∀ y : E, BddAbove (Set.range fun i : ι => ‖F i y‖)) :
    (fun i => ‖F i‖) =O[l] fun _ => (1 : ℝ) := by
  let p : Fin 1 → Seminorm ℝ E := fun _ => normSeminorm ℝ E
  have hp : WithSeminorms p := by
    simpa [p] using (norm_withSeminorms ℝ E)
  obtain ⟨s, C, huniform⟩ :=
    exists_seminorm_bound_of_bddAbove hp F hpointwise
  have hseminorm : s.sup p ≤ normSeminorm ℝ E := by
    apply Finset.sup_le
    intro i hi
    rfl
  have hop : ∀ i : ι, ‖F i‖ ≤ (C : ℝ) := by
    intro i
    apply (F i).opNorm_le_bound (NNReal.coe_nonneg C)
    intro x
    refine (huniform i x).trans ?_
    simpa [p] using
      (mul_le_mul_of_nonneg_left (hseminorm x) (NNReal.coe_nonneg C))
  apply IsBigO.of_bound (C : ℝ)
  filter_upwards [] with i
  simpa only [Real.norm_eq_abs, abs_norm, norm_one, mul_one] using hop i

/-- Every pointwise-bounded scalar current family on a barrelled source belongs to every finite
Rees grade on a contracting scale.  Grade zero is the operative conclusion; higher grades are
included for reuse by the filtered source calculus. -/
theorem barrelledPointwiseBounded_reesOperatorGradeAtMost
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [BarrelledSpace ℝ E]
    (l : Filter ι) (a : ι → ℝ)
    (hscale : ∀ᶠ i in l, 0 < a i ∧ a i ≤ 1)
    (F : ι → E →L[ℝ] ℝ)
    (hpointwise : ∀ y : E, BddAbove (Set.range fun i : ι => ‖F i y‖))
    (K : ℕ) :
    ReesOperatorGradeAtMost l a K F :=
  reesOperatorGradeAtMost_of_isBigO_one hscale
    (barrelledPointwiseBounded_opNorm_isBigO_one l F hpointwise) K

/-- **Null-provenance superselection.**  A pointwise-bounded family of continuous currents on one
barrelled source cannot resurrect a nonflat charge history from an all-orders-flat source history.
Any exact sewing across that asymptotic-type wall must therefore leave the pointwise-bounded
finite-action category. -/
theorem no_barrelledPointwiseBounded_sews_flat_to_nonflat
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [BarrelledSpace ℝ E]
    (l : Filter ι) (a : ι → ℝ) (F : ι → E →L[ℝ] ℝ)
    (f : ι → E) (g : ι → ℝ)
    (ha : ∀ᶠ i in l, a i ≠ 0)
    (hscale : ∀ᶠ i in l, 0 < a i ∧ a i ≤ 1)
    (hpointwise : ∀ y : E, BddAbove (Set.range fun i : ι => ‖F i y‖))
    (hf : ReesAllOrdersFlat l a f)
    (hg : ¬ ReesAllOrdersFlat l a g) :
    (fun i => F i (f i)) ≠ g :=
  no_finiteReesOperator_sews_flat_to_nonflat l a 0 F f g ha
    (barrelledPointwiseBounded_reesOperatorGradeAtMost
      l a hscale F hpointwise 0) hf hg

end

end RHTower
