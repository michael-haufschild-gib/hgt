import GaloisForLFunctions.HTGeometry.HilbertSchmidtDominatesPointwise

/-!
# How many modes a Hilbert--Schmidt operator can fail to contract

Family domination bounds the total image energy of a finite orthonormal family by the operator's
Hilbert--Schmidt energy.  Reading that bound from below rather than from above counts modes: every
family member whose image exceeds `ε` contributes at least `ε²`, so the number of such members is at
most the energy divided by `ε²`.

The count does not grow with the family.  So along a family whose size grows, all but a bounded
number of members are contracted below `ε` — which is what lets a growing orthonormal family survive
a fixed Hilbert--Schmidt perturbation.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Bad-mode count.**  In a finite orthonormal family, the members whose image exceeds `ε` number
at most the Hilbert--Schmidt energy divided by `ε²`. -/
theorem card_filter_le_hsNormSq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → E} (he : Orthonormal 𝕜 e)
    (ε : ℝ) (hε : 0 < ε) :
    (((Finset.univ.filter fun i => ε ≤ ‖T (e i)‖).card : ℝ)) * ε ^ 2 ≤ hsNormSq T := by
  classical
  set S : Finset ι := Finset.univ.filter fun i => ε ≤ ‖T (e i)‖ with hS
  have hlow : ((S.card : ℝ)) * ε ^ 2 ≤ ∑ i ∈ S, ‖T (e i)‖ ^ 2 := by
    have hconst : ((S.card : ℝ)) * ε ^ 2 = ∑ _i ∈ S, ε ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    refine Finset.sum_le_sum fun i hi => ?_
    have hbig : ε ≤ ‖T (e i)‖ := (Finset.mem_filter.mp hi).2
    nlinarith [hε.le, hbig]
  have hsub : ∑ i ∈ S, ‖T (e i)‖ ^ 2 ≤ ∑ i, ‖T (e i)‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun i _ _ => by positivity
  exact le_trans (le_trans hlow hsub) (sum_norm_sq_apply_le_hsNormSq hT he)

/-- **Surviving-mode count.**  All but at most `hsNormSq T / ε²` members of a finite orthonormal
family have image below `ε`. -/
theorem card_le_card_filter_lt_add_hsNormSq {T : E →L[𝕜] F} (hT : IsHilbertSchmidt T)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → E} (he : Orthonormal 𝕜 e)
    (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card ι : ℝ) ≤
      ((Finset.univ.filter fun i => ‖T (e i)‖ < ε).card : ℝ) + hsNormSq T / ε ^ 2 := by
  classical
  have hsplit : (Finset.univ.filter fun i => ‖T (e i)‖ < ε).card +
      (Finset.univ.filter fun i => ε ≤ ‖T (e i)‖).card = Fintype.card ι := by
    rw [add_comm]
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => ε ≤ ‖T (e i)‖)
    simpa only [not_le, Finset.card_univ] using this
  have hbad := card_filter_le_hsNormSq hT he ε hε
  have hεsq : (0 : ℝ) < ε ^ 2 := by positivity
  have hbad' : (((Finset.univ.filter fun i => ε ≤ ‖T (e i)‖).card : ℝ)) ≤ hsNormSq T / ε ^ 2 :=
    (le_div_iff₀ hεsq).mpr hbad
  have hcast : (Fintype.card ι : ℝ) =
      ((Finset.univ.filter fun i => ‖T (e i)‖ < ε).card : ℝ) +
        ((Finset.univ.filter fun i => ε ≤ ‖T (e i)‖).card : ℝ) := by
    rw [← Nat.cast_add, hsplit]
  rw [hcast]
  linarith

end RHTower
