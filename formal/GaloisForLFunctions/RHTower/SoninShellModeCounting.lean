import GaloisForLFunctions.HTGeometry.HilbertSchmidtDominatesPointwise
import GaloisForLFunctions.RHTower.SoninEvenCarrier

/-!
# Counting shell modes inside the Hilbert--Schmidt energy

A fixed shell carries an orthonormal family of modes indexed by the mode number, so the
Hilbert--Schmidt energy of any operator dominates the total energy it puts on any finite set of
them, and dominates the count of the modes it does not contract.

This is the instrument a growth rate needs: the family lives in one fixed shell and is indexed by a
number that can grow with the scale, unlike a subdivision of the window into ever more annuli.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open ContinuousLinearMap

/-- **Shell modes inside the energy.**  The Hilbert--Schmidt energy dominates the total image energy
of any finite set of shell modes. -/
theorem sum_norm_sq_evenShellVectorEven_apply_le_hsNormSq
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : T.IsHilbertSchmidt)
    (s t : ℝ) (hs : 0 < s) (hst : s < t) (F : Finset ℕ) :
    ∑ j ∈ F, ‖T (evenShellVectorEven s t hst j)‖ ^ 2 ≤ hsNormSq T := by
  classical
  have hortho : Orthonormal ℂ (fun j : F => evenShellVectorEven s t hst (j : ℕ)) :=
    (evenShellVectorEven_orthonormal s t hs hst).comp _ Subtype.val_injective
  have hsum := sum_norm_sq_apply_le_hsNormSq hT hortho
  have hconv : ∑ j : F, ‖T (evenShellVectorEven s t hst (j : ℕ))‖ ^ 2 =
      ∑ j ∈ F, ‖T (evenShellVectorEven s t hst j)‖ ^ 2 :=
    Finset.sum_coe_sort F (fun j => ‖T (evenShellVectorEven s t hst j)‖ ^ 2)
  rw [← hconv]
  exact hsum

/-- **Mode counting.**  The Hilbert--Schmidt energy dominates the number of shell modes the operator
does not contract. -/
theorem card_le_hsNormSq_of_evenShellVectorEven
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : T.IsHilbertSchmidt)
    (s t : ℝ) (hs : 0 < s) (hst : s < t) (F : Finset ℕ)
    (hmodes : ∀ j ∈ F, 1 ≤ ‖T (evenShellVectorEven s t hst j)‖) :
    (F.card : ℝ) ≤ hsNormSq T := by
  refine le_trans ?_ (sum_norm_sq_evenShellVectorEven_apply_le_hsNormSq hT s t hs hst F)
  have hterm : ∀ j ∈ F, (1 : ℝ) ≤ ‖T (evenShellVectorEven s t hst j)‖ ^ 2 := by
    intro j hj
    have h := hmodes j hj
    nlinarith [norm_nonneg (T (evenShellVectorEven s t hst j))]
  calc (F.card : ℝ) = ∑ _j ∈ F, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ j ∈ F, ‖T (evenShellVectorEven s t hst j)‖ ^ 2 := Finset.sum_le_sum hterm

end RHTower
