import GaloisForLFunctions.HTGeometry.HilbertSchmidtNearIsometryCount
import GaloisForLFunctions.RHTower.SoninIdealBadModeCount

/-!
# Energy surviving the relative-ideal errors

An operator estimated on an orthonormal family by "a unit target, up to finitely many relative-ideal
errors and a fixed slack" has energy at least the family's size, discounted twice.  The ideal errors
discount it by a *fixed* amount, since each is Hilbert--Schmidt and so exceeds a threshold on only
boundedly many members; the slack and the threshold discount each surviving member's contribution by
the squared shortfall from one.

Both discounts are independent of the family's size.  So the energy grows with the number of modes
supplied, no matter that the errors are only known qualitatively.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- **Survivor energy.**  If an operator carries each member of a finite orthonormal family to
within `(∑ₖ ‖Tₖ eᵢ‖) + β` of a unit vector, with each `Tₖ` in the principal-relative ideal, then its
Hilbert--Schmidt energy is at least the family's size less `∑ₖ hsNormSq Tₖ / ε²`, times `(1 - η)²`,
for any threshold `ε` and any `η ≥ (card κ) ε + β`. -/
theorem card_sub_le_hsNormSq_of_ideal_errors
    {Z : evenSubspace →L[ℂ] evenSubspace} (hZ : IsHilbertSchmidt Z)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : κ → evenSubspace →L[ℂ] evenSubspace)
    (hT : ∀ k, IsSoninPrincipalRelativeIdeal (T k))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → evenSubspace} (he : Orthonormal ℂ e)
    (u : ι → evenSubspace) (hu : ∀ i, ‖u i‖ = 1)
    (β ε η : ℝ) (hε : 0 < ε) (hη : η ≤ 1)
    (hcomb : (Fintype.card κ : ℝ) * ε + β ≤ η)
    (hest : ∀ i, ‖Z (e i) - u i‖ ≤ (∑ k : κ, ‖T k (e i)‖) + β) :
    ((Fintype.card ι : ℝ) - ∑ k : κ, hsNormSq (T k) / ε ^ (2 : ℕ)) * (1 - η) ^ (2 : ℕ) ≤ hsNormSq Z := by
  classical
  set S : Finset ι := Finset.univ.filter fun i : ι => ∀ k, ‖T k (e i)‖ < ε with hSdef
  have hcount := card_le_card_filter_forall_lt_of_isSoninPrincipalRelativeIdeal T hT he ε hε
  have hnear : ∀ i ∈ S, ‖Z (e i) - u i‖ ≤ η := by
    intro i hi
    have hlt : ∀ k, ‖T k (e i)‖ < ε := (Finset.mem_filter.mp hi).2
    have hsum : (∑ k : κ, ‖T k (e i)‖) ≤ (Fintype.card κ : ℝ) * ε := by
      calc (∑ k : κ, ‖T k (e i)‖) ≤ ∑ _k : κ, ε := Finset.sum_le_sum fun k _ => (hlt k).le
        _ = (Fintype.card κ : ℝ) * ε := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith [hest i, hsum, hcomb]
  have hS := card_mul_sq_le_hsNormSq_of_near_unit hZ he S u (fun i _ => hu i) η hη hnear
  have hsq : (0 : ℝ) ≤ (1 - η) ^ (2 : ℕ) := sq_nonneg _
  have hcard : (Fintype.card ι : ℝ) - ∑ k : κ, hsNormSq (T k) / ε ^ (2 : ℕ) ≤ (S.card : ℝ) := by
    linarith [hcount]
  exact le_trans (mul_le_mul_of_nonneg_right hcard hsq) hS

/-- **Survivor energy from a single ideal error.** -/
theorem card_sub_le_hsNormSq_of_one_ideal_error
    {Z : evenSubspace →L[ℂ] evenSubspace} (hZ : IsHilbertSchmidt Z)
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : IsSoninPrincipalRelativeIdeal T)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → evenSubspace} (he : Orthonormal ℂ e)
    (u : ι → evenSubspace) (hu : ∀ i, ‖u i‖ = 1)
    (β ε η : ℝ) (hε : 0 < ε) (hη : η ≤ 1) (hcomb : ε + β ≤ η)
    (hest : ∀ i, ‖Z (e i) - u i‖ ≤ ‖T (e i)‖ + β) :
    ((Fintype.card ι : ℝ) - hsNormSq T / ε ^ (2 : ℕ)) * (1 - η) ^ (2 : ℕ) ≤ hsNormSq Z := by
  classical
  have hmain := card_sub_le_hsNormSq_of_ideal_errors hZ (κ := Unit) (fun _ => T) (fun _ => hT)
    he u hu β ε η hε hη (by simpa using hcomb) (by simpa using hest)
  simpa using hmain

end RHTower
