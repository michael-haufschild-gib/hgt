import GaloisForLFunctions.HTGeometry.HilbertSchmidtBadModeCount
import GaloisForLFunctions.RHTower.SoninPrincipalRelativeCyclicExtension

/-!
# A relative-ideal error contracts all but boundedly many modes

Every element of the principal-relative ideal is Schatten-1, hence Hilbert--Schmidt, so its energy
is a finite number fixed once and for all.  Counting modes against that energy shows that in any
finite orthonormal family, the members it fails to contract below a threshold number at most the
energy divided by the squared threshold — a bound independent of the family.

This is what a growing family of wavepackets needs: the ideal errors of the aperture reduction are
fixed operators, so they can spoil only boundedly many members however many are supplied.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap

/-- Every relative-ideal element is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_of_isSoninPrincipalRelativeIdeal
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : IsSoninPrincipalRelativeIdeal T) :
    IsHilbertSchmidt T :=
  MemSchattenClass.one_isHilbertSchmidt (IsSoninPrincipalRelativeIdeal.memSchattenClass_one hT)

/-- The exact projection correction is Hilbert--Schmidt. -/
theorem isHilbertSchmidt_evenSoninProjectionCorrection (a : ℝ) (ha : 0 < a) :
    IsHilbertSchmidt (evenSoninProjectionCorrection a) :=
  isHilbertSchmidt_of_isSoninPrincipalRelativeIdeal
    (IsSoninPrincipalRelativeIdeal.projectionCorrection a ha)

/-- **Bounded spoilage.**  A relative-ideal error exceeds a threshold on at most
`hsNormSq T / ε²` members of any finite orthonormal family. -/
theorem card_filter_le_hsNormSq_of_isSoninPrincipalRelativeIdeal
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : IsSoninPrincipalRelativeIdeal T)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → evenSubspace} (he : Orthonormal ℂ e)
    (ε : ℝ) (hε : 0 < ε) :
    (((Finset.univ.filter fun i => ε ≤ ‖T (e i)‖).card : ℝ)) * ε ^ (2 : ℕ) ≤ hsNormSq T :=
  card_filter_le_hsNormSq (isHilbertSchmidt_of_isSoninPrincipalRelativeIdeal hT) he ε hε

/-- **Surviving modes.**  All but at most `hsNormSq T / ε²` members of a finite orthonormal family
are contracted below `ε` by a relative-ideal error. -/
theorem card_le_card_filter_lt_of_isSoninPrincipalRelativeIdeal
    {T : evenSubspace →L[ℂ] evenSubspace} (hT : IsSoninPrincipalRelativeIdeal T)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → evenSubspace} (he : Orthonormal ℂ e)
    (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card ι : ℝ) ≤
      ((Finset.univ.filter fun i => ‖T (e i)‖ < ε).card : ℝ) + hsNormSq T / ε ^ (2 : ℕ) :=
  card_le_card_filter_lt_add_hsNormSq (isHilbertSchmidt_of_isSoninPrincipalRelativeIdeal hT)
    he ε hε

/-- **Simultaneous survival for finitely many ideal errors.**  Given a finite list of relative-ideal
errors, all but a bounded number of the family's members are contracted below `ε` by every one of
them at once. -/
theorem card_le_card_filter_forall_lt_of_isSoninPrincipalRelativeIdeal
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (T : κ → evenSubspace →L[ℂ] evenSubspace)
    (hT : ∀ k, IsSoninPrincipalRelativeIdeal (T k))
    {ι : Type*} [Fintype ι] [DecidableEq ι] {e : ι → evenSubspace} (he : Orthonormal ℂ e)
    (ε : ℝ) (hε : 0 < ε) :
    (Fintype.card ι : ℝ) ≤
      ((Finset.univ.filter fun i => ∀ k, ‖T k (e i)‖ < ε).card : ℝ) +
        ∑ k : κ, hsNormSq (T k) / ε ^ (2 : ℕ) := by
  classical
  have hcover : (Finset.univ.filter fun i : ι => ¬ ∀ k, ‖T k (e i)‖ < ε) ⊆
      Finset.univ.biUnion fun k : κ => Finset.univ.filter fun i : ι => ε ≤ ‖T k (e i)‖ := by
    intro i hi
    obtain ⟨k, hk⟩ := not_forall.mp (Finset.mem_filter.mp hi).2
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k,
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, not_lt.mp hk⟩⟩
  have hcard : ((Finset.univ.filter fun i : ι => ¬ ∀ k, ‖T k (e i)‖ < ε).card : ℝ) ≤
      ∑ k : κ, ((Finset.univ.filter fun i : ι => ε ≤ ‖T k (e i)‖).card : ℝ) := by
    have hnat := le_trans (Finset.card_le_card hcover) (Finset.card_biUnion_le)
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    simpa only [Nat.cast_sum] using this
  have hεsq : (0 : ℝ) < ε ^ (2 : ℕ) := by positivity
  have hterm : ∀ k : κ, ((Finset.univ.filter fun i : ι => ε ≤ ‖T k (e i)‖).card : ℝ) ≤
      hsNormSq (T k) / ε ^ (2 : ℕ) := fun k =>
    (le_div_iff₀ hεsq).mpr
      (card_filter_le_hsNormSq_of_isSoninPrincipalRelativeIdeal (hT k) he ε hε)
  have hsum : ((Finset.univ.filter fun i : ι => ¬ ∀ k, ‖T k (e i)‖ < ε).card : ℝ) ≤
      ∑ k : κ, hsNormSq (T k) / ε ^ (2 : ℕ) :=
    le_trans hcard (Finset.sum_le_sum fun k _ => hterm k)
  have hsplit : (Finset.univ.filter fun i : ι => ∀ k, ‖T k (e i)‖ < ε).card +
      (Finset.univ.filter fun i : ι => ¬ ∀ k, ‖T k (e i)‖ < ε).card = Fintype.card ι := by
    have := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => ∀ k, ‖T k (e i)‖ < ε)
    simpa only [Finset.card_univ] using this
  have hcast : (Fintype.card ι : ℝ) =
      ((Finset.univ.filter fun i : ι => ∀ k, ‖T k (e i)‖ < ε).card : ℝ) +
        ((Finset.univ.filter fun i : ι => ¬ ∀ k, ‖T k (e i)‖ < ε).card : ℝ) := by
    rw [← Nat.cast_add, hsplit]
  rw [hcast]
  linarith

end RHTower
