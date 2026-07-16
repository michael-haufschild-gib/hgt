import GaloisForLFunctions.HTGeometry.TelescopeIdeal
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic

/-!
# Pair-face private sectors and exact transverse concealment order

On one free transverse orbit, pushing a finite pair-face charge through direction `k` sets its
augmentation variable to `1`.  The product of one augmentation factor in every direction outside
the pair is therefore invisible to every adjacent triple, but is itself nonzero.  Its total degree
is exactly the number of transverse directions.

This is the unconditional algebraic core of pair-face noncompression.  Turning the private charge
into a meromorphic hypertranscendental function additionally uses the analytic exact-image theorem
for compatible pair-face residues and is deliberately not asserted here.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial Finset

noncomputable section

variable {F : Type*} [Field F] {σ : Type*}

private theorem X_sub_one_ne_zero (k : σ) :
    (X k - 1 : MvPolynomial σ F) ≠ 0 := by
  intro h
  have heval := congrArg (eval fun _ => (0 : F)) h
  simp at heval

private theorem totalDegree_X_sub_one (k : σ) :
    totalDegree (X k - 1 : MvPolynomial σ F) = 1 := by
  rw [sub_eq_add_neg]
  calc
    totalDegree (X k + (-1 : MvPolynomial σ F)) = totalDegree (X k) :=
      totalDegree_add_eq_left_of_totalDegree_lt (by simp)
    _ = 1 := by simp

variable [DecidableEq σ]

/-- Substitute `1` for one augmentation variable and leave all other variables fixed.  On a free
orbit this is the algebraic form of pushforward in that transverse direction. -/
def setVariableOne (k : σ) : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  bind₁ fun i => if i = k then 1 else X i

/-- Substitute `1` simultaneously on a finite set of augmentation variables. -/
def setVariablesOne (s : Finset σ) : MvPolynomial σ F →ₐ[F] MvPolynomial σ F :=
  bind₁ fun i => if i ∈ s then 1 else X i

/-- The full transverse augmentation product on a finite set of directions. -/
def privateSectorPolynomial (s : Finset σ) : MvPolynomial σ F :=
  ∏ k ∈ s, (X k - 1)

omit [DecidableEq σ] in
/-- The transverse augmentation product is a nonzero orbit charge. -/
theorem privateSectorPolynomial_ne_zero (s : Finset σ) :
    privateSectorPolynomial (F := F) s ≠ 0 := by
  rw [privateSectorPolynomial, prod_ne_zero_iff]
  exact fun k _ => X_sub_one_ne_zero k

/-- Pushing the private charge through any one of its transverse directions kills it. -/
theorem setVariableOne_privateSectorPolynomial_eq_zero
    {s : Finset σ} {k : σ} (hk : k ∈ s) :
    setVariableOne (F := F) k (privateSectorPolynomial (F := F) s) = 0 := by
  rw [privateSectorPolynomial, map_prod]
  apply Finset.prod_eq_zero hk
  simp [setVariableOne]

/-- Pushing only in directions disjoint from the transverse support leaves the private charge
unchanged. -/
theorem setVariablesOne_privateSectorPolynomial_eq_self
    {s t : Finset σ} (hdisj : Disjoint s t) :
    setVariablesOne (F := F) s (privateSectorPolynomial (F := F) t) =
      privateSectorPolynomial (F := F) t := by
  rw [privateSectorPolynomial, map_prod]
  apply Finset.prod_congr rfl
  intro k hk
  have hks : k ∉ s := fun hks => Finset.disjoint_left.mp hdisj hks hk
  simp [setVariablesOne, hks]

/-- Pushing through any direction in the transverse support kills the private charge. -/
theorem setVariablesOne_privateSectorPolynomial_eq_zero
    {s t : Finset σ} {k : σ} (hks : k ∈ s) (hkt : k ∈ t) :
    setVariablesOne (F := F) s (privateSectorPolynomial (F := F) t) = 0 := by
  rw [privateSectorPolynomial, map_prod]
  apply Finset.prod_eq_zero hkt
  simp [setVariablesOne, hks]

/-- The private charge uses exactly one augmentation factor in every transverse direction. -/
theorem privateSectorPolynomial_totalDegree (s : Finset σ) :
    totalDegree (privateSectorPolynomial (F := F) s) = s.card := by
  induction s using Finset.induction_on with
  | empty => simp [privateSectorPolynomial]
  | @insert k s hk ih =>
      rw [privateSectorPolynomial, Finset.prod_insert hk]
      rw [totalDegree_mul_of_isDomain (X_sub_one_ne_zero k)
          (by simpa [privateSectorPolynomial] using
            privateSectorPolynomial_ne_zero (F := F) s),
        totalDegree_X_sub_one]
      rw [Finset.card_insert_of_notMem hk]
      have ih' : totalDegree (∏ x ∈ s, (X x - 1 : MvPolynomial σ F)) = s.card := by
        simpa [privateSectorPolynomial] using ih
      rw [ih']
      omega

/-- Every nonzero charge divisible by the full transverse product has augmentation degree at
least the number of transverse directions.  Combined with `TelescopeIdeal`'s intersection-equals-
product theorem, this is the lower bound for every private charge on a free orbit. -/
theorem privateSector_card_le_totalDegree_of_dvd
    {s : Finset σ} {P : MvPolynomial σ F} (hP : P ≠ 0)
    (hdiv : privateSectorPolynomial (F := F) s ∣ P) :
    s.card ≤ totalDegree P := by
  rw [← privateSectorPolynomial_totalDegree (F := F) s]
  exact totalDegree_le_of_dvd_of_isDomain hdiv hP

/-- The canonical charge private to a pair: multiply one augmentation factor for every direction
outside the pair. -/
def pairPrivateWitness (d : ℕ) (e : Finset (Fin d)) : MvPolynomial (Fin d) F :=
  privateSectorPolynomial (F := F) (Finset.univ \ e)

/-- A pair-private witness is nonzero, is killed by every transverse push, and has exact transverse
order `d - 2` when `e` is a pair. -/
theorem pairPrivateWitness_exact
    {d : ℕ} {e : Finset (Fin d)} (he : e.card = 2) :
    pairPrivateWitness (F := F) d e ≠ 0 ∧
      (∀ k ∉ e, setVariableOne (F := F) k (pairPrivateWitness (F := F) d e) = 0) ∧
      totalDegree (pairPrivateWitness (F := F) d e) = d - 2 := by
  refine ⟨privateSectorPolynomial_ne_zero (F := F) (Finset.univ \ e), ?_, ?_⟩
  · intro k hk
    apply setVariableOne_privateSectorPolynomial_eq_zero (F := F)
    simp [hk]
  · rw [pairPrivateWitness, privateSectorPolynomial_totalDegree]
    calc
      (Finset.univ \ e).card = d - e.card := by
        rw [Finset.card_sdiff]
        simp
      _ = d - 2 := by rw [he]

/-- The private witness is visible on its chosen pair coordinate and vanishes on every other pair
coordinate.  Thus deleting any pair coordinate loses a concrete nonzero orbit charge. -/
theorem pairPrivateWitness_coordinates
    {d : ℕ} {e f : Finset (Fin d)} (he : e.card = 2) (hf : f.card = 2) (hef : f ≠ e) :
    setVariablesOne (F := F) e (pairPrivateWitness (F := F) d e) =
        pairPrivateWitness (F := F) d e ∧
      setVariablesOne (F := F) f (pairPrivateWitness (F := F) d e) = 0 := by
  constructor
  · change setVariablesOne (F := F) e
        (privateSectorPolynomial (F := F) (Finset.univ \ e)) = _
    apply setVariablesOne_privateSectorPolynomial_eq_self (F := F)
    exact Finset.disjoint_sdiff
  · have hnsub : ¬f ⊆ e := by
      intro hsub
      apply hef
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    obtain ⟨k, hkf, hke⟩ := Finset.not_subset.mp hnsub
    change setVariablesOne (F := F) f
      (privateSectorPolynomial (F := F) (Finset.univ \ e)) = 0
    apply setVariablesOne_privateSectorPolynomial_eq_zero (F := F) hkf
    simp [hke]

end

end GaloisForLFunctions.HTGeometry
