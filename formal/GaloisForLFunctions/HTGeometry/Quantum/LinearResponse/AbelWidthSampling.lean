import GaloisForLFunctions.HTGeometry.WeightedDeterminantDegree
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardMatrix
import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelForwardFibers
import Mathlib.Algebra.Polynomial.Roots

/-!
# Recovery from finitely many damping widths

Cramer's rule gives a degree bound of one less than the dimension of the
matrix space for each response numerator. A commutant shared at enough
widths therefore commutes with the unfiltered probe.
-/

open Matrix Set Polynomial
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem natDegree_det_le_column_sum (A : Matrix ι ι (Polynomial ℂ)) (w : ι → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ w j) : A.det.natDegree ≤ ∑ j, w j := by
  let e := Fintype.equivFin ι
  have he (i j : Fin (Fintype.card ι)) :
      ((Matrix.reindex e e A) i j).degree ≤ (0 : WithBot ℕ) + (w (e.symm j) : WithBot ℕ) := by
    rw [zero_add]
    exact Polynomial.natDegree_le_iff_degree_le.mp (h (e.symm i) (e.symm j))
  have hd := natDegree_det_le_of_degree_le (Matrix.reindex e e A) (fun _ => 0)
    (fun j => w (e.symm j)) he
  rw [Matrix.det_reindex_self, Finset.sum_const_zero, zero_add, Equiv.sum_comp e.symm w] at hd
  exact hd

private theorem sum_excluding_column {κ : Type*} [Fintype κ] [DecidableEq κ] (p : κ) :
    (∑ j, if j = p then 0 else (1 : ℕ)) = Fintype.card κ - 1 := by
  have he := Finset.sum_erase_add (f := fun j : κ => if j = p then 0 else (1 : ℕ))
    Finset.univ (Finset.mem_univ p)
  rw [if_pos rfl, add_zero] at he
  rw [← he]
  calc
    _ = ∑ _j ∈ (Finset.univ : Finset κ).erase p, (1 : ℕ) := by
      exact Finset.sum_congr rfl fun j hj => if_neg (Finset.mem_erase.mp hj).1
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ p)]
      rfl

/-- Numerator of a forward reading as a polynomial in inverse width. -/
def abelWidthNumerator (H X : Matrix ι ι ℂ) : Matrix ι ι (Polynomial ℂ) :=
  abelClearedResponse Polynomial.X (H.map Polynomial.C) (X.map Polynomial.C)

theorem map_abelWidthNumerator_eval (H X : Matrix ι ι ℂ) (γ : ℂ) :
    (abelWidthNumerator H X).map (Polynomial.evalRingHom γ) = abelClearedResponse γ H X := by
  let f := Polynomial.evalRingHom γ
  have hc (Y : Matrix ι ι ℂ) : (Y.map Polynomial.C).map f = Y :=
    Matrix.ext fun _ _ => Polynomial.eval_C
  change (abelClearedResponse Polynomial.X (H.map Polynomial.C) (X.map Polynomial.C)).map f = _
  rw [map_abelClearedResponse, hc, hc]
  exact congrArg (fun z => abelClearedResponse z H X) Polynomial.eval_X

omit [Fintype ι] in
private theorem natDegree_abelForwardPencil_X_apply_le (H : Matrix ι ι ℂ) (p q : ι × ι) :
    (abelForwardPencil Polynomial.X (H.map Polynomial.C) p q).natDegree ≤ 1 := by
  rw [abelForwardPencil, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    ← map_commutatorKroneckerMatrix Polynomial.C H, Matrix.map_apply]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · by_cases h : p = q
    · rw [h, Matrix.one_apply_eq, Polynomial.natDegree_one]
      exact Nat.zero_le 1
    · rw [Matrix.one_apply_ne h, Polynomial.natDegree_zero]
      exact Nat.zero_le 1
  · exact Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_X, Polynomial.natDegree_C,
      add_zero])

/-- Replacing one affine column by constant forcing lowers the maximal degree by one. -/
theorem natDegree_abelWidthNumerator_apply_le (H X : Matrix ι ι ℂ) (i j : ι) :
    (abelWidthNumerator H X i j).natDegree ≤ Fintype.card (ι × ι) - 1 := by
  let A := abelForwardPencil Polynomial.X (H.map Polynomial.C)
  let p := (j, i)
  let b := (X.map Polynomial.C).vec
  have he : abelWidthNumerator H X i j = (A.updateCol p b).det := by
    change (A.adjugate *ᵥ b) p = _
    rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  rw [he, ← sum_excluding_column p]
  apply natDegree_det_le_column_sum
  intro r q
  by_cases h : q = p
  · subst q
    rw [if_pos rfl, Matrix.updateCol_self]
    change (Polynomial.C (X r.2 r.1)).natDegree ≤ 0
    rw [Polynomial.natDegree_C]
  · rw [if_neg h, Matrix.updateCol_ne h]
    exact natDegree_abelForwardPencil_X_apply_le H r q

private theorem natDegree_widthCommutator_apply_le (H X T : Matrix ι ι ℂ) (i j : ι) :
    (((T.map Polynomial.C) * abelWidthNumerator H X -
      abelWidthNumerator H X * (T.map Polynomial.C)) i j).natDegree ≤ Fintype.card (ι × ι) - 1 := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Matrix.map_apply, Polynomial.natDegree_C, zero_add]
    exact natDegree_abelWidthNumerator_apply_le H X k j
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro k _
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Matrix.map_apply, Polynomial.natDegree_C, add_zero]
    exact natDegree_abelWidthNumerator_apply_le H X i k

private theorem widthCommutator_eval (H X T : Matrix ι ι ℂ) (γ : ℂ) :
    (Polynomial.evalRingHom γ).mapMatrix
      (T.map Polynomial.C * abelWidthNumerator H X - abelWidthNumerator H X * T.map Polynomial.C) =
      T * abelClearedResponse γ H X - abelClearedResponse γ H X * T := by
  let f := Polynomial.evalRingHom γ
  have hT : f.mapMatrix (T.map Polynomial.C) = T :=
    Matrix.ext fun _ _ => Polynomial.eval_C
  have hN : f.mapMatrix (abelWidthNumerator H X) = abelClearedResponse γ H X :=
    map_abelWidthNumerator_eval H X γ
  change f.mapMatrix (_ - _) = _
  rw [map_sub, map_mul, map_mul, hT, hN]

/-- Commutation at sufficiently many widths implies commutation with
the forcing and with the responses at all widths. -/
theorem commute_of_sampled_abelResponse {H : Matrix ι ι ℂ} (hH : H.IsHermitian)
    (T X : Matrix ι ι ℂ) (s : Finset (Ioi (0 : ℝ)))
    (hs : Fintype.card (ι × ι) - 1 < s.card)
    (hc : ∀ ε ∈ s, Commute T (hamiltonianDampedGapResponse hH 0 ε X)) :
    Commute T X ∧ ∀ ε, Commute T (hamiltonianDampedGapResponse hH 0 ε X) := by
  let W := T.map Polynomial.C * abelWidthNumerator H X - abelWidthNumerator H X * T.map Polynomial.C
  let f : s → ℂ := fun ε => (hamiltonianAbelShift ε.1)⁻¹
  have hf : Function.Injective f := by
    intro ε η he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg Complex.im (inv_injective he)
  have hW (ε : s) : (Polynomial.evalRingHom (f ε)).mapMatrix W = 0 := by
    have he := (hc ε.1 ε.2).eq
    rw [show (Polynomial.evalRingHom (f ε)).mapMatrix W =
      T * abelClearedResponse (f ε) H X - abelClearedResponse (f ε) H X * T
        from widthCommutator_eval H X T (f ε)]
    change T * abelClearedResponse (hamiltonianAbelShift ε.1)⁻¹ H X -
      abelClearedResponse (hamiltonianAbelShift ε.1)⁻¹ H X * T = 0
    rw [abelClearedResponse_eq hH, Matrix.mul_smul, Matrix.smul_mul, he, sub_self]
  have hzero : W = 0 := by
    apply Matrix.ext
    intro i j
    change W i j = 0
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (W i j) hf
    · intro ε
      exact congrArg (fun M : Matrix ι ι ℂ => M i j) (hW ε)
    · rw [Fintype.card_coe]
      exact (natDegree_widthCommutator_apply_le H X T i j).trans_lt hs
  have hδ (γ : ℂ) :
      0 = T * abelClearedResponse γ H X - abelClearedResponse γ H X * T := by
    have he := widthCommutator_eval H X T γ
    change (Polynomial.evalRingHom γ).mapMatrix W = _ at he
    rw [hzero, map_zero] at he
    exact he
  constructor
  · have he := hδ 0
    rw [abelClearedResponse_zeroParameter] at he
    exact sub_eq_zero.mp he.symm
  · intro ε
    let A := abelForwardPencil (hamiltonianAbelShift ε)⁻¹ H
    have hn : A.det ≠ 0 := isUnit_iff_ne_zero.mp
      ((Matrix.isUnit_iff_isUnit_det A).mp (isUnit_abelForwardPencil hH ε))
    have he := hδ (hamiltonianAbelShift ε)⁻¹
    rw [abelClearedResponse_eq hH, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub] at he
    exact sub_eq_zero.mp ((smul_eq_zero.mp he.symm).resolve_left hn)

/-- For any fixed probe, equality at enough sampled widths implies
equality at every positive width. -/
theorem abelForwardReading_sampled_eq_iff_all_widths {H K : Matrix ι ι ℂ}
    (hH : H.IsHermitian) (hK : K.IsHermitian) (X : Matrix ι ι ℂ) (s : Finset (Ioi (0 : ℝ)))
    (hs : Fintype.card (ι × ι) - 1 < s.card) :
    (∀ ε ∈ s, hamiltonianDampedGapResponse hH 0 ε X =
      hamiltonianDampedGapResponse hK 0 ε X) ↔
      ∀ ε, hamiltonianDampedGapResponse hH 0 ε X = hamiltonianDampedGapResponse hK 0 ε X := by
  constructor
  · intro h ε
    apply (abelForwardReading_eq_iff_commute hH hK ε X).mpr
    exact (commute_of_sampled_abelResponse hH (H - K) X s hs
      (fun η hη => (abelForwardReading_eq_iff_commute hH hK η X).mp (h η hη))).2 ε
  · exact fun h ε _ => h ε

/-- Agreement of both fixed probes at any (d^2) distinct positive
widths determines the Hamiltonian up to a scalar shift. -/
theorem abelForwardReadings_sampled_eq_iff_scalarDifference {d : ℕ} (o : Fin d)
    {H K : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) (hK : K.IsHermitian)
    (s : Finset (Ioi (0 : ℝ))) (hs : d ^ 2 ≤ s.card) :
    (∀ ε ∈ s, hamiltonianDampedGapResponse hH 0 ε (abelDiagonalProbe d) =
        hamiltonianDampedGapResponse hK 0 ε (abelDiagonalProbe d) ∧
      hamiltonianDampedGapResponse hH 0 ε (abelSumProbe d) =
        hamiltonianDampedGapResponse hK 0 ε (abelSumProbe d)) ↔
      ∃ c : ℂ, H - K = c • 1 := by
  constructor
  · intro h
    have hs' : Fintype.card (Fin d × Fin d) - 1 < s.card := by
      rw [Fintype.card_prod, Fintype.card_fin, ← pow_two]
      exact (Nat.sub_lt (pow_pos (Nat.zero_lt_of_lt o.isLt) _) Nat.zero_lt_one).trans_le hs
    let ε₀ : Ioi (0 : ℝ) := ⟨1, by
      change (0 : ℝ) < 1
      exact zero_lt_one⟩
    have hinv (X : Matrix (Fin d) (Fin d) ℂ)
        (hX : ∀ ε ∈ s, hamiltonianDampedGapResponse hH 0 ε X =
          hamiltonianDampedGapResponse hK 0 ε X) :
        hamiltonianAbelInverse (H - K) ε₀ X = hamiltonianAbelInverse 0 ε₀ X := by
      have hc := commute_of_sampled_abelResponse hH (H - K) X s hs'
        (fun ε hε => (abelForwardReading_eq_iff_commute hH hK ε X).mp (hX ε hε))
      apply (hamiltonianAbelInverse_eq_iff_commutators (H - K) 0 ε₀ X).mpr
      rw [Matrix.zero_mul, Matrix.mul_zero, sub_zero]
      exact sub_eq_zero.mpr hc.1.eq
    obtain ⟨c, he⟩ := (abelProbeReadings_eq_iff_scalarDifference o (H - K) 0 ε₀).mp
      ⟨hinv _ (fun ε hε => (h ε hε).1), hinv _ (fun ε hε => (h ε hε).2)⟩
    exact ⟨c, by simpa only [sub_zero] using he⟩
  · intro h ε _
    have he := (hamiltonianDampedGapResponse_zero_eq_iff_scalarDifference o hH hK ε).mpr h
    exact ⟨congrFun he (abelDiagonalProbe d), congrFun he (abelSumProbe d)⟩

#print axioms natDegree_abelWidthNumerator_apply_le
#print axioms commute_of_sampled_abelResponse
#print axioms abelForwardReading_sampled_eq_iff_all_widths
#print axioms abelForwardReadings_sampled_eq_iff_scalarDifference

end

end GaloisForLFunctions.HTGeometry
