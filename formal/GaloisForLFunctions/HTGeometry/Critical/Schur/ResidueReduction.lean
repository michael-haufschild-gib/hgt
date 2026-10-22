import GaloisForLFunctions.HTGeometry.Critical.Observation.JacobianMinor

/-!
# Reduction at the source Schur place

Three ingredients for transporting the generic corank-one statement to the residue field of the
source Schur place:

```text
mvPolynomialDropFirst, mvPolynomialDropFirst_rename_succ
mem_span_of_rename_succ_mem_span
    ** the variable shift reflects membership in a principal ideal **
map_aeval_rectangularSchurToeplitz
    ** the universal Schur matrix evaluates to the normalized reciprocal-square Toeplitz matrix **
criticalSchur_residue_algebraMap_eq_zero_iff
    ** a Schur coordinate polynomial has zero residue exactly on the ramification ideal **
```
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix IsLocalRing MvPolynomial

set_option synthInstance.maxHeartbeats 1000000

section DropFirst

variable (K : Type*) [CommRing K] (N : ℕ)

/-- The retraction of the variable shift: it kills the first variable and shifts the rest back. -/
def mvPolynomialDropFirst : MvPolynomial (Fin (N + 1)) K →ₐ[K] MvPolynomial (Fin N) K :=
  MvPolynomial.aeval (Fin.cases 0 MvPolynomial.X)

@[simp] theorem mvPolynomialDropFirst_rename_succ (p : MvPolynomial (Fin N) K) :
    mvPolynomialDropFirst K N (MvPolynomial.rename Fin.succ p) = p := by
  classical
  rw [mvPolynomialDropFirst, MvPolynomial.aeval_rename]
  have : (Fin.cases (motive := fun _ => MvPolynomial (Fin N) K) 0 MvPolynomial.X) ∘ Fin.succ
      = MvPolynomial.X := by
    funext i
    simp
  rw [this]
  exact MvPolynomial.aeval_X_left_apply p

/-- Membership in a principal ideal is reflected by the variable shift. -/
theorem mem_span_of_rename_succ_mem_span {K : Type*} [CommRing K] {N : ℕ}
    {a d : MvPolynomial (Fin N) K}
    (h : MvPolynomial.rename Fin.succ a ∈ Ideal.span
      ({MvPolynomial.rename Fin.succ d} : Set (MvPolynomial (Fin (N + 1)) K))) :
    a ∈ Ideal.span ({d} : Set (MvPolynomial (Fin N) K)) := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨g, hg⟩ := h
  refine ⟨mvPolynomialDropFirst K N g, ?_⟩
  have := congrArg (mvPolynomialDropFirst K N) hg
  rwa [mvPolynomialDropFirst_rename_succ, map_mul, mvPolynomialDropFirst_rename_succ] at this

end DropFirst

/-- **The universal Schur matrix evaluates to the normalized reciprocal-square Toeplitz matrix.** -/
theorem map_aeval_rectangularSchurToeplitz
    (K : Type*) [Field K] [CharZero K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    (rectangularSchurToeplitz (schurVar K (m + n - 1)) n m).map
        (MvPolynomial.aeval (criticalSourceReciprocalSquareReversed K hm hn))
      = rectangularSchurToeplitz
          (unitConstantSeries (criticalSourceReciprocalSquarePositive K hm hn)) n m := by
  classical
  let z := criticalSourceReciprocalSquarePositive K hm hn
  let zr := criticalSourceReciprocalSquareReversed K hm hn
  let φ : MvPolynomial (Fin (m + n - 1)) K →ₐ[K] criticalSourceField K m n :=
    MvPolynomial.aeval zr
  apply Matrix.ext
  intro i j
  rw [Matrix.map_apply]
  change φ (rectangularSchurToeplitz (schurVar K (m + n - 1)) n m i j) =
    rectangularSchurToeplitz (unitConstantSeries z) n m i j
  simp only [rectangularSchurToeplitz]
  by_cases hij : (j : ℕ) ≤ n + (i : ℕ)
  · rw [if_pos hij, if_pos hij]
    rcases hindex : n + (i : ℕ) - (j : ℕ) with _ | k
    · simp [φ, schurVar, unitConstantSeries]
    · have hk : k < m + n - 1 := by
        have hi := i.isLt
        omega
      rw [schurVar, if_neg (by omega : k + 1 ≠ 0), dif_pos (by omega)]
      rw [unitConstantSeries_succ z hk]
      simp only [φ, MvPolynomial.aeval_X, zr,
        criticalSourceReciprocalSquareReversed, z]
      congr 1
      apply Fin.ext
      simp
      omega
  · rw [if_neg hij, if_neg hij, map_zero]

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ}

omit [IsAlgClosed K] in
/-- The residue of a Schur coordinate polynomial vanishes exactly on the ramification ideal. -/
theorem criticalSchur_residue_algebraMap_eq_zero_iff (hm : 0 < m) (hn : 0 < n)
    (f : criticalSchurSourceRing K m n) :
    IsLocalRing.residue (criticalSchurSourceValuationSubring K hm hn)
        (algebraMap (criticalSchurSourceRing K m n)
          (criticalSchurSourceValuationSubring K hm hn) f) = 0
      ↔ f ∈ criticalSchurRamificationIdeal K m n := by
  rw [IsLocalRing.residue_eq_zero_iff]
  have hcomap := IsLocalization.AtPrime.under_maximalIdeal
    (R := criticalSchurSourceRing K m n)
    (S := criticalSchurSourceValuationSubring K hm hn)
    (I := (criticalSchurPrimeDivisor K hm hn).1)
  constructor
  · intro hmem
    have hf : f ∈ Ideal.under (criticalSchurSourceRing K m n)
        (IsLocalRing.maximalIdeal (criticalSchurSourceValuationSubring K hm hn)) := hmem
    rw [hcomap] at hf
    exact hf
  · intro hmem
    have hf : f ∈ Ideal.under (criticalSchurSourceRing K m n)
        (IsLocalRing.maximalIdeal (criticalSchurSourceValuationSubring K hm hn)) := by
      rw [hcomap]; exact hmem
    exact hf

end

end GaloisForLFunctions.HTGeometry
