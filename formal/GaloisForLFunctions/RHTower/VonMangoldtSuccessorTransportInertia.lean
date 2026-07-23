import GaloisForLFunctions.HTGeometry.SignedAtomicMomentInertia
import GaloisForLFunctions.RHTower.VonMangoldtSuccessorPrincipalRelativeHankel
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Exact inertia of the von Mangoldt successor transport

The aperture-`M` principal-relative moment is a signed atomic moment on the `M + 1` consecutive
logarithmic nodes `log 2, ..., log (M + 2)`.  At an interior node, the atomic mass is incoming
von Mangoldt conductance minus outgoing von Mangoldt conductance; the two endpoints retain the
unpaired outgoing and incoming conductances.  The full `(M + 1)`-jet section is therefore a square
Vandermonde congruence of this diagonal transport mass.

This file proves the exact positive, negative, and null indices.  In particular, every nonempty
aperture has a negative direction forced by the left endpoint `2`.
-/

open scoped BigOperators Matrix

namespace RHTower

noncomputable section

/-- Consecutive logarithmic node number `i + 2` in the aperture-`M` transport. -/
def vonMangoldtSuccessorTransportNode (M : ℕ) (i : Fin (M + 1)) : ℝ :=
  Real.log ((i : ℕ) + 2 : ℕ)

/-- Consolidated signed mass at one node of the aperture-`M` successor transport.

Each edge `p + 2 -> p + 3` contributes positively at its target and negatively at its source.
The factor `log(i + 2)^2` accounts for the two-index offset in the principal-relative Hankel
matrix. -/
def vonMangoldtSuccessorTransportMass (M : ℕ) (i : Fin (M + 1)) : ℝ :=
  (∑ p : Fin M,
      ((if p.succ = i then finiteVonMangoldtRealWeight ((p : ℕ) + 2) else 0) -
        (if Fin.castSucc p = i then
          finiteVonMangoldtRealWeight ((p : ℕ) + 2) else 0))) *
    vonMangoldtSuccessorTransportNode M i ^ 2

/-- Consecutive logarithmic transport nodes are pairwise distinct. -/
theorem vonMangoldtSuccessorTransportNode_injective (M : ℕ) :
    Function.Injective (vonMangoldtSuccessorTransportNode M) := by
  intro i j hij
  apply Fin.ext
  have hcast :
      (((i : ℕ) + 2 : ℕ) : ℝ) = (((j : ℕ) + 2 : ℕ) : ℝ) := by
    exact Real.strictMonoOn_log.injOn
      (show 0 < (((i : ℕ) + 2 : ℕ) : ℝ) by positivity)
      (show 0 < (((j : ℕ) + 2 : ℕ) : ℝ) by positivity) hij
  exact Nat.add_right_cancel (by exact_mod_cast hcast)

/-- Exact endpoint-consolidated atomic presentation of every finite successor-relative moment. -/
theorem finiteModalSequence_vonMangoldtSuccessorTransportMass
    (M k : ℕ) :
    HTGeometry.finiteModalSequence
        (vonMangoldtSuccessorTransportMass M)
        (vonMangoldtSuccessorTransportNode M) k =
      finiteVonMangoldtSuccessorRelativeMoment M (k + 2) := by
  unfold HTGeometry.finiteModalSequence vonMangoldtSuccessorTransportMass
  unfold finiteVonMangoldtSuccessorRelativeMoment
  unfold vonMangoldtSuccessorRelativeMomentTerm
  unfold vonMangoldtAdditiveLogJetDifference vonMangoldtAdditiveLogJet
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [vonMangoldtSuccessorTransportNode, pow_add]
  apply Finset.sum_congr rfl
  intro p _
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp
  ring_nf

/-- The full principal-relative jet section is exactly its signed atomic moment matrix. -/
theorem finiteVonMangoldtSuccessorPrincipalRelativeMatrix_eq_atomicMomentMatrix
    (M : ℕ) :
    finiteVonMangoldtSuccessorPrincipalRelativeMatrix M (M + 1) =
      HTGeometry.algebraicHankelMatrix
        (HTGeometry.finiteModalSequence
          (vonMangoldtSuccessorTransportMass M)
          (vonMangoldtSuccessorTransportNode M)) (M + 1) := by
  ext i j
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_apply,
    HTGeometry.algebraicHankelMatrix]
  exact (finiteModalSequence_vonMangoldtSuccessorTransportMass
    M ((i : ℕ) + (j : ℕ))).symm

/-- **Exact von Mangoldt successor transport inertia law, negative index.** -/
theorem sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix (M : ℕ) :
    sigNeg
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix
          M (M + 1)).toQuadraticForm' =
      {i | vonMangoldtSuccessorTransportMass M i < 0}.ncard := by
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_eq_atomicMomentMatrix]
  exact HTGeometry.sigNeg_algebraicHankelMatrix_finiteModalSequence
    (vonMangoldtSuccessorTransportNode_injective M)

/-- **Exact von Mangoldt successor transport inertia law, positive index.** -/
theorem sigPos_finiteVonMangoldtSuccessorPrincipalRelativeMatrix (M : ℕ) :
    sigPos
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix
          M (M + 1)).toQuadraticForm' =
      {i | 0 < vonMangoldtSuccessorTransportMass M i}.ncard := by
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_eq_atomicMomentMatrix]
  exact HTGeometry.sigPos_algebraicHankelMatrix_finiteModalSequence
    (vonMangoldtSuccessorTransportNode_injective M)

/-- **Exact von Mangoldt successor transport inertia law, null index.** -/
theorem finrank_radical_finiteVonMangoldtSuccessorPrincipalRelativeMatrix (M : ℕ) :
    Module.finrank ℝ
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix
          M (M + 1)).toQuadraticForm'.radical =
      {i | vonMangoldtSuccessorTransportMass M i = 0}.ncard := by
  rw [finiteVonMangoldtSuccessorPrincipalRelativeMatrix_eq_atomicMomentMatrix]
  exact HTGeometry.finrank_radical_algebraicHankelMatrix_finiteModalSequence
    (vonMangoldtSuccessorTransportNode_injective M)

/-- The left endpoint retains exactly the negative outgoing conductance at `2`. -/
theorem vonMangoldtSuccessorTransportMass_zero
    (M : ℕ) (hM : 0 < M) :
    vonMangoldtSuccessorTransportMass M ⟨0, Nat.zero_lt_succ M⟩ =
      -finiteVonMangoldtRealWeight 2 * Real.log 2 ^ 2 := by
  classical
  let p0 : Fin M := ⟨0, hM⟩
  unfold vonMangoldtSuccessorTransportMass
  rw [Finset.sum_eq_single p0]
  · simp [p0, vonMangoldtSuccessorTransportNode]
  · intro p _ hp
    have hpval : (p : ℕ) ≠ 0 := by
      intro h
      apply hp
      apply Fin.ext
      simpa [p0] using h
    have hcast : Fin.castSucc p ≠ (0 : Fin (M + 1)) := by
      intro h
      apply hpval
      exact congrArg Fin.val h
    simp [hcast]
  · simp

/-- The left endpoint mass is strictly negative at every nonempty aperture. -/
theorem vonMangoldtSuccessorTransportMass_zero_neg
    (M : ℕ) (hM : 0 < M) :
    vonMangoldtSuccessorTransportMass M ⟨0, Nat.zero_lt_succ M⟩ < 0 := by
  rw [vonMangoldtSuccessorTransportMass_zero M hM]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos finiteVonMangoldtRealWeight_two_pos)
    (sq_pos_of_pos (Real.log_pos (by norm_num)))

/-- Every nonempty full-jet successor principal-relative section has a negative direction. -/
theorem sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_pos
    (M : ℕ) (hM : 0 < M) :
    0 < sigNeg
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix
          M (M + 1)).toQuadraticForm' := by
  rw [sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix]
  exact (Set.ncard_pos
    (s := {i | vonMangoldtSuccessorTransportMass M i < 0})).2
      ⟨⟨0, Nat.zero_lt_succ M⟩,
        vonMangoldtSuccessorTransportMass_zero_neg M hM⟩

/-- A prime strictly beyond `3` in the residue class `3 mod 4` cannot have prime-power
predecessor. -/
theorem not_isPrimePow_pred_of_prime_mod_four_eq_three
    {p : ℕ} (hp3 : p % 4 = 3) (hpgt : 3 < p) :
    ¬ IsPrimePow (p - 1) := by
  intro hpow
  rcases (isPrimePow_nat_iff (p - 1)).mp hpow with ⟨q, k, hq, hk, hqk⟩
  have heven : Even (p - 1) :=
    (Nat.even_iff).2 (by omega)
  have hqpowEven : Even (q ^ k) := by
    rw [hqk]
    exact heven
  have hqeven : Even q := ((Nat.even_pow).1 hqpowEven).1
  have hq2 : q = 2 := hq.even_iff.mp hqeven
  have hk_cases : k = 1 ∨ 2 ≤ k := by omega
  rcases hk_cases with rfl | hk2
  · simp [hq2] at hqk
    omega
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hk2
    have hfour : 4 ∣ p - 1 := by
      refine ⟨2 ^ l, ?_⟩
      rw [← hqk, hq2, pow_add]
      ring
    have hmod : (p - 1) % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp hfour
    omega

/-- Interior node mass is incoming conductance minus outgoing conductance. -/
theorem vonMangoldtSuccessorTransportMass_prime_interior
    {p M : ℕ} (hpgt : 3 < p) (hM : p - 1 ≤ M) :
    vonMangoldtSuccessorTransportMass M ⟨p - 2, by omega⟩ =
      (finiteVonMangoldtRealWeight (p - 1) -
          finiteVonMangoldtRealWeight p) * Real.log p ^ 2 := by
  classical
  let i : Fin (M + 1) := ⟨p - 2, by omega⟩
  let qIn : Fin M := ⟨p - 3, by omega⟩
  let qOut : Fin M := ⟨p - 2, by omega⟩
  have hin :
      (∑ q : Fin M,
        if q.succ = i then finiteVonMangoldtRealWeight ((q : ℕ) + 2) else 0) =
        finiteVonMangoldtRealWeight (p - 1) := by
    rw [Finset.sum_eq_single qIn]
    · have h1 : p - 3 + 1 = p - 2 := by omega
      have h2 : p - 3 + 2 = p - 1 := by omega
      simp [qIn, i, h1, h2]
    · intro q _ hq
      have hne : q.succ ≠ i := by
        intro h
        apply hq
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp [qIn, i] at hv ⊢
        omega
      simp [hne]
    · simp
  have hout :
      (∑ q : Fin M,
        if Fin.castSucc q = i then
          finiteVonMangoldtRealWeight ((q : ℕ) + 2) else 0) =
        finiteVonMangoldtRealWeight p := by
    rw [Finset.sum_eq_single qOut]
    · have h2 : p - 2 + 2 = p := by omega
      simp [qOut, i, h2]
    · intro q _ hq
      have hne : Fin.castSucc q ≠ i := by
        intro h
        apply hq
        apply Fin.ext
        have hv := congrArg Fin.val h
        simp [qOut, i] at hv ⊢
        omega
      simp [hne]
    · simp
  change vonMangoldtSuccessorTransportMass M i = _
  unfold vonMangoldtSuccessorTransportMass
  rw [Finset.sum_sub_distrib, hin, hout]
  have h2 : p - 2 + 2 = p := by omega
  simp [vonMangoldtSuccessorTransportNode, i, h2]

/-- Every sufficiently large prime `3 mod 4` forces another negative transport mass. -/
theorem vonMangoldtSuccessorTransportMass_prime_mod_four_three_neg
    {p M : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3)
    (hpgt : 3 < p) (hM : p - 1 ≤ M) :
    vonMangoldtSuccessorTransportMass M ⟨p - 2, by omega⟩ < 0 := by
  rw [vonMangoldtSuccessorTransportMass_prime_interior hpgt hM]
  have hpred :
      finiteVonMangoldtRealWeight (p - 1) = 0 := by
    rw [finiteVonMangoldtRealWeight,
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
        (not_isPrimePow_pred_of_prime_mod_four_eq_three hp3 hpgt)]
    simp
  have hpweight : 0 < finiteVonMangoldtRealWeight p := by
    rw [finiteVonMangoldtRealWeight]
    exact div_pos
      (ArithmeticFunction.vonMangoldt_pos_iff.mpr hp.isPrimePow)
      (by positivity)
  rw [hpred, zero_sub]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hpweight)
    (sq_pos_of_pos (Real.log_pos (by exact_mod_cast hp.one_lt)))

/-- **Unbounded negative-index law.** Full-jet successor principal-relative sections have
arbitrarily large negative index. -/
theorem sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix_unbounded
    (K : ℕ) :
    ∃ M, K < sigNeg
        (finiteVonMangoldtSuccessorPrincipalRelativeMatrix
          M (M + 1)).toQuadraticForm' := by
  let A : Set ℕ := {p | p.Prime ∧ p ≡ 3 [MOD 4]}
  have hA : A.Infinite := by
    exact Nat.infinite_setOf_prime_and_modEq
      (q := 4) (a := 3) (by norm_num) (by norm_num)
  have hAlarge : (A \ Set.Iic 3).Infinite :=
    hA.diff (Set.finite_Iic 3)
  obtain ⟨S, hSA, hScard⟩ :=
    hAlarge.exists_subset_card_eq (K + 1)
  let M : ℕ := S.sum id
  have hprop {p : ℕ} (hpS : p ∈ S) :
      p.Prime ∧ p % 4 = 3 ∧ 3 < p := by
    have hp := hSA hpS
    change (p.Prime ∧ p ≡ 3 [MOD 4]) ∧ p ∉ Set.Iic 3 at hp
    exact ⟨hp.1.1, by simpa [Nat.ModEq] using hp.1.2, by simpa using hp.2⟩
  have hleM {p : ℕ} (hpS : p ∈ S) : p ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun q _ => Nat.zero_le q) hpS
  let f : ↥S → Fin (M + 1) := fun p =>
    ⟨(p : ℕ) - 2, by
      have hpM := hleM p.property
      omega⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    have hv := congrArg Fin.val hpq
    change (p : ℕ) - 2 = (q : ℕ) - 2 at hv
    have hpgt := (hprop p.property).2.2
    have hqgt := (hprop q.property).2.2
    omega
  let I : Finset (Fin (M + 1)) := S.attach.image f
  have hIcard : I.card = S.card := by
    dsimp [I]
    rw [Finset.card_image_of_injective _ hf]
    simp
  have hIneg :
      (↑I : Set (Fin (M + 1))) ⊆
        {i | vonMangoldtSuccessorTransportMass M i < 0} := by
    intro i hi
    change i ∈ I at hi
    rcases Finset.mem_image.mp hi with ⟨p, _, rfl⟩
    have hp := hprop p.property
    exact vonMangoldtSuccessorTransportMass_prime_mod_four_three_neg
      hp.1 hp.2.1 hp.2.2 (by
        have hpM := hleM p.property
        omega)
  refine ⟨M, ?_⟩
  rw [sigNeg_finiteVonMangoldtSuccessorPrincipalRelativeMatrix]
  calc
    K < K + 1 := Nat.lt_succ_self K
    _ = S.card := hScard.symm
    _ = I.card := hIcard.symm
    _ = (↑I : Set (Fin (M + 1))).ncard := by simp
    _ ≤ {i | vonMangoldtSuccessorTransportMass M i < 0}.ncard :=
      Set.ncard_le_ncard hIneg

end

end RHTower
