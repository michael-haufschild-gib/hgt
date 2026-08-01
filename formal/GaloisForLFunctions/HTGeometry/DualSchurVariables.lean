import GaloisForLFunctions.HTGeometry.SchurVariablePresentation

/-!
# The dual family of coefficients

The elementary symmetric coefficients are determined by the complete homogeneous ones through the
alternating convolution identity, which expresses each in terms of the earlier ones together with the
coefficient of its own index.

So the passage between the two families is triangular, and in particular each dual coefficient
involves only the coefficients of index at most its own.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K]

/-- The dual coefficients, defined by the alternating convolution. -/
noncomputable def dualVar (K : Type*) [Field K] (L : ℕ) : ℕ → MvPolynomial (Fin L) K
  | 0 => 1
  | (k + 1) =>
      ∑ i ∈ Finset.range (k + 1),
        (-1 : MvPolynomial (Fin L) K) ^ i * schurVar K L (i + 1) * dualVar K L (k - i)

theorem dualVar_zero {L : ℕ} : dualVar K L 0 = 1 := by
  rw [dualVar]

theorem dualVar_succ {L k : ℕ} :
    dualVar K L (k + 1) =
      ∑ i ∈ Finset.range (k + 1),
        (-1 : MvPolynomial (Fin L) K) ^ i * schurVar K L (i + 1) * dualVar K L (k - i) := by
  rw [dualVar]

/-- **Each dual coefficient involves only the coefficients of index at most its own.** -/
theorem degreeOf_dualVar {L : ℕ} (v : Fin L) :
    ∀ j : ℕ, j < L - (v : ℕ) → MvPolynomial.degreeOf v (dualVar K L j) = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j with
    | 0 =>
        intro _
        rw [dualVar_zero, MvPolynomial.degreeOf_one]
    | (k + 1) =>
        intro hk
        rw [dualVar_succ]
        refine Nat.le_zero.1 ?_
        refine le_trans (MvPolynomial.degreeOf_sum_le v _ _) ?_
        refine Finset.sup_le fun i hi => ?_
        rw [Finset.mem_range] at hi
        refine le_trans (MvPolynomial.degreeOf_mul_le v _ _) ?_
        have hterm : MvPolynomial.degreeOf v
            ((-1 : MvPolynomial (Fin L) K) ^ i * schurVar K L (i + 1)) = 0 := by
          refine Nat.le_zero.1 ?_
          refine le_trans (MvPolynomial.degreeOf_mul_le v _ _) ?_
          have hneg : MvPolynomial.degreeOf v ((-1 : MvPolynomial (Fin L) K) ^ i) = 0 := by
            rw [show ((-1 : MvPolynomial (Fin L) K)) = MvPolynomial.C (-1 : K) by simp,
              ← map_pow, MvPolynomial.degreeOf_C]
          have hvar : MvPolynomial.degreeOf v (schurVar K L (i + 1)) = 0 := by
            rw [schurVar, if_neg (by omega)]
            by_cases hlt : L - (i + 1) < L
            · refine (dif_pos hlt) ▸ MvPolynomial.degreeOf_X_of_ne ?_
              intro hcon
              rw [Fin.ext_iff] at hcon
              have hv := v.isLt
              simp only [] at hcon
              omega
            · rw [dif_neg hlt, MvPolynomial.degreeOf_zero]
          rw [hneg, hvar]
        rw [hterm, ih (k - i) (by omega) (by omega)]

/-! ## The convolution identity -/

theorem dualVar_succ_reflect {L k : ℕ} :
    dualVar K L (k + 1) =
      (-1 : MvPolynomial (Fin L) K) ^ k *
        ∑ i ∈ Finset.range (k + 1),
          (-1 : MvPolynomial (Fin L) K) ^ i * dualVar K L i * schurVar K L (k + 1 - i) := by
  rw [dualVar_succ, Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show k + 1 - 1 - i = k - i from by omega, show k - (k - i) = i from by omega,
    show k - i + 1 = k + 1 - i from by omega]
  have hsign : (-1 : MvPolynomial (Fin L) K) ^ k * (-1 : MvPolynomial (Fin L) K) ^ i =
      (-1 : MvPolynomial (Fin L) K) ^ (k - i) := by
    rw [← pow_add, show k + i = (k - i) + 2 * i from by omega, pow_add, pow_mul, neg_one_sq,
      one_pow, mul_one]
  rw [← hsign]
  ring

/-- **The alternating convolution of the two families vanishes above degree zero.** -/
theorem sum_dualVar_schurVar {L k : ℕ} :
    ∑ i ∈ Finset.range (k + 2),
      (-1 : MvPolynomial (Fin L) K) ^ i * dualVar K L i * schurVar K L (k + 1 - i) = 0 := by
  rw [Finset.sum_range_succ]
  have hlast : (-1 : MvPolynomial (Fin L) K) ^ (k + 1) * dualVar K L (k + 1) *
      schurVar K L (k + 1 - (k + 1)) =
      (-1 : MvPolynomial (Fin L) K) ^ (k + 1) * dualVar K L (k + 1) := by
    rw [show k + 1 - (k + 1) = 0 from by omega, schurVar, if_pos rfl, mul_one]
  have hsign : (-1 : MvPolynomial (Fin L) K) ^ (k + 1) *
      (-1 : MvPolynomial (Fin L) K) ^ k = -1 := by
    rw [← pow_add, show k + 1 + k = 2 * k + 1 from by omega, pow_add, pow_mul, neg_one_sq,
      one_pow, one_mul, pow_one]
  rw [hlast, dualVar_succ_reflect, ← mul_assoc, hsign]
  ring

/-- **The convolution solved for the complete homogeneous coefficient.**  Each coefficient is the
alternating convolution of the dual family with the earlier coefficients — the same shape as the
definition of the dual family, with the two families exchanged. -/
theorem schurVar_succ_eq_sum {L k : ℕ} :
    schurVar K L (k + 1) =
      ∑ i ∈ Finset.range (k + 1),
        (-1 : MvPolynomial (Fin L) K) ^ i * dualVar K L (i + 1) * schurVar K L (k - i) := by
  have h := sum_dualVar_schurVar (K := K) (L := L) (k := k)
  rw [Finset.sum_range_succ'] at h
  have hzero : (-1 : MvPolynomial (Fin L) K) ^ 0 * dualVar K L 0 * schurVar K L (k + 1 - 0) =
      schurVar K L (k + 1) := by
    rw [dualVar_zero, pow_zero, one_mul, one_mul, show k + 1 - 0 = k + 1 from rfl]
  rw [hzero] at h
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (-1 : MvPolynomial (Fin L) K) ^ (i + 1) * dualVar K L (i + 1) *
          schurVar K L (k + 1 - (i + 1)) =
        -((-1 : MvPolynomial (Fin L) K) ^ i * dualVar K L (i + 1) * schurVar K L (k - i)) := by
    intro i _
    rw [show k + 1 - (i + 1) = k - i from by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib] at h
  linear_combination h

/-! ## The substitution exchanging the two families -/

/-- Sending each coefficient to the corresponding dual one. -/
noncomputable def dualSub (K : Type*) [Field K] (L : ℕ) :
    MvPolynomial (Fin L) K →ₐ[K] MvPolynomial (Fin L) K :=
  MvPolynomial.aeval (fun v : Fin L => dualVar K L (L - (v : ℕ)))

theorem dualSub_schurVar {L k : ℕ} (hk : k ≤ L) :
    dualSub K L (schurVar K L k) = dualVar K L k := by
  rw [schurVar]
  by_cases h0 : k = 0
  · rw [if_pos h0, h0, map_one, dualVar_zero]
  · rw [if_neg h0]
    by_cases hlt : L - k < L
    · rw [dif_pos hlt, dualSub, MvPolynomial.aeval_X]
      congr 1
      show L - (L - k) = k
      omega
    · rw [dif_neg hlt, map_zero]
      omega

/-- **The substitution is an involution on the coefficients.**  Applying it twice returns each
coefficient, because the two families satisfy the same recursion with their roles exchanged. -/
theorem dualSub_dualVar {L : ℕ} :
    ∀ k : ℕ, k ≤ L → dualSub K L (dualVar K L k) = schurVar K L k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 =>
        intro _
        rw [dualVar_zero, map_one, schurVar, if_pos rfl]
    | (j + 1) =>
        intro hj
        rw [dualVar_succ, map_sum, schurVar_succ_eq_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [map_mul, map_mul, map_pow, map_neg, map_one,
          dualSub_schurVar (by omega : i + 1 ≤ L), ih (j - i) (by omega) (by omega)]

/-- **The substitution squares to the identity.** -/
theorem dualSub_comp_dualSub {L : ℕ} :
    (dualSub K L).comp (dualSub K L) = AlgHom.id K (MvPolynomial (Fin L) K) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  have hv := v.isLt
  rw [AlgHom.comp_apply, dualSub, MvPolynomial.aeval_X]
  show dualSub K L (dualVar K L (L - (v : ℕ))) = _
  rw [dualSub_dualVar (L - (v : ℕ)) (by omega), schurVar, if_neg (by omega),
    dif_pos (by omega : L - (L - (v : ℕ)) < L)]
  show MvPolynomial.X (⟨L - (L - (v : ℕ)), _⟩ : Fin L) = MvPolynomial.X v
  congr 1
  refine Fin.ext ?_
  show L - (L - (v : ℕ)) = (v : ℕ)
  omega

/-- **The substitution is an automorphism.** -/
noncomputable def dualEquiv (K : Type*) [Field K] (L : ℕ) :
    MvPolynomial (Fin L) K ≃ₐ[K] MvPolynomial (Fin L) K :=
  AlgEquiv.ofAlgHom (dualSub K L) (dualSub K L) dualSub_comp_dualSub dualSub_comp_dualSub

theorem dualEquiv_apply {L : ℕ} (p : MvPolynomial (Fin L) K) :
    dualEquiv K L p = dualSub K L p := rfl

/-- **Irreducibility is preserved by the exchange of the two families.** -/
theorem irreducible_dualSub_iff {L : ℕ} (p : MvPolynomial (Fin L) K) :
    Irreducible (dualSub K L p) ↔ Irreducible p := by
  have h : dualSub K L p = dualEquiv K L p := rfl
  rw [h]
  exact MulEquiv.irreducible_iff (dualEquiv K L).toMulEquiv

end GaloisForLFunctions.HTGeometry
