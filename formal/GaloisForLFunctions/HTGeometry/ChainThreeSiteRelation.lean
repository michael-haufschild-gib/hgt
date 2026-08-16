import GaloisForLFunctions.HTGeometry.ThreeSiteLabelProduct

/-!
# The three-site relation of two commuting chain shell operators

Pairing the commutator of two open-chain two-local operators against a Pauli string supported on
three consecutive sites leaves only the two consecutive edges covering those sites, and the
resulting scalar equation says that the two cross products of the corresponding coupling rows and
columns agree.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {m : ℕ}

/-- The coefficient family of the one-site part. -/
def chainSiteCoeff (h : Fin (m + 1) → Fin 3 → ℝ) : Fin (m + 1) × Fin 3 → ℂ :=
  fun p => ((h p.1 p.2 : ℝ) : ℂ)

/-- The coefficient family of the two-site part. -/
def chainEdgeCoeff (J : Fin m → Fin 3 → Fin 3 → ℝ) : Fin m × Fin 3 × Fin 3 → ℂ :=
  fun q => ((J q.1 q.2.1 q.2.2 : ℝ) : ℂ)

theorem chainSiteOp_eq (h : Fin (m + 1) → Fin 3 → ℝ) :
    chainSiteOp h = ∑ p, chainSiteCoeff h p • finitePauliMatrix (chainSiteLabel p) := rfl

theorem chainEdgeOp_eq (J : Fin m → Fin 3 → Fin 3 → ℝ) :
    chainEdgeOp J = ∑ q, chainEdgeCoeff J q • finitePauliMatrix (chainEdgeLabel q) := rfl

section Sites

variable {p q : Fin m}

theorem castSucc_eq_succ_of_consecutive (hq : (q : ℕ) = (p : ℕ) + 1) :
    (q.castSucc : Fin (m + 1)) = p.succ := by
  refine Fin.ext ?_
  rw [Fin.val_castSucc, Fin.val_succ, hq]

theorem chain_ne_left_mid (p : Fin m) : (p.castSucc : Fin (m + 1)) ≠ p.succ :=
  castSucc_ne_succ p

theorem chain_ne_mid_right (hq : (q : ℕ) = (p : ℕ) + 1) :
    (p.succ : Fin (m + 1)) ≠ q.succ := by
  rw [Ne, Fin.ext_iff, Fin.val_succ, Fin.val_succ, hq]
  omega

theorem chain_ne_left_right (hq : (q : ℕ) = (p : ℕ) + 1) :
    (p.castSucc : Fin (m + 1)) ≠ q.succ := by
  rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, hq]
  omega

theorem ne_of_consecutive (hq : (q : ℕ) = (p : ℕ) + 1) : p ≠ q := by
  intro hc
  rw [hc] at hq
  omega

theorem chainSites_union_eq_labelSupport (hq : (q : ℕ) = (p : ℕ) + 1) (a f e : Fin 3) :
    chainSites p ∪ chainSites q =
      labelSupport (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) := by
  classical
  rw [labelSupport_tripleLabel (chain_ne_left_mid p) (chain_ne_mid_right hq)
    (chain_ne_left_right hq), chainSites, chainSites, castSucc_eq_succ_of_consecutive hq]
  ext s
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

end Sites

/-- Only the two consecutive edges covering a three-site string contribute to the commutator. -/
theorem pairCoeff2_chainEdge_eq_zero {p q i j : Fin m} (hq : (q : ℕ) = (p : ℕ) + 1)
    (a f e : Fin 3) (hij : ¬ ((i = p ∧ j = q) ∨ (i = q ∧ j = p)))
    (hc hk : Fin m × Fin 3 × Fin 3 → ℂ) (u1 u2 : Fin 3 × Fin 3) :
    pairCoeff2 chainEdgeLabel chainEdgeLabel hc hk
      (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) (i, u1) (j, u2) = 0 := by
  classical
  refine pairCoeff2_eq_zero_of_card _ _ _ _ _
    (card_labelSupport_tripleLabel (chain_ne_left_mid p) (chain_ne_mid_right hq)
      (chain_ne_left_right hq) a f e)
    (le_of_eq (card_labelSupport_chainEdgeLabel _))
    (le_of_eq (card_labelSupport_chainEdgeLabel _)) ?_
  rintro ⟨-, -, hint, hunion⟩
  simp only [labelSupport_chainEdgeLabel] at hint hunion
  rw [← chainSites_union_eq_labelSupport hq a f e] at hunion
  refine hij ?_
  rcases consecutive_of_card_inter_eq_one hint with hji | hij'
  · have hip : i = p := eq_of_chainSites_union hji hq hunion
    have hval : (i : ℕ) = (p : ℕ) := congrArg Fin.val hip
    have h2 : (j : ℕ) = (q : ℕ) := by omega
    exact Or.inl ⟨hip, Fin.eq_of_val_eq h2⟩
  · rw [Finset.union_comm] at hunion
    have hjp : j = p := eq_of_chainSites_union hij' hq hunion
    have hval : (j : ℕ) = (p : ℕ) := congrArg Fin.val hjp
    have h2 : (i : ℕ) = (q : ℕ) := by omega
    exact Or.inr ⟨Fin.eq_of_val_eq h2, hjp⟩


/-- The commutator coefficient of a pair of two-site terms. -/
def chainPairTerm (J K : Fin m → Fin 3 → Fin 3 → ℝ) (R : Fin (m + 1) → Option (Fin 3))
    (q1 q2 : Fin m × Fin 3 × Fin 3) : ℂ :=
  pairCoeff2 chainEdgeLabel chainEdgeLabel (chainEdgeCoeff J) (chainEdgeCoeff K) R q1 q2

/-- The total commutator coefficient of a pair of edges. -/
def chainBlock (J K : Fin m → Fin 3 → Fin 3 → ℝ) (R : Fin (m + 1) → Option (Fin 3))
    (i j : Fin m) : ℂ :=
  ∑ u1 : Fin 3 × Fin 3, ∑ u2 : Fin 3 × Fin 3, chainPairTerm J K R (i, u1) (j, u2)

/-- **The commutator equation at a three-site string involves only the two-site part.** -/
theorem sum_chainPairTerm_eq_zero (h1 h2 : Fin (m + 1) → Fin 3 → ℝ)
    (J K : Fin m → Fin 3 → Fin 3 → ℝ)
    (hcomm : (chainSiteOp h1 + chainEdgeOp J) * (chainSiteOp h2 + chainEdgeOp K) =
      (chainSiteOp h2 + chainEdgeOp K) * (chainSiteOp h1 + chainEdgeOp J))
    (R : Fin (m + 1) → Option (Fin 3)) (hR : (labelSupport R).card = 3) :
    (∑ q1, ∑ q2, chainPairTerm J K R q1 q2) = 0 := by
  classical
  have hzero : (chainSiteOp h1 + chainEdgeOp J) * (chainSiteOp h2 + chainEdgeOp K) -
      (chainSiteOp h2 + chainEdgeOp K) * (chainSiteOp h1 + chainEdgeOp J) = 0 :=
    sub_eq_zero_of_eq hcomm
  have hexp : (chainSiteOp h1 + chainEdgeOp J) * (chainSiteOp h2 + chainEdgeOp K) -
      (chainSiteOp h2 + chainEdgeOp K) * (chainSiteOp h1 + chainEdgeOp J) =
      (chainSiteOp h1 * chainSiteOp h2 - chainSiteOp h2 * chainSiteOp h1) +
      (chainSiteOp h1 * chainEdgeOp K - chainEdgeOp K * chainSiteOp h1) +
      (chainEdgeOp J * chainSiteOp h2 - chainSiteOp h2 * chainEdgeOp J) +
      (chainEdgeOp J * chainEdgeOp K - chainEdgeOp K * chainEdgeOp J) := by
    noncomm_ring
  have htr : Matrix.trace (finitePauliMatrix R *
      ((chainSiteOp h1 * chainSiteOp h2 - chainSiteOp h2 * chainSiteOp h1) +
      (chainSiteOp h1 * chainEdgeOp K - chainEdgeOp K * chainSiteOp h1) +
      (chainEdgeOp J * chainSiteOp h2 - chainSiteOp h2 * chainEdgeOp J) +
      (chainEdgeOp J * chainEdgeOp K - chainEdgeOp K * chainEdgeOp J))) = 0 := by
    rw [← hexp, hzero, Matrix.mul_zero, Matrix.trace_zero]
  rw [Matrix.mul_add, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, chainSiteOp_eq h1, chainSiteOp_eq h2, chainEdgeOp_eq J, chainEdgeOp_eq K,
    trace_commutator_eq_smul_sum, trace_commutator_eq_smul_sum, trace_commutator_eq_smul_sum,
    trace_commutator_eq_smul_sum] at htr
  have hs1 : (∑ i, ∑ j, pairCoeff2 chainSiteLabel chainSiteLabel (chainSiteCoeff h1)
      (chainSiteCoeff h2) R i j) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      pairCoeff2_eq_zero_of_left_card_one _ _ _ _ _ hR (card_labelSupport_chainSiteLabel i)
        (by rw [card_labelSupport_chainSiteLabel]; omega)
  have hs2 : (∑ i, ∑ j, pairCoeff2 chainSiteLabel chainEdgeLabel (chainSiteCoeff h1)
      (chainEdgeCoeff K) R i j) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      pairCoeff2_eq_zero_of_left_card_one _ _ _ _ _ hR (card_labelSupport_chainSiteLabel i)
        (le_of_eq (card_labelSupport_chainEdgeLabel j))
  have hs3 : (∑ i, ∑ j, pairCoeff2 chainEdgeLabel chainSiteLabel (chainEdgeCoeff J)
      (chainSiteCoeff h2) R i j) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      pairCoeff2_eq_zero_of_right_card_one _ _ _ _ _ hR
        (le_of_eq (card_labelSupport_chainEdgeLabel i)) (card_labelSupport_chainSiteLabel j)
  rw [hs1, hs2, hs3] at htr
  simp only [mul_zero, add_zero, zero_add] at htr
  exact (mul_eq_zero.mp htr).resolve_left (pow_ne_zero _ two_ne_zero)

theorem sum_chainBlock_eq_zero (h1 h2 : Fin (m + 1) → Fin 3 → ℝ)
    (J K : Fin m → Fin 3 → Fin 3 → ℝ)
    (hcomm : (chainSiteOp h1 + chainEdgeOp J) * (chainSiteOp h2 + chainEdgeOp K) =
      (chainSiteOp h2 + chainEdgeOp K) * (chainSiteOp h1 + chainEdgeOp J))
    (R : Fin (m + 1) → Option (Fin 3)) (hR : (labelSupport R).card = 3) :
    (∑ i, ∑ j, chainBlock J K R i j) = 0 := by
  classical
  have h := sum_chainPairTerm_eq_zero h1 h2 J K hcomm R hR
  rw [Fintype.sum_prod_type (fun q1 => ∑ q2, chainPairTerm J K R q1 q2)] at h
  rw [show (∑ i, ∑ u1 : Fin 3 × Fin 3, ∑ q2, chainPairTerm J K R (i, u1) q2) =
      ∑ i, ∑ u1 : Fin 3 × Fin 3, ∑ j, ∑ u2 : Fin 3 × Fin 3,
        chainPairTerm J K R (i, u1) (j, u2) from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun u1 _ =>
      Fintype.sum_prod_type (fun q2 => chainPairTerm J K R (i, u1) q2)] at h
  rw [show (∑ i, ∑ u1 : Fin 3 × Fin 3, ∑ j, ∑ u2 : Fin 3 × Fin 3,
        chainPairTerm J K R (i, u1) (j, u2)) = ∑ i, ∑ j, chainBlock J K R i j from
    Finset.sum_congr rfl fun i _ => Finset.sum_comm] at h
  exact h


theorem sum_four_ite (a e : Fin 3) (W : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    (∑ a' : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, ∑ e' : Fin 3,
      (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) * W a' b d e'))
      = ∑ b : Fin 3, ∑ d : Fin 3, W a b d e := by
  classical
  have hinner : ∀ a' b d : Fin 3, (∑ e' : Fin 3,
      (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) * W a' b d e')) =
      (if a' = a then (1 : ℂ) else 0) * W a' b d e := by
    intro a' b d
    rw [← Finset.mul_sum]
    congr 1
    simp
  simp only [hinner]
  have houter : ∀ a' : Fin 3, (∑ b : Fin 3, ∑ d : Fin 3,
      (if a' = a then (1 : ℂ) else 0) * W a' b d e) =
      (if a' = a then (1 : ℂ) else 0) * ∑ b : Fin 3, ∑ d : Fin 3, W a' b d e := by
    intro a'
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
  simp only [houter]
  simp

theorem sum_four_ite_rev (a e : Fin 3) (W : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) :
    (∑ d : Fin 3, ∑ e' : Fin 3, ∑ a' : Fin 3, ∑ b : Fin 3,
      (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) * W a' b d e'))
      = ∑ d : Fin 3, ∑ b : Fin 3, W a b d e := by
  classical
  refine Finset.sum_congr rfl fun d _ => ?_
  have hb : ∀ e' a' : Fin 3, (∑ b : Fin 3,
      (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) * W a' b d e')) =
      (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) *
        ∑ b : Fin 3, W a' b d e') := by
    intro e' a'
    rw [Finset.mul_sum, Finset.mul_sum]
  simp only [hb]
  have ha : ∀ e' : Fin 3, (∑ a' : Fin 3, (if a' = a then (1 : ℂ) else 0) *
      ((if e' = e then (1 : ℂ) else 0) * ∑ b : Fin 3, W a' b d e')) =
      (if e' = e then (1 : ℂ) else 0) * ∑ b : Fin 3, W a b d e' := by
    intro e'
    simp
  simp only [ha]
  simp

section Blocks

variable {p q : Fin m}

/-- **The commutator coefficient of the two consecutive edges.** -/
theorem chainBlock_consecutive (J K : Fin m → Fin 3 → Fin 3 → ℝ)
    (hq : (q : ℕ) = (p : ℕ) + 1) (a e f : Fin 3) :
    chainBlock J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) p q =
      2 * Complex.I * ((crossProduct (fun b => J p a b) (fun d => K q d e) f : ℝ) : ℂ) := by
  classical
  have hvw := chain_ne_left_mid p
  have hwx := chain_ne_mid_right hq
  have hvx := chain_ne_left_right hq
  have hind : ∀ a' b d e' : Fin 3,
      (if tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e =
          optMulLabel (pairLabel (p.castSucc : Fin (m + 1)) p.succ a' b)
            (pairLabel (p.succ : Fin (m + 1)) q.succ d e') then (1 : ℂ) else 0) =
      (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) *
        (if some f = optMul (some b) (some d) then (1 : ℂ) else 0)) := by
    intro a' b d e'
    by_cases h1 : a' = a <;> by_cases h2 : e' = e <;>
      by_cases h3 : (some f : Option (Fin 3)) = optMul (some b) (some d) <;>
      simp [tripleLabel_eq_optMulLabel_iff hvw hwx hvx, h1, h2, h3]
  have hterm : ∀ a' b d e' : Fin 3,
      chainPairTerm J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e)
          (p, a', b) (q, d, e') =
        (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) *
          (((J p a' b : ℝ) : ℂ) * ((K q d e' : ℝ) : ℂ) * (pauliComm b d *
            (if some f = optMul (some b) (some d) then (1 : ℂ) else 0)))) := by
    intro a' b d e'
    simp only [chainPairTerm, pairCoeff2, chainEdgeCoeff, chainEdgeLabel, pauliComm,
      castSucc_eq_succ_of_consecutive hq, optPhaseProd_pairLabel hvw hwx hvx,
      optPhaseProd_pairLabel_rev hvw hwx hvx, hind]
    ring
  have hexpand : chainBlock J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) p q =
      ∑ a' : Fin 3, ∑ b : Fin 3, ∑ d : Fin 3, ∑ e' : Fin 3,
        chainPairTerm J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e)
          (p, a', b) (q, d, e') := by
    rw [chainBlock, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun b _ =>
      Fintype.sum_prod_type _
  rw [hexpand]
  simp only [hterm]
  rw [sum_four_ite a e fun a' b d e' => ((J p a' b : ℝ) : ℂ) * ((K q d e' : ℝ) : ℂ) *
    (pauliComm b d * (if some f = optMul (some b) (some d) then (1 : ℂ) else 0))]
  exact sum_pauliComm_eq_cross (fun b => J p a b) (fun d => K q d e) f

/-- The commutator coefficient of the two consecutive edges in the opposite order. -/
theorem chainBlock_consecutive_rev (J K : Fin m → Fin 3 → Fin 3 → ℝ)
    (hq : (q : ℕ) = (p : ℕ) + 1) (a e f : Fin 3) :
    chainBlock J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) q p =
      -(2 * Complex.I * ((crossProduct (fun b => K p a b) (fun d => J q d e) f : ℝ) : ℂ)) := by
  classical
  have hvw := chain_ne_left_mid p
  have hwx := chain_ne_mid_right hq
  have hvx := chain_ne_left_right hq
  have hind : ∀ a' b d e' : Fin 3,
      (if tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e =
          optMulLabel (pairLabel (p.succ : Fin (m + 1)) q.succ d e')
            (pairLabel (p.castSucc : Fin (m + 1)) p.succ a' b) then (1 : ℂ) else 0) =
      (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) *
        (if some f = optMul (some b) (some d) then (1 : ℂ) else 0)) := by
    intro a' b d e'
    by_cases h1 : a' = a <;> by_cases h2 : e' = e <;>
      by_cases h3 : (some f : Option (Fin 3)) = optMul (some b) (some d) <;>
      simp [tripleLabel_eq_optMulLabel_rev_iff hvw hwx hvx, h1, h2, h3]
  have hterm : ∀ a' b d e' : Fin 3,
      chainPairTerm J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e)
          (q, d, e') (p, a', b) =
        (if a' = a then (1 : ℂ) else 0) * ((if e' = e then (1 : ℂ) else 0) *
          (-(((K p a' b : ℝ) : ℂ) * ((J q d e' : ℝ) : ℂ) * (pauliComm b d *
            (if some f = optMul (some b) (some d) then (1 : ℂ) else 0))))) := by
    intro a' b d e'
    simp only [chainPairTerm, pairCoeff2, chainEdgeCoeff, chainEdgeLabel, pauliComm,
      castSucc_eq_succ_of_consecutive hq, optPhaseProd_pairLabel hvw hwx hvx,
      optPhaseProd_pairLabel_rev hvw hwx hvx, hind]
    ring
  have hexpand : chainBlock J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) q p =
      ∑ d : Fin 3, ∑ e' : Fin 3, ∑ a' : Fin 3, ∑ b : Fin 3,
        chainPairTerm J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e)
          (q, d, e') (p, a', b) := by
    rw [chainBlock, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e' _ =>
      Fintype.sum_prod_type _
  rw [hexpand]
  simp only [hterm]
  rw [sum_four_ite_rev a e fun a' b d e' => -(((K p a' b : ℝ) : ℂ) * ((J q d e' : ℝ) : ℂ) *
    (pauliComm b d * (if some f = optMul (some b) (some d) then (1 : ℂ) else 0)))]
  have hneg : (∑ d : Fin 3, ∑ b : Fin 3, -(((K p a b : ℝ) : ℂ) * ((J q d e : ℝ) : ℂ) *
      (pauliComm b d * (if some f = optMul (some b) (some d) then (1 : ℂ) else 0)))) =
      -(∑ b : Fin 3, ∑ d : Fin 3, (((K p a b : ℝ) : ℂ) * ((J q d e : ℝ) : ℂ)) *
        (pauliComm b d * (if some f = optMul (some b) (some d) then (1 : ℂ) else 0))) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_neg_distrib]
  rw [hneg, sum_pauliComm_eq_cross (fun b => K p a b) (fun d => J q d e) f]


/-- **The three-site relation of two commuting open-chain two-local operators.**

If two two-local operators on an open chain commute, then for every pair of consecutive edges the
cross product of a coupling row of the first with a coupling column of the second agrees with the
cross product of the corresponding row and column with the roles exchanged. -/
theorem crossProduct_chain_eq (h1 h2 : Fin (m + 1) → Fin 3 → ℝ)
    (J K : Fin m → Fin 3 → Fin 3 → ℝ)
    (hcomm : (chainSiteOp h1 + chainEdgeOp J) * (chainSiteOp h2 + chainEdgeOp K) =
      (chainSiteOp h2 + chainEdgeOp K) * (chainSiteOp h1 + chainEdgeOp J))
    (hq : (q : ℕ) = (p : ℕ) + 1) (a e f : Fin 3) :
    crossProduct (fun b => J p a b) (fun d => K q d e) f =
      crossProduct (fun b => K p a b) (fun d => J q d e) f := by
  classical
  have hvw := chain_ne_left_mid p
  have hwx := chain_ne_mid_right hq
  have hvx := chain_ne_left_right hq
  have hpq := ne_of_consecutive hq
  have htot := sum_chainBlock_eq_zero h1 h2 J K hcomm
    (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e)
    (card_labelSupport_tripleLabel hvw hwx hvx a f e)
  have hblk0 : ∀ i j : Fin m, ¬ ((i = p ∧ j = q) ∨ (i = q ∧ j = p)) →
      chainBlock J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) i j = 0 := by
    intro i j hij
    exact Finset.sum_eq_zero fun u1 _ => Finset.sum_eq_zero fun u2 _ =>
      pairCoeff2_chainEdge_eq_zero hq a f e hij _ _ u1 u2
  have hrowp : (∑ j, chainBlock J K
      (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) p j) =
      chainBlock J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) p q :=
    Finset.sum_eq_single q (fun j _ hj => hblk0 p j (fun hc => by
      rcases hc with ⟨-, h2'⟩ | ⟨h1', -⟩
      · exact hj h2'
      · exact hpq h1')) (fun hc => absurd (Finset.mem_univ q) hc)
  have hrowq : (∑ j, chainBlock J K
      (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) q j) =
      chainBlock J K (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) q p :=
    Finset.sum_eq_single p (fun j _ hj => hblk0 q j (fun hc => by
      rcases hc with ⟨h1', -⟩ | ⟨-, h2'⟩
      · exact hpq h1'.symm
      · exact hj h2')) (fun hc => absurd (Finset.mem_univ p) hc)
  have hrow0 : ∀ i : Fin m, i ≠ p → i ≠ q → (∑ j, chainBlock J K
      (tripleLabel (p.castSucc : Fin (m + 1)) p.succ q.succ a f e) i j) = 0 :=
    fun i hip hiq => Finset.sum_eq_zero fun j _ => hblk0 i j (fun hc => by
      rcases hc with ⟨h1', -⟩ | ⟨h1', -⟩
      · exact hip h1'
      · exact hiq h1')
  rw [Finset.sum_eq_add_of_mem p q (Finset.mem_univ p) (Finset.mem_univ q) hpq
    (fun c _ hc => hrow0 c hc.1 hc.2), hrowp, hrowq, chainBlock_consecutive J K hq a e f,
    chainBlock_consecutive_rev J K hq a e f, ← sub_eq_add_neg, sub_eq_zero] at htot
  exact Complex.ofReal_inj.mp
    (mul_left_cancel₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero) htot)

end Blocks

end GaloisForLFunctions.HTGeometry
