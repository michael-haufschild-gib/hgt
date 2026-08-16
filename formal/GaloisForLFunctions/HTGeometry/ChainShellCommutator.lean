import GaloisForLFunctions.HTGeometry.ChainEdgeStructure

/-!
# The open-chain two-local shell and its commutator coefficients

The Pauli part of an open-chain two-local Hamiltonian splits into a one-site and a two-site part.
Pairing a commutator against a Pauli string supported on three sites annihilates every cross term
involving a one-site factor, because a one-site label either fails the two-site requirement or is
disjoint from its partner.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

section TwoFamily

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- The commutator coefficient of an index pair from two families. -/
def pairCoeff2 {ι κ : Type*} (S : ι → (σ → Option (Fin 3))) (T : κ → (σ → Option (Fin 3)))
    (h : ι → ℂ) (k : κ → ℂ) (R : σ → Option (Fin 3)) (i : ι) (j : κ) : ℂ :=
  h i * k j * ((optPhaseProd (S i) (T j) - optPhaseProd (T j) (S i)) *
    (if R = optMulLabel (S i) (T j) then 1 else 0))

theorem trace_commutator_eq_smul_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : σ → Option (Fin 3)) (S : ι → (σ → Option (Fin 3))) (T : κ → (σ → Option (Fin 3)))
    (h : ι → ℂ) (k : κ → ℂ) :
    Matrix.trace (finitePauliMatrix R *
        ((∑ i, h i • finitePauliMatrix (S i)) * (∑ j, k j • finitePauliMatrix (T j)) -
          (∑ j, k j • finitePauliMatrix (T j)) * (∑ i, h i • finitePauliMatrix (S i)))) =
      ((2 : ℂ) ^ Fintype.card σ) * ∑ i, ∑ j, pairCoeff2 S T h k R i j := by
  classical
  rw [trace_pauli_commutator_sum R S T h k, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pairCoeff2]
  by_cases hRij : R = optMulLabel (S i) (T j)
  · rw [if_pos hRij, if_pos hRij]
    ring
  · rw [if_neg hRij, if_neg hRij]
    ring

theorem pairCoeff2_eq_zero_of_card {ι κ : Type*} (S : ι → (σ → Option (Fin 3)))
    (T : κ → (σ → Option (Fin 3))) (h : ι → ℂ) (k : κ → ℂ) (R : σ → Option (Fin 3))
    (hR : (labelSupport R).card = 3) {i : ι} {j : κ}
    (hSi : (labelSupport (S i)).card ≤ 2) (hTj : (labelSupport (T j)).card ≤ 2)
    (hnot : ¬ ((labelSupport (S i)).card = 2 ∧ (labelSupport (T j)).card = 2 ∧
      (labelSupport (S i) ∩ labelSupport (T j)).card = 1 ∧
      labelSupport (S i) ∪ labelSupport (T j) = labelSupport R)) :
    pairCoeff2 S T h k R i j = 0 := by
  classical
  by_cases hRij : R = optMulLabel (S i) (T j)
  · by_cases hdisj : Disjoint (labelSupport (S i)) (labelSupport (T j))
    · rw [pairCoeff2, optPhaseProd_sub_eq_zero_of_disjoint hdisj, zero_mul, mul_zero]
    · exact absurd (card_inter_eq_one_of_card_three hSi hTj hR hRij hdisj) hnot
  · rw [pairCoeff2, if_neg hRij, mul_zero, mul_zero]

/-- A one-site factor never contributes at a three-site string. -/
theorem pairCoeff2_eq_zero_of_left_card_one {ι κ : Type*} (S : ι → (σ → Option (Fin 3)))
    (T : κ → (σ → Option (Fin 3))) (h : ι → ℂ) (k : κ → ℂ) (R : σ → Option (Fin 3))
    (hR : (labelSupport R).card = 3) {i : ι} {j : κ}
    (hSi : (labelSupport (S i)).card = 1) (hTj : (labelSupport (T j)).card ≤ 2) :
    pairCoeff2 S T h k R i j = 0 := by
  refine pairCoeff2_eq_zero_of_card S T h k R hR (by omega) hTj ?_
  rintro ⟨h1, -, -, -⟩
  omega

theorem pairCoeff2_eq_zero_of_right_card_one {ι κ : Type*} (S : ι → (σ → Option (Fin 3)))
    (T : κ → (σ → Option (Fin 3))) (h : ι → ℂ) (k : κ → ℂ) (R : σ → Option (Fin 3))
    (hR : (labelSupport R).card = 3) {i : ι} {j : κ}
    (hSi : (labelSupport (S i)).card ≤ 2) (hTj : (labelSupport (T j)).card = 1) :
    pairCoeff2 S T h k R i j = 0 := by
  refine pairCoeff2_eq_zero_of_card S T h k R hR hSi (by omega) ?_
  rintro ⟨-, h2, -, -⟩
  omega

end TwoFamily

section Shell

variable {m : ℕ}

/-- The one-site index family of the chain shell. -/
def chainSiteLabel (p : Fin (m + 1) × Fin 3) : Fin (m + 1) → Option (Fin 3) :=
  siteLabel p.1 p.2

/-- The two-site index family of the chain shell. -/
def chainEdgeLabel (q : Fin m × Fin 3 × Fin 3) : Fin (m + 1) → Option (Fin 3) :=
  pairLabel q.1.castSucc q.1.succ q.2.1 q.2.2

theorem castSucc_ne_succ (i : Fin m) : (i.castSucc : Fin (m + 1)) ≠ i.succ := by
  rw [Ne, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

theorem card_labelSupport_chainSiteLabel (p : Fin (m + 1) × Fin 3) :
    (labelSupport (chainSiteLabel p)).card = 1 :=
  card_labelSupport_siteLabel p.1 p.2

theorem card_labelSupport_chainEdgeLabel (q : Fin m × Fin 3 × Fin 3) :
    (labelSupport (chainEdgeLabel q)).card = 2 :=
  card_labelSupport_pairLabel (castSucc_ne_succ q.1) q.2.1 q.2.2

theorem labelSupport_chainEdgeLabel (q : Fin m × Fin 3 × Fin 3) :
    labelSupport (chainEdgeLabel q) = chainSites q.1 := by
  rw [chainEdgeLabel, labelSupport_pairLabel (castSucc_ne_succ q.1), chainSites]

/-- The one-site part of a chain shell operator. -/
def chainSiteOp (h : Fin (m + 1) → Fin 3 → ℝ) :
    Matrix (FiniteQubitConfiguration (Fin (m + 1))) (FiniteQubitConfiguration (Fin (m + 1))) ℂ :=
  ∑ p : Fin (m + 1) × Fin 3, ((h p.1 p.2 : ℝ) : ℂ) • finitePauliMatrix (chainSiteLabel p)

/-- The two-site part of a chain shell operator. -/
def chainEdgeOp (J : Fin m → Fin 3 → Fin 3 → ℝ) :
    Matrix (FiniteQubitConfiguration (Fin (m + 1))) (FiniteQubitConfiguration (Fin (m + 1))) ℂ :=
  ∑ q : Fin m × Fin 3 × Fin 3,
    ((J q.1 q.2.1 q.2.2 : ℝ) : ℂ) • finitePauliMatrix (chainEdgeLabel q)

end Shell

end GaloisForLFunctions.HTGeometry
