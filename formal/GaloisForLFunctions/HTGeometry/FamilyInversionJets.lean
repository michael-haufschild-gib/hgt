import GaloisForLFunctions.HTGeometry.JetTotalDerivation
import GaloisForLFunctions.HTGeometry.FamilyPolynomialGauge

/-!
# The jets of a reciprocal family in the family jet ring

The reciprocal jet formula is stated for a single function with jets indexed by `ℕ`.  A differential
relation for a finite family lives in the jet ring indexed by one spectral variable and one bounded
jet block per member.  This file transports the reciprocal numerators into that ring, blockwise, and
records the resulting formula for the jet vector of the reciprocal family.

The transport is legitimate because the `k`-th reciprocal numerator only involves jets of order at
most `k`, so the renaming used to place it in block `i` is correct on its whole support.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Evaluation of a supported polynomial only depends on the coordinates of its support. -/
theorem eval_eq_of_supported {σ : Type*} {s : Set σ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ MvPolynomial.supported ℂ s) {x y : σ → ℂ} (hxy : ∀ i ∈ s, x i = y i) :
    MvPolynomial.eval x P = MvPolynomial.eval y P := by
  rw [MvPolynomial.supported_eq_adjoin_X] at hP
  induction hP using Algebra.adjoin_induction with
  | mem u hu =>
      obtain ⟨j, hj, rfl⟩ := hu
      rw [MvPolynomial.eval_X, MvPolynomial.eval_X, hxy j hj]
  | algebraMap r =>
      have hCr : (algebraMap ℂ (MvPolynomial σ ℂ)) r = MvPolynomial.C r := rfl
      rw [hCr, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add a b ha hb iha ihb =>
      rw [map_add, map_add, iha, ihb]
  | mul a b ha hb iha ihb =>
      rw [map_mul, map_mul, iha, ihb]

/-- The renaming placing the `ℕ`-indexed jet variables into one block of the family jet ring. -/
def familyJetRename (m n : ℕ) (i : Fin m) : ℕ → FamilyJetIndex m n :=
  fun j => if h : j < n + 1 then Sum.inr (i, ⟨j, h⟩) else Sum.inl ()

/-- On a polynomial supported in the available jet orders the blockwise renaming computes the
single-function evaluation. -/
theorem eval_rename_familyJetRename {m n k : ℕ} (hk : k ≤ n) (i : Fin m)
    {P : MvPolynomial ℕ ℂ} (hP : P ∈ MvPolynomial.supported ℂ (Set.Iic k))
    (g : Fin m → ℂ → ℂ) (z : ℂ) :
    MvPolynomial.eval (familyJetVec (n := n) g z)
        (MvPolynomial.rename (familyJetRename m n i) P)
      = MvPolynomial.eval (jetVec (g i) z) P := by
  rw [MvPolynomial.eval_rename]
  refine eval_eq_of_supported hP ?_
  intro j hj
  simp only [Set.mem_Iic] at hj
  have hjn : j < n + 1 := by omega
  simp only [Function.comp_apply, familyJetRename, dif_pos hjn, familyJetVec, Sum.elim_inr,
    jetVec_apply]

/-- The blockwise reciprocal numerator in the family jet ring. -/
def familyInvJetNum (m n : ℕ) (i : Fin m) (k : ℕ) : MvPolynomial (FamilyJetIndex m n) ℂ :=
  MvPolynomial.rename (familyJetRename m n i) (invJetNum k)

/-- **The jets of a reciprocal family.**  Every jet of `1 / g i` is the blockwise reciprocal
numerator evaluated on the jets of the family, divided by the corresponding power of `g i`. -/
theorem familyJetVec_inv_apply {m n : ℕ} {U : Set ℂ} (hU : IsOpen U) {g : Fin m → ℂ → ℂ}
    (hg : ∀ i, ∀ w ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (g i) w) (hne : ∀ i, ∀ w ∈ U, g i w ≠ 0)
    {z : ℂ} (hz : z ∈ U) (i : Fin m) (k : Fin (n + 1)) :
    familyJetVec (n := n) (fun i w => (g i w)⁻¹) z (Sum.inr (i, k))
      = MvPolynomial.eval (familyJetVec (n := n) g z) (familyInvJetNum m n i (k : ℕ))
        / (g i z) ^ ((k : ℕ) + 1) := by
  have hjet : familyJetVec (n := n) (fun i w => (g i w)⁻¹) z (Sum.inr (i, k))
      = iteratedDeriv (k : ℕ) (fun w => (g i w)⁻¹) z := rfl
  rw [hjet, iteratedDeriv_inv_eq_invJetNum_div hU (hg i) (hne i) (k : ℕ) z hz, familyInvJetNum,
    eval_rename_familyJetRename (Nat.lt_succ_iff.mp k.2) i (invJetNum_mem_supported (k : ℕ)) g z]

end

end GaloisForLFunctions.HTGeometry
