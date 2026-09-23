import GaloisForLFunctions.HTGeometry.CoppoSSH

/-!
# Dimer boundary operators on the actual square-summable carrier

The SSH recurrence from arXiv:2503.11928 defines an everywhere-defined linear
operator on `ℓ²`. Its kernel contains the constructed geometric edge state.
The same recurrence on an even finite chain leaves an explicit terminal defect.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

abbrev CoppoEdgeHilbert := lp (fun _ : ℕ => ℝ) 2

/-- The backward unilateral shift on the square-summable carrier. -/
def coppoEdgeBackwardShift : Module.End ℝ CoppoEdgeHilbert where
  toFun f := ⟨fun n => f (n + 1), by
    apply memℓp_gen
    exact (summable_nat_add_iff 1).mpr (Memℓp.summable (by norm_num) f.property)⟩
  map_add' f g := by apply lp.ext; rfl
  map_smul' c f := by apply lp.ext; rfl

/-- The zero-energy sublattice constraint for intercell coupling one. -/
def coppoEdgeConstraint (a : ℝ) : Module.End ℝ CoppoEdgeHilbert :=
  coppoSSHRatio a • LinearMap.id + coppoEdgeBackwardShift

/-- The geometric vector is an actual kernel vector, not just a scalar formal solution. -/
theorem coppoEdgeConstraint_edge (a : ℝ) :
    coppoEdgeConstraint a (coppoSSHEdgeVector a) = 0 := by
  apply lp.ext
  funext n
  exact coppoSSHEdgeProfile_recurrence a n

/-- The half-line boundary constraint has a nontrivial kernel. -/
theorem coppoEdgeConstraint_kernel_ne_bot (a : ℝ) :
    LinearMap.ker (coppoEdgeConstraint a) ≠ ⊥ := by
  intro h
  have hm : coppoSSHEdgeVector a ∈ LinearMap.ker (coppoEdgeConstraint a) :=
    coppoEdgeConstraint_edge a
  rw [h] at hm
  exact coppoSSHEdgeVector_ne_zero a hm

/-- Finite-chain sublattice constraint, with the absent far neighbour set to zero. -/
def coppoFiniteEdgeConstraint (q : ℝ) (N : ℕ)
    (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ :=
  q * f i + if h : i.val < N then f ⟨i.val + 1, by omega⟩ else 0

/-- A finite chain has exactly one residual entry for the truncated geometric edge profile. -/
theorem coppoFiniteEdgeConstraint_profile (a : ℝ) (N : ℕ) (i : Fin (N + 1)) :
    coppoFiniteEdgeConstraint (coppoSSHRatio a) N (fun j => coppoSSHEdgeProfile a j.val) i =
      if i.val = N then coppoSSHRatio a * coppoSSHEdgeProfile a N else 0 := by
  unfold coppoFiniteEdgeConstraint
  by_cases hi : i.val = N
  · simp [hi]
  · have hl : i.val < N := by omega
    simp only [dif_pos hl, if_neg hi]
    exact coppoSSHEdgeProfile_recurrence a i.val

/-- Squared terminal error is the exact exponentially decaying power. -/
theorem coppoFiniteEdgeConstraint_terminal_sq (a : ℝ) (N : ℕ) :
    coppoFiniteEdgeConstraint (coppoSSHRatio a) N
        (fun j => coppoSSHEdgeProfile a j.val) ⟨N, by omega⟩ ^ (2 : ℕ) =
      coppoSSHRatio a ^ (2 * (N + 1)) := by
  rw [coppoFiniteEdgeConstraint_profile]
  simp only [ite_true]
  rw [coppoSSHEdgeProfile_terminal_residual, neg_sq]
  dsimp [coppoSSHEdgeProfile]
  rw [← pow_mul, Nat.mul_comm (N + 1) 2, pow_mul, neg_sq, ← pow_mul]

/-- Every square-summable zero mode is a scalar multiple of the constructed edge vector. -/
theorem coppoEdgeConstraint_zero_iff (a : ℝ) (f : CoppoEdgeHilbert) :
    coppoEdgeConstraint a f = 0 ↔ f = f 0 • coppoSSHEdgeVector a := by
  constructor
  · intro hf
    have hr (n : ℕ) : coppoSSHRatio a * f n + f (n + 1) = 0 := by
      exact congrArg (fun v : CoppoEdgeHilbert => v n) hf
    apply lp.ext
    funext n
    change f n = f 0 * coppoSSHEdgeProfile a n
    induction n with
    | zero => simp [coppoSSHEdgeProfile_zero]
    | succ n ih =>
      have he := coppoSSHEdgeProfile_recurrence a n
      change f (n + 1) = f 0 * coppoSSHEdgeProfile a (n + 1)
      have hn := hr n
      rw [ih] at hn
      rw [show coppoSSHEdgeProfile a (n + 1) =
        -coppoSSHRatio a * coppoSSHEdgeProfile a n by linarith [he]]
      nlinarith [hn]
  · intro hf
    rw [hf, map_smul, coppoEdgeConstraint_edge, smul_zero]

/-- The finite open-chain constraint has no exact zero mode at nonzero intracell coupling. -/
theorem coppoFiniteEdgeConstraint_zero_iff (a : ℝ) (N : ℕ) (f : Fin (N + 1) → ℝ) :
    coppoFiniteEdgeConstraint (coppoSSHRatio a) N f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    funext i
    have hr (j : Fin (N + 1)) := congrFun hf j
    have hq := (coppoSSHRatio_pos a).ne'
    induction i using Fin.reverseInduction with
    | last =>
      have h := hr (Fin.last N)
      simp [coppoFiniteEdgeConstraint] at h
      exact h.resolve_left hq
    | cast i ih =>
      simp only [Pi.zero_apply] at ih ⊢
      have h := hr i.castSucc
      have he : (⟨i.val + 1, by omega⟩ : Fin (N + 1)) = i.succ := rfl
      simp only [coppoFiniteEdgeConstraint, Fin.val_castSucc, dif_pos i.isLt, he,
        Pi.zero_apply] at h
      rw [ih, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hq
  · rintro rfl
    funext i
    simp [coppoFiniteEdgeConstraint]

end GaloisForLFunctions.HTGeometry
