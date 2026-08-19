import GaloisForLFunctions.HTGeometry.SiegelProjIntrinsic

/-!
# The Lovász swap identity

Transposing two adjacent basis vectors leaves the span of the earlier ones unchanged, so — the
projected norm being intrinsic — the new `i`-th Jacobi entry is the *old* projected norm of the
transposed vector:

`d'ᵢ = projNorm i e_{i+1} = dᵢ Uᵢ,ᵢ₊₁² + dᵢ₊₁`.

No determinant of a minor and no re-triangularisation are needed: both inequalities follow from the
two halves of the intrinsic characterisation, transported through the permutation.

* `quadForm_congr` : the value of a congruate is the value at the transported vector.
* `permMatrix` : the matrix of a permutation, with its action on vectors.
* `swap_d_eq_projNorm` : **the swap identity.**
* `swap_d_lt` : **a swap strictly lowers `dᵢ` exactly when the Lovász condition fails.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The value of a congruate at `x` is the value of the form at the transported vector. -/
theorem quadForm_congr (A γ : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((γᵀ * A * γ) *ᵥ x) = (γ *ᵥ x) ⬝ᵥ (A *ᵥ (γ *ᵥ x)) := by
  have hstep : (γᵀ * A * γ) *ᵥ x = γᵀ *ᵥ (A *ᵥ (γ *ᵥ x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hstep, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- The matrix of a permutation. -/
noncomputable def permMatrix (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => if b = σ a then (1 : ℝ) else 0

@[simp]
theorem permMatrix_mulVec (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (a : Fin n) :
    (permMatrix σ *ᵥ x) a = x (σ a) := by
  classical
  show ∑ b, (if b = σ a then (1 : ℝ) else 0) * x b = x (σ a)
  rw [Finset.sum_eq_single (σ a) (fun b _ hb => by simp [hb])
    (fun hcon => absurd (Finset.mem_univ (σ a)) hcon)]
  simp

/-- An involution acts as an involution. -/
theorem permMatrix_involutive {σ : Equiv.Perm (Fin n)} (hσ : ∀ a, σ (σ a) = a)
    (x : Fin n → ℝ) : permMatrix σ *ᵥ (permMatrix σ *ᵥ x) = x := by
  funext a
  rw [permMatrix_mulVec, permMatrix_mulVec, hσ]

theorem permMatrix_single_swap {i j : Fin n} (hij : i ≠ j) :
    permMatrix (Equiv.swap i j) *ᵥ (Pi.single i (1 : ℝ)) = Pi.single j (1 : ℝ) := by
  classical
  funext a
  rw [permMatrix_mulVec]
  by_cases haj : a = j
  · subst haj
    rw [Equiv.swap_apply_right]
    simp
  · have hne : Equiv.swap i j a ≠ i := by
      intro hcon
      have := congrArg (Equiv.swap i j) hcon
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact haj this
    rw [Pi.single_apply, Pi.single_apply, if_neg hne, if_neg haj]

/-- The swap of two indices at least `i` preserves the support condition. -/
theorem permMatrix_lowerSupport {i j k : Fin n} (hji : i ≤ j) (hki : i ≤ k)
    {w : Fin n → ℝ} (hw : w ∈ lowerSupport i) :
    permMatrix (Equiv.swap j k) *ᵥ w ∈ lowerSupport i := by
  classical
  intro p hp
  rw [permMatrix_mulVec]
  refine hw _ ?_
  by_cases hpj : p = j
  · subst hpj
    rw [Equiv.swap_apply_left]
    exact hki
  by_cases hpk : p = k
  · subst hpk
    rw [Equiv.swap_apply_right]
    exact hji
  · rw [Equiv.swap_apply_of_ne_of_ne hpj hpk]
    exact hp

/-- **The swap identity.**  If `J'` is Jacobi data for the form obtained by transposing the basis
vectors `i` and `j`, then `d'ᵢ` is the projected norm of `e_j` for the original data. -/
theorem swap_d_eq_projNorm {J J' : JacobiData n} {i j : Fin n} (hij : i ≠ j)
    (hji : i ≤ j)
    (hform : J'.form
      = (permMatrix (Equiv.swap i j))ᵀ * J.form * (permMatrix (Equiv.swap i j))) :
    J'.d i = J.projNorm i (Pi.single j (1 : ℝ)) := by
  classical
  set σ : Equiv.Perm (Fin n) := Equiv.swap i j with hσdef
  have hinv : ∀ a, σ (σ a) = a := fun a => Equiv.swap_apply_self i j a
  have hei : permMatrix σ *ᵥ (Pi.single i (1 : ℝ)) = Pi.single j (1 : ℝ) :=
    permMatrix_single_swap hij
  have hej : permMatrix σ *ᵥ (Pi.single j (1 : ℝ)) = Pi.single i (1 : ℝ) := by
    have := congrArg (fun x => permMatrix σ *ᵥ x) hei
    rw [permMatrix_involutive hinv] at this
    exact this.symm
  have htransport : ∀ x : Fin n → ℝ,
      x ⬝ᵥ (J'.form *ᵥ x) = (permMatrix σ *ᵥ x) ⬝ᵥ (J.form *ᵥ (permMatrix σ *ᵥ x)) := by
    intro x
    rw [hform]
    exact quadForm_congr _ _ x
  refine le_antisymm ?_ ?_
  · obtain ⟨w, hw, hwval⟩ := J.projNorm_eq_form_sub i (Pi.single j (1 : ℝ))
    have hw' : permMatrix σ *ᵥ w ∈ lowerSupport i :=
      permMatrix_lowerSupport (le_refl i) hji hw
    have hstep := J'.projNorm_le_form_sub i (Pi.single i (1 : ℝ)) hw'
    rw [J'.projNorm_self i] at hstep
    have hkey1 : permMatrix σ *ᵥ (Pi.single i (1 : ℝ) - permMatrix σ *ᵥ w)
        = Pi.single j (1 : ℝ) - w := by
      rw [Matrix.mulVec_sub, hei, permMatrix_involutive hinv]
    refine le_trans hstep (le_of_eq ?_)
    rw [htransport, hkey1, hwval]
  · obtain ⟨w, hw, hwval⟩ := J'.projNorm_eq_form_sub i (Pi.single i (1 : ℝ))
    have hw' : permMatrix σ *ᵥ w ∈ lowerSupport i :=
      permMatrix_lowerSupport (le_refl i) hji hw
    have hstep := J.projNorm_le_form_sub i (Pi.single j (1 : ℝ)) hw'
    have hkey2 : permMatrix σ *ᵥ (Pi.single i (1 : ℝ) - w)
        = Pi.single j (1 : ℝ) - permMatrix σ *ᵥ w := by
      rw [Matrix.mulVec_sub, hei]
    refine le_trans hstep (le_of_eq ?_)
    rw [J'.projNorm_self i] at hwval
    rw [hwval, htransport, hkey2]

/-- **A swap strictly lowers the `i`-th entry exactly when the Lovász condition fails.** -/
theorem swap_d_lt {J J' : JacobiData n} {i j : Fin n} (hij : i ≠ j) (hji : i ≤ j)
    (hjs : (j : ℕ) = (i : ℕ) + 1)
    (hform : J'.form
      = (permMatrix (Equiv.swap i j))ᵀ * J.form * (permMatrix (Equiv.swap i j)))
    (hred : ∀ a b : Fin n, a < b → |J.U a b| ≤ 1 / 2)
    (hfail : J.d j < 3 / 4 * J.d i) : J'.d i < J.d i := by
  rw [swap_d_eq_projNorm hij hji hform, J.projNorm_succ hjs]
  have hb : (J.U i j) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    have := hred i j (Fin.lt_def.2 (by omega))
    nlinarith [abs_nonneg (J.U i j), sq_abs (J.U i j)]
  nlinarith [hfail, hb, J.pos i]

end GaloisForLFunctions.HTGeometry
