import GaloisForLFunctions.HTGeometry.ProjectiveOperatorNormReturnTarget
import GaloisForLFunctions.HTGeometry.HilbertSchmidtOperatorBound

/-!
# The kernel split of a self-adjoint propagator

A self-adjoint generator has an orthogonal kernel projector which the generated unitary group
fixes, so the evolution splits as that projector plus its own restriction to the orthogonal
complement.  On that complement the evolution stays unitary at every time, so removing the
projector cannot contract any norm: the operator norm of the difference is exactly one whenever
the complement is nonzero, and the squared Hilbert--Schmidt norm of the difference is exactly the
dimension of the complement, independently of the time.

This is the exact obstruction to a quenched decay statement: a fixed self-adjoint generator retains
its whole kernel forever, and its centered propagator is an isometry of the complement.
-/

open scoped Matrix.Norms.L2Operator
open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## Diagonal calculus in a fixed eigenbasis -/

theorem diagonal_mul_diagonal_fun (f g : d → ℂ) :
    Matrix.diagonal f * Matrix.diagonal g = Matrix.diagonal (fun i => f i * g i) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.mul_apply, h]

omit [Fintype d] in
theorem diagonal_sub_diagonal_fun (f g : d → ℂ) :
    Matrix.diagonal f - Matrix.diagonal g = Matrix.diagonal (fun i => f i - g i) := by
  ext i j
  by_cases h : i = j <;> simp [h]

/-- Conjugated diagonal matrices multiply entrywise in the same basis. -/
theorem conj_diagonal_mul (V : Matrix d d ℂ) (hV : star V * V = 1) (f g : d → ℂ) :
    (V * Matrix.diagonal f * star V) * (V * Matrix.diagonal g * star V) =
      V * Matrix.diagonal (fun i => f i * g i) * star V := by
  calc (V * Matrix.diagonal f * star V) * (V * Matrix.diagonal g * star V)
      = V * Matrix.diagonal f * ((star V * V) * (Matrix.diagonal g * star V)) := by
        simp only [Matrix.mul_assoc]
    _ = V * (Matrix.diagonal f * Matrix.diagonal g) * star V := by
        rw [hV, Matrix.one_mul]; simp only [Matrix.mul_assoc]
    _ = V * Matrix.diagonal (fun i => f i * g i) * star V := by
        rw [diagonal_mul_diagonal_fun]

/-- Conjugated diagonal matrices subtract entrywise in the same basis. -/
theorem conj_diagonal_sub (V : Matrix d d ℂ) (f g : d → ℂ) :
    V * Matrix.diagonal f * star V - V * Matrix.diagonal g * star V =
      V * Matrix.diagonal (fun i => f i - g i) * star V := by
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, diagonal_sub_diagonal_fun]

/-! ## The spectral kernel projector -/

/-- The orthogonal projection onto the kernel of a Hermitian matrix, written in the matrix's own
eigenbasis. -/
def spectralKernelProjector {L : Matrix d d ℂ} (hL : L.IsHermitian) : Matrix d d ℂ :=
  (hL.eigenvectorUnitary : Matrix d d ℂ) *
      Matrix.diagonal (fun i => if hL.eigenvalues i = 0 then (1 : ℂ) else 0) *
    star (hL.eigenvectorUnitary : Matrix d d ℂ)

section

variable {L : Matrix d d ℂ}

theorem star_mul_eigenvectorUnitary (hL : L.IsHermitian) :
    star (hL.eigenvectorUnitary : Matrix d d ℂ) * (hL.eigenvectorUnitary : Matrix d d ℂ) = 1 :=
  (Unitary.mem_iff.mp hL.eigenvectorUnitary.2).1

/-- The spectral kernel projector is an idempotent. -/
theorem spectralKernelProjector_idem (hL : L.IsHermitian) :
    spectralKernelProjector hL * spectralKernelProjector hL = spectralKernelProjector hL := by
  have hfun : (fun i => (if hL.eigenvalues i = 0 then (1 : ℂ) else 0) *
      (if hL.eigenvalues i = 0 then (1 : ℂ) else 0)) =
      fun i => if hL.eigenvalues i = 0 then (1 : ℂ) else 0 := by
    funext i
    by_cases h : hL.eigenvalues i = 0 <;> simp [h]
  rw [spectralKernelProjector, conj_diagonal_mul _ (star_mul_eigenvectorUnitary hL), hfun]

/-- The kernel projector is fixed by the generated unitary group: this is the invariant part of
the evolution. -/
theorem unitaryEvolution_mul_spectralKernelProjector (hL : L.IsHermitian) (t : ℝ) :
    unitaryEvolution L t * spectralKernelProjector hL = spectralKernelProjector hL := by
  have hfun : (fun i => Complex.exp (-(Complex.I * ((t : ℂ) * (hL.eigenvalues i : ℂ)))) *
      (if hL.eigenvalues i = 0 then (1 : ℂ) else 0)) =
      fun i => if hL.eigenvalues i = 0 then (1 : ℂ) else 0 := by
    funext i
    by_cases h : hL.eigenvalues i = 0
    · simp [h]
    · simp [h]
  rw [unitaryEvolution_spectral hL, spectralKernelProjector,
    conj_diagonal_mul _ (star_mul_eigenvectorUnitary hL), hfun]

/-- **Equation (8).**  The propagator of a self-adjoint generator is its kernel projector plus its
own restriction to the orthogonal complement of the kernel. -/
theorem unitaryEvolution_eq_spectralKernelProjector_add (hL : L.IsHermitian) (t : ℝ) :
    unitaryEvolution L t =
      spectralKernelProjector hL +
        unitaryEvolution L t * (1 - spectralKernelProjector hL) := by
  rw [Matrix.mul_sub, Matrix.mul_one, unitaryEvolution_mul_spectralKernelProjector hL]
  abel

/-! ## The centered propagator is an isometry of the complement -/

/-- The centered propagator is the conjugated diagonal matrix supported off the kernel. -/
theorem unitaryEvolution_sub_spectralKernelProjector_eq (hL : L.IsHermitian) (t : ℝ) :
    unitaryEvolution L t - spectralKernelProjector hL =
      (hL.eigenvectorUnitary : Matrix d d ℂ) *
          Matrix.diagonal (fun i =>
            if hL.eigenvalues i = 0 then (0 : ℂ)
            else Complex.exp (-(Complex.I * (t * hL.eigenvalues i)))) *
        star (hL.eigenvectorUnitary : Matrix d d ℂ) := by
  have hfun : (fun i => Complex.exp (-(Complex.I * ((t : ℂ) * (hL.eigenvalues i : ℂ)))) -
      (if hL.eigenvalues i = 0 then (1 : ℂ) else 0)) =
      fun i => if hL.eigenvalues i = 0 then (0 : ℂ)
        else Complex.exp (-(Complex.I * ((t : ℂ) * (hL.eigenvalues i : ℂ)))) := by
    funext i
    by_cases h : hL.eigenvalues i = 0
    · simp [h]
    · simp [h]
  rw [unitaryEvolution_spectral hL, spectralKernelProjector, conj_diagonal_sub, hfun]

private theorem norm_exp_neg_I_mul_ofReal (x : ℝ) : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (-(Complex.I * (x : ℂ))).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- **Equation (9), operator norm.**  If the generator has a nonzero eigenvalue, then removing the
kernel projector from the propagator leaves an operator of norm exactly one, at every time. -/
theorem l2_opNorm_unitaryEvolution_sub_spectralKernelProjector (hL : L.IsHermitian) (t : ℝ)
    (hne : ∃ i, hL.eigenvalues i ≠ 0) :
    ‖unitaryEvolution L t - spectralKernelProjector hL‖ = 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := hne
  haveI : Nonempty d := ⟨i₀⟩
  rw [unitaryEvolution_sub_spectralKernelProjector_eq hL,
    l2_opNorm_unitary_conj_eq hL.eigenvectorUnitary.2, Matrix.l2_opNorm_diagonal]
  have hentry : ∀ i, hL.eigenvalues i ≠ 0 →
      ‖(if hL.eigenvalues i = 0 then (0 : ℂ)
        else Complex.exp (-(Complex.I * ((t : ℂ) * (hL.eigenvalues i : ℂ)))))‖ = 1 := by
    intro i hi
    rw [if_neg hi]
    have := norm_exp_neg_I_mul_ofReal (t * hL.eigenvalues i)
    push_cast at this
    exact this
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases h : hL.eigenvalues i = 0
    · simp [h]
    · exact le_of_eq (hentry i h)
  · exact le_trans (le_of_eq (hentry i₀ hi₀).symm)
      (norm_le_pi_norm (fun i => if hL.eigenvalues i = 0 then (0 : ℂ)
        else Complex.exp (-(Complex.I * ((t : ℂ) * (hL.eigenvalues i : ℂ))))) i₀)

/-! ## The Hilbert--Schmidt identity -/

theorem hsNorm_conj_le {V : Matrix d d ℂ} (hVnorm : ‖V‖ = 1) (hVstar : ‖star V‖ = 1)
    (X : Matrix d d ℂ) : hsNorm (V * X * star V) ≤ hsNorm X := by
  calc hsNorm (V * X * star V) ≤ hsNorm (V * X) * ‖star V‖ := hsNorm_mul_le' _ _
    _ ≤ (‖V‖ * hsNorm X) * ‖star V‖ :=
        mul_le_mul_of_nonneg_right (hsNorm_mul_le _ _) (norm_nonneg _)
    _ = hsNorm X := by rw [hVnorm, hVstar]; ring

theorem hsNorm_unitary_conj [Nonempty d] {V : Matrix d d ℂ} (hV : V ∈ unitary (Matrix d d ℂ))
    (X : Matrix d d ℂ) : hsNorm (V * X * star V) = hsNorm X := by
  have hVnorm : ‖V‖ = 1 := CStarRing.norm_coe_unitary (⟨V, hV⟩ : unitary (Matrix d d ℂ))
  have hVstar : ‖star V‖ = 1 := by rw [norm_star]; exact hVnorm
  refine le_antisymm (hsNorm_conj_le hVnorm hVstar X) ?_
  have hback : star V * (V * X * star V) * star (star V) = X := by
    have h1 : star V * V = 1 := (Unitary.mem_iff.mp hV).1
    rw [star_star]
    calc star V * (V * X * star V) * V = (star V * V) * X * (star V * V) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1]; simp
  calc hsNorm X = hsNorm (star V * (V * X * star V) * star (star V)) := by rw [hback]
    _ ≤ hsNorm (V * X * star V) := by
        refine hsNorm_conj_le hVstar ?_ _
        rw [star_star]; exact hVnorm

theorem hsNorm_sq_diagonal (f : d → ℂ) :
    hsNorm (Matrix.diagonal f) ^ (2 : ℕ) = ∑ i, ‖f i‖ ^ (2 : ℕ) := by
  classical
  rw [hsNorm_sq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Equation (9), Hilbert--Schmidt norm.**  The squared Hilbert--Schmidt norm of the centered
propagator is the number of nonzero eigenvalues of the generator, at every time. -/
theorem hsNorm_sq_unitaryEvolution_sub_spectralKernelProjector [Nonempty d] (hL : L.IsHermitian)
    (t : ℝ) :
    hsNorm (unitaryEvolution L t - spectralKernelProjector hL) ^ (2 : ℕ) =
      ((Finset.univ.filter fun i => hL.eigenvalues i ≠ 0).card : ℝ) := by
  classical
  rw [unitaryEvolution_sub_spectralKernelProjector_eq hL,
    hsNorm_unitary_conj hL.eigenvectorUnitary.2, hsNorm_sq_diagonal]
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : hL.eigenvalues i = 0
  · simp [h]
  · rw [if_neg h, if_pos h]
    have := norm_exp_neg_I_mul_ofReal (t * hL.eigenvalues i)
    push_cast at this ⊢
    rw [this]
    norm_num

/-! ## The complement dimension is the codimension of the kernel -/

/-- The number of nonzero eigenvalues is the codimension of the kernel of the generator. -/
theorem card_filter_eigenvalues_ne_zero (hL : L.IsHermitian) :
    (Finset.univ.filter fun i => hL.eigenvalues i ≠ 0).card =
      Fintype.card d - Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin L)) := by
  classical
  have hrank : L.rank = (Finset.univ.filter fun i => hL.eigenvalues i ≠ 0).card := by
    rw [hL.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hsplit :
      Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin L)) +
          Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin L)) =
        Fintype.card d := by
    rw [LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin L)]
    simp
  have hrangerank : L.rank = Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin L)) := rfl
  omega

/-- **Equation (9) in the card's form.**  The squared Hilbert--Schmidt norm of the centered
propagator is the total dimension minus the dimension of the centralizer. -/
theorem hsNorm_sq_unitaryEvolution_sub_spectralKernelProjector_eq_codim [Nonempty d]
    (hL : L.IsHermitian) (t : ℝ) :
    hsNorm (unitaryEvolution L t - spectralKernelProjector hL) ^ (2 : ℕ) =
      ((Fintype.card d : ℝ) - Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin L))) := by
  classical
  have hle : Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin L)) ≤ Fintype.card d := by
    have hsub := Submodule.finrank_le (LinearMap.ker (Matrix.mulVecLin L))
    simpa using hsub
  rw [hsNorm_sq_unitaryEvolution_sub_spectralKernelProjector hL t,
    card_filter_eigenvalues_ne_zero hL, Nat.cast_sub hle]

end

end GaloisForLFunctions.HTGeometry
