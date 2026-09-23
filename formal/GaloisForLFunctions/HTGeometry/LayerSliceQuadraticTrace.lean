/-
# The quadratic rate along a one-qubit extension slice

Along the slice `H(z,g) = diag(layerSplitEnergy E z) + g·layerCrossPerturbation M` the quadratic
rate `Tr(H²)` has no linear term in the coupling, because the cross perturbation has zero diagonal
and therefore no trace against a diagonal matrix.  So

  `Tr H(z,g)² = Q₀(z) + g²·Q_V`,

which is exactly the shape the quadratic-rate rigidity theorem consumes.  The residual energy
`Q_V = Tr(V²)` is twice the Hilbert–Schmidt pairing of the transition channel with its transpose,
hence a strictly positive real number whenever the channel is Hermitian and nonzero.

Main results:
* `trace_sq_layerExtensionSlice` — the rate has the shape `Q₀(z) + g² Q_V`.
* `trace_sq_layerCrossPerturbation` — `Q_V = 2 ∑_{a,b} M_{ab} M_{ba}`.
* `trace_sq_layerCrossPerturbation_ne_zero` — it is nonzero for a nonzero Hermitian channel.
-/
import GaloisForLFunctions.HTGeometry.BlockExtensionSecondOrderResponse

namespace GaloisForLFunctions.HTGeometry

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The trace of a square is the full double sum of the entries against their transposes. -/
theorem trace_sq_eq_sum {n : Type*} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    (X ^ (2 : ℕ)).trace = ∑ x, ∑ y, X x y * X y x := by
  rw [sq, Matrix.trace]
  exact Finset.sum_congr rfl fun x _ => by rw [Matrix.diag_apply, Matrix.mul_apply]

/-- The cross perturbation has no trace against a diagonal matrix, from either side. -/
theorem trace_diagonal_mul_layerCrossPerturbation (d : A × Bool → ℂ) (M : Matrix A A ℂ) :
    (Matrix.diagonal d * layerCrossPerturbation M).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rcases eq_or_ne x y with rfl | hxy
  · rw [layerCrossPerturbation_diagonal, mul_zero]
  · rw [Matrix.diagonal_apply_ne _ hxy, zero_mul]

theorem trace_layerCrossPerturbation_mul_diagonal (d : A × Bool → ℂ) (M : Matrix A A ℂ) :
    (layerCrossPerturbation M * Matrix.diagonal d).trace = 0 := by
  rw [Matrix.trace]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun y _ => ?_
  rcases eq_or_ne y x with rfl | hyx
  · rw [layerCrossPerturbation_diagonal, zero_mul]
  · rw [Matrix.diagonal_apply_ne _ hyx, mul_zero]

theorem trace_diagonal_sq (d : A × Bool → ℂ) :
    (Matrix.diagonal d * Matrix.diagonal d).trace = ∑ x, d x ^ (2 : ℕ) := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun x _ => by rw [sq]

/-- **The quadratic rate along the extension slice has no linear term.** -/
theorem trace_sq_layerExtensionSlice (E : A → ℂ) (M : Matrix A A ℂ) (z g : ℂ) :
    ((Matrix.diagonal (layerSplitEnergy E z) + g • layerCrossPerturbation M) ^ (2 : ℕ)).trace
      = (∑ x, layerSplitEnergy E z x ^ (2 : ℕ))
        + g ^ (2 : ℕ) * ((layerCrossPerturbation M) ^ (2 : ℕ)).trace := by
  set d : A × Bool → ℂ := layerSplitEnergy E z with hd
  set V : Matrix (A × Bool) (A × Bool) ℂ := layerCrossPerturbation M with hV
  have hexp : (Matrix.diagonal d + g • V) ^ (2 : ℕ)
      = Matrix.diagonal d * Matrix.diagonal d + g • (Matrix.diagonal d * V)
        + g • (V * Matrix.diagonal d) + (g * g) • (V * V) := by
    rw [sq, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    abel
  rw [hexp, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_smul, hV, hd,
    trace_diagonal_mul_layerCrossPerturbation, trace_layerCrossPerturbation_mul_diagonal,
    trace_diagonal_sq, ← sq]
  simp [smul_eq_mul, sq]

/-- The residual energy of the cross perturbation. -/
theorem trace_sq_layerCrossPerturbation (M : Matrix A A ℂ) :
    ((layerCrossPerturbation M) ^ (2 : ℕ)).trace = 2 * ∑ a, ∑ b, M a b * M b a := by
  rw [trace_sq_eq_sum]
  have hinner : ∀ (a : A) (r : Bool),
      (∑ y : A × Bool, layerCrossPerturbation M (a, r) y * layerCrossPerturbation M y (a, r))
        = ∑ b, M a b * M b a := by
    intro a r
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_bool]
    cases r <;> simp [layerCrossPerturbation]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ a : A,
      (∑ r : Bool, ∑ y : A × Bool,
        layerCrossPerturbation M (a, r) y * layerCrossPerturbation M y (a, r))
        = 2 * ∑ b, M a b * M b a := by
    intro a
    rw [Fintype.sum_bool, hinner a false, hinner a true, two_mul]
  rw [Finset.sum_congr rfl fun a _ => hrow a, ← Finset.mul_sum]

/-- **The residual energy is nonzero for a nonzero Hermitian channel.** -/
theorem trace_sq_layerCrossPerturbation_ne_zero {M : Matrix A A ℂ} (hM : M.IsHermitian)
    (hne : M ≠ 0) : ((layerCrossPerturbation M) ^ (2 : ℕ)).trace ≠ 0 := by
  classical
  rw [trace_sq_layerCrossPerturbation]
  have hentry : ∀ a b : A, M a b * M b a = ((‖M a b‖ : ℂ)) ^ (2 : ℕ) := by
    intro a b
    have hstar : M b a = star (M a b) := by
      have := congrArg (fun N : Matrix A A ℂ => N b a) hM
      simpa [Matrix.conjTranspose_apply] using this.symm
    rw [hstar, Complex.star_def, Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have hsum : (∑ a, ∑ b, M a b * M b a) = ((∑ a, ∑ b, ‖M a b‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hentry a b
  obtain ⟨a, b, hab⟩ : ∃ a b, M a b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by funext a b; exact hcon a b)
  have hpos : (0 : ℝ) < ∑ a, ∑ b, ‖M a b‖ ^ (2 : ℕ) := by
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun a => ∑ b, ‖M a b‖ ^ (2 : ℕ)) (fun a _ => Finset.sum_nonneg fun b _ => by positivity)
      (Finset.mem_univ a))
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun b => ‖M a b‖ ^ (2 : ℕ)) (fun b _ => by positivity) (Finset.mem_univ b))
    have : ‖M a b‖ ≠ 0 := norm_ne_zero_iff.mpr hab
    positivity
  rw [hsum]
  intro hzero
  have : ((∑ a, ∑ b, ‖M a b‖ ^ (2 : ℕ) : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · norm_num at h
    · exact h
  have hreal : (∑ a, ∑ b, ‖M a b‖ ^ (2 : ℕ) : ℝ) = 0 := by exact_mod_cast this
  exact hpos.ne' hreal

end GaloisForLFunctions.HTGeometry
