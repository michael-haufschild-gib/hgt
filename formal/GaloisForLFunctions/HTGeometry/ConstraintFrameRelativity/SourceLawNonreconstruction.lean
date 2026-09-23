import Mathlib

/-!
# Source-law nonreconstruction from observer-fibre coordinates

Two derivations of the *same* polynomial algebra on the *same* algebraically independent packet
have opposite finite-type behaviour.  The free prolongation `D₊ X_j = X_{j+1}` produces the jet
tower `D₊^n X_0 = X_n`, which is algebraically independent, while the truncated prolongation
`D_m X_j = X_{j+1}` for `j < m`, `D_m X_j = 0` for `j ≥ m`, annihilates the jet tower after
`m + 1` steps and confines the whole orbit to the span of `X_0, …, X_m`.

The Stokes side has the same shape: the exact contact form of two branches at contact `j` is
`Q_j = ((1+j)/2) z² + ((3-j)/2) t²`, positive definite at `j = 1` and indefinite at `j = 4`, while
the cluster-split intervention changes the form by `-2(k-ℓ) X_U X_V`, i.e. by
`((k-ℓ)/2)((X_U - X_V)² - M²)` with the port `M = X_U + X_V` fixed.

Hence no invariant of the shared coefficient/prolongation/aperture/history data determines the
governing law.
-/

namespace HTGeometry.ConstraintFrameRelativity

open MvPolynomial

variable (K : Type*) [Field K]

/-! ## The free and truncated prolongations -/

/-- The free prolongation `X_j ↦ X_{j+1}`. -/
noncomputable def freeProlongation :
    Derivation K (MvPolynomial ℕ K) (MvPolynomial ℕ K) :=
  mkDerivation K fun j => X (j + 1)

/-- The prolongation truncated at level `m`. -/
noncomputable def truncProlongation (m : ℕ) :
    Derivation K (MvPolynomial ℕ K) (MvPolynomial ℕ K) :=
  mkDerivation K fun j => if j < m then X (j + 1) else 0

@[simp] theorem freeProlongation_X (j : ℕ) :
    freeProlongation K (X j) = (X (j + 1) : MvPolynomial ℕ K) := by
  rw [freeProlongation, mkDerivation_X]

@[simp] theorem truncProlongation_X (m j : ℕ) :
    truncProlongation K m (X j) = if j < m then (X (j + 1) : MvPolynomial ℕ K) else 0 := by
  rw [truncProlongation, mkDerivation_X]

/-- **The free jet tower.**  `D₊^n X_0 = X_n`. -/
theorem freeProlongation_iterate (n : ℕ) :
    (fun p => freeProlongation K p)^[n] (X 0) = (X n : MvPolynomial ℕ K) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, freeProlongation_X]

/-- **The free jet tower is algebraically independent.** -/
theorem freeProlongation_algebraicIndependent :
    AlgebraicIndependent K fun n : ℕ => (fun p => freeProlongation K p)^[n] (X 0) := by
  have h : (fun n : ℕ => (fun p => freeProlongation K p)^[n] (X 0))
      = (X : ℕ → MvPolynomial ℕ K) := by
    funext n
    exact freeProlongation_iterate K n
  rw [h]
  exact algebraicIndependent_X ℕ K

/-- **The truncated jet tower before the wall.** -/
theorem truncProlongation_iterate_le {m j : ℕ} (hj : j ≤ m) :
    (fun p => truncProlongation K m p)^[j] (X 0) = (X j : MvPolynomial ℕ K) := by
  induction j with
  | zero => rfl
  | succ k ih =>
    have hk : k ≤ m := Nat.le_of_succ_le hj
    have hklt : k < m := Nat.lt_of_succ_le hj
    rw [Function.iterate_succ_apply', ih hk, truncProlongation_X, if_pos hklt]

/-- **The truncated jet tower is annihilated at the wall.** -/
theorem truncProlongation_iterate_wall (m : ℕ) :
    (fun p => truncProlongation K m p)^[m + 1] (X 0) = (0 : MvPolynomial ℕ K) := by
  rw [Function.iterate_succ_apply', truncProlongation_iterate_le K (le_refl m),
    truncProlongation_X, if_neg (lt_irrefl m)]

theorem iterate_map_zero (D : Derivation K (MvPolynomial ℕ K) (MvPolynomial ℕ K)) (d : ℕ) :
    (fun p => D p)^[d] (0 : MvPolynomial ℕ K) = 0 := by
  induction d with
  | zero => rfl
  | succ e ih =>
    rw [Function.iterate_succ_apply', ih, map_zero]

theorem truncProlongation_iterate_gt {m j : ℕ} (hj : m < j) :
    (fun p => truncProlongation K m p)^[j] (X 0) = (0 : MvPolynomial ℕ K) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = d + (m + 1) := ⟨j - (m + 1), by omega⟩
  rw [Function.iterate_add_apply, truncProlongation_iterate_wall K m,
    iterate_map_zero K (truncProlongation K m) d]

/-- **The truncated orbit is confined to a finite filtration stage.** -/
theorem truncProlongation_orbit_mem_span (m j : ℕ) :
    (fun p => truncProlongation K m p)^[j] (X 0)
      ∈ Submodule.span K (Set.range fun i : Fin (m + 1) => (X (i : ℕ) : MvPolynomial ℕ K)) := by
  rcases Nat.lt_or_ge m j with hj | hj
  · rw [truncProlongation_iterate_gt K hj]
    exact Submodule.zero_mem _
  · rw [truncProlongation_iterate_le K hj]
    exact Submodule.subset_span ⟨⟨j, Nat.lt_succ_of_le hj⟩, rfl⟩

/-- **Same packet, opposite jet law.** -/
theorem jet_law_nonreconstruction (m : ℕ) :
    AlgebraicIndependent K (fun n : ℕ => (fun p => freeProlongation K p)^[n] (X 0))
      ∧ (fun p => freeProlongation K p)^[m + 1] (X 0) ≠ (0 : MvPolynomial ℕ K)
      ∧ (fun p => truncProlongation K m p)^[m + 1] (X 0) = (0 : MvPolynomial ℕ K) := by
  refine ⟨freeProlongation_algebraicIndependent K, ?_, truncProlongation_iterate_wall K m⟩
  rw [freeProlongation_iterate]
  exact X_ne_zero (m + 1)

/-! ## The Stokes contact form and its cluster-split intervention -/

/-- The exact contact form of two branches at contact `j`. -/
noncomputable def contactForm (j z t : ℝ) : ℝ := (1 + j) / 2 * z ^ (2 : ℕ) + (3 - j) / 2 * t ^ (2 : ℕ)

/-- At contact one the form is positive definite. -/
theorem contactForm_pos {z t : ℝ} (h : z ≠ 0 ∨ t ≠ 0) : 0 < contactForm 1 z t := by
  rw [contactForm]
  rcases h with h | h
  · have hz : 0 < z ^ (2 : ℕ) := by positivity
    have ht : (0 : ℝ) ≤ t ^ (2 : ℕ) := sq_nonneg t
    nlinarith
  · have ht : 0 < t ^ (2 : ℕ) := by positivity
    have hz : (0 : ℝ) ≤ z ^ (2 : ℕ) := sq_nonneg z
    nlinarith

/-- At contact four the form takes a negative value, so its negative index is one. -/
theorem contactForm_neg : contactForm 4 0 1 < 0 := by
  rw [contactForm]
  norm_num

/-- The port direction is unchanged: the form restricted to `z = 0` is the port coefficient. -/
theorem contactForm_port (j t : ℝ) : contactForm j 0 t = (3 - j) / 2 * t ^ (2 : ℕ) := by
  rw [contactForm]
  ring

/-- **The exact cluster-split intervention.**  Activating a coefficient at order `k > ℓ` changes
the Stokes form by `-2(k-ℓ) X_U X_V`, equivalently by `((k-ℓ)/2)((X_U - X_V)² - M²)` where
`M = X_U + X_V` is the physical-rank port. -/
theorem cluster_split (k l xU xV : ℝ) :
    -2 * (k - l) * xU * xV = (k - l) / 2 * ((xU - xV) ^ (2 : ℕ) - (xU + xV) ^ (2 : ℕ)) := by
  ring

end HTGeometry.ConstraintFrameRelativity
