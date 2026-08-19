import GaloisForLFunctions.HTGeometry.HalfLineExponentialCoDistance

/-!
# The canonical biorthogonal reader of a half-line exponential system

The orthogonal residual of one exponential against the closed span of all the others is, after
normalising by its own squared length, an element of the closed span of the whole system whose
Laplace pairings with the system are the Kronecker delta, and it is the only such element.  Its
norm is the reciprocal of the co-distance.

No existence proposition is required: the reader is the normalised orthogonal projection residual.
-/

open Filter Topology Finset MeasureTheory
open scoped InnerProductSpace
open InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {lam : ℕ → ℝ} (hpos : ∀ k, 0 < lam k)

/-- The closed span of every exponential except the `n`-th. -/
def expCoSpan (lam : ℕ → ℝ) (hpos : ∀ k, 0 < lam k) (n : ℕ) :
    Submodule ℂ (Lp ℂ 2 halfLineLaplaceMeasure) :=
  (Submodule.span ℂ ((expSystem lam hpos) '' {m : ℕ | m ≠ n})).topologicalClosure

/-- The closed span of the whole exponential system. -/
def expFullSpan (lam : ℕ → ℝ) (hpos : ∀ k, 0 < lam k) :
    Submodule ℂ (Lp ℂ 2 halfLineLaplaceMeasure) :=
  (Submodule.span ℂ (Set.range (expSystem lam hpos))).topologicalClosure

instance instCompleteExpCoSpan (n : ℕ) : CompleteSpace (expCoSpan lam hpos n) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem expSystem_mem_expCoSpan {m n : ℕ} (hmn : m ≠ n) :
    expSystem lam hpos m ∈ expCoSpan lam hpos n :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨m, hmn, rfl⟩)

theorem expSystem_mem_expFullSpan (m : ℕ) :
    expSystem lam hpos m ∈ expFullSpan lam hpos :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨m, rfl⟩)

theorem expCoSpan_le_expFullSpan (n : ℕ) :
    expCoSpan lam hpos n ≤ expFullSpan lam hpos := by
  refine Submodule.topologicalClosure_minimal _ ?_
    (Submodule.isClosed_topologicalClosure _)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨m, -, rfl⟩
  exact expSystem_mem_expFullSpan hpos m

/-! ## The orthogonal residual -/

/-- The component of the `n`-th exponential orthogonal to all the others. -/
def expResidual (lam : ℕ → ℝ) (hpos : ∀ k, 0 < lam k) (n : ℕ) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  expSystem lam hpos n - (expCoSpan lam hpos n).starProjection (expSystem lam hpos n)

theorem expResidual_mem_orthogonal (n : ℕ) :
    expResidual lam hpos n ∈ (expCoSpan lam hpos n)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal _

theorem expResidual_mem_expFullSpan (n : ℕ) :
    expResidual lam hpos n ∈ expFullSpan lam hpos := by
  refine Submodule.sub_mem _ (expSystem_mem_expFullSpan hpos n) ?_
  exact expCoSpan_le_expFullSpan hpos n
    ((expCoSpan lam hpos n).starProjection_apply_mem _)

theorem inner_expSystem_expResidual_of_ne {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (expSystem lam hpos m) (expResidual lam hpos n) = 0 :=
  (Submodule.mem_orthogonal _ _).mp (expResidual_mem_orthogonal hpos n) _
    (expSystem_mem_expCoSpan hpos hmn)

theorem inner_expSystem_expResidual_self (n : ℕ) :
    inner ℂ (expSystem lam hpos n) (expResidual lam hpos n) =
      ((‖expResidual lam hpos n‖ : ℂ)) ^ 2 := by
  have hproj : inner ℂ ((expCoSpan lam hpos n).starProjection (expSystem lam hpos n))
      (expResidual lam hpos n) = 0 :=
    (Submodule.mem_orthogonal _ _).mp (expResidual_mem_orthogonal hpos n) _
      ((expCoSpan lam hpos n).starProjection_apply_mem _)
  have hsplit : expSystem lam hpos n =
      (expCoSpan lam hpos n).starProjection (expSystem lam hpos n) +
        expResidual lam hpos n := by
    rw [expResidual]
    abel
  rw [hsplit, inner_add_left, hproj, zero_add]
  exact inner_self_eq_norm_sq_to_K _

/-! ## The reader -/

/-- The canonical biorthogonal reader of the `n`-th rate. -/
def expReader (lam : ℕ → ℝ) (hpos : ∀ k, 0 < lam k) (n : ℕ) :
    Lp ℂ 2 halfLineLaplaceMeasure :=
  ((((‖expResidual lam hpos n‖ : ℝ) ^ 2 : ℝ) : ℂ))⁻¹ • expResidual lam hpos n

theorem expReader_mem_expFullSpan (n : ℕ) :
    expReader lam hpos n ∈ expFullSpan lam hpos :=
  Submodule.smul_mem _ _ (expResidual_mem_expFullSpan hpos n)

/-- **Biorthogonality.**  The reader pairs with the exponential system as a Kronecker delta. -/
theorem inner_expSystem_expReader {n : ℕ} (hne : expResidual lam hpos n ≠ 0) (m : ℕ) :
    inner ℂ (expSystem lam hpos m) (expReader lam hpos n) = if m = n then 1 else 0 := by
  have hnorm : (((‖expResidual lam hpos n‖ : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have hp : (0 : ℝ) < ‖expResidual lam hpos n‖ := norm_pos_iff.mpr hne
    have hsq : (0 : ℝ) < ‖expResidual lam hpos n‖ ^ 2 := by positivity
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hsq)
  by_cases hmn : m = n
  · subst hmn
    rw [expReader, inner_smul_right, inner_expSystem_expResidual_self, if_pos rfl,
      show (((‖expResidual lam hpos m‖ : ℂ)) ^ 2) =
        (((‖expResidual lam hpos m‖ : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact inv_mul_cancel₀ hnorm
  · rw [expReader, inner_smul_right, inner_expSystem_expResidual_of_ne hpos hmn,
      mul_zero, if_neg hmn]

/-- **The reader norm.**  It is the reciprocal of the co-distance. -/
theorem norm_expReader {n : ℕ} (hne : expResidual lam hpos n ≠ 0) :
    ‖expReader lam hpos n‖ = ‖expResidual lam hpos n‖⁻¹ := by
  have hpos' : 0 < ‖expResidual lam hpos n‖ := norm_pos_iff.mpr hne
  rw [expReader, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖expResidual lam hpos n‖ ^ 2)]
  field_simp

/-- **Canonicity.**  A biorthogonal element of the closed span of the system is unique. -/
theorem eq_of_inner_expSystem_eq {r r' : Lp ℂ 2 halfLineLaplaceMeasure}
    (hr : r ∈ expFullSpan lam hpos) (hr' : r' ∈ expFullSpan lam hpos)
    (h : ∀ m, inner ℂ (expSystem lam hpos m) r = inner ℂ (expSystem lam hpos m) r') :
    r = r' := by
  have hdiff : ∀ m, inner ℂ (expSystem lam hpos m) (r - r') = 0 := by
    intro m
    rw [inner_sub_right, h m, sub_self]
  have hspan : ∀ u ∈ Submodule.span ℂ (Set.range (expSystem lam hpos)),
      inner ℂ u (r - r') = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨m, rfl⟩ := hx
        exact hdiff m
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  have horth : r - r' ∈ (expFullSpan lam hpos)ᗮ := by
    refine (Submodule.mem_orthogonal _ _).mpr ?_
    intro u hu
    have hcont : Continuous fun v : Lp ℂ 2 halfLineLaplaceMeasure => inner ℂ v (r - r') :=
      continuous_inner.comp (continuous_id.prodMk continuous_const)
    have hclosed : IsClosed {v : Lp ℂ 2 halfLineLaplaceMeasure | inner ℂ v (r - r') = 0} :=
      isClosed_eq hcont continuous_const
    exact closure_minimal hspan hclosed hu
  have hmem : r - r' ∈ expFullSpan lam hpos := Submodule.sub_mem _ hr hr'
  have hzero := (Submodule.mem_orthogonal _ _).mp horth _ hmem
  rw [inner_self_eq_zero] at hzero
  exact sub_eq_zero.mp hzero

end

end GaloisForLFunctions.HTGeometry
