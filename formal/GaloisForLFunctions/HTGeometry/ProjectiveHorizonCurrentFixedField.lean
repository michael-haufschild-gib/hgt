import GaloisForLFunctions.HTGeometry.FreeJetTranslationFixedField
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonOneSidedCurrentAlgebra
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie

/-!
# The projective current action has scalar fixed field

The abstract polynomial `sl₂` current algebra of
`ProjectiveHorizonOneSidedCurrentAlgebra` is realized here on the free scalar jet field.  On the
polynomial jet coordinates `x₀, x₁, ...`, its relevant modes are

* `Eₖ = ∂/∂xₖ`;
* `Fₖ(xₙ) = -∑ᵣ xᵣ x_(n-k-r)` for `k ≤ n`;
* `Hₖ(xₙ) = -2 x_(n-k)` for `k ≤ n`.

They extend uniquely to the free rational jet field by the quotient rule.  The two one-sided
projective modes `E₀` and `F₁` generate `H₁`, and repeated bracketing with `H₁` generates every
coordinate current `Eₖ`.  Consequently their simultaneous kernel is exactly the scalar field.
Equivalently, it is the fixed field of every independent free-coordinate translation.

This is the rational fixed-field layer for the actual projective current action.  It is stronger
than the three-mode packet `E₀, F₀, F₁`: the constant opposite mode `F₀` is not needed for fixed-field
collapse.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-! ## Polynomial projective current modes -/

/-- The quadratic coefficient of the square of the free divided-power jet arc. -/
def projectiveJetSquareCoeff (C : Type*) [Field C] (n : ℕ) : MvPolynomial ℕ C :=
  ∑ r ∈ Finset.range (n + 1), X r * X (n - r)

/-- Differentiating the quadratic arc coefficient in its constant coordinate gives twice the
opposite endpoint coefficient. -/
theorem pderiv_zero_projectiveJetSquareCoeff
    {C : Type*} [Field C] (n : ℕ) :
    MvPolynomial.pderiv 0 (projectiveJetSquareCoeff C n) =
      (2 : C) • MvPolynomial.X n := by
  classical
  simp only [projectiveJetSquareCoeff, map_sum, Derivation.leibniz,
    MvPolynomial.pderiv_X, Finset.sum_add_distrib, Pi.single_apply, Algebra.smul_def]
  have hleft :
      ∑ x ∈ Finset.range (n + 1),
        X x * (if n - x = 0 then (1 : MvPolynomial ℕ C) else 0) = X n := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      have hble : b ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
      have hsub : n - b ≠ 0 := by omega
      simp [hsub]
    · simp
  have hright :
      ∑ x ∈ Finset.range (n + 1),
        X (n - x) * (if x = 0 then (1 : MvPolynomial ℕ C) else 0) = X n := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b hb hb0
      simp [hb0]
    · simp
  simp only [Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.algebraMap_eq]
  rw [hleft, hright]
  rw [show MvPolynomial.C (2 : C) = (2 : MvPolynomial ℕ C) by
      exact map_ofNat (MvPolynomial.C : C →+* MvPolynomial ℕ C) 2,
    two_mul]

/-- The polynomial translation-current mode `Eₖ`. -/
def projectiveJetCurrentEPolynomial (C : Type*) [Field C] (k : ℕ) :
    Derivation C (MvPolynomial ℕ C) (MvPolynomial ℕ C) :=
  MvPolynomial.pderiv k

/-- The polynomial inversion-conjugate current mode `Fₖ`. -/
def projectiveJetCurrentFPolynomial (C : Type*) [Field C] (k : ℕ) :
    Derivation C (MvPolynomial ℕ C) (MvPolynomial ℕ C) :=
  MvPolynomial.mkDerivation C fun n ↦
    if k ≤ n then -(projectiveJetSquareCoeff C (n - k)) else 0

/-- The polynomial diagonal current mode `Hₖ`. -/
def projectiveJetCurrentHPolynomial (C : Type*) [Field C] (k : ℕ) :
    Derivation C (MvPolynomial ℕ C) (MvPolynomial ℕ C) :=
  MvPolynomial.mkDerivation C fun n ↦
    if k ≤ n then -(2 : C) • MvPolynomial.X (n - k) else 0

/-- The actual free-jet action satisfies the one-sided current relation `[E₀,F₁]=H₁`. -/
theorem projectiveJetCurrentEPolynomial_lie_FPolynomial_one
    {C : Type*} [Field C] :
    ⁅projectiveJetCurrentEPolynomial C 0, projectiveJetCurrentFPolynomial C 1⁆ =
      projectiveJetCurrentHPolynomial C 1 := by
  apply MvPolynomial.derivation_ext
  intro n
  rw [Derivation.commutator_apply]
  simp only [projectiveJetCurrentEPolynomial, projectiveJetCurrentFPolynomial,
    projectiveJetCurrentHPolynomial, MvPolynomial.mkDerivation_X,
    MvPolynomial.pderiv_X]
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, if_pos hn, map_neg,
      show MvPolynomial.pderiv 0 (projectiveJetSquareCoeff C (n - 1)) =
        (2 : C) • MvPolynomial.X (n - 1) by
          exact pderiv_zero_projectiveJetSquareCoeff (C := C) (n - 1)]
    have hn0 : n ≠ 0 := by omega
    simp [hn0]
  · have hn0 : n = 0 := by omega
    subst n
    simp

/-- The diagonal linear mode raises every translation-current mode:
`[H₁,Eₖ]=2E_(k+1)`. -/
theorem projectiveJetCurrentHPolynomial_one_lie_EPolynomial
    {C : Type*} [Field C] (k : ℕ) :
    ⁅projectiveJetCurrentHPolynomial C 1, projectiveJetCurrentEPolynomial C k⁆ =
      (2 : C) • projectiveJetCurrentEPolynomial C (k + 1) := by
  apply MvPolynomial.derivation_ext
  intro n
  rw [Derivation.commutator_apply, Derivation.smul_apply]
  change projectiveJetCurrentHPolynomial C 1
        (MvPolynomial.pderiv k (MvPolynomial.X n)) -
      MvPolynomial.pderiv k
        (projectiveJetCurrentHPolynomial C 1 (MvPolynomial.X n)) =
    (2 : C) • MvPolynomial.pderiv (k + 1) (MvPolynomial.X n)
  have hfirst :
      projectiveJetCurrentHPolynomial C 1
          (MvPolynomial.pderiv k (MvPolynomial.X n)) = 0 := by
    rw [MvPolynomial.pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  rw [hfirst, projectiveJetCurrentHPolynomial, MvPolynomial.mkDerivation_X]
  by_cases hn : 1 ≤ n
  · rw [if_pos hn, (MvPolynomial.pderiv k).map_smul,
      MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
    by_cases hkn : k + 1 = n
    · subst n
      simp
    · have hk : k ≠ n - 1 := by omega
      simp [hkn, hk]
  · have hn0 : n = 0 := by omega
    subst n
    simp

/-! ## Quotient-rule action on the free rational jet field -/

/-- The rational translation-current mode `Eₖ`. -/
def projectiveJetCurrentE (C : Type*) [Field C] (k : ℕ) :
    Derivation C (FreeCoordinateRationalField C ℕ)
      (FreeCoordinateRationalField C ℕ) :=
  extendFreeCoordinatePolynomialDerivation (projectiveJetCurrentEPolynomial C k)

/-- The rational inversion-conjugate current mode `Fₖ`. -/
def projectiveJetCurrentF (C : Type*) [Field C] (k : ℕ) :
    Derivation C (FreeCoordinateRationalField C ℕ)
      (FreeCoordinateRationalField C ℕ) :=
  extendFreeCoordinatePolynomialDerivation (projectiveJetCurrentFPolynomial C k)

/-- The rational diagonal current mode `Hₖ`. -/
def projectiveJetCurrentH (C : Type*) [Field C] (k : ℕ) :
    Derivation C (FreeCoordinateRationalField C ℕ)
      (FreeCoordinateRationalField C ℕ) :=
  extendFreeCoordinatePolynomialDerivation (projectiveJetCurrentHPolynomial C k)

/-- Translation-current modes are exactly the existing free-coordinate derivations. -/
theorem projectiveJetCurrentE_eq_freeCoordinateDerivation
    {C : Type*} [Field C] (k : ℕ) :
    projectiveJetCurrentE C k = freeCoordinateDerivation C ℕ k :=
  rfl

/-- The rational projective current action satisfies `[E₀,F₁]=H₁`. -/
theorem projectiveJetCurrentE_lie_F_one
    {C : Type*} [Field C] :
    ⁅projectiveJetCurrentE C 0, projectiveJetCurrentF C 1⁆ =
      projectiveJetCurrentH C 1 := by
  calc
    ⁅projectiveJetCurrentE C 0, projectiveJetCurrentF C 1⁆ =
        extendFreeCoordinatePolynomialDerivation
          ⁅projectiveJetCurrentEPolynomial C 0,
            projectiveJetCurrentFPolynomial C 1⁆ :=
      extendFreeCoordinatePolynomialDerivation_lie
        (projectiveJetCurrentEPolynomial C 0)
        (projectiveJetCurrentFPolynomial C 1)
    _ = extendFreeCoordinatePolynomialDerivation
        (projectiveJetCurrentHPolynomial C 1) :=
      congrArg extendFreeCoordinatePolynomialDerivation
        projectiveJetCurrentEPolynomial_lie_FPolynomial_one
    _ = projectiveJetCurrentH C 1 := rfl

/-- The rational projective current action satisfies `[H₁,Eₖ]=2E_(k+1)`. -/
theorem projectiveJetCurrentH_one_lie_E
    {C : Type*} [Field C] (k : ℕ) :
    ⁅projectiveJetCurrentH C 1, projectiveJetCurrentE C k⁆ =
      (2 : C) • projectiveJetCurrentE C (k + 1) := by
  calc
    ⁅projectiveJetCurrentH C 1, projectiveJetCurrentE C k⁆ =
        extendFreeCoordinatePolynomialDerivation
          ⁅projectiveJetCurrentHPolynomial C 1,
            projectiveJetCurrentEPolynomial C k⁆ :=
      extendFreeCoordinatePolynomialDerivation_lie
        (projectiveJetCurrentHPolynomial C 1)
        (projectiveJetCurrentEPolynomial C k)
    _ = extendFreeCoordinatePolynomialDerivation
        ((2 : C) • projectiveJetCurrentEPolynomial C (k + 1)) :=
      congrArg extendFreeCoordinatePolynomialDerivation
        (projectiveJetCurrentHPolynomial_one_lie_EPolynomial k)
    _ = (2 : C) • extendFreeCoordinatePolynomialDerivation
        (projectiveJetCurrentEPolynomial C (k + 1)) :=
      extendFreeCoordinatePolynomialDerivation_smul 2 _
    _ = (2 : C) • projectiveJetCurrentE C (k + 1) := rfl

/-! ## One-sided generation and the exact fixed field -/

/-- **Two-mode projective-current generation.** If the actual current modes `E₀` and `F₁`
annihilate a rational free-jet observable, then every translation-current mode `Eₖ` annihilates
it. -/
theorem projectiveJetCurrent_annihilation_propagates
    {C : Type*} [Field C] [CharZero C]
    {f : FreeCoordinateRationalField C ℕ}
    (hE0 : projectiveJetCurrentE C 0 f = 0)
    (hF1 : projectiveJetCurrentF C 1 f = 0) :
    ∀ k, projectiveJetCurrentE C k f = 0 := by
  have hH1 : projectiveJetCurrentH C 1 f = 0 := by
    rw [← projectiveJetCurrentE_lie_F_one, Derivation.commutator_apply, hF1, hE0]
    simp
  intro k
  induction k with
  | zero => exact hE0
  | succ k ih =>
      have hbracket :
          ⁅projectiveJetCurrentH C 1, projectiveJetCurrentE C k⁆ f = 0 := by
        rw [Derivation.commutator_apply, hH1, ih]
        simp
      rw [projectiveJetCurrentH_one_lie_E, Derivation.smul_apply] at hbracket
      have hscaled := congrArg
        (fun z : FreeCoordinateRationalField C ℕ ↦ (2 : C)⁻¹ • z) hbracket
      simpa [smul_smul] using hscaled

/-- A rational free-jet observable is annihilated by `E₀,F₁` exactly when it is fixed by every
independent coordinate translation. -/
theorem projectiveJetCurrent_fixed_iff_all_freeCoordinateTranslations_fixed
    {C : Type*} [Field C] [CharZero C]
    (f : FreeCoordinateRationalField C ℕ) :
    (projectiveJetCurrentE C 0 f = 0 ∧ projectiveJetCurrentF C 1 f = 0) ↔
      ∀ c : ℕ → C, freeCoordinateTranslationEquiv C ℕ c f = f := by
  constructor
  · rintro ⟨hE0, hF1⟩
    apply (all_freeCoordinateTranslations_fixed_iff f).2
    apply (all_freeCoordinateDerivations_eq_zero_iff f).1
    intro k
    rw [← projectiveJetCurrentE_eq_freeCoordinateDerivation]
    exact projectiveJetCurrent_annihilation_propagates hE0 hF1 k
  · intro hfixed
    obtain ⟨a, rfl⟩ := (all_freeCoordinateTranslations_fixed_iff f).1 hfixed
    exact ⟨(projectiveJetCurrentE C 0).map_algebraMap a,
      (projectiveJetCurrentF C 1).map_algebraMap a⟩

/-- The simultaneous kernel of `E₀,F₁` consists exactly of scalar rational functions. -/
theorem projectiveJetCurrent_fixed_iff_scalar
    {C : Type*} [Field C] [CharZero C]
    (f : FreeCoordinateRationalField C ℕ) :
    (projectiveJetCurrentE C 0 f = 0 ∧ projectiveJetCurrentF C 1 f = 0) ↔
      ∃ a : C, f = algebraMap C (FreeCoordinateRationalField C ℕ) a :=
  (projectiveJetCurrent_fixed_iff_all_freeCoordinateTranslations_fixed f).trans
    (all_freeCoordinateTranslations_fixed_iff f)

/-- The simultaneous kernel field of the two actual projective current modes `E₀,F₁`. -/
def projectiveJetCurrentFixedField
    (C : Type*) [Field C] :
    IntermediateField C (FreeCoordinateRationalField C ℕ) where
  carrier := {f |
    projectiveJetCurrentE C 0 f = 0 ∧ projectiveJetCurrentF C 1 f = 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp [hx.1, hx.2, hy.1, hy.2]
  mul_mem' := by
    intro x y hx hy
    simp [Derivation.leibniz, hx.1, hx.2, hy.1, hy.2]
  algebraMap_mem' := by
    intro a
    exact ⟨(projectiveJetCurrentE C 0).map_algebraMap a,
      (projectiveJetCurrentF C 1).map_algebraMap a⟩
  inv_mem' := by
    intro x hx
    exact ⟨by simp [(projectiveJetCurrentE C 0).leibniz_inv, hx.1],
      by simp [(projectiveJetCurrentF C 1).leibniz_inv, hx.2]⟩

@[simp]
theorem mem_projectiveJetCurrentFixedField_iff
    {C : Type*} [Field C]
    (f : FreeCoordinateRationalField C ℕ) :
    f ∈ projectiveJetCurrentFixedField C ↔
      projectiveJetCurrentE C 0 f = 0 ∧ projectiveJetCurrentF C 1 f = 0 :=
  Iff.rfl

/-- **Projective chart/current fixed-field theorem.** The two-mode projective current kernel is
literally the full independent-translation fixed field. -/
theorem projectiveJetCurrentFixedField_eq_freeCoordinateTranslationFixedField
    {C : Type*} [Field C] [CharZero C] :
    projectiveJetCurrentFixedField C = freeCoordinateTranslationFixedField C ℕ := by
  ext f
  rw [mem_projectiveJetCurrentFixedField_iff,
    mem_freeCoordinateTranslationFixedField_iff]
  exact projectiveJetCurrent_fixed_iff_all_freeCoordinateTranslations_fixed f

/-- The actual one-sided projective current action has no nonconstant rational invariant. -/
@[simp]
theorem projectiveJetCurrentFixedField_eq_bot
    {C : Type*} [Field C] [CharZero C] :
    projectiveJetCurrentFixedField C = ⊥ := by
  rw [projectiveJetCurrentFixedField_eq_freeCoordinateTranslationFixedField,
    freeCoordinateTranslationFixedField_eq_bot]

end

end GaloisForLFunctions.HTGeometry
