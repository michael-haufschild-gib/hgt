import GaloisForLFunctions.RHTower.RealSphericalComplementaryWeights
import GaloisForLFunctions.RHTower.RealSphericalUnitarity
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators

/-!
# Explicit spherical complementary series for `SL(2, ℝ)`

This file constructs the positive-definite invariant Hermitian form on the algebraic spherical
principal-series model for every real parameter `|s| < 1`.  Combining this construction with the
existing raising-norm obstruction proves that the model's exact unitarity locus is `(-1, 1)`, or
`(-1/2, 1/2)` in complementary-exponent normalization `s = 2ν`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Sesquilinear form diagonal in the standard spherical `K`-type basis. -/
def diagonalKTypeHermitianForm (q : ℤ → ℝ) :
    ComplexHermitianForm SphericalKFiniteModel :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun v w ↦ v.sum fun m z ↦ star z * (q m : ℂ) * w m)
    (by
      intro v₁ v₂ w
      rw [Finsupp.sum_add_index]
      · intro m hm
        simp
      · intro m hm z₁ z₂
        rw [star_add]
        ring)
    (by
      intro c v w
      rw [Finsupp.sum_smul_index']
      · simp only [smul_eq_mul, star_mul, starRingEnd_apply]
        rw [Finsupp.mul_sum]
        apply Finsupp.sum_congr
        intro m hm
        ring
      · intro m
        simp)
    (by
      intro v w₁ w₂
      simp only [Finsupp.add_apply, mul_add, Finsupp.sum_add])
    (by
      intro c v w
      simp only [Finsupp.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finsupp.mul_sum]
      apply Finsupp.sum_congr
      intro m hm
      ring)

@[simp]
theorem diagonalKTypeHermitianForm_apply (q : ℤ → ℝ)
    (v w : SphericalKFiniteModel) :
    diagonalKTypeHermitianForm q v w =
      v.sum fun m z ↦ star z * (q m : ℂ) * w m := rfl

@[simp]
theorem diagonalKTypeHermitianForm_single_left (q : ℤ → ℝ)
    (m : ℤ) (z : ℂ) (w : SphericalKFiniteModel) :
    diagonalKTypeHermitianForm q (Finsupp.single m z) w =
      star z * (q m : ℂ) * w m := by
  simp [diagonalKTypeHermitianForm]

@[simp]
theorem diagonalKTypeHermitianForm_single (q : ℤ → ℝ)
    (m n : ℤ) (z w : ℂ) :
    diagonalKTypeHermitianForm q (Finsupp.single m z) (Finsupp.single n w) =
      if m = n then star z * (q m : ℂ) * w else 0 := by
  by_cases h : m = n
  · subst n
    simp
  · simp [h]

/-- Real diagonal weights define a Hermitian form. -/
theorem diagonalKTypeHermitianForm_isSymm (q : ℤ → ℝ) :
    (diagonalKTypeHermitianForm q).IsSymm := by
  rw [LinearMap.isSymm_iff_basis (Finsupp.basisSingleOne :
    Module.Basis ℤ ℂ SphericalKFiniteModel)]
  intro m n
  by_cases h : m = n
  · subst n
    simp
  · simp [h, Ne.symm h]

/-- Diagonal values are finite weighted sums of complex squared norms. -/
theorem diagonalKTypeHermitianForm_self_re (q : ℤ → ℝ)
    (v : SphericalKFiniteModel) :
    (diagonalKTypeHermitianForm q v v).re =
      ∑ m ∈ v.support, Complex.normSq (v m) * q m := by
  rw [diagonalKTypeHermitianForm_apply]
  simp only [Finsupp.sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    (star (v m) * (q m : ℂ) * v m).re =
        ((q m : ℂ) * (star (v m) * v m)).re := by ring_nf
    _ = ((q m : ℂ) * (Complex.normSq (v m) : ℂ)).re := by
      change
        ((q m : ℂ) * ((starRingEnd ℂ) (v m) * v m)).re =
          ((q m : ℂ) * (Complex.normSq (v m) : ℂ)).re
      rw [← Complex.normSq_eq_conj_mul_self]
    _ = Complex.normSq (v m) * q m := by simp [mul_comm]

/-- Strictly positive diagonal weights define a positive-definite Hermitian form. -/
theorem diagonalKTypeHermitianForm_positiveDefinite (q : ℤ → ℝ)
    (hq : ∀ m, 0 < q m) :
    IsPositiveDefiniteHermitian (diagonalKTypeHermitianForm q) := by
  constructor
  · exact diagonalKTypeHermitianForm_isSymm q
  · intro v hv
    rw [diagonalKTypeHermitianForm_self_re]
    apply Finset.sum_pos
    · intro m hm
      exact mul_pos ((Complex.normSq_pos).2 (Finsupp.mem_support_iff.mp hm)) (hq m)
    · exact Finsupp.support_nonempty_iff.mpr hv

/-- Weight recurrence proves infinitesimal invariance on basis vectors. -/
theorem complementaryDiagonalForm_single_invariant (s : ℝ) (hs : |s| < 1)
    (m n : ℤ) (z w : ℂ) :
    diagonalKTypeHermitianForm (complementaryKTypeWeight s)
        (sphericalPrincipalE (s : ℂ) (Finsupp.single m z))
        (Finsupp.single n w) =
      -diagonalKTypeHermitianForm (complementaryKTypeWeight s)
        (Finsupp.single m z)
        (sphericalPrincipalF (s : ℂ) (Finsupp.single n w)) := by
  by_cases h : m + 1 = n
  · subst n
    simp
    have hrec := complementaryKTypeWeight_succ_recurrence s hs m
    have hrecC := congrArg (fun x : ℝ ↦ (x : ℂ)) hrec
    push_cast at hrecC
    simp only [starRingEnd_apply, star_ofNat] at ⊢
    norm_num at hrecC ⊢
    linear_combination (-((starRingEnd ℂ) z * w) / 2) * hrecC
  · have hback : n - 1 ≠ m := by omega
    simp [h, hback]

/-- Complementary-series diagonal form satisfies `e† = -f` on every finite vector. -/
theorem complementaryDiagonalForm_invariant (s : ℝ) (hs : |s| < 1) :
    IsSphericalPrincipalInvariant s
      (diagonalKTypeHermitianForm (complementaryKTypeWeight s)) := by
  intro v
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v₁ v₂ hv₁ hv₂ =>
      intro w
      simp only [map_add, LinearMap.add_apply]
      rw [hv₁ w, hv₂ w]
      ring
  | single m z =>
      intro w
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ =>
          simp only [map_add]
          rw [hw₁, hw₂]
          ring
      | single n w =>
          exact complementaryDiagonalForm_single_invariant s hs m n z w

/-- Explicit complementary-series Hermitian form on the spherical `K`-finite model. -/
def sphericalComplementaryHermitianForm (s : ℝ) :
    ComplexHermitianForm SphericalKFiniteModel :=
  diagonalKTypeHermitianForm (complementaryKTypeWeight s)

/-- Inside `(-1,1)`, the explicit complementary-series form is positive definite. -/
theorem sphericalComplementaryHermitianForm_positiveDefinite (s : ℝ) (hs : |s| < 1) :
    IsPositiveDefiniteHermitian (sphericalComplementaryHermitianForm s) := by
  exact diagonalKTypeHermitianForm_positiveDefinite _
    (complementaryKTypeWeight_pos s hs)

/-- Inside `(-1,1)`, the explicit complementary-series form is infinitesimally invariant. -/
theorem sphericalComplementaryHermitianForm_invariant (s : ℝ) (hs : |s| < 1) :
    IsSphericalPrincipalInvariant s (sphericalComplementaryHermitianForm s) := by
  exact complementaryDiagonalForm_invariant s hs

/-- Every complementary-series parameter in `(-1,1)` is unitarizable in the algebraic spherical
model. -/
theorem mem_unitarizableSphericalPrincipalParameter (s : ℝ) (hs : |s| < 1) :
    s ∈ UnitarizableSphericalPrincipalParameter := by
  exact ⟨sphericalComplementaryHermitianForm s,
    sphericalComplementaryHermitianForm_positiveDefinite s hs,
    sphericalComplementaryHermitianForm_invariant s hs⟩

/-- Exact unitarity locus of the real spherical principal-series Harish-Chandra model. -/
theorem unitarizableSphericalPrincipalParameter_eq_Ioo :
    UnitarizableSphericalPrincipalParameter = Set.Ioo (-1) 1 := by
  apply Set.Subset.antisymm
  · exact unitarizableSphericalPrincipalParameter_subset
  · intro s hs
    exact mem_unitarizableSphericalPrincipalParameter s (abs_lt.mpr hs)

/-- Exact complementary-exponent locus after the normalization `s = 2ν`. -/
theorem unitarizableSphericalExponentParameter_eq_Ioo :
    {ν : ℝ | 2 * ν ∈ UnitarizableSphericalPrincipalParameter} =
      Set.Ioo (-1 / 2) (1 / 2) := by
  apply Set.Subset.antisymm
  · exact unitarizableSphericalExponentParameter_subset
  · intro ν hν
    exact mem_unitarizableSphericalPrincipalParameter (2 * ν)
      (abs_lt.mpr ⟨by linarith [hν.1], by linarith [hν.2]⟩)

end
end GaloisForLFunctions.RHTower
