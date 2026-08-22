import GaloisForLFunctions.HTGeometry.TwistedLyapunovUnit
import GaloisForLFunctions.HTGeometry.HilbertSchmidtLyapunovInverse

/-!
# Norm bounds for the Lyapunov inverse

A solution of `v y + y v = q` with `μ • 1 ≤ v` satisfies `2μ ‖y‖ ≤ ‖q‖`, in the operator norm
and — when `y` is Hilbert–Schmidt — in the Hilbert–Schmidt norm.  The proof is the fixed-point
identity `2μ y = q - w y - y w` for `w = v - μ'` with `μ'` the midpoint of a Loewner interval
containing `v`: the two commutator terms are bounded by the half-length of the interval, and the
difference of midpoint and half-length is exactly the lower Loewner bound.
-/

open scoped Ring BigOperators
open ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- The midpoint identity behind every Lyapunov norm bound. -/
lemma lyapunov_midpoint_identity {v y q : A} (μ : ℝ) (heq : v * y + y * v = q) :
    (2 * μ) • y = q - (v - μ • (1 : A)) * y - y * (v - μ • (1 : A)) := by
  rw [← heq, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/-- **Operator-norm bound for the Lyapunov inverse.** -/
theorem norm_le_of_lyapunov {v y q : A} (hv : IsSelfAdjoint v) {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hlb : μ₁ • (1 : A) ≤ v) (heq : v * y + y * v = q) :
    (2 * μ₁) * ‖y‖ ≤ ‖q‖ := by
  rcases subsingleton_or_nontrivial A with hsub | hnt
  · have hy : y = 0 := Subsingleton.elim _ _
    have hq : q = 0 := Subsingleton.elim _ _
    rw [hy, hq, norm_zero, mul_zero]
  have hvM : v ≤ ‖v‖ • (1 : A) := by
    have h := hv.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hμM : μ₁ ≤ ‖v‖ := by
    have h0 : (0 : A) ≤ μ₁ • (1 : A) := smul_nonneg hμ₁.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hlb
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hμ₁, norm_one, mul_one] at h
  have hwn : ‖v - ((μ₁ + ‖v‖) / 2) • (1 : A)‖ ≤ (‖v‖ - μ₁) / 2 :=
    norm_sub_midpoint_le hμM hv hlb hvM
  have hid := lyapunov_midpoint_identity (y := y) (q := q) ((μ₁ + ‖v‖) / 2) heq
  have hpos : (0 : ℝ) < 2 * ((μ₁ + ‖v‖) / 2) := by linarith
  have hnorm : (2 * ((μ₁ + ‖v‖) / 2)) * ‖y‖
      ≤ ‖q‖ + ((‖v‖ - μ₁) / 2) * ‖y‖ + ‖y‖ * ((‖v‖ - μ₁) / 2) := by
    have hL : ‖(2 * ((μ₁ + ‖v‖) / 2)) • y‖ = (2 * ((μ₁ + ‖v‖) / 2)) * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    have h1 : ‖q - (v - ((μ₁ + ‖v‖) / 2) • (1 : A)) * y - y * (v - ((μ₁ + ‖v‖) / 2) • (1 : A))‖
        ≤ ‖q‖ + ((‖v‖ - μ₁) / 2) * ‖y‖ + ‖y‖ * ((‖v‖ - μ₁) / 2) := by
      have ha := norm_sub_le (q - (v - ((μ₁ + ‖v‖) / 2) • (1 : A)) * y)
        (y * (v - ((μ₁ + ‖v‖) / 2) • (1 : A)))
      have hb := norm_sub_le q ((v - ((μ₁ + ‖v‖) / 2) • (1 : A)) * y)
      have hc : ‖(v - ((μ₁ + ‖v‖) / 2) • (1 : A)) * y‖ ≤ ((‖v‖ - μ₁) / 2) * ‖y‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hwn (norm_nonneg _))
      have hd : ‖y * (v - ((μ₁ + ‖v‖) / 2) • (1 : A))‖ ≤ ‖y‖ * ((‖v‖ - μ₁) / 2) :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hwn (norm_nonneg _))
      linarith
    rw [← hL, hid]
    exact h1
  nlinarith [norm_nonneg y, norm_nonneg q]

/-- **Resolvent comparison at the identity.**  `2 Λ_v⁻¹(q) - q` is small when `v` is close to
`1`. -/
theorem norm_two_smul_sub_lyapunov {v y q : A} (hv : IsSelfAdjoint v) {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hlb : μ₁ • (1 : A) ≤ v) (heq : v * y + y * v = q) :
    μ₁ * ‖(2 : ℝ) • y - q‖ ≤ ‖(1 : A) - v‖ * ‖q‖ := by
  have hid : (2 : ℝ) • y - q = ((1 : A) - v) * y + y * ((1 : A) - v) := by
    rw [← heq, sub_mul, mul_sub, one_mul, mul_one]
    module
  have h1 : ‖(2 : ℝ) • y - q‖ ≤ 2 * ‖(1 : A) - v‖ * ‖y‖ := by
    rw [hid]
    calc ‖((1 : A) - v) * y + y * ((1 : A) - v)‖
        ≤ ‖((1 : A) - v) * y‖ + ‖y * ((1 : A) - v)‖ := norm_add_le _ _
      _ ≤ ‖(1 : A) - v‖ * ‖y‖ + ‖y‖ * ‖(1 : A) - v‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = 2 * ‖(1 : A) - v‖ * ‖y‖ := by ring
  have h2 : (2 * μ₁) * ‖y‖ ≤ ‖q‖ := norm_le_of_lyapunov hv hμ₁ hlb heq
  nlinarith [norm_nonneg ((1 : A) - v), norm_nonneg y, norm_nonneg q]

/-- **Operator-norm bound for the inverse of the twisted Lyapunov unit.** -/
theorem norm_twisted_unit_inv_le {c : A} {u : (A →L[ℝ] A)ˣ}
    (hu : (↑u : A →L[ℝ] A)
      = (lyapunov (CFC.sqrt c)).comp (saProj : A →L[ℝ] A) + ((1 : A →L[ℝ] A) - saProj))
    {μ₁ : ℝ} (hμ₁ : 0 < μ₁) (hlb : μ₁ • (1 : A) ≤ CFC.sqrt c)
    {q : A} (hq : IsSelfAdjoint q) :
    (2 * μ₁) * ‖(↑u⁻¹ : A →L[ℝ] A) q‖ ≤ ‖q‖ :=
  norm_le_of_lyapunov (CFC.sqrt_nonneg c).isSelfAdjoint hμ₁ hlb
    (lyapunov_twisted_unit_inv hu hq)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [PartialOrder (E →L[ℂ] E)] [StarOrderedRing (E →L[ℂ] E)]

/-- **Hilbert–Schmidt bound for the Lyapunov inverse.** -/
theorem hsNorm_le_of_lyapunov {v y q : E →L[ℂ] E} (hv : IsSelfAdjoint v)
    (hy : IsHilbertSchmidt y) {μ₁ : ℝ} (hμ₁ : 0 < μ₁)
    (hlb : μ₁ • (1 : E →L[ℂ] E) ≤ v) (heq : v * y + y * v = q) :
    (2 * μ₁) * hsNorm y ≤ hsNorm q := by
  rcases subsingleton_or_nontrivial (E →L[ℂ] E) with hsub | hnt
  · have hy0 : y = 0 := Subsingleton.elim _ _
    have hq0 : q = 0 := Subsingleton.elim _ _
    rw [hy0, hq0, hsNorm_zero, mul_zero]
  have hvM : v ≤ ‖v‖ • (1 : E →L[ℂ] E) := by
    have h := hv.le_algebraMap_norm_self
    rwa [Algebra.algebraMap_eq_smul_one] at h
  have hμM : μ₁ ≤ ‖v‖ := by
    have h0 : (0 : E →L[ℂ] E) ≤ μ₁ • (1 : E →L[ℂ] E) := smul_nonneg hμ₁.le zero_le_one
    have h := CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hlb
    rwa [norm_smul, Real.norm_eq_abs, abs_of_pos hμ₁, norm_one, mul_one] at h
  have hwn : ‖v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)‖ ≤ (‖v‖ - μ₁) / 2 :=
    norm_sub_midpoint_le hμM hv hlb hvM
  have hid := lyapunov_midpoint_identity (y := y) (q := q) ((μ₁ + ‖v‖) / 2) heq
  have hpos : (0 : ℝ) < 2 * ((μ₁ + ‖v‖) / 2) := by linarith
  have hqHS : IsHilbertSchmidt q := by
    rw [← heq]; exact (hy.comp_left v).add (hy.comp_right v)
  have hw1 : IsHilbertSchmidt
      ((v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) * y : E →L[ℂ] E) := hy.comp_left _
  have hw2 : IsHilbertSchmidt
      (y * (v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) : E →L[ℂ] E) := hy.comp_right _
  have hbound : (2 * ((μ₁ + ‖v‖) / 2)) * hsNorm y
      ≤ hsNorm q + ((‖v‖ - μ₁) / 2) * hsNorm y + hsNorm y * ((‖v‖ - μ₁) / 2) := by
    have hL : hsNorm ((2 * ((μ₁ + ‖v‖) / 2)) • y) = (2 * ((μ₁ + ‖v‖) / 2)) * hsNorm y := by
      rw [hsNorm_real_smul, abs_of_pos hpos]
    have ha : hsNorm ((q - (v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) * y)
        - y * (v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) : E →L[ℂ] E)
        ≤ hsNorm (q - (v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) * y : E →L[ℂ] E)
          + hsNorm (y * (v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) : E →L[ℂ] E) :=
      hsNorm_sub_le (hqHS.sub hw1) hw2
    have hb : hsNorm (q - (v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) * y : E →L[ℂ] E)
        ≤ hsNorm q + hsNorm ((v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) * y : E →L[ℂ] E) :=
      hsNorm_sub_le hqHS hw1
    have hc : hsNorm ((v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) * y : E →L[ℂ] E)
        ≤ ((‖v‖ - μ₁) / 2) * hsNorm y :=
      (hsNorm_comp_left_le hy).trans (mul_le_mul_of_nonneg_right hwn (hsNorm_nonneg _))
    have hd : hsNorm (y * (v - ((μ₁ + ‖v‖) / 2) • (1 : E →L[ℂ] E)) : E →L[ℂ] E)
        ≤ hsNorm y * ((‖v‖ - μ₁) / 2) :=
      (hsNorm_comp_right_le hy).trans (mul_le_mul_of_nonneg_left hwn (hsNorm_nonneg _))
    rw [← hL, hid]
    linarith
  nlinarith [hsNorm_nonneg y, hsNorm_nonneg q]

end

end GaloisForLFunctions.HTGeometry
