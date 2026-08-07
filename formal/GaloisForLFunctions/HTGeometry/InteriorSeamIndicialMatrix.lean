import Mathlib

/-!
# The interior indicial matrix of a paired half-log seam

At an interior prime seam the paired leading coefficients of a log-conormal profile transform under

`I_τ = [(1 − 2τ) I − J] / (1 − τ)`,

where `J` is the orientation swap.  Its eigenvalues are `−2τ/(1 − τ)` on the symmetric orientation
and `2` on the antisymmetric one, so it is invertible for every paired order `0 < τ < 1`: bounded
interior forcing kills both coefficients, and the physical half-log indicial root is a boundary
phenomenon rather than an independent interior root.

At the borderline `τ = 1` the matrix degenerates and its numerator `−I − J` has the antisymmetric
line as kernel, so boundedness forces antisymmetry first.
-/

namespace GaloisForLFunctions.HTGeometry

/-- The orientation swap on a paired half-log profile. -/
def orientationSwap (v : ℝ × ℝ) : ℝ × ℝ := (v.2, v.1)

/-- The interior indicial matrix `I_τ = [(1−2τ)I − J]/(1−τ)` acting on paired leading
coefficients. -/
noncomputable def indicialMatrix (τ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (((1 - 2 * τ) * v.1 - v.2) / (1 - τ), ((1 - 2 * τ) * v.2 - v.1) / (1 - τ))

theorem indicialMatrix_apply (τ : ℝ) (v : ℝ × ℝ) :
    indicialMatrix τ v
      = (((1 - 2 * τ) • v - orientationSwap v).1 / (1 - τ),
         ((1 - 2 * τ) • v - orientationSwap v).2 / (1 - τ)) := by
  unfold indicialMatrix orientationSwap
  simp [Prod.smul_def]

/-- **The symmetric eigenvalue is `−2τ/(1−τ)`.** -/
theorem indicialMatrix_sym (τ : ℝ) :
    indicialMatrix τ (1, 1) = (-(2 * τ) / (1 - τ)) • ((1, 1) : ℝ × ℝ) := by
  unfold indicialMatrix
  simp only [Prod.smul_mk, smul_eq_mul, mul_one, Prod.mk.injEq]
  constructor <;> · congr 1; ring

/-- **The antisymmetric eigenvalue is `2`.** -/
theorem indicialMatrix_anti {τ : ℝ} (hτ : τ ≠ 1) :
    indicialMatrix τ (1, -1) = (2 : ℝ) • ((1, -1) : ℝ × ℝ) := by
  have h : (1 : ℝ) - τ ≠ 0 := sub_ne_zero.mpr (Ne.symm hτ)
  unfold indicialMatrix
  simp only [Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  constructor <;> field_simp <;> ring

/-- **The indicial matrix is injective for every paired order `0 < τ < 1`.**  Its two eigenvalues
`−2τ/(1−τ)` and `2` are both nonzero there, so bounded interior forcing kills both leading
coefficients: the card's `(5)`. -/
theorem indicialMatrix_eq_zero_iff {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1) (v : ℝ × ℝ) :
    indicialMatrix τ v = 0 ↔ v = 0 := by
  have hne : (1 : ℝ) - τ ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt h1))
  constructor
  · intro h
    unfold indicialMatrix at h
    rw [Prod.ext_iff] at h
    obtain ⟨h1', h2'⟩ := h
    simp only [Prod.fst_zero, Prod.snd_zero, div_eq_zero_iff, hne, or_false] at h1' h2'
    have hb : v.2 = (1 - 2 * τ) * v.1 := by linarith
    have ha : v.1 = (1 - 2 * τ) * v.2 := by linarith
    have hkey : v.1 * (4 * τ * (1 - τ)) = 0 := by nlinarith [ha, hb]
    have hpos : 0 < 4 * τ * (1 - τ) := by nlinarith
    have hv1 : v.1 = 0 := by
      rcases mul_eq_zero.mp hkey with h | h
      · exact h
      · exact absurd h (ne_of_gt hpos)
    have hv2 : v.2 = 0 := by rw [hb, hv1]; ring
    exact Prod.ext hv1 hv2
  · intro h
    subst h
    unfold indicialMatrix
    simp

/-- **The borderline `τ = 1`.**  There the indicial numerator is `−I − J`, whose kernel is exactly
the antisymmetric line: boundedness first forces `F₋ = −F₊` at leading order.  This is the card's
`(6)`. -/
theorem indicialNumerator_kernel_at_one (v : ℝ × ℝ) :
    (1 - 2 * (1 : ℝ)) • v - orientationSwap v = 0 ↔ v.2 = -v.1 := by
  unfold orientationSwap
  rw [Prod.ext_iff]
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub,
    Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, _⟩; linarith
  · intro h; constructor <;> linarith

end GaloisForLFunctions.HTGeometry
