import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair

/-!
# The isometries of a reflection pair

A carrier localizes at one point of an off-line pair `{ρ, ρ*}` only through a symmetry that
distinguishes `ρ` from `ρ*`. This file classifies the isometries of the local form
`h(u, v) = 2 Re(u v̄)` that are diagonal (act on each point separately, as multiplicative
correspondences do) or antidiagonal (exchange the two points, as the functional equation does).

* **Diagonal isometries** (`diagonal_isometry_iff`): `(u, v) ↦ (au, bv)` preserves `h` iff `a b̄ = 1`.
  It **separates** the two points (`a ≠ b`) iff `|a| ≠ 1`, i.e. iff it is a boost
  (`diagonal_isometry_separates_iff`); otherwise it is the scalar rotation `a = b`, `|a| = 1`.
* **Antidiagonal isometries** (`antidiagonal_isometry_iff`): `(u, v) ↦ (λv, μu)` preserves `h` iff
  `λ μ̄ = 1`. Its square is the scalar rotation by `λ/λ̄` (`antidiagonal_isometry_sq`): it is always
  elliptic. The swap fixes the positive line `u = v` (`localForm_swap_fixed`), on which `h = 2|u|²`.
* **Separation is hyperbolic** (`separating_isometry_is_boost`). A diagonal or antidiagonal
  isometry that maps the fibre of `ρ` to itself and distinguishes `ρ` from `ρ*` is a boost; every
  elliptic one is a scalar on the pair or exchanges its points.

So localization at an off-line point by local isometries is hyperbolic, and hyperbolic invariance
forces half-blindness (`mul_conj_eq_zero_of_cyclic_nonneg`). An elliptic local symmetry is a scalar
rotation, which constrains nothing, or a reflection, which cannot separate `ρ` from `ρ*`. A
positivity beyond isotropy that localizes must therefore isolate the pair by a non-isometric
operation — the role point sources play in finite interpolation — and no arithmetic correspondence
of the corpus does that.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- `Re(c X) = Re X` for all `X` iff `c = 1`. -/
theorem re_mul_eq_re_forall_iff (c : ℂ) : (∀ X : ℂ, (c * X).re = X.re) ↔ c = 1 := by
  constructor
  · intro h
    have h1 := h 1
    have hI := h I
    simp only [mul_one, Complex.one_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, zero_sub] at h1 hI
    apply Complex.ext
    · simpa using h1
    · simp at hI ⊢; linarith
  · rintro rfl X; rw [one_mul]

/-- **Diagonal isometries**: `(u, v) ↦ (au, bv)` preserves the local form iff `a b̄ = 1`. -/
theorem diagonal_isometry_iff (a b : ℂ) :
    (∀ u v : ℂ, localForm (a * u) (b * v) = localForm u v) ↔ a * conj b = 1 := by
  rw [← re_mul_eq_re_forall_iff]
  constructor
  · intro h X
    have := h X 1
    simp only [localForm, map_one, mul_one] at this
    have e : a * X * conj b = a * conj b * X := by ring
    rw [e] at this
    linarith
  · intro h u v
    simp only [localForm, map_mul]
    rw [show a * u * (conj b * conj v) = a * conj b * (u * conj v) by ring, h]

/-- **A diagonal isometry separates the two points iff it is a boost.** -/
theorem diagonal_isometry_separates_iff {a b : ℂ} (h : a * conj b = 1) : a ≠ b ↔ ‖a‖ ≠ 1 := by
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have hb : b = (conj a)⁻¹ := by
    have hcb : conj b = a⁻¹ := (eq_inv_of_mul_eq_one_right h)
    rw [← Complex.conj_conj b, hcb, map_inv₀]
  rw [hb, Ne, Ne, eq_conj_inv_iff_norm_eq_one ha]

/-- **Antidiagonal isometries**: `(u, v) ↦ (λv, μu)` preserves the local form iff `λ μ̄ = 1`. -/
theorem antidiagonal_isometry_iff (l m : ℂ) :
    (∀ u v : ℂ, localForm (l * v) (m * u) = localForm u v) ↔ l * conj m = 1 := by
  rw [← re_mul_eq_re_forall_iff]
  constructor
  · intro h X
    have := h 1 X
    simp only [localForm, mul_one, one_mul] at this
    -- `2 Re(l X m̄) = 2 Re(conj X)` and `Re(conj X) = Re X`
    have e : l * X * conj m = l * conj m * X := by ring
    rw [e, Complex.conj_re] at this
    linarith
  · intro h u v
    simp only [localForm, map_mul]
    rw [show l * v * (conj m * conj u) = l * conj m * (v * conj u) by ring, h]
    congr 1
    rw [show v * conj u = conj (u * conj v) by simp [mul_comm], Complex.conj_re]

/-- **An antidiagonal isometry is elliptic**: its square is the scalar `λ μ = λ/λ̄`, of modulus one. -/
theorem antidiagonal_isometry_sq {l m : ℂ} (h : l * conj m = 1) (u v : ℂ) :
    (l * (m * u), m * (l * v)) = (l * m * u, l * m * v) ∧ ‖l * m‖ = 1 := by
  refine ⟨by ext <;> simp <;> ring, ?_⟩
  have hn : ‖l‖ * ‖m‖ = 1 := by
    have := congrArg norm h
    rwa [norm_mul, Complex.norm_conj, norm_one] at this
  rw [norm_mul, hn]

/-- **The swap fixes a positive line**: `u = v` is invariant, with `h(u, u) = 2|u|²`. -/
theorem localForm_swap_fixed (u : ℂ) : localForm u u = 2 * Complex.normSq u := by
  rw [localForm, Complex.mul_conj, Complex.ofReal_re]

/-- **Separation is hyperbolic.** A diagonal isometry distinguishing the two points of a pair is a
boost (`|a| ≠ 1`); an elliptic diagonal isometry is the scalar rotation `a = b`. -/
theorem separating_isometry_is_boost {a b : ℂ} (h : a * conj b = 1) :
    (a ≠ b → ‖a‖ ≠ 1 ∧ b = (conj a)⁻¹) ∧ (‖a‖ = 1 → a = b) := by
  have ha : a ≠ 0 := by rintro rfl; simp at h
  have hb : b = (conj a)⁻¹ := by
    have hcb : conj b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [← Complex.conj_conj b, hcb, map_inv₀]
  refine ⟨fun hne => ⟨(diagonal_isometry_separates_iff h).mp hne, hb⟩, fun h1 => ?_⟩
  rw [hb]
  exact (eq_conj_inv_iff_norm_eq_one ha).mpr h1

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
