import GaloisForLFunctions.HTGeometry.CocycleCommutatorPairing

/-!
# Alternating forms and Hermitian forms

The generalized Riemann relations are stated for a Hermitian form, but the datum produced by a
factor of automorphy is an alternating real form.  The two are the same object.  Given an
alternating `R`-bilinear `E` on a complex vector space which is invariant under simultaneous
multiplication by `i`,

`H (x, y) = E (i x, y) + i E (x, y)`

is Hermitian and complex-linear in its first argument, with `Im H = E` exactly.  It is positive
definite precisely when `E (i x, x) > 0` for `x` nonzero.

Complex homogeneity is the only clause with content: it follows from real homogeneity together with
the single computation `H (i x, y) = i H (x, y)`, which uses `i^(2 : ℕ) = -1` and nothing else.

Combined with `cocycleCommutator_isAlternatingBiadditive`, this turns the integral alternating form
of a factor of automorphy into the Hermitian form a quasi-Abelian facet certificate requires.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An alternating real form on a complex vector space, invariant under simultaneous multiplication
by `i`. -/
structure IsAlternatingCompatible (E : V → V → ℝ) : Prop where
  add_left : ∀ x y z : V, E (x + y) z = E x z + E y z
  smul_left : ∀ (r : ℝ) (x y : V), E ((r : ℂ) • x) y = r * E x y
  alt : ∀ x y : V, E y x = -E x y
  compat : ∀ x y : V, E (Complex.I • x) (Complex.I • y) = E x y

namespace IsAlternatingCompatible

variable {E : V → V → ℝ} (hE : IsAlternatingCompatible E)

include hE

theorem add_right (x y z : V) : E x (y + z) = E x y + E x z := by
  rw [hE.alt, hE.add_left, hE.alt x y, hE.alt x z]
  ring

theorem smul_right (r : ℝ) (x y : V) : E x ((r : ℂ) • y) = r * E x y := by
  rw [hE.alt, hE.smul_left, hE.alt x y]
  ring

theorem neg_left (x y : V) : E (-x) y = -E x y := by
  have h : ((-1 : ℝ) : ℂ) • x = -x := by
    push_cast
    rw [neg_one_smul]
  rw [← h, hE.smul_left]
  ring

theorem smul_I_left (x y : V) : E (Complex.I • (Complex.I • x)) y = -E x y := by
  have h : Complex.I • (Complex.I • x) = -x := by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rw [h, hE.neg_left]

end IsAlternatingCompatible

/-- The Hermitian form of an alternating compatible form. -/
noncomputable def hermitianOfAlternating (E : V → V → ℝ) (x y : V) : ℂ :=
  ((E (Complex.I • x) y : ℝ) : ℂ) + Complex.I * ((E x y : ℝ) : ℂ)

theorem hermitianOfAlternating_re (E : V → V → ℝ) (x y : V) :
    (hermitianOfAlternating E x y).re = E (Complex.I • x) y := by
  simp [hermitianOfAlternating]

theorem hermitianOfAlternating_im (E : V → V → ℝ) (x y : V) :
    (hermitianOfAlternating E x y).im = E x y := by
  simp [hermitianOfAlternating]

namespace IsAlternatingCompatible

variable {E : V → V → ℝ} (hE : IsAlternatingCompatible E)

include hE

theorem hermitian_add_left (x y z : V) :
    hermitianOfAlternating E (x + y) z
      = hermitianOfAlternating E x z + hermitianOfAlternating E y z := by
  simp only [hermitianOfAlternating, smul_add, hE.add_left]
  push_cast
  ring

theorem hermitian_real_smul (r : ℝ) (x y : V) :
    hermitianOfAlternating E ((r : ℂ) • x) y = (r : ℂ) * hermitianOfAlternating E x y := by
  have hcomm : Complex.I • ((r : ℂ) • x) = (r : ℂ) • (Complex.I • x) := by
    rw [smul_smul, smul_smul, mul_comm]
  simp only [hermitianOfAlternating, hcomm, hE.smul_left]
  push_cast
  ring

theorem hermitian_I_smul (x y : V) :
    hermitianOfAlternating E (Complex.I • x) y = Complex.I * hermitianOfAlternating E x y := by
  simp only [hermitianOfAlternating, hE.smul_I_left]
  push_cast
  rw [Complex.ext_iff]
  constructor <;> simp

/-- **Complex homogeneity.** -/
theorem hermitian_smul_left (a : ℂ) (x y : V) :
    hermitianOfAlternating E (a • x) y = a * hermitianOfAlternating E x y := by
  have hdecomp : a • x = ((a.re : ℂ)) • x + ((a.im : ℂ)) • (Complex.I • x) := by
    rw [smul_smul, ← add_smul]
    congr 1
    rw [Complex.ext_iff]
    constructor <;> simp
  set H := hermitianOfAlternating E x y with hH
  rw [hdecomp, hE.hermitian_add_left, hE.hermitian_real_smul, hE.hermitian_real_smul,
    hE.hermitian_I_smul]
  have hre : ((a.re : ℂ)) + ((a.im : ℂ)) * Complex.I = a := Complex.re_add_im a
  conv_rhs => rw [← hre]
  ring

/-- **Hermitian symmetry.** -/
theorem hermitian_symm (x y : V) :
    hermitianOfAlternating E y x = star (hermitianOfAlternating E x y) := by
  have hre : E (Complex.I • y) x = E (Complex.I • x) y := by
    have h1 : E (Complex.I • y) x = E (Complex.I • (Complex.I • y)) (Complex.I • x) :=
      (hE.compat _ _).symm
    rw [h1, hE.smul_I_left, hE.alt]
    ring
  simp only [hermitianOfAlternating, hre, hE.alt x y, Complex.star_def]
  push_cast
  rw [Complex.ext_iff]
  constructor <;> simp

omit hE in
theorem hermitian_self_re (x : V) :
    (hermitianOfAlternating E x x).re = E (Complex.I • x) x :=
  hermitianOfAlternating_re E x x

/-- **The dictionary.**  An alternating compatible form with positive `E (i x, x)` yields a
positive-definite Hermitian form whose imaginary part is `E` itself. -/
theorem exists_hermitian_of_alternating (hpos : ∀ x : V, x ≠ 0 → 0 < E (Complex.I • x) x) :
    ∃ H : V → V → ℂ,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧
      (∀ (a : ℂ) (x y), H (a • x) y = a * H x y) ∧
      (∀ x y, H y x = star (H x y)) ∧
      (∀ x, x ≠ 0 → 0 < (H x x).re) ∧
      (∀ x y, (H x y).im = E x y) :=
  ⟨hermitianOfAlternating E, hE.hermitian_add_left, hE.hermitian_smul_left, hE.hermitian_symm,
    fun x hx => by rw [hermitianOfAlternating_re E x x]; exact hpos x hx,
    hermitianOfAlternating_im E⟩

end IsAlternatingCompatible

end GaloisForLFunctions.HTGeometry
