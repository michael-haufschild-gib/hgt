import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass

/-!
# Finite Hankel boundary extension as a Krein crossing form

At a singular finite Hankel face, the monic null polynomial is lightlike for the moment bilinear
form.  The first affine extension coordinate is exactly its crossing form against multiplication
by `X`.  This identifies the missing orientation as null-cone spectral-flow data rather than
ordinary square positivity.
-/

open Matrix Polynomial

namespace HTGeometry

noncomputable section

/-- Crossing form of multiplication by `X` on the canonical monic null polynomial. -/
def finiteHankelBoundaryNullCrossingForm
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  momentInner s (finiteHankelNullMonicPolynomial c)
    (X * finiteHankelNullMonicPolynomial c)


/-- **Null-cone law.**  A monic polynomial selected by a singular Hankel face is lightlike for
the moment bilinear form. -/
theorem finiteHankelBoundaryNullSelf_eq_zero
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentInner s (finiteHankelNullMonicPolynomial c)
      (finiteHankelNullMonicPolynomial c) = 0 := by
  apply momentInner_finiteHankelNullMonicPolynomial_eq_zero_of_kernel hc
  rw [finiteHankelNullMonicPolynomial_natDegree c hlast]
  omega

/-- **Krein crossing identity.**  The canonical first extension coordinate is the crossing form
of multiplication by `X` on the lightlike monic null polynomial. -/
theorem finiteHankelBoundaryNullCrossingForm_eq_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelBoundaryNullCrossingForm s c =
      finiteHankelBoundaryMonicRemainder s c := by
  rw [finiteHankelBoundaryNullCrossingForm, momentInner_def,
    finiteHankelBoundaryMonicRemainder_eq_shiftedSquare s c hc hlast]
  congr 1
  ring

/-- Extension orientation is exactly positive Krein crossing type on the canonical null line. -/
theorem finiteHankelBoundaryMonicRemainder_pos_iff_nullCrossingForm_pos
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < finiteHankelBoundaryMonicRemainder s c ↔
      0 < finiteHankelBoundaryNullCrossingForm s c := by
  rw [finiteHankelBoundaryNullCrossingForm_eq_monicRemainder s c hc hlast]

/-- **Finite-face Krein class.**  Singular incidence produces a lightlike monic vector, and its
crossing slope is precisely the projective affine extension class. -/
theorem finiteHankelBoundary_kreinCrossingClass
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    momentInner s (finiteHankelNullMonicPolynomial c)
        (finiteHankelNullMonicPolynomial c) = 0 ∧
      finiteHankelBoundaryNullCrossingForm s c =
        finiteHankelBoundaryMonicRemainder s c :=
  ⟨finiteHankelBoundaryNullSelf_eq_zero c hc hlast,
    finiteHankelBoundaryNullCrossingForm_eq_monicRemainder s c hc hlast⟩

end

end HTGeometry
