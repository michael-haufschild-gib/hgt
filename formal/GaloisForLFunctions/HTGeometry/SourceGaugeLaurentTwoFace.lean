import Mathlib.Algebra.Polynomial.Laurent

/-!
# The two-face Laurent normalization law for residual source gauges

A bare translation source forgets periodic gauge directions.  Its finite Fourier-character
shadow is a Laurent polynomial on the quotient cylinder.  The two compactifying faces impose
genuinely opposite conditions: extension through zero kills negative modes, while extension
through infinity kills positive modes.

This file proves the exact local law.  Either face alone retains a nonconstant gauge, inversion
exchanges the faces, and simultaneous extension through both faces leaves precisely the scalar
gauge.  After scalar normalization the joint gauge is zero.  Thus reconstruction does not come
from further postprocessing of one source face; it comes from a transverse counterface.

The Laurent theorem is classical algebra.  Its role is to constrain, not establish, the proposed
HT-specific self-dual Tate/Fredholm obstruction field.
-/

open LaurentPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- A finite Laurent gauge extends through the zero face when it has no negative modes. -/
def LaurentRegularAtZero {R : Type*} [Semiring R]
    (f : R[T;T⁻¹]) : Prop :=
  ∀ n : ℤ, n < 0 → f n = 0

/-- A finite Laurent gauge extends through the infinity face when it has no positive modes. -/
def LaurentRegularAtInfinity {R : Type*} [Semiring R]
    (f : R[T;T⁻¹]) : Prop :=
  ∀ n : ℤ, 0 < n → f n = 0

/-- A Laurent character extends through zero exactly when its weight is nonnegative. -/
theorem laurentRegularAtZero_T_iff
    {R : Type*} [Semiring R] [Nontrivial R] (n : ℤ) :
    LaurentRegularAtZero (T n : R[T;T⁻¹]) ↔ 0 ≤ n := by
  constructor
  · intro h
    by_contra hn
    have hnneg : n < 0 := lt_of_not_ge hn
    have := h n hnneg
    simp at this
  · intro hn m hm
    have hne : n ≠ m := by omega
    simp [T_apply, hne]

/-- A Laurent character extends through infinity exactly when its weight is nonpositive. -/
theorem laurentRegularAtInfinity_T_iff
    {R : Type*} [Semiring R] [Nontrivial R] (n : ℤ) :
    LaurentRegularAtInfinity (T n : R[T;T⁻¹]) ↔ n ≤ 0 := by
  constructor
  · intro h
    by_contra hn
    have hnpos : 0 < n := lt_of_not_ge hn
    have := h n hnpos
    simp at this
  · intro hn m hm
    have hne : n ≠ m := by omega
    simp [T_apply, hne]

/-- Laurent inversion exchanges zero-face and infinity-face regularity. -/
theorem laurentRegularAtZero_invert_iff
    {R : Type*} [CommSemiring R] (f : R[T;T⁻¹]) :
    LaurentRegularAtZero (invert f) ↔ LaurentRegularAtInfinity f := by
  constructor
  · intro h n hn
    have hneg : -n < 0 := by omega
    simpa using h (-n) hneg
  · intro h n hn
    have hpos : 0 < -n := by omega
    simpa using h (-n) hpos

/-- Laurent inversion exchanges infinity-face and zero-face regularity. -/
theorem laurentRegularAtInfinity_invert_iff
    {R : Type*} [CommSemiring R] (f : R[T;T⁻¹]) :
    LaurentRegularAtInfinity (invert f) ↔ LaurentRegularAtZero f := by
  simp only [← laurentRegularAtZero_invert_iff (invert f), involutive_invert f]

/-- A finite Laurent gauge extending through both compactifying faces is constant. -/
theorem laurent_eq_C_coeff_zero_of_biFace
    {R : Type*} [Semiring R] (f : R[T;T⁻¹])
    (hzero : LaurentRegularAtZero f)
    (hinfinity : LaurentRegularAtInfinity f) :
    f = C (f 0) := by
  ext n
  rcases lt_trichotomy n 0 with hn | hn | hn
  · rw [hzero n hn]
    simp [C_apply, ne_of_lt hn]
  · subst n
    simp
  · rw [hinfinity n hn]
    simp [C_apply, ne_of_gt hn]

/-- Exact bi-face intersection law: simultaneous regularity is precisely the scalar stratum. -/
theorem laurent_biFace_iff_eq_C
    {R : Type*} [Semiring R] (f : R[T;T⁻¹]) :
    LaurentRegularAtZero f ∧ LaurentRegularAtInfinity f ↔
      ∃ c : R, f = C c := by
  constructor
  · rintro ⟨hzero, hinfinity⟩
    exact ⟨f 0, laurent_eq_C_coeff_zero_of_biFace f hzero hinfinity⟩
  · rintro ⟨c, rfl⟩
    constructor <;> intro n hn <;> simp [C_apply, ne_of_lt hn, ne_of_gt hn]

/-- Any inversion-invariant condition contained in one Laurent face collapses to the scalar
stratum.  Thus a nontrivial orientation-invariant normalization must retain the unordered pair of
opposite faces rather than canonically select either face. -/
theorem laurent_inversionInvariant_zeroSubface_rigid
    {R : Type*} [CommSemiring R]
    (P : R[T;T⁻¹] → Prop)
    (hsubface : ∀ f, P f → LaurentRegularAtZero f)
    (hinversion : ∀ f, P (invert f) ↔ P f)
    (f : R[T;T⁻¹]) (hf : P f) :
    ∃ c : R, f = C c := by
  have hzero : LaurentRegularAtZero f := hsubface f hf
  have hzeroInvert : LaurentRegularAtZero (invert f) :=
    hsubface (invert f) ((hinversion f).2 hf)
  have hinfinity : LaurentRegularAtInfinity f :=
    (laurentRegularAtZero_invert_iff f).mp hzeroInvert
  exact (laurent_biFace_iff_eq_C f).mp ⟨hzero, hinfinity⟩

/-- Opposite-face regularity together with scalar normalization kills the entire finite gauge. -/
theorem laurent_biFace_normalized_eq_zero
    {R : Type*} [Semiring R] (f : R[T;T⁻¹])
    (hzero : LaurentRegularAtZero f)
    (hinfinity : LaurentRegularAtInfinity f)
    (hnormalized : f 0 = 0) :
    f = 0 := by
  rw [laurent_eq_C_coeff_zero_of_biFace f hzero hinfinity, hnormalized]
  exact map_zero C

/-- The zero face alone retains a nonconstant positive mode. -/
theorem laurent_zeroFace_not_rigid
    {R : Type*} [Semiring R] [Nontrivial R] :
    LaurentRegularAtZero (T 1 : R[T;T⁻¹]) ∧
      (T 1 : R[T;T⁻¹]) ≠ C ((T 1 : R[T;T⁻¹]) 0) := by
  constructor
  · exact (laurentRegularAtZero_T_iff 1).2 (by omega)
  · intro h
    have hzero : ((T 1 : R[T;T⁻¹]) 0) = 0 := by simp
    rw [hzero, map_zero] at h
    have hT : (Finsupp.single (1 : ℤ) (1 : R) : ℤ →₀ R) ≠ 0 :=
      Finsupp.single_ne_zero.mpr one_ne_zero
    exact hT h

/-- The infinity face alone retains a nonconstant negative mode. -/
theorem laurent_infinityFace_not_rigid
    {R : Type*} [Semiring R] [Nontrivial R] :
    LaurentRegularAtInfinity (T (-1) : R[T;T⁻¹]) ∧
      (T (-1) : R[T;T⁻¹]) ≠ C ((T (-1) : R[T;T⁻¹]) 0) := by
  constructor
  · exact (laurentRegularAtInfinity_T_iff (-1)).2 (by omega)
  · intro h
    have hzero : ((T (-1) : R[T;T⁻¹]) 0) = 0 := by simp
    rw [hzero, map_zero] at h
    have hT : (Finsupp.single (-1 : ℤ) (1 : R) : ℤ →₀ R) ≠ 0 :=
      Finsupp.single_ne_zero.mpr one_ne_zero
    exact hT h

end

end GaloisForLFunctions
