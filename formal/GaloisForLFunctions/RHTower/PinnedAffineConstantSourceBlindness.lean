import GaloisForLFunctions.RHTower.PinnedAffineDefectQuotient

/-!
# Constant and prime sources activate the pinned-affine quotient everywhere

The pinned-affine defect quotient is a genuine universal obstruction object, but its proposed
arithmetic source map must still pass a location-sensitivity test.  This file performs that test on
the smallest canonical local presentation.

For the one-slot presentation `A=X^m`, the Fitting boundary of the constant defect `C(c)` is exactly
the constant divisor jet `C(c) mod X^m`.  When `m>0`, every nonzero `c` gives a nonzero boundary and
hence a nonzero pinned-affine quotient class.  In particular the obvious prime evaluation
`c=p^(-rho)` is nonzero for every positive base and every complex point `rho`.

Therefore raw prime evaluation activates the quotient everywhere: no zero hypothesis, orbit shape,
or critical-line condition is involved.  Quotient nonvanishing is a valid non-affineness witness but
is not by itself an RH detector.  A completed arithmetic attachment must contain a new compatibility
or cancellation law beyond pointwise prime evaluation.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial Complex
open scoped BigOperators

/-- The canonical one-slot presentation of a divisor of order `m`. -/
def oneSlotTorsionPresentation (R : Type*) [CommRing R] (m : ℕ) :
    Matrix (Fin 1) (Fin 1) (Polynomial R) :=
  Matrix.of ![![(X : Polynomial R) ^ m]]

/-- A constant transverse source in the one-slot presentation. -/
def oneSlotConstantDefect (R : Type*) [CommRing R] (c : R) :
    Matrix (Fin 1) (Fin 1) (Polynomial R) :=
  Matrix.of ![![Polynomial.C c]]

theorem oneSlotTorsionPresentation_det (R : Type*) [CommRing R] (m : ℕ) :
    (oneSlotTorsionPresentation R m).det = (X : Polynomial R) ^ m := by
  rw [oneSlotTorsionPresentation, Matrix.det_fin_one]
  rfl

/-- Exact boundary formula: the constant defect maps to the constant local divisor jet. -/
theorem fittingBoundaryClass_oneSlotConstant_eq
    (R : Type*) [CommRing R] (m : ℕ) (c : R) :
    fittingBoundaryClass m (oneSlotTorsionPresentation R m) (oneSlotConstantDefect R c) =
      jetClass R m (Polynomial.C c) := by
  simp [fittingBoundaryClass, fittingBoundaryTrace, oneSlotTorsionPresentation,
    oneSlotConstantDefect, Matrix.adjugate_fin_one, Matrix.trace_fin_one]

/-- The descended quotient boundary has the same exact constant-jet value. -/
theorem pinnedAffineBoundaryHom_oneSlotConstant_eq
    (R : Type*) [CommRing R] (m : ℕ) (c : R) :
    pinnedAffineBoundaryHom m (oneSlotTorsionPresentation R m)
        (oneSlotTorsionPresentation_det R m)
        (QuotientAddGroup.mk (oneSlotConstantDefect R c) :
          PinnedAffineDefectQuotient m (oneSlotTorsionPresentation R m)) =
      jetClass R m (Polynomial.C c) := by
  rw [pinnedAffineBoundaryHom_mk, fittingBoundaryClass_oneSlotConstant_eq]

/-- Every nonzero constant source at positive divisor order has nonzero Fitting boundary. -/
theorem fittingBoundaryClass_oneSlotConstant_ne_zero
    (R : Type*) [CommRing R] {m : ℕ} (hm : 0 < m) {c : R} (hc : c ≠ 0) :
    fittingBoundaryClass m (oneSlotTorsionPresentation R m) (oneSlotConstantDefect R c) ≠ 0 := by
  rw [fittingBoundaryClass_ne_zero_iff_exists_coeff_lt_ne_zero]
  refine ⟨0, hm, ?_⟩
  simp [fittingBoundaryTrace, oneSlotTorsionPresentation, oneSlotConstantDefect,
    Matrix.adjugate_fin_one, Matrix.trace_fin_one, hc]

/-- Every nonzero constant source survives modulo all pinned affine realizations. -/
theorem oneSlotConstant_pinnedAffineClass_ne_zero
    (R : Type*) [CommRing R] {m : ℕ} (hm : 0 < m) {c : R} (hc : c ≠ 0) :
    (QuotientAddGroup.mk (oneSlotConstantDefect R c) :
      PinnedAffineDefectQuotient m (oneSlotTorsionPresentation R m)) ≠ 0 := by
  apply pinnedAffineClass_ne_zero_of_fittingBoundaryClass_ne_zero
    m (oneSlotTorsionPresentation R m) (oneSlotConstantDefect R c)
    (oneSlotTorsionPresentation_det R m)
  exact fittingBoundaryClass_oneSlotConstant_ne_zero R hm hc

/-- The obvious prime-evaluation source class at a point `rho`. -/
def primeEvaluationPinnedAffineClass (m p : ℕ) (rho : ℂ) :
    PinnedAffineDefectQuotient m (oneSlotTorsionPresentation ℂ m) :=
  QuotientAddGroup.mk (oneSlotConstantDefect ℂ ((p : ℂ) ^ (-rho)))

/-- **All-point activation.**  Prime evaluation gives a nonzero quotient class at every complex
point.  No vanishing or critical-line hypothesis is used. -/
theorem primeEvaluationPinnedAffineClass_ne_zero {m : ℕ} (hm : 0 < m)
    {p : ℕ} (hp : 0 < p) (rho : ℂ) :
    primeEvaluationPinnedAffineClass m p rho ≠ 0 := by
  apply oneSlotConstant_pinnedAffineClass_ne_zero ℂ hm
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne'))

/-- Prime specialization of the all-point activation theorem. -/
theorem prime_primeEvaluationPinnedAffineClass_ne_zero {m : ℕ} (hm : 0 < m)
    {p : ℕ} (hp : p.Prime) (rho : ℂ) :
    primeEvaluationPinnedAffineClass m p rho ≠ 0 :=
  primeEvaluationPinnedAffineClass_ne_zero hm hp.pos rho

/-! ## Finite constant-source collapse -/

/-- A finite family of constant sources enters the one-slot quotient only through its scalar sum. -/
def finiteConstantSourcePinnedAffineClass {ι : Type*}
    (R : Type*) [CommRing R] (m : ℕ) (s : Finset ι) (c : ι → R) :
    PinnedAffineDefectQuotient m (oneSlotTorsionPresentation R m) :=
  QuotientAddGroup.mk (oneSlotConstantDefect R (∑ i ∈ s, c i))

/-- **Exact finite-source collapse.**  At positive divisor order, a finite constant-source family
has zero quotient class exactly when its single scalar total is zero.  All source labels are lost. -/
theorem finiteConstantSourcePinnedAffineClass_eq_zero_iff {ι : Type*}
    (R : Type*) [CommRing R] {m : ℕ} (hm : 0 < m) (s : Finset ι) (c : ι → R) :
    finiteConstantSourcePinnedAffineClass R m s c = 0 ↔ ∑ i ∈ s, c i = 0 := by
  constructor
  · intro hzero
    by_contra hsum
    exact oneSlotConstant_pinnedAffineClass_ne_zero R hm hsum hzero
  · intro hsum
    rw [finiteConstantSourcePinnedAffineClass, QuotientAddGroup.eq_zero_iff, hsum]
    have hdef : oneSlotConstantDefect R 0 = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [oneSlotConstantDefect]
    rw [hdef]
    exact (pinnedAffineDefects m (oneSlotTorsionPresentation R m)).zero_mem

/-- The two-prime pointwise source class with freely supplied coefficients. -/
def twoPrimeEvaluationPinnedAffineClass (m p q : ℕ) (a b : ℂ) (rho : ℂ) :
    PinnedAffineDefectQuotient m (oneSlotTorsionPresentation ℂ m) :=
  QuotientAddGroup.mk
    (oneSlotConstantDefect ℂ (a * (p : ℂ) ^ (-rho) + b * (q : ℂ) ^ (-rho)))

/-- A two-prime constant-source class vanishes exactly when its scalar evaluation sum vanishes. -/
theorem twoPrimeEvaluationPinnedAffineClass_eq_zero_iff {m : ℕ} (hm : 0 < m)
    (p q : ℕ) (a b rho : ℂ) :
    twoPrimeEvaluationPinnedAffineClass m p q a b rho = 0 ↔
      a * (p : ℂ) ^ (-rho) + b * (q : ℂ) ^ (-rho) = 0 := by
  constructor
  · intro hzero
    by_contra hsum
    exact oneSlotConstant_pinnedAffineClass_ne_zero ℂ hm hsum hzero
  · intro hsum
    rw [twoPrimeEvaluationPinnedAffineClass, QuotientAddGroup.eq_zero_iff, hsum]
    have hdef : oneSlotConstantDefect ℂ 0 = 0 := by
      ext i j
      fin_cases i
      fin_cases j
      simp [oneSlotConstantDefect]
    rw [hdef]
    exact (pinnedAffineDefects m (oneSlotTorsionPresentation ℂ m)).zero_mem

/-- **Pointwise-tuned cancellation is vacuous.**  At every point and for every two positive bases,
there are nonzero coefficients—chosen from that point—which cancel the quotient class. -/
theorem twoPrimeEvaluation_tunedCancellation {m : ℕ} (hm : 0 < m)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (rho : ℂ) :
    let a := (q : ℂ) ^ (-rho)
    let b := -((p : ℂ) ^ (-rho))
    a ≠ 0 ∧ b ≠ 0 ∧ twoPrimeEvaluationPinnedAffineClass m p q a b rho = 0 := by
  dsimp
  have hp0 : (p : ℂ) ^ (-rho) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne'))
  have hq0 : (q : ℂ) ^ (-rho) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hq.ne'))
  refine ⟨hq0, neg_ne_zero.mpr hp0, ?_⟩
  rw [twoPrimeEvaluationPinnedAffineClass_eq_zero_iff hm]
  ring

end RHTower
