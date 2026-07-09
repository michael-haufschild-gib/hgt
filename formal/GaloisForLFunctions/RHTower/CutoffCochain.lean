/-
The cross-boundary cochain of a cutoff, and the escape from the pinned-germ collapse.

A **cutoff** is an idempotent `e` in an operator ring `E` (`e² = e`): the projection onto the "kept"
region of a two-region split (inside/outside a radius `|x| = λ`). The **cross-boundary cochain** of
an operator `a` is the lower corner

  `crossBoundary e a = (1 − e) · a · e`

— the part of `a·(kept)` that lands outside the cutoff: the mass `a` pushes across the boundary.

Three facts organize the whole picture.

* **Semicommutator (compression) identity** (`compression_semicommutator`): the compression
  `c(a) = e·a·e` fails to be multiplicative by exactly the product of the two opposite corners,
  `e(ab)e − (eae)(ebe) = (upper corner of a)·(lower corner of b)`. This is the Toeplitz–Hankel
  law: compressions multiply up to a boundary correction.

* **The collapse** (`crossBoundary_eq_zero_of_commute`, `crossBoundary_smul_one`): if `a` commutes
  with the cutoff `e` — in particular if `a` is a **central scalar** — both corners vanish. At a
  pinned germ the prime action `σ_p` is multiplication by the unit `p^(−s)`, a scalar, hence central,
  hence commutes with every cutoff: its cross-boundary cochain is `0`. This is the single reason
  behind the three earlier collapses (the free reference is a coboundary; the unit has order 0; the
  commutator with the presentation is fake) — a **germ-local** action is central, so it never crosses
  a boundary.

* **The escape** (`exists_nonfake_crossBoundary`): a cutoff-**crossing** action — one that does not
  commute with `e` — has a nonzero cross-boundary cochain, and that cochain can carry a **nonzero
  Fitting boundary class** on a torsion seam presentation `det A = Xᵐ`. Being non-fake, it is (by
  `nonzero_fittingBoundaryClass_not_commutator`) **not** a commutator with the presentation:
  `exists_nonfake_crossBoundary_not_commutator`. The cross-boundary cochain is the object that
  escapes the pinned-germ no-go — and it exists only for a non-central, boundary-crossing action.
-/
import GaloisForLFunctions.RHTower.SoninSeamDefect

noncomputable section

namespace RHTower

open Matrix Polynomial

/-! ### §1 The cross-boundary cochain and the compression -/

variable {E : Type*} [Ring E]

/-- The lower cross-boundary corner `(1 − e)·a·e`: the mass `a` pushes out of the cutoff `e`. -/
def crossBoundary (e a : E) : E := (1 - e) * a * e

/-- The upper cross-boundary corner `e·a·(1 − e)`: the mass `a` pulls into the cutoff. -/
def upperBoundary (e a : E) : E := e * a * (1 - e)

/-- The compression of `a` to the cutoff `e`. -/
def compression (e a : E) : E := e * a * e

/-- The cross-boundary cochain is additive in the operator. -/
theorem crossBoundary_add (e a b : E) :
    crossBoundary e (a + b) = crossBoundary e a + crossBoundary e b := by
  simp only [crossBoundary, mul_add, add_mul]

/-- The cross-boundary cochain kills the identity: a cutoff does not cross itself. -/
theorem crossBoundary_one {e : E} (he : IsIdempotentElem e) : crossBoundary e 1 = 0 := by
  have hee : e * e = e := he
  rw [crossBoundary, mul_one, sub_mul, one_mul, hee, sub_self]

/-- **The cross-boundary cochain is a corner of the inner derivation `[e, a]`.**  Writing the
commutator with the cutoff as `[e,a] = e·a − a·e`, the lower corner is `(1−e)·a·e = −(1−e)·[e,a]`:
the cross-boundary cochain measures the failure of `a` to commute with the cutoff, read from outside.
It is a commutator with the **cutoff** `e`, in contrast with the fake commutator with the divisor
**presentation** `A` (`SoninSeamDefect`). -/
theorem crossBoundary_eq_corner_commutator {e : E} (he : IsIdempotentElem e) (a : E) :
    crossBoundary e a = -((1 - e) * (e * a - a * e)) := by
  have hone : (1 - e) * e = 0 := by rw [sub_mul, one_mul, (he : e * e = e), sub_self]
  have h : (1 - e) * (e * a - a * e) = (1 - e) * e * a - (1 - e) * a * e := by noncomm_ring
  rw [crossBoundary, h, hone, zero_mul, zero_sub, neg_neg]

/-- **Same-direction crossings are square-zero.**  The product of two lower cross-boundary cochains
is `0`: `((1−e)·a·e)·((1−e)·b·e) = 0`, because `e·(1−e) = 0`.  Mass cannot cross out twice in a row;
the cross-boundary cochains span a square-zero set — the first-order (defect) structure. -/
theorem crossBoundary_mul_crossBoundary (e a b : E) (he : IsIdempotentElem e) :
    crossBoundary e a * crossBoundary e b = 0 := by
  have hee : e * e = e := he
  have h : ((1 - e) * a * e) * ((1 - e) * b * e) = (1 - e) * a * (e * (1 - e)) * b * e := by
    noncomm_ring
  rw [crossBoundary, crossBoundary, h, show e * (1 - e) = 0 by rw [mul_sub, mul_one, hee, sub_self]]
  noncomm_ring

/-! ### §1b The cross-boundary cochain is intrinsically non-commutative and traceless -/

/-- **The cross-boundary cochain vanishes identically in a commutative ring.**  If the operator ring
is commutative, `(1 − e)·a·e = a·((1 − e)·e) = a·(e − e²) = 0` for every `a` and every idempotent `e`.
The cochain carries content only in a genuinely **non-commutative** operator algebra — it needs the
action `a` not to commute with the cutoff `e`. -/
theorem crossBoundary_eq_zero_comm {R : Type*} [CommRing R] {e : R} (he : IsIdempotentElem e) (a : R) :
    crossBoundary e a = 0 := by
  have hee : e * e = e := he
  have h : crossBoundary e a = a * ((1 - e) * e) := by rw [crossBoundary]; ring
  rw [h, sub_mul, one_mul, hee, sub_self, mul_zero]

/-- **The cross-boundary cochain is traceless.**  For a matrix idempotent `e`, the trace of
`(1 − e)·a·e` is `0`: by cyclicity it equals `tr((e·(1 − e))·a) = tr(0·a) = 0`.  The cochain lives
entirely in the traceless part of the operator algebra, orthogonal to every trace/abelian class. -/
theorem crossBoundary_trace_zero {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    {e : Matrix n n R} (he : IsIdempotentElem e) (a : Matrix n n R) :
    (crossBoundary e a).trace = 0 := by
  have hee : e * e = e := he
  rw [crossBoundary, Matrix.trace_mul_comm ((1 - e) * a) e, ← Matrix.mul_assoc,
    show e * (1 - e) = 0 by rw [mul_sub, mul_one, hee, sub_self], Matrix.zero_mul, Matrix.trace_zero]

/-! ### §2 The semicommutator identity: compressions multiply up to a boundary correction -/

/-- **The Toeplitz–Hankel semicommutator identity.**  The compression `c(a) = e·a·e` is multiplicative
up to the product of opposite corners: `e(ab)e − (eae)(ebe) = (e·a·(1−e))·((1−e)·b·e)`. -/
theorem compression_semicommutator {e : E} (he : IsIdempotentElem e) (a b : E) :
    e * (a * b) * e - (e * a * e) * (e * b * e) = (e * a * (1 - e)) * ((1 - e) * b * e) := by
  have hee : e * e = e := he
  have h1e : (1 - e) * (1 - e) = 1 - e := he.one_sub
  have lhs_eq : (e * a * e) * (e * b * e) = e * a * e * b * e := by
    have : (e * a * e) * (e * b * e) = e * a * (e * e) * b * e := by noncomm_ring
    rw [this, hee]
  have rhs_eq : (e * a * (1 - e)) * ((1 - e) * b * e) = e * a * b * e - e * a * e * b * e := by
    have h1 : (e * a * (1 - e)) * ((1 - e) * b * e) = e * a * ((1 - e) * (1 - e)) * b * e := by
      noncomm_ring
    rw [h1, h1e]; noncomm_ring
  rw [lhs_eq, rhs_eq]; noncomm_ring

/-- The compression multiplies exactly when it is corrected by the boundary product:
`c(ab) = c(a)·c(b) + upper(a)·lower(b)`. -/
theorem compression_mul {e : E} (he : IsIdempotentElem e) (a b : E) :
    compression e (a * b) = compression e a * compression e b + upperBoundary e a * crossBoundary e b :=
  by rw [compression, compression, compression, upperBoundary, crossBoundary,
    ← compression_semicommutator he a b]; abel

/-! ### §3 The collapse: a boundary-commuting (central) action crosses nothing -/

/-- **The pinned-germ collapse.**  If `a` commutes with the cutoff `e`, its cross-boundary cochain
vanishes: a boundary-preserving action pushes no mass across. -/
theorem crossBoundary_eq_zero_of_commute {e a : E} (he : IsIdempotentElem e) (hcomm : a * e = e * a) :
    crossBoundary e a = 0 := by
  have hee : e * e = e := he
  have h : crossBoundary e a = a * e - e * a * e := by rw [crossBoundary]; noncomm_ring
  rw [h, ← hcomm, mul_assoc a e e, hee, sub_self]

/-- The upper corner also vanishes for a boundary-commuting action. -/
theorem upperBoundary_eq_zero_of_commute {e a : E} (he : IsIdempotentElem e) (hcomm : a * e = e * a) :
    upperBoundary e a = 0 := by
  have hee : e * e = e := he
  have h : upperBoundary e a = e * a - e * a * e := by rw [upperBoundary]; noncomm_ring
  rw [h, mul_assoc e a e, hcomm, ← mul_assoc, hee, sub_self]

/-- **A central scalar crosses no boundary.**  The germ-local prime action is multiplication by the
unit `p^(−s)`, a scalar `c·1`; a scalar commutes with every cutoff, so its cross-boundary cochain is
`0`.  This is the algebraic root of the freeness / unit / commutator collapses: a germ-local action
is central. -/
theorem crossBoundary_smul_one {e : E} (he : IsIdempotentElem e) (c : E) (hc : c * e = e * c) :
    crossBoundary e (c * 1) = 0 := by
  rw [mul_one]; exact crossBoundary_eq_zero_of_commute he hc

/-! ### §4 The escape: a cutoff-crossing cochain is non-fake -/

/-- **The cross-boundary escape exists.**  There is a cutoff `e` (idempotent), a boundary-crossing
action `σ`, and a torsion seam presentation `A` with `det A = Xᵐ`, whose cross-boundary cochain
`(1 − e)·σ·e` has a **nonzero** Fitting boundary class in `R[X]/(Xᵐ)`.  A boundary-crossing action
sources a genuine pinned divisor obstruction — the object every pinned-germ (central) action cannot
produce. -/
theorem exists_nonfake_crossBoundary (m : ℕ) (hm : 0 < m) :
    ∃ (e σ A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ A.det = (X : Polynomial ℚ) ^ m ∧
      fittingBoundaryClass m A (crossBoundary e σ) ≠ 0 := by
  refine ⟨!![1, 0; 0, 0], !![0, 0; 1, 0], !![(X : Polynomial ℚ) ^ m, 1; 0, 1], ?_, ?_, ?_⟩
  · show _ * _ = _
    rw [Matrix.mul_fin_two]; norm_num
  · rw [Matrix.det_fin_two]; simp
  · have hsub : (!![(1:Polynomial ℚ),0;0,1] - !![(1:Polynomial ℚ),0;0,0])
        = !![(0:Polynomial ℚ),0;0,1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hΔ : crossBoundary (!![(1 : Polynomial ℚ), 0; 0, 0]) (!![0, 0; 1, 0])
        = !![0, 0; 1, 0] := by
      rw [crossBoundary, Matrix.one_fin_two, hsub, Matrix.mul_fin_two, Matrix.mul_fin_two]
      norm_num
    have hadj : (!![(X:Polynomial ℚ)^m, 1; 0, 1]).adjugate = !![1, -1; 0, (X:Polynomial ℚ)^m] := by
      rw [Matrix.adjugate_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
    have htr : (!![(1:Polynomial ℚ), -1; 0, (X:Polynomial ℚ)^m] * !![0,0;1,0]).trace = -1 := by
      rw [Matrix.mul_fin_two, Matrix.trace_fin_two]; norm_num
    rw [hΔ, fittingBoundaryClass, fittingBoundaryTrace, hadj, htr]
    intro hzero
    rw [jetClass, Ideal.Quotient.eq_zero_iff_mem, jetIdeal, Ideal.mem_span_singleton] at hzero
    obtain ⟨c, hc⟩ := hzero
    have hco := congrArg (fun p => Polynomial.coeff p 0) hc
    simp only [Polynomial.coeff_neg, Polynomial.coeff_one, if_true,
      Polynomial.coeff_X_pow_mul'] at hco
    rw [if_neg (by omega : ¬ (m ≤ 0))] at hco
    norm_num at hco

/-- **The nonfake cutoff witness is genuinely crossing.**  Its action cannot
commute with the cutoff: otherwise the cross-boundary cochain would vanish by the
pinned-germ collapse. -/
theorem exists_nonfake_crossBoundary_not_commute (m : ℕ) (hm : 0 < m) :
    ∃ (e σ A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ σ * e ≠ e * σ ∧ A.det = (X : Polynomial ℚ) ^ m ∧
      fittingBoundaryClass m A (crossBoundary e σ) ≠ 0 := by
  obtain ⟨e, σ, A, he, hdet, hclass⟩ := exists_nonfake_crossBoundary m hm
  have hDelta_ne_zero : crossBoundary e σ ≠ 0 := by
    intro hzero
    apply hclass
    rw [hzero, fittingBoundaryClass, fittingBoundaryTrace]
    simp [jetClass]
  have hnotcomm : σ * e ≠ e * σ := by
    intro hcomm
    exact hDelta_ne_zero (crossBoundary_eq_zero_of_commute he hcomm)
  exact ⟨e, σ, A, he, hnotcomm, hdet, hclass⟩

/-- **The escape is genuinely outside the commutator no-go.**  The non-fake cross-boundary cochain
of §4 is, being of nonzero Fitting boundary class, **not** a commutator with the presentation `A`
(`nonzero_fittingBoundaryClass_not_commutator`) — it escapes the pinned commutator collapse. -/
theorem exists_nonfake_crossBoundary_not_commutator (m : ℕ) (hm : 0 < m) :
    ∃ (e σ A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ A.det = (X : Polynomial ℚ) ^ m ∧
      fittingBoundaryClass m A (crossBoundary e σ) ≠ 0 ∧
      ¬ ∃ τ : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
          crossBoundary e σ = commutatorDefect A τ := by
  obtain ⟨e, σ, A, he, hdet, hclass⟩ := exists_nonfake_crossBoundary m hm
  exact ⟨e, σ, A, he, hdet, hclass, nonzero_fittingBoundaryClass_not_commutator m hclass⟩

/-- **The cross-boundary escape is outside the right fake class.**  The same explicit
cutoff-crossing cochain whose Fitting boundary is nonzero cannot be written as
`A H + X^m K`.  This is the concrete cutoff version of
`Delta_p ∉ A End + (X^m)`. -/
theorem exists_crossBoundary_not_right_factor_mod_X_pow (m : ℕ) (hm : 0 < m) :
    ∃ (e σ A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ A.det = (X : Polynomial ℚ) ^ m ∧
      fittingBoundaryClass m A (crossBoundary e σ) ≠ 0 ∧
      ¬ ∃ H K : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        crossBoundary e σ = A * H + ((X : Polynomial ℚ) ^ m) • K := by
  obtain ⟨e, σ, A, he, hdet, hclass⟩ := exists_nonfake_crossBoundary m hm
  exact ⟨e, σ, A, he, hdet, hclass,
    nonzero_fittingBoundaryClass_obstructs_right_factor_mod_X_pow m hdet hclass⟩

/-- **The surviving cutoff witness is both noncentral and nonfake.**  It crosses the
cutoff and is outside the right fake class `A End + (X^m)`. -/
theorem exists_crossing_crossBoundary_not_right_factor_mod_X_pow (m : ℕ) (hm : 0 < m) :
    ∃ (e σ A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ σ * e ≠ e * σ ∧ A.det = (X : Polynomial ℚ) ^ m ∧
      fittingBoundaryClass m A (crossBoundary e σ) ≠ 0 ∧
      ¬ ∃ H K : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        crossBoundary e σ = A * H + ((X : Polynomial ℚ) ^ m) • K := by
  obtain ⟨e, σ, A, he, hnotcomm, hdet, hclass⟩ := exists_nonfake_crossBoundary_not_commute m hm
  exact ⟨e, σ, A, he, hnotcomm, hdet, hclass,
    nonzero_fittingBoundaryClass_obstructs_right_factor_mod_X_pow m hdet hclass⟩

/-- **The cross-boundary escape is outside the left fake class as well.**  The same
cutoff-crossing cochain cannot be written as `H A + X^m K`; hence it is not a source
basis-change artifact. -/
theorem exists_crossBoundary_not_left_factor_mod_X_pow (m : ℕ) (hm : 0 < m) :
    ∃ (e σ A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ A.det = (X : Polynomial ℚ) ^ m ∧
      fittingBoundaryClass m A (crossBoundary e σ) ≠ 0 ∧
      ¬ ∃ H K : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
        crossBoundary e σ = H * A + ((X : Polynomial ℚ) ^ m) • K := by
  obtain ⟨e, σ, A, he, hdet, hclass⟩ := exists_nonfake_crossBoundary m hm
  exact ⟨e, σ, A, he, hdet, hclass,
    nonzero_fittingBoundaryClass_obstructs_left_factor_mod_X_pow m hdet hclass⟩

/-- **The cross-boundary escape is determinant-transverse.**  For the explicit cutoff
witness, the adjugate trace is not divisible by the pinned divisor equation `X^m`. -/
theorem exists_crossBoundary_not_trace_X_pow_dvd (m : ℕ) (hm : 0 < m) :
    ∃ (e σ A : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)),
      IsIdempotentElem e ∧ A.det = (X : Polynomial ℚ) ^ m ∧
      ¬ (X : Polynomial ℚ) ^ m ∣ fittingBoundaryTrace A (crossBoundary e σ) := by
  obtain ⟨e, σ, A, he, hdet, hclass⟩ := exists_nonfake_crossBoundary m hm
  exact ⟨e, σ, A, he, hdet,
    (fittingBoundaryClass_ne_zero_iff_not_trace_X_pow_dvd m A (crossBoundary e σ)).mp hclass⟩

/-! ### §4b Split torsion presentations are boundary-blind -/

variable {R : Type*} [CommRing R]

/-- The standard two-region cutoff used by the concrete lower-corner witness. -/
def standardCutoff : Matrix (Fin 2) (Fin 2) (Polynomial R) := !![1, 0; 0, 0]

/-- The lower-corner polynomial defect used by the non-split crossing witness. -/
def polynomialLowerCrossing : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) := !![0, 0; 1, 0]

/-- The polynomial lower-corner defect is a standard cutoff-crossing cochain. -/
theorem polynomialLowerCrossing_eq_crossBoundary :
    polynomialLowerCrossing = crossBoundary (standardCutoff (R := ℚ)) polynomialLowerCrossing := by
  have hsub : (!![(1 : Polynomial ℚ), 0; 0, 1] - !![(1 : Polynomial ℚ), 0; 0, 0]) =
      !![(0 : Polynomial ℚ), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [polynomialLowerCrossing, crossBoundary, standardCutoff, Matrix.one_fin_two, hsub,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

/-- The split diagonal torsion presentation `R[X] --X^m--> R[X]` plus a free summand. -/
def splitTorsionPresentation (m : ℕ) : Matrix (Fin 2) (Fin 2) (Polynomial R) :=
  !![(X : Polynomial R) ^ m, 0; 0, 1]

/-- The split torsion presentation has determinant `X^m`. -/
theorem splitTorsionPresentation_det (m : ℕ) :
    (splitTorsionPresentation (R := R) m).det = (X : Polynomial R) ^ m := by
  rw [splitTorsionPresentation, Matrix.det_fin_two]
  simp

/-- The non-split two-lane torsion seam presentation over `ℚ[X]` used by the lower
crossing witness. -/
def shearTorsionPresentation (m : ℕ) : Matrix (Fin 2) (Fin 2) (Polynomial ℚ) :=
  !![(X : Polynomial ℚ) ^ m, 1; 0, 1]

/-- The sheared torsion presentation has determinant `X^m`. -/
theorem shearTorsionPresentation_det (m : ℕ) :
    (shearTorsionPresentation m).det = (X : Polynomial ℚ) ^ m := by
  rw [shearTorsionPresentation, Matrix.det_fin_two]
  simp

/-- The sheared presentation sees the lower crossing with constant boundary trace `-1`. -/
theorem fittingBoundaryTrace_shearTorsion_lowerCrossing (m : ℕ) :
    fittingBoundaryTrace (shearTorsionPresentation m) polynomialLowerCrossing = -1 := by
  rw [fittingBoundaryTrace, shearTorsionPresentation, polynomialLowerCrossing]
  have hadj : (!![(X : Polynomial ℚ) ^ m, 1; 0, 1]).adjugate =
      !![1, -1; 0, (X : Polynomial ℚ) ^ m] := by
    rw [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hadj, Matrix.mul_fin_two, Matrix.trace_fin_two]
  norm_num

/-- Coordinate formula for the sheared seam: against an arbitrary defect `Delta`, the
boundary trace depends on the entry difference `Delta 0 0 - Delta 1 0`, up to a
multiple of `X^m`. -/
theorem fittingBoundaryTrace_shearTorsion_apply (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    fittingBoundaryTrace (shearTorsionPresentation m) Delta =
      Delta 0 0 - Delta 1 0 + ((X : Polynomial ℚ) ^ m) * Delta 1 1 := by
  rw [fittingBoundaryTrace, shearTorsionPresentation]
  have hadj : (!![(X : Polynomial ℚ) ^ m, 1; 0, 1]).adjugate =
      !![1, -1; 0, (X : Polynomial ℚ) ^ m] := by
    rw [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hadj]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The sheared seam boundary class is exactly the divisor jet of the single entry
difference `Delta 0 0 - Delta 1 0`. -/
theorem fittingBoundaryClass_shearTorsion_apply (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    fittingBoundaryClass m (shearTorsionPresentation m) Delta =
      jetClass ℚ m (Delta 0 0 - Delta 1 0) := by
  rw [fittingBoundaryClass, fittingBoundaryTrace_shearTorsion_apply]
  exact jetClass_add_X_pow_mul ℚ m (Delta 0 0 - Delta 1 0) (Delta 1 1)

/-- Determinant transversality for the sheared seam is exactly nonvanishing of the
entry-difference divisor jet. -/
theorem fittingBoundaryClass_shearTorsion_ne_zero_iff (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    fittingBoundaryClass m (shearTorsionPresentation m) Delta ≠ 0 ↔
      jetClass ℚ m (Delta 0 0 - Delta 1 0) ≠ 0 := by
  rw [fittingBoundaryClass_shearTorsion_apply]

/-- Equivalently, the sheared seam is boundary-blind to `Delta` exactly when the
entry difference is divisible by the seam equation `X^m`. -/
theorem fittingBoundaryClass_shearTorsion_eq_zero_iff (m : ℕ)
    (Delta : Matrix (Fin 2) (Fin 2) (Polynomial ℚ)) :
    fittingBoundaryClass m (shearTorsionPresentation m) Delta = 0 ↔
      (X : Polynomial ℚ) ^ m ∣ Delta 0 0 - Delta 1 0 := by
  rw [fittingBoundaryClass_shearTorsion_apply]
  rw [jetClass]
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hmem
    simpa [jetIdeal] using (Ideal.mem_span_singleton.mp hmem)
  · intro hdiv
    exact Ideal.mem_span_singleton.mpr hdiv

/-- Hence the lower crossing is determinant-transverse to the sheared seam for every
positive order. -/
theorem fittingBoundaryClass_shearTorsion_lowerCrossing_ne_zero (m : ℕ) (hm : 0 < m) :
    fittingBoundaryClass m (shearTorsionPresentation m) polynomialLowerCrossing ≠ 0 := by
  rw [fittingBoundaryClass, fittingBoundaryTrace_shearTorsion_lowerCrossing]
  intro hzero
  rw [jetClass, Ideal.Quotient.eq_zero_iff_mem, jetIdeal, Ideal.mem_span_singleton] at hzero
  obtain ⟨c, hc⟩ := hzero
  have hco := congrArg (fun p => Polynomial.coeff p 0) hc
  simp only [Polynomial.coeff_neg, Polynomial.coeff_one, if_true,
    Polynomial.coeff_X_pow_mul'] at hco
  rw [if_neg (by omega : ¬ (m ≤ 0))] at hco
  norm_num at hco

/-- The same concrete witness is outside the right fake class. -/
theorem lowerCrossing_not_right_factor_shearTorsion_mod_X_pow (m : ℕ) (hm : 0 < m) :
    ¬ ∃ H K : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
      polynomialLowerCrossing = shearTorsionPresentation m * H + ((X : Polynomial ℚ) ^ m) • K := by
  exact nonzero_fittingBoundaryClass_obstructs_right_factor_mod_X_pow m
    (shearTorsionPresentation_det m)
    (fittingBoundaryClass_shearTorsion_lowerCrossing_ne_zero m hm)

/-- The same concrete witness is outside the left fake class. -/
theorem lowerCrossing_not_left_factor_shearTorsion_mod_X_pow (m : ℕ) (hm : 0 < m) :
    ¬ ∃ H K : Matrix (Fin 2) (Fin 2) (Polynomial ℚ),
      polynomialLowerCrossing = H * shearTorsionPresentation m + ((X : Polynomial ℚ) ^ m) • K := by
  exact nonzero_fittingBoundaryClass_obstructs_left_factor_mod_X_pow m
    (shearTorsionPresentation_det m)
    (fittingBoundaryClass_shearTorsion_lowerCrossing_ne_zero m hm)

/-- **Split torsion seams do not detect a standard lower cross-boundary corner.**
For the diagonal presentation `diag(X^m, 1)`, every defect of the form
`(1 - e) sigma e` has zero adjugate trace.  The determinant-transverse witness
therefore needs the non-split/sheared presentation used in `exists_nonfake_crossBoundary`. -/
theorem fittingBoundaryTrace_splitTorsion_crossBoundary (m : ℕ)
    (σ : Matrix (Fin 2) (Fin 2) (Polynomial R)) :
    fittingBoundaryTrace (splitTorsionPresentation (R := R) m) (crossBoundary standardCutoff σ) = 0 := by
  rw [fittingBoundaryTrace, splitTorsionPresentation, standardCutoff]
  have hsub : (!![(1 : Polynomial R), 0; 0, 1] - !![(1 : Polynomial R), 0; 0, 0]) =
      !![(0 : Polynomial R), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hleft : (!![(0 : Polynomial R), 0; 0, 1] * σ) =
      !![0, 0; σ 1 0, σ 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  have hΔ : crossBoundary (!![(1 : Polynomial R), 0; 0, 0]) σ =
      !![0, 0; σ 1 0, 0] := by
    rw [crossBoundary, Matrix.one_fin_two, hsub, hleft]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  have hadj : (!![(X : Polynomial R) ^ m, 0; 0, 1]).adjugate =
      !![1, 0; 0, (X : Polynomial R) ^ m] := by
    rw [Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hΔ, hadj, Matrix.mul_fin_two, Matrix.trace_fin_two]
  simp

/-- Consequently, the split diagonal torsion presentation has zero Fitting boundary
class for every standard lower cross-boundary defect. -/
theorem fittingBoundaryClass_splitTorsion_crossBoundary (m : ℕ)
    (σ : Matrix (Fin 2) (Fin 2) (Polynomial R)) :
    fittingBoundaryClass m (splitTorsionPresentation (R := R) m) (crossBoundary standardCutoff σ) = 0 := by
  rw [fittingBoundaryClass]
  rw [fittingBoundaryTrace_splitTorsion_crossBoundary]
  simp [jetClass]

/-! ### §5 The two-cutoff asymmetry: blind to one cutoff, crossing another -/

/-- **The two-cutoff asymmetry.**  There are two cutoffs `e, f` and an action `σ` that commutes with
`e` — so its `e`-cross-boundary cochain vanishes (`crossBoundary_eq_zero_of_commute`) — yet crosses
`f`: `crossBoundary f σ ≠ 0`.  A single cutoff can be blind to an action that a second cutoff detects;
compatibility with one boundary does not imply compatibility with another.  This is the abstract
Sonin double-vanishing obstruction: an action can respect the physical cutoff while crossing the
Fourier one. -/
theorem crossBoundary_two_cutoff_asymmetry :
    ∃ (e f σ : Matrix (Fin 2) (Fin 2) ℚ),
      IsIdempotentElem e ∧ IsIdempotentElem f ∧ σ * e = e * σ ∧
      crossBoundary e σ = 0 ∧ crossBoundary f σ ≠ 0 := by
  refine ⟨1, !![1, 0; 0, 0], !![0, 0; 1, 0], IsIdempotentElem.one, ?_, ?_, ?_, ?_⟩
  · show _ * _ = _
    rw [Matrix.mul_fin_two]; norm_num
  · rw [mul_one, one_mul]
  · rw [crossBoundary, sub_self, zero_mul, zero_mul]
  · have hsub : (!![(1:ℚ),0;0,1] - !![(1:ℚ),0;0,0]) = !![(0:ℚ),0;0,1] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [crossBoundary, Matrix.one_fin_two, hsub, Matrix.mul_fin_two, Matrix.mul_fin_two]
    intro h
    have := congrFun (congrFun h 1) 0
    norm_num at this

/-! ### §6 The unipotent obstruction: a boundary cochain cannot exponentiate to a deck root of unity -/

/-- **The unipotent expansion.**  For a square-zero element `Δ` (`Δ² = 0`), `(1 + Δ)ⁿ = 1 + n·Δ`:
the binomial collapses past the linear term, so `exp Δ = 1 + Δ` is unipotent. -/
theorem pow_one_add_of_sq_zero {Δ : E} (h : Δ * Δ = 0) (n : ℕ) :
    (1 + Δ) ^ n = 1 + n • Δ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, succ_nsmul]
    have hkΔ : (k • Δ) * Δ = k • (Δ * Δ) := by rw [smul_mul_assoc]
    rw [hkΔ, h, smul_zero, add_zero]; abel

/-- **A unipotent boundary cochain is never a nontrivial deck root of unity.**  If `1 + Δ` has finite
multiplicative order dividing `2^k` — the order type of a deck class `w_k ∈ μ_{2^k}` — then in a
torsion-free ring `Δ = 0`.  Because `(1 + Δ)^{2^k} = 1 + 2^k·Δ` (unipotent), being a `2^k`-th root of
unity forces `2^k·Δ = 0`, hence `Δ = 0`.  A nonzero square-zero cochain cannot exponentiate to a
nontrivial root of unity: **unipotent and torsion-semisimple live in different factors.** -/
theorem sq_zero_unipotent_root_trivial [NoZeroSMulDivisors ℕ E]
    {Δ : E} (h : Δ * Δ = 0) {k : ℕ} (hroot : (1 + Δ) ^ (2 ^ k) = 1) : Δ = 0 := by
  have hp := pow_one_add_of_sq_zero h (2 ^ k)
  rw [hroot] at hp
  have h0 : (2 ^ k) • Δ = 0 := left_eq_add.mp hp
  rcases (smul_eq_zero).mp h0 with hc | hc
  · exact absurd hc (pow_ne_zero k (by norm_num))
  · exact hc

/-- **The cross-boundary cochain cannot exponentiate to a nontrivial deck class.**  Applied to
`Δ = crossBoundary e a` (square-zero by `crossBoundary_mul_crossBoundary`): if `1 + (1−e)·a·e` is a
`2^k`-th root of unity in a torsion-free ring, the cochain vanishes.  So the deck ladder `w_k` (a
torsion element of `μ_{2^k}`) is **not** `exp` of the cross-boundary cochain — the labelled bridge
`w_k = exp(Δ)` is false for every nontrivial `w_k`.  The correct coupling is the lifted datum
`g_k = w_k·(1 + Δ)` (torsion × unipotent), whose two independent projections are the deck class and
the seam cochain — not an exponential identification of one with the other. -/
theorem crossBoundary_unipotent_root_trivial [NoZeroSMulDivisors ℕ E]
    {e a : E} (he : IsIdempotentElem e) {k : ℕ}
    (hroot : (1 + crossBoundary e a) ^ (2 ^ k) = 1) : crossBoundary e a = 0 :=
  sq_zero_unipotent_root_trivial (crossBoundary_mul_crossBoundary e a a he) hroot

/-- **The unipotent group of a square-zero ideal is additive.**  When `Δ·Δ' = 0`,
`(1 + Δ)·(1 + Δ') = 1 + (Δ + Δ')`: multiplication of unipotents is addition of cochains.  This is the
group law of the seam side of the lifted gluing datum `g_k = w_k·(1 + Δ_k)` — the additive `[Δ]`-face,
distinct from the multiplicative torsion `[w_k]`-face. -/
theorem one_add_mul_one_add_of_mul_zero {Δ Δ' : E} (h : Δ * Δ' = 0) :
    (1 + Δ) * (1 + Δ') = 1 + (Δ + Δ') := by
  rw [add_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h, add_zero]; abel

/-! ### §7 Closing the open seam: the traceless corner becomes a zero-free Euler factor -/

/-- The surviving cutoff-crossing corner, as a concrete matrix — the open seam `Δ = (1−e)·σ·e`. -/
def crossWitness : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]

/-- The open corner is a genuine cross-boundary cochain of a cutoff. -/
theorem crossWitness_eq_crossBoundary :
    crossWitness = crossBoundary (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) !![0, 0; 1, 0] := by
  have hsub : (!![(1:ℚ),0;0,1] - !![(1:ℚ),0;0,0]) = !![(0:ℚ),0;0,1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [crossWitness, crossBoundary, Matrix.one_fin_two, hsub, Matrix.mul_fin_two, Matrix.mul_fin_two]
  norm_num

/-- **The open seam is traceless** (`crossBoundary_trace_zero` instance): an open crossing carries no
trace, so it has no characteristic determinant of its own. -/
theorem crossWitness_trace_zero : crossWitness.trace = 0 := by
  rw [crossWitness, Matrix.trace_fin_two]; norm_num

/-- The **closed seam** `Δᵀ·Δ`: the canonical closure of the open crossing. -/
def closedSeam : Matrix (Fin 2) (Fin 2) ℚ := crossWitnessᵀ * crossWitness

theorem closedSeam_eq : closedSeam = !![1, 0; 0, 0] := by
  rw [closedSeam, crossWitness,
    show (!![(0:ℚ),0;1,0])ᵀ = !![(0:ℚ),1;0,0] by ext i j; fin_cases i <;> fin_cases j <;> simp,
    Matrix.mul_fin_two]
  norm_num

/-- **The closed seam is a rank-one idempotent.**  Closing the open crossing produces a projection —
the object with a trace and a determinant that the open corner lacked. -/
theorem closedSeam_idempotent : IsIdempotentElem closedSeam := by
  rw [closedSeam_eq]; show _ * _ = _; rw [Matrix.mul_fin_two]; norm_num

/-- **The closed seam has trace one** — where the open seam was traceless.  This is the correction
that gives the crossing a determinant: `Δ` is traceless, but `Δᵀ·Δ` is a rank-one projection. -/
theorem closedSeam_trace_one : closedSeam.trace = 1 := by
  rw [closedSeam_eq, Matrix.trace_fin_two]; norm_num

/-- **The closed seam's characteristic determinant is the local Euler-factor shape.**
`det(1 − λ·(Δᵀ·Δ)) = 1 − λ`; with `λ = p^(−s)` this is the local Euler factor `1 − p^(−s)`, so
`det(1 − λ·closedSeam)⁻¹ = (1 − p^(−s))⁻¹`.  The closed seam recovers the Euler factor — **but that
determinant is zero only at `λ = 1`**, so it is the **zero-free** Euler factor.  The divisor (the
strip zeros) is *not* in the closed seam or its finite Euler product; it lives across the wall of
convergence `Re s = 1`, reachable only by an analytic continuation the determinant does not supply.
Closing the seam produces the prime side, not the divisor. -/
theorem det_one_sub_smul_closedSeam (lam : ℚ) :
    (1 - lam • closedSeam).det = 1 - lam := by
  rw [closedSeam_eq, Matrix.one_fin_two,
    show lam • (!![(1:ℚ),0;0,0] : Matrix (Fin 2) (Fin 2) ℚ) = !![lam,0;0,0] by
      ext i j; fin_cases i <;> fin_cases j <;> simp,
    show (!![(1:ℚ),0;0,1] - !![lam,0;0,0]) = !![1-lam,0;0,1] by
      ext i j; fin_cases i <;> fin_cases j <;> simp,
    Matrix.det_fin_two]
  simp

/-! ### §8 Place transitions: a naturally transported cutoff has no crossing defect -/

section TransitionBoundary

variable {R H K B : Type*} [CommRing R]
variable [AddCommGroup H] [Module R H]
variable [AddCommGroup K] [Module R K]
variable [AddCommGroup B] [Module R B]

/-- The part of a linear transition which carries the source cutoff into the complement of the
target cutoff.  Unlike `crossBoundary`, the source and target may be different realizations of one
carrier. -/
def transitionBoundary (qH : H →ₗ[R] H) (qK : K →ₗ[R] K) (J : H →ₗ[R] K) : H →ₗ[R] K :=
  (LinearMap.id - qK).comp (J.comp qH)

/-- An intertwiner of idempotent cutoffs has zero transition boundary.  This is the two-space
version of `crossBoundary_eq_zero_of_commute`: a natural change of realization cannot manufacture a
cutoff-crossing defect. -/
theorem transitionBoundary_eq_zero_of_intertwines
    {qH : H →ₗ[R] H} {qK : K →ₗ[R] K} {J : H →ₗ[R] K}
    (hqK : ∀ y, qK (qK y) = qK y)
    (hJ : ∀ x, J (qH x) = qK (J x)) :
    transitionBoundary qH qK J = 0 := by
  ext x
  simp only [transitionBoundary, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.zero_apply]
  rw [hJ, hqK]
  simp

/-- The failure of an operator family to be natural across a transition `J`.  For the semilocal
prolate candidate this is `W_T J - J W_S`; the definition itself is independent of that realization. -/
def operatorNaturalityDefect (WH : H →ₗ[R] H) (WK : K →ₗ[R] K)
    (J : H →ₗ[R] K) : H →ₗ[R] K :=
  WK.comp J - J.comp WH

/-- For a cutoff-compatible transition, the boundary of the operator naturality defect is exactly
the difference between the target crossing transported from the right and the source crossing
transported from the left.  Thus a place-naturality defect produces new cutoff content only through
the failure of the operator family to preserve the transported cutoff sectors. -/
theorem transitionBoundary_operatorNaturalityDefect
    (qH : H →ₗ[R] H) (qK : K →ₗ[R] K)
    (WH : H →ₗ[R] H) (WK : K →ₗ[R] K) (J : H →ₗ[R] K)
    (hJ : ∀ x, J (qH x) = qK (J x)) :
    transitionBoundary qH qK (operatorNaturalityDefect WH WK J) =
      (crossBoundary qK WK).comp J - J.comp (crossBoundary qH WH) := by
  ext x
  simp [transitionBoundary, operatorNaturalityDefect, crossBoundary, hJ]
  abel

/-- Transport a cutoff from a common carrier through a linear equivalence. -/
def transportedCutoff (e : B ≃ₗ[R] H) (q : B →ₗ[R] B) : H →ₗ[R] H :=
  e.toLinearMap.comp (q.comp e.symm.toLinearMap)

/-- The canonical transition between two realizations of one fixed carrier. -/
def canonicalTransition (eH : B ≃ₗ[R] H) (eK : B ≃ₗ[R] K) : H →ₗ[R] K :=
  eK.toLinearMap.comp eH.symm.toLinearMap

/-- Canonical transitions intertwine every cutoff transported from the common carrier. -/
theorem canonicalTransition_intertwines_transportedCutoff
    (eH : B ≃ₗ[R] H) (eK : B ≃ₗ[R] K) (q : B →ₗ[R] B) (x : H) :
    canonicalTransition eH eK (transportedCutoff eH q x) =
      transportedCutoff eK q (canonicalTransition eH eK x) := by
  simp [canonicalTransition, transportedCutoff]

/-- Transport through an equivalence preserves idempotence of a cutoff. -/
theorem transportedCutoff_idempotent
    (e : B ≃ₗ[R] H) {q : B →ₗ[R] B} (hq : ∀ x, q (q x) = q x) (y : H) :
    transportedCutoff e q (transportedCutoff e q y) = transportedCutoff e q y := by
  simp [transportedCutoff, hq]

/-- A place-change or realization-change map induced from a common carrier has zero cutoff defect
for every naturally transported idempotent.  A nonzero place defect therefore needs extra structure
which is not part of the canonical identification. -/
theorem canonicalTransition_boundary_eq_zero
    (eH : B ≃ₗ[R] H) (eK : B ≃ₗ[R] K) {q : B →ₗ[R] B}
    (hq : ∀ x, q (q x) = q x) :
    transitionBoundary (transportedCutoff eH q) (transportedCutoff eK q)
      (canonicalTransition eH eK) = 0 := by
  apply transitionBoundary_eq_zero_of_intertwines
  · exact transportedCutoff_idempotent eK hq
  · exact canonicalTransition_intertwines_transportedCutoff eH eK q

end TransitionBoundary

end RHTower
