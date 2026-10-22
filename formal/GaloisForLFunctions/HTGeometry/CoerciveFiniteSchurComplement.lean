import GaloisForLFunctions.HTGeometry.CoerciveOperatorInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Schur complements of block quadratic forms on Hilbert spaces

For bounded operators `A` on `F`, `B : H → F` and a self-adjoint `D` on `H` with right inverse `D⁻¹`,
the block quadratic form `Q(f, h) = Re(⟨A f + B h, f⟩ + ⟨B* f + D h, h⟩)` splits as the Schur-complement
form `Re⟨(A - B D⁻¹ B*) f, f⟩` plus `Re⟨D(h + D⁻¹ B* f), h + D⁻¹ B* f⟩` (completion of the square). When
`D` is a nonnegative form, `Q` is nonnegative everywhere iff the Schur complement is. The second part
realizes this decomposition for a self-adjoint `T` on `E = Mᗮ ⊕ M` via orthogonal compressions: the
block form of the compressed blocks of `T` is exactly `Re⟨T(f + m), f + m⟩`.

## Main results

- `adjoint_inverse_of_twoSided`: a right inverse of a self-adjoint bounded operator is self-adjoint.
- `coerciveSchurBlockQuadratic_eq`: the completion-of-the-square identity for the block form.
- `coerciveSchurBlockQuadratic_nonneg_iff`: if `⟨D h, h⟩` has nonnegative real part, the block form is
  nonnegative iff the Schur complement form is.
- `finiteSchurBlockQuadratic_eq_inner`: the block form of the orthogonal compressions of a self-adjoint
  `T` relative to `M` equals `Re⟨T(f + m), f + m⟩` for `f ∈ Mᗮ`, `m ∈ M`.
- `finiteSchurCoupling_adjoint`, `finiteSchurExteriorBlock_adjoint`: adjoints of the coupling and of
  the compression to `M`.

## Hypotheses

Unconditional operator identities. The Schur results assume `D` self-adjoint with `D ∘ D⁻¹ = 1`, and the
nonnegativity criterion additionally assumes `0 ≤ Re⟨D h, h⟩` for all `h`. The compression results assume
`T` self-adjoint and that `M` and `Mᗮ` are complete with orthogonal projections; no finite-dimensionality
is required.
-/

open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {F H : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Schur complement `A - B D⁻¹ B*` of the block operator with blocks `A`, `B`, `B*`, `D`. -/
def coerciveSchurComplement
    (A : F →L[ℂ] F) (B : H →L[ℂ] F) (Dinv : H →L[ℂ] H) : F →L[ℂ] F :=
  A - B ∘L Dinv ∘L B.adjoint

/-- The real block quadratic form `Re(⟨A f + B h, f⟩ + ⟨B* f + D h, h⟩)` on `F × H`. -/
def coerciveSchurBlockQuadratic
    (A : F →L[ℂ] F) (B : H →L[ℂ] F) (D : H →L[ℂ] H)
    (f : F) (h : H) : ℝ :=
  (inner ℂ (A f + B h) f + inner ℂ (B.adjoint f + D h) h).re

/-- The Schur complement `A - B D⁻¹ C` for a general (not necessarily symmetric) block operator. -/
def hilbertSchurComplement
    (A : F →L[ℂ] F) (B : H →L[ℂ] F) (C : F →L[ℂ] H)
    (Dinv : H →L[ℂ] H) : F →L[ℂ] F :=
  A - B ∘L Dinv ∘L C

/-- The real block quadratic form `Re(⟨A f + B h, f⟩ + ⟨C f + D h, h⟩)` for a general block operator. -/
def hilbertSchurBlockQuadratic
    (A : F →L[ℂ] F) (B : H →L[ℂ] F) (C : F →L[ℂ] H)
    (D : H →L[ℂ] H) (f : F) (h : H) : ℝ :=
  (inner ℂ (A f + B h) f + inner ℂ (C f + D h) h).re

/-- If `D` is self-adjoint and `D ∘ D⁻¹ = 1`, then `D⁻¹` is self-adjoint. -/
theorem adjoint_inverse_of_twoSided
    (D Dinv : H →L[ℂ] H) (hD : D.adjoint = D)
    (hright : D ∘L Dinv = 1) :
    Dinv.adjoint = Dinv := by
  have hrightAdj := congrArg ContinuousLinearMap.adjoint hright
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_one] at hrightAdj
  rw [hD] at hrightAdj
  ext x
  have hrightApply : D (Dinv x) = x := by
    have hx := DFunLike.congr_fun hright x
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using hx
  have hrightAdjApply : Dinv.adjoint (D (Dinv x)) = Dinv x := by
    have hx := DFunLike.congr_fun hrightAdj (Dinv x)
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using hx
  calc
    Dinv.adjoint x = Dinv.adjoint (D (Dinv x)) :=
      congrArg Dinv.adjoint hrightApply.symm
    _ = Dinv x := hrightAdjApply

/-- Completion of the square: for self-adjoint `D` with `D ∘ D⁻¹ = 1`,
`Q(f, h) = Re⟨(A - B D⁻¹ B*) f, f⟩ + Re⟨D(h + D⁻¹ B* f), h + D⁻¹ B* f⟩`. -/
theorem coerciveSchurBlockQuadratic_eq
    (A : F →L[ℂ] F) (B : H →L[ℂ] F) (D Dinv : H →L[ℂ] H)
    (hD : D.adjoint = D) (hright : D ∘L Dinv = 1)
    (f : F) (h : H) :
    coerciveSchurBlockQuadratic A B D f h =
      (inner ℂ (coerciveSchurComplement A B Dinv f) f).re +
        (inner ℂ (D (h + Dinv (B.adjoint f)))
          (h + Dinv (B.adjoint f))).re := by
  have hDadj : D.adjoint = D := hD
  have hDinva : Dinv.adjoint = Dinv :=
    adjoint_inverse_of_twoSided D Dinv hD hright
  have hrightApply : ∀ x, D (Dinv x) = x := by
    intro x
    have hx := DFunLike.congr_fun hright x
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using hx
  unfold coerciveSchurBlockQuadratic coerciveSchurComplement
  simp only [sub_apply, ContinuousLinearMap.comp_apply, map_add, inner_add_left,
    inner_add_right, inner_sub_left, Complex.add_re, Complex.sub_re]
  have hB : inner ℂ (B h) f = inner ℂ h (B.adjoint f) := by
    exact (B.adjoint_inner_right h f).symm
  have hBD : inner ℂ (B (Dinv (B.adjoint f))) f =
      inner ℂ (Dinv (B.adjoint f)) (B.adjoint f) := by
    exact (B.adjoint_inner_right (Dinv (B.adjoint f)) f).symm
  have hDcross : inner ℂ (D h) (Dinv (B.adjoint f)) =
      inner ℂ h (B.adjoint f) := by
    calc
      inner ℂ (D h) (Dinv (B.adjoint f)) =
          inner ℂ h (D.adjoint (Dinv (B.adjoint f))) :=
        (D.adjoint_inner_right h (Dinv (B.adjoint f))).symm
      _ = inner ℂ h (B.adjoint f) := by rw [hDadj, hrightApply]
  have hDlast : inner ℂ (D (Dinv (B.adjoint f))) (Dinv (B.adjoint f)) =
      inner ℂ (Dinv (B.adjoint f)) (B.adjoint f) := by
    rw [hrightApply]
    have hs := Dinv.adjoint_inner_right (B.adjoint f) (B.adjoint f)
    rw [hDinva] at hs
    exact hs
  have hDright : D (Dinv (B.adjoint f)) = B.adjoint f :=
    hrightApply _
  rw [hB, hBD, hDcross, hDlast, hDright]
  ring

/-- Schur criterion: for self-adjoint `D` with `D ∘ D⁻¹ = 1` and `Re⟨D h, h⟩ ≥ 0` (`hDnonneg`), the block
form is nonnegative on `F × H` iff the Schur complement form `Re⟨(A - B D⁻¹ B*) f, f⟩` is nonnegative. -/
theorem coerciveSchurBlockQuadratic_nonneg_iff
    (A : F →L[ℂ] F) (B : H →L[ℂ] F) (D Dinv : H →L[ℂ] H)
    (hD : D.adjoint = D) (hright : D ∘L Dinv = 1)
    (hDnonneg : ∀ h : H, 0 ≤ (inner ℂ (D h) h).re) :
    (∀ f h, 0 ≤ coerciveSchurBlockQuadratic A B D f h) ↔
      ∀ f, 0 ≤ (inner ℂ (coerciveSchurComplement A B Dinv f) f).re := by
  constructor
  · intro hall f
    have h := hall f (-(Dinv (B.adjoint f)))
    rw [coerciveSchurBlockQuadratic_eq A B D Dinv hD hright] at h
    simp only [neg_add_cancel, map_zero, inner_zero_left, Complex.zero_re, add_zero] at h
    exact h
  · intro hschur f h
    rw [coerciveSchurBlockQuadratic_eq A B D Dinv hD hright]
    exact add_nonneg (hschur f) (hDnonneg _)

section OrthogonalCompression

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Pairing the orthogonal projection of `v` onto `M` with `m ∈ M` gives `⟨v, m⟩`. -/
theorem coe_orthogonalProjectionOnto_inner_eq
    (M : Submodule ℂ E) [M.HasOrthogonalProjection] (v : E) (m : M) :
    inner ℂ ((M.orthogonalProjectionOnto v : M) : E) (m : E) =
      inner ℂ v (m : E) := by
  rw [← M.coe_inner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]

omit [CompleteSpace E] in
/-- Pairing `m ∈ M` with the orthogonal projection of `v` onto `M` gives `⟨m, v⟩`. -/
theorem inner_coe_orthogonalProjectionOnto_eq
    (M : Submodule ℂ E) [M.HasOrthogonalProjection] (m : M) (v : E) :
    inner ℂ (m : E) ((M.orthogonalProjectionOnto v : M) : E) =
      inner ℂ (m : E) v := by
  rw [← M.coe_inner, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]

/-- The compression `P_(Mᗮ) T` restricted to `Mᗮ`. -/
def finiteSchurExceptionalBlock (T : E →L[ℂ] E) (M : Submodule ℂ E)
    [Mᗮ.HasOrthogonalProjection] : Mᗮ →L[ℂ] Mᗮ :=
  Mᗮ.orthogonalProjectionOnto ∘L T ∘L Mᗮ.subtypeL

/-- The off-diagonal block `P_(Mᗮ) T` restricted to `M`, as a map `M → Mᗮ`. -/
def finiteSchurCoupling (T : E →L[ℂ] E) (M : Submodule ℂ E)
    [Mᗮ.HasOrthogonalProjection] : M →L[ℂ] Mᗮ :=
  Mᗮ.orthogonalProjectionOnto ∘L T ∘L M.subtypeL

/-- The compression `P_M T` restricted to `M`. -/
def finiteSchurExteriorBlock (T : E →L[ℂ] E) (M : Submodule ℂ E)
    [M.HasOrthogonalProjection] : M →L[ℂ] M :=
  M.orthogonalProjectionOnto ∘L T ∘L M.subtypeL

/-- For self-adjoint `T`, the adjoint of the coupling `M → Mᗮ` is the compression `P_M T` restricted to
`Mᗮ`. -/
theorem finiteSchurCoupling_adjoint
    (T : E →L[ℂ] E) (M : Submodule ℂ E)
    [CompleteSpace M] [CompleteSpace Mᗮ]
    [M.HasOrthogonalProjection] [Mᗮ.HasOrthogonalProjection]
    (hT : T.adjoint = T) :
    (finiteSchurCoupling T M).adjoint =
      M.orthogonalProjectionOnto ∘L T ∘L Mᗮ.subtypeL := by
  rw [finiteSchurCoupling, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_comp, Submodule.adjoint_orthogonalProjectionOnto,
    Submodule.adjoint_subtypeL]
  rw [hT]
  rfl

/-- For self-adjoint `T`, the block form of the compressions of `T` relative to `E = Mᗮ ⊕ M` is the
quadratic form of `T`: `Q(f, m) = Re⟨T(f + m), f + m⟩`. -/
theorem finiteSchurBlockQuadratic_eq_inner
    (T : E →L[ℂ] E) (M : Submodule ℂ E)
    [CompleteSpace M] [CompleteSpace Mᗮ]
    [M.HasOrthogonalProjection] [Mᗮ.HasOrthogonalProjection]
    (hT : T.adjoint = T) (f : Mᗮ) (m : M) :
    coerciveSchurBlockQuadratic
        (finiteSchurExceptionalBlock T M) (finiteSchurCoupling T M)
        (finiteSchurExteriorBlock T M) f m =
      (inner ℂ (T ((f : E) + (m : E))) ((f : E) + (m : E))).re := by
  rw [coerciveSchurBlockQuadratic, finiteSchurCoupling_adjoint T M hT,
    finiteSchurExceptionalBlock, finiteSchurCoupling, finiteSchurExteriorBlock]
  simp only [ContinuousLinearMap.comp_apply, map_add, inner_add_left, inner_add_right,
    Complex.add_re]
  simp

/-- For self-adjoint `T`, the compression of `T` to `M` is self-adjoint. -/
theorem finiteSchurExteriorBlock_adjoint
    (T : E →L[ℂ] E) (M : Submodule ℂ E)
    [CompleteSpace M] [M.HasOrthogonalProjection]
    (hT : T.adjoint = T) :
    (finiteSchurExteriorBlock T M).adjoint = finiteSchurExteriorBlock T M := by
  rw [finiteSchurExteriorBlock,
    ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_orthogonalProjectionOnto, Submodule.adjoint_subtypeL,
    hT]
  rfl

end OrthogonalCompression

end GaloisForLFunctions.HTGeometry

