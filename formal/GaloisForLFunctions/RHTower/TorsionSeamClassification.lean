/-
Fake-defect vanishing and the non-fake classification for the extended `M+` torsion seam layer.

The extended category `𝓜̃⁺` (`MPlusTorsionSeamObject`) and its objects (a presentation `R[X]ⁿ →ᴬ R[X]ⁿ`
with `det A = Xᵐ` and σ-labelled defects `Δ_p`), morphisms (`Hom`, preserving `A` and the defect class),
and the boundary functional `∂_p(A,Δ_p) = tr(adj A · Δ_p) mod Xᵐ` (`boundaryClass`) are defined in
`MPlusTorsionSeam`; the adjugate/Fitting algebra is in `FittingSeamBoundary`.  This file closes the two
remaining program deliverables.

**Fake defects vanish.**  A defect factoring through the presentation modulo the local zero ideal
(`Δ_p = A·H + Xᵐ·K`) has zero boundary functional (`boundaryClass_eq_zero_of_defectFactorsThrough`):
`tr(adj A · (A·H + Xᵐ·K)) = det A · tr H + Xᵐ·tr(adj A · K) = Xᵐ·(…) ≡ 0 mod Xᵐ`, using `adj A · A =
det A · 1`.  The same holds for left-fake defects.

**Classification.**  A non-fake defect is a genuine seam obstruction.  Its existence is governed by the
divisor: at `m = 0` the divisor `X⁰ = 1` is a unit and *every* defect is fake
(`defectFactorsThrough_of_m_zero`), while for `m ≥ 1` the cutoff-crossing witness is non-fake.  Hence a
torsion seam presentation carries a non-fake defect iff `m ≥ 1` (`exists_nonfake_seam_iff`): the seam is
a non-fake-carrying refinement exactly when its local divisor is nontrivial.  In the transverse
direction the boundary functional is a complete detector — `¬ (Xᵐ ∣ tr(adj A · Δ_p))` already forces
non-fakeness (`TorsionSeamPresentation.defectNonmember_of_not_traceDivisible`).
-/
import GaloisForLFunctions.RHTower.CutoffTorsionSeam

noncomputable section

namespace RHTower

open Matrix Polynomial

variable {n R Sigma : Type*} [Fintype n] [DecidableEq n] [CommRing R]

namespace TorsionSeamPresentation

/-- **Fake defects vanish (Deliverable 2).**  A defect factoring through the presentation modulo the
local zero ideal (`Δ_p = A·H + Xᵐ·K`) has zero boundary functional: `∂_p(A,Δ_p) ≡ 0 mod Xᵐ`. -/
theorem boundaryClass_eq_zero_of_defectFactorsThrough {m : ℕ}
    (S : TorsionSeamPresentation Sigma n R m) {p : Sigma} (h : S.DefectFactorsThrough p) :
    S.boundaryClass p = 0 := by
  obtain ⟨H, K, hHK⟩ := h
  exact fittingBoundaryClass_eq_zero_of_right_factor_mod_X_pow m S.det_eq hHK

/-- The trace form of fake-defect vanishing: a fake defect has boundary trace divisible by `Xᵐ`. -/
theorem boundaryTraceDivisible_of_defectFactorsThrough {m : ℕ}
    (S : TorsionSeamPresentation Sigma n R m) {p : Sigma} (h : S.DefectFactorsThrough p) :
    S.BoundaryTraceDivisible p :=
  (fittingBoundaryClass_eq_zero_iff_trace_X_pow_dvd m S.A (S.Delta p)).mp
    (boundaryClass_eq_zero_of_defectFactorsThrough S h)

/-- Left-sided fake-defect vanishing: a left-fake defect (`Δ_p = H·A + Xᵐ·K`) also has zero boundary
functional. -/
theorem boundaryClass_eq_zero_of_defectFactorsThroughLeft {m : ℕ}
    (S : TorsionSeamPresentation Sigma n R m) {p : Sigma} (h : S.DefectFactorsThroughLeft p) :
    S.boundaryClass p = 0 := by
  obtain ⟨H, K, hHK⟩ := h
  exact fittingBoundaryClass_eq_zero_of_left_factor_mod_X_pow m S.det_eq hHK

/-- The trace form of left-fake-defect vanishing. -/
theorem boundaryTraceDivisible_of_defectFactorsThroughLeft {m : ℕ}
    (S : TorsionSeamPresentation Sigma n R m) {p : Sigma}
    (h : S.DefectFactorsThroughLeft p) :
    S.BoundaryTraceDivisible p :=
  (fittingBoundaryClass_eq_zero_iff_trace_X_pow_dvd m S.A (S.Delta p)).mp
    (boundaryClass_eq_zero_of_defectFactorsThroughLeft S h)

/-- **Every defect is fake at `m = 0`.**  The trivial divisor `X⁰ = 1` makes every defect factor as
`Δ = A·0 + X⁰·Δ`; there is no non-fake defect when the seam divisor is a unit. -/
theorem defectFactorsThrough_of_m_zero
    (S : TorsionSeamPresentation Sigma n R 0) (p : Sigma) : S.DefectFactorsThrough p :=
  ⟨0, S.Delta p, by simp⟩

/-- At the unit divisor, every defect also factors through the presentation on the left. -/
theorem defectFactorsThroughLeft_of_m_zero
    (S : TorsionSeamPresentation Sigma n R 0) (p : Sigma) : S.DefectFactorsThroughLeft p :=
  ⟨0, S.Delta p, by simp⟩

/-- At the unit divisor `m = 0`, every seam boundary class vanishes; the intermediate
factor-through Prop is discharged by the canonical factorization. -/
theorem boundaryClass_eq_zero_of_m_zero
    (S : TorsionSeamPresentation Sigma n R 0) (p : Sigma) : S.boundaryClass p = 0 :=
  boundaryClass_eq_zero_of_defectFactorsThrough S (defectFactorsThrough_of_m_zero S p)

/-- At the unit divisor `m = 0`, every boundary trace is divisible by `X⁰`; no fake-defect
interface remains. -/
theorem boundaryTraceDivisible_of_m_zero
    (S : TorsionSeamPresentation Sigma n R 0) (p : Sigma) : S.BoundaryTraceDivisible p :=
  boundaryTraceDivisible_of_defectFactorsThrough S (defectFactorsThrough_of_m_zero S p)

/-- No defect is non-fake at `m = 0`. -/
theorem no_defectNonmember_of_m_zero
    (S : TorsionSeamPresentation Sigma n R 0) (p : Sigma) : ¬ S.DefectNonmember p :=
  fun h => h (defectFactorsThrough_of_m_zero S p)

/-- No defect is left-nonfake at the unit divisor. -/
theorem no_defectLeftNonmember_of_m_zero
    (S : TorsionSeamPresentation Sigma n R 0) (p : Sigma) : ¬ S.DefectLeftNonmember p :=
  fun h => h (defectFactorsThroughLeft_of_m_zero S p)

end TorsionSeamPresentation

/-- **Classification (Deliverable 3).**  A torsion seam presentation over `ℚ` at rank `n = 2` carries a
non-fake defect *iff* `m ≥ 1`: the seam is a non-fake-carrying refinement exactly when the local
divisor `Xᵐ` is nontrivial.  Forward — at `m = 0` every defect is fake; backward — for `m ≥ 1` the
cutoff-crossing witness (`exists_crossing_cutoffTorsionSeam`) is non-fake. -/
theorem exists_nonfake_seam_iff (m : ℕ) :
    (∃ (S : TorsionSeamPresentation Unit (Fin 2) ℚ m) (p : Unit), S.DefectNonmember p) ↔ 1 ≤ m := by
  constructor
  · rintro ⟨S, p, hp⟩
    by_contra hlt
    have hm0 : m = 0 := by omega
    subst hm0
    exact hp (TorsionSeamPresentation.defectFactorsThrough_of_m_zero S p)
  · intro hm
    obtain ⟨S, _, _, _, _, _, _, _, hnf, _⟩ := exists_crossing_cutoffTorsionSeam m hm
    exact ⟨S, (), hnf⟩

end RHTower
