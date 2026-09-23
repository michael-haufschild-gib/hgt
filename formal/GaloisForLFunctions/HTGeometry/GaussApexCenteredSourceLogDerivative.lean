import GaloisForLFunctions.HTGeometry.GaussTerminalSourceLogDerivative

/-!
# Apex-centered faithful Gauss source

De-resisted completed source leaves one unit atom at every admitted node.  Centering each atom at
the moving hard apex before aggregation gives residue `(y*x)^(2 : ℕ) - 1`.  Its Cauchy transform has an
exact landing in the current admission logarithmic derivative, with degree and root-trace
counterterms forced by polynomial division.

Everything is finite-block algebra.  No representing measure, infinite extension, limiting
argument, or computation is used.
-/

open scoped BigOperators
open Polynomial Complex

namespace HTGeometry

/-- First trace of the current finite Gauss face. -/
noncomputable def gaussNodeTrace (s : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ x ∈ gaussNodes s m, x

/-- Faithful unit-pole carrier centered at moving hard apex `1/y` before aggregation. -/
noncomputable def gaussApexCenteredUnitPoleTransformComplex
    (s : ℕ → ℝ) (m : ℕ) (y : ℝ) (z : ℂ) : ℂ :=
  ∑ x ∈ gaussNodes s m,
    (((y * x) ^ (2 : ℕ) - 1 : ℝ) : ℂ) / (z - (x : ℂ))

/-- Total signed moving-apex residue before any Cauchy or Poisson reporting. -/
noncomputable def gaussApexCenteredResidueTotal
    (s : ℕ → ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  ∑ x ∈ gaussNodes s m, ((y * x) ^ (2 : ℕ) - 1)

/-- Exact quadratic-energy form of total centered faithful source. -/
theorem gaussApexCenteredResidueTotal_eq
    (s : ℕ → ℝ) (m : ℕ) (y : ℝ) :
    gaussApexCenteredResidueTotal s m y =
      y ^ (2 : ℕ) * (∑ x ∈ gaussNodes s m, x ^ (2 : ℕ)) - (gaussNodes s m).card := by
  classical
  rw [gaussApexCenteredResidueTotal]
  calc
    ∑ x ∈ gaussNodes s m, ((y * x) ^ (2 : ℕ) - 1) =
        ∑ x ∈ gaussNodes s m, (y ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = y ^ (2 : ℕ) * (∑ x ∈ gaussNodes s m, x ^ (2 : ℕ)) - (gaussNodes s m).card := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Exact apex-centered source landing.**  The signed faithful carrier is the admission
logarithmic derivative multiplied by its moving-apex quadratic, minus the intrinsic degree and
root-trace vacuum forced by polynomial division. -/
theorem gaussApexCenteredUnitPoleTransformComplex_eq_logDerivative
    {s : ℕ → ℝ} {N m : ℕ} (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N)
    (y : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    gaussApexCenteredUnitPoleTransformComplex s m y z =
      ((y : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - 1) *
          (Polynomial.aeval z (monicOrtho s (m + 1)).derivative /
            monicOrthoC s (m + 1) z) -
        (y : ℂ) ^ (2 : ℕ) *
          (((gaussNodes s m).card : ℂ) * z + (gaussNodeTrace s m : ℂ)) := by
  classical
  let nodes := gaussNodes s m
  have hpoint (x : ℝ) (hx : x ∈ nodes) :
      (((y * x) ^ (2 : ℕ) - 1 : ℝ) : ℂ) / (z - (x : ℂ)) =
        (((y : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - 1) / (z - (x : ℂ)) -
          (y : ℂ) ^ (2 : ℕ) * (z + (x : ℂ))) := by
    have hxz : z - (x : ℂ) ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at him
      exact hz him
    push_cast
    field_simp [hxz]
    ring_nf
  rw [gaussApexCenteredUnitPoleTransformComplex,
    show gaussNodes s m = nodes by rfl]
  calc
    ∑ x ∈ nodes, (((y * x) ^ (2 : ℕ) - 1 : ℝ) : ℂ) / (z - (x : ℂ)) =
        ∑ x ∈ nodes,
          (((y : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - 1) / (z - (x : ℂ)) -
            (y : ℂ) ^ (2 : ℕ) * (z + (x : ℂ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpoint x hx
    _ = ((y : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - 1) *
          gaussUnitPoleTransformComplex s m z -
        (y : ℂ) ^ (2 : ℕ) * (((nodes.card : ℂ) * z) + (gaussNodeTrace s m : ℂ)) := by
      rw [Finset.sum_sub_distrib]
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      rw [gaussUnitPoleTransformComplex,
        show gaussNodes s m = nodes by rfl, gaussNodeTrace,
        show gaussNodes s m = nodes by rfl]
      push_cast
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      ring_nf
    _ = _ := by
      rw [gaussUnitPoleTransformComplex_eq_logDerivative h hmN hz]

/-- Current degree form of the exact apex-centered landing. -/
theorem gaussApexCenteredUnitPoleTransformComplex_eq_degree_logDerivative
    {s : ℕ → ℝ} {N m : ℕ} (h : PositiveMomentFormBelow s N) (hmN : m + 1 < N)
    (y : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    gaussApexCenteredUnitPoleTransformComplex s m y z =
      ((y : ℂ) ^ (2 : ℕ) * z ^ (2 : ℕ) - 1) *
          (Polynomial.aeval z (monicOrtho s (m + 1)).derivative /
            monicOrthoC s (m + 1) z) -
        (y : ℂ) ^ (2 : ℕ) *
          (((m + 1 : ℕ) : ℂ) * z + (gaussNodeTrace s m : ℂ)) := by
  rw [gaussApexCenteredUnitPoleTransformComplex_eq_logDerivative h hmN y hz,
    gaussNodes_card_below h m hmN]

/-- Pole residue of the centered faithful carrier has exactly the moving-apex sign. -/
theorem gaussApexCenteredResidue_pos_iff
    {y x : ℝ} (hy : 0 < y) (hx : 0 < x) :
    0 < (y * x) ^ (2 : ℕ) - 1 ↔ 1 < y * x := by
  have hprod : 0 < y * x := mul_pos hy hx
  constructor
  · intro hsquare
    by_contra hnot
    have hle : y * x ≤ 1 := le_of_not_gt hnot
    have hfactor : 0 ≤ (1 - y * x) * (1 + y * x) :=
      mul_nonneg (sub_nonneg.mpr hle) (by linarith)
    nlinarith
  · intro hlinear
    have hfactor : 0 < (y * x - 1) * (y * x + 1) :=
      mul_pos (sub_pos.mpr hlinear) (by linarith)
    nlinarith

/-- Admission-sensitive positive null-flag shear of the centered faithful source.  Positive part
is taken at each node before Poisson aggregation, so sub-apex residues cannot cancel a super-apex
source atom. -/
noncomputable def gaussSuperApexNullFlagPoissonSource
    (s : ℕ → ℝ) (m : ℕ) (y a eta : ℝ) : ℝ :=
  ∑ x ∈ gaussNodes s m,
    max 0 ((y * x) ^ (2 : ℕ) - 1) * eta / ((a - x) ^ (2 : ℕ) + eta ^ (2 : ℕ))

/-- **Exact null-flag detection.**  At positive aperture, the pre-aggregation positive shear is
strictly positive exactly when some current admitted residue is super-apex. -/
theorem gaussSuperApexNullFlagPoissonSource_pos_iff
    (s : ℕ → ℝ) (m : ℕ) (y a : ℝ) {eta : ℝ} (heta : 0 < eta) :
    0 < gaussSuperApexNullFlagPoissonSource s m y a eta ↔
      ∃ x ∈ gaussNodes s m, 0 < (y * x) ^ (2 : ℕ) - 1 := by
  let nodes := gaussNodes s m
  let term : ℝ → ℝ := fun x =>
    max 0 ((y * x) ^ (2 : ℕ) - 1) * eta / ((a - x) ^ (2 : ℕ) + eta ^ (2 : ℕ))
  have hden (x : ℝ) : 0 < (a - x) ^ (2 : ℕ) + eta ^ (2 : ℕ) :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos heta)
  have hterm_nonneg (x : ℝ) (hx : x ∈ nodes) : 0 ≤ term x :=
    div_nonneg (mul_nonneg (le_max_left _ _) heta.le) (hden x).le
  have hterm_pos_iff (x : ℝ) : 0 < term x ↔ 0 < (y * x) ^ (2 : ℕ) - 1 := by
    change 0 < max 0 ((y * x) ^ (2 : ℕ) - 1) * eta /
        ((a - x) ^ (2 : ℕ) + eta ^ (2 : ℕ)) ↔ 0 < (y * x) ^ (2 : ℕ) - 1
    by_cases hx : 0 < (y * x) ^ (2 : ℕ) - 1
    · rw [max_eq_right hx.le]
      exact ⟨fun _ => hx, fun _ => div_pos (mul_pos hx heta) (hden x)⟩
    · have hle : (y * x) ^ (2 : ℕ) - 1 ≤ 0 := le_of_not_gt hx
      rw [max_eq_left hle]
      simp only [zero_mul, zero_div, lt_self_iff_false]
      constructor
      · intro hfalse
        contradiction
      · intro hpos
        exact (hx hpos).elim
  rw [gaussSuperApexNullFlagPoissonSource,
    show gaussNodes s m = nodes by rfl,
    show (∑ x ∈ nodes,
      max 0 ((y * x) ^ (2 : ℕ) - 1) * eta / ((a - x) ^ (2 : ℕ) + eta ^ (2 : ℕ))) =
        ∑ x ∈ nodes, term x by rfl,
    Finset.sum_pos_iff_of_nonneg hterm_nonneg]
  constructor
  · rintro ⟨x, hxmem, hxterm⟩
    exact ⟨x, hxmem, (hterm_pos_iff x).mp hxterm⟩
  · rintro ⟨x, hxmem, hxsource⟩
    exact ⟨x, hxmem, (hterm_pos_iff x).mpr hxsource⟩

end HTGeometry
