/-
The mirror identity and the incidence map (MWM lane, M8 — task #127; doc 16 §3,
verified numerically to 30 digits in R9-RESULTS.md before formalization).

Abstract layer: for any FE-paired functions Λ₁(1−s) = ε·Λ₂(s), Λ₂(1−s) = ε'·Λ₁(s),
the two-parameter PENCIL c·Λ₁ + d·Λ₂ satisfies

* `pencil_mirror` — reflection s ↦ 1−s is the parameter involution
  (c, d) ↦ (d·ε', c·ε);
* `pencil_fe_unit` — ε·ε' = 1 (so the involution is involutive on zeros:
  `pencil_mirror_zero_iff`);
* `pencil_conj_symm` / `pencil_conj_zero` — members with d = conj c are
  real-symmetric when Λ₂ is the conjugate-dual of Λ₁;
* `incidence` / `pencil_eq_zero_iff_incidence` — the pencil is LINEAR in (c, d), so
  the member through any point s₀ is exact algebra: c/d = −Λ₂(s₀)/Λ₁(s₀). The entire
  family dynamics (measured in R3/R5/R5b) is the level-set geometry of this one
  meromorphic function.

Dirichlet layer: `dirichletXi χ := N^{s/2}·completedLFunction χ` renormalizes
mathlib's completed L so the functional equation has a CONSTANT root number:
`dirichletXi_one_sub : dirichletXi χ (1−s) = rootNumber χ · dirichletXi χ⁻¹ s`
(for primitive χ), and `dirichlet_pencil_mirror` instantiates the mirror identity on
actual Dirichlet pencils — the family of the R3/R5 measurement campaigns (χ mod 5,
D–H at the FE fixed point).
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace RHTower

open Complex DirichletCharacter

/-- The two-parameter pencil spanned by a pair of functions. -/
noncomputable def pencil (Λ₁ Λ₂ : ℂ → ℂ) (c d : ℂ) : ℂ → ℂ :=
  fun s => c * Λ₁ s + d * Λ₂ s

section Abstract

variable {Λ₁ Λ₂ : ℂ → ℂ} {ε ε' : ℂ}

/-- **The mirror identity.** Reflection `s ↦ 1−s` acts on the pencil as the parameter
involution `(c, d) ↦ (d·ε', c·ε)`. -/
theorem pencil_mirror (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s)
    (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s) (c d s : ℂ) :
    pencil Λ₁ Λ₂ c d (1 - s) = pencil Λ₁ Λ₂ (d * ε') (c * ε) s := by
  simp only [pencil]
  rw [hFE₁, hFE₂]
  ring

/-- The FE pair multiplies to `1` (read off at any nonvanishing point). -/
theorem pencil_fe_unit (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s)
    (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s) {s₀ : ℂ} (h0 : Λ₁ s₀ ≠ 0) :
    ε * ε' = 1 := by
  have h1 : Λ₁ (1 - (1 - s₀)) = ε * Λ₂ (1 - s₀) := hFE₁ (1 - s₀)
  rw [hFE₂ s₀, show (1 : ℂ) - (1 - s₀) = s₀ from by ring] at h1
  have h2 : (ε * ε') * Λ₁ s₀ = 1 * Λ₁ s₀ := by
    linear_combination -h1
  exact mul_right_cancel₀ h0 h2

/-- Applying the mirror twice returns the original member scaled by `ε·ε'`. -/
theorem pencil_mirror_sq (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s)
    (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s) (c d ρ : ℂ) :
    pencil Λ₁ Λ₂ (d * ε') (c * ε) (1 - ρ) = (ε * ε') * pencil Λ₁ Λ₂ c d ρ := by
  simp only [pencil]
  rw [hFE₁, hFE₂]
  ring

/-- **Zero-set mirror**: `ρ` is a zero of the member `(c,d)` iff `1−ρ` is a zero of
the mirrored member `(d·ε', c·ε)`. -/
theorem pencil_mirror_zero_iff (hFE₁ : ∀ s, Λ₁ (1 - s) = ε * Λ₂ s)
    (hFE₂ : ∀ s, Λ₂ (1 - s) = ε' * Λ₁ s) (hunit : ε * ε' = 1) {c d ρ : ℂ} :
    pencil Λ₁ Λ₂ (d * ε') (c * ε) (1 - ρ) = 0 ↔ pencil Λ₁ Λ₂ c d ρ = 0 := by
  rw [pencil_mirror_sq hFE₁ hFE₂, hunit, one_mul]

/-- Members with `d = conj c` are real-symmetric when `Λ₂` is the conjugate-dual of
`Λ₁` (`Λ₂(s) = conj Λ₁(conj s)` — the χ̄-relation). -/
theorem pencil_conj_symm (hdual : ∀ s, Λ₂ s = (starRingEnd ℂ) (Λ₁ ((starRingEnd ℂ) s)))
    (c s : ℂ) :
    pencil Λ₁ Λ₂ c ((starRingEnd ℂ) c) ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (pencil Λ₁ Λ₂ c ((starRingEnd ℂ) c) s) := by
  simp only [pencil, hdual, map_add, map_mul, Complex.conj_conj]
  ring

/-- Zeros of real-symmetric members come in conjugate pairs. -/
theorem pencil_conj_zero (hdual : ∀ s, Λ₂ s = (starRingEnd ℂ) (Λ₁ ((starRingEnd ℂ) s)))
    {c ρ : ℂ} (h0 : pencil Λ₁ Λ₂ c ((starRingEnd ℂ) c) ρ = 0) :
    pencil Λ₁ Λ₂ c ((starRingEnd ℂ) c) ((starRingEnd ℂ) ρ) = 0 := by
  rw [pencil_conj_symm hdual, h0, map_zero]

/-- **The incidence map**: the ratio of the unique pencil member vanishing at a given
point. The pencil is linear in `(c,d)`, so the member through any point is exact
algebra; the entire family's zero dynamics is the level-set geometry of this one
meromorphic function (zeros of the member with ratio `r` = the level curve
`incidence = r`). -/
noncomputable def incidence (Λ₁ Λ₂ : ℂ → ℂ) (s : ℂ) : ℂ := -Λ₂ s / Λ₁ s

/-- A pencil member vanishes at `s₀` iff its ratio equals the incidence value. -/
theorem pencil_eq_zero_iff_incidence {c d s₀ : ℂ} (hd : d ≠ 0) (hΛ : Λ₁ s₀ ≠ 0) :
    pencil Λ₁ Λ₂ c d s₀ = 0 ↔ c / d = incidence Λ₁ Λ₂ s₀ := by
  simp only [pencil, incidence]
  rw [div_eq_div_iff hd hΛ]
  constructor
  · intro h
    linear_combination h
  · intro h
    linear_combination h

end Abstract

section Dirichlet

variable {N : ℕ} [NeZero N]

/-- The `N^{s/2}`-renormalized completed Dirichlet L-function: with this normalization
the functional equation has a CONSTANT root number. -/
noncomputable def dirichletXi (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  fun s => (N : ℂ) ^ (s / 2) * completedLFunction χ s

/-- **Constant-ε functional equation** for the renormalized completed L-function of a
primitive character: `dirichletXi χ (1−s) = rootNumber χ · dirichletXi χ⁻¹ s`. -/
theorem dirichletXi_one_sub {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (s : ℂ) :
    dirichletXi χ (1 - s) = rootNumber χ * dirichletXi χ⁻¹ s := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [dirichletXi]
  rw [hχ.completedLFunction_one_sub s, ← mul_assoc, ← mul_assoc,
    ← cpow_add _ _ hN, show (1 - s) / 2 + (s - 1 / 2) = s / 2 from by ring]
  ring

/-- The mirror identity on actual Dirichlet pencils (the R3/R5 measurement family):
reflection across the critical line is the parameter involution
`(c, d) ↦ (d·rootNumber χ⁻¹, c·rootNumber χ)`. -/
theorem dirichlet_pencil_mirror {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hχ' : (χ⁻¹).IsPrimitive) (c d s : ℂ) :
    pencil (dirichletXi χ) (dirichletXi χ⁻¹) c d (1 - s) =
      pencil (dirichletXi χ) (dirichletXi χ⁻¹)
        (d * rootNumber χ⁻¹) (c * rootNumber χ) s := by
  refine pencil_mirror (fun t => dirichletXi_one_sub hχ t) (fun t => ?_) c d s
  have h := dirichletXi_one_sub hχ' t
  rwa [inv_inv χ] at h

end Dirichlet

end RHTower
