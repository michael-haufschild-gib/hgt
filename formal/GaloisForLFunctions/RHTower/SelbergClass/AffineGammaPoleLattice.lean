import GaloisForLFunctions.RHTower.SelbergClass.GammaPoleOrder

/-!
# Affine Gamma-pole lattices

This is the exact pole geometry used by the Gamma factors in the
Kaczorowski--Perelli contour argument.  It does not assert a contour shift,
compute a residue, or claim that a contour is globally pole-free.

For the concrete factor `w ↦ Gamma (b * w + A)`, its poles are solved as the
horizontal arithmetic lattice `- (A + n) / b`.  The order classification is
inherited from `GammaPoleOrder`; this file supplies the coordinate and spacing
geometry needed to select and audit contour lines.  A factor `Gamma (A - b*w)`
is obtained by instantiating the order and lattice theorems with `b := -b`.
-/

open Complex Filter Set

namespace RHTower

noncomputable section

/-- The `n`th pole of the concrete affine Gamma factor
`w ↦ Gamma (b * w + A)`. -/
def affineGammaAddPole (A : ℂ) (b : ℝ) (n : ℕ) : ℂ :=
  -((A + (n : ℂ)) / (b : ℂ))

/-- Exact pole lattice of the concrete affine Gamma factor
`w ↦ Gamma (b * w + A)`. -/
def affineGammaAddPoleLattice (A : ℂ) (b : ℝ) : Set ℂ :=
  {w | ∃ n : ℕ, w = affineGammaAddPole A b n}

/-- Substituting the explicit lattice point into the affine Gamma argument
recovers its `n`th nonpositive integer. -/
theorem affineGammaAddPole_argument (A : ℂ) {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    (b : ℂ) * affineGammaAddPole A b n + A = -(n : ℂ) := by
  unfold affineGammaAddPole
  have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
  field_simp
  ring

/-- Exact solution of the affine equation defining a Gamma pole. -/
theorem affineGammaAdd_argument_eq_neg_nat_iff (A w : ℂ) {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    (b : ℂ) * w + A = -(n : ℂ) ↔ w = affineGammaAddPole A b n := by
  constructor
  · intro h
    unfold affineGammaAddPole
    have hbC : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
    have hdiv : w = -(A + (n : ℂ)) / (b : ℂ) := by
      apply (eq_div_iff hbC).mpr
      calc
        w * (b : ℂ) = (b : ℂ) * w := by ring
        _ = -(n : ℂ) - A := (eq_sub_iff_add_eq).mpr h
        _ = -(A + (n : ℂ)) := by ring
    calc
      w = -(A + (n : ℂ)) / (b : ℂ) := hdiv
      _ = -((A + (n : ℂ)) / (b : ℂ)) := by ring
  · intro h
    rw [h]
    exact affineGammaAddPole_argument A hb n

/-- Real coordinate of an affine Gamma pole. -/
theorem affineGammaAddPole_re (A : ℂ) {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    (affineGammaAddPole A b n).re = -(A.re + n) / b := by
  unfold affineGammaAddPole
  simp [Complex.div_re]
  field_simp [hb]
  ring

/-- Every pole of one affine Gamma factor lies at its one fixed imaginary
height. -/
theorem affineGammaAddPole_im (A : ℂ) {b : ℝ} (hb : b ≠ 0) (n : ℕ) :
    (affineGammaAddPole A b n).im = -A.im / b := by
  unfold affineGammaAddPole
  simp [Complex.div_im]
  field_simp [hb]

/-- Consecutive poles of a positive-slope affine Gamma factor have exact real
spacing `b⁻¹`. -/
theorem affineGammaAddPole_re_succ (A : ℂ) {b : ℝ} (hb : 0 < b) (n : ℕ) :
    (affineGammaAddPole A b (n + 1)).re =
      (affineGammaAddPole A b n).re - b⁻¹ := by
  rw [affineGammaAddPole_re A hb.ne' (n + 1), affineGammaAddPole_re A hb.ne' n]
  push_cast
  field_simp
  ring

/-- For positive slope, the pole lattice is strictly decreasing in its real
coordinate.  Thus a vertical contour can meet this factor at most once. -/
theorem affineGammaAddPole_re_strictAnti (A : ℂ) {b : ℝ} (hb : 0 < b) :
    StrictAnti (fun n : ℕ ↦ (affineGammaAddPole A b n).re) := by
  intro m n hmn
  change (affineGammaAddPole A b n).re < (affineGammaAddPole A b m).re
  rw [affineGammaAddPole_re A hb.ne' m, affineGammaAddPole_re A hb.ne' n]
  have hcast : (m : ℝ) < n := by exact_mod_cast hmn
  apply (div_lt_div_iff₀ hb hb).mpr
  have hmul : (m : ℝ) * b < (n : ℝ) * b :=
    mul_lt_mul_of_pos_right hcast hb
  nlinarith

/-- A positive-slope affine Gamma pole index is uniquely determined by its
real coordinate. -/
theorem affineGammaAddPole_re_injective (A : ℂ) {b : ℝ} (hb : 0 < b) :
    Function.Injective (fun n : ℕ ↦ (affineGammaAddPole A b n).re) := by
  exact (affineGammaAddPole_re_strictAnti A hb).injective

/-- Exact vertical-line uniqueness for the positive-slope affine Gamma pole
lattice. -/
theorem affineGammaAddPole_re_eq_iff (A : ℂ) {b : ℝ} (hb : 0 < b) (m n : ℕ) :
    (affineGammaAddPole A b m).re = (affineGammaAddPole A b n).re ↔ m = n := by
  constructor
  · intro h
    exact affineGammaAddPole_re_injective A hb h
  · intro h
    subst n
    rfl

/-- All poles of a fixed affine Gamma factor lie on one horizontal line. -/
theorem affineGammaAddPole_im_eq (A : ℂ) {b : ℝ} (hb : b ≠ 0) (m n : ℕ) :
    (affineGammaAddPole A b m).im = (affineGammaAddPole A b n).im := by
  rw [affineGammaAddPole_im A hb m, affineGammaAddPole_im A hb n]

/-- Exact simple-pole classification in the explicit affine lattice form. -/
theorem meromorphicOrderAt_gamma_affineAdd_eq_neg_one_iff
    (A w : ℂ) {b : ℝ} (hb : b ≠ 0) :
    meromorphicOrderAt (fun z : ℂ ↦ Gamma ((b : ℂ) * z + A)) w = (-1 : ℤ) ↔
      ∃ n : ℕ, w = affineGammaAddPole A b n := by
  rw [Complex.meromorphicOrderAt_Gamma_affine_eq_neg_one_iff b hb A w]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (affineGammaAdd_argument_eq_neg_nat_iff A w hb n).mp hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, (affineGammaAdd_argument_eq_neg_nat_iff A w hb n).mpr hn⟩

/-- Membership in the concrete affine pole lattice is equivalent to a simple
Gamma pole, with no unproved contour premise. -/
theorem mem_affineGammaAddPoleLattice_iff_meromorphicOrderAt_gamma_affineAdd_eq_neg_one
    (A w : ℂ) {b : ℝ} (hb : b ≠ 0) :
    w ∈ affineGammaAddPoleLattice A b ↔
      meromorphicOrderAt (fun z : ℂ ↦ Gamma ((b : ℂ) * z + A)) w = (-1 : ℤ) := by
  change (∃ n : ℕ, w = affineGammaAddPole A b n) ↔ _
  exact (meromorphicOrderAt_gamma_affineAdd_eq_neg_one_iff A w hb).symm

end

end RHTower
