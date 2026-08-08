import GaloisForLFunctions.HTGeometry.AutomorphyLogarithmDefect

/-!
# Nondegeneracy turns semi-definiteness into definiteness

The Hermitian form attached to an alternating compatible form `E` has real part the symmetric
`R`-bilinear form

`S (u, v) = E (i u, v)`,

and `Re H (x, x) = S (x, x)`.  Symmetry of `S` is the `i`-invariance of `E` combined with
alternation.  Cauchy--Schwarz for a positive semi-definite symmetric form then says that a null
vector of `S` is orthogonal to everything, so a semi-definite `S` with trivial radical is definite.

This is the step at which nondegeneracy of a periodic meromorphic function is converted into strict
positivity of the Hermitian form: the radical of `S` consists of directions the form cannot see, and
fullness of the period group is exactly the statement that there are none.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The symmetric real form underlying the Hermitian form of an alternating compatible form. -/
def altSym (E : V → V → ℝ) (u v : V) : ℝ := E (Complex.I • u) v

theorem altSym_eq_hermitian_re (E : V → V → ℝ) (u v : V) :
    altSym E u v = (hermitianOfAlternating E u v).re :=
  (hermitianOfAlternating_re E u v).symm

/-- **Cauchy--Schwarz in degenerate form.**  Stated for any real form whose diagonal expands
quadratically along a one-parameter family: a null vector of a positive semi-definite such form is
orthogonal to the whole space.  The proof avoids limits -- at `t = ±|S (u,v)|/(1 + S (v,v))` the
expansion is already contradictory. -/
theorem symmBilin_eq_zero_of_self_eq_zero {X : Type*} {S : X → X → ℝ} {comb : ℝ → X → X → X}
    (hexp : ∀ (t : ℝ) (u v : X), S (comb t u v) (comb t u v)
      = S u u + 2 * t * S u v + t ^ 2 * S v v)
    (hpsd : ∀ x : X, 0 ≤ S x x) {u : X} (hu : S u u = 0) (v : X) : S u v = 0 := by
  by_contra hne
  have hvv : 0 ≤ S v v := hpsd v
  set s : ℝ := |S u v| / (1 + S v v) with hs
  have hden : (0 : ℝ) < 1 + S v v := by linarith
  have habs : 0 < |S u v| := abs_pos.mpr hne
  have hspos : 0 < s := by rw [hs]; positivity
  have hfrac : s * S v v ≤ |S u v| := by
    rw [hs, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [habs.le, hvv]
  have hkey : s ^ 2 * S v v ≤ s * |S u v| := by
    have hmul := mul_le_mul_of_nonneg_left hfrac hspos.le
    nlinarith [hmul]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hexp' := hexp s u v
    rw [hu] at hexp'
    have hnn : 0 ≤ S (comb s u v) (comb s u v) := hpsd _
    rw [hexp'] at hnn
    have habs' : |S u v| = -S u v := abs_of_neg hneg
    rw [habs'] at hkey
    nlinarith [hspos, hneg, hkey, hnn]
  · have hexp' := hexp (-s) u v
    rw [hu] at hexp'
    have hnn : 0 ≤ S (comb (-s) u v) (comb (-s) u v) := hpsd _
    rw [hexp'] at hnn
    have habs' : |S u v| = S u v := abs_of_pos hpos
    rw [habs'] at hkey
    nlinarith [hspos, hpos, hkey, hnn]

namespace IsAlternatingCompatible

variable {E : V → V → ℝ} (hE : IsAlternatingCompatible E)

include hE

theorem altSym_symm (u v : V) : altSym E v u = altSym E u v := by
  have h1 : E (Complex.I • v) u = E (Complex.I • (Complex.I • v)) (Complex.I • u) :=
    (hE.compat _ _).symm
  rw [altSym, altSym, h1, hE.smul_I_left, hE.alt v (Complex.I • u)]

theorem altSym_add_left (u v w : V) : altSym E (u + v) w = altSym E u w + altSym E v w := by
  simp only [altSym, smul_add, hE.add_left]

theorem altSym_smul_left (r : ℝ) (u v : V) : altSym E ((r : ℂ) • u) v = r * altSym E u v := by
  have hcomm : Complex.I • ((r : ℂ) • u) = (r : ℂ) • (Complex.I • u) := by
    rw [smul_smul, smul_smul, mul_comm]
  simp only [altSym, hcomm, hE.smul_left]

theorem altSym_add_right (u v w : V) : altSym E u (v + w) = altSym E u v + altSym E u w := by
  rw [← hE.altSym_symm, hE.altSym_add_left, hE.altSym_symm, hE.altSym_symm w u]

theorem altSym_smul_right (r : ℝ) (u v : V) : altSym E u ((r : ℂ) • v) = r * altSym E u v := by
  rw [← hE.altSym_symm, hE.altSym_smul_left, hE.altSym_symm]

/-- The quadratic expansion of the symmetric form along a real direction. -/
theorem altSym_expand (t : ℝ) (u v : V) :
    altSym E (u + (t : ℂ) • v) (u + (t : ℂ) • v)
      = altSym E u u + 2 * t * altSym E u v + t ^ 2 * altSym E v v := by
  have h1 : altSym E (u + (t : ℂ) • v) (u + (t : ℂ) • v)
      = altSym E u (u + (t : ℂ) • v) + altSym E ((t : ℂ) • v) (u + (t : ℂ) • v) :=
    hE.altSym_add_left _ _ _
  have h2 : altSym E u (u + (t : ℂ) • v) = altSym E u u + t * altSym E u v := by
    rw [hE.altSym_add_right, hE.altSym_smul_right]
  have h3 : altSym E ((t : ℂ) • v) (u + (t : ℂ) • v)
      = t * altSym E v u + t * (t * altSym E v v) := by
    rw [hE.altSym_add_right, hE.altSym_smul_left, hE.altSym_smul_left, hE.altSym_smul_right]
  rw [h1, h2, h3, hE.altSym_symm u v]
  ring

/-- Degenerate Cauchy--Schwarz for the symmetric form of an alternating compatible form. -/
theorem altSym_eq_zero_of_self_eq_zero (hpsd : ∀ x : V, 0 ≤ altSym E x x)
    {u : V} (hu : altSym E u u = 0) (v : V) : altSym E u v = 0 :=
  symmBilin_eq_zero_of_self_eq_zero (comb := fun t x y => x + ((t : ℝ) : ℂ) • y)
    (fun t x y => hE.altSym_expand t x y) hpsd hu v

/-- **Semi-definite plus nondegenerate is definite.** -/
theorem altSym_pos_of_psd_of_nondegenerate (hpsd : ∀ x : V, 0 ≤ altSym E x x)
    (hnd : ∀ x : V, x ≠ 0 → ∃ y, altSym E x y ≠ 0) {x : V} (hx : x ≠ 0) :
    0 < altSym E x x := by
  rcases (hpsd x).lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨y, hy⟩ := hnd x hx
    exact hy (hE.altSym_eq_zero_of_self_eq_zero hpsd h.symm y)

/-- **The certificate shape from semi-definiteness and nondegeneracy.** -/
theorem exists_hermitian_of_psd_of_nondegenerate (hpsd : ∀ x : V, 0 ≤ altSym E x x)
    (hnd : ∀ x : V, x ≠ 0 → ∃ y, altSym E x y ≠ 0) :
    ∃ H : V → V → ℂ,
      (∀ x y z, H (x + y) z = H x z + H y z) ∧
      (∀ (a : ℂ) (x y), H (a • x) y = a * H x y) ∧
      (∀ x y, H y x = star (H x y)) ∧
      (∀ x, x ≠ 0 → 0 < (H x x).re) ∧
      (∀ x y, (H x y).im = E x y) :=
  hE.exists_hermitian_of_alternating fun _ hx => hE.altSym_pos_of_psd_of_nondegenerate hpsd hnd hx

end IsAlternatingCompatible

end GaloisForLFunctions.HTGeometry
