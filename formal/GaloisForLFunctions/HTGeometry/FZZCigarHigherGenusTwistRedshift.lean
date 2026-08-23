import GaloisForLFunctions.HTGeometry.FZZCigarReplicaBackreaction

/-!
# Higher-genus FZZ holonomy is radial black-hole redshift

The higher-genus path-integral proof of FZZ duality does not leave torus twists in an abstract
modular sector.  For a cycle number `n` and complex twist `λ`, the first-order cigar fields obey

`β ↦ exp(2π i n λ) β`,
`γ ↦ exp(-2π i n λ) γ`,
`φ ↦ φ + 2π n Im(λ) / b`,

where `b = 1 / sqrt(k - 2)` is the radial linear-dilaton slope.  Consequently

`|exp(2π i n λ)| = exp(-b Δφ)`.

Thus a non-unit-modulus worldsheet holonomy is literally radial translation/redshift along the
Euclidean black-hole throat.  The opposite first-order field carries the reciprocal dilation, and
unitary holonomy is equivalent to zero radial monodromy.  This is the source-faithful
higher-genus mixing law needed before asking whether the torus replica-area insertion has an
arithmetic spectral decomposition.

No modular spectral parameter is identified with cigar radial momentum here.  Establishing such
a Ward lock for the torus one-point function remains the speculative RH-bearing step.

Physics source:

* Hikida--Schomerus, *The FZZ-Duality Conjecture -- A Proof*, arXiv:0805.3931,
  equations (4.1)--(4.2) and the higher-genus cigar path integral (4.14)--(4.18).
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FZZCigar

/-- Multiplier of the higher-genus first-order field `β` around one homology combination.
Physical cycle numbers are integers; retaining the integer type records that quantization. -/
def higherGenusBetaTwistMultiplier (n : ℤ) (twist : ℂ) : ℂ :=
  Complex.exp (((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I * twist)

/-- Reciprocal multiplier of the conjugate first-order field `γ`. -/
def higherGenusGammaTwistMultiplier (n : ℤ) (twist : ℂ) : ℂ :=
  Complex.exp (-(((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I * twist))

/-- Radial target-space monodromy forced by the same higher-genus twist. -/
def higherGenusRadialMonodromy (b : ℝ) (n : ℤ) (twist : ℂ) : ℝ :=
  2 * Real.pi * (n : ℝ) * twist.im / b

/-- The `β` and `γ` holonomies form the exact reciprocal dilation pair of the cigar first-order
system. -/
theorem higherGenusBetaTwist_mul_gammaTwist (n : ℤ) (twist : ℂ) :
    higherGenusBetaTwistMultiplier n twist * higherGenusGammaTwistMultiplier n twist = 1 := by
  rw [higherGenusBetaTwistMultiplier, higherGenusGammaTwistMultiplier,
    ← Complex.exp_add]
  ring_nf
  simp

/-- Exact twist/redshift identity: holonomy modulus is the exponential of minus radial
linear-dilaton work. -/
theorem norm_higherGenusBetaTwistMultiplier_eq_exp_neg_radialMonodromy
    {b : ℝ} (hb : b ≠ 0) (n : ℤ) (twist : ℂ) :
    ‖higherGenusBetaTwistMultiplier n twist‖ =
      Real.exp (-b * higherGenusRadialMonodromy b n twist) := by
  rw [higherGenusBetaTwistMultiplier, Complex.norm_exp]
  congr 1
  rw [higherGenusRadialMonodromy]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  field_simp [hb]
  ring

/-- The inverse first-order field carries the opposite radial dilation. -/
theorem norm_higherGenusGammaTwistMultiplier_eq_exp_radialMonodromy
    {b : ℝ} (hb : b ≠ 0) (n : ℤ) (twist : ℂ) :
    ‖higherGenusGammaTwistMultiplier n twist‖ =
      Real.exp (b * higherGenusRadialMonodromy b n twist) := by
  rw [higherGenusGammaTwistMultiplier, Complex.norm_exp]
  congr 1
  rw [higherGenusRadialMonodromy]
  simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  field_simp [hb]
  ring

/-- At physical positive dilaton slope, unit-modulus torus holonomy is equivalent to absence of
radial black-hole monodromy. -/
theorem norm_higherGenusBetaTwistMultiplier_eq_one_iff
    {b : ℝ} (hb : 0 < b) (n : ℤ) (twist : ℂ) :
    ‖higherGenusBetaTwistMultiplier n twist‖ = 1 ↔
      higherGenusRadialMonodromy b n twist = 0 := by
  rw [norm_higherGenusBetaTwistMultiplier_eq_exp_neg_radialMonodromy hb.ne' n twist,
    Real.exp_eq_one_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hb0 | hshift
    · exact absurd hb0 (neg_ne_zero.mpr hb.ne')
    · exact hshift
  · rintro hshift
    rw [hshift]
    ring

/-- Positive imaginary twist along a positive cycle contracts `β` and translates outward along
the radial linear-dilaton coordinate. -/
theorem higherGenusBetaTwist_contractive_of_im_pos
    {b : ℝ} (hb : 0 < b) {n : ℤ} (hn : 0 < n) {twist : ℂ} (htwist : 0 < twist.im) :
    0 < higherGenusRadialMonodromy b n twist ∧
      ‖higherGenusBetaTwistMultiplier n twist‖ < 1 := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hshift : 0 < higherGenusRadialMonodromy b n twist := by
    rw [higherGenusRadialMonodromy]
    exact div_pos (mul_pos (mul_pos (mul_pos zero_lt_two Real.pi_pos) hnReal) htwist) hb
  refine ⟨hshift, ?_⟩
  rw [norm_higherGenusBetaTwistMultiplier_eq_exp_neg_radialMonodromy hb.ne' n twist,
    Real.exp_lt_one_iff]
  exact neg_mul_neg_of_neg_of_pos (neg_neg_of_pos hb) hshift

end FZZCigar

end


end GaloisForLFunctions.HTGeometry
