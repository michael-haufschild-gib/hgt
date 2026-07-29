import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# A bounded Weyl character retains its unbounded generator in its tangent value

For a real charge `q`, the scalar one-parameter unitary character

```text
chi_q(t) = exp(-i q t)
```

has unit modulus on the real parameter axis, while its derivative at the identity is
`-i q`.  Consequently `i chi_q'(0) = q`.  A uniformly bounded family of phase values can
therefore retain an unbounded charge in its tangent without asking any one bounded observable to
equal that charge.

This is the scalar value core of the Weyl/Stone description of a one-parameter quantum symmetry.
It is useful in the hypertranscendental constraint corpus whenever a fixed bounded response is too
small but a differentiable phase character is available.  No operator generator, domain claim, or
flow equation is asserted here.

Primary provenance: H. Weyl, *Quantenmechanik und Gruppentheorie*, Z. Phys. 46 (1927), 1--46,
DOI 10.1007/BF02055756; M. H. Stone, *Linear Transformations in Hilbert Space. III. Operational
Methods and Group Theory*, PNAS 16 (1930), 172--175, DOI 10.1073/pnas.16.2.172; E. P. Wigner,
*Lower Limit for the Energy Derivative of the Scattering Phase Shift*, Phys. Rev. 98 (1955),
145--147, DOI 10.1103/PhysRev.98.145; F. T. Smith, *Lifetime Matrix in Collision Theory*,
Phys. Rev. 118 (1960), 349--356, DOI 10.1103/PhysRev.118.349.
-/

namespace HTGeometry

noncomputable section

/-- Scalar Weyl character with real generator/charge `q`.  The complex parameter keeps the
derivative statement inside ordinary complex analysis; its restriction to the real axis is
unitary. -/
def scalarWeylCharacter (q : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (q : ℂ) * z)

@[simp]
theorem scalarWeylCharacter_zero (q : ℝ) :
    scalarWeylCharacter q 0 = 1 := by
  simp [scalarWeylCharacter]

/-- Characters add their generators by multiplication. -/
theorem scalarWeylCharacter_add_charge (q r : ℝ) (z : ℂ) :
    scalarWeylCharacter (q + r) z =
      scalarWeylCharacter q z * scalarWeylCharacter r z := by
  simp only [scalarWeylCharacter]
  rw [← Complex.exp_add]
  push_cast
  congr 1
  ring

/-- The Weyl character is a one-parameter representation of the additive parameter group. -/
theorem scalarWeylCharacter_add_parameter (q : ℝ) (z w : ℂ) :
    scalarWeylCharacter q (z + w) =
      scalarWeylCharacter q z * scalarWeylCharacter q w := by
  simp only [scalarWeylCharacter]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Every real-parameter phase value has exactly unit norm, independently of the size of its
generator. -/
theorem norm_scalarWeylCharacter_ofReal (q t : ℝ) :
    ‖scalarWeylCharacter q (t : ℂ)‖ = 1 := by
  rw [scalarWeylCharacter, Complex.norm_exp]
  have hre : (-Complex.I * (q : ℂ) * (t : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- Differential form of the scalar Weyl law. -/
theorem hasDerivAt_scalarWeylCharacter (q : ℝ) (z : ℂ) :
    HasDerivAt (scalarWeylCharacter q)
      (-Complex.I * (q : ℂ) * scalarWeylCharacter q z) z := by
  have hlinear :
      HasDerivAt (fun w : ℂ => -Complex.I * (q : ℂ) * w)
        (-Complex.I * (q : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul (-Complex.I * (q : ℂ))
  rw [scalarWeylCharacter]
  exact hlinear.cexp.congr_deriv (by ring)

/-- Pointwise derivative of the scalar Weyl character. -/
theorem deriv_scalarWeylCharacter (q : ℝ) (z : ℂ) :
    deriv (scalarWeylCharacter q) z =
      -Complex.I * (q : ℂ) * scalarWeylCharacter q z :=
  (hasDerivAt_scalarWeylCharacter q z).deriv

/-- The tangent of the bounded character at the identity is its skew generator. -/
@[simp]
theorem deriv_scalarWeylCharacter_zero (q : ℝ) :
    deriv (scalarWeylCharacter q) 0 = -Complex.I * (q : ℂ) := by
  rw [deriv_scalarWeylCharacter]
  simp

/-- **Stone generator value.**  Multiplication by `i` recovers the full real charge from the
identity tangent of the unit-modulus character. -/
theorem I_mul_deriv_scalarWeylCharacter_zero (q : ℝ) :
    Complex.I * deriv (scalarWeylCharacter q) 0 = (q : ℂ) := by
  rw [deriv_scalarWeylCharacter_zero]
  calc
    Complex.I * (-Complex.I * (q : ℂ)) =
        -(Complex.I * Complex.I) * (q : ℂ) := by ring
    _ = (q : ℂ) := by rw [Complex.I_mul_I]; ring

/-- A fixed bound on all real phase values imposes no bound on the recovered tangent charge.  This
is the precise value-level escape from arguments that try to represent a growing source by one
fixed bounded detector. -/
theorem scalarWeylCharacter_bounded_and_generator_exact (q : ℝ) :
    (∀ t : ℝ, ‖scalarWeylCharacter q (t : ℂ)‖ = 1) ∧
      Complex.I * deriv (scalarWeylCharacter q) 0 = (q : ℂ) := by
  exact ⟨norm_scalarWeylCharacter_ofReal q,
    I_mul_deriv_scalarWeylCharacter_zero q⟩

/-- **Scalar Wigner--Smith value.**  The relative phase derivative recovers the same real charge
at every real parameter, not only at the identity.  The conjugate phase removes the arbitrary
point on the unitary orbit. -/
def scalarWeylWignerSmithValue (q t : ℝ) : ℂ :=
  Complex.I * (starRingEnd ℂ) (scalarWeylCharacter q (t : ℂ)) *
    deriv (scalarWeylCharacter q) (t : ℂ)

/-- The Wigner--Smith value of a scalar Weyl channel is exactly its generator everywhere on the
real parameter axis. -/
theorem scalarWeylWignerSmithValue_eq (q t : ℝ) :
    scalarWeylWignerSmithValue q t = (q : ℂ) := by
  let χ := scalarWeylCharacter q (t : ℂ)
  have hnorm : ‖χ‖ = 1 := by
    simpa only [χ] using norm_scalarWeylCharacter_ofReal q t
  have hphase : (starRingEnd ℂ) χ * χ = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [scalarWeylWignerSmithValue, deriv_scalarWeylCharacter]
  change Complex.I * (starRingEnd ℂ) χ *
      (-Complex.I * (q : ℂ) * χ) = (q : ℂ)
  calc
    Complex.I * (starRingEnd ℂ) χ * (-Complex.I * (q : ℂ) * χ) =
        (q : ℂ) * ((starRingEnd ℂ) χ * χ) := by
          ring_nf
          rw [Complex.I_sq]
          ring
    _ = (q : ℂ) := by rw [hphase, mul_one]

end

end HTGeometry
