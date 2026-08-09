import GaloisForLFunctions.RHTower.PowerLatticeResidue

/-!
# Ramification makes the lattice residues constant

Pulling a singular ray back through `ξ = -e^{±iα} η^s` transports the residue at a simple pole by
dividing by the derivative of the substitution.  At the lattice point `η = 2πn` the derivative is
`-e^{±iα} s (2πn)^{s-1}`, and the residue at `ξ = -(2πn)^s e^{±iα}` carries the factor
`(2πn)^s/n`.  The two `n`-dependences cancel exactly, leaving `±i/s`.

So the `n`-dependence in the residues of the transform is entirely an artefact of the unramified
coordinate: after the Newton-compatible substitution both lattices have constant residue.

* `GaloisForLFunctions.RHTower.residue_transport_pos`;
* `GaloisForLFunctions.RHTower.residue_transport_neg`.
-/

open Complex

namespace GaloisForLFunctions.RHTower

/-- **Residue transport along the `+` ray.**  The `n`-dependence cancels and the transported
residue is `i/s`. -/
theorem residue_transport_pos {s : ℝ} (hs : s ≠ 0) (α : ℝ) {n : ℕ} (hn : 0 < n) :
    ((((2 * Real.pi * (n : ℝ)) ^ s : ℝ) : ℂ) * Complex.exp ((α : ℝ) * Complex.I)
        / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)))
      / (-(Complex.exp ((α : ℝ) * Complex.I)) * (s : ℂ)
          * ((((2 * Real.pi * (n : ℝ)) ^ (s - 1) : ℝ)) : ℂ))
      = Complex.I / (s : ℂ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) < 2 * Real.pi * (n : ℝ) := by positivity
  have hstep : ((2 * Real.pi * (n : ℝ)) ^ s : ℝ)
      = ((2 * Real.pi * (n : ℝ)) ^ (s - 1) : ℝ) * (2 * Real.pi * (n : ℝ)) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp
  have hbne : ((((2 * Real.pi * (n : ℝ)) ^ (s - 1) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ne_of_gt (Real.rpow_pos_of_pos hx _))
  have hene : Complex.exp ((α : ℝ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  have hpine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hnne : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [hstep]
  push_cast
  field_simp
  rw [Complex.I_sq]

/-- **Residue transport along the `−` ray.**  The transported residue is `-i/s`. -/
theorem residue_transport_neg {s : ℝ} (hs : s ≠ 0) (α : ℝ) {n : ℕ} (hn : 0 < n) :
    (-((((2 * Real.pi * (n : ℝ)) ^ s : ℝ) : ℂ) * Complex.exp (-((α : ℝ) * Complex.I))
        / (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ))))
      / (-(Complex.exp (-((α : ℝ) * Complex.I))) * (s : ℂ)
          * ((((2 * Real.pi * (n : ℝ)) ^ (s - 1) : ℝ)) : ℂ))
      = -(Complex.I / (s : ℂ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hx : (0 : ℝ) < 2 * Real.pi * (n : ℝ) := by positivity
  have hstep : ((2 * Real.pi * (n : ℝ)) ^ s : ℝ)
      = ((2 * Real.pi * (n : ℝ)) ^ (s - 1) : ℝ) * (2 * Real.pi * (n : ℝ)) := by
    rw [Real.rpow_sub hx, Real.rpow_one]
    field_simp
  have hbne : ((((2 * Real.pi * (n : ℝ)) ^ (s - 1) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ne_of_gt (Real.rpow_pos_of_pos hx _))
  have hene : Complex.exp (-((α : ℝ) * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  have hpine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hnne : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [hstep]
  push_cast
  field_simp
  rw [Complex.I_sq]
  ring

end GaloisForLFunctions.RHTower
