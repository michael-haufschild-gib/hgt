import GaloisForLFunctions.RHTower.ConnesWeilRewriting

/-!
# Appendix II (12)-(16): the change of variables in the explicit formula

Appendix II (12)-(16) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

To compare Weil's explicit formula with the trace formula, Connes substitutes

  `|g|^{-1/2} h(g^{-1}) = F(|g|) Χ₀(g)`,                                       (12)

and rewrites Weil's `Φ` as a moment of `h`:

  `∫ h(g) Χ₀(g) |g|^{1/2+is} d^*g = Φ(1/2+is)`,  i.e.  `ĥ(Χ₀, ρ) = Φ(ρ)`.      (15)/(16)

The proof is the inversion substitution `g ↦ g^{-1}` on the idele class group, whose Haar measure
is inversion invariant, together with the two quasi-character laws
`|g^{-1}|^s = |g|^{-s}` and `Χ₀(g^{-1}) = Χ₀(g)^{-1}`.  Writing the modulus power through the
exponential (`connesModulusPower`) keeps every step free of branch conditions, so the statement
holds for an arbitrary complex exponent.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {G : Type*} [CommGroup G] [MeasurableSpace G] [MeasurableInv G]
  {μ : Measure G} [μ.IsInvInvariant]

set_option linter.unusedSectionVars false

/-- The quasi-character law `|x|^a |x|^b = |x|^{a+b}`. -/
theorem connesModulusPower_add (mod : G → ℝ) (a b : ℂ) (x : G) :
    connesModulusPower mod a x * connesModulusPower mod b x
      = connesModulusPower mod (a + b) x := by
  rw [connesModulusPower, connesModulusPower, connesModulusPower, ← Complex.exp_add]
  congr 1
  ring

/-- The quasi-character law `|x^{-1}|^s = |x|^{-s}`. -/
theorem connesModulusPower_inv {mod : G → ℝ} (hmodinv : ∀ g : G, mod g⁻¹ = (mod g)⁻¹)
    (s : ℂ) (x : G) :
    connesModulusPower mod s x⁻¹ = connesModulusPower mod (-s) x := by
  rw [connesModulusPower, connesModulusPower, hmodinv, Real.log_inv]
  congr 1
  push_cast
  ring

/-- **Appendix II (12) ⟶ (15)/(16).**  Under Connes' substitution the moment of `h` against the
character `Χ₀` at `1/2 + s` is Weil's `Φ(1/2 + s)`. -/
theorem connes_weil_mellin_change {mod : G → ℝ}
    (hmodinv : ∀ g : G, mod g⁻¹ = (mod g)⁻¹)
    {χ₀ : G → ℂ} (hχ0 : ∀ g : G, χ₀ g ≠ 0) (hχinv : ∀ g : G, χ₀ g⁻¹ = (χ₀ g)⁻¹)
    {h : G → ℂ} {F : ℝ → ℂ}
    (hrel : ∀ g : G, connesModulusPower mod (-(1 / 2 : ℂ)) g * h g⁻¹ = F (mod g) * χ₀ g)
    (s : ℂ) :
    connesHatMoment mod μ χ₀ ((1 / 2 : ℂ) + s) h
      = ∫ g : G, F (mod g) * connesModulusPower mod (-s) g ∂μ := by
  have hzero : ∀ x : G, connesModulusPower mod 0 x = 1 := by
    intro x
    simp [connesModulusPower]
  have hsub := (MeasureTheory.integral_inv_eq_self
    (fun g : G => h g * χ₀ g * connesModulusPower mod ((1 / 2 : ℂ) + s) g) μ).symm
  rw [connesHatMoment, hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  show h g⁻¹ * χ₀ g⁻¹ * connesModulusPower mod ((1 / 2 : ℂ) + s) g⁻¹
    = F (mod g) * connesModulusPower mod (-s) g
  have hmulP : connesModulusPower mod (1 / 2 : ℂ) g * connesModulusPower mod (-(1 / 2 : ℂ)) g
      = 1 := by
    rw [connesModulusPower_add]
    have : (1 / 2 : ℂ) + -(1 / 2 : ℂ) = 0 := by ring
    rw [this, hzero]
  have hh : h g⁻¹ = connesModulusPower mod (1 / 2 : ℂ) g * (F (mod g) * χ₀ g) := by
    rw [← hrel g, ← mul_assoc, hmulP, one_mul]
  have hcombine : connesModulusPower mod (1 / 2 : ℂ) g
      * connesModulusPower mod (-((1 / 2 : ℂ) + s)) g = connesModulusPower mod (-s) g := by
    rw [connesModulusPower_add]
    congr 1
    ring
  rw [hh, hχinv g, connesModulusPower_inv hmodinv]
  calc connesModulusPower mod (1 / 2 : ℂ) g * (F (mod g) * χ₀ g) * (χ₀ g)⁻¹
        * connesModulusPower mod (-((1 / 2 : ℂ) + s)) g
      = F (mod g) * (χ₀ g * (χ₀ g)⁻¹) * (connesModulusPower mod (1 / 2 : ℂ) g
          * connesModulusPower mod (-((1 / 2 : ℂ) + s)) g) := by ring
    _ = F (mod g) * connesModulusPower mod (-s) g := by
        rw [mul_inv_cancel₀ (hχ0 g), hcombine, mul_one]

end

end GaloisForLFunctions.RHTower
