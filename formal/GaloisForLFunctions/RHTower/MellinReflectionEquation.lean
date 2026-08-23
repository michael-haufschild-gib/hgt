import GaloisForLFunctions.RHTower.MellinContinuationOrder
import GaloisForLFunctions.RHTower.PrimeZeroSusceptibility

/-!
# The functional equation of the continued Mellin transform, and Burnol's reflection

Burnol's left vertical edge is reduced to a right vertical edge by

`G(1−s)/ζ(1−s) = F₊(G)(s)/ζ(s)`.

In the concrete model this is an *identity of definitions*: the numerator left of the critical line
is by construction

`N_a(c,d,f)(s) = χ(s)·N_a(d,c,F f)(1−s)`,

and the archimedean multiplier `χ` is exactly the one in the functional equation of `ζ`.  Dividing,
the Burnol edge integrand of `(f, Z)` at `s` is minus the edge integrand of `(F f, 1−Z)` at `1−s`.

## Main results

* `burnolChiFactor_eq_chiFE_one_sub`, `riemannZeta_eq_burnolChiFactor_mul_one_sub`
* `extendedMellinNumerator_reflect`, `extendedMellinContinuation_reflect`
* `burnolEdgeIntegrand`, `burnolIntegrand_eq_smul_edge`
* `burnolEdgeIntegrand_reflect` — **the left edge is the reflected right edge**.
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## `χ` and the functional equation of `ζ` -/

theorem burnolChiFactor_eq_chiFE_one_sub (s : ℂ) : burnolChiFactor s = Susceptibility.chiFE (1 - s) := by
  rw [burnolChiFactor, Susceptibility.chiFE]
  have hexp : -(1 - s) = s - 1 := by ring
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2)
      = Complex.cos ((Real.pi : ℂ) * (s - 1) / 2) := by
    rw [show (Real.pi : ℂ) * (1 - s) / 2 = -((Real.pi : ℂ) * (s - 1) / 2) by ring,
      Complex.cos_neg]
  rw [hexp, hcos]
  push_cast
  ring

/-- **The functional equation in Burnol's normalisation.** -/
theorem riemannZeta_eq_burnolChiFactor_mul_one_sub {s : ℂ} (hint : ∀ m : ℤ, s ≠ (m : ℂ)) :
    riemannZeta s = burnolChiFactor s * riemannZeta (1 - s) := by
  have hs : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
    intro n hn
    refine hint (1 + (n : ℤ)) ?_
    have : s = 1 + (n : ℂ) := by linear_combination -hn
    rw [this]
    push_cast
    ring
  have hs' : (1 - s) ≠ 1 := by
    intro h
    exact hint 0 (by push_cast; linear_combination -h)
  have h := Susceptibility.riemannZeta_one_sub_chiFE hs hs'
  rw [show (1 : ℂ) - (1 - s) = s by ring] at h
  rw [h, burnolChiFactor_eq_chiFE_one_sub]

/-- `χ` is nonvanishing away from the integers. -/
theorem burnolChiFactor_ne_zero {s : ℂ} (hint : ∀ m : ℤ, s ≠ (m : ℂ)) :
    burnolChiFactor s ≠ 0 := by
  rw [burnolChiFactor]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · refine Complex.Gamma_ne_zero ?_
    intro n hn
    refine hint (1 + (n : ℤ)) ?_
    have : s = 1 + (n : ℂ) := by linear_combination -hn
    rw [this]; push_cast; ring
  · refine cpow_ne_zero_iff.2 (Or.inl ?_)
    exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
  · refine mul_ne_zero two_ne_zero ?_
    intro hcos
    rw [Complex.cos_eq_zero_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    refine hint (2 * k + 2) ?_
    have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    have : (Real.pi : ℂ) * (s - 1) = (Real.pi : ℂ) * ((2 * (k : ℂ) + 2) - 1) := by
      field_simp at hk ⊢
      linear_combination hk
    have hs := mul_left_cancel₀ hpi this
    push_cast
    linear_combination hs

/-! ## The functional equation of the numerator -/

theorem extendedMellinNumeratorLeft_eq_chi_mul (a : ℝ) (c d : ℂ) (f : SoninL2) (s : ℂ) :
    extendedMellinNumeratorLeft a c d f s
      = burnolChiFactor s * extendedMellinNumeratorRight a d c (fourierUnitary f) (1 - s) := by
  rw [extendedMellinNumeratorLeft, extendedMellinNumeratorRight]
  rw [show (1 : ℂ) - (1 - s) = s by ring]
  ring

/-- **The functional equation of the entire numerator.** -/
theorem extendedMellinNumerator_reflect (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : s.re < 1 / 2) :
    extendedMellinNumerator a c d f s
      = burnolChiFactor s * extendedMellinNumerator a d c (fourierUnitary f) (1 - s) := by
  have hre : (1 : ℝ) / 2 ≤ ((1 : ℂ) - s).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  rw [extendedMellinNumerator_eq_left a c d f hs,
    extendedMellinNumerator_eq_right a d c (fourierUnitary f) hre,
    extendedMellinNumeratorLeft_eq_chi_mul]

/-- **The functional equation of the continued Mellin transform.** -/
theorem extendedMellinContinuation_reflect (a : ℝ) (c d : ℂ) (f : SoninL2) {s : ℂ}
    (hs : s.re < 1 / 2) :
    extendedMellinContinuation a c d f s
      = burnolChiFactor s * extendedMellinContinuation a d c (fourierUnitary f) (1 - s) := by
  rw [extendedMellinContinuation, extendedMellinContinuation,
    extendedMellinNumerator_reflect a c d f hs]
  rw [show (1 : ℂ) - (1 - s) = s by ring]
  rw [mul_comm s (1 - s)]
  ring

/-! ## The edge integrand -/

/-- Burnol's integrand without the constant factor `ζ(Z)`: this is what the edge estimates use. -/
def burnolEdgeIntegrand (G : ℂ → ℂ) (Z : ℂ) : ℂ → ℂ :=
  fun s => G s * (riemannZeta s)⁻¹ * (Z - s)⁻¹

theorem burnolIntegrand_eq_smul_edge (G : ℂ → ℂ) (Z : ℂ) (s : ℂ) :
    burnolIntegrand G Z s = riemannZeta Z * burnolEdgeIntegrand G Z s := by
  rw [burnolIntegrand, burnolEdgeIntegrand, div_eq_mul_inv, mul_inv]
  ring

/-- **Burnol's reflection.**  Off the integers and left of the critical line, the edge integrand of
`(f, Z)` is minus the edge integrand of the Fourier-transformed datum at `1 − s`. -/
theorem burnolEdgeIntegrand_reflect (a : ℝ) (c d : ℂ) (f : SoninL2) (Z : ℂ) {s : ℂ}
    (hs : s.re < 1 / 2) (hint : ∀ m : ℤ, s ≠ (m : ℂ)) :
    burnolEdgeIntegrand (extendedMellinContinuation a c d f) Z s
      = -burnolEdgeIntegrand (extendedMellinContinuation a d c (fourierUnitary f)) (1 - Z)
          (1 - s) := by
  have hchi : burnolChiFactor s ≠ 0 := burnolChiFactor_ne_zero hint
  have hζ : riemannZeta s = burnolChiFactor s * riemannZeta (1 - s) :=
    riemannZeta_eq_burnolChiFactor_mul_one_sub hint
  have hsub : (1 - Z) - (1 - s) = -(Z - s) := by ring
  rw [burnolEdgeIntegrand, burnolEdgeIntegrand, extendedMellinContinuation_reflect a c d f hs, hζ,
    hsub, mul_inv, inv_neg]
  field_simp

end

end RHTower
