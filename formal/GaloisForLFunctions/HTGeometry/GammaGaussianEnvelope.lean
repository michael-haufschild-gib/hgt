import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-!
# The universal Gamma–Gaussian multiplier

The entire multiplier

```text
A(s) = exp((s - 1/2)^2) · π^(s/2) / Γ(s/2)
```

is the centered Gaussian times the inverse archimedean factor `Γ_ℝ(s) = π^(-s/2) Γ(s/2)`.  Against
the even cosine-Fourier reflection factor

```text
χ(s) = π^(s - 1/2) Γ((1-s)/2) / Γ(s/2) = Γ_ℝ(1-s) / Γ_ℝ(s)
```

it satisfies the exact reflection identity

```text
χ(s) · A(1-s) = A(s),
```

because the Gaussian is invariant under `s ↦ 1 - s` and the two archimedean factors cancel.  Its
zero set is the even nonpositive lattice `{0, -2, -4, …}`, so `A` is a holomorphic unit on the whole
critical strip, and multiplying by `Γ_ℝ` returns the bare Gaussian.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- The even cosine-Fourier reflection factor `π^(s-1/2) Γ((1-s)/2)/Γ(s/2)`, written as the ratio of
archimedean factors. -/
def evenChiFactor (s : ℂ) : ℂ := Complex.Gammaℝ (1 - s) * (Complex.Gammaℝ s)⁻¹

/-- The universal Gamma–Gaussian multiplier `exp((s-1/2)^2) π^(s/2)/Γ(s/2)`. -/
def gammaGaussianEnvelope (s : ℂ) : ℂ := Complex.exp ((s - 1 / 2) ^ 2) * (Complex.Gammaℝ s)⁻¹

/-! ## The explicit shapes -/

/-- The reciprocal archimedean factor in explicit Gamma coordinates. -/
theorem inv_Gammaℝ_eq (s : ℂ) :
    (Complex.Gammaℝ s)⁻¹ = (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.Gammaℝ_def, mul_inv]
  congr 1
  rw [← Complex.cpow_neg]
  congr 1
  ring

/-- The multiplier in the explicit form `exp((s-1/2)^2) π^(s/2)/Γ(s/2)`. -/
theorem gammaGaussianEnvelope_eq (s : ℂ) :
    gammaGaussianEnvelope s
      = Complex.exp ((s - 1 / 2) ^ 2) * (Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹ := by
  rw [gammaGaussianEnvelope, inv_Gammaℝ_eq, mul_assoc]

/-- The reflection factor in the explicit form `π^(s-1/2) Γ((1-s)/2)/Γ(s/2)`. -/
theorem evenChiFactor_eq (s : ℂ) :
    evenChiFactor s
      = (Real.pi : ℂ) ^ (s - 1 / 2) * Complex.Gamma ((1 - s) / 2) * (Complex.Gamma (s / 2))⁻¹ := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [evenChiFactor, Complex.Gammaℝ_def, inv_Gammaℝ_eq]
  have hsplit : (Real.pi : ℂ) ^ (-(1 - s) / 2) * (Real.pi : ℂ) ^ (s / 2)
      = (Real.pi : ℂ) ^ (s - 1 / 2) := by
    rw [← Complex.cpow_add _ _ hpi]
    congr 1
    ring
  calc (Real.pi : ℂ) ^ (-(1 - s) / 2) * Complex.Gamma ((1 - s) / 2) *
        ((Real.pi : ℂ) ^ (s / 2) * (Complex.Gamma (s / 2))⁻¹)
      = ((Real.pi : ℂ) ^ (-(1 - s) / 2) * (Real.pi : ℂ) ^ (s / 2)) *
          Complex.Gamma ((1 - s) / 2) * (Complex.Gamma (s / 2))⁻¹ := by ring
    _ = (Real.pi : ℂ) ^ (s - 1 / 2) * Complex.Gamma ((1 - s) / 2) *
          (Complex.Gamma (s / 2))⁻¹ := by rw [hsplit]

/-! ## The zero set -/

/-- `Γ_ℝ` vanishes exactly on the even nonpositive lattice. -/
theorem Gammaℝ_eq_zero_iff (s : ℂ) :
    Complex.Gammaℝ s = 0 ↔ ∃ n : ℕ, s = -(2 * n : ℕ) := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [Complex.Gammaℝ_def, mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact absurd h (Complex.cpow_ne_zero_iff.mpr (Or.inl hpi))
    · obtain ⟨m, hm⟩ := (Complex.Gamma_eq_zero_iff _).1 h
      refine ⟨m, ?_⟩
      have : s = 2 * (-(m : ℂ)) := by
        field_simp at hm
        linear_combination hm
      push_cast
      rw [this]
      ring
  · intro ⟨n, hn⟩
    refine Or.inr ((Complex.Gamma_eq_zero_iff _).2 ⟨n, ?_⟩)
    rw [hn]
    push_cast
    ring

/-- **The zero set of the multiplier** is `{0, -2, -4, …}`. -/
theorem gammaGaussianEnvelope_eq_zero_iff (s : ℂ) :
    gammaGaussianEnvelope s = 0 ↔ ∃ n : ℕ, s = -(2 * n : ℕ) := by
  rw [gammaGaussianEnvelope, mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact absurd h (Complex.exp_ne_zero _)
    · exact (Gammaℝ_eq_zero_iff s).1 (inv_eq_zero.mp h)
  · intro h
    exact Or.inr (inv_eq_zero.mpr ((Gammaℝ_eq_zero_iff s).2 h))

/-- **The multiplier is a holomorphic unit on the right half-plane**, in particular throughout the
critical strip. -/
theorem gammaGaussianEnvelope_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    gammaGaussianEnvelope s ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := (gammaGaussianEnvelope_eq_zero_iff s).1 h
  rw [hn] at hs
  simp only [Complex.neg_re, Complex.natCast_re] at hs
  have : (0:ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
  linarith

/-- The reflected argument stays off the pole lattice on the left of the line `Re s = 1`. -/
theorem Gammaℝ_one_sub_ne_zero_of_re_lt_one {s : ℂ} (hs : s.re < 1) :
    Complex.Gammaℝ (1 - s) ≠ 0 := by
  refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-! ## The reflection identity -/

/-- **The exact Fourier-reflection identity.**  The Gaussian is invariant under `s ↦ 1-s` and the
archimedean factors cancel. -/
theorem evenChiFactor_mul_envelope_one_sub {s : ℂ} (hs : Complex.Gammaℝ (1 - s) ≠ 0) :
    evenChiFactor s * gammaGaussianEnvelope (1 - s) = gammaGaussianEnvelope s := by
  have hsq : (1 - s - 1 / 2) ^ 2 = (s - 1 / 2) ^ 2 := by ring
  rw [evenChiFactor, gammaGaussianEnvelope, gammaGaussianEnvelope, hsq]
  calc Complex.Gammaℝ (1 - s) * (Complex.Gammaℝ s)⁻¹ *
        (Complex.exp ((s - 1 / 2) ^ 2) * (Complex.Gammaℝ (1 - s))⁻¹)
      = (Complex.Gammaℝ (1 - s) * (Complex.Gammaℝ (1 - s))⁻¹) *
          (Complex.exp ((s - 1 / 2) ^ 2) * (Complex.Gammaℝ s)⁻¹) := by ring
    _ = Complex.exp ((s - 1 / 2) ^ 2) * (Complex.Gammaℝ s)⁻¹ := by
        rw [mul_inv_cancel₀ hs, one_mul]

/-- The reflection identity holds throughout the critical strip and its left half-plane. -/
theorem evenChiFactor_mul_envelope_one_sub_of_re_lt_one {s : ℂ} (hs : s.re < 1) :
    evenChiFactor s * gammaGaussianEnvelope (1 - s) = gammaGaussianEnvelope s :=
  evenChiFactor_mul_envelope_one_sub (Gammaℝ_one_sub_ne_zero_of_re_lt_one hs)

/-- **The archimedean seam.**  Completing the enveloped datum cancels the multiplier and leaves the
bare centered Gaussian. -/
theorem Gammaℝ_mul_gammaGaussianEnvelope {s : ℂ} (hs : Complex.Gammaℝ s ≠ 0) :
    Complex.Gammaℝ s * gammaGaussianEnvelope s = Complex.exp ((s - 1 / 2) ^ 2) := by
  rw [gammaGaussianEnvelope]
  calc Complex.Gammaℝ s * (Complex.exp ((s - 1 / 2) ^ 2) * (Complex.Gammaℝ s)⁻¹)
      = (Complex.Gammaℝ s * (Complex.Gammaℝ s)⁻¹) * Complex.exp ((s - 1 / 2) ^ 2) := by ring
    _ = Complex.exp ((s - 1 / 2) ^ 2) := by rw [mul_inv_cancel₀ hs, one_mul]

/-- The completion of an enveloped datum is the Gaussian times the original datum. -/
theorem Gammaℝ_mul_envelope_mul {s : ℂ} (hs : Complex.Gammaℝ s ≠ 0) (F : ℂ → ℂ) :
    Complex.Gammaℝ s * (gammaGaussianEnvelope s * F s)
      = Complex.exp ((s - 1 / 2) ^ 2) * F s := by
  rw [← mul_assoc, Gammaℝ_mul_gammaGaussianEnvelope hs]

/-! ## Entirety -/

/-- The reciprocal archimedean factor is entire. -/
theorem differentiable_inv_Gammaℝ : Differentiable ℂ (fun s : ℂ => (Complex.Gammaℝ s)⁻¹) := by
  have hpi : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hrw : (fun s : ℂ => (Complex.Gammaℝ s)⁻¹)
      = fun s : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (s / 2)) *
          (Complex.Gamma (s / 2))⁻¹ := by
    funext s
    rw [inv_Gammaℝ_eq, Complex.cpow_def_of_ne_zero hpi]
  rw [hrw]
  refine Differentiable.mul ?_ ?_
  · exact (Complex.differentiable_exp.comp (by fun_prop))
  · exact Complex.differentiable_one_div_Gamma.comp (by fun_prop)

/-- **The multiplier is entire.** -/
theorem differentiable_gammaGaussianEnvelope : Differentiable ℂ gammaGaussianEnvelope := by
  refine Differentiable.mul ?_ differentiable_inv_Gammaℝ
  exact Complex.differentiable_exp.comp (by fun_prop)

/-- The multiplier is analytic at every point. -/
theorem analyticAt_gammaGaussianEnvelope (s : ℂ) : AnalyticAt ℂ gammaGaussianEnvelope s :=
  differentiable_gammaGaussianEnvelope.analyticAt s

end

end GaloisForLFunctions
