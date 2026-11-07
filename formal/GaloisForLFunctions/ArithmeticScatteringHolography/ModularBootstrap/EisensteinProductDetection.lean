import GaloisForLFunctions.BlackHoleRingdown.TheModesOfTheRingdown
import Mathlib.Analysis.Meromorphic.Order

/-!
# Detection of arithmetic poles by products of Eisenstein numerators

Write `N(u,z) = ξ(1+2u) E(1/2+u,z)`. The quotient
`N(u,z) N(u,w) / ξ(1+2u)` retains every arithmetic pole, with its full
multiplicity, for some points on any two prescribed horocycles.
Its iterated horocycle average also retains every pole: its numerator is
the product of the two explicit constant terms, both nonzero at a resonance.

These are statements about the actual Eisenstein function. Identifying this
product with a torus partition-function overlap is a separate assertion.
-/

open Complex MeasureTheory Set Filter Topology
open RHTower GaloisForLFunctions.BlackHoleRingdown

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual arithmetic resonances, in the coordinate `ρ = 1 + 2u`. -/
abbrev Resonance := {u : ℂ // xi (1 + 2 * u) = 0}

/-- Positive heights of closed horocycles. -/
abbrev Height := Ioi (0 : ℝ)

/-- The constant term of the pole-cleared Eisenstein function. -/
def numeratorMean (u : ℂ) (Y : Height) : ℂ :=
  (Y.val : ℂ) ^ (1 / 2 + u) * xi (1 + 2 * u) +
    (1 + 2 * u) / (2 * u - 1) * xi (2 * u) * (Y.val : ℂ) ^ (1 / 2 - u)

/-- The product quotient before the elementary scalar normalization. -/
def productQuotient (Y Z : Height) (x w : ℝ) (u : ℂ) : ℂ :=
  eisensteinNumerator u x Y.val * eisensteinNumerator u w Z.val / xi (1 + 2 * u)

/-- The quotient after averaging over both horocycle coordinates. -/
def meanQuotient (Y Z : Height) (u : ℂ) : ℂ :=
  numeratorMean u Y * numeratorMean u Z / xi (1 + 2 * u)

/-- The averaged numerator has one term divisible by `D²`, two by `D`,
and a reflected term that survives on the zero divisor of `D`. -/
theorem meanNumerator_decomposition (Y Z : Height) (u : ℂ) :
    let D := xi (1 + 2 * u)
    let A := (1 + 2 * u) / (2 * u - 1) * xi (2 * u)
    numeratorMean u Y * numeratorMean u Z =
      D ^ 2 * (Y.val : ℂ) ^ (1 / 2 + u) * (Z.val : ℂ) ^ (1 / 2 + u) +
      D * A * ((Y.val : ℂ) ^ (1 / 2 + u) * (Z.val : ℂ) ^ (1 / 2 - u) +
        (Y.val : ℂ) ^ (1 / 2 - u) * (Z.val : ℂ) ^ (1 / 2 + u)) +
      A ^ 2 * (Y.val : ℂ) ^ (1 / 2 - u) * (Z.val : ℂ) ^ (1 / 2 - u) := by
  dsimp only [numeratorMean]
  ring

theorem integral_numerator (u : ℂ) (Y : Height) :
    (∫ x in Ioc (0 : ℝ) 1, eisensteinNumerator u x Y.val) = numeratorMean u Y :=
  setIntegral_eisensteinNumerator u Y.property

/-- Averaging both target coordinates gives an explicit scalar quotient. -/
theorem integral_productQuotient (Y Z : Height) (u : ℂ) :
    (∫ x in Ioc (0 : ℝ) 1, ∫ w in Ioc (0 : ℝ) 1,
      productQuotient Y Z x w u) = meanQuotient Y Z u := by
  simp only [productQuotient, integral_div, integral_const_mul, integral_mul_const,
    integral_numerator, meanQuotient]

/-- At a resonance only the reflected constant term survives. -/
theorem numeratorMean_at_resonance (p : Resonance) (Y : Height) :
    numeratorMean p.val Y =
      (1 + 2 * p.val) / (2 * p.val - 1) * xi (2 * p.val) *
        (Y.val : ℂ) ^ (1 / 2 - p.val) := by
  simp only [numeratorMean, p.property, mul_zero, zero_add]

/-- The reflected constant term cannot vanish at any arithmetic resonance. -/
theorem numeratorMean_ne_zero (p : Resonance) (Y : Height) :
    numeratorMean p.val Y ≠ 0 := by
  have hr := re_neg_of_xi_shift_eq_zero p.property
  have hl := re_gt_of_xi_shift_eq_zero p.property
  have h₁ : (1 : ℂ) + 2 * p.val ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, Complex.zero_re] at hh
    linarith
  have h₂ : (2 : ℂ) * p.val - 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.one_re,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, Complex.zero_re] at hh
    linarith
  have hY : (Y.val : ℂ) ≠ 0 := by exact_mod_cast Y.property.ne'
  rw [numeratorMean_at_resonance]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero h₁ h₂) (xi_two_mul_ne_zero p.property))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hY))

private theorem analyticAt_numeratorMean (p : Resonance) (Y : Height) :
    AnalyticAt ℂ (fun u => numeratorMean u Y) p.val := by
  have hN := analyticAt_eisensteinNumerator 0 Y.property
    (re_neg_of_xi_shift_eq_zero p.property).le
  have hd : Differentiable ℂ (fun u => eisTail u 0 Y.val) :=
    fun u => differentiableAt_eisTail 0 Y.property u
  have hT : AnalyticAt ℂ (fun u => eisTail u 0 Y.val) p.val := hd.analyticAt p.val
  have hP : AnalyticAt ℂ (fun u : ℂ => (1 + 2 * u) * (2 * u)) p.val := by
    fun_prop
  convert hN.sub (hP.mul hT) using 1
  funext u
  simp only [Pi.sub_apply, Pi.mul_apply, eisensteinNumerator, numeratorMean,
    add_sub_cancel_right]

private theorem quotient_order {F : ℂ → ℂ} (p : Resonance)
    (hF : AnalyticAt ℂ F p.val) (hF₀ : F p.val ≠ 0) :
    meromorphicOrderAt (fun u => F u / xi (1 + 2 * u)) p.val =
      -meromorphicOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val := by
  have hD := differentiable_xi_shift.analyticAt p.val
  change meromorphicOrderAt (F / (fun u : ℂ => xi (1 + 2 * u))) p.val = _
  rw [meromorphicOrderAt_div hF.meromorphicAt hD.meromorphicAt,
    hF.meromorphicOrderAt_eq, hF.analyticOrderAt_eq_zero.mpr hF₀]
  simp

/-- Both moduli can be chosen on any prescribed horocycles without cancelling
any part of the pole. No simplicity assumption is needed. -/
theorem exists_product_full_order (p : Resonance) (Y Z : Height) :
    ∃ x ∈ Ioc (0 : ℝ) 1, ∃ w ∈ Ioc (0 : ℝ) 1,
      meromorphicOrderAt (productQuotient Y Z x w) p.val =
        -meromorphicOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val := by
  obtain ⟨x, hx, hNx⟩ := exists_eisensteinNumerator_ne_zero p.property Y.property
  obtain ⟨w, hw, hNw⟩ := exists_eisensteinNumerator_ne_zero p.property Z.property
  refine ⟨x, hx, w, hw, ?_⟩
  exact quotient_order p
    ((analyticAt_eisensteinNumerator x Y.property
      (re_neg_of_xi_shift_eq_zero p.property).le).mul
      (analyticAt_eisensteinNumerator w Z.property
        (re_neg_of_xi_shift_eq_zero p.property).le)) (mul_ne_zero hNx hNw)

/-- The explicit average preserves the full pole order at every resonance. -/
theorem meanQuotient_full_order (p : Resonance) (Y Z : Height) :
    meromorphicOrderAt (meanQuotient Y Z) p.val =
      -meromorphicOrderAt (fun u : ℂ => xi (1 + 2 * u)) p.val :=
  quotient_order p ((analyticAt_numeratorMean p Y).mul (analyticAt_numeratorMean p Z))
    (mul_ne_zero (numeratorMean_ne_zero p Y) (numeratorMean_ne_zero p Z))

/-- The order is a strictly negative integer, not an indeterminate order. -/
theorem meanQuotient_pole (p : Resonance) (Y Z : Height) :
    ∃ n : ℕ, meromorphicOrderAt (meanQuotient Y Z) p.val = -((n + 1 : ℕ) : ℤ) := by
  obtain ⟨n, g, hn, _⟩ := exists_xi_shift_factor p.property
  refine ⟨n, ?_⟩
  rw [meanQuotient_full_order, (differentiable_xi_shift.analyticAt p.val).meromorphicOrderAt_eq,
    hn]
  simp only [ENat.map_coe]

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.integral_productQuotient
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.exists_product_full_order
#print axioms GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.meanQuotient_pole
