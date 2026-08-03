import GaloisForLFunctions.HTGeometry.GammaGaussianEnvelope

/-!
# The translated multiplier and exact decimation neutrality

In the pole coordinate `u = ρ + 1/2` the Riemann reflection `ρ ↦ 1 - ρ` becomes `u ↦ 2 - u`, with
center `u = 1`.  Translating the multiplier and the reflection factor by `1/2`,

```text
A_BV(u) = A(u - 1/2) = exp((u-1)^2) π^((u-1/2)/2) / Γ((u-1/2)/2),
χ_BV(u) = χ(u - 1/2) = π^(u-1) Γ((3/2-u)/2) / Γ((u-1/2)/2),
```

the reflection identity becomes `χ_BV(u) A_BV(2-u) = A_BV(u)`, and the zero set is the translate
`{1/2, -3/2, -7/2, …}`, so `A_BV` is a holomorphic unit on the shifted strip `1/2 < Re u < 3/2`.

A geometric Laurent family `R_j = 2 m r^{j(ρ - 1/2)} M` has decimation ratio `R_{j+2}/R_j =
r^{2ρ-1}`, and multiplying every coefficient by one nonzero scalar leaves that ratio unchanged.  So
the translated multiplier is exactly neutral under decimation: it cannot change, damp or orient the
radial Lyapunov exponent `log‖r^{2ρ-1}‖ = (2 Re ρ - 1) log r`.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-! ## The translated factors -/

/-- The reflection factor in the shifted pole coordinate. -/
def bvChiFactor (u : ℂ) : ℂ := evenChiFactor (u - 1 / 2)

/-- The multiplier in the shifted pole coordinate. -/
def bvGammaGaussianEnvelope (u : ℂ) : ℂ := gammaGaussianEnvelope (u - 1 / 2)

/-- The translated multiplier in explicit coordinates: the Gaussian is centered at `u = 1`. -/
theorem bvGammaGaussianEnvelope_eq (u : ℂ) :
    bvGammaGaussianEnvelope u
      = Complex.exp ((u - 1) ^ 2) * (Real.pi : ℂ) ^ ((u - 1 / 2) / 2) *
          (Complex.Gamma ((u - 1 / 2) / 2))⁻¹ := by
  rw [bvGammaGaussianEnvelope, gammaGaussianEnvelope_eq]
  congr 2
  ring

/-- The translated reflection factor in explicit coordinates. -/
theorem bvChiFactor_eq (u : ℂ) :
    bvChiFactor u
      = (Real.pi : ℂ) ^ (u - 1) * Complex.Gamma ((3 / 2 - u) / 2) *
          (Complex.Gamma ((u - 1 / 2) / 2))⁻¹ := by
  rw [bvChiFactor, evenChiFactor_eq]
  have h1 : u - 1 / 2 - 1 / 2 = u - 1 := by ring
  have h2 : (1 - (u - 1 / 2)) / 2 = (3 / 2 - u) / 2 := by ring
  rw [h1, h2]

/-! ## The shifted reflection identity -/

/-- **The translated reflection identity** `χ_BV(u) A_BV(2-u) = A_BV(u)`. -/
theorem bvChiFactor_mul_bvEnvelope_two_sub {u : ℂ} (hu : u.re < 3 / 2) :
    bvChiFactor u * bvGammaGaussianEnvelope (2 - u) = bvGammaGaussianEnvelope u := by
  have hshift : (2 - u) - 1 / 2 = 1 - (u - 1 / 2) := by ring
  have hre : (u - 1 / 2).re < 1 := by
    simp only [Complex.sub_re]
    norm_num
    linarith
  rw [bvChiFactor, bvGammaGaussianEnvelope, bvGammaGaussianEnvelope, hshift]
  exact evenChiFactor_mul_envelope_one_sub_of_re_lt_one hre

/-! ## The shifted zero set -/

/-- **The zero set of the translated multiplier** is `{1/2, -3/2, -7/2, …}`. -/
theorem bvGammaGaussianEnvelope_eq_zero_iff (u : ℂ) :
    bvGammaGaussianEnvelope u = 0 ↔ ∃ n : ℕ, u = 1 / 2 - (2 * n : ℕ) := by
  rw [bvGammaGaussianEnvelope, gammaGaussianEnvelope_eq_zero_iff]
  constructor
  · intro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have : u = 1 / 2 + -((2 * n : ℕ) : ℂ) := by
      linear_combination hn
    rw [this]
    ring
  · intro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn]
    ring

/-- **The translated multiplier is a holomorphic unit on the shifted strip.** -/
theorem bvGammaGaussianEnvelope_ne_zero_of_half_lt_re {u : ℂ} (hu : 1 / 2 < u.re) :
    bvGammaGaussianEnvelope u ≠ 0 := by
  refine gammaGaussianEnvelope_ne_zero_of_re_pos ?_
  simp only [Complex.sub_re]
  norm_num
  linarith

/-! ## The geometric Laurent family and its decimation ratio -/

/-- The proved shape of the BV Laurent coefficients at a pole: a geometric family in the decimation
index with ratio determined by the radial character. -/
def bvLaurentCoeff (r : ℝ) (ρ m M : ℂ) (j : ℕ) : ℂ :=
  2 * m * (r : ℂ) ^ ((j : ℂ) * (ρ - 1 / 2)) * M

/-- No coefficient of the family vanishes when the amplitude and the boundary datum do not. -/
theorem bvLaurentCoeff_ne_zero {r : ℝ} (hr : 0 < r) {ρ m M : ℂ} (hm : m ≠ 0) (hM : M ≠ 0)
    (j : ℕ) : bvLaurentCoeff r ρ m M j ≠ 0 := by
  have hrne : ((r : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hcpow : ((r : ℂ)) ^ ((j : ℂ) * (ρ - 1 / 2)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hrne)
  rw [bvLaurentCoeff]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hm) hcpow) hM

/-- **The decimation ratio is the radial character** `r^{2ρ-1}`. -/
theorem bvLaurentCoeff_ratio {r : ℝ} (hr : 0 < r) {ρ m M : ℂ} (hm : m ≠ 0) (hM : M ≠ 0) (j : ℕ) :
    bvLaurentCoeff r ρ m M (j + 2) / bvLaurentCoeff r ρ m M j = (r : ℂ) ^ (2 * ρ - 1) := by
  have hrne : ((r : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hsplit : ((j : ℂ) + 2) * (ρ - 1 / 2)
      = (j : ℂ) * (ρ - 1 / 2) + (2 * ρ - 1) := by ring
  have hcast : (((j + 2 : ℕ) : ℂ)) = (j : ℂ) + 2 := by push_cast; ring
  have hnum : bvLaurentCoeff r ρ m M (j + 2)
      = bvLaurentCoeff r ρ m M j * (r : ℂ) ^ (2 * ρ - 1) := by
    rw [bvLaurentCoeff, bvLaurentCoeff, hcast, hsplit, Complex.cpow_add _ _ hrne]
    ring
  rw [hnum, mul_comm, mul_div_assoc, div_self (bvLaurentCoeff_ne_zero hr hm hM j), mul_one]

/-- Multiplying every coefficient by one nonzero scalar leaves the decimation ratio unchanged. -/
theorem ratio_eq_of_common_scalar {c x y : ℂ} (hc : c ≠ 0) (hy : y ≠ 0) :
    c * x / (c * y) = x / y := by
  rw [mul_div_mul_left _ _ hc]

/-- **Exact decimation neutrality.**  Multiplying the Laurent family by the value of the translated
multiplier at the pole — one nonzero scalar, independent of the decimation index — leaves the radial
character `r^{2ρ-1}` unchanged. -/
theorem bvEnvelope_decimation_neutral {r : ℝ} (hr : 0 < r) {ρ m M : ℂ} (hm : m ≠ 0) (hM : M ≠ 0)
    (hρ : 0 < ρ.re) (j : ℕ) :
    bvGammaGaussianEnvelope (ρ + 1 / 2) * bvLaurentCoeff r ρ m M (j + 2) /
        (bvGammaGaussianEnvelope (ρ + 1 / 2) * bvLaurentCoeff r ρ m M j)
      = (r : ℂ) ^ (2 * ρ - 1) := by
  have hAne : bvGammaGaussianEnvelope (ρ + 1 / 2) ≠ 0 := by
    refine bvGammaGaussianEnvelope_ne_zero_of_half_lt_re ?_
    simp only [Complex.add_re]
    norm_num
    linarith
  rw [ratio_eq_of_common_scalar hAne (bvLaurentCoeff_ne_zero hr hm hM j)]
  exact bvLaurentCoeff_ratio hr hm hM j

/-- **The radial Lyapunov exponent.**  Its sign is exactly the off-line displacement of the pole,
and nothing in the envelope can change it. -/
theorem log_norm_radial_character {r : ℝ} (hr : 0 < r) (ρ : ℂ) :
    Real.log ‖(r : ℂ) ^ (2 * ρ - 1)‖ = (2 * ρ.re - 1) * Real.log r := by
  rw [norm_cpow_eq_rpow_re_of_pos hr, Real.log_rpow hr]
  congr 1
  simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.one_re]
  ring

/-- The radial character has modulus one exactly on the critical line. -/
theorem norm_radial_character_eq_one_iff {r : ℝ} (hr : 1 < r) (ρ : ℂ) :
    ‖(r : ℂ) ^ (2 * ρ - 1)‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hlogpos : 0 < Real.log r := Real.log_pos hr
  have hpos : 0 < ‖(r : ℂ) ^ (2 * ρ - 1)‖ := by
    rw [norm_cpow_eq_rpow_re_of_pos hr0]
    exact Real.rpow_pos_of_pos hr0 _
  constructor
  · intro h
    have hlog : Real.log ‖(r : ℂ) ^ (2 * ρ - 1)‖ = 0 := by rw [h, Real.log_one]
    rw [log_norm_radial_character hr0] at hlog
    rcases mul_eq_zero.mp hlog with h1 | h2
    · linarith
    · exact absurd h2 (ne_of_gt hlogpos)
  · intro h
    have hlog : Real.log ‖(r : ℂ) ^ (2 * ρ - 1)‖ = 0 := by
      rw [log_norm_radial_character hr0, h]
      ring
    have := Real.exp_log hpos
    rw [hlog, Real.exp_zero] at this
    exact this.symm

end

end GaloisForLFunctions
