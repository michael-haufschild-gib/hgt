import GaloisForLFunctions.RHTower.BurnolCartierHeadEnergyStokesFlux

/-!
# The two-orientation first-wall residue and its polarization

The zero-divided Burnol source has forward aperture head `a_ρ = (1-ρ)⁻¹` and cosine-oriented head
`b_ρ = -(log 2)/ρ`.  Its exterior mass beyond the fixed aperture is `B_ρ = (b_ρ - a_ρ)/2`, and the
singular first-wall crossing residues of the two Fourier orientations are

`r_ρ = -a_ρ conj B_ρ`,   `r_ρ^∨ = b_ρ conj B_ρ`.

Their sum is a nonnegative quadrature `|a_ρ - b_ρ|²/2`, and twice the real part of their oriented
difference is exactly the fixed physical Route-R current `|a_ρ|² - |b_ρ|²`.  The exterior mass
cannot vanish anywhere in the critical strip: `B_ρ = 0` forces the negative real value
`ρ = -log 2/(1 - log 2)`.
-/

open Complex Real
open scoped ComplexConjugate

noncomputable section

namespace RHTower

/-- Forward aperture head of the zero-divided source. -/
def burnolFirstWallHead (rho : ℂ) : ℂ := ((1 : ℂ) - rho)⁻¹

/-- Cosine-oriented aperture head of the zero-divided source. -/
def burnolFirstWallCosineHead (rho : ℂ) : ℂ := -(Real.log 2 : ℂ) / rho

/-- Exterior mass beyond the fixed aperture, `B_ρ = (b_ρ - a_ρ)/2`. -/
def burnolFirstWallExteriorMass (rho : ℂ) : ℂ :=
  (burnolFirstWallCosineHead rho - burnolFirstWallHead rho) / 2

/-- Singular first-wall crossing residue of the forward orientation. -/
def burnolFirstWallResidue (rho : ℂ) : ℂ :=
  -burnolFirstWallHead rho * conj (burnolFirstWallExteriorMass rho)

/-- Singular first-wall crossing residue of the reflected orientation. -/
def burnolFirstWallCosineResidue (rho : ℂ) : ℂ :=
  burnolFirstWallCosineHead rho * conj (burnolFirstWallExteriorMass rho)

/-! ## The two exact quadrature laws -/

/-- **Positive polarization.**  The residue sum is a nonnegative quadrature of the head gap. -/
theorem burnolFirstWallResidue_add_cosineResidue (rho : ℂ) :
    burnolFirstWallResidue rho + burnolFirstWallCosineResidue rho =
      ((‖burnolFirstWallHead rho - burnolFirstWallCosineHead rho‖ ^ 2 / 2 : ℝ) : ℂ) := by
  set a : ℂ := burnolFirstWallHead rho with ha
  set b : ℂ := burnolFirstWallCosineHead rho with hb
  have hB : burnolFirstWallExteriorMass rho = (b - a) / 2 := rfl
  rw [burnolFirstWallResidue, burnolFirstWallCosineResidue, hB, ← ha, ← hb]
  have h1 : -a * conj ((b - a) / 2) + b * conj ((b - a) / 2) =
      (b - a) * conj (b - a) / 2 := by
    rw [map_div₀, Complex.conj_ofNat]
    ring
  rw [h1, Complex.mul_conj', norm_sub_rev b a]
  push_cast
  ring

/-- The residue sum is a nonnegative real number. -/
theorem burnolFirstWallResidue_add_cosineResidue_re_nonneg (rho : ℂ) :
    0 ≤ (burnolFirstWallResidue rho + burnolFirstWallCosineResidue rho).re := by
  rw [burnolFirstWallResidue_add_cosineResidue, Complex.ofReal_re]
  positivity

/-- Halving commutes with the real part. -/
theorem two_mul_div_two_re (w : ℂ) : 2 * (w / 2).re = w.re := by
  have hsum : (w / 2 + w / 2 : ℂ) = w := by ring
  have h2 := congrArg Complex.re hsum
  rw [Complex.add_re] at h2
  linarith

/-- **Exact landing on the fixed physical Route-R current.** -/
theorem burnolFirstWallResidue_sub_cosineResidue_re (rho : ℂ) :
    2 * (burnolFirstWallResidue rho - burnolFirstWallCosineResidue rho).re =
      ‖burnolFirstWallHead rho‖ ^ 2 - ‖burnolFirstWallCosineHead rho‖ ^ 2 := by
  set a : ℂ := burnolFirstWallHead rho with ha
  set b : ℂ := burnolFirstWallCosineHead rho with hb
  have hB : burnolFirstWallExteriorMass rho = (b - a) / 2 := rfl
  have hexp : burnolFirstWallResidue rho - burnolFirstWallCosineResidue rho =
      (a + b) * conj (a - b) / 2 := by
    rw [burnolFirstWallResidue, burnolFirstWallCosineResidue, hB, ← ha, ← hb, map_div₀,
      Complex.conj_ofNat, map_sub, map_sub]
    ring
  have key : ((a + b) * conj (a - b)).re = ‖a‖ ^ 2 - ‖b‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
    ring
  rw [hexp, two_mul_div_two_re, key]

/-- The oriented residue difference is exactly the explicit divided-shift head current. -/
theorem burnolFirstWallResidue_sub_cosineResidue_re_eq_headFlux (rho : ℂ) :
    2 * (burnolFirstWallResidue rho - burnolFirstWallCosineResidue rho).re =
      burnolCartierDividedShiftHeadFlux rho := by
  rw [burnolFirstWallResidue_sub_cosineResidue_re, burnolCartierDividedShiftHeadFlux,
    burnolFirstWallHead, burnolFirstWallCosineHead, norm_div, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.log_pos one_lt_two), div_pow, norm_inv]
  rw [norm_inv]
  ring

/-! ## Nonvanishing of the exterior mass -/

/-- **The exterior mass vanishes only at a negative real point.** -/
theorem burnolFirstWallExteriorMass_eq_zero_iff {rho : ℂ} (h0 : rho ≠ 0) (h1 : rho ≠ 1) :
    burnolFirstWallExteriorMass rho = 0 ↔
      rho = -(Real.log 2 : ℂ) / ((1 : ℂ) - (Real.log 2 : ℂ)) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hloglt : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have hden : (1 : ℂ) - (Real.log 2 : ℂ) ≠ 0 := by
    intro hc
    have : ((1 : ℝ) : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination hc
    have := Complex.ofReal_inj.mp this
    linarith
  have hsub : (1 : ℂ) - rho ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hlogC : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hlog)
  constructor
  · intro h
    rw [burnolFirstWallExteriorMass, div_eq_zero_iff] at h
    have heq : burnolFirstWallCosineHead rho = burnolFirstWallHead rho := by
      rcases h with h | h
      · exact sub_eq_zero.mp h
      · norm_num at h
    rw [burnolFirstWallCosineHead, burnolFirstWallHead, div_eq_iff h0, inv_mul_eq_div,
      eq_div_iff hsub] at heq
    field_simp
    linear_combination -heq
  · intro h
    rw [burnolFirstWallExteriorMass, burnolFirstWallCosineHead, burnolFirstWallHead, h]
    field_simp
    ring

/-- **In the open right half-strip the exterior mass is nonzero.** -/
theorem burnolFirstWallExteriorMass_ne_zero {rho : ℂ} (hlo : 1 / 2 < rho.re) (hhi : rho.re < 1) :
    burnolFirstWallExteriorMass rho ≠ 0 := by
  have h0 : rho ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hlo; linarith
  have h1 : rho ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hhi; linarith
  intro hz
  rw [burnolFirstWallExteriorMass_eq_zero_iff h0 h1] at hz
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hloglt : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have hre : rho.re = -Real.log 2 / (1 - Real.log 2) := by
    rw [hz]
    rw [show -(Real.log 2 : ℂ) / ((1 : ℂ) - (Real.log 2 : ℂ)) =
        ((-Real.log 2 / (1 - Real.log 2) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hre] at hlo
  have hneg : -Real.log 2 / (1 - Real.log 2) < 0 := by
    apply div_neg_of_neg_of_pos <;> linarith
  linarith

/-! ## Landing on the actual zero-divided source heads -/

/-- The forward residue head is the intrinsic forward aperture head of the divided shift. -/
theorem xiDivisor_burnolFirstWallHead_eq
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninForwardHeadCoefficient (1 / 2)
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) =
      burnolFirstWallHead (rho : ℂ) :=
  xiDivisor_burnolSoninForwardHeadCoefficient_mellinDividedShift rho h

/-- The reflected residue head is the intrinsic cosine aperture head of the divided shift. -/
theorem xiDivisor_burnolFirstWallCosineHead_eq
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolSoninCosineHeadCoefficient (1 / 2)
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) =
      burnolFirstWallCosineHead (rho : ℂ) :=
  xiDivisor_burnolSoninCosineHeadCoefficient_mellinDividedShift rho h

/-- **The oriented residue difference is the intrinsic two-head current of the actual
zero-divided source.** -/
theorem xiDivisor_burnolFirstWallResidue_landing
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    2 * (burnolFirstWallResidue (rho : ℂ) - burnolFirstWallCosineResidue (rho : ℂ)).re =
      burnolSoninOrientedGammaHeadFlux (1 / 2)
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom) := by
  rw [burnolFirstWallResidue_sub_cosineResidue_re_eq_headFlux,
    xiDivisor_burnolSoninOrientedGammaHeadFlux_mellinDividedShift rho h]

end RHTower
