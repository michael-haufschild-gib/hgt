import GaloisForLFunctions.RHTower.HeatEnergyAsymptotic

/-!
# The coefficients of the heat-aperture expansion

The two side coefficients of the Jonquière expansion combine into the card's `(8)` and `(9)`:
their average is `Γ(1-s) sin(πs/2)` and the average of their squared moduli is
`|Γ(1-s)|² cosh(π t)`.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- **The averaged leading coefficient.**  This is the `(A₊+A₋)/2 = Γ(1-s) sin(πs/2)` of `(9)`. -/
theorem jonquiereLead_avg (s : ℂ) :
    (jonquiereLead s + jonquiereLeadNeg s) / 2
      = Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2) := by
  have hcos : Complex.cos (↑Real.pi * (1 - s) / 2)
      = (Complex.exp (↑Real.pi * I * (1 - s) / 2)
          + Complex.exp (-↑Real.pi * I * (1 - s) / 2)) / 2 := by
    rw [Complex.cos]
    ring_nf
  have hshift : Complex.cos (↑Real.pi * (1 - s) / 2) = Complex.sin (↑Real.pi * s / 2) := by
    rw [show (↑Real.pi * (1 - s) / 2 : ℂ) = ↑Real.pi / 2 - ↑Real.pi * s / 2 by ring]
    exact Complex.cos_pi_div_two_sub _
  rw [jonquiereLead, jonquiereLeadNeg, ← hshift, hcos]
  ring

/-- **The averaged squared modulus.**  This is the `(|A₊|²+|A₋|²)/2 = |Γ(1-s)|² cosh(π t)` of
`(8)`. -/
theorem normSq_jonquiereLead_avg (s : ℂ) :
    (‖jonquiereLead s‖ ^ 2 + ‖jonquiereLeadNeg s‖ ^ 2) / 2
      = ‖Complex.Gamma (1 - s)‖ ^ 2 * Real.cosh (Real.pi * s.im) := by
  have hre1 : (↑Real.pi * I * (1 - s) / 2).re = Real.pi * s.im / 2 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have hre2 : (-↑Real.pi * I * (1 - s) / 2).re = -(Real.pi * s.im / 2) := by
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
    ring
  have h1 : ‖jonquiereLead s‖ ^ 2
      = ‖Complex.Gamma (1 - s)‖ ^ 2 * Real.exp (Real.pi * s.im) := by
    rw [jonquiereLead, norm_mul, Complex.norm_exp, hre1, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have h2 : ‖jonquiereLeadNeg s‖ ^ 2
      = ‖Complex.Gamma (1 - s)‖ ^ 2 * Real.exp (-(Real.pi * s.im)) := by
    rw [jonquiereLeadNeg, norm_mul, Complex.norm_exp, hre2, mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [h1, h2, Real.cosh_eq]
  ring

/-- The main term splits into a constant and the aperture power. -/
theorem heatMomentTerm_split {x : ℝ} (hx : 0 < x) (lam : ℂ) :
    heatMomentTerm x lam
      = ((((4 * Real.pi : ℝ)) : ℂ) ^ (lam / 2) * Complex.Gamma ((lam + 1) / 2)
          / ((Real.sqrt Real.pi : ℝ) : ℂ)) * ((x : ℝ) : ℂ) ^ (lam / 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [heatMomentTerm]
  have hmul : (((4 * Real.pi * x : ℝ)) : ℂ) ^ (lam / 2)
      = ((((4 * Real.pi : ℝ)) : ℂ)) ^ (lam / 2) * (((x : ℝ)) : ℂ) ^ (lam / 2) := by
    rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) hx.le, ← Complex.ofReal_mul]
  rw [hmul]
  ring

/-- The card's `L(s)` of `(8)`. -/
noncomputable def heatEchoL (s : ℂ) : ℝ :=
  ‖Complex.Gamma (1 - s)‖ ^ 2 * Real.cosh (Real.pi * s.im)
    * ((4 * Real.pi) ^ (s.re - 1) * Real.Gamma (s.re - 1 / 2) / Real.sqrt Real.pi)

/-- The card's `C(s)` of `(9)`. -/
noncomputable def heatEchoC (s : ℂ) : ℂ :=
  Complex.Gamma (1 - s) * Complex.sin (↑Real.pi * s / 2)
    * ((((4 * Real.pi : ℝ)) : ℂ) ^ ((s - 1) / 2) * Complex.Gamma ((s - 1 + 1) / 2)
        / ((Real.sqrt Real.pi : ℝ) : ℂ))

theorem gamma_one_sub_ne_zero {s : ℂ} (_h0 : 0 < s.re) (h1 : s.re < 1) :
    Complex.Gamma (1 - s) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m => ?_
  intro hcon
  have hre : (1 - s).re = -(m : ℝ) := by rw [hcon]; simp
  simp only [Complex.sub_re, Complex.one_re] at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem gamma_half_ne_zero {s : ℂ} (h0 : 0 < s.re) : Complex.Gamma (s / 2) ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m => ?_
  intro hcon
  have hre : (s / 2).re = -(m : ℝ) := by rw [hcon]; simp
  simp only [Complex.div_re] at hre
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  norm_num at hre
  linarith

/-- **`L(s)` is strictly positive throughout the strip.** -/
theorem heatEchoL_pos {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) : 0 < heatEchoL s := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0' : (0 : ℝ) < s.re := by linarith
  have hg : ‖Complex.Gamma (1 - s)‖ ≠ 0 := norm_ne_zero_iff.mpr (gamma_one_sub_ne_zero h0' h1)
  have hgpos : 0 < ‖Complex.Gamma (1 - s)‖ ^ 2 := by positivity
  have hcosh : 0 < Real.cosh (Real.pi * s.im) := Real.cosh_pos _
  have hgam : 0 < Real.Gamma (s.re - 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hpow : (0 : ℝ) < (4 * Real.pi) ^ (s.re - 1) := Real.rpow_pos_of_pos (by positivity) _
  have hsqrt : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi
  rw [heatEchoL]
  positivity

/-- **`C(s)` is nonzero throughout the strip.** -/
theorem heatEchoC_ne_zero {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) : heatEchoC s ≠ 0 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0' : (0 : ℝ) < s.re := by linarith
  have hsqrt : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpi).ne'
  have hbase : ((((4 * Real.pi : ℝ)) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hpow : ((((4 * Real.pi : ℝ)) : ℂ)) ^ ((s - 1) / 2) ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl hbase)
  have hsin : Complex.sin (↑Real.pi * s / 2) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hcon
    have hre : (↑Real.pi * s / 2 : ℂ).re = ((k : ℂ) * ↑Real.pi).re := by rw [hcon]
    simp only [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im] at hre
    norm_num at hre
    have hk : (k : ℝ) = s.re / 2 := by
      field_simp at hre
      linarith
    have hk2 : (k : ℝ) < 1 / 2 := by rw [hk]; linarith
    have hk1 : (1 : ℝ) / 4 < (k : ℝ) := by rw [hk]; linarith
    have hk0 : k = 0 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have hk' : k ≤ -1 := by omega
        have : (k : ℝ) ≤ -1 := by exact_mod_cast hk'
        linarith
      · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
        linarith
    rw [hk0] at hk1
    norm_num at hk1
  have hgs : Complex.Gamma ((s - 1 + 1) / 2) ≠ 0 := by
    have : (s - 1 + 1) / 2 = s / 2 := by ring
    rw [this]
    exact gamma_half_ne_zero h0'
  rw [heatEchoC]
  refine mul_ne_zero (mul_ne_zero (gamma_one_sub_ne_zero h0' h1) hsin) ?_
  exact div_ne_zero (mul_ne_zero hpow hgs) hsqrt

/-- **The exact zero detector `(11)`.**  The subleading heat-aperture echo coefficient vanishes
exactly when the zeta value does. -/
theorem heatEcho_eq_zero_iff {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    heatEchoC s * (starRingEnd ℂ) (riemannZeta s) = 0 ↔ riemannZeta s = 0 := by
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (heatEchoC_ne_zero h0 h1)
    · exact (map_eq_zero_iff _ (starRingEnd ℂ).injective).mp h
  · intro h
    exact Or.inr (by rw [h, map_zero])

end RHTower
