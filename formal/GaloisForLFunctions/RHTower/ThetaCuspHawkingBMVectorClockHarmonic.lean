import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullIncomingCurrent

/-!
# The corpus clock coefficients of the incoming horizon current, harmonic by harmonic

The corpus's `clockCoefficients q a b z j 0` are the plateau values that the translation moment at rate
`−6` reads off the post-onset incoming current (`incomingCurrent_horizon_clockMoment`). Its mass and
radial entries are quadratic forms in the three angular covectors of the incoming field — the coexact
responses `G = coexact F₊`, `G' = coexact F₋` at the doubled-rate parameters and the square covector
`Q = S·⋆dS` — with explicit polynomial coefficients in the physical rate (`clockCoefficients_mass`,
`clockCoefficients_radial`, proved by unfolding the corpus definitions). Since `F±` solve
`Δ F± = λ₂(±)·F± + (λ₂(±)/2)·S²` (`fullAngularField_equation`), on an angular harmonic `μ` the response
contributes `λ₂/(2(μ − λ₂))` per unit of the square covector; the per-harmonic coefficients
`vectorClockMass s μ`, `vectorClockRadial s μ` are the quadratic forms evaluated there
(`_eq_form`), rational functions with denominator `2(μ − (2s+1)(2s+2))·2(μ − (2s+4)(2s+5))` and reduced
numerators of degree two in `μ`.

On the critical line `s = −3/2 + iτ` with a real harmonic `μ = −l` both are purely imaginary
(`_line`, `_line_re`), the denominator is `4((4τ²−2−l)² + 36τ²) > 0`, and the imaginary parts are, up to
sign, the quadratics `A(τ) + B(τ)·l + C(τ)·l²` (`vectorClock{Mass,Radial}Line_eq`) whose discriminants
`4AC − B²` are polynomials in `τ` with positive coefficients (`_Disc_pos`; the leading terms of `4AC`
and `B²` cancel, the doubled-frequency edge `l = 4τ²` being the minimiser). Hence the mass coefficient
has positive and the radial coefficient negative imaginary part at **every** harmonic `l ≥ 0` and
**every** height `τ > 0` (`vectorClockMass_line_im`, `vectorClockRadial_line_im`): the on-line sign of
the vector-sector clock coefficient is pointwise in the harmonic, with no exceptional band.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMVectorClock
open D4BMModularCore D4BMFullIncomingCurrent D4BMPhysicalLiftCurrent D4BMHorizon

/-- Coefficient `α` of the pairing `⟨G, G'⟩` in the corpus mass coefficient. -/
noncomputable def vectorClockMassAlpha (s : ℂ) : ℂ := (-9 : ℂ) * s + (-9 : ℂ) * s ^ 2 + (-2 : ℂ) * s ^ 3
noncomputable def vectorClockMassBeta (s : ℂ) : ℂ := (3 : ℂ) * s + (67 / 4 : ℂ) * s ^ 2 + (15 : ℂ) * s ^ 3 + (19 / 4 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5
noncomputable def vectorClockMassGamma (s : ℂ) : ℂ := (-3 : ℂ) * s + (-13 / 4 : ℂ) * s ^ 2 + (3 : ℂ) * s ^ 3 + (11 / 4 : ℂ) * s ^ 4 + (1 / 2 : ℂ) * s ^ 5
noncomputable def vectorClockMassDelta (s : ℂ) : ℂ := (27 / 4 : ℂ) * s ^ 2 + (63 / 16 : ℂ) * s ^ 3 + (-75 / 16 : ℂ) * s ^ 4 + (-73 / 16 : ℂ) * s ^ 5 + (-21 / 16 : ℂ) * s ^ 6 + (-1 / 8 : ℂ) * s ^ 7

/-- Reduced numerator of the per-harmonic mass coefficient. -/
noncomputable def vectorClockMassNumerator (s μ : ℂ) : ℂ := (-360 : ℂ) * s + (-54 : ℂ) * s * μ + (-2034 : ℂ) * s ^ 2 + (-216 : ℂ) * s ^ 2 * μ + (27 / 4 : ℂ) * s ^ 2 * μ ^ 2 + (-9727 / 2 : ℂ) * s ^ 3 + (-933 / 8 : ℂ) * s ^ 3 * μ + (63 / 16 : ℂ) * s ^ 3 * μ ^ 2 + (-27777 / 4 : ℂ) * s ^ 4 + (1737 / 8 : ℂ) * s ^ 4 * μ + (-75 / 16 : ℂ) * s ^ 4 * μ ^ 2 + (-6928 : ℂ) * s ^ 5 + (2739 / 8 : ℂ) * s ^ 5 * μ + (-73 / 16 : ℂ) * s ^ 5 * μ ^ 2 + (-5103 : ℂ) * s ^ 6 + (1743 / 8 : ℂ) * s ^ 6 * μ + (-21 / 16 : ℂ) * s ^ 6 * μ ^ 2 + (-2727 : ℂ) * s ^ 7 + (299 / 4 : ℂ) * s ^ 7 * μ + (-1 / 8 : ℂ) * s ^ 7 * μ ^ 2 + (-4023 / 4 : ℂ) * s ^ 8 + (27 / 2 : ℂ) * s ^ 8 * μ + (-479 / 2 : ℂ) * s ^ 9 + (1 : ℂ) * s ^ 9 * μ + (-33 : ℂ) * s ^ 10 + (-2 : ℂ) * s ^ 11

/-- The per-harmonic mass coefficient: the quadratic form evaluated on the harmonic `μ`, where the
angular response contributes `λ₂/(2(μ−λ₂))` per unit of the square covector. -/
noncomputable def vectorClockMass (s μ : ℂ) : ℂ :=
  vectorClockMassNumerator s μ / (2 * (μ - (2 * s + 1) * (2 * s + 2))) / (2 * (μ - (2 * s + 4) * (2 * s + 5)))

theorem vectorClockMass_eq_form (s μ : ℂ) (h1 : μ - (2 * s + 1) * (2 * s + 2) ≠ 0) (h2 : μ - (2 * s + 4) * (2 * s + 5) ≠ 0) :
    vectorClockMass s μ =
      vectorClockMassAlpha s * ((2 * s + 1) * (2 * s + 2) / (2 * (μ - (2 * s + 1) * (2 * s + 2)))) * ((2 * s + 4) * (2 * s + 5) / (2 * (μ - (2 * s + 4) * (2 * s + 5)))) +
      vectorClockMassBeta s * ((2 * s + 1) * (2 * s + 2) / (2 * (μ - (2 * s + 1) * (2 * s + 2)))) / 2 +
      vectorClockMassGamma s * ((2 * s + 4) * (2 * s + 5) / (2 * (μ - (2 * s + 4) * (2 * s + 5)))) / 2 +
      vectorClockMassDelta s / 4 := by
  have hN : vectorClockMassNumerator s μ =
      vectorClockMassAlpha s * (((2 * s + 1) * (2 * s + 2)) * ((2 * s + 4) * (2 * s + 5))) +
      vectorClockMassBeta s * ((2 * s + 1) * (2 * s + 2)) * (μ - (2 * s + 4) * (2 * s + 5)) +
      vectorClockMassGamma s * ((2 * s + 4) * (2 * s + 5)) * (μ - (2 * s + 1) * (2 * s + 2)) +
      vectorClockMassDelta s * ((μ - (2 * s + 1) * (2 * s + 2)) * (μ - (2 * s + 4) * (2 * s + 5))) := by
    unfold vectorClockMassNumerator vectorClockMassAlpha vectorClockMassBeta vectorClockMassGamma vectorClockMassDelta
    ring
  unfold vectorClockMass
  have h1' : (2 : ℂ) * (μ - (2 * s + 1) * (2 * s + 2)) ≠ 0 := mul_ne_zero two_ne_zero h1
  have h2' : (2 : ℂ) * (μ - (2 * s + 4) * (2 * s + 5)) ≠ 0 := mul_ne_zero two_ne_zero h2
  have e1 := mul_inv_cancel₀ h1'
  have e2 := mul_inv_cancel₀ h2'
  linear_combination ((2 * (μ - (2 * s + 1) * (2 * s + 2)))⁻¹ * (2 * (μ - (2 * s + 4) * (2 * s + 5)))⁻¹) * hN +
    ((vectorClockMassGamma s * ((2 * s + 4) * (2 * s + 5)) * (2 * (μ - (2 * s + 4) * (2 * s + 5)))⁻¹ +
      vectorClockMassDelta s * (μ - (2 * s + 4) * (2 * s + 5)) * (2 * (μ - (2 * s + 4) * (2 * s + 5)))⁻¹) / 2) * e1 +
    ((vectorClockMassBeta s * ((2 * s + 1) * (2 * s + 2)) * (2 * (μ - (2 * s + 1) * (2 * s + 2)))⁻¹ +
      vectorClockMassDelta s / 2) / 2) * e2

/-- Imaginary part of the reduced numerator on the critical line at the real harmonic `μ = −l`. -/
noncomputable def vectorClockMassLine (τ l : ℝ) : ℝ := (1737 / 128 : ℝ) * τ + (5049 / 128 : ℝ) * τ * l + (2025 / 512 : ℝ) * τ * l ^ 2 + (9529 / 128 : ℝ) * τ ^ 3 + (2445 / 64 : ℝ) * τ ^ 3 * l + (531 / 128 : ℝ) * τ ^ 3 * l ^ 2 + (709 / 8 : ℝ) * τ ^ 5 + (3 / 16 : ℝ) * τ ^ 5 * l + (43 / 32 : ℝ) * τ ^ 5 * l ^ 2 + (135 / 4 : ℝ) * τ ^ 7 + (-25 / 4 : ℝ) * τ ^ 7 * l + (1 / 8 : ℝ) * τ ^ 7 * l ^ 2 + (8 : ℝ) * τ ^ 9 + (-1 : ℝ) * τ ^ 9 * l + (2 : ℝ) * τ ^ 11

theorem vectorClockMassNumerator_line (τ l : ℝ) :
    vectorClockMassNumerator ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ)) = Complex.I * (vectorClockMassLine τ l : ℂ) := by
  unfold vectorClockMassNumerator vectorClockMassLine
  push_cast
  linear_combination ((-9529 / 128 : ℂ) * (τ : ℂ) ^ 3 * Complex.I + (-2445 / 64 : ℂ) * (τ : ℂ) ^ 3 * (l : ℂ) * Complex.I + (-531 / 128 : ℂ) * (τ : ℂ) ^ 3 * (l : ℂ) ^ 2 * Complex.I + (-709 / 8 : ℂ) * (τ : ℂ) ^ 5 * Complex.I + (709 / 8 : ℂ) * (τ : ℂ) ^ 5 * Complex.I ^ 3 + (-3 / 16 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) * Complex.I + (3 / 16 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) * Complex.I ^ 3 + (-43 / 32 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) ^ 2 * Complex.I + (43 / 32 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (-135 / 4 : ℂ) * (τ : ℂ) ^ 7 * Complex.I + (135 / 4 : ℂ) * (τ : ℂ) ^ 7 * Complex.I ^ 3 + (-135 / 4 : ℂ) * (τ : ℂ) ^ 7 * Complex.I ^ 5 + (25 / 4 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) * Complex.I + (-25 / 4 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) * Complex.I ^ 3 + (25 / 4 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) * Complex.I ^ 5 + (-1 / 8 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I + (1 / 8 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (-1 / 8 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I ^ 5 + (-8 : ℂ) * (τ : ℂ) ^ 9 * Complex.I + (8 : ℂ) * (τ : ℂ) ^ 9 * Complex.I ^ 3 + (-8 : ℂ) * (τ : ℂ) ^ 9 * Complex.I ^ 5 + (8 : ℂ) * (τ : ℂ) ^ 9 * Complex.I ^ 7 + (1 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I + (-1 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 3 + (1 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 5 + (-1 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 7 + (-2 : ℂ) * (τ : ℂ) ^ 11 * Complex.I + (2 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 3 + (-2 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 5 + (2 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 7 + (-2 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 9) * Complex.I_sq

noncomputable def vectorClockMassLineA (τ : ℝ) : ℝ := (1737 / 128 : ℝ) * τ + (9529 / 128 : ℝ) * τ ^ 3 + (709 / 8 : ℝ) * τ ^ 5 + (135 / 4 : ℝ) * τ ^ 7 + (8 : ℝ) * τ ^ 9 + (2 : ℝ) * τ ^ 11
noncomputable def vectorClockMassLineB (τ : ℝ) : ℝ := (5049 / 128 : ℝ) * τ + (2445 / 64 : ℝ) * τ ^ 3 + (3 / 16 : ℝ) * τ ^ 5 + (-25 / 4 : ℝ) * τ ^ 7 + (-1 : ℝ) * τ ^ 9
noncomputable def vectorClockMassLineC (τ : ℝ) : ℝ := (2025 / 512 : ℝ) * τ + (531 / 128 : ℝ) * τ ^ 3 + (43 / 32 : ℝ) * τ ^ 5 + (1 / 8 : ℝ) * τ ^ 7

theorem vectorClockMassLine_eq (τ l : ℝ) :
    vectorClockMassLine τ l = (1 : ℝ) * (vectorClockMassLineA τ + vectorClockMassLineB τ * l + vectorClockMassLineC τ * l ^ 2) := by
  unfold vectorClockMassLine vectorClockMassLineA vectorClockMassLineB vectorClockMassLineC
  ring

/-- The discriminant `4AC − B²` of the line quadratic is positive for `τ ≥ 1` (the leading terms of
`4AC` and `B²` cancel; the doubled-frequency edge is the minimiser). -/
theorem vectorClockMassDisc_pos (τ : ℝ) (hτ : 1 ≤ τ) :
    0 < 4 * vectorClockMassLineA τ * vectorClockMassLineC τ - vectorClockMassLineB τ ^ 2 := by
  have h : 4 * vectorClockMassLineA τ * vectorClockMassLineC τ - vectorClockMassLineB τ ^ 2 = (-343359 / 256 : ℝ) * τ ^ 2 + (-26393607 / 16384 : ℝ) * τ ^ 4 + (2531475 / 2048 : ℝ) * τ ^ 6 + (2959591 / 1024 : ℝ) * τ ^ 8 + (112421 / 64 : ℝ) * τ ^ 10 + (30007 / 64 : ℝ) * τ ^ 12 + (435 / 8 : ℝ) * τ ^ 14 + (9 / 4 : ℝ) * τ ^ 16 := by
    unfold vectorClockMassLineA vectorClockMassLineB vectorClockMassLineC
    ring
  rw [h]
  have p2 : τ ^ 2 ≤ τ ^ 4 := pow_le_pow_right₀ hτ (by norm_num)
  have p4 : τ ^ 4 ≤ τ ^ 6 := pow_le_pow_right₀ hτ (by norm_num)
  have p6 : τ ^ 6 ≤ τ ^ 8 := pow_le_pow_right₀ hτ (by norm_num)
  have p8 : τ ^ 8 ≤ τ ^ 10 := pow_le_pow_right₀ hτ (by norm_num)
  have p10 : τ ^ 10 ≤ τ ^ 12 := pow_le_pow_right₀ hτ (by norm_num)
  have p12 : τ ^ 12 ≤ τ ^ 14 := pow_le_pow_right₀ hτ (by norm_num)
  have p14 : τ ^ 14 ≤ τ ^ 16 := pow_le_pow_right₀ hτ (by norm_num)
  have q2 : (0 : ℝ) < τ ^ 2 := by positivity
  linarith

theorem vectorClockMassLineC_pos (τ : ℝ) (hτ : 1 ≤ τ) : 0 < vectorClockMassLineC τ := by
  unfold vectorClockMassLineC
  have h1 : (0 : ℝ) < τ := by linarith
  have h3 : (0 : ℝ) < τ ^ 3 := pow_pos h1 3
  have h5 : (0 : ℝ) < τ ^ 5 := pow_pos h1 5
  have h7 : (0 : ℝ) < τ ^ 7 := pow_pos h1 7
  linarith

/-- The line quadratic is positive at every harmonic `l ≥ 0` and every height `τ ≥ 1`. -/
theorem vectorClockMassQuadratic_pos (τ l : ℝ) (hτ : 1 ≤ τ) :
    0 < vectorClockMassLineA τ + vectorClockMassLineB τ * l + vectorClockMassLineC τ * l ^ 2 := by
  have hC := vectorClockMassLineC_pos τ hτ
  have hD := vectorClockMassDisc_pos τ hτ
  have key : 4 * vectorClockMassLineC τ * (vectorClockMassLineA τ + vectorClockMassLineB τ * l + vectorClockMassLineC τ * l ^ 2) =
      (2 * vectorClockMassLineC τ * l + vectorClockMassLineB τ) ^ 2 + (4 * vectorClockMassLineA τ * vectorClockMassLineC τ - vectorClockMassLineB τ ^ 2) := by ring
  have hsq : 0 ≤ (2 * vectorClockMassLineC τ * l + vectorClockMassLineB τ) ^ 2 := sq_nonneg _
  have hprod : 0 < 4 * vectorClockMassLineC τ * (vectorClockMassLineA τ + vectorClockMassLineB τ * l + vectorClockMassLineC τ * l ^ 2) := by
    rw [key]; linarith
  exact pos_of_mul_pos_right hprod (by linarith)

/-- Coefficient `α` of the pairing `⟨G, G'⟩` in the corpus radial coefficient. -/
noncomputable def vectorClockRadialAlpha (s : ℂ) : ℂ := (18 : ℂ) * s + (18 : ℂ) * s ^ 2 + (4 : ℂ) * s ^ 3
noncomputable def vectorClockRadialBeta (s : ℂ) : ℂ := (-24 : ℂ) * s + (-56 : ℂ) * s ^ 2 + (-77 / 2 : ℂ) * s ^ 3 + (-21 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5
noncomputable def vectorClockRadialGamma (s : ℂ) : ℂ := (3 / 2 : ℂ) * s + (13 / 2 : ℂ) * s ^ 2 + (-5 / 2 : ℂ) * s ^ 3 + (-9 / 2 : ℂ) * s ^ 4 + (-1 : ℂ) * s ^ 5
noncomputable def vectorClockRadialDelta (s : ℂ) : ℂ := (-9 / 2 : ℂ) * s + (-117 / 8 : ℂ) * s ^ 2 + (-35 / 8 : ℂ) * s ^ 3 + (45 / 4 : ℂ) * s ^ 4 + (75 / 8 : ℂ) * s ^ 5 + (21 / 8 : ℂ) * s ^ 6 + (1 / 4 : ℂ) * s ^ 7

/-- Reduced numerator of the per-harmonic radial coefficient. -/
noncomputable def vectorClockRadialNumerator (s μ : ℂ) : ℂ := (1440 : ℂ) * s + (81 : ℂ) * s * μ + (-9 / 2 : ℂ) * s * μ ^ 2 + (7731 : ℂ) * s ^ 2 + (1323 / 4 : ℂ) * s ^ 2 * μ + (-117 / 8 : ℂ) * s ^ 2 * μ ^ 2 + (33859 / 2 : ℂ) * s ^ 3 + (189 / 4 : ℂ) * s ^ 3 * μ + (-35 / 8 : ℂ) * s ^ 3 * μ ^ 2 + (21207 : ℂ) * s ^ 4 + (-1221 / 2 : ℂ) * s ^ 4 * μ + (45 / 4 : ℂ) * s ^ 4 * μ ^ 2 + (36329 / 2 : ℂ) * s ^ 5 + (-3085 / 4 : ℂ) * s ^ 5 * μ + (75 / 8 : ℂ) * s ^ 5 * μ ^ 2 + (23541 / 2 : ℂ) * s ^ 6 + (-1827 / 4 : ℂ) * s ^ 6 * μ + (21 / 8 : ℂ) * s ^ 6 * μ ^ 2 + (5819 : ℂ) * s ^ 7 + (-303 / 2 : ℂ) * s ^ 7 * μ + (1 / 4 : ℂ) * s ^ 7 * μ ^ 2 + (4131 / 2 : ℂ) * s ^ 8 + (-27 : ℂ) * s ^ 8 * μ + (483 : ℂ) * s ^ 9 + (-2 : ℂ) * s ^ 9 * μ + (66 : ℂ) * s ^ 10 + (4 : ℂ) * s ^ 11

/-- The per-harmonic radial coefficient: the quadratic form evaluated on the harmonic `μ`, where the
angular response contributes `λ₂/(2(μ−λ₂))` per unit of the square covector. -/
noncomputable def vectorClockRadial (s μ : ℂ) : ℂ :=
  vectorClockRadialNumerator s μ / (2 * (μ - (2 * s + 1) * (2 * s + 2))) / (2 * (μ - (2 * s + 4) * (2 * s + 5)))

theorem vectorClockRadial_eq_form (s μ : ℂ) (h1 : μ - (2 * s + 1) * (2 * s + 2) ≠ 0) (h2 : μ - (2 * s + 4) * (2 * s + 5) ≠ 0) :
    vectorClockRadial s μ =
      vectorClockRadialAlpha s * ((2 * s + 1) * (2 * s + 2) / (2 * (μ - (2 * s + 1) * (2 * s + 2)))) * ((2 * s + 4) * (2 * s + 5) / (2 * (μ - (2 * s + 4) * (2 * s + 5)))) +
      vectorClockRadialBeta s * ((2 * s + 1) * (2 * s + 2) / (2 * (μ - (2 * s + 1) * (2 * s + 2)))) / 2 +
      vectorClockRadialGamma s * ((2 * s + 4) * (2 * s + 5) / (2 * (μ - (2 * s + 4) * (2 * s + 5)))) / 2 +
      vectorClockRadialDelta s / 4 := by
  have hN : vectorClockRadialNumerator s μ =
      vectorClockRadialAlpha s * (((2 * s + 1) * (2 * s + 2)) * ((2 * s + 4) * (2 * s + 5))) +
      vectorClockRadialBeta s * ((2 * s + 1) * (2 * s + 2)) * (μ - (2 * s + 4) * (2 * s + 5)) +
      vectorClockRadialGamma s * ((2 * s + 4) * (2 * s + 5)) * (μ - (2 * s + 1) * (2 * s + 2)) +
      vectorClockRadialDelta s * ((μ - (2 * s + 1) * (2 * s + 2)) * (μ - (2 * s + 4) * (2 * s + 5))) := by
    unfold vectorClockRadialNumerator vectorClockRadialAlpha vectorClockRadialBeta vectorClockRadialGamma vectorClockRadialDelta
    ring
  unfold vectorClockRadial
  have h1' : (2 : ℂ) * (μ - (2 * s + 1) * (2 * s + 2)) ≠ 0 := mul_ne_zero two_ne_zero h1
  have h2' : (2 : ℂ) * (μ - (2 * s + 4) * (2 * s + 5)) ≠ 0 := mul_ne_zero two_ne_zero h2
  have e1 := mul_inv_cancel₀ h1'
  have e2 := mul_inv_cancel₀ h2'
  linear_combination ((2 * (μ - (2 * s + 1) * (2 * s + 2)))⁻¹ * (2 * (μ - (2 * s + 4) * (2 * s + 5)))⁻¹) * hN +
    ((vectorClockRadialGamma s * ((2 * s + 4) * (2 * s + 5)) * (2 * (μ - (2 * s + 4) * (2 * s + 5)))⁻¹ +
      vectorClockRadialDelta s * (μ - (2 * s + 4) * (2 * s + 5)) * (2 * (μ - (2 * s + 4) * (2 * s + 5)))⁻¹) / 2) * e1 +
    ((vectorClockRadialBeta s * ((2 * s + 1) * (2 * s + 2)) * (2 * (μ - (2 * s + 1) * (2 * s + 2)))⁻¹ +
      vectorClockRadialDelta s / 2) / 2) * e2

/-- Imaginary part of the reduced numerator on the critical line at the real harmonic `μ = −l`. -/
noncomputable def vectorClockRadialLine (τ l : ℝ) : ℝ := (-3717 / 64 : ℝ) * τ + (-5589 / 64 : ℝ) * τ * l + (-1125 / 256 : ℝ) * τ * l ^ 2 + (-20165 / 64 : ℝ) * τ ^ 3 + (-2817 / 32 : ℝ) * τ ^ 3 * l + (-395 / 64 : ℝ) * τ ^ 3 * l ^ 2 + (-715 / 2 : ℝ) * τ ^ 5 + (-67 / 8 : ℝ) * τ ^ 5 * l + (-39 / 16 : ℝ) * τ ^ 5 * l ^ 2 + (-217 / 2 : ℝ) * τ ^ 7 + (21 / 2 : ℝ) * τ ^ 7 * l + (-1 / 4 : ℝ) * τ ^ 7 * l ^ 2 + (-12 : ℝ) * τ ^ 9 + (2 : ℝ) * τ ^ 9 * l + (-4 : ℝ) * τ ^ 11

theorem vectorClockRadialNumerator_line (τ l : ℝ) :
    vectorClockRadialNumerator ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ)) = Complex.I * (vectorClockRadialLine τ l : ℂ) := by
  unfold vectorClockRadialNumerator vectorClockRadialLine
  push_cast
  linear_combination ((20165 / 64 : ℂ) * (τ : ℂ) ^ 3 * Complex.I + (2817 / 32 : ℂ) * (τ : ℂ) ^ 3 * (l : ℂ) * Complex.I + (395 / 64 : ℂ) * (τ : ℂ) ^ 3 * (l : ℂ) ^ 2 * Complex.I + (715 / 2 : ℂ) * (τ : ℂ) ^ 5 * Complex.I + (-715 / 2 : ℂ) * (τ : ℂ) ^ 5 * Complex.I ^ 3 + (67 / 8 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) * Complex.I + (-67 / 8 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) * Complex.I ^ 3 + (39 / 16 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) ^ 2 * Complex.I + (-39 / 16 : ℂ) * (τ : ℂ) ^ 5 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (217 / 2 : ℂ) * (τ : ℂ) ^ 7 * Complex.I + (-217 / 2 : ℂ) * (τ : ℂ) ^ 7 * Complex.I ^ 3 + (217 / 2 : ℂ) * (τ : ℂ) ^ 7 * Complex.I ^ 5 + (-21 / 2 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) * Complex.I + (21 / 2 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) * Complex.I ^ 3 + (-21 / 2 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) * Complex.I ^ 5 + (1 / 4 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I + (-1 / 4 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I ^ 3 + (1 / 4 : ℂ) * (τ : ℂ) ^ 7 * (l : ℂ) ^ 2 * Complex.I ^ 5 + (12 : ℂ) * (τ : ℂ) ^ 9 * Complex.I + (-12 : ℂ) * (τ : ℂ) ^ 9 * Complex.I ^ 3 + (12 : ℂ) * (τ : ℂ) ^ 9 * Complex.I ^ 5 + (-12 : ℂ) * (τ : ℂ) ^ 9 * Complex.I ^ 7 + (-2 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I + (2 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 3 + (-2 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 5 + (2 : ℂ) * (τ : ℂ) ^ 9 * (l : ℂ) * Complex.I ^ 7 + (4 : ℂ) * (τ : ℂ) ^ 11 * Complex.I + (-4 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 3 + (4 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 5 + (-4 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 7 + (4 : ℂ) * (τ : ℂ) ^ 11 * Complex.I ^ 9) * Complex.I_sq

noncomputable def vectorClockRadialLineA (τ : ℝ) : ℝ := (3717 / 64 : ℝ) * τ + (20165 / 64 : ℝ) * τ ^ 3 + (715 / 2 : ℝ) * τ ^ 5 + (217 / 2 : ℝ) * τ ^ 7 + (12 : ℝ) * τ ^ 9 + (4 : ℝ) * τ ^ 11
noncomputable def vectorClockRadialLineB (τ : ℝ) : ℝ := (5589 / 64 : ℝ) * τ + (2817 / 32 : ℝ) * τ ^ 3 + (67 / 8 : ℝ) * τ ^ 5 + (-21 / 2 : ℝ) * τ ^ 7 + (-2 : ℝ) * τ ^ 9
noncomputable def vectorClockRadialLineC (τ : ℝ) : ℝ := (1125 / 256 : ℝ) * τ + (395 / 64 : ℝ) * τ ^ 3 + (39 / 16 : ℝ) * τ ^ 5 + (1 / 4 : ℝ) * τ ^ 7

theorem vectorClockRadialLine_eq (τ l : ℝ) :
    vectorClockRadialLine τ l = (-1 : ℝ) * (vectorClockRadialLineA τ + vectorClockRadialLineB τ * l + vectorClockRadialLineC τ * l ^ 2) := by
  unfold vectorClockRadialLine vectorClockRadialLineA vectorClockRadialLineB vectorClockRadialLineC
  ring

/-- The discriminant `4AC − B²` of the line quadratic is positive for `τ ≥ 1` (the leading terms of
`4AC` and `B²` cancel; the doubled-frequency edge is the minimiser). -/
theorem vectorClockRadialDisc_pos (τ : ℝ) (hτ : 1 ≤ τ) :
    0 < 4 * vectorClockRadialLineA τ * vectorClockRadialLineC τ - vectorClockRadialLineB τ ^ 2 := by
  have h : 4 * vectorClockRadialLineA τ * vectorClockRadialLineC τ - vectorClockRadialLineB τ ^ 2 = (-422739 / 64 : ℝ) * τ ^ 2 + (-34418367 / 4096 : ℝ) * τ ^ 4 + (2773343 / 512 : ℝ) * τ ^ 6 + (3640951 / 256 : ℝ) * τ ^ 8 + (141089 / 16 : ℝ) * τ ^ 10 + (36959 / 16 : ℝ) * τ ^ 12 + (495 / 2 : ℝ) * τ ^ 14 + (9 : ℝ) * τ ^ 16 := by
    unfold vectorClockRadialLineA vectorClockRadialLineB vectorClockRadialLineC
    ring
  rw [h]
  have p2 : τ ^ 2 ≤ τ ^ 4 := pow_le_pow_right₀ hτ (by norm_num)
  have p4 : τ ^ 4 ≤ τ ^ 6 := pow_le_pow_right₀ hτ (by norm_num)
  have p6 : τ ^ 6 ≤ τ ^ 8 := pow_le_pow_right₀ hτ (by norm_num)
  have p8 : τ ^ 8 ≤ τ ^ 10 := pow_le_pow_right₀ hτ (by norm_num)
  have p10 : τ ^ 10 ≤ τ ^ 12 := pow_le_pow_right₀ hτ (by norm_num)
  have p12 : τ ^ 12 ≤ τ ^ 14 := pow_le_pow_right₀ hτ (by norm_num)
  have p14 : τ ^ 14 ≤ τ ^ 16 := pow_le_pow_right₀ hτ (by norm_num)
  have q2 : (0 : ℝ) < τ ^ 2 := by positivity
  linarith

theorem vectorClockRadialLineC_pos (τ : ℝ) (hτ : 1 ≤ τ) : 0 < vectorClockRadialLineC τ := by
  unfold vectorClockRadialLineC
  have h1 : (0 : ℝ) < τ := by linarith
  have h3 : (0 : ℝ) < τ ^ 3 := pow_pos h1 3
  have h5 : (0 : ℝ) < τ ^ 5 := pow_pos h1 5
  have h7 : (0 : ℝ) < τ ^ 7 := pow_pos h1 7
  linarith

/-- The line quadratic is positive at every harmonic `l ≥ 0` and every height `τ ≥ 1`. -/
theorem vectorClockRadialQuadratic_pos (τ l : ℝ) (hτ : 1 ≤ τ) :
    0 < vectorClockRadialLineA τ + vectorClockRadialLineB τ * l + vectorClockRadialLineC τ * l ^ 2 := by
  have hC := vectorClockRadialLineC_pos τ hτ
  have hD := vectorClockRadialDisc_pos τ hτ
  have key : 4 * vectorClockRadialLineC τ * (vectorClockRadialLineA τ + vectorClockRadialLineB τ * l + vectorClockRadialLineC τ * l ^ 2) =
      (2 * vectorClockRadialLineC τ * l + vectorClockRadialLineB τ) ^ 2 + (4 * vectorClockRadialLineA τ * vectorClockRadialLineC τ - vectorClockRadialLineB τ ^ 2) := by ring
  have hsq : 0 ≤ (2 * vectorClockRadialLineC τ * l + vectorClockRadialLineB τ) ^ 2 := sq_nonneg _
  have hprod : 0 < 4 * vectorClockRadialLineC τ * (vectorClockRadialLineA τ + vectorClockRadialLineB τ * l + vectorClockRadialLineC τ * l ^ 2) := by
    rw [key]; linarith
  exact pos_of_mul_pos_right hprod (by linarith)


/-- Pointwise Euclidean pairing of two covector jets. -/
noncomputable def covectorPair (P Q : Fin 2 → ScalarTwoJet (Fin 2) ℂ) : ℂ := ∑ j : Fin 2, (P j).value * (Q j).value

/-- The corpus mass coefficient of the incoming horizon current is a quadratic form in the two angular
responses `G = coexact F₊`, `G' = coexact F₋` and the square covector `Q = S·⋆dS`, with the coefficients
`vectorClockMass{Alpha,Beta,Gamma,Delta}` evaluated at the physical rate. -/
theorem clockCoefficients_mass (q : XiZeroCopy) (a b : ℂ) (z : Point) :
    clockCoefficients q a b z 0 0 = (a ^ 2 * b ^ 2 / 16) *
      (vectorClockMassAlpha (physicalRate q true) *
          covectorPair (fun j => ScalarTwoJet.ofField (fullAngularCovector q true j) z) (fun j => ScalarTwoJet.ofField (fullAngularCovector q false j) z) +
        vectorClockMassBeta (physicalRate q true) *
          covectorPair (fun j => ScalarTwoJet.ofField (fullAngularCovector q true j) z) (angularJets q z) +
        vectorClockMassGamma (physicalRate q true) *
          covectorPair (fun j => ScalarTwoJet.ofField (fullAngularCovector q false j) z) (angularJets q z) +
        vectorClockMassDelta (physicalRate q true) * covectorPair (angularJets q z) (angularJets q z)) := by
  have ht : physicalRate q false = -3 - physicalRate q true := by simp [physicalRate]; ring
  have hN : ∀ j, (normalJet q true z j).value = -(physicalRate q true) * (ScalarTwoJet.ofField (fullAngularCovector q true j) z).value +
      (physicalRate q true * (physicalRate q true - 1) * (physicalRate q true + 2) / 4) * (angularJets q z j).value := fun j => rfl
  have hM : ∀ j, (normalJet q false z j).value = -(physicalRate q false) * (ScalarTwoJet.ofField (fullAngularCovector q false j) z).value +
      (physicalRate q false * (physicalRate q false - 1) * (physicalRate q false + 2) / 4) * (angularJets q z j).value := fun j => rfl
  have hU : ∀ j, (traceJet q true z j).value = 1 * (ScalarTwoJet.ofField (fullAngularCovector q true j) z).value +
      (-(physicalRate q true) * (physicalRate q true - 1) / 4) * (angularJets q z j).value := fun j => rfl
  have hV : ∀ j, (traceJet q false z j).value = 1 * (ScalarTwoJet.ofField (fullAngularCovector q false j) z).value +
      (-(physicalRate q false) * (physicalRate q false - 1) / 4) * (angularJets q z j).value := fun j => rfl
  show 4 * (a ^ 2 * b ^ 2 / 64) * ((physicalRate q true - physicalRate q false) * covectorPair (normalJet q true z) (normalJet q false z) +
      physicalRate q false * covectorPair (traceJet q false z) (normalJet q true z) -
      physicalRate q true * covectorPair (traceJet q true z) (normalJet q false z)) = _
  unfold covectorPair vectorClockMassAlpha vectorClockMassBeta vectorClockMassGamma vectorClockMassDelta
  simp only [Fin.sum_univ_two, hN, hM, hU, hV, ht]
  ring

/-- The corpus radial coefficient of the incoming horizon current as the same kind of quadratic form. -/
theorem clockCoefficients_radial (q : XiZeroCopy) (a b : ℂ) (z : Point) :
    clockCoefficients q a b z 1 0 = (a ^ 2 * b ^ 2 / 16) *
      (vectorClockRadialAlpha (physicalRate q true) *
          covectorPair (fun j => ScalarTwoJet.ofField (fullAngularCovector q true j) z) (fun j => ScalarTwoJet.ofField (fullAngularCovector q false j) z) +
        vectorClockRadialBeta (physicalRate q true) *
          covectorPair (fun j => ScalarTwoJet.ofField (fullAngularCovector q true j) z) (angularJets q z) +
        vectorClockRadialGamma (physicalRate q true) *
          covectorPair (fun j => ScalarTwoJet.ofField (fullAngularCovector q false j) z) (angularJets q z) +
        vectorClockRadialDelta (physicalRate q true) * covectorPair (angularJets q z) (angularJets q z)) := by
  have ht : physicalRate q false = -3 - physicalRate q true := by simp [physicalRate]; ring
  have hN : ∀ j, (normalJet q true z j).value = -(physicalRate q true) * (ScalarTwoJet.ofField (fullAngularCovector q true j) z).value +
      (physicalRate q true * (physicalRate q true - 1) * (physicalRate q true + 2) / 4) * (angularJets q z j).value := fun j => rfl
  have hM : ∀ j, (normalJet q false z j).value = -(physicalRate q false) * (ScalarTwoJet.ofField (fullAngularCovector q false j) z).value +
      (physicalRate q false * (physicalRate q false - 1) * (physicalRate q false + 2) / 4) * (angularJets q z j).value := fun j => rfl
  have hU : ∀ j, (traceJet q true z j).value = 1 * (ScalarTwoJet.ofField (fullAngularCovector q true j) z).value +
      (-(physicalRate q true) * (physicalRate q true - 1) / 4) * (angularJets q z j).value := fun j => rfl
  have hV : ∀ j, (traceJet q false z j).value = 1 * (ScalarTwoJet.ofField (fullAngularCovector q false j) z).value +
      (-(physicalRate q false) * (physicalRate q false - 1) / 4) * (angularJets q z j).value := fun j => rfl
  show 4 * (a ^ 2 * b ^ 2 / 64) * (physicalRate q false * (2 * physicalRate q true + 1) * covectorPair (traceJet q false z) (normalJet q true z) -
      physicalRate q true * (2 * physicalRate q false + 1) * covectorPair (traceJet q true z) (normalJet q false z)) = _
  unfold covectorPair vectorClockRadialAlpha vectorClockRadialBeta vectorClockRadialGamma vectorClockRadialDelta
  simp only [Fin.sum_univ_two, hN, hM, hU, hV, ht]
  ring


/-- The line denominator of the per-harmonic coefficients. -/
theorem vectorClock_line_denominator (τ l : ℝ) :
    2 * ((-(l : ℂ)) - (2 * ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) + 1) * (2 * ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) + 2)) *
        (2 * ((-(l : ℂ)) - (2 * ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) + 4) * (2 * ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) + 5))) =
      ((4 * ((4 * τ ^ 2 - 2 - l) ^ 2 + 36 * τ ^ 2) : ℝ) : ℂ) := by
  push_cast
  linear_combination ((-80 : ℂ) * (τ : ℂ) ^ 2 + (32 : ℂ) * (τ : ℂ) ^ 2 * (l : ℂ) + (-64 : ℂ) * (τ : ℂ) ^ 4 + (64 : ℂ) * (τ : ℂ) ^ 4 * Complex.I ^ 2) * Complex.I_sq

theorem vectorClock_line_den_pos (τ l : ℝ) (hτ : 0 < τ) : (0 : ℝ) < 4 * ((4 * τ ^ 2 - 2 - l) ^ 2 + 36 * τ ^ 2) := by
  have : (0 : ℝ) < 36 * τ ^ 2 := by positivity
  nlinarith [sq_nonneg (4 * τ ^ 2 - 2 - l)]


theorem vectorClockMass_line (τ l : ℝ) (hτ : 0 < τ) :
    vectorClockMass ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ)) * ((4 * ((4 * τ ^ 2 - 2 - l) ^ 2 + 36 * τ ^ 2) : ℝ) : ℂ) =
      Complex.I * (vectorClockMassLine τ l : ℂ) := by
  have hden : ((4 * ((4 * τ ^ 2 - 2 - l) ^ 2 + 36 * τ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (vectorClock_line_den_pos τ l hτ).ne'
  unfold vectorClockMass
  rw [div_div, ← vectorClock_line_denominator τ l, div_mul_cancel₀ _ (by rw [vectorClock_line_denominator τ l]; exact hden)]
  exact vectorClockMassNumerator_line τ l

/-- On the critical line the per-harmonic mass coefficient has positive imaginary part at
every harmonic `l ≥ 0` and every height `τ ≥ 1`. -/
theorem vectorClockMass_line_im (τ l : ℝ) (hτ : 1 ≤ τ) : 0 < (vectorClockMass ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ))).im := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  have h := congrArg Complex.im (vectorClockMass_line τ l hτ0)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
  have hden := vectorClock_line_den_pos τ l hτ0
  have hq := vectorClockMassQuadratic_pos τ l hτ
  rw [vectorClockMassLine_eq] at h
  nlinarith

theorem vectorClockMass_line_re (τ l : ℝ) (hτ : 0 < τ) :
    (vectorClockMass ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ))).re = 0 := by
  have h := congrArg Complex.re (vectorClockMass_line τ l hτ)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' (vectorClock_line_den_pos τ l hτ).ne'

theorem vectorClockRadial_line (τ l : ℝ) (hτ : 0 < τ) :
    vectorClockRadial ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ)) * ((4 * ((4 * τ ^ 2 - 2 - l) ^ 2 + 36 * τ ^ 2) : ℝ) : ℂ) =
      Complex.I * (vectorClockRadialLine τ l : ℂ) := by
  have hden : ((4 * ((4 * τ ^ 2 - 2 - l) ^ 2 + 36 * τ ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (vectorClock_line_den_pos τ l hτ).ne'
  unfold vectorClockRadial
  rw [div_div, ← vectorClock_line_denominator τ l, div_mul_cancel₀ _ (by rw [vectorClock_line_denominator τ l]; exact hden)]
  exact vectorClockRadialNumerator_line τ l

/-- On the critical line the per-harmonic radial coefficient has negative imaginary part at
every harmonic `l ≥ 0` and every height `τ ≥ 1`. -/
theorem vectorClockRadial_line_im (τ l : ℝ) (hτ : 1 ≤ τ) : (vectorClockRadial ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ))).im < 0 := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  have h := congrArg Complex.im (vectorClockRadial_line τ l hτ0)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_add, one_mul] at h
  have hden := vectorClock_line_den_pos τ l hτ0
  have hq := vectorClockRadialQuadratic_pos τ l hτ
  rw [vectorClockRadialLine_eq] at h
  nlinarith

theorem vectorClockRadial_line_re (τ l : ℝ) (hτ : 0 < τ) :
    (vectorClockRadial ((-3 / 2 : ℂ) + (τ : ℂ) * Complex.I) (-(l : ℂ))).re = 0 := by
  have h := congrArg Complex.re (vectorClockRadial_line τ l hτ)
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at h
  simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' (vectorClock_line_den_pos τ l hτ).ne'

end RHTower.D4BMVectorClock
