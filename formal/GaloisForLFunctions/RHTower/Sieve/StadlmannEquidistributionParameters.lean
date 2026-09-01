import GaloisForLFunctions.RHTower.Sieve.StadlmannBoundedGapsApplications

/-!
# Parameter applications for Stadlmann's equidistribution lemmas

The proof of Proposition 3 in arXiv:2608.31126 introduces auxiliary widths `δ*` to invoke
Lemmas 3--7.  This file verifies every displayed admissibility implication and specializes the
whole chain to the final rational parameters.  Analytic equidistribution conclusions are not
postulated here; these are the exact closed parameter gates that their future formalizations can
consume.
-/

namespace RHTower.Sieve.StadlmannEquidistributionParameters

open StadlmannBoundedGaps

noncomputable section

/-- Auxiliary width for Lemma 5 below the half exponent. -/
def typeILowDeltaStar (omega gamma epsilon : ℝ) : ℝ :=
  gamma - 4 * omega - 1 / 3 - epsilon

/-- Auxiliary width for Lemma 5 above the half exponent. -/
def typeIHighDeltaStar (omega epsilon : ℝ) : ℝ :=
  1 / 14 - 68 * omega / 14 - epsilon

/-- Auxiliary width for Lemma 3 (Type IIa). -/
def typeIIaDeltaStar (omega gamma epsilon : ℝ) : ℝ :=
  5 * gamma / 7 - 2 / 7 - 24 * omega / 7 - epsilon

/-- Auxiliary width for Lemma 4 (Type IIb). -/
def typeIIbDeltaStar (omega gamma epsilon : ℝ) : ℝ :=
  3 * gamma / 7 - 1 / 7 - 24 * omega / 7 - epsilon

/-- Auxiliary width for Lemma 7 (Type III). -/
def typeIIIDeltaStar (omega xiThree epsilon : ℝ) : ℝ :=
  1 / 2 - 7 * omega / 2 - 9 * xiThree / 8 - epsilon

/-- Lemma 5's low-exponent inequality is automatic for the paper's chosen `δ*`. -/
theorem typeILowDeltaStar_permissible
    {omega gamma epsilon : ℝ} (hepsilon : 0 < epsilon) :
    1 < 3 * gamma - 12 * omega - 3 * typeILowDeltaStar omega gamma epsilon := by
  simp [typeILowDeltaStar]
  linarith

/-- Lemma 5's high-exponent inequality is automatic for the paper's chosen `δ*`. -/
theorem typeIHighDeltaStar_permissible
    {omega epsilon : ℝ} (hepsilon : 0 < epsilon) :
    68 * omega + 14 * typeIHighDeltaStar omega epsilon < 1 := by
  simp [typeIHighDeltaStar]
  linarith

/-- Common range data for the Type II applications. -/
structure TypeIIRangeData where
  omega : ℝ
  gamma : ℝ
  epsilon : ℝ
  omega_nonneg : 0 ≤ omega
  gamma_le_half : gamma ≤ 1 / 2
  epsilon_pos : 0 < epsilon

/-- Lemma 3's two parameter inequalities for the paper's Type-IIa width. -/
theorem TypeIIRangeData.typeIIa_permissible (D : TypeIIRangeData) :
    24 * D.omega + 7 * typeIIaDeltaStar D.omega D.gamma D.epsilon -
          5 * D.gamma < -2 ∧
      8 * D.omega + 3 * typeIIaDeltaStar D.omega D.gamma D.epsilon -
          D.gamma < 0 := by
  constructor
  · simp [typeIIaDeltaStar]
    linarith [D.epsilon_pos]
  · simp [typeIIaDeltaStar]
    linarith [D.omega_nonneg, D.gamma_le_half, D.epsilon_pos]

/-- Lemma 4's two parameter inequalities for the paper's Type-IIb width. -/
theorem TypeIIRangeData.typeIIb_permissible (D : TypeIIRangeData) :
    24 * D.omega + 7 * typeIIbDeltaStar D.omega D.gamma D.epsilon -
          3 * D.gamma < -1 ∧
      8 * D.omega + 3 * typeIIbDeltaStar D.omega D.gamma D.epsilon -
          D.gamma < 0 := by
  constructor
  · simp [typeIIbDeltaStar]
    linarith [D.epsilon_pos]
  · simp [typeIIbDeltaStar]
    linarith [D.omega_nonneg, D.gamma_le_half, D.epsilon_pos]

/-- Upper-envelope data used to invoke Lemma 6 (Type IIc). -/
structure TypeIIcUpperData where
  omega : ℝ
  gamma : ℝ
  deltaStar : ℝ
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  first_upper :
    deltaStar ≤ 1 / 4 - 2 * omega - gamma / 2 - epsilon
  second_upper :
    deltaStar ≤ gamma / 10 - 32 * omega / 10 - epsilon
  third_upper :
    deltaStar ≤ gamma / 4 - 1 / 16 - 3 * omega - epsilon

/-- Lemma 6's three strict inequalities follow from its three upper envelopes. -/
theorem TypeIIcUpperData.permissible (D : TypeIIcUpperData) :
    8 * D.omega + 4 * D.deltaStar + 2 * D.gamma < 1 ∧
      32 * D.omega + 10 * D.deltaStar - D.gamma < 0 ∧
      48 * D.omega + 16 * D.deltaStar - 4 * D.gamma < -1 := by
  constructor
  · linarith [D.first_upper, D.epsilon_pos]
  constructor
  · linarith [D.second_upper, D.epsilon_pos]
  · linarith [D.third_upper, D.epsilon_pos]

/-- Lemma 7's Type-III inequality is automatic for its chosen `δ*`. -/
theorem typeIIIDeltaStar_permissible
    {omega xiThree epsilon : ℝ} (hepsilon : 0 < epsilon) :
    28 * omega + 9 * xiThree + 8 * typeIIIDeltaStar omega xiThree epsilon < 4 := by
  simp [typeIIIDeltaStar]
  linarith

/-- Lowest Type-IIa exponent used by Proposition 3. -/
def typeIIaGammaStart (omega delta epsilon : ℝ) : ℝ :=
  2 / 5 + 24 * omega / 5 + 7 * delta / 5 + 2 * epsilon

/-- Lowest Type-IIb exponent used by Proposition 3. -/
def typeIIbGammaStart (omega delta epsilon : ℝ) : ℝ :=
  1 / 3 + 24 * omega / 3 + 7 * delta / 3 + 3 * epsilon

/-- At the Type-IIa transition, the auxiliary width has a strict `3ε/7` surplus. -/
theorem typeIIaDeltaStar_at_start (omega delta epsilon : ℝ) :
    typeIIaDeltaStar omega (typeIIaGammaStart omega delta epsilon) epsilon =
      delta + 3 * epsilon / 7 := by
  simp [typeIIaDeltaStar, typeIIaGammaStart]
  ring

/-- At the Type-IIb transition, the auxiliary width has a strict `2ε/7` surplus. -/
theorem typeIIbDeltaStar_at_start (omega delta epsilon : ℝ) :
    typeIIbDeltaStar omega (typeIIbGammaStart omega delta epsilon) epsilon =
      delta + 2 * epsilon / 7 := by
  simp [typeIIbDeltaStar, typeIIbGammaStart]
  ring

/-- Final low Type-I exponent range. -/
structure FinalTypeILowScale where
  gamma : ℝ
  lower : xiOne - criterionEpsilon ≤ gamma
  upper : gamma ≤ 1 / 2

/-- The final low Type-I range invokes Lemma 5 with an auxiliary width at least `delta`. -/
theorem FinalTypeILowScale.certificate (D : FinalTypeILowScale) :
    delta ≤ typeILowDeltaStar omega D.gamma criterionEpsilon ∧
      1 < 3 * D.gamma - 12 * omega -
        3 * typeILowDeltaStar omega D.gamma criterionEpsilon := by
  constructor
  · have hlower := D.lower
    norm_num [typeILowDeltaStar, delta, omega, supportEndpoint, xiOne,
      criterionEpsilon] at hlower ⊢
    linarith
  · exact typeILowDeltaStar_permissible (by norm_num [criterionEpsilon])

/-- Final high Type-I auxiliary width invokes Lemma 5 and remains above `delta`. -/
theorem finalTypeIHighCertificate :
    delta ≤ typeIHighDeltaStar omega criterionEpsilon ∧
      68 * omega + 14 * typeIHighDeltaStar omega criterionEpsilon < 1 := by
  constructor
  · norm_num [typeIHighDeltaStar, delta, omega, supportEndpoint, criterionEpsilon]
  · exact typeIHighDeltaStar_permissible (by norm_num [criterionEpsilon])

/-- Final Type-IIa exponent range. -/
structure FinalTypeIIaScale where
  gamma : ℝ
  lower : typeIIaGammaStart omega delta criterionEpsilon ≤ gamma
  upper : gamma ≤ 1 / 2

/-- Every final Type-IIa exponent invokes Lemma 3 with width at least `delta`. -/
theorem FinalTypeIIaScale.certificate (D : FinalTypeIIaScale) :
    delta ≤ typeIIaDeltaStar omega D.gamma criterionEpsilon ∧
      24 * omega + 7 * typeIIaDeltaStar omega D.gamma criterionEpsilon -
          5 * D.gamma < -2 ∧
      8 * omega + 3 * typeIIaDeltaStar omega D.gamma criterionEpsilon -
          D.gamma < 0 := by
  have hstart := typeIIaDeltaStar_at_start omega delta criterionEpsilon
  have hmono : typeIIaDeltaStar omega
      (typeIIaGammaStart omega delta criterionEpsilon) criterionEpsilon ≤
      typeIIaDeltaStar omega D.gamma criterionEpsilon := by
    simp [typeIIaDeltaStar]
    linarith [D.lower]
  have hwidth : delta ≤ typeIIaDeltaStar omega D.gamma criterionEpsilon := by
    rw [hstart] at hmono
    norm_num [criterionEpsilon] at hmono ⊢
    linarith
  let R : TypeIIRangeData :=
    { omega := omega
      gamma := D.gamma
      epsilon := criterionEpsilon
      omega_nonneg := by norm_num [omega, supportEndpoint]
      gamma_le_half := D.upper
      epsilon_pos := by norm_num [criterionEpsilon] }
  exact ⟨hwidth, R.typeIIa_permissible⟩

/-- Final Type-IIb exponent range. -/
structure FinalTypeIIbScale where
  gamma : ℝ
  lower : typeIIbGammaStart omega delta criterionEpsilon ≤ gamma
  upper : gamma ≤ 1 / 2

/-- Every final Type-IIb exponent invokes Lemma 4 with width at least `delta`. -/
theorem FinalTypeIIbScale.certificate (D : FinalTypeIIbScale) :
    delta ≤ typeIIbDeltaStar omega D.gamma criterionEpsilon ∧
      24 * omega + 7 * typeIIbDeltaStar omega D.gamma criterionEpsilon -
          3 * D.gamma < -1 ∧
      8 * omega + 3 * typeIIbDeltaStar omega D.gamma criterionEpsilon -
          D.gamma < 0 := by
  have hstart := typeIIbDeltaStar_at_start omega delta criterionEpsilon
  have hmono : typeIIbDeltaStar omega
      (typeIIbGammaStart omega delta criterionEpsilon) criterionEpsilon ≤
      typeIIbDeltaStar omega D.gamma criterionEpsilon := by
    simp [typeIIbDeltaStar]
    linarith [D.lower]
  have hwidth : delta ≤ typeIIbDeltaStar omega D.gamma criterionEpsilon := by
    rw [hstart] at hmono
    norm_num [criterionEpsilon] at hmono ⊢
    linarith
  let R : TypeIIRangeData :=
    { omega := omega
      gamma := D.gamma
      epsilon := criterionEpsilon
      omega_nonneg := by norm_num [omega, supportEndpoint]
      gamma_le_half := D.upper
      epsilon_pos := by norm_num [criterionEpsilon] }
  exact ⟨hwidth, R.typeIIb_permissible⟩

/-- Full final Type-IIc exponent range. -/
structure FinalTypeIIcScale where
  gamma : ℝ
  lower : xiTwo - criterionEpsilon ≤ gamma
  upper : gamma ≤
    1 / 3 + 24 * omega / 3 + 7 * delta / 3 + 3 * criterionEpsilon

/-- **Uniform final Lemma 6 application.**  The original `delta` itself satisfies all three
Type-IIc inequalities at every exponent in the final interval. -/
theorem FinalTypeIIcScale.certificate (D : FinalTypeIIcScale) :
    8 * omega + 4 * delta + 2 * D.gamma < 1 ∧
      32 * omega + 10 * delta - D.gamma < 0 ∧
      48 * omega + 16 * delta - 4 * D.gamma < -1 := by
  have hLower := D.lower
  have hUpper := D.upper
  norm_num [omega, supportEndpoint, delta, xiTwo, criterionEpsilon] at hLower hUpper ⊢
  constructor
  · linarith
  constructor <;> linarith

/-- Final Type-III auxiliary width invokes Lemma 7 and remains above `delta`. -/
theorem finalTypeIIICertificate :
    delta < typeIIIDeltaStar omega xiThree criterionEpsilon ∧
      28 * omega + 9 * xiThree +
        8 * typeIIIDeltaStar omega xiThree criterionEpsilon < 4 := by
  constructor
  · norm_num [typeIIIDeltaStar, delta, omega, supportEndpoint, xiThree,
      criterionEpsilon]
  · exact typeIIIDeltaStar_permissible (by norm_num [criterionEpsilon])

end

end RHTower.Sieve.StadlmannEquidistributionParameters
