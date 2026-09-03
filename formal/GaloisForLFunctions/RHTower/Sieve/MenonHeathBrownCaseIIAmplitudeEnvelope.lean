import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIComplementGeometry

/-!
# Uniform amplitude envelope for Menon's Case II

The zeta, logarithm, and fixed-order derivative receivers have different literal left-hand
amplitudes.  Their common quantitative content is the smaller of the frequency height and the
fixed derivative gain, divided by one explicit polylogarithmic envelope.  This module extracts
that common lower bound without discarding either gain.
-/

noncomputable section

namespace RHTower.Sieve

/-- Common quantitative lower envelope of all three literal Case-II receiver amplitudes. -/
def menonHeathBrownCaseIICommonAmplitude
    {cells : ℕ} (L X : ℕ) (sigma Q T : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  (min T (N ^ maynardDerivativeDeficit 26) /
      (5120 * maynardLongPolylogEnvelope X)) *
    menonHeathBrownCaseIICoreThreshold L X Q * N ^ (sigma - 1)

/-- The common envelope is positive whenever the original core threshold and height are
positive. -/
theorem menonHeathBrownCaseIICommonAmplitude_pos
    {L X cells : ℕ} {sigma Q T : ℝ}
    (hT : 0 < T)
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q)
    (label : MenonHeathBrownCaseIILabel L X cells) :
    0 < menonHeathBrownCaseIICommonAmplitude L X sigma Q T label := by
  dsimp only [menonHeathBrownCaseIICommonAmplitude]
  have hE : 0 < maynardLongPolylogEnvelope X :=
    lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
  positivity

/-- Every literal Case-II receiver amplitude dominates the common frequency/derivative
envelope.  The logarithmic factor and derivative-test constants are absorbed by the same
explicit `5120` polylogarithmic denominator. -/
theorem menonHeathBrownCaseIICommonAmplitude_le_receiverAmplitude
    {L X cells : ℕ} {sigma Q T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T)
    (hthreshold : 0 ≤ menonHeathBrownCaseIICoreThreshold L X Q)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
      heathBrownBoxFactorKind 3 label.box.m label.factor = .log) :
    menonHeathBrownCaseIICommonAmplitude L X sigma Q T label ≤
      menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  let E : ℝ := maynardLongPolylogEnvelope X
  let g : ℝ := min T (N ^ maynardDerivativeDeficit 26)
  let D : ℝ := 5120 * E
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind 3 label.box.m label.factor)
    (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q label.factor)
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have hE : 1 ≤ E := by
    dsimp only [E]
    exact one_le_maynardLongPolylogEnvelope X
  have hEpos : 0 < E := zero_lt_one.trans_le hE
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hgain : 0 < g := by
    dsimp only [g]
    exact lt_min hT (Real.rpow_pos_of_pos hN _)
  have hzetaConstant : 6 * Real.pi + 1 ≤ D := by
    have hpi := Real.pi_lt_four
    have hsmall : 6 * Real.pi + 1 ≤ (5120 : ℝ) := by linarith
    exact hsmall.trans (by
      dsimp only [D]
      nlinarith)
  have hlogConstant : 2 * (6 * Real.pi + 1) * E ≤ D := by
    have hpi := Real.pi_lt_four
    have hsmall : 2 * (6 * Real.pi + 1) ≤ (5120 : ℝ) := by linarith
    dsimp only [D]
    exact mul_le_mul_of_nonneg_right hsmall (zero_le_one.trans hE)
  have hderivativeConstant : C ≤ D := by
    dsimp only [C, D, E]
    exact heathBrownDerivativeConstant_le_polylogEnvelope
      label.box label.factor hkind hX
  have hCpos : 0 < C := by
    dsimp only [C]
    exact heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hzetaGain : g / D ≤ T / (6 * Real.pi + 1) := by
    exact div_le_div₀ hT.le (by exact min_le_left _ _) (by positivity) hzetaConstant
  have hlogGain : g / D ≤ T / (2 * (6 * Real.pi + 1) * E) := by
    exact div_le_div₀ hT.le (by exact min_le_left _ _) (by positivity) hlogConstant
  have hderivativeGain : g / D ≤ N ^ maynardDerivativeDeficit 26 / C := by
    exact div_le_div₀ (Real.rpow_nonneg hN.le _) (by exact min_le_right _ _) hCpos
      hderivativeConstant
  have hzeta : menonHeathBrownCaseIICommonAmplitude L X sigma Q T label ≤
      menonHeathBrownCaseIIZetaAmplitude L X sigma Q T label := by
    dsimp only [menonHeathBrownCaseIICommonAmplitude,
      menonHeathBrownCaseIIZetaAmplitude, N, E, g, D] at hzetaGain ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hzetaGain hthreshold)
      (Real.rpow_nonneg hN.le _)
  have hlog : menonHeathBrownCaseIICommonAmplitude L X sigma Q T label ≤
      menonHeathBrownCaseIILogAmplitude L X sigma Q T label := by
    dsimp only [menonHeathBrownCaseIICommonAmplitude,
      menonHeathBrownCaseIILogAmplitude, N, E, g, D] at hlogGain ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hlogGain hthreshold)
      (Real.rpow_nonneg hN.le _)
  have hderivative : menonHeathBrownCaseIICommonAmplitude L X sigma Q T label ≤
      menonHeathBrownCaseIIDerivativeTwentySixAmplitude L X sigma Q label := by
    dsimp only [menonHeathBrownCaseIICommonAmplitude,
      menonHeathBrownCaseIIDerivativeTwentySixAmplitude, N, E, g, D, C]
      at hderivativeGain ⊢
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hderivativeGain hthreshold)
      (Real.rpow_nonneg hN.le _)
  exact le_min hzeta (le_min hlog hderivative)

/-- Every exhaustive receiver alternative controls its color fibre with the common quantitative
amplitude, before any support geometry is simplified. -/
theorem menonHeathBrownCaseII_receiverAlternative_commonAmplitude_fibreBound
    {L X cells : ℕ} {sigma Δ Q T : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    (hX : 1 ≤ X) (hT : 0 < T)
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
      heathBrownBoxFactorKind 3 label.box.m label.factor = .log)
    (hreceiver :
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
        MenonHeathBrownCaseIIZetaOverHeightBound
          L X cells S color sigma Δ Q T label) ∨
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
        MenonHeathBrownCaseIILogOverHeightBound
          L X cells S color sigma Δ Q T label) ∨
      MenonHeathBrownCaseIIDerivativeTwentySixBound
        L X cells S color sigma Δ Q T label) :
    ((menonHeathBrownCaseIIColorFibre S color label).card : ℝ) *
        (menonHeathBrownCaseIICommonAmplitude L X sigma Q T label) ^ 2 ≤
      menonHeathBrownCaseIIReceiverUpper L X sigma Δ T label := by
  have hcommon : 0 < menonHeathBrownCaseIICommonAmplitude L X sigma Q T label :=
    menonHeathBrownCaseIICommonAmplitude_pos hT hthreshold label
  have hamplitude : menonHeathBrownCaseIICommonAmplitude L X sigma Q T label ≤
      menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label :=
    menonHeathBrownCaseIICommonAmplitude_le_receiverAmplitude
      hX hT hthreshold.le label hkind
  have hsquare : (menonHeathBrownCaseIICommonAmplitude L X sigma Q T label) ^ 2 ≤
      (menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label) ^ 2 :=
    pow_le_pow_left₀ hcommon.le hamplitude 2
  calc
    ((menonHeathBrownCaseIIColorFibre S color label).card : ℝ) *
          (menonHeathBrownCaseIICommonAmplitude L X sigma Q T label) ^ 2 ≤
        ((menonHeathBrownCaseIIColorFibre S color label).card : ℝ) *
          (menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ ≤ menonHeathBrownCaseIIReceiverUpper L X sigma Δ T label :=
      menonHeathBrownCaseII_receiverAlternative_fibreBound
        hX hT hthreshold label hkind hreceiver

/-- Window relevance turns the common-amplitude fibre count into the fixed degree-three
two-term Montgomery envelope.  Both complementary power savings remain literal. -/
theorem windowRelevant_menonHeathBrownCaseII_commonAmplitude_fibreBound
    {L X cells : ℕ} {a sigma Δ Q T : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    (hX : 1 ≤ X) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (hΔT : Δ / 2 ≤ T)
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hbox : IsHeathBrownBoxWindowRelevant a X 3 label.box)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
      heathBrownBoxFactorKind 3 label.box.m label.factor = .log)
    (hreceiver :
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
        MenonHeathBrownCaseIIZetaOverHeightBound
          L X cells S color sigma Δ Q T label) ∨
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
        MenonHeathBrownCaseIILogOverHeightBound
          L X cells S color sigma Δ Q T label) ∨
      MenonHeathBrownCaseIIDerivativeTwentySixBound
        L X cells S color sigma Δ Q T label) :
    let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
      i ∈ (Finset.univ.erase label.factor)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
    let A : ℝ := (groupedDyadicLower q : ℝ)
    let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
    ((menonHeathBrownCaseIIColorFibre S color label).card : ℝ) *
        (menonHeathBrownCaseIICommonAmplitude L X sigma Q T label) ^ 2 ≤
      (12 * W ^ 2 *
          (1 + Real.log (W * (X : ℝ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T * A ^ (1 - 2 * sigma) + A ^ (2 - 2 * sigma)) := by
  let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
    i ∈ (Finset.univ.erase label.factor)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
  let A : ℝ := (groupedDyadicLower q : ℝ)
  let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
  exact (menonHeathBrownCaseII_receiverAlternative_commonAmplitude_fibreBound
      hX (zero_lt_one.trans_le hT) hthreshold label hkind hreceiver).trans
    (by
      simpa only [I, q, A, W] using
        windowRelevant_menonHeathBrownCaseIIReceiverUpper_le_fixedPolylog
          label hbox hX hT hΔ hΔT)

end RHTower.Sieve
