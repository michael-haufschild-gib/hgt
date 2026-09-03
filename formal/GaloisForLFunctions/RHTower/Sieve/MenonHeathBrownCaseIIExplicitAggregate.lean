import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIUniformAggregate

/-!
# Explicit fixed-polylogarithm Case-II aggregate

The degree-three Heath--Brown box count and the full Case-II label count are replaced by their
literal fixed-polylogarithm majorants.  The second theorem also invokes the already proved
exhaustive receiver theorem internally, so no receiver alternative remains among its inputs.
-/

namespace RHTower.Sieve

noncomputable section

open Filter

/-- Explicit Case-II aggregation after paying every degree-three box and label. -/
theorem card_mul_sq_le_menonHeathBrownCaseII_explicit
    {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
    (S : Finset ℕ) (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    {selectedY tau : ℕ → ℝ}
    (ha : 1 ≤ a) (hX : 1 ≤ X) (hT : 1 ≤ T) (hΔ : 1 ≤ Δ) (hΔT : Δ / 2 ≤ T)
    (hQ : 0 < Q)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (hactive : ∀ label : MenonHeathBrownCaseIILabel L X cells,
      (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
        heathBrownBoxFactorKind 3 label.box.m label.factor = .log) ∧
      ((heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
          MenonHeathBrownCaseIIZetaOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
          MenonHeathBrownCaseIILogOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        MenonHeathBrownCaseIIDerivativeTwentySixBound
          L X cells S color sigma Δ Q T label))
    (hsigma : 1 ≤ sigma) :
    let D : ℕ :=
      3 * (Nat.log 2 X + 1) ^ 3 * (Nat.log 2 L + 1) ^ 3
    let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
    let Vexp : ℝ :=
      min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
    let Hmax : ℝ :=
      (12 * W ^ 2 *
          (1 + Real.log (W * (X : ℝ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
    (S.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  let D : ℕ :=
    3 * (Nat.log 2 X + 1) ^ 3 * (Nat.log 2 L + 1) ^ 3
  let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
  let Vexp : ℝ :=
    min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
  let Vraw : ℝ :=
    min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope X) *
      menonHeathBrownCaseIICoreThreshold L X Q
  let Hmax : ℝ :=
    (12 * W ^ 2 *
        (1 + Real.log (W * (X : ℝ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
  let C : ℕ := Fintype.card (HeathBrownBoxChoice L X 3)
  letI : Nonempty (HeathBrownBoxChoice L X 3) :=
    nonempty_heathBrownBoxChoice L X 3 (by norm_num)
  have hCposNat : 0 < C := by
    dsimp only [C]
    exact Fintype.card_pos
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast hCposNat
  have hDposNat : 0 < D := by
    dsimp only [D]
    positivity
  have hDpos : 0 < (D : ℝ) := by exact_mod_cast hDposNat
  have hCDNat : C ≤ D := by
    dsimp only [C, D]
    simpa only [Nat.reduceMul] using card_heathBrownBoxChoice_le L X 3
  have hCD : (C : ℝ) ≤ (D : ℝ) := by exact_mod_cast hCDNat
  have hcorePos : 0 < menonHeathBrownCaseIICoreThreshold L X Q := by
    rw [menonHeathBrownCaseIICoreThreshold]
    dsimp only [C] at hCpos ⊢
    positivity
  have hcoreLower : Q / ((D : ℝ) * 8) ≤
      menonHeathBrownCaseIICoreThreshold L X Q := by
    rw [menonHeathBrownCaseIICoreThreshold]
    dsimp only [C] at hCpos hCD ⊢
    exact div_le_div_of_nonneg_left hQ.le (by positivity)
      (mul_le_mul_of_nonneg_right hCD (by norm_num))
  have hprefix : 0 ≤
      min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope X) := by
    have hgain : 0 ≤ ((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26 :=
      Real.rpow_nonneg (by positivity) _
    have henv := one_le_maynardLongPolylogEnvelope X
    positivity
  have hVV : Vexp ≤ Vraw := by
    dsimp only [Vexp, Vraw]
    exact mul_le_mul_of_nonneg_left hcoreLower hprefix
  have hVexp : 0 ≤ Vexp := by
    dsimp only [Vexp]
    positivity
  have hsq : Vexp ^ 2 ≤ Vraw ^ 2 := pow_le_pow_left₀ hVexp hVV 2
  have hraw := card_mul_sq_le_menonHeathBrownCaseII_uniform
    S color ha hX hT hΔ hΔT hcorePos hselection hactive hsigma
  have hraw' : (S.card : ℝ) * Vraw ^ 2 ≤
      (Fintype.card (MenonHeathBrownCaseIILabel L X cells) : ℝ) * Hmax := by
    simpa only [Vraw, Hmax, W] using hraw
  have hlabelNat : Fintype.card (MenonHeathBrownCaseIILabel L X cells) ≤
      cells * D * 12 := by
    exact (card_menonHeathBrownCaseIILabel_le L X cells).trans
      (Nat.mul_le_mul_right 12 (Nat.mul_le_mul_left cells hCDNat))
  have hlabel : (Fintype.card (MenonHeathBrownCaseIILabel L X cells) : ℝ) ≤
      (((cells * D * 12 : ℕ) : ℝ)) := by exact_mod_cast hlabelNat
  have hHmax : 0 ≤ Hmax := by
    dsimp only [Hmax, W]
    have hWR : 1 ≤ menonHeathBrownCaseIIComplementWidthConstant := by
      norm_num [menonHeathBrownCaseIIComplementWidthConstant]
    have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have hlog : 0 ≤ Real.log
        (menonHeathBrownCaseIIComplementWidthConstant * (X : ℝ)) :=
      Real.log_nonneg (one_le_mul_of_one_le_of_one_le hWR hXR)
    positivity
  exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans
    (hraw'.trans (mul_le_mul_of_nonneg_right hlabel hHmax))

/-- After the selected-factor exponent is sufficiently large, the exhaustive receiver theorem
discharges every active-color alternative and yields the explicit aggregate directly. -/
theorem eventually_card_mul_sq_le_menonHeathBrownCaseII_explicit
    (A : ℝ) :
    ∀ᶠ a : ℕ in atTop,
      ∀ {L X cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
        {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
        {selectedY tau : ℕ → ℝ},
      1 ≤ L → 1 ≤ X → 1 ≤ sigma →
      1 ≤ Δ → 2 * V = (cells : ℝ) * Δ →
      (∀ r ∈ S,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
          (selectedY r) (color r)) →
      (∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1)) →
      1 ≤ T → Δ / 2 ≤ T →
      (∀ r ∈ S, T + V ≤ tau r ∧ tau r ≤ 2 * T - V) →
      (∀ label : MenonHeathBrownCaseIILabel L X cells,
        (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
        ∀ r ∈ menonHeathBrownCaseIIColorFibre S color label,
          |selectedY r + tau r| ≤ (a : ℝ) ^ (3 : ℕ)) →
      (∀ label : MenonHeathBrownCaseIILabel L X cells,
        (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
        (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) * 8 *
            (((groupedDyadicLower
              (heathBrownBoxFactorExponent
                label.box.a label.box.b label.box.q) : ℕ) : ℝ) ^ (1 - sigma) *
              (Real.log (((2 ^ heathBrownBoxFactorExponent
                label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))) ^ (-A) *
                maynardLongPolylogEnvelope X) < Q) →
      0 < Q →
      let D : ℕ :=
        3 * (Nat.log 2 X + 1) ^ 3 * (Nat.log 2 L + 1) ^ 3
      let W : ℝ := menonHeathBrownCaseIIComplementWidthConstant
      let Vexp : ℝ :=
        min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
            (5120 * maynardLongPolylogEnvelope X) * (Q / ((D : ℝ) * 8))
      let Hmax : ℝ :=
        (12 * W ^ 2 *
            (1 + Real.log (W * (X : ℝ))) ^
              (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
          (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
      (S.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨qmin, hqmin⟩ :=
    Filter.eventually_atTop.mp (eventually_menonHeathBrownCaseII_nonempty_fibre_receiver A)
  filter_upwards [eventually_ge_atTop (2 ^ (8 * qmin))] with a hamin
  intro L X cells T0 t sigma V Δ Q T S color selectedY tau hL hX hsigma hΔ hgrid
    hselection hbaseGap hT hΔT hbaseBand hfrequency habsorb hQ
  have ha : 1 ≤ a := (Nat.one_le_two_pow).trans hamin
  letI : Nonempty (HeathBrownBoxChoice L X 3) :=
    nonempty_heathBrownBoxChoice L X 3 (by norm_num)
  have hboxCard : 0 < (Fintype.card (HeathBrownBoxChoice L X 3) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (HeathBrownBoxChoice L X 3))
  have hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q := by
    rw [menonHeathBrownCaseIICoreThreshold]
    positivity
  have hactive : ∀ label : MenonHeathBrownCaseIILabel L X cells,
      (menonHeathBrownCaseIIColorFibre S color label).Nonempty →
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
        heathBrownBoxFactorKind 3 label.box.m label.factor = .log) ∧
      ((heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
          MenonHeathBrownCaseIIZetaOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
          MenonHeathBrownCaseIILogOverHeightBound
            L X cells S color sigma Δ Q T label) ∨
        MenonHeathBrownCaseIIDerivativeTwentySixBound
          L X cells S color sigma Δ Q T label) := by
    intro label hnonempty
    obtain ⟨r0, hr0⟩ := hnonempty
    have hnonempty' : (menonHeathBrownCaseIIColorFibre S color label).Nonempty :=
      ⟨r0, hr0⟩
    have hselected0 := isMenonHeathBrownCaseIISelection_on_colorFibre
      hselection label hr0
    have hq : qmin ≤ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor :=
      menonHeathBrownCaseIISelection_factorExponent_ge ha hamin hselected0
    exact hqmin _ hq ha hL hX hsigma (lt_of_lt_of_le zero_lt_one hΔ) hgrid
      hselection hbaseGap (lt_of_lt_of_le zero_lt_one hT) hΔT hbaseBand label rfl
      (hfrequency label hnonempty') (habsorb label hnonempty') hthreshold hnonempty'
  exact card_mul_sq_le_menonHeathBrownCaseII_explicit
    S color ha hX hT hΔ hΔT hQ hselection hactive hsigma

end

end RHTower.Sieve
