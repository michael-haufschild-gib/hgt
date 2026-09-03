import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIGapSequence
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownDerivativeReceiver

/-!
# Menon's Case-II receiver on one finite color fibre

The selected Perron ordinates of one color are continued to a globally separated sequence.  This
module inserts that exact sequence and the normalized selected-core threshold into the literal
Heath--Brown Montgomery receivers.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- A long zeta color, whose selected factor lies above the ordinate height, is received by the
exact factor-excised Montgomery inequality on its complete color fibre. -/
theorem derivativeExcised_montgomery_menonHeathBrownCaseII_zeta_overHeight
    {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hX : 1 ≤ X) (hsigma : 0 ≤ sigma)
    (hΔ : 0 < Δ) (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (hbaseGap : ∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1))
    (hT : 0 < T) (hΔT : Δ / 2 ≤ T)
    (hbaseBand : ∀ r ∈ S, T + V ≤ tau r ∧ tau r ≤ 2 * T - V)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta)
    (hTN : T ≤
      (((2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)))
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q) :
    let F := menonHeathBrownCaseIIColorFibre S color label
    let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
      i ∈ (Finset.univ.erase label.factor)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
    let U : ℕ := groupedDyadicUpper q
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    (F.card : ℝ) *
        (((T / (6 * Real.pi + 1)) * menonHeathBrownCaseIICoreThreshold L X Q *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              (sigma - 1)) ^ 2) ≤
      (2 * T + Δ / 2 + 4 * (U : ℝ) * (1 + Real.log U)) *
        (1 / Δ + 2 * Real.log U) *
        (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
          ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  let F := menonHeathBrownCaseIIColorFibre S color label
  let lam := menonHeathBrownCaseIISelectedOrdinate
    S color selectedY tau V Δ label
  have hgap : ∀ r : ℕ, lam r + Δ ≤ lam (r + 1) := by
    exact menonHeathBrownCaseIISelectedOrdinate_gap hΔ hselection hbaseGap label
  have hordinate : ∀ r ∈ F, T ≤ lam r ∧ lam r ≤ 2 * T := by
    intro r hr
    exact menonHeathBrownCaseIISelectedOrdinate_mem_band
      hΔ hgrid hselection hbaseBand label r (Finset.mem_filter.mp hr).1
  have hband : ∀ r ∈ F, Δ / 2 ≤ lam r ∧ lam r + Δ / 2 ≤ 2 * T + Δ / 2 := by
    intro r hr
    have hrange := hordinate r hr
    constructor
    · exact hΔT.trans hrange.1
    · linarith
  have hlarge : ∀ r ∈ F,
      menonHeathBrownCaseIICoreThreshold L X Q ^ ((sigma + 1) - sigma) ≤
        ‖heathBrownDyadicCoreProduct L X 3 label.box.m
          label.box.a label.box.b label.box.q
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
    intro r hr
    simpa only [add_sub_cancel_left, Real.rpow_one] using
      menonHeathBrownCaseIICoreThreshold_le_on_colorFibre hselection label hr
  simpa only [F, lam, add_sub_cancel_left, Real.rpow_one] using
    (derivativeExcised_montgomery_heathBrownBox_zeta_overHeight
      label.box label.factor hkind hX hsigma hΔ
      (by positivity : 0 ≤ 2 * T + Δ / 2) hgap hband
      hthreshold hT hordinate hTN hlarge :
        let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
          i ∈ (Finset.univ.erase label.factor)}
        let q : I → ℕ := fun i =>
          heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
        let U : ℕ := groupedDyadicUpper q
        let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
        (F.card : ℝ) *
            (((T / (6 * Real.pi + 1)) *
              menonHeathBrownCaseIICoreThreshold L X Q ^ ((sigma + 1) - sigma) *
              (((2 ^ heathBrownBoxFactorExponent
                label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
                  (sigma - 1)) ^ 2) ≤
          (2 * T + Δ / 2 + 4 * (U : ℝ) * (1 + Real.log U)) *
            (1 / Δ + 2 * Real.log U) *
            (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
              ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)))

/-- The logarithm-factor branch has the identical color-fibre geometry, with its one literal
polylogarithmic envelope retained in the receiver constant. -/
theorem derivativeExcised_montgomery_menonHeathBrownCaseII_log_overHeight
    {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hX : 1 ≤ X) (hsigma : 0 ≤ sigma)
    (hΔ : 0 < Δ) (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (hbaseGap : ∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1))
    (hT : 0 < T) (hΔT : Δ / 2 ≤ T)
    (hbaseBand : ∀ r ∈ S, T + V ≤ tau r ∧ tau r ≤ 2 * T - V)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .log)
    (hTN : T ≤
      (((2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)))
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q) :
    let F := menonHeathBrownCaseIIColorFibre S color label
    let C := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
    let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
      i ∈ (Finset.univ.erase label.factor)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
    let U : ℕ := groupedDyadicUpper q
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    (F.card : ℝ) *
        (((T / C) * menonHeathBrownCaseIICoreThreshold L X Q *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              (sigma - 1)) ^ 2) ≤
      (2 * T + Δ / 2 + 4 * (U : ℝ) * (1 + Real.log U)) *
        (1 / Δ + 2 * Real.log U) *
        (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
          ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  let F := menonHeathBrownCaseIIColorFibre S color label
  let lam := menonHeathBrownCaseIISelectedOrdinate
    S color selectedY tau V Δ label
  have hgap : ∀ r : ℕ, lam r + Δ ≤ lam (r + 1) := by
    exact menonHeathBrownCaseIISelectedOrdinate_gap hΔ hselection hbaseGap label
  have hordinate : ∀ r ∈ F, T ≤ lam r ∧ lam r ≤ 2 * T := by
    intro r hr
    exact menonHeathBrownCaseIISelectedOrdinate_mem_band
      hΔ hgrid hselection hbaseBand label r (Finset.mem_filter.mp hr).1
  have hband : ∀ r ∈ F, Δ / 2 ≤ lam r ∧ lam r + Δ / 2 ≤ 2 * T + Δ / 2 := by
    intro r hr
    have hrange := hordinate r hr
    constructor
    · exact hΔT.trans hrange.1
    · linarith
  have hlarge : ∀ r ∈ F,
      menonHeathBrownCaseIICoreThreshold L X Q ^ ((sigma + 1) - sigma) ≤
        ‖heathBrownDyadicCoreProduct L X 3 label.box.m
          label.box.a label.box.b label.box.q
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
    intro r hr
    simpa only [add_sub_cancel_left, Real.rpow_one] using
      menonHeathBrownCaseIICoreThreshold_le_on_colorFibre hselection label hr
  simpa only [F, lam, add_sub_cancel_left, Real.rpow_one] using
    (derivativeExcised_montgomery_heathBrownBox_log_overHeight
      label.box label.factor hkind hX hsigma hΔ
      (by positivity : 0 ≤ 2 * T + Δ / 2) hgap hband
      hthreshold hT hordinate hTN hlarge :
        let C := 2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X
        let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
          i ∈ (Finset.univ.erase label.factor)}
        let q : I → ℕ := fun i =>
          heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
        let U : ℕ := groupedDyadicUpper q
        let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
        (F.card : ℝ) *
            (((T / C) *
              menonHeathBrownCaseIICoreThreshold L X Q ^ ((sigma + 1) - sigma) *
              (((2 ^ heathBrownBoxFactorExponent
                label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
                  (sigma - 1)) ^ 2) ≤
          (2 * T + Δ / 2 + 4 * (U : ℝ) * (1 + Real.log U)) *
            (1 / Δ + 2 * Real.log U) *
            (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
              ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)))

/-- In the complementary ordinate range, the same selected sequence feeds the derivative-defect
receiver.  Its factorial order, factor scale, and derivative window remain literal. -/
theorem derivativeExcised_montgomery_menonHeathBrownCaseII_derivativeDefect
    {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
    {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
    {selectedY tau : ℕ → ℝ}
    (hX : 1 ≤ X) (hsigma : 0 ≤ sigma)
    (hΔ : 0 < Δ) (hgrid : 2 * V = (cells : ℝ) * Δ)
    (hselection : ∀ r ∈ S,
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
        (selectedY r) (color r))
    (hbaseGap : ∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1))
    (hT : 0 < T) (hΔT : Δ / 2 ≤ T)
    (hbaseBand : ∀ r ∈ S, T + V ≤ tau r ∧ tau r ≤ 2 * T - V)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
      heathBrownBoxFactorKind 3 label.box.m label.factor = .log)
    {k0 : ℕ} (hk0 : 2 ≤ k0)
    (hfac : Nat.factorial (k0 - 1) ≤
      2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor)
    (hderivative : ∀ r ∈ menonHeathBrownCaseIIColorFibre S color label,
      let lam := menonHeathBrownCaseIISelectedOrdinate
        S color selectedY tau V Δ label r
      0 < lam ∧
      8 * Real.pi *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              ((1 : ℝ) / 3) ≤ lam ∧
      lam ≤ 2 * Real.pi * 2 ^ k0 *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              (k0 - 1) *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              (-(1 / 3) : ℝ))
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q) :
    let F := menonHeathBrownCaseIIColorFibre S color label
    let N : ℝ :=
      (((2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
    let C : ℝ := heathBrownDerivativeConstant X
      (heathBrownBoxFactorKind 3 label.box.m label.factor)
      (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q label.factor)
    let Tsave : ℝ := N ^ maynardDerivativeDeficit k0
    let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
      i ∈ (Finset.univ.erase label.factor)}
    let q : I → ℕ := fun i =>
      heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
    let U : ℕ := groupedDyadicUpper q
    let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
    (F.card : ℝ) *
        (((Tsave / C) * menonHeathBrownCaseIICoreThreshold L X Q *
          N ^ (sigma - 1)) ^ 2) ≤
      (2 * T + Δ / 2 + 4 * (U : ℝ) * (1 + Real.log U)) *
        (1 / Δ + 2 * Real.log U) *
        (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
          ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)) := by
  let F := menonHeathBrownCaseIIColorFibre S color label
  let lam := menonHeathBrownCaseIISelectedOrdinate
    S color selectedY tau V Δ label
  have hgap : ∀ r : ℕ, lam r + Δ ≤ lam (r + 1) := by
    exact menonHeathBrownCaseIISelectedOrdinate_gap hΔ hselection hbaseGap label
  have hordinate : ∀ r ∈ F, T ≤ lam r ∧ lam r ≤ 2 * T := by
    intro r hr
    exact menonHeathBrownCaseIISelectedOrdinate_mem_band
      hΔ hgrid hselection hbaseBand label r (Finset.mem_filter.mp hr).1
  have hband : ∀ r ∈ F, Δ / 2 ≤ lam r ∧ lam r + Δ / 2 ≤ 2 * T + Δ / 2 := by
    intro r hr
    have hrange := hordinate r hr
    constructor
    · exact hΔT.trans hrange.1
    · linarith
  have hlarge : ∀ r ∈ F,
      menonHeathBrownCaseIICoreThreshold L X Q ^ ((sigma + 1) - sigma) ≤
        ‖heathBrownDyadicCoreProduct L X 3 label.box.m
          label.box.a label.box.b label.box.q
          ((sigma : ℂ) + (lam r : ℝ) * Complex.I)‖ := by
    intro r hr
    simpa only [add_sub_cancel_left, Real.rpow_one] using
      menonHeathBrownCaseIICoreThreshold_le_on_colorFibre hselection label hr
  have hderivative' : ∀ r ∈ F,
      0 < lam r ∧
      8 * Real.pi *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              ((1 : ℝ) / 3) ≤ lam r ∧
      lam r ≤ 2 * Real.pi * 2 ^ k0 *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              (k0 - 1) *
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^
              (-(1 / 3) : ℝ) := by
    intro r hr
    simpa only [lam] using hderivative r hr
  simpa only [F, lam, add_sub_cancel_left, Real.rpow_one] using
    (derivativeExcised_montgomery_heathBrownBox_derivativeDefect
      label.box label.factor hkind hX hsigma hΔ
      (by positivity : 0 ≤ 2 * T + Δ / 2) hgap hband
      hthreshold hk0 hfac hderivative' hlarge :
        let N : ℝ :=
          (((2 ^ heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
        let C : ℝ := heathBrownDerivativeConstant X
          (heathBrownBoxFactorKind 3 label.box.m label.factor)
          (heathBrownBoxFactorExponent
            label.box.a label.box.b label.box.q label.factor)
        let Tsave : ℝ := N ^ maynardDerivativeDeficit k0
        let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
          i ∈ (Finset.univ.erase label.factor)}
        let q : I → ℕ := fun i =>
          heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
        let U : ℕ := groupedDyadicUpper q
        let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
        (F.card : ℝ) *
            (((Tsave / C) *
              menonHeathBrownCaseIICoreThreshold L X Q ^ ((sigma + 1) - sigma) *
              N ^ (sigma - 1)) ^ 2) ≤
          (2 * T + Δ / 2 + 4 * (U : ℝ) * (1 + Real.log U)) *
            (1 / Δ + 2 * Real.log U) *
            (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
              ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E)))

end RHTower.Sieve
