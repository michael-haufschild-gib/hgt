import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIFibreReceiver
import GaloisForLFunctions.RHTower.Sieve.MaynardColorFiberCounting

/-!
# Aggregating Menon's Case-II color receivers

The zeta, logarithm, and fixed-order derivative alternatives have one common complementary
Montgomery energy.  This module records their literal amplitudes and converts the exhaustive
receiver alternative into one branch-independent bound on a color fibre.
-/

noncomputable section

namespace RHTower.Sieve

open Filter Finset

/-- An eighth-power natural cutoff becomes the corresponding eighth-root real cutoff. -/
theorem two_pow_le_rpow_oneEighth_of_eight_mul_exponent_pow_le
    {a q0 : ℕ} (h : 2 ^ (8 * q0) ≤ a) :
    (((2 ^ q0 : ℕ) : ℝ)) ≤ (a : ℝ) ^ (1 / 8 : ℝ) := by
  have hcast : (((2 ^ (8 * q0) : ℕ) : ℝ)) ≤ (a : ℝ) := by
    exact_mod_cast h
  have hrpow := Real.rpow_le_rpow
    (by positivity : (0 : ℝ) ≤ ((2 ^ (8 * q0) : ℕ) : ℝ))
    hcast (by norm_num : (0 : ℝ) ≤ 1 / 8)
  calc
    (((2 ^ q0 : ℕ) : ℝ)) = (2 : ℝ) ^ (q0 : ℕ) := by norm_num
    _ = (2 : ℝ) ^ (q0 : ℝ) := (Real.rpow_natCast 2 q0).symm
    _ = (2 : ℝ) ^ (((8 * q0 : ℕ) : ℝ) * (1 / 8 : ℝ)) := by
      congr 1
      push_cast
      ring
    _ = ((2 : ℝ) ^ ((8 * q0 : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by
      rw [Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2)]
    _ = (((2 : ℝ) ^ (8 * q0 : ℕ))) ^ (1 / 8 : ℝ) := by
      rw [Real.rpow_natCast]
    _ = (((2 ^ (8 * q0) : ℕ) : ℝ)) ^ (1 / 8 : ℝ) := by norm_num
    _ ≤ (a : ℝ) ^ (1 / 8 : ℝ) := hrpow

/-- Every selected factor lies beyond a fixed dyadic exponent once the ambient scale passes the
corresponding eighth power.  The statement is uniform in the medium/long branch. -/
theorem menonHeathBrownCaseIISelection_factorExponent_ge
    {L X a cells q0 : ℕ} {T0 t sigma tau V Δ Q y : ℝ}
    {label : MenonHeathBrownCaseIILabel L X cells}
    (ha : 1 ≤ a) (hlarge : 2 ^ (8 * q0) ≤ a)
    (hselection :
      IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma tau V Δ Q y label) :
    q0 ≤ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor := by
  let q := heathBrownBoxFactorExponent
    label.box.a label.box.b label.box.q label.factor
  have hroot : (((2 ^ q0 : ℕ) : ℝ)) ≤ (a : ℝ) ^ (1 / 8 : ℝ) :=
    two_pow_le_rpow_oneEighth_of_eight_mul_exponent_pow_le hlarge
  have hfactor : (a : ℝ) ^ (1 / 8 : ℝ) ≤ (((2 ^ q : ℕ) : ℝ)) := by
    cases hlong : label.isLong with
    | false =>
        have hbranch := hselection.2.2.2.2.2
        simp only [hlong, Bool.false_eq_true, ↓reduceIte] at hbranch
        exact hbranch.1
    | true =>
        have hbranch := hselection.2.2.2.2.2
        simp only [hlong, ↓reduceIte] at hbranch
        have haReal : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
        have hexponents : (1 / 8 : ℝ) ≤ 1 / 3 := by norm_num
        exact (Real.rpow_le_rpow_of_exponent_le haReal hexponents).trans hbranch.1.le
  have hpowsReal : (((2 ^ q0 : ℕ) : ℝ)) ≤ (((2 ^ q : ℕ) : ℝ)) :=
    hroot.trans hfactor
  have hpowsNat : 2 ^ q0 ≤ 2 ^ q := by exact_mod_cast hpowsReal
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpowsNat

/-- Literal left-hand amplitude in the zeta over-height receiver. -/
def menonHeathBrownCaseIIZetaAmplitude
    {cells : ℕ} (L X : ℕ) (sigma Q T : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  (T / (6 * Real.pi + 1)) * menonHeathBrownCaseIICoreThreshold L X Q *
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^ (sigma - 1)

/-- Literal left-hand amplitude in the logarithm over-height receiver. -/
def menonHeathBrownCaseIILogAmplitude
    {cells : ℕ} (L X : ℕ) (sigma Q T : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  (T / (2 * (6 * Real.pi + 1) * maynardLongPolylogEnvelope X)) *
    menonHeathBrownCaseIICoreThreshold L X Q *
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ)) ^ (sigma - 1)

/-- Literal left-hand amplitude in the fixed-order derivative receiver. -/
def menonHeathBrownCaseIIDerivativeTwentySixAmplitude
    {cells : ℕ} (L X : ℕ) (sigma Q : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind 3 label.box.m label.factor)
    (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q label.factor)
  (N ^ maynardDerivativeDeficit 26 / C) * menonHeathBrownCaseIICoreThreshold L X Q *
    N ^ (sigma - 1)

/-- Common complementary Montgomery energy on the right of all three Case-II receivers. -/
def menonHeathBrownCaseIIReceiverUpper
    {cells : ℕ} (L X : ℕ) (sigma Δ T : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  let I := {i : HeathBrownBoxFactorIndex 3 label.box.m //
    i ∈ (Finset.univ.erase label.factor)}
  let q : I → ℕ := fun i =>
    heathBrownBoxFactorExponent label.box.a label.box.b label.box.q i
  let U : ℕ := groupedDyadicUpper q
  let E : ℕ := 2 * Fintype.card I + (2 ^ (2 * Fintype.card I) - 1)
  (2 * T + Δ / 2 + 4 * (U : ℝ) * (1 + Real.log U)) *
    (1 / Δ + 2 * Real.log U) *
    (((groupedDyadicLower q : ℝ) ^ (-sigma)) ^ 2 *
      ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E))

/-- Smallest of the three literal Case-II receiver amplitudes. -/
def menonHeathBrownCaseIIReceiverAmplitude
    {cells : ℕ} (L X : ℕ) (sigma Q T : ℝ)
    (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  min
    (menonHeathBrownCaseIIZetaAmplitude L X sigma Q T label)
    (min (menonHeathBrownCaseIILogAmplitude L X sigma Q T label)
      (menonHeathBrownCaseIIDerivativeTwentySixAmplitude L X sigma Q label))

/-- The common Case-II receiver amplitude is positive for either surviving factor kind. -/
theorem menonHeathBrownCaseIIReceiverAmplitude_pos
    {L X cells : ℕ} {sigma Q T : ℝ}
    (hX : 1 ≤ X) (hT : 0 < T)
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q)
    (label : MenonHeathBrownCaseIILabel L X cells)
    (hkind : heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
      heathBrownBoxFactorKind 3 label.box.m label.factor = .log) :
    0 < menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  have hN : 0 < N := by positivity
  have hzeta : 0 < menonHeathBrownCaseIIZetaAmplitude L X sigma Q T label := by
    dsimp only [menonHeathBrownCaseIIZetaAmplitude]
    positivity
  have hlogEnvelope : 0 < maynardLongPolylogEnvelope X :=
    lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope X)
  have hlog : 0 < menonHeathBrownCaseIILogAmplitude L X sigma Q T label := by
    dsimp only [menonHeathBrownCaseIILogAmplitude]
    positivity
  have hC : 0 < heathBrownDerivativeConstant X
      (heathBrownBoxFactorKind 3 label.box.m label.factor)
      (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q label.factor) :=
    heathBrownDerivativeConstant_pos_of_zeta_or_log _ _ hX hkind
  have hderivative : 0 <
      menonHeathBrownCaseIIDerivativeTwentySixAmplitude L X sigma Q label := by
    dsimp only [menonHeathBrownCaseIIDerivativeTwentySixAmplitude]
    positivity
  rw [menonHeathBrownCaseIIReceiverAmplitude]
  exact lt_min hzeta (lt_min hlog hderivative)

/-- Every literal receiver alternative controls the fibre with the smallest receiver amplitude. -/
theorem menonHeathBrownCaseII_receiverAlternative_fibreBound
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
        (menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label) ^ 2 ≤
      menonHeathBrownCaseIIReceiverUpper L X sigma Δ T label := by
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  have hmin := menonHeathBrownCaseIIReceiverAmplitude_pos
    (sigma := sigma) hX hT hthreshold label hkind
  rcases hreceiver with hzetaBound | hlogBound | hderivativeBound
  · have hamp : menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label ≤
        (T / (6 * Real.pi + 1)) * menonHeathBrownCaseIICoreThreshold L X Q *
          N ^ (sigma - 1) := by
      exact min_le_left _ _
    have hsq := pow_le_pow_left₀ hmin.le hamp 2
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans (by
      simpa only [MenonHeathBrownCaseIIZetaOverHeightBound,
        menonHeathBrownCaseIIReceiverUpper, N] using hzetaBound.2)
  · have hamp : menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label ≤
        menonHeathBrownCaseIILogAmplitude L X sigma Q T label := by
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hsq := pow_le_pow_left₀ hmin.le hamp 2
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans (by
      simpa only [MenonHeathBrownCaseIILogOverHeightBound,
        menonHeathBrownCaseIILogAmplitude, menonHeathBrownCaseIIReceiverUpper] using hlogBound.2)
  · have hamp : menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label ≤
        menonHeathBrownCaseIIDerivativeTwentySixAmplitude L X sigma Q label := by
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hsq := pow_le_pow_left₀ hmin.le hamp 2
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _)).trans (by
      simpa only [MenonHeathBrownCaseIIDerivativeTwentySixBound,
        menonHeathBrownCaseIIDerivativeTwentySixAmplitude,
        menonHeathBrownCaseIIReceiverUpper] using hderivativeBound)

/-- Empty colors receive unit amplitude; nonempty colors retain the exact smallest receiver
amplitude.  This removes irrelevant Möbius-labelled colors without weakening active colors. -/
noncomputable def menonHeathBrownCaseIIActiveAmplitude
    {L X cells : ℕ} (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (sigma Q T : ℝ) (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  if (menonHeathBrownCaseIIColorFibre S color label).Nonempty then
    menonHeathBrownCaseIIReceiverAmplitude L X sigma Q T label
  else 1

/-- Empty colors contribute zero energy; nonempty colors retain the literal complementary
Montgomery energy. -/
noncomputable def menonHeathBrownCaseIIActiveUpper
    {L X cells : ℕ} (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (sigma Δ T : ℝ) (label : MenonHeathBrownCaseIILabel L X cells) : ℝ :=
  if (menonHeathBrownCaseIIColorFibre S color label).Nonempty then
    menonHeathBrownCaseIIReceiverUpper L X sigma Δ T label
  else 0

/-- Exact summation of the three receiver branches over all active Case-II colors. -/
theorem card_le_sum_menonHeathBrownCaseII_activeReceiver
    {L X cells : ℕ} {sigma Δ Q T : ℝ}
    (S : Finset ℕ) (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (hX : 1 ≤ X) (hT : 0 < T)
    (hthreshold : 0 < menonHeathBrownCaseIICoreThreshold L X Q)
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
          L X cells S color sigma Δ Q T label)) :
    (S.card : ℝ) ≤
      ∑ label : MenonHeathBrownCaseIILabel L X cells,
        menonHeathBrownCaseIIActiveUpper S color sigma Δ T label /
          (menonHeathBrownCaseIIActiveAmplitude S color sigma Q T label) ^ 2 := by
  apply card_le_sum_div_sq_of_color_fibre_bounds S color
  · intro label
    by_cases hne : (menonHeathBrownCaseIIColorFibre S color label).Nonempty
    · rw [menonHeathBrownCaseIIActiveAmplitude, if_pos hne]
      exact menonHeathBrownCaseIIReceiverAmplitude_pos
        hX hT hthreshold label (hactive label hne).1
    · simp [menonHeathBrownCaseIIActiveAmplitude, hne]
  · intro label
    change ((menonHeathBrownCaseIIColorFibre S color label).card : ℝ) *
        (menonHeathBrownCaseIIActiveAmplitude S color sigma Q T label) ^ 2 ≤
      menonHeathBrownCaseIIActiveUpper S color sigma Δ T label
    by_cases hne : (menonHeathBrownCaseIIColorFibre S color label).Nonempty
    · rw [menonHeathBrownCaseIIActiveAmplitude, if_pos hne,
        menonHeathBrownCaseIIActiveUpper, if_pos hne]
      exact menonHeathBrownCaseII_receiverAlternative_fibreBound
        hX hT hthreshold label (hactive label hne).1 (hactive label hne).2
    · have hempty : menonHeathBrownCaseIIColorFibre S color label = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hne
      simp [menonHeathBrownCaseIIActiveAmplitude,
        menonHeathBrownCaseIIActiveUpper, hempty]

/-- The selected-factor lower edge makes the fixed receiver cutoff uniform across every active
color.  Consequently the exact three-branch receiver sum controls the whole exceptional set for
all sufficiently large ambient scales. -/
theorem eventually_card_le_sum_menonHeathBrownCaseII_activeReceiver
    (A : ℝ) :
    ∀ᶠ a : ℕ in atTop,
      ∀ {L X cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
        {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
        {selectedY tau : ℕ → ℝ},
      1 ≤ L → 1 ≤ X → 1 ≤ sigma →
      0 < Δ → 2 * V = (cells : ℝ) * Δ →
      (∀ r ∈ S,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
          (selectedY r) (color r)) →
      (∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1)) →
      0 < T → Δ / 2 ≤ T →
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
      0 < menonHeathBrownCaseIICoreThreshold L X Q →
      (S.card : ℝ) ≤
        ∑ label : MenonHeathBrownCaseIILabel L X cells,
          menonHeathBrownCaseIIActiveUpper S color sigma Δ T label /
            (menonHeathBrownCaseIIActiveAmplitude S color sigma Q T label) ^ 2 := by
  obtain ⟨qmin, hqmin⟩ :=
    Filter.eventually_atTop.mp (eventually_menonHeathBrownCaseII_nonempty_fibre_receiver A)
  filter_upwards [Filter.eventually_ge_atTop (2 ^ (8 * qmin))] with a hamin
  intro L X cells T0 t sigma V Δ Q T S color selectedY tau hL hX hsigma hΔ hgrid
    hselection hbaseGap hT hΔT hbaseBand hfrequency habsorb hthreshold
  have ha : 1 ≤ a := (Nat.one_le_two_pow).trans hamin
  apply card_le_sum_menonHeathBrownCaseII_activeReceiver S color hX hT hthreshold
  intro label hnonempty
  obtain ⟨r0, hr0⟩ := hnonempty
  have hnonempty' : (menonHeathBrownCaseIIColorFibre S color label).Nonempty :=
    ⟨r0, hr0⟩
  have hselected0 := isMenonHeathBrownCaseIISelection_on_colorFibre
    hselection label hr0
  have hq : qmin ≤ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor :=
    menonHeathBrownCaseIISelection_factorExponent_ge ha hamin hselected0
  exact hqmin _ hq ha hL hX hsigma hΔ hgrid hselection hbaseGap hT hΔT hbaseBand
    label rfl (hfrequency label hnonempty') (habsorb label hnonempty') hthreshold hnonempty'

end RHTower.Sieve
