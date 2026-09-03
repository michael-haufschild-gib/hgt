import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownCaseIIReceiver

/-!
# Exhaustive height split for Menon's selected Case-II factor

The polynomial frequency horizon is `N^24`.  At sufficiently late dyadic factor scales, fixed
derivative order `26` covers that entire horizon whenever the factor is not itself above height.
-/

noncomputable section

namespace RHTower.Sieve

open Filter

/-- Exact zeta over-height receiver proposition for one Case-II color. -/
def MenonHeathBrownCaseIIZetaOverHeightBound
    (L X cells : ℕ) (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (sigma Δ Q T : ℝ) (label : MenonHeathBrownCaseIILabel L X cells) : Prop :=
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
        ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E))

/-- Exact logarithm over-height receiver proposition for one Case-II color. -/
def MenonHeathBrownCaseIILogOverHeightBound
    (L X cells : ℕ) (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (sigma Δ Q T : ℝ) (label : MenonHeathBrownCaseIILabel L X cells) : Prop :=
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
        ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E))

/-- Exact fixed-order derivative receiver proposition for one Case-II color. -/
def MenonHeathBrownCaseIIDerivativeTwentySixBound
    (L X cells : ℕ) (S : Finset ℕ)
    (color : ℕ → MenonHeathBrownCaseIILabel L X cells)
    (sigma Δ Q T : ℝ) (label : MenonHeathBrownCaseIILabel L X cells) : Prop :=
  let F := menonHeathBrownCaseIIColorFibre S color label
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  let C : ℝ := heathBrownDerivativeConstant X
    (heathBrownBoxFactorKind 3 label.box.m label.factor)
    (heathBrownBoxFactorExponent label.box.a label.box.b label.box.q label.factor)
  let Tsave : ℝ := N ^ maynardDerivativeDeficit 26
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
        ((U : ℝ) * (1 + Real.log (U : ℝ)) ^ E))

/-- A sufficiently long dyadic factor both absorbs `25!` and dominates its one-third-power
derivative threshold. -/
theorem eventually_menonHeathBrown_derivativeOrderTwentySix_ready :
    ∀ᶠ q : ℕ in atTop,
      Nat.factorial 25 ≤ 2 ^ q ∧
      8 * Real.pi * (((2 ^ q : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤
        ((2 ^ q : ℕ) : ℝ) := by
  have hfac : ∀ᶠ q : ℕ in atTop, Nat.factorial 25 ≤ 2 ^ q :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)).eventually_ge_atTop _
  have htwoThird : Filter.Tendsto
      (fun q : ℕ => (((2 ^ q : ℕ) : ℝ)) ^ ((2 : ℝ) / 3))
      atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (tendsto_natCast_atTop_atTop.comp
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)))
  filter_upwards [hfac, htwoThird.eventually_ge_atTop (8 * Real.pi)] with q hfacq hpi
  refine ⟨hfacq, ?_⟩
  have hN : 0 < (((2 ^ q : ℕ) : ℝ)) := by positivity
  calc
    8 * Real.pi * (((2 ^ q : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) ≤
        (((2 ^ q : ℕ) : ℝ)) ^ ((2 : ℝ) / 3) *
          (((2 ^ q : ℕ) : ℝ)) ^ ((1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right hpi (Real.rpow_nonneg hN.le _)
    _ = (((2 ^ q : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hN]
      norm_num

/-- Fixed order `26` reaches every ordinate in the literal twenty-fourth-power horizon. -/
theorem pow_twentyFour_le_derivativeOrderTwentySix_upper
    {N : ℝ} (hN : 1 ≤ N) :
    N ^ (24 : ℕ) ≤
      2 * Real.pi * 2 ^ (26 : ℕ) * N ^ (26 - 1 : ℕ) * N ^ (-(1 / 3) : ℝ) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hexponent : (24 : ℝ) ≤ 25 + (-(1 / 3) : ℝ) := by norm_num
  have hpow : N ^ (24 : ℝ) ≤ N ^ (25 + (-(1 / 3) : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN hexponent
  have hconstant : 1 ≤ 2 * Real.pi * 2 ^ (26 : ℕ) := by
    have hpowTwo : (1 : ℝ) ≤ 2 ^ (26 : ℕ) := by norm_num
    nlinarith [Real.pi_gt_three]
  calc
    N ^ (24 : ℕ) = N ^ (24 : ℝ) := (Real.rpow_natCast N 24).symm
    _ ≤ N ^ (25 + (-(1 / 3) : ℝ)) := hpow
    _ = N ^ (25 : ℕ) * N ^ (-(1 / 3) : ℝ) := by
      rw [Real.rpow_add hN0]
      norm_num [Real.rpow_natCast]
    _ ≤ (2 * Real.pi * 2 ^ (26 : ℕ)) *
          (N ^ (25 : ℕ) * N ^ (-(1 / 3) : ℝ)) := by
      exact le_mul_of_one_le_left (by positivity) hconstant
    _ = 2 * Real.pi * 2 ^ (26 : ℕ) * N ^ (26 - 1 : ℕ) *
          N ^ (-(1 / 3) : ℝ) := by
      norm_num
      ring

/-- Above the ready factor scale, failure of the over-height branch forces the derivative-test
lower edge; the `N^24` horizon supplies the fixed-order upper edge. -/
theorem derivativeOrderTwentySix_range_of_not_overHeight
    {N T lam : ℝ}
    (hN : 1 ≤ N)
    (hready : 8 * Real.pi * N ^ ((1 : ℝ) / 3) ≤ N)
    (hnotOverHeight : ¬ T ≤ N)
    (hTlam : T ≤ lam) (hlam : 0 < lam)
    (hfrequency : |lam| ≤ N ^ (24 : ℕ)) :
    0 < lam ∧
      8 * Real.pi * N ^ ((1 : ℝ) / 3) ≤ lam ∧
      lam ≤ 2 * Real.pi * 2 ^ (26 : ℕ) * N ^ (26 - 1 : ℕ) *
        N ^ (-(1 / 3) : ℝ) := by
  have hNT : N ≤ T := le_of_not_ge hnotOverHeight
  refine ⟨hlam, hready.trans (hNT.trans hTlam), ?_⟩
  calc
    lam ≤ |lam| := le_abs_self lam
    _ ≤ N ^ (24 : ℕ) := hfrequency
    _ ≤ 2 * Real.pi * 2 ^ (26 : ℕ) * N ^ (26 - 1 : ℕ) *
        N ^ (-(1 / 3) : ℝ) := pow_twentyFour_le_derivativeOrderTwentySix_upper hN

/-- Every sufficiently late selected zeta/log color satisfies one of the two literal over-height
receivers or the fixed-order derivative receiver.  This is the exhaustive analytic Case-II split,
not a conditional choice of a preferred branch. -/
theorem eventually_menonHeathBrownCaseII_zetaLog_receiver
    : ∀ᶠ q0 : ℕ in atTop,
      ∀ {L X a cells : ℕ} {T0 t sigma V Δ Q T : ℝ}
        {S : Finset ℕ} {color : ℕ → MenonHeathBrownCaseIILabel L X cells}
        {selectedY tau : ℕ → ℝ},
      1 ≤ X → 0 ≤ sigma →
      0 < Δ → 2 * V = (cells : ℝ) * Δ →
      (∀ r ∈ S,
        IsMenonHeathBrownCaseIISelection L X a cells T0 t sigma (tau r) V Δ Q
          (selectedY r) (color r)) →
      (∀ r : ℕ, tau r + 2 * Δ ≤ tau (r + 1)) →
      0 < T → Δ / 2 ≤ T →
      (∀ r : ℕ, T + V ≤ tau r ∧ tau r ≤ 2 * T - V) →
      ∀ (label : MenonHeathBrownCaseIILabel L X cells),
      heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor = q0 →
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∨
        heathBrownBoxFactorKind 3 label.box.m label.factor = .log) →
      (∀ r ∈ menonHeathBrownCaseIIColorFibre S color label,
        let lam := menonHeathBrownCaseIISelectedOrdinate
          S color selectedY tau V Δ label r
        |lam| ≤ (((2 ^ q0 : ℕ) : ℝ)) ^ (24 : ℕ)) →
      0 < menonHeathBrownCaseIICoreThreshold L X Q →
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .zeta ∧
        MenonHeathBrownCaseIIZetaOverHeightBound L X cells S color sigma Δ Q T label) ∨
      (heathBrownBoxFactorKind 3 label.box.m label.factor = .log ∧
        MenonHeathBrownCaseIILogOverHeightBound L X cells S color sigma Δ Q T label) ∨
      MenonHeathBrownCaseIIDerivativeTwentySixBound
        L X cells S color sigma Δ Q T label := by
  filter_upwards [eventually_menonHeathBrown_derivativeOrderTwentySix_ready]
    with q0 hready
  intro L X a cells T0 t sigma V Δ Q T S color selectedY tau hX hsigma hΔ hgrid
    hselection hbaseGap hT hΔT hbaseBand label hexponent hkind hfrequency hthreshold
  let N : ℝ :=
    (((2 ^ heathBrownBoxFactorExponent
      label.box.a label.box.b label.box.q label.factor : ℕ) : ℝ))
  have hN : 1 ≤ N := by
    dsimp [N]
    have hNat : 1 ≤ 2 ^ heathBrownBoxFactorExponent
        label.box.a label.box.b label.box.q label.factor := Nat.one_le_two_pow
    exact_mod_cast hNat
  by_cases hoverHeight : T ≤ N
  · rcases hkind with hkind | hkind
    · left
      refine ⟨hkind, ?_⟩
      simpa only [MenonHeathBrownCaseIIZetaOverHeightBound] using
        derivativeExcised_montgomery_menonHeathBrownCaseII_zeta_overHeight
          hX hsigma hΔ hgrid hselection hbaseGap hT hΔT hbaseBand label hkind
            hoverHeight hthreshold
    · right; left
      refine ⟨hkind, ?_⟩
      simpa only [MenonHeathBrownCaseIILogOverHeightBound] using
        derivativeExcised_montgomery_menonHeathBrownCaseII_log_overHeight
          hX hsigma hΔ hgrid hselection hbaseGap hT hΔT hbaseBand label hkind
            hoverHeight hthreshold
  · right; right
    have hfac : Nat.factorial (26 - 1) ≤
        2 ^ heathBrownBoxFactorExponent
          label.box.a label.box.b label.box.q label.factor := by
      have hk : 26 - 1 = 25 := by omega
      rw [hk, hexponent]
      exact hready.1
    have hderivative : ∀ r ∈ menonHeathBrownCaseIIColorFibre S color label,
        let lam := menonHeathBrownCaseIISelectedOrdinate
          S color selectedY tau V Δ label r
        0 < lam ∧
        8 * Real.pi * N ^ ((1 : ℝ) / 3) ≤ lam ∧
        lam ≤ 2 * Real.pi * 2 ^ (26 : ℕ) * N ^ (26 - 1 : ℕ) *
          N ^ (-(1 / 3) : ℝ) := by
      intro r hr
      let lam := menonHeathBrownCaseIISelectedOrdinate
        S color selectedY tau V Δ label r
      have hrange := menonHeathBrownCaseIISelectedOrdinate_mem_band
        hΔ hgrid hselection hbaseBand label r
      have hlam : 0 < lam := hT.trans_le hrange.1
      have hfreq : |lam| ≤ N ^ (24 : ℕ) := by
        dsimp only [lam, N]
        simpa only [hexponent] using hfrequency r hr
      have hreadyN : 8 * Real.pi * N ^ ((1 : ℝ) / 3) ≤ N := by
        dsimp only [N]
        simpa only [hexponent] using hready.2
      exact derivativeOrderTwentySix_range_of_not_overHeight
        hN hreadyN hoverHeight hrange.1 hlam hfreq
    simpa only [MenonHeathBrownCaseIIDerivativeTwentySixBound] using
      derivativeExcised_montgomery_menonHeathBrownCaseII_derivativeDefect
        hX hsigma hΔ hgrid hselection hbaseGap hT hΔT hbaseBand label hkind
          (k0 := 26) (by norm_num) hfac hderivative hthreshold

end RHTower.Sieve
