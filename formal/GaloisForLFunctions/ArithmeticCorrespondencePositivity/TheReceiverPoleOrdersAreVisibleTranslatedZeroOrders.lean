import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheCenteredReceiverSymbolIsHardy
import GaloisForLFunctions.ArithmeticOrientationTheory.PaidKernelsCoverVisibleTranslatedZeroOrders
import GaloisForLFunctions.RHTower.ZetaSelfReturnThresholdReadsTheVanishingOrder

/-!
# The effective pole order of the actual receiver

At a translated zeta zero, the difference of the two vanishing orders is
exactly the surviving pole order. The centering factor equals one at the
denominator zero, so it cannot remove any further part of the pole.
-/

open Complex Set Filter Topology
open RHTower RHTower.Sieve GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The existing extended-natural effective order is finite in the strip. -/
theorem visibleTranslatedZetaOrder_eq_nat_sub {ε : ℝ} {ρ : ℂ}
    (hρ : ρ ≠ 1) (hs : ρ - (ε : ℂ) ≠ 1) :
    visibleTranslatedZetaOrder ε ρ =
      ((analyticOrderNatAt riemannZeta ρ -
        analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) : ℕ) : ℕ∞) := by
  rw [visibleTranslatedZetaOrder, ENat.coe_sub,
    Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannZeta_ne_top_of_ne_one' hρ),
    Nat.cast_analyticOrderNatAt (analyticOrderAt_riemannZeta_ne_top_of_ne_one' hs)]

/-- After the two exact vanishing powers are removed, centering leaves an
analytic nonvanishing factor. -/
theorem exists_centeredReceiverSymbol_order_factor {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
        centeredReceiverSymbol ε (ρ - (ε : ℂ) + z) =
          z ^ analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) /
            z ^ analyticOrderNatAt riemannZeta ρ * H z := by
  let s : ℂ := ρ - (ε : ℂ)
  have hsre : 1 / 2 < s.re := by dsimp [s]; linarith
  have hsre1 : s.re < 1 := by dsimp [s]; linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hsre; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hsre1; linarith
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre1; linarith
  have hN : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hD : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  obtain ⟨u, hu, hu0, huf⟩ := hN.analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_ne_top_of_ne_one' hs1)
  obtain ⟨v, hv, hv0, hvf⟩ := hD.analyticOrderAt_ne_top.mp
    (analyticOrderAt_riemannZeta_ne_top_of_ne_one' hρ1)
  let c : ℂ := invZeta (1 + (ε : ℂ))
  let H : ℂ → ℂ := fun z =>
    u (s + z) * (1 - c * riemannZeta (ρ + z)) / ((s + z) * v (ρ + z))
  have huA : AnalyticAt ℂ (fun z : ℂ => u (s + z)) 0 := by
    have hu' : AnalyticAt ℂ u (s + (0 : ℂ)) := by simpa only [add_zero] using hu
    exact hu'.comp (f := fun z : ℂ => s + z) (analyticAt_const.add analyticAt_id)
  have hvA : AnalyticAt ℂ (fun z : ℂ => v (ρ + z)) 0 := by
    have hv' : AnalyticAt ℂ v (ρ + (0 : ℂ)) := by simpa only [add_zero] using hv
    exact hv'.comp (f := fun z : ℂ => ρ + z) (analyticAt_const.add analyticAt_id)
  have hzA : AnalyticAt ℂ (fun z : ℂ => riemannZeta (ρ + z)) 0 := by
    have hD' : AnalyticAt ℂ riemannZeta (ρ + (0 : ℂ)) := by simpa only [add_zero] using hD
    exact hD'.comp (f := fun z : ℂ => ρ + z) (analyticAt_const.add analyticAt_id)
  have hHA : AnalyticAt ℂ H 0 :=
    (huA.mul (analyticAt_const.sub (analyticAt_const.mul hzA))).div
      ((analyticAt_const.add analyticAt_id).mul hvA)
      (by simpa only [add_zero] using mul_ne_zero hs0 hv0)
  have hH0 : H 0 ≠ 0 := by
    dsimp only [H]
    rw [add_zero, add_zero, hz, mul_zero, sub_zero, mul_one]
    exact div_ne_zero hu0 (mul_ne_zero hs0 hv0)
  refine ⟨H, hHA, hH0, ?_⟩
  have htN : Tendsto (fun z : ℂ => s + z) (𝓝 0) (𝓝 s) := by
    simpa only [add_zero] using
      (by fun_prop : Continuous fun z : ℂ => s + z).tendsto (0 : ℂ)
  have htD : Tendsto (fun z : ℂ => ρ + z) (𝓝 0) (𝓝 ρ) := by
    simpa only [add_zero] using
      (by fun_prop : Continuous fun z : ℂ => ρ + z).tendsto (0 : ℂ)
  have hnear : ∀ᶠ z : ℂ in 𝓝 0,
      riemannZeta (s + z) = z ^ analyticOrderNatAt riemannZeta s * u (s + z) ∧
      riemannZeta (ρ + z) = z ^ analyticOrderNatAt riemannZeta ρ * v (ρ + z) ∧
      s + z ≠ 0 ∧ s + z ≠ 1 ∧ ρ + z ≠ 1 ∧ v (ρ + z) ≠ 0 := by
    filter_upwards [htN.eventually huf, htD.eventually hvf,
      htN.eventually (eventually_ne_nhds hs0), htN.eventually (eventually_ne_nhds hs1),
      htD.eventually (eventually_ne_nhds hρ1), htD.eventually (hv.continuousAt.eventually_ne hv0)]
      with z hu hv hs0 hs1 hρ1 hv0
    simp only [add_sub_cancel_left, smul_eq_mul] at hu hv
    exact ⟨hu, hv, hs0, hs1, hρ1, hv0⟩
  filter_upwards [hnear] with z hz hz0'
  rcases hz with ⟨hu, hv, hs0, hs1, hρ1, hv0⟩
  have hshift : s + z + (ε : ℂ) = ρ + z := by dsimp [s]; ring
  change centeredReceiverSymbol ε (s + z) =
    z ^ analyticOrderNatAt riemannZeta s / z ^ analyticOrderNatAt riemannZeta ρ * H z
  rw [centeredReceiverSymbol_eq hs1, hshift, invZeta_eq_inv hρ1, hu, hv]
  dsimp only [H, c]
  rw [hv]
  field_simp [hz0', hs0, hv0]

/-- A positive visible order is exactly the surviving pole order. -/
theorem exists_centeredReceiverSymbol_pole_factor {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1)
    {m : ℕ} (hm : 0 < m) (horder : visibleTranslatedZetaOrder ε ρ = (m : ℕ∞)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
        centeredReceiverSymbol ε (ρ - (ε : ℂ) + z) = H z / z ^ m := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre1; linarith
  have hs1 : ρ - (ε : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, one_re] at this
    linarith
  have hnm : analyticOrderNatAt riemannZeta ρ -
      analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) = m := by
    rw [visibleTranslatedZetaOrder_eq_nat_sub hρ1 hs1] at horder
    exact_mod_cast horder
  have hDm : analyticOrderNatAt riemannZeta ρ =
      analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) + m := by omega
  obtain ⟨H, hH, hH0, hf⟩ := exists_centeredReceiverSymbol_order_factor hε hz hre hre1
  refine ⟨H, hH, hH0, ?_⟩
  filter_upwards [hf] with z hz hz0
  rw [hz hz0, hDm, pow_add]
  field_simp [hz0]

/-- Complete cancellation gives an analytic extension across the translated zero. -/
theorem exists_centeredReceiverSymbol_regular_factor {ε : ℝ} (hε : 0 < ε)
    {ρ : ℂ} (hz : riemannZeta ρ = 0) (hre : 1 / 2 + ε < ρ.re) (hre1 : ρ.re < 1)
    (horder : visibleTranslatedZetaOrder ε ρ = 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), z ≠ 0 →
        centeredReceiverSymbol ε (ρ - (ε : ℂ) + z) = H z := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre1; linarith
  have hs1 : ρ - (ε : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, one_re] at this
    linarith
  have hnm : analyticOrderNatAt riemannZeta ρ ≤
      analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) := by
    rw [visibleTranslatedZetaOrder_eq_nat_sub hρ1 hs1] at horder
    have h : analyticOrderNatAt riemannZeta ρ -
        analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) = 0 := by exact_mod_cast horder
    omega
  obtain ⟨H, hH, _, hf⟩ := exists_centeredReceiverSymbol_order_factor hε hz hre hre1
  let k := analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) - analyticOrderNatAt riemannZeta ρ
  refine ⟨fun z => z ^ k * H z, (analyticAt_id.pow k).mul hH, ?_⟩
  filter_upwards [hf] with z hz hz0
  have hN : analyticOrderNatAt riemannZeta (ρ - (ε : ℂ)) =
      analyticOrderNatAt riemannZeta ρ + k := by dsimp [k]; omega
  rw [hz hz0, hN, pow_add]
  field_simp [hz0]

#print axioms exists_centeredReceiverSymbol_pole_factor
#print axioms exists_centeredReceiverSymbol_regular_factor

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
