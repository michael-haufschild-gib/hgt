import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheZetaResidueHasConstantScaledJets

/-!
# The scaled value and first two derivatives at the zeta pole

The entire residue contributes only its limiting value one. Quotient
differentiation therefore gives the literal scaled zeta jets with limits
`1/(κu)`, `−1/(κu²)`, and `2/(κu³)` away from the normalized pole.
-/

open Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The actual real zeta value divided by the scaling logarithm. -/
def scaledZetaPoleValue (N : ℕ) (κ u : ℝ) : ℝ :=
  (riemannZeta (1 + ((κ * u / Real.log N : ℝ) : ℂ))).re / Real.log N

/-- First scaled pole jet, retaining the exact entire residue. -/
def scaledZetaPoleFirstJet (N : ℕ) (κ u : ℝ) : ℝ :=
  realScaledZetaResidueJet N κ 1 u / (κ * u) -
    realScaledZetaResidueJet N κ 0 u / (κ * u ^ 2)

/-- Second scaled pole jet, retaining both residue derivatives. -/
def scaledZetaPoleSecondJet (N : ℕ) (κ u : ℝ) : ℝ :=
  realScaledZetaResidueJet N κ 2 u / (κ * u) -
    2 * realScaledZetaResidueJet N κ 1 u / (κ * u ^ 2) +
    2 * realScaledZetaResidueJet N κ 0 u / (κ * u ^ 3)

theorem hasDerivAt_scaledZetaPoleValue {N : ℕ} (hN : 1 < N) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (scaledZetaPoleValue N κ) (scaledZetaPoleFirstJet N κ u) u := by
  have hd := (hasDerivAt_realScaledZetaResidueJet N κ 0 u).div
    ((hasDerivAt_id u).const_mul κ) (mul_ne_zero hκ hu)
  have he : scaledZetaPoleValue N κ =ᶠ[𝓝 u]
      (fun x => realScaledZetaResidueJet N κ 0 x / (κ * x)) := by
    filter_upwards [isOpen_ne.mem_nhds hu] with x hx
    exact scaled_zeta_value_eq_residue hN hκ hx
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  simp only [scaledZetaPoleFirstJet, id_eq, mul_one]
  field_simp [hκ, hu] <;> ring

theorem hasDerivAt_scaledZetaPoleFirstJet (N : ℕ) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (scaledZetaPoleFirstJet N κ) (scaledZetaPoleSecondJet N κ u) u := by
  have h1 := (hasDerivAt_realScaledZetaResidueJet N κ 1 u).div
    ((hasDerivAt_id u).const_mul κ) (mul_ne_zero hκ hu)
  have h2 := (hasDerivAt_realScaledZetaResidueJet N κ 0 u).div
    (((hasDerivAt_id u).pow 2).const_mul κ) (mul_ne_zero hκ (pow_ne_zero 2 hu))
  apply (h1.sub h2).congr_deriv
  simp only [scaledZetaPoleSecondJet, id_eq, mul_one, Pi.pow_apply]
  norm_num only [Nat.reduceAdd]
  field_simp [hκ, hu] <;> ring

/-- The displayed pole jets are the actual first and second real derivatives. -/
theorem scaledZetaPoleValue_derivatives {N : ℕ} (hN : 1 < N) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    deriv (scaledZetaPoleValue N κ) u = scaledZetaPoleFirstJet N κ u ∧
    iteratedDeriv 2 (scaledZetaPoleValue N κ) u = scaledZetaPoleSecondJet N κ u := by
  constructor
  · exact (hasDerivAt_scaledZetaPoleValue hN hκ hu).deriv
  · have he : deriv (scaledZetaPoleValue N κ) =ᶠ[𝓝 u] scaledZetaPoleFirstJet N κ := by
      filter_upwards [isOpen_ne.mem_nhds hu] with x hx
      exact (hasDerivAt_scaledZetaPoleValue hN hκ hx).deriv
    have hh := ((hasDerivAt_scaledZetaPoleFirstJet N hκ hu).congr_of_eventuallyEq he).deriv
    simpa only [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one] using hh

/-- The normalized zeta value tends to its simple-pole model. -/
theorem tendsto_scaledZetaPoleValue {κ : ℝ} (hκ : κ ≠ 0)
    {u : ℕ → ℝ} {u₀ : ℝ} (hu : Tendsto u atTop (𝓝 u₀)) (hu₀ : u₀ ≠ 0) :
    Tendsto (fun N => scaledZetaPoleValue N κ (u N)) atTop (𝓝 (1 / (κ * u₀))) := by
  have hh := (tendsto_realScaledZetaResidueJet_zero κ hu).div (hu.const_mul κ) (mul_ne_zero hκ hu₀)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2, hu.eventually_ne hu₀] with N hN huN
  exact (scaled_zeta_value_eq_residue (by omega : 1 < N) hκ huN).symm

/-- Both literal derivatives tend to the corresponding derivatives of the simple pole. -/
theorem tendsto_scaledZetaPoleValue_derivatives {κ : ℝ} (hκ : κ ≠ 0)
    {u : ℕ → ℝ} {u₀ : ℝ} (hu : Tendsto u atTop (𝓝 u₀)) (hu₀ : u₀ ≠ 0) :
    Tendsto (fun N => deriv (scaledZetaPoleValue N κ) (u N)) atTop (𝓝 (-1 / (κ * u₀ ^ 2))) ∧
    Tendsto (fun N => iteratedDeriv 2 (scaledZetaPoleValue N κ) (u N)) atTop (𝓝 (2 / (κ * u₀ ^ 3))) := by
  have h0 := tendsto_realScaledZetaResidueJet_zero κ hu
  have h1 := tendsto_realScaledZetaResidueJet_succ κ hu 0
  have h2 := tendsto_realScaledZetaResidueJet_succ κ hu 1
  have hd := hu.const_mul κ
  have hd2 := (hu.pow 2).const_mul κ
  have hd3 := (hu.pow 3).const_mul κ
  have hn := mul_ne_zero hκ hu₀
  have hn2 := mul_ne_zero hκ (pow_ne_zero 2 hu₀)
  have hn3 := mul_ne_zero hκ (pow_ne_zero 3 hu₀)
  have hf : Tendsto (fun N => scaledZetaPoleFirstJet N κ (u N)) atTop (𝓝 (-1 / (κ * u₀ ^ 2))) := by
    simpa only [scaledZetaPoleFirstJet, zero_div, zero_sub, neg_div] using
      (h1.div hd hn).sub (h0.div hd2 hn2)
  have hs : Tendsto (fun N => scaledZetaPoleSecondJet N κ (u N)) atTop (𝓝 (2 / (κ * u₀ ^ 3))) := by
    simpa only [scaledZetaPoleSecondJet, mul_zero, zero_div, sub_zero, zero_add, mul_one] using
      ((h2.div hd hn).sub ((h1.const_mul 2).div hd2 hn2)).add ((h0.const_mul 2).div hd3 hn3)
  constructor
  · apply hf.congr'
    filter_upwards [eventually_ge_atTop 2, hu.eventually_ne hu₀] with N hN huN
    exact (scaledZetaPoleValue_derivatives (by omega : 1 < N) hκ huN).1.symm
  · apply hs.congr'
    filter_upwards [eventually_ge_atTop 2, hu.eventually_ne hu₀] with N hN huN
    exact (scaledZetaPoleValue_derivatives (by omega : 1 < N) hκ huN).2.symm

end GaloisForLFunctions.MultiscaleMollifiedZetaField
