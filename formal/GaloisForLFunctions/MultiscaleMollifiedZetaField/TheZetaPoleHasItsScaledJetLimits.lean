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
def scaledZetaPoleValue (L : ℝ) (κ u : ℝ) : ℝ :=
  (riemannZeta (1 + ((κ * u / L : ℝ) : ℂ))).re / L

/-- First scaled pole jet, retaining the exact entire residue. -/
def scaledZetaPoleFirstJet (L : ℝ) (κ u : ℝ) : ℝ :=
  realScaledZetaResidueJet L κ 1 u / (κ * u) -
    realScaledZetaResidueJet L κ 0 u / (κ * u ^ 2)

/-- Second scaled pole jet, retaining both residue derivatives. -/
def scaledZetaPoleSecondJet (L : ℝ) (κ u : ℝ) : ℝ :=
  realScaledZetaResidueJet L κ 2 u / (κ * u) -
    2 * realScaledZetaResidueJet L κ 1 u / (κ * u ^ 2) +
    2 * realScaledZetaResidueJet L κ 0 u / (κ * u ^ 3)

theorem hasDerivAt_scaledZetaPoleValue {L : ℝ} (hL : L ≠ 0) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (scaledZetaPoleValue L κ) (scaledZetaPoleFirstJet L κ u) u := by
  have hd := (hasDerivAt_realScaledZetaResidueJet L κ 0 u).div
    ((hasDerivAt_id u).const_mul κ) (mul_ne_zero hκ hu)
  have he : scaledZetaPoleValue L κ =ᶠ[𝓝 u]
      (fun x => realScaledZetaResidueJet L κ 0 x / (κ * x)) := by
    filter_upwards [isOpen_ne.mem_nhds hu] with x hx
    exact scaled_zeta_value_eq_residue hL hκ hx
  apply (hd.congr_of_eventuallyEq he).congr_deriv
  simp only [scaledZetaPoleFirstJet, id_eq, mul_one]
  field_simp [hκ, hu] <;> ring

theorem hasDerivAt_scaledZetaPoleFirstJet (L : ℝ) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    HasDerivAt (scaledZetaPoleFirstJet L κ) (scaledZetaPoleSecondJet L κ u) u := by
  have h1 := (hasDerivAt_realScaledZetaResidueJet L κ 1 u).div
    ((hasDerivAt_id u).const_mul κ) (mul_ne_zero hκ hu)
  have h2 := (hasDerivAt_realScaledZetaResidueJet L κ 0 u).div
    (((hasDerivAt_id u).pow 2).const_mul κ) (mul_ne_zero hκ (pow_ne_zero 2 hu))
  apply (h1.sub h2).congr_deriv
  simp only [scaledZetaPoleSecondJet, id_eq, mul_one, Pi.pow_apply]
  norm_num only [Nat.reduceAdd]
  field_simp [hκ, hu] <;> ring

/-- The displayed pole jets are the actual first and second real derivatives. -/
theorem scaledZetaPoleValue_derivatives {L : ℝ} (hL : L ≠ 0) {κ u : ℝ}
    (hκ : κ ≠ 0) (hu : u ≠ 0) :
    deriv (scaledZetaPoleValue L κ) u = scaledZetaPoleFirstJet L κ u ∧
    iteratedDeriv 2 (scaledZetaPoleValue L κ) u = scaledZetaPoleSecondJet L κ u := by
  constructor
  · exact (hasDerivAt_scaledZetaPoleValue hL hκ hu).deriv
  · have he : deriv (scaledZetaPoleValue L κ) =ᶠ[𝓝 u] scaledZetaPoleFirstJet L κ := by
      filter_upwards [isOpen_ne.mem_nhds hu] with x hx
      exact (hasDerivAt_scaledZetaPoleValue hL hκ hx).deriv
    have hh := ((hasDerivAt_scaledZetaPoleFirstJet L hκ hu).congr_of_eventuallyEq he).deriv
    simpa only [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hh

/-- The normalized zeta value tends to its simple-pole model. -/
theorem tendsto_scaledZetaPoleValue {κ : ℝ} (hκ : κ ≠ 0)
    {ι : Type*} {l : Filter ι} {L : ι → ℝ} (hL : Tendsto L l atTop)
    {u : ι → ℝ} {u₀ : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : u₀ ≠ 0) :
    Tendsto (fun N => scaledZetaPoleValue (L N) κ (u N)) l (𝓝 (1 / (κ * u₀))) := by
  have hh := (tendsto_realScaledZetaResidueJet_zero κ hL hu).div (hu.const_mul κ) (mul_ne_zero hκ hu₀)
  apply hh.congr'
  filter_upwards [hL.eventually_gt_atTop 0, hu.eventually_ne hu₀] with N hLN huN
  exact (scaled_zeta_value_eq_residue hLN.ne' hκ huN).symm

/-- Both literal derivatives tend to the corresponding derivatives of the simple pole. -/
theorem tendsto_scaledZetaPoleValue_derivatives {κ : ℝ} (hκ : κ ≠ 0)
    {ι : Type*} {l : Filter ι} {L : ι → ℝ} (hL : Tendsto L l atTop)
    {u : ι → ℝ} {u₀ : ℝ} (hu : Tendsto u l (𝓝 u₀)) (hu₀ : u₀ ≠ 0) :
    Tendsto (fun N => deriv (scaledZetaPoleValue (L N) κ) (u N)) l (𝓝 (-1 / (κ * u₀ ^ 2))) ∧
    Tendsto (fun N => iteratedDeriv 2 (scaledZetaPoleValue (L N) κ) (u N)) l (𝓝 (2 / (κ * u₀ ^ 3))) := by
  have h0 := tendsto_realScaledZetaResidueJet_zero κ hL hu
  have h1 := tendsto_realScaledZetaResidueJet_succ κ hL hu 0
  have h2 := tendsto_realScaledZetaResidueJet_succ κ hL hu 1
  have hd := hu.const_mul κ
  have hd2 := (hu.pow 2).const_mul κ
  have hd3 := (hu.pow 3).const_mul κ
  have hn := mul_ne_zero hκ hu₀
  have hn2 := mul_ne_zero hκ (pow_ne_zero 2 hu₀)
  have hn3 := mul_ne_zero hκ (pow_ne_zero 3 hu₀)
  have hf : Tendsto (fun N => scaledZetaPoleFirstJet (L N) κ (u N)) l (𝓝 (-1 / (κ * u₀ ^ 2))) := by
    simpa only [scaledZetaPoleFirstJet, Pi.div_apply, Nat.reduceAdd, zero_div, zero_sub, neg_div] using
      (h1.div hd hn).sub (h0.div hd2 hn2)
  have hs : Tendsto (fun N => scaledZetaPoleSecondJet (L N) κ (u N)) l (𝓝 (2 / (κ * u₀ ^ 3))) := by
    simpa only [scaledZetaPoleSecondJet, Pi.div_apply, Nat.reduceAdd, mul_zero, zero_div, sub_zero, zero_add, mul_one] using
      ((h2.div hd hn).sub ((h1.const_mul 2).div hd2 hn2)).add ((h0.const_mul 2).div hd3 hn3)
  constructor
  · apply hf.congr'
    filter_upwards [hL.eventually_gt_atTop 0, hu.eventually_ne hu₀] with N hLN huN
    exact (scaledZetaPoleValue_derivatives hLN.ne' hκ huN).1.symm
  · apply hs.congr'
    filter_upwards [hL.eventually_gt_atTop 0, hu.eventually_ne hu₀] with N hLN huN
    exact (scaledZetaPoleValue_derivatives hLN.ne' hκ huN).2.symm

end GaloisForLFunctions.MultiscaleMollifiedZetaField
