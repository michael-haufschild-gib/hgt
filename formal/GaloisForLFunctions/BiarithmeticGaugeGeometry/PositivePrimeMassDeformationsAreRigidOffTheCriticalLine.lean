import GaloisForLFunctions.BiarithmeticGaugeGeometry.AnchorLinePositivityAndCapacityOfRationalDeformations
import GaloisForLFunctions.BiarithmeticGaugeGeometry.TheLandauWronskianDeformationPrinciple

/-!
# Positive Prime-Mass Deformations Are Rigid Off the Critical Line

A member `(F, Λ)` of `HeightCoupledSystem 2 1 1 γ` is a **positive prime-mass deformation** of the
height-coupled carrier `ζ_γ` when its prime-side measure exceeds that of `ζ_γ` by a nonnegative
measure `ν`:

`−F'/F(σ) + ζ_γ'/ζ_γ(σ) = ∫₀^∞ e^{−σu} dν(u)` on a real ray, `ν ≥ 0`.

No finiteness of the divisor of `Λ / Λ_γ` is assumed: `ν` may be any nonnegative measure with a
convergent Laplace transform somewhere (rational deformations, infinite products, transcendental
multipliers). This module proves that such deformations **cannot touch the divisor off the critical
line and cannot raise the central vanishing order**, unless `ξ` has an off-critical zero at ordinate
`γ` itself.

1. **Orders and the anchor (`positiveDeformation_orders_and_anchor`).** The Landau–Wronskian
   principle (`landauWronskian_orders_and_anchor`) applied to `Λ` and `Λ_γ`: with `ν' = ν + Lebesgue`
   pinning a finite abscissa `c ≥ 0`, `ord_w Λ = ord_w Λ_γ` for `Re w > c`, and if `c > 0` it is a real
   zero of `Λ_γ` with `ord_c Λ < ord_c Λ_γ`.

2. **Off-line rigidity (`positiveDeformation_offLine_rigid`).** If `ξ` has no off-critical zero at
   ordinate `γ`, the abscissa lies at or left of `1/2`; hence `ord_w Λ = ord_w Λ_γ` for every
   `w` off the critical line and `ord_{1/2} Λ ≤ ord_{1/2} Λ_γ`. Adding nonnegative prime mass to the
   height-coupled carrier can only move zeros along the critical line and can only lower the central
   order: a violation of the central ceiling requires a deformation that removes prime mass, or an
   off-critical zero at ordinate `γ`.

3. **The positive ceiling is a horizontal zero-free line
   (`positiveCentralVanishingCeiling_iff`, `riemannHypothesis_iff_forall_positiveCentralVanishingCeiling`).**
   The coupled quartet contraction is a positive prime-mass deformation (its scale density is
   nonnegative), so for `γ ≠ 0` the ceiling over all positive deformations holds iff `ξ` has no
   off-critical zero at ordinate `γ`; RH is the positive ceiling at every height.
-/

open Complex Filter Topology Set MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

open ArithmeticCorrespondencePositivity StripBochnerWeilForcing MultiplicativePositivityGeometry
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa
  complexLaplace_ofReal differentiableOn_complexLaplace integrable_cexp_of_gt_abscissa
  isAbscissa_volume_zero exists_isAbscissa false_of_analyticAt_abscissa laplaceMass_antitone)


/-! ## §1. Orders right of the abscissa and the real pole at it -/

/-- **Orders and the anchor of a perturbed positive prime-mass deformation.** If
`−F'/F + ζ_γ'/ζ_γ = 𝓛ν + E` on a real ray, with `ν ≥ 0` and `E` holomorphic on `Re s > σ_E`, there is
`c ≥ 0` such that `ord_w Λ = ord_w Λ_γ` for all `Re w > max(c, σ_E)`, and if `c > max(0, σ_E)`
then `c` is a real zero of `Λ_γ` with `ord_c Λ < ord_c Λ_γ`. -/
theorem positiveDeformation_orders_and_anchor_of_perturbation {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ}
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ w : ℂ, max c σE < w.re →
        analyticOrderAt Λ w = analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w) ∧
      (0 < c → σE < c → heightCoupledΛ (fun s => 2 * RHTower.xi s) γ (c : ℂ) = 0 ∧
        (analyticOrderAt Λ (c : ℂ)).toNat <
          (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (c : ℂ)).toNat) ∧
      (∀ z : ℂ, max c σE < z.re → Λ z ≠ 0 →
        heightCoupledΛ (fun s => 2 * RHTower.xi s) γ z ≠ 0 →
        logDeriv (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) z - logDeriv Λ z =
          complexLaplace ν z + E z) ∧
      (∀ z : ℂ, c < z.re →
        Integrable (fun u : ℝ => Complex.exp (-z * (u : ℂ))) (ν.restrict (Ioi (0 : ℝ)))) := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  refine landauWronskian_orders_and_anchor hHC.entire_Λ hHC0.entire_Λ hHC.orderAt_ne_top
    hHC0.orderAt_ne_top (σ₁ := max σ₁ 1)
    (ne_top_of_le_ne_top hconv (laplaceMass_antitone ν (le_max_left σ₁ 1))) hE fun σ hσ => ?_
  have hσre : 1 < (σ : ℂ).re := by simpa using lt_of_le_of_lt (le_max_right _ _) hσ
  refine ⟨hHC.ne_zero_of_one_lt_re hσre, hHC0.ne_zero_of_one_lt_re hσre, ?_⟩
  have h1 := hHC.neg_logDeriv_F_eq hσre
  have h2 := hHC0.neg_logDeriv_F_eq hσre
  rw [← hagree σ (lt_of_le_of_lt (le_max_left _ _) hσ)]
  linear_combination h2 - h1

/-- **Orders and the anchor of a positive prime-mass deformation** (`E = 0`). -/
theorem positiveDeformation_orders_and_anchor {γ : ℝ} {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤)
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ)) :
    ∃ c : ℝ, 0 ≤ c ∧
      (∀ w : ℂ, c < w.re →
        analyticOrderAt Λ w = analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w) ∧
      (0 < c → heightCoupledΛ (fun s => 2 * RHTower.xi s) γ (c : ℂ) = 0 ∧
        (analyticOrderAt Λ (c : ℂ)).toNat <
          (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (c : ℂ)).toNat) := by
  obtain ⟨c, hc0, hord, hanc, -, -⟩ :=
    positiveDeformation_orders_and_anchor_of_perturbation hHC hconv
    (E := fun _ => 0) (σE := -1) (differentiableOn_const 0)
    (fun σ hσ => by rw [hagree σ hσ, add_zero])
  refine ⟨c, hc0, fun w hw => hord w ?_, fun hcpos => hanc hcpos (by linarith)⟩
  rwa [max_eq_left (by linarith)]

/-! ## §2. Off-line rigidity -/

/-- **Off-line rigidity under a sub-critical perturbation.** If `ξ` has no off-critical zero at
ordinate `γ` and `−F'/F + ζ_γ'/ζ_γ = 𝓛ν + E` with `ν ≥ 0` and `E` holomorphic on `Re s > σ_E`,
`σ_E < 1/2`, then `Λ` has exactly the zeros of `Λ_γ` off the critical line and central vanishing
order at most that of `Λ_γ`. -/
theorem perturbedDeformation_offLine_rigid {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤) {E : ℂ → ℂ} {σE : ℝ} (hσE : σE < 1 / 2)
    (hE : DifferentiableOn ℂ E {s : ℂ | σE < s.re})
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ) + E σ) :
    (∀ w : ℂ, w.re ≠ 1 / 2 →
        analyticOrderAt Λ w = analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w) ∧
      (analyticOrderAt Λ (1 / 2)).toNat ≤
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat := by
  have hHC0 := zeta_mem_heightCoupledSystem γ
  obtain ⟨c, hc0, hord, hanchor, -, -⟩ :=
    positiveDeformation_orders_and_anchor_of_perturbation hHC hconv hE hagree
  have hc : c ≤ 1 / 2 := by
    by_contra hgt
    push Not at hgt
    have hz := (hanchor (by linarith) (by linarith)).1
    have := hoff c (xi_add_eq_zero_of_heightCoupledΛ_real_zero hz)
    linarith
  have hmax : max c σE ≤ 1 / 2 := max_le hc hσE.le
  have hright : ∀ w : ℂ, 1 / 2 < w.re → analyticOrderAt Λ w =
      analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w := fun w hw =>
    hord w (lt_of_le_of_lt hmax hw)
  refine ⟨fun w hw => ?_, ?_⟩
  · rcases lt_or_gt_of_ne hw with hlt | hgt
    · have h1 : 1 / 2 < (1 - w).re := by simp; linarith
      rw [← hHC.orderAt_one_sub, ← hHC0.orderAt_one_sub]
      exact hright _ h1
    · exact hright w hgt
  · rcases lt_or_eq_of_le hmax with hlt | heq
    · rw [hord (1 / 2) (by simpa using hlt)]
    · have hc2 : c = 1 / 2 := by
        rcases max_choice c σE with h | h <;> rw [h] at heq
        · exact heq
        · linarith
      have h := (hanchor (by rw [hc2]; norm_num) (by rw [hc2]; exact hσE)).2
      rw [hc2] at h
      have hhalf : (((1 / 2 : ℝ)) : ℂ) = 1 / 2 := by norm_num
      rw [hhalf] at h
      exact h.le

/-- **Off-line rigidity of positive prime-mass deformations.** If `ξ` has no off-critical zero at
ordinate `γ`, every positive prime-mass deformation `(F, Λ)` of `ζ_γ` inside
`HeightCoupledSystem 2 1 1 γ` has exactly the zeros of `Λ_γ` off the critical line, and central
vanishing order at most that of `Λ_γ`. -/
theorem positiveDeformation_offLine_rigid {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) {F Λ : ℂ → ℂ}
    (hHC : HeightCoupledSystem 2 1 1 γ F Λ) {ν : Measure ℝ} {σ₁ : ℝ}
    (hconv : laplaceMass ν σ₁ ≠ ⊤)
    (hagree : ∀ σ : ℝ, σ₁ < σ →
      -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
        ((laplaceReal ν σ : ℝ) : ℂ)) :
    (∀ w : ℂ, w.re ≠ 1 / 2 →
        analyticOrderAt Λ w = analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) w) ∧
      (analyticOrderAt Λ (1 / 2)).toNat ≤
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat :=
  perturbedDeformation_offLine_rigid hoff hHC hconv (E := fun _ => 0) (σE := 0) (by norm_num)
    (differentiableOn_const 0) (fun σ hσ => by rw [hagree σ hσ, add_zero])

/-! ## §3. The positive central ceiling -/

/-- `(F, Λ)` is a **positive prime-mass deformation** of `ζ_γ` inside `HeightCoupledSystem 2 1 1 γ`:
`−F'/F + ζ_γ'/ζ_γ` is the Laplace transform of a nonnegative measure on a real ray. -/
def IsPositiveMassDeformation (γ : ℝ) (F Λ : ℂ → ℂ) : Prop :=
  HeightCoupledSystem 2 1 1 γ F Λ ∧ ∃ (ν : Measure ℝ) (σ₁ : ℝ), laplaceMass ν σ₁ ≠ ⊤ ∧
    ∀ σ : ℝ, σ₁ < σ → -logDeriv F (σ : ℂ) + logDeriv (heightCoupledF riemannZeta γ) (σ : ℂ) =
      ((laplaceReal ν σ : ℝ) : ℂ)

/-- `CentralVanishingCeiling γ` restricted to positive prime-mass deformations of `ζ_γ`. -/
def PositiveCentralVanishingCeiling (γ : ℝ) : Prop :=
  ∀ F Λ : ℂ → ℂ, IsPositiveMassDeformation γ F Λ →
    (analyticOrderAt Λ (1 / 2)).toNat ≤
      (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat

theorem positiveCentralVanishingCeiling_of_offCritical_free {γ : ℝ}
    (hoff : ∀ x : ℝ, RHTower.xi ((x : ℂ) + (γ : ℂ) * I) = 0 → x = 1 / 2) :
    PositiveCentralVanishingCeiling γ :=
  fun _ _ ⟨hHC, _, _, hconv, hagree⟩ => (positiveDeformation_offLine_rigid hoff hHC hconv hagree).2

/-- A nonnegative continuous density with an integrable Laplace kernel gives a positive measure with
finite Laplace mass and the expected real transform. -/
theorem laplace_withDensity {w : ℝ → ℝ} (hw : Continuous w) (hw0 : ∀ t, 0 < t → 0 ≤ w t)
    {σ : ℝ} (hint : IntegrableOn (fun t => w t * Real.exp (-σ * t)) (Ioi 0)) :
    laplaceMass (volume.withDensity fun t => ((Real.toNNReal (w t) : NNReal) : ℝ≥0∞)) σ ≠ ⊤ ∧
      laplaceReal (volume.withDensity fun t => ((Real.toNNReal (w t) : NNReal) : ℝ≥0∞)) σ =
        ∫ t in Ioi (0 : ℝ), w t * Real.exp (-σ * t) := by
  have hmeas : Measurable fun t => Real.toNNReal (w t) := hw.measurable.real_toNNReal
  have hcongr : EqOn (fun t => ((Real.toNNReal (w t) : NNReal) : ℝ) * Real.exp (-σ * t))
      (fun t => w t * Real.exp (-σ * t)) (Ioi 0) := fun t ht => by
    simp only [Real.coe_toNNReal _ (hw0 t ht)]
  refine ⟨?_, ?_⟩
  · unfold laplaceMass
    rw [setLIntegral_withDensity_eq_setLIntegral_mul volume (by fun_prop) (by fun_prop)
      measurableSet_Ioi]
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => w t * Real.exp (-σ * t) :=
      (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (hw0 t ht) (Real.exp_pos _).le)
    have heq : ∫⁻ t in Ioi (0 : ℝ), ((fun t => ((Real.toNNReal (w t) : NNReal) : ℝ≥0∞)) *
        fun t => ENNReal.ofReal (Real.exp (-σ * t))) t =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (w t * Real.exp (-σ * t)) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul (hw0 t ht)]
      rfl
    rw [heq, ← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_ne_top
  · unfold laplaceReal
    rw [setIntegral_withDensity_eq_setIntegral_smul hmeas _ measurableSet_Ioi]
    exact setIntegral_congr_fun measurableSet_Ioi hcongr

/-- **Off-critical zeros produce positive deformations above the central ceiling.** If
`ξ(1/2 + a + iγ) = 0` with `0 < a < 1/2`, `γ ≠ 0`, the coupled quartet contraction is a positive
prime-mass deformation raising the central vanishing order by `4`. -/
theorem exists_positiveDeformation_above_ceiling {γ a : ℝ} (hγ : γ ≠ 0) (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (hxi : RHTower.xi (1 / 2 + a + γ * I) = 0) :
    ∃ F Λ : ℂ → ℂ, IsPositiveMassDeformation γ F Λ ∧
      (analyticOrderAt Λ (1 / 2)).toNat =
        (analyticOrderAt (heightCoupledΛ (fun s => 2 * RHTower.xi s) γ) (1 / 2)).toNat + 4 := by
  have hZ := completedPositiveSystem_riemannZeta
  have hHC0 := zeta_mem_heightCoupledSystem γ
  have hq : (fun s => 2 * RHTower.xi s) (1 / 2 + (a : ℂ) + (γ : ℂ) * I) = 0 := by
    simp only [hxi, mul_zero]
  obtain ⟨Λc, hHCc, hord⟩ :=
    CompletedPositiveSystem.contractComplexQuartet_heightCoupled hZ ha0 ha1 hγ hq
  set z := quartetMultiplierPoints a γ
  set m := quartetMultiplierOrders
  set S := Finset.univ.image z
  set c := multiplierWeight z m
  set Q := coupledQuartetSymSquare a a γ
  have haQ : |a| < 1 / 2 := abs_lt.mpr ⟨by linarith, ha1⟩
  obtain ⟨a₀, ha₀1, hza⟩ := exists_bound_re_rationalMultiplier z
  have hSa : ∀ w ∈ S, w.re ≤ a₀ := fun w hw => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hw; linarith [hza i]
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  -- the multiplier's log-derivative is the polar sum right of the multiplier points
  have hQpol : ∀ s : ℂ, a₀ < s.re → -logDeriv Q s = polarSum S c s := by
    intro s hs
    have hs1 : 1 < s.re := by linarith
    have hsz : ∀ i, s ≠ z i := fun i h => by have := hza i; rw [← h] at this; linarith
    have hev : Q =ᶠ[𝓝 s] rationalMultiplier z m :=
      Filter.eventually_of_mem (hU.mem_nhds hs1) fun w hw =>
        coupledQuartetSymSquare_eq_rationalMultiplier haQ hw
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, ← logDeriv_apply]
    exact neg_logDeriv_rationalMultiplier z m hsz
  have hQne : ∀ s : ℂ, a₀ < s.re → Q s ≠ 0 := fun s hs => by
    have hs1 : 1 < s.re := by linarith
    show coupledQuartetSymSquare a a γ s ≠ 0
    rw [coupledQuartetSymSquare_eq_rationalMultiplier haQ hs1]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (sub_ne_zero.mpr fun h => by
      have hzi := hza i
      change (quartetMultiplierPoints a γ i).re + 1 < a₀ at hzi
      rw [← h] at hzi; linarith)
  have hpd : ∀ σ : ℝ, a₀ < σ → IsEvenPosDef fun u : ℝ =>
      (LSeries (fun _ : ℕ => ((0 : ℝ) : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
        polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
    intro σ hσ
    have h := isEvenPosDef_coupledQuartetSymSquare (γ := γ) ha0 le_rfl ha1 (by linarith : 1 < σ)
    have heq : (fun u : ℝ => (-logDeriv Q ((σ : ℂ) + (u : ℂ) * I)).re) =
        fun u : ℝ => (LSeries (fun _ : ℕ => ((0 : ℝ) : ℂ)) ((σ : ℂ) + (u : ℂ) * I) +
          polarSum S c ((σ : ℂ) + (u : ℂ) * I)).re := by
      funext u
      rw [hQpol _ (by simpa using hσ)]
      simp [LSeries, LSeries.term_def]
    rwa [heq] at h
  have habs : LSeries.abscissaOfAbsConv (fun _ : ℕ => ((0 : ℝ) : ℂ)) < a₀ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 0)
      fun y _ => by
        have h : LSeriesSummable (0 : ℕ → ℂ) (y : ℂ) := LSeriesSummable_zero
        convert h using 1
        funext n; simp)
      (by exact_mod_cast (by linarith : (0 : ℝ) < a₀))
  have hw : ∀ t : ℝ, 0 < t → 0 ≤ polarScaleWeight S c t := fun t ht =>
    polarScaleWeight_nonneg_of_lattice_posDef (fun _ => le_rfl) hSa habs
      (fun σ hσ => (hpd σ hσ).posDef) ht
  have hσS : ∀ w ∈ S, c w ≠ 0 → w.re ≤ a₀ := fun w hw _ => hSa w hw
  have hsym : ∀ s : ℂ, a₀ < s.re → polarSum S c s = ∑ w ∈ S, (c w : ℂ) / (s - conj w) :=
    fun s hs => polarSum_eq_reflected_of_even hSa hσS (polarSum_re_even_of_lattice_even hpd) hs
  set wd : ℝ → ℝ := polarScaleWeight S c
  have hwc : Continuous wd := by simp only [wd]; unfold polarScaleWeight; fun_prop
  have hreal : ∀ σ : ℝ, a₀ < σ →
      polarSum S c (σ : ℂ) = ((∫ t in Ioi (0 : ℝ), wd t * Real.exp (-σ * t) : ℝ) : ℂ) := by
    intro σ hσ
    have hint := integral_polarScaleWeight_cos_mul_exp hσS hsym hσ 0
    simp only [zero_mul, Real.cos_zero, mul_one, Complex.ofReal_zero, add_zero] at hint
    have him : (polarSum S c (σ : ℂ)).im = 0 := by
      have h1 := conj_polarSum_conj S c (σ : ℂ)
      rw [Complex.conj_ofReal, ← hsym _ (by simpa using hσ)] at h1
      exact Complex.conj_eq_iff_im.mp h1
    apply Complex.ext
    · rw [Complex.ofReal_re, ← hint]
    · rw [him, Complex.ofReal_im]
  refine ⟨_, Λc, ⟨hHCc, volume.withDensity fun t => ((Real.toNNReal (wd t) : NNReal) : ℝ≥0∞),
    a₀ + 1, ?_, fun σ hσ => ?_⟩, ?_⟩
  · exact (laplace_withDensity hwc hw (integrableOn_polarScaleWeight_mul_exp hσS
      (by linarith : a₀ < a₀ + 1) (fun _ => 1) continuous_const (fun _ => by simp)
      |>.congr_fun (fun t _ => by simp only [mul_one]; rfl) measurableSet_Ioi)).1
  · have hσa : a₀ < σ := by linarith
    have hσ1 : 1 < (σ : ℂ).re := by simp; linarith
    have hσre : a₀ < (σ : ℂ).re := by simpa using hσa
    have hζd : DifferentiableAt ℂ (heightCoupledF riemannZeta γ) (σ : ℂ) :=
      (hHC0.diffOn_F _ hσ1).differentiableAt (hU.mem_nhds hσ1)
    have hQd : DifferentiableAt ℂ Q (σ : ℂ) := by
      have hev : Q =ᶠ[𝓝 (σ : ℂ)] rationalMultiplier z m :=
        Filter.eventually_of_mem (hU.mem_nhds hσ1) fun w hw =>
          coupledQuartetSymSquare_eq_rationalMultiplier haQ hw
      exact ((rationalMultiplier_analyticAt z m fun i h => by
        have := hza i; rw [← h] at this; simp at this; linarith).differentiableAt).congr_of_eventuallyEq hev
    have hlog : logDeriv (fun s => heightCoupledF riemannZeta γ s * Q s) (σ : ℂ) =
        logDeriv (heightCoupledF riemannZeta γ) σ + logDeriv Q σ :=
      logDeriv_mul _ (hHC0.ne_zero_F _ hσ1) (hQne _ hσre) hζd hQd
    rw [hlog, (laplace_withDensity hwc hw (integrableOn_polarScaleWeight_mul_exp hσS hσa
      (fun _ => 1) continuous_const (fun _ => by simp)
      |>.congr_fun (fun t _ => by simp only [mul_one]; rfl) measurableSet_Ioi)).2, ← hreal σ hσa,
      ← hQpol _ hσre]
    ring
  · have h0 := CompletedPositiveSystem.orderAt_heightCoupledΛ_real hZ γ (1 / 2)
    have hhalf : (((1 / 2 : ℝ) : ℂ)) = (1 / 2 : ℂ) := by norm_num
    rw [hhalf] at h0
    omega

/-- **The positive central ceiling is exactly a horizontal zero-free line.** For `γ ≠ 0`, no
positive prime-mass deformation of `ζ_γ` exceeds its central vanishing order iff `ξ` has no
off-critical zero at ordinate `γ`. -/
theorem positiveCentralVanishingCeiling_iff {γ : ℝ} (hγ : γ ≠ 0) :
    PositiveCentralVanishingCeiling γ ↔
      ∀ a : ℝ, 0 < a → a < 1 / 2 → RHTower.xi (1 / 2 + a + γ * I) ≠ 0 := by
  constructor
  · intro hceil a ha0 ha1 hxi
    obtain ⟨F, Λ, hdef, hord⟩ := exists_positiveDeformation_above_ceiling hγ ha0 ha1 hxi
    have := hceil F Λ hdef
    omega
  · intro hfree
    refine positiveCentralVanishingCeiling_of_offCritical_free fun x hx => ?_
    by_contra hne
    have hpos := RHTower.xi_zero_re_pos hx
    have hlt := RHTower.xi_zero_re_lt_one hx
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero] at hpos hlt
    rcases lt_or_gt_of_ne hne with hx' | hx'
    · have h1 : RHTower.xi (1 - ((x : ℂ) + (γ : ℂ) * I)) = 0 := by
        rw [RHTower.xi_one_sub]; exact hx
      have hc : (1 / 2 : ℂ) + ((1 / 2 - x : ℝ) : ℂ) + (γ : ℂ) * I =
          conj (1 - ((x : ℂ) + (γ : ℂ) * I)) := Complex.ext (by simp; ring) (by simp)
      refine hfree (1 / 2 - x) (by linarith) (by linarith) ?_
      rw [hc]
      have h2 : 2 * RHTower.xi (conj (1 - ((x : ℂ) + (γ : ℂ) * I))) = 0 := by
        rw [completedPositiveSystem_riemannZeta.conj_Λ]; simp [h1]
      exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
    · refine hfree (x - 1 / 2) (by linarith) (by linarith) ?_
      rw [show (1 / 2 : ℂ) + ((x - 1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I = (x : ℂ) + (γ : ℂ) * I by
        push_cast; ring]
      exact hx

/-- **RH is the positive central ceiling at every height.** -/
theorem riemannHypothesis_iff_forall_positiveCentralVanishingCeiling :
    RiemannHypothesis ↔ ∀ γ : ℝ, γ ≠ 0 → PositiveCentralVanishingCeiling γ := by
  rw [riemannHypothesis_iff_forall_rationalCentralVanishingCeiling]
  refine forall_congr' fun γ => imp_congr_right fun hγ => ?_
  rw [rationalCentralVanishingCeiling_iff hγ, positiveCentralVanishingCeiling_iff hγ]

end GaloisForLFunctions.BiarithmeticGaugeGeometry
