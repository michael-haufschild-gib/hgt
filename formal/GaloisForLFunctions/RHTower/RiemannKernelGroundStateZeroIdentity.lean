import GaloisForLFunctions.RHTower.WeilFullConeExtremePoint
import GaloisForLFunctions.RHTower.WeilMarginSuperexponentialLaw

/-!
# Weil's zero sum in the ground-state coordinates of Riemann's kernel

Riemann's kernel `Φ` (with `ξ(s) = ∫ Φ(x) e^{(s-1/2)x} dx`) is positive and its transform
vanishes at every nontrivial zero `ρ`, on the critical line or not
(`riemannPhiTransform_eq_zero_of_nontrivial`).
Writing a test function as `f = Φh` (`h` real, continuous, compactly supported) and expanding
`(h(x) - h(y))² = h(x)² - 2h(x)h(y) + h(y)²`, the square terms are killed by
`∫ Φ e^{±(ρ-1/2)x} = 0`, so each summand of Weil's form becomes a difference energy:

`m_ρ ĥ_f(γ_ρ)\overline{ĥ_f(\bar γ_ρ)} = -(m_ρ/2) ∫∫ Φ(x)Φ(y)(h(x)-h(y))² e^{(ρ-1/2)(x-y)} dx dy`

(`wsummand_riemannPhi_mul`), and summing over the zeros
`W(Φh, Φh) = Σ_ρ -(m_ρ/2) ∫∫ Φ(x)Φ(y)(h(x)-h(y))² e^{(ρ-1/2)(x-y)}` (`weil_riemannPhi_mul_eq_tsum`).

This is the zero side of the ground-state (Allegretto–Piepenbrink) transform of the Weil form at
the radical vector `Φ`: on the arithmetic side the pole terms become the variances of `h` under the
tilted laws `Φe^{±x/2}/ξ(1)`, and the prime terms become nonnegative jump energies of `h`.
-/

open Complex MeasureTheory
open Zeta23

namespace RHTower.RiemannKernelGroundState

noncomputable section

local notation "Φ" => RHTower.riemannPhiKernel

/-- `x ↦ e^{(s-1/2)x}Φ(x)` is integrable for every complex `s`. -/
theorem integrable_cexp_mul_riemannPhiKernel (s : ℂ) :
    Integrable fun x : ℝ => Complex.exp ((s - 1 / 2) * x) * Φ x := by
  have h := RHTower.integrable_modXiIntegrand (F := Bottcher.thetaThree) (c := 1)
    (M := RHTower.jacobiThetaTailConstant) RHTower.thetaThree_differentiableOn
    RHTower.thetaThree_axis RHTower.thetaThree_cuspDecay (I * (s - 1 / 2))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  unfold RHTower.modXiIntegrand RHTower.riemannPhiKernel
  congr 2
  ring_nf; rw [Complex.I_sq]; ring

/-- At a nontrivial zero `ρ`, `∫ e^{(ρ-1/2)x}Φ(x) dx = 0`. -/
theorem integral_cexp_mul_riemannPhiKernel_eq_zero {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ∫ x : ℝ, Complex.exp ((ρ - 1 / 2) * x) * Φ x = 0 :=
  RHTower.riemannPhiTransform_eq_zero_of_nontrivial hρ.1 hρ.2.1 hρ.2.2

/-- At a nontrivial zero `ρ`, also `∫ e^{-(ρ-1/2)x}Φ(x) dx = 0` (`Φ` is even). -/
theorem integral_cexp_neg_mul_riemannPhiKernel_eq_zero {ρ : ℂ} (hρ : IsNontrivialZero ρ) :
    ∫ x : ℝ, Complex.exp (-(ρ - 1 / 2) * x) * Φ x = 0 := by
  have h := integral_neg_eq_self (fun x : ℝ => Complex.exp ((ρ - 1 / 2) * x) * Φ x) volume
  rw [integral_cexp_mul_riemannPhiKernel_eq_zero hρ] at h
  rw [← h]
  congr 1; funext x
  rw [RHTower.riemannPhiKernel_neg]; push_cast; ring_nf

/-- **Ground-state identity at one zero.** For a nontrivial zero `ρ` and a real continuous compactly
supported `h`, with `c = ρ - 1/2`,
`(∫Φhe^{cx})(∫Φhe^{-cy}) = -½∫∫Φ(x)Φ(y)(h(x)-h(y))²e^{c(x-y)}`.
The square terms `h(x)²`, `h(y)²` drop out because `∫Φe^{±cx} = 0`. -/
theorem groundState_zero_identity {ρ : ℂ} (hρ : IsNontrivialZero ρ) {h : ℝ → ℝ}
    (hh : Continuous h) (hc : HasCompactSupport h) :
    (∫ x : ℝ, Φ x * (h x : ℂ) * Complex.exp ((ρ - 1 / 2) * x)) *
        (∫ y : ℝ, Φ y * (h y : ℂ) * Complex.exp (-(ρ - 1 / 2) * y))
      = -(1 / 2) * ∫ x : ℝ, ∫ y : ℝ, Φ x * Φ y * (((h x - h y) ^ 2 : ℝ) : ℂ)
          * Complex.exp ((ρ - 1 / 2) * (x - y)) := by
  set c : ℂ := ρ - 1 / 2 with hcdef
  obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hc
  set a : ℝ → ℂ := fun x => Complex.exp (c * x) * Φ x with ha
  set b : ℝ → ℂ := fun y => Complex.exp (-c * y) * Φ y with hb
  have hia : Integrable a := integrable_cexp_mul_riemannPhiKernel ρ
  have hib : Integrable b := by
    have := integrable_cexp_mul_riemannPhiKernel (1 - ρ)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hb, hcdef]; congr 2; ring
  have hza : ∫ x, a x = 0 := integral_cexp_mul_riemannPhiKernel_eq_zero hρ
  have hzb : ∫ y, b y = 0 := by
    simp only [hb, hcdef]; exact integral_cexp_neg_mul_riemannPhiKernel_eq_zero hρ
  have hmeas : Continuous fun x : ℝ => ((h x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hh
  have hbd : ∀ x, ‖((h x : ℝ) : ℂ)‖ ≤ C := fun x => by
    rw [Complex.norm_real]; exact hC x
  have hbd2 : ∀ x, ‖((h x : ℝ) : ℂ) ^ 2‖ ≤ C ^ 2 := fun x => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hbd x) 2
  have hiah : Integrable fun x => ((h x : ℝ) : ℂ) * a x :=
    hia.bdd_mul hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hiah2 : Integrable fun x => ((h x : ℝ) : ℂ) ^ 2 * a x :=
    hia.bdd_mul (hmeas.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall hbd2)
  have hibh : Integrable fun y => ((h y : ℝ) : ℂ) * b y :=
    hib.bdd_mul hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbd)
  have hibh2 : Integrable fun y => ((h y : ℝ) : ℂ) ^ 2 * b y :=
    hib.bdd_mul (hmeas.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall hbd2)
  set J : ℂ := ∫ x, ((h x : ℝ) : ℂ) * a x with hJ
  set K : ℂ := ∫ y, ((h y : ℝ) : ℂ) * b y with hK
  set I₂ : ℂ := ∫ y, ((h y : ℝ) : ℂ) ^ 2 * b y with hI₂
  -- the inner integral
  have hinner : ∀ x : ℝ, (∫ y : ℝ, Φ x * Φ y * (((h x - h y) ^ 2 : ℝ) : ℂ)
      * Complex.exp (c * (x - y))) = a x * (I₂ - 2 * ((h x : ℝ) : ℂ) * K) := by
    intro x
    have hpt : ∀ y : ℝ, Φ x * Φ y * (((h x - h y) ^ 2 : ℝ) : ℂ) * Complex.exp (c * (x - y))
        = ((h x : ℝ) : ℂ) ^ 2 * a x * b y + a x * (((h y : ℝ) : ℂ) ^ 2 * b y)
          - 2 * ((h x : ℝ) : ℂ) * a x * (((h y : ℝ) : ℂ) * b y) := by
      intro y
      simp only [ha, hb]
      rw [show c * ((x : ℂ) - y) = c * x + -c * y by ring, Complex.exp_add]
      push_cast; ring
    have i1 : Integrable fun y => ((h x : ℝ) : ℂ) ^ 2 * a x * b y := hib.const_mul _
    have i2 : Integrable fun y => a x * (((h y : ℝ) : ℂ) ^ 2 * b y) := hibh2.const_mul _
    have i3 : Integrable fun y => 2 * ((h x : ℝ) : ℂ) * a x * (((h y : ℝ) : ℂ) * b y) :=
      hibh.const_mul _
    have i12 : Integrable fun y => ((h x : ℝ) : ℂ) ^ 2 * a x * b y
        + a x * (((h y : ℝ) : ℂ) ^ 2 * b y) := i1.add i2
    simp_rw [hpt]
    rw [integral_sub i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
      integral_const_mul, hzb]
    ring
  simp_rw [hinner]
  have hout : (fun x => a x * (I₂ - 2 * ((h x : ℝ) : ℂ) * K))
      = fun x => I₂ * a x - (2 * K) * (((h x : ℝ) : ℂ) * a x) := by
    funext x; ring
  rw [hout, integral_sub (hia.const_mul _) (hiah.const_mul _), integral_const_mul,
    integral_const_mul, hza]
  have hL : (∫ x : ℝ, Φ x * (h x : ℂ) * Complex.exp (c * x)) = J := by
    simp only [hJ, ha]; congr 1; funext x; ring
  have hR : (∫ y : ℝ, Φ y * (h y : ℂ) * Complex.exp (-c * y)) = K := by
    simp only [hK, hb]; congr 1; funext y; ring
  rw [hL, hR]
  ring

/-- `paperFT (Φh)` at `γ_ρ` is the Laplace integral `∫Φhe^{(ρ-1/2)x}`. -/
theorem paperFT_riemannPhi_mul_gammaOf (ρ : ℂ) (h : ℝ → ℝ) :
    paperFT (fun u => Φ u * (h u : ℂ)) (gammaOf ρ)
      = ∫ x : ℝ, Φ x * (h x : ℂ) * Complex.exp ((ρ - 1 / 2) * x) := by
  unfold paperFT gammaOf
  congr 1; funext x
  congr 2
  field_simp

/-- The conjugated second factor of the Weil summand is `∫Φhe^{-(ρ-1/2)y}`. -/
theorem conj_paperFT_riemannPhi_mul_conj_gammaOf (ρ : ℂ) (h : ℝ → ℝ) :
    (starRingEnd ℂ) (paperFT (fun u => Φ u * (h u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ)))
      = ∫ y : ℝ, Φ y * (h y : ℂ) * Complex.exp (-(ρ - 1 / 2) * y) := by
  unfold paperFT
  rw [← integral_conj]
  congr 1; funext y
  rw [map_mul, map_mul, ← Complex.exp_conj, RHTower.riemannPhiKernel_eq_ofReal,
    Complex.conj_ofReal, Complex.conj_ofReal]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal, gammaOf]
  field_simp

/-- **The Weil summand in ground-state coordinates.** At every nontrivial zero `ρ` and for every
real continuous compactly supported `h`, the summand `m_ρ ĥ_f(γ_ρ)\overline{ĥ_f(\bar γ_ρ)}` of
`f = Φh` equals `-(m_ρ/2)∫∫Φ(x)Φ(y)(h(x)-h(y))²e^{(ρ-1/2)(x-y)}`. -/
theorem wsummand_riemannPhi_mul {ρ : ℂ} (hρ : IsNontrivialZero ρ) {h : ℝ → ℝ}
    (hh : Continuous h) (hc : HasCompactSupport h) (Z : ZeroConfig) :
    Z.Wsummand (fun u => Φ u * (h u : ℂ)) (fun u => Φ u * (h u : ℂ)) ρ
      = -((Z.mult ρ : ℂ) / 2) * ∫ x : ℝ, ∫ y : ℝ, Φ x * Φ y * (((h x - h y) ^ 2 : ℝ) : ℂ)
          * Complex.exp ((ρ - 1 / 2) * (x - y)) := by
  unfold ZeroConfig.Wsummand
  rw [paperFT_riemannPhi_mul_gammaOf, mul_assoc, conj_paperFT_riemannPhi_mul_conj_gammaOf,
    groundState_zero_identity hρ hh hc]
  ring

/-- **Weil's zero sum in ground-state coordinates.** For `f = Φh` with `h` real, continuous and
compactly supported, `W(f,f) = Σ_ρ -(m_ρ/2)∫∫Φ(x)Φ(y)(h(x)-h(y))²e^{(ρ-1/2)(x-y)}`. -/
theorem weil_riemannPhi_mul_eq_tsum {h : ℝ → ℝ} (hh : Continuous h) (hc : HasCompactSupport h) :
    zetaZeroConfig.W (fun u => Φ u * (h u : ℂ)) (fun u => Φ u * (h u : ℂ))
      = ∑' ρ : zetaZeroConfig.carrier, -((zetaZeroConfig.mult ρ : ℂ) / 2) *
          ∫ x : ℝ, ∫ y : ℝ, Φ x * Φ y * (((h x - h y) ^ 2 : ℝ) : ℂ)
            * Complex.exp (((ρ : ℂ) - 1 / 2) * (x - y)) := by
  unfold ZeroConfig.W
  congr 1; funext ρ
  have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
  exact wsummand_riemannPhi_mul hρ hh hc zetaZeroConfig

end

end RHTower.RiemannKernelGroundState
