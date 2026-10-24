import GaloisForLFunctions.ArithmeticOrientationGeometry.TheCorrespondenceAlgebra
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.SquareRootThreshold.HodgeClassificationOfFiniteOffLineSets
import GaloisForLFunctions.RHTower.WeilPhiDoobPrimeAtoms

/-!
# The scaling datum of a zero configuration

Every tempered zero configuration `Z` (a reflection-symmetric multiset of points of the strip with
`Σ m_ρ/(1 + |γ_ρ|²) < ∞`) carries a scaling datum over `ℝ`: the cycles are `aH + bV + f` with
`f` a real `C²` compactly supported test, the pairing is that of the scaling surface with Weil's
pairing replaced by the zero-side form `Re W_Z(f, g) = Re Σ_ρ m_ρ h_f(γ_ρ) conj h_g(γ̄_ρ)`
(`configSurface`), and the scales act by logarithmic translation (`configScalingDatum`). So the
zeros of `ζ`, the zeros of a curve, those of the golden datum, of a shifted pair or of a cluster
model are all instances of one theory, and the selectivity battery is a list of scaling data.

* **The defect is the zero-side Weil form** (`configSurface_defect_tests`).
* **Translation law** (`Wsummand_scaleShift`). Translating the two tests by `s` and `t` multiplies
  the summand at `ρ` by `e^{(s − t)(ρ − ½)}`; with `s = t` the form is translation invariant.
* **The orbit correlation is an exponential sum over the zeros**
  (`configScalingDatum_orbitCorr_eq`): `c_f(t) = Re Σ_ρ e^{t(ρ − ½)} m_ρ h_f(γ_ρ) conj h_f(γ̄_ρ)`.
  Zeros on the line contribute bounded almost-periodic terms; a zero at depth `δ = Re ρ − ½`
  contributes a term of size `e^{δ t}`.
* **Configurations on the line have the Hodge index** (`configSurface_hodgeIndex_of_onLine`).
* **For `ζ` the explicit formula identifies the two scaling data** (`configWeil_zeta_eq_weilPair`,
  `configSurface_zeta_eq`): the zero-side datum of the nontrivial zeros is the scaling datum of
  `ℤ`, whose pairing is defined from primes, the Gamma factor and the pole.
-/

noncomputable section

open Complex Finset
open scoped ComplexConjugate
open Zeta23

namespace GaloisForLFunctions.ArithmeticOrientationGeometry

open ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig temperedConfig_zetaZeroConfig)

/-! ### The zero-side Weil pairing on real tests -/

/-- The zero-side Weil pairing of two real tests, `Re W_Z(f, g)`. -/
def configWeil (Z : ZeroConfig) (f g : ℝ → ℝ) : ℝ := (Z.W (cx f) (cx g)).re

theorem configWeil_comm (Z : ZeroConfig) (f g : ℝ → ℝ) : configWeil Z f g = configWeil Z g f := by
  rw [configWeil, configWeil, ← W_conj_symm Z (cx f) (cx g), Complex.conj_re]

theorem configWeil_add_left (Z : ZeroConfig) (hZ : TemperedConfig Z) {f₁ f₂ g : ℝ → ℝ}
    (h₁ : f₁ ∈ realTests) (h₂ : f₂ ∈ realTests) (hg : g ∈ realTests) :
    configWeil Z (f₁ + f₂) g = configWeil Z f₁ g + configWeil Z f₂ g := by
  rw [configWeil, cx_add, W_add_left Z hZ (cx_contDiff h₁.1) (cx_hasCompactSupport h₁.2)
    (cx_contDiff h₂.1) (cx_hasCompactSupport h₂.2) (cx_contDiff hg.1) (cx_hasCompactSupport hg.2),
    Complex.add_re, configWeil, configWeil]

theorem configWeil_smul_left (Z : ZeroConfig) (c : ℝ) (f g : ℝ → ℝ) :
    configWeil Z (c • f) g = c * configWeil Z f g := by
  rw [configWeil, cx_smul, W_smul_left, Complex.re_ofReal_mul, configWeil]

/-- The local intersection of two real tests on the configuration surface. -/
def configLocalPair (Z : ZeroConfig) (f g : ℝ → ℝ) : ℝ :=
  poleB f * poleA g + poleA f * poleB g - configWeil Z f g

theorem configLocalPair_comm (Z : ZeroConfig) (f g : ℝ → ℝ) :
    configLocalPair Z f g = configLocalPair Z g f := by
  simp only [configLocalPair, configWeil_comm Z f g]; ring

theorem configLocalPair_add_left (Z : ZeroConfig) (hZ : TemperedConfig Z) {f₁ f₂ g : ℝ → ℝ}
    (h₁ : f₁ ∈ realTests) (h₂ : f₂ ∈ realTests) (hg : g ∈ realTests) :
    configLocalPair Z (f₁ + f₂) g = configLocalPair Z f₁ g + configLocalPair Z f₂ g := by
  simp only [configLocalPair, poleB_add h₁ h₂, poleA_add h₁ h₂, configWeil_add_left Z hZ h₁ h₂ hg]
  ring

theorem configLocalPair_smul_left (Z : ZeroConfig) (c : ℝ) (f g : ℝ → ℝ) :
    configLocalPair Z (c • f) g = c * configLocalPair Z f g := by
  simp only [configLocalPair, poleB_smul, poleA_smul, configWeil_smul_left]; ring

theorem configLocalPair_zero_left (Z : ZeroConfig) (g : ℝ → ℝ) : configLocalPair Z 0 g = 0 := by
  have := configLocalPair_smul_left Z 0 0 g
  simpa using this

/-- The pairing of the configuration surface on `ScalingCycle`. -/
def configPairFun (Z : ZeroConfig) (x y : ScalingCycle) : ℝ :=
  x.1 * y.2.1 + x.2.1 * y.1 + x.1 * poleB y.2.2 + x.2.1 * poleA y.2.2 + y.1 * poleB x.2.2
    + y.2.1 * poleA x.2.2 + configLocalPair Z x.2.2 y.2.2

/-- The pairing of the configuration surface as a bilinear map. -/
def configPair (Z : ZeroConfig) (hZ : TemperedConfig Z) :
    ScalingCycle →ₗ[ℝ] ScalingCycle →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (configPairFun Z)
    (fun x x' y => by
      simp only [configPairFun, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        poleB_add x.2.2.2 x'.2.2.2, poleA_add x.2.2.2 x'.2.2.2,
        configLocalPair_add_left Z hZ x.2.2.2 x'.2.2.2 y.2.2.2]; ring)
    (fun c x y => by
      simp only [configPairFun, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul,
        poleB_smul, poleA_smul, configLocalPair_smul_left]; ring)
    (fun x y y' => by
      simp only [configPairFun, Prod.fst_add, Prod.snd_add, Submodule.coe_add,
        poleB_add y.2.2.2 y'.2.2.2, poleA_add y.2.2.2 y'.2.2.2]
      rw [configLocalPair_comm Z x.2.2, configLocalPair_add_left Z hZ y.2.2.2 y'.2.2.2 x.2.2.2,
        configLocalPair_comm Z y.2.2, configLocalPair_comm Z y'.2.2]; ring)
    (fun c x y => by
      simp only [configPairFun, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul,
        poleB_smul, poleA_smul]
      rw [configLocalPair_comm Z x.2.2, configLocalPair_smul_left, configLocalPair_comm]; ring)

theorem configPair_apply (Z : ZeroConfig) (hZ : TemperedConfig Z) (x y : ScalingCycle) :
    configPair Z hZ x y = configPairFun Z x y := rfl

/-- **The scaling surface of a configuration.** -/
def configSurface (Z : ZeroConfig) (hZ : TemperedConfig Z) : PolarSurface ScalingCycle where
  pair := configPair Z hZ
  pair_comm x y := by
    simp only [configPair_apply, configPairFun, configLocalPair_comm Z x.2.2]; ring
  H := (1, 0, 0)
  V := (0, 1, 0)
  pair_H_H := by
    simp [configPair_apply, configPairFun, poleB_zero, poleA_zero, configLocalPair_zero_left]
  pair_V_V := by
    simp [configPair_apply, configPairFun, poleB_zero, poleA_zero, configLocalPair_zero_left]
  pair_H_V := by
    simp [configPair_apply, configPairFun, poleB_zero, poleA_zero, configLocalPair_zero_left]

section Surface

variable (Z : ZeroConfig) (hZ : TemperedConfig Z)

theorem configSurface_pair_H (x : ScalingCycle) :
    (configSurface Z hZ).pair x (configSurface Z hZ).H = x.2.1 + poleB x.2.2 := by
  simp only [configSurface, configPair_apply, configPairFun, Submodule.coe_zero, poleB_zero,
    poleA_zero]
  rw [configLocalPair_comm, configLocalPair_zero_left]
  ring

theorem configSurface_pair_V (x : ScalingCycle) :
    (configSurface Z hZ).pair x (configSurface Z hZ).V = x.1 + poleA x.2.2 := by
  simp only [configSurface, configPair_apply, configPairFun, Submodule.coe_zero, poleB_zero,
    poleA_zero]
  rw [configLocalPair_comm, configLocalPair_zero_left]
  ring

/-- **The defect of the configuration surface is the zero-side Weil form.** -/
theorem configSurface_defect (x y : ScalingCycle) :
    (configSurface Z hZ).defect x y = configWeil Z x.2.2 y.2.2 := by
  simp only [PolarSurface.defect, PolarSurface.polar, configSurface_pair_H, configSurface_pair_V]
  simp only [configSurface, configPair_apply, configPairFun, configLocalPair]
  ring

theorem configSurface_defect_tests {f g : ℝ → ℝ} (hf : f ∈ realTests) (hg : g ∈ realTests) :
    (configSurface Z hZ).defect (0, 0, ⟨f, hf⟩) (0, 0, ⟨g, hg⟩) = configWeil Z f g :=
  configSurface_defect Z hZ _ _

/-- **Hodge index of the configuration surface** is zero-side Weil positivity on real tests. -/
theorem configSurface_hodgeIndex_iff :
    (configSurface Z hZ).HodgeIndex ↔ ∀ f ∈ realTests, 0 ≤ configWeil Z f f := by
  rw [(configSurface Z hZ).hodgeIndex_iff_castelnuovoSeveri,
    (configSurface Z hZ).castelnuovoSeveri_iff_defect_nonneg]
  constructor
  · intro h f hf
    have := h (0, 0, ⟨f, hf⟩)
    rwa [configSurface_defect] at this
  · intro h x
    rw [configSurface_defect]
    exact h _ x.2.2.2

/-- A configuration on the critical line has the Hodge index. -/
theorem configSurface_hodgeIndex_of_onLine (hon : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2) :
    (configSurface Z hZ).HodgeIndex :=
  (configSurface_hodgeIndex_iff Z hZ).mpr fun f _ =>
    SquareRootThreshold.weil_nonneg_of_onLine Z hon (cx f)

end Surface

/-! ### Translation and the scaling action -/

theorem ofReal_exp_cpow (t : ℝ) (w : ℂ) : ((Real.exp t : ℝ) : ℂ) ^ w = cexp (t * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos t).ne'),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]

theorem paperFT_cx_scaleShift (t : ℝ) (f : ℝ → ℝ) (ρ : ℂ) :
    paperFT (cx (scaleShift t f)) (gammaOf ρ) = cexp (t * (ρ - 1 / 2)) * paperFT (cx f) (gammaOf ρ) := by
  have h := paperFT_scaleShift_gammaOf (Real.exp_pos t) f ρ
  rwa [Real.log_exp, ofReal_exp_cpow] at h

/-- **Translation law.** Translating `f` by `s` and `g` by `t` multiplies the summand at `ρ` by
`e^{(s − t)(ρ − ½)}`. -/
theorem Wsummand_scaleShift (Z : ZeroConfig) (s t : ℝ) (f g : ℝ → ℝ) (ρ : ℂ) :
    Z.Wsummand (cx (scaleShift s f)) (cx (scaleShift t g)) ρ =
      cexp ((s - t) * (ρ - 1 / 2)) * Z.Wsummand (cx f) (cx g) ρ := by
  have hconj : conj (gammaOf ρ) = gammaOf (reflect ρ) := (gammaOf_reflect ρ).symm
  have hexp : cexp (s * (ρ - 1 / 2)) * conj (cexp (t * (reflect ρ - 1 / 2))) =
      cexp ((s - t) * (ρ - 1 / 2)) := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [reflect, map_mul, map_sub, Complex.conj_ofReal, map_one, conj_conj, map_div₀,
      map_ofNat]
    ring
  rw [ZeroConfig.Wsummand, ZeroConfig.Wsummand, hconj, paperFT_cx_scaleShift,
    paperFT_cx_scaleShift, map_mul, ← hexp]
  ring

theorem configWeil_scaleShift (Z : ZeroConfig) (s t : ℝ) (f g : ℝ → ℝ) :
    configWeil Z (scaleShift s f) (scaleShift t g) =
      (∑' ρ : Z.carrier, cexp ((s - t) * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx f) (cx g) ρ).re := by
  rw [configWeil, ZeroConfig.W]
  congr 1
  exact tsum_congr fun ρ => Wsummand_scaleShift Z s t f g ρ

/-- The zero-side form is translation invariant. -/
theorem configWeil_scaleShift_same (Z : ZeroConfig) (t : ℝ) (f g : ℝ → ℝ) :
    configWeil Z (scaleShift t f) (scaleShift t g) = configWeil Z f g := by
  rw [configWeil_scaleShift, sub_self, configWeil, ZeroConfig.W]
  simp

theorem configLocalPair_scaleShift_same (Z : ZeroConfig) (t : ℝ) (f g : ℝ → ℝ) :
    configLocalPair Z (scaleShift t f) (scaleShift t g) = configLocalPair Z f g := by
  simp only [configLocalPair, poleB_scaleShift, poleA_scaleShift, configWeil_scaleShift_same]
  have hexp : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := ScalingDatum.exp_neg_half_mul_exp_half t
  linear_combination (poleB f * poleA g + poleA f * poleB g) * hexp

section Datum

variable (Z : ZeroConfig) (hZ : TemperedConfig Z)

theorem configPair_scalingAction (t : ℝ) (x y : ScalingCycle) :
    (configSurface Z hZ).pair (scalingAction t x) (scalingAction t y) =
      (configSurface Z hZ).pair x y := by
  simp only [configSurface, configPair_apply, configPairFun, scalingAction, LinearMap.coe_mk,
    AddHom.coe_mk, poleB_scaleShift, poleA_scaleShift, configLocalPair_scaleShift_same]
  have hexp : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
    rw [mul_comm]; exact ScalingDatum.exp_neg_half_mul_exp_half t
  linear_combination (x.1 * y.2.1 + x.2.1 * y.1 + x.1 * poleB y.2.2 + x.2.1 * poleA y.2.2 +
    y.1 * poleB x.2.2 + y.2.1 * poleA x.2.2) * hexp

theorem configPair_scalingAction_H (t : ℝ) (x : ScalingCycle) :
    (configSurface Z hZ).pair (scalingAction t x) (configSurface Z hZ).H =
      Real.exp (-t / 2) * (configSurface Z hZ).pair x (configSurface Z hZ).H := by
  rw [configSurface_pair_H, configSurface_pair_H]
  simp only [scalingAction, LinearMap.coe_mk, AddHom.coe_mk, poleB_scaleShift]
  ring

theorem configPair_scalingAction_V (t : ℝ) (x : ScalingCycle) :
    (configSurface Z hZ).pair (scalingAction t x) (configSurface Z hZ).V =
      Real.exp (t / 2) * (configSurface Z hZ).pair x (configSurface Z hZ).V := by
  rw [configSurface_pair_V, configSurface_pair_V]
  simp only [scalingAction, LinearMap.coe_mk, AddHom.coe_mk, poleA_scaleShift]
  ring

/-- **The scaling datum of a tempered configuration**, with logarithmic translation. -/
def configScalingDatum : ScalingDatum ℝ ScalingCycle where
  toPolarSurface := configSurface Z hZ
  scale := AddMonoidHom.id ℝ
  act := scalingAction
  act_zero x := by rw [scalingAction_zero, LinearMap.id_apply]
  act_add := scalingAction_add
  pair_act := configPair_scalingAction Z hZ
  pair_act_H := configPair_scalingAction_H Z hZ
  pair_act_V := configPair_scalingAction_V Z hZ

/-- **The orbit correlation of a configuration is an exponential sum over its zeros.**
`c_f(t) = Re Σ_ρ e^{t(ρ − ½)} m_ρ h_f(γ_ρ) conj h_f(γ̄_ρ)`. -/
theorem configScalingDatum_orbitCorr_eq (x : ScalingCycle) (t : ℝ) :
    (configScalingDatum Z hZ).orbitCorr x t =
      (∑' ρ : Z.carrier, cexp (t * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx x.2.2) (cx x.2.2) ρ).re := by
  rw [ScalingDatum.orbitCorr]
  change (configSurface Z hZ).defect (scalingAction t x) x = _
  rw [configSurface_defect]
  have h := configWeil_scaleShift Z t 0 x.2.2 x.2.2
  rw [scaleShift_zero, Complex.ofReal_zero, sub_zero] at h
  exact h

theorem configScalingDatum_hodgeIndex_iff :
    (configScalingDatum Z hZ).HodgeIndex ↔ ∀ f ∈ realTests, 0 ≤ configWeil Z f f :=
  configSurface_hodgeIndex_iff Z hZ

end Datum

/-! ### `ζ`: the explicit formula identifies the two scaling data -/

/-- **Explicit formula on real tests.** The zero-side pairing of the nontrivial zeros is Weil's
pairing from primes, Gamma factor and pole. -/
theorem configWeil_zeta_eq_weilPair {f g : ℝ → ℝ} (hf : f ∈ realTests) (hg : g ∈ realTests) :
    configWeil zetaZeroConfig f g = weilPair f g := by
  rw [configWeil, weilPair, RHTower.zeta_W_eq_weilFullFunctional_mixed (cx_contDiff hf.1)
    (cx_hasCompactSupport hf.2) (cx_contDiff hg.1) (cx_hasCompactSupport hg.2)]

/-- The configuration surface of the zeros of `ζ` is the scaling surface of `ℤ`. -/
theorem configSurface_zeta_eq :
    configSurface zetaZeroConfig temperedConfig_zetaZeroConfig = scalingSurface := by
  have hpair : configPair zetaZeroConfig temperedConfig_zetaZeroConfig = scalingPair := by
    refine LinearMap.ext₂ fun x y => ?_
    rw [configPair_apply, scalingPair_apply, configPairFun, scalingPairFun, configLocalPair,
      localPair, configWeil_zeta_eq_weilPair x.2.2.2 y.2.2.2]
  simp only [configSurface, scalingSurface, hpair]

end GaloisForLFunctions.ArithmeticOrientationGeometry
