import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingCalculus
import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep

/-!
# Mixed differences see every zero: coupling completeness

The **mixed difference** of a real test in the log-scales `α, β` is

  `f_{α,β} = f(· − α − β) − f(· − α) − f(· − β) + f = (T_α − 1)(T_β − 1) f`.

Its Weil orbit kernel is the coupling Laplacian of the orbit kernel of `f`:
`K_{f_{α,β}} = L_a L_b K_f` with `a = e^α`, `b = e^β` (`orbitKernel_mixedDiff`). So the Weil form on
mixed-difference tests is the coupling form.

* **Transform** (`paperFT_mixedDiff`): `ĥ_{f_{α,β}}(z) = (e^{izα} − 1)(e^{izβ} − 1) ĥ_f(z)`.
* **Visibility** (`sees_mixedDiff_iff`, `seenRightZeros_mixedDiff`): for `α, β ≠ 0` the multiplier
  never vanishes at an off-line ordinate (`Im z ≠ 0` there), so `f_{α,β}` sees exactly the off-line
  zeros that `f` sees.
* **Coupling completeness** (`negIndex_orbitKernel_mixedDiff`, `negIndex_lap_lap_zetaKernel`): the
  coupling form has the same negative index as the kernel, `κ(L_a L_b K_ζ) = κ(K_ζ)` for all
  `a, b ≠ 1`, although `L_a L_b` annihilates every kernel that is coupling-free across subgroups
  containing `a` and `b` (`lap_lap_eq_zero_of_coupling_eq_zero`). In particular RH holds iff the
  coupling form of `ζ` is positive definite (`riemannHypothesis_iff_negIndex_lap_lap_zetaKernel`).
-/

open Complex Filter Topology
open scoped ComplexConjugate
open Zeta23
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (cx realTests paperFT_translate rightZeros)
open GaloisForLFunctions.ArithmeticOrientationGeometry (Sees seenRightZeros)
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

/-! ### Mixed differences of real tests -/

/-- The mixed difference `f(· − α − β) − f(· − α) − f(· − β) + f`. -/
def mixedDiff (α β : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => f (x - α - β) - f (x - α) - f (x - β) + f x

theorem shift_mem_realTests {f : ℝ → ℝ} (hf : f ∈ realTests) (c : ℝ) :
    (fun x => f (x - c)) ∈ realTests :=
  ⟨hf.1.comp (contDiff_id.sub contDiff_const), hf.2.comp_homeomorph (Homeomorph.subRight c)⟩

theorem mixedDiff_mem_realTests {f : ℝ → ℝ} (hf : f ∈ realTests) (α β : ℝ) :
    mixedDiff α β f ∈ realTests := by
  have h := realTests.add_mem (realTests.sub_mem (realTests.sub_mem
    (shift_mem_realTests hf (α + β)) (shift_mem_realTests hf α)) (shift_mem_realTests hf β)) hf
  convert h using 1
  funext x
  simp [mixedDiff, sub_sub]

private theorem integrable_paperFT_kernel {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (z : ℂ) : MeasureTheory.Integrable fun u : ℝ => g u * cexp (I * z * u) :=
  (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right

/-- **The transform of a mixed difference**: `(e^{izα} − 1)(e^{izβ} − 1) ĥ_f(z)`. -/
theorem paperFT_mixedDiff {f : ℝ → ℝ} (hf : f ∈ realTests) (α β : ℝ) (z : ℂ) :
    paperFT (cx (mixedDiff α β f)) z =
      (cexp (I * z * α) - 1) * (cexp (I * z * β) - 1) * paperFT (cx f) z := by
  set g := cx f
  have hgc : Continuous g := (ArithmeticCastelnuovoSeveri.cx_contDiff hf.1).continuous
  have hgs : HasCompactSupport g := ArithmeticCastelnuovoSeveri.cx_hasCompactSupport hf.2
  have hT : ∀ c : ℝ, MeasureTheory.Integrable fun u : ℝ => ArithmeticCastelnuovoSeveri.translate c g u * cexp (I * z * u) :=
    fun c => integrable_paperFT_kernel (hgc.comp (continuous_id.sub continuous_const))
      (hgs.comp_homeomorph (Homeomorph.subRight c)) z
  have hsplit : (fun u : ℝ => cx (mixedDiff α β f) u * cexp (I * z * u)) = fun u =>
      ArithmeticCastelnuovoSeveri.translate (α + β) g u * cexp (I * z * u) - ArithmeticCastelnuovoSeveri.translate α g u * cexp (I * z * u) -
        ArithmeticCastelnuovoSeveri.translate β g u * cexp (I * z * u) + g u * cexp (I * z * u) := by
    funext u
    simp only [ArithmeticCastelnuovoSeveri.cx, mixedDiff, ArithmeticCastelnuovoSeveri.translate, g, sub_sub]
    push_cast
    ring
  have iAB : MeasureTheory.Integrable fun u : ℝ =>
      ArithmeticCastelnuovoSeveri.translate (α + β) g u * cexp (I * z * u) -
        ArithmeticCastelnuovoSeveri.translate α g u * cexp (I * z * u) := (hT _).sub (hT _)
  have iABC : MeasureTheory.Integrable fun u : ℝ =>
      ArithmeticCastelnuovoSeveri.translate (α + β) g u * cexp (I * z * u) -
        ArithmeticCastelnuovoSeveri.translate α g u * cexp (I * z * u) -
          ArithmeticCastelnuovoSeveri.translate β g u * cexp (I * z * u) := iAB.sub (hT _)
  rw [paperFT, hsplit, MeasureTheory.integral_add iABC (integrable_paperFT_kernel hgc hgs z),
    MeasureTheory.integral_sub iAB (hT _), MeasureTheory.integral_sub (hT _) (hT _)]
  rw [← paperFT, ← paperFT, ← paperFT, ← paperFT, paperFT_translate, paperFT_translate,
    paperFT_translate]
  push_cast
  rw [mul_add, Complex.exp_add]
  ring

/-- `e^{izα} ≠ 1` when `α ≠ 0` and `z` is not real. -/
theorem cexp_I_mul_ne_one {z : ℂ} (hz : z.im ≠ 0) {α : ℝ} (hα : α ≠ 0) :
    cexp (I * z * α) ≠ 1 := by
  intro h
  have hn := congrArg (fun w => ‖w‖) h
  simp only [Complex.norm_exp, norm_one] at hn
  have hre : (I * z * α).re = -(z.im * α) := by simp
  rw [hre, Real.exp_eq_one_iff, neg_eq_zero] at hn
  exact mul_ne_zero hz hα hn

theorem im_gammaOf (ρ : ℂ) : (gammaOf ρ).im = -(ρ.re - 1 / 2) := by
  simp [gammaOf, Complex.div_I]

/-- **Mixed differences see exactly the off-line zeros the test sees.** -/
theorem sees_mixedDiff_iff {f : ℝ → ℝ} (hf : f ∈ realTests) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0)
    {ρ : ℂ} (hρ : ρ.re ≠ 1 / 2) : Sees (mixedDiff α β f) ρ ↔ Sees f ρ := by
  have him : (gammaOf ρ).im ≠ 0 := by
    rw [im_gammaOf]; intro h; exact hρ (by linarith)
  have him' : (conj (gammaOf ρ)).im ≠ 0 := by rw [Complex.conj_im]; exact neg_ne_zero.mpr him
  have hM : ∀ z : ℂ, z.im ≠ 0 → (cexp (I * z * α) - 1) * (cexp (I * z * β) - 1) ≠ 0 :=
    fun z hz => mul_ne_zero (sub_ne_zero.mpr (cexp_I_mul_ne_one hz hα))
      (sub_ne_zero.mpr (cexp_I_mul_ne_one hz hβ))
  unfold Sees
  rw [paperFT_mixedDiff hf, paperFT_mixedDiff hf]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨right_ne_zero_of_mul h1, right_ne_zero_of_mul h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_ne_zero (hM _ him) h1, mul_ne_zero (hM _ him') h2⟩

theorem seenRightZeros_mixedDiff (Z : ZeroConfig) {f : ℝ → ℝ} (hf : f ∈ realTests) {α β : ℝ}
    (hα : α ≠ 0) (hβ : β ≠ 0) : seenRightZeros Z (mixedDiff α β f) = seenRightZeros Z f := by
  ext ρ
  simp only [seenRightZeros, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (sees_mixedDiff_iff hf hα hβ (by linarith)).mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (sees_mixedDiff_iff hf hα hβ (by linarith)).mpr h3⟩

/-- **Coupling completeness on configurations.** The orbit kernel of a mixed difference has the
same negative index as the orbit kernel of the test. -/
theorem negIndex_orbitKernel_mixedDiff (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) {α β : ℝ} (hα : α ≠ 0) (hβ : β ≠ 0) :
    negIndex (orbitKernel Z (mixedDiff α β f)) = negIndex (orbitKernel Z f) := by
  rw [negIndex_orbitKernel Z hZ (mixedDiff_mem_realTests hf α β), negIndex_orbitKernel Z hZ hf,
    seenRightZeros_mixedDiff Z hf hα hβ]

/-! ### The orbit kernel of a mixed difference is the coupling Laplacian -/

/-- The orbit kernel as an exponential sum over the zeros. -/
theorem orbitKernel_eq_tsum (Z : ZeroConfig) (f : ℝ → ℝ) (u : HeckeLattice) :
    orbitKernel Z f u = ∑' ρ : Z.carrier, cexp (-(scale heckeLogScale u : ℂ) * ((ρ : ℂ) - 1 / 2)) *
      Z.Wsummand (cx f) (cx f) ρ := by
  rw [orbitKernel_eq, W_shiftTest_shiftTest]
  refine tsum_congr fun ρ => ?_
  congr 2
  push_cast; ring

theorem summable_cexp_mul_Wsummand (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (c : ℝ) :
    Summable fun ρ : Z.carrier => cexp ((c : ℂ) * ((ρ : ℂ) - 1 / 2)) * Z.Wsummand (cx f) (cx f) ρ := by
  have hs := ArithmeticCastelnuovoSeveri.summable_norm_Wsummand Z hZ
    (ArithmeticCastelnuovoSeveri.cx_contDiff hf.1) (ArithmeticCastelnuovoSeveri.cx_hasCompactSupport hf.2)
    (ArithmeticCastelnuovoSeveri.cx_contDiff hf.1) (ArithmeticCastelnuovoSeveri.cx_hasCompactSupport hf.2)
  refine Summable.of_norm_bounded (hs.mul_left (Real.exp (|c| / 2))) fun ρ => ?_
  rw [norm_mul, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hstrip := Z.strip ρ.1 ρ.2
  have hre : ((c : ℂ) * ((ρ : ℂ) - 1 / 2)).re = c * ((ρ : ℂ).re - 1 / 2) := by simp
  rw [hre]
  have h1 : |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  calc c * ((ρ : ℂ).re - 1 / 2) ≤ |c * ((ρ : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |c| * |(ρ : ℂ).re - 1 / 2| := abs_mul _ _
    _ ≤ |c| * (1 / 2) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |c| / 2 := by ring

/-- The Weil summand of a mixed difference: the summand of `f` times
`(2 − e^{αs} − e^{−αs})(2 − e^{βs} − e^{−βs})`, `s = ρ − 1/2`. -/
theorem Wsummand_mixedDiff (Z : ZeroConfig) {f : ℝ → ℝ} (hf : f ∈ realTests) (α β : ℝ) (ρ : ℂ) :
    Z.Wsummand (cx (mixedDiff α β f)) (cx (mixedDiff α β f)) ρ =
      (2 - cexp (α * (ρ - 1 / 2)) - cexp (-(α * (ρ - 1 / 2)))) *
        (2 - cexp (β * (ρ - 1 / 2)) - cexp (-(β * (ρ - 1 / 2)))) * Z.Wsummand (cx f) (cx f) ρ := by
  have hIg : I * gammaOf ρ = ρ - 1 / 2 := by rw [gammaOf, mul_div_cancel₀ _ I_ne_zero]
  have hc : ∀ c : ℝ, (starRingEnd ℂ) (cexp (I * (starRingEnd ℂ) (gammaOf ρ) * c)) =
      cexp (-(c * (ρ - 1 / 2))) := fun c => by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
    rw [← hIg]; ring
  have hd : ∀ c : ℝ, cexp (I * gammaOf ρ * c) = cexp (c * (ρ - 1 / 2)) := fun c => by
    congr 1; rw [← hIg]; ring
  simp only [ZeroConfig.Wsummand, paperFT_mixedDiff hf, map_mul, map_sub, map_one, hc, hd]
  have hα : cexp (α * (ρ - 1 / 2)) * cexp (-(α * (ρ - 1 / 2))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hβ : cexp (β * (ρ - 1 / 2)) * cexp (-(β * (ρ - 1 / 2))) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination (↑(Z.mult ρ) * paperFT (cx f) (gammaOf ρ) *
    (starRingEnd ℂ) (paperFT (cx f) ((starRingEnd ℂ) (gammaOf ρ)))) *
    ((cexp (β * (ρ - 1 / 2)) - 1) * (cexp (-(β * (ρ - 1 / 2))) - 1) * hα +
      (2 - cexp (α * (ρ - 1 / 2)) - cexp (-(α * (ρ - 1 / 2)))) * hβ)

/-- **The orbit kernel of a mixed difference is the coupling Laplacian of the orbit kernel.** -/
theorem orbitKernel_mixedDiff (Z : ZeroConfig) (hZ : TemperedConfig Z) {f : ℝ → ℝ}
    (hf : f ∈ realTests) (a b : HeckeLattice) :
    orbitKernel Z (mixedDiff (scale heckeLogScale a) (scale heckeLogScale b) f) =
      lap a (lap b (orbitKernel Z f)) := by
  funext w
  set α := scale heckeLogScale a
  set β := scale heckeLogScale b
  set t := scale heckeLogScale w
  set W : Z.carrier → ℂ := fun ρ => Z.Wsummand (cx f) (cx f) ρ
  have hK : ∀ v : HeckeLattice, orbitKernel Z f v =
      ∑' ρ : Z.carrier, cexp ((-(scale heckeLogScale v) : ℝ) * ((ρ : ℂ) - 1 / 2)) * W ρ :=
    fun v => by rw [orbitKernel_eq_tsum]; push_cast; rfl
  have hS : ∀ c : ℝ, HasSum (fun ρ : Z.carrier => cexp ((c : ℂ) * ((ρ : ℂ) - 1 / 2)) * W ρ)
      (∑' ρ : Z.carrier, cexp ((c : ℂ) * ((ρ : ℂ) - 1 / 2)) * W ρ) :=
    fun c => (summable_cexp_mul_Wsummand Z hZ hf c).hasSum
  rw [lap_lap_apply]
  simp only [hK, scale_mul, scale_inv]
  have hsum := (((((((((hS (-t)).mul_left 4).sub ((hS (-(t + α))).mul_left 2)).sub
    ((hS (-(t + -α))).mul_left 2)).sub ((hS (-(t + β))).mul_left 2)).sub
    ((hS (-(t + -β))).mul_left 2)).add (hS (-(t + α + β)))).add (hS (-(t + α + -β)))).add
    (hS (-(t + -α + β)))).add (hS (-(t + -α + -β)))
  rw [← hsum.tsum_eq, orbitKernel_eq_tsum]
  refine tsum_congr fun ρ => ?_
  rw [Wsummand_mixedDiff Z hf]
  set s : ℂ := (ρ : ℂ) - 1 / 2
  simp only [W]
  push_cast
  have e1 : cexp (-((t : ℂ) + α) * s) = cexp (-(t : ℂ) * s) * cexp (-((α : ℂ) * s)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : cexp (-((t : ℂ) + -α) * s) = cexp (-(t : ℂ) * s) * cexp ((α : ℂ) * s) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e3 : cexp (-((t : ℂ) + β) * s) = cexp (-(t : ℂ) * s) * cexp (-((β : ℂ) * s)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e4 : cexp (-((t : ℂ) + -β) * s) = cexp (-(t : ℂ) * s) * cexp ((β : ℂ) * s) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e5 : cexp (-((t : ℂ) + α + β) * s) =
      cexp (-(t : ℂ) * s) * cexp (-((α : ℂ) * s)) * cexp (-((β : ℂ) * s)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e6 : cexp (-((t : ℂ) + α + -β) * s) =
      cexp (-(t : ℂ) * s) * cexp (-((α : ℂ) * s)) * cexp ((β : ℂ) * s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e7 : cexp (-((t : ℂ) + -α + β) * s) =
      cexp (-(t : ℂ) * s) * cexp ((α : ℂ) * s) * cexp (-((β : ℂ) * s)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have e8 : cexp (-((t : ℂ) + -α + -β) * s) =
      cexp (-(t : ℂ) * s) * cexp ((α : ℂ) * s) * cexp ((β : ℂ) * s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  ring

/-! ### Coupling completeness for `ζ` -/

theorem scale_ne_zero {a : HeckeLattice} (ha : a ≠ 1) : scale heckeLogScale a ≠ 0 := fun h =>
  ha (scale_heckeLogScale_injective (h.trans (by simp [scale])))

/-- **The coupling form of `ζ` carries the whole index**: `κ(L_a L_b K_ζ) = κ(K_ζ)` for `a, b ≠ 1`. -/
theorem negIndex_lap_lap_zetaKernel {a b : HeckeLattice} (ha : a ≠ 1) (hb : b ≠ 1) :
    negIndex (lap a (lap b zetaKernel)) = negIndex zetaKernel := by
  rw [zetaKernel, ← orbitKernel_mixedDiff _ SquareRootThreshold.temperedConfig_zetaZeroConfig
      cubicSpline_mem_realTests,
    negIndex_orbitKernel_mixedDiff _ SquareRootThreshold.temperedConfig_zetaZeroConfig
      cubicSpline_mem_realTests
      (scale_ne_zero ha) (scale_ne_zero hb)]

/-- **RH is positivity of the coupling form**, for any pair of scales `a, b ≠ 1`. -/
theorem riemannHypothesis_iff_negIndex_lap_lap_zetaKernel {a b : HeckeLattice} (ha : a ≠ 1)
    (hb : b ≠ 1) : RiemannHypothesis ↔ negIndex (lap a (lap b zetaKernel)) = 0 := by
  rw [negIndex_lap_lap_zetaKernel ha hb]
  exact riemannHypothesis_iff_negIndex_zetaKernel_eq_zero

end GaloisForLFunctions.ArithmeticCouplingTheory
