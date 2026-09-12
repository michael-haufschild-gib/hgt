import GaloisForLFunctions.RHTower.MobiusThetaNativeBoundarySurvival
import GaloisForLFunctions.HTGeometry.RiemannZetaMeromorphic
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Poles retained by the original native Mellin tail

The order-zero first collar agrees on its admitted integral region with an explicit
meromorphic continuation. At every original Xi divisor, sufficiently large native depths
retain the entire zero multiplicity as a pole, for every finite Möbius prefix. The leading
Laurent coefficient is independent of that prefix, even when the prefix changes with depth;
its depth-normalized limit is explicitly nonzero.

This is local pole data for the actual admitted source. It does not identify a continued
value with an integral outside its admission domain, supply a global contour shift, or prove
agreement of the fixed quadratic readers. These poles also occur at critical-line zeros.
-/

set_option autoImplicit false
open Complex Filter Topology MeasureTheory ArithmeticFunction
open scoped Moebius LSeries.notation
namespace RHTower
noncomputable section

/-- Scalar numerator fixed by the original order-zero native Mellin integral. -/
def mobiusThetaNativeMellinNumerator (m : ℕ+) (s : ℂ) : ℂ :=
  (m : ℂ)⁻¹ * XiC (mobiusThetaNativeFixedMellinParameter s m)

/-- Literal finite prefix, including the original zero-index convention. -/
def mobiusThetaNativeMellinPrefix (p : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range p, LSeries.term (↗(μ : ArithmeticFunction ℤ)) s n

/-- Meromorphic expression forced by the admitted original native tail. -/
def mobiusThetaNativeTailContinuation (p : ℕ) (m : ℕ+) (s : ℂ) : ℂ :=
  mobiusThetaNativeMellinNumerator m s / riemannZeta s -
    mobiusThetaNativeMellinPrefix p s * mobiusThetaNativeMellinNumerator m s

/-- Agreement with the literal first-collar Mellin integral on its open admitted region. -/
theorem mobiusThetaNativeTailContinuation_hasMellin
    {p : ℕ} (hp : 0 < p) (m : ℕ+) (s : ℂ)
    (hs : 1 < s.re) (hv : |(mobiusThetaNativeFixedMellinParameter s m).im| < 1) :
    HasMellin (mobiusThetaNativeCollarTail 0 p m) s
      (mobiusThetaNativeTailContinuation p m s) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast m.pos
  have hc := mobiusThetaNativeFixedMellinParameter_centered s m
  have hcre : (m : ℝ) *
      (mobiusThetaCenteredParameter (mobiusThetaNativeFixedMellinParameter s m)).re = s.re := by
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero] using congrArg Complex.re hc
  have hmv : 1 / (m : ℝ) <
      (mobiusThetaCenteredParameter (mobiusThetaNativeFixedMellinParameter s m)).re := by
    apply (div_lt_iff₀ hmpos).2
    rw [mul_comm, hcre]
    exact hs
  have h := mobiusThetaNativeCollarTail_hasMellin_prefix hp 0 m hv hmv
  rw [hc] at h
  convert h using 1
  simp only [mobiusThetaNativeTailContinuation, mobiusThetaNativeMellinNumerator,
    mobiusThetaNativeMellinPrefix, iteratedDeriv_zero, div_eq_mul_inv]
  ring

private theorem nativeNumerator_analytic (m : ℕ+) (s : ℂ) :
    AnalyticAt ℂ (mobiusThetaNativeMellinNumerator m) s := by
  apply AnalyticAt.mul analyticAt_const
  apply (XiC_differentiable.analyticAt _).comp
  dsimp [mobiusThetaNativeFixedMellinParameter]
  fun_prop

private theorem nativePrefix_analytic (p : ℕ) (s : ℂ) :
    AnalyticAt ℂ (mobiusThetaNativeMellinPrefix p) s := by
  have hd : Differentiable ℂ (mobiusThetaNativeMellinPrefix p) := by
    intro z
    apply DifferentiableAt.fun_sum
    intro n hn
    exact (LSeries.hasDerivAt_term (↗(μ : ArithmeticFunction ℤ)) n z).differentiableAt
  exact hd.analyticAt s

private theorem nativeZeta_analytic (rho : XiDivisorSupport) :
    AnalyticAt ℂ riemannZeta (rho : ℂ) :=
  GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta (xiDivisorSupport_ne_one rho)

private theorem nativeZeta_order (rho : XiDivisorSupport) :
    analyticOrderAt riemannZeta (rho : ℂ) = xiSupportMultiplicity rho := by
  rw [← xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
    (xi_divisor_support_re_mem_open_unit rho), xiSupportMultiplicity_eq_analyticOrderAt_toNat]
  exact (ENat.coe_toNat (xi_orderAt_ne_top (rho : ℂ))).symm

theorem mobiusThetaNativeTailContinuation_meromorphicAt
    (p : ℕ) (m : ℕ+) (rho : XiDivisorSupport) :
    MeromorphicAt (mobiusThetaNativeTailContinuation p m) (rho : ℂ) :=
  ((nativeNumerator_analytic m _).meromorphicAt.div (nativeZeta_analytic rho).meromorphicAt).sub
    ((nativePrefix_analytic p _).mul (nativeNumerator_analytic m _)).meromorphicAt

theorem tendsto_mobiusThetaNativeMellinNumerator_scaled (s : ℂ) :
    Tendsto (fun m : ℕ+ => (m : ℂ) * mobiusThetaNativeMellinNumerator m s)
      atTop (𝓝 (1 / 2)) := by
  apply (tendsto_mobiusThetaNativeFixedMellin_scaled s).congr'
  filter_upwards [mobiusThetaNativeFixedMellin_data s] with m hm
  rw [hm.2]
  rfl

private theorem nativeNumerator_ne_zero_cofinal (s : ℂ) :
    ∀ᶠ m : ℕ+ in atTop, mobiusThetaNativeMellinNumerator m s ≠ 0 := by
  have h := (tendsto_mobiusThetaNativeMellinNumerator_scaled s).eventually_ne
    (by norm_num : (1 / 2 : ℂ) ≠ 0)
  filter_upwards [h] with m hm
  exact fun hz => hm (by rw [hz, mul_zero])

private theorem nativePole_data (m : ℕ+) (rho : XiDivisorSupport)
    (hN0 : mobiusThetaNativeMellinNumerator m (rho : ℂ) ≠ 0) (p : ℕ) :
    meromorphicOrderAt (mobiusThetaNativeTailContinuation p m) (rho : ℂ) =
        ((-(xiSupportMultiplicity rho : ℤ)) : WithTop ℤ) ∧
      meromorphicTrailingCoeffAt (mobiusThetaNativeTailContinuation p m) (rho : ℂ) =
        mobiusThetaNativeMellinNumerator m (rho : ℂ) /
          meromorphicTrailingCoeffAt riemannZeta (rho : ℂ) := by
  let N := mobiusThetaNativeMellinNumerator m
  let E : ℂ → ℂ := fun s => mobiusThetaNativeMellinPrefix p s * N s
  have hN : AnalyticAt ℂ N (rho : ℂ) := nativeNumerator_analytic m _
  have hZ := nativeZeta_analytic rho
  have hE : AnalyticAt ℂ E (rho : ℂ) := (nativePrefix_analytic p _).mul hN
  have hF : MeromorphicAt (fun s => N s / riemannZeta s) (rho : ℂ) :=
    hN.meromorphicAt.div hZ.meromorphicAt
  have hFo : meromorphicOrderAt (fun s => N s / riemannZeta s) (rho : ℂ) =
      ((-(xiSupportMultiplicity rho : ℤ)) : WithTop ℤ) := by
    rw [fun_meromorphicOrderAt_div hN.meromorphicAt hZ.meromorphicAt,
      hN.meromorphicOrderAt_eq, hN.analyticOrderAt_eq_zero.mpr hN0,
      hZ.meromorphicOrderAt_eq, nativeZeta_order]
    simp
  have hneg : meromorphicOrderAt (fun s => N s / riemannZeta s) (rho : ℂ) < 0 := by
    rw [hFo]
    have hpos : (0 : ℤ) < xiSupportMultiplicity rho := by
      exact_mod_cast xiSupportMultiplicity_pos rho
    exact_mod_cast neg_neg_of_pos hpos
  constructor
  · change meromorphicOrderAt ((fun s => N s / riemannZeta s) - E) (rho : ℂ) = _
    rw [sub_eq_add_neg,
      meromorphicOrderAt_add_eq_left_of_lt hE.neg.meromorphicAt
        (hneg.trans_le hE.neg.meromorphicOrderAt_nonneg)]
    exact hFo
  · change meromorphicTrailingCoeffAt (fun s => N s / riemannZeta s - E s) (rho : ℂ) = _
    rw [hE.meromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt
      (hneg.trans_le hE.meromorphicOrderAt_nonneg)]
    simp_rw [div_eq_mul_inv]
    change meromorphicTrailingCoeffAt (N * riemannZeta⁻¹) (rho : ℂ) =
      N (rho : ℂ) * (meromorphicTrailingCoeffAt riemannZeta (rho : ℂ))⁻¹
    rw [hN.meromorphicAt.meromorphicTrailingCoeffAt_mul hZ.meromorphicAt.inv,
      hN.meromorphicTrailingCoeffAt_of_ne_zero hN0, meromorphicTrailingCoeffAt_inv]

/-- Every finite prefix leaves the full native pole order and the same leading coefficient.
The cofinal depth condition is independent of the prefix. -/
theorem mobiusThetaNativeTailContinuation_pole_cofinal (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop, ∀ p : ℕ,
      meromorphicOrderAt (mobiusThetaNativeTailContinuation p m) (rho : ℂ) =
          ((-(xiSupportMultiplicity rho : ℤ)) : WithTop ℤ) ∧
        meromorphicTrailingCoeffAt (mobiusThetaNativeTailContinuation p m) (rho : ℂ) =
          mobiusThetaNativeMellinNumerator m (rho : ℂ) /
            meromorphicTrailingCoeffAt riemannZeta (rho : ℂ) := by
  filter_upwards [nativeNumerator_ne_zero_cofinal (rho : ℂ)] with m hm
  exact nativePole_data m rho hm

private theorem nativeZeta_trailing_ne_zero (rho : XiDivisorSupport) :
    meromorphicTrailingCoeffAt riemannZeta (rho : ℂ) ≠ 0 := by
  apply (nativeZeta_analytic rho).meromorphicAt.meromorphicTrailingCoeffAt_ne_zero
  rw [(nativeZeta_analytic rho).meromorphicOrderAt_eq, nativeZeta_order]
  simp

/-- Even an arbitrary moving finite prefix cannot change the depth-normalized leading pole. -/
theorem tendsto_mobiusThetaNativeTailContinuation_scaled_trailing
    (rho : XiDivisorSupport) (p : ℕ+ → ℕ) :
    Tendsto (fun m : ℕ+ => (m : ℂ) *
      meromorphicTrailingCoeffAt (mobiusThetaNativeTailContinuation (p m) m) (rho : ℂ))
      atTop (𝓝 ((1 / 2 : ℂ) / meromorphicTrailingCoeffAt riemannZeta (rho : ℂ))) := by
  apply ((tendsto_mobiusThetaNativeMellinNumerator_scaled (rho : ℂ)).div_const
    (meromorphicTrailingCoeffAt riemannZeta (rho : ℂ))).congr'
  filter_upwards [mobiusThetaNativeTailContinuation_pole_cofinal rho] with m hm
  rw [(hm (p m)).2]
  ring

/-- The original source fixes a nonzero normalized principal coefficient. -/
theorem mobiusThetaNativeTailContinuation_scaled_trailing_ne_zero (rho : XiDivisorSupport) :
    (1 / 2 : ℂ) / meromorphicTrailingCoeffAt riemannZeta (rho : ℂ) ≠ 0 :=
  div_ne_zero (by norm_num) (nativeZeta_trailing_ne_zero rho)

/-- Every original divisor forces a nonremovable native pole, with every finite prefix retained. -/
theorem mobiusThetaNativeTailContinuation_no_finite_limit_cofinal (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop, ∀ p : ℕ,
      ¬ ∃ c : ℂ, Tendsto (mobiusThetaNativeTailContinuation p m) (𝓝[≠] (rho : ℂ)) (𝓝 c) := by
  filter_upwards [mobiusThetaNativeTailContinuation_pole_cofinal rho] with m hm
  intro p
  rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg
    (mobiusThetaNativeTailContinuation_meromorphicAt p m rho), (hm p).1]
  have hpos : (0 : ℤ) < xiSupportMultiplicity rho := by
    exact_mod_cast xiSupportMultiplicity_pos rho
  exact not_le.mpr (by exact_mod_cast neg_neg_of_pos hpos)

end
end RHTower
