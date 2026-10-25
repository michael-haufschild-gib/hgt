import GaloisForLFunctions.ArithmeticOrientationTheory.TheOffLineZerosObstructTheMoebiusReceiver
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Interior jets of critical Wiener series

Every strict-interior jet is complex linear on the full critical Wiener
algebra. Local analytic order adds under products and scales under powers.
-/
section

noncomputable section
set_option autoImplicit false
open Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt TransHorizonIncidenceMechanics

/-- The Dirichlet series of a critical Wiener element is analytic in the strict half-plane. -/
theorem analyticAt_wienerLSeries (a : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : 1 / 2 < s.re) : AnalyticAt ℂ (LSeries (⇑a.toFn)) s := by
  have hr := analyticOnNhd_lSeries_kernel (criticalWiener_rePart a) s hs
  have hi := analyticOnNhd_lSeries_kernel (criticalWiener_imPart a) s hs
  have heq : LSeries (⇑a.toFn) =ᶠ[𝓝 s]
      (fun z => LSeries (cplx (rePart a)) z + I * LSeries (cplx (imPart a)) z) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact lSeries_toFn_eq a hz.le
  exact (hr.add (analyticAt_const.mul hi)).congr heq.symm

/-- Half-plane evaluation of a Wiener series is an algebra character. -/
theorem wienerLSeries_eq_character (a : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    LSeries (⇑a.toFn) s = WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) s hs) a := by
  rw [bohrCharacter_apply, bohrEval_halfPlanePoint]

theorem wienerLSeries_add (a b : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    LSeries (⇑(a + b).toFn) s = LSeries (⇑a.toFn) s + LSeries (⇑b.toFn) s := by
  simp only [wienerLSeries_eq_character _ hs, map_add]

theorem wienerLSeries_smul (c : ℂ) (a : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    LSeries (⇑(c • a).toFn) s = c * LSeries (⇑a.toFn) s := by
  simp only [wienerLSeries_eq_character _ hs, map_smul, smul_eq_mul]

theorem wienerLSeries_mul (a b : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    LSeries (⇑(a * b).toFn) s = LSeries (⇑a.toFn) s * LSeries (⇑b.toFn) s := by
  simp only [wienerLSeries_eq_character _ hs, map_mul]

theorem wienerLSeries_sub_algebraMap (a : WienerAlgebraAt (1 / 2)) (c : ℂ)
    {s : ℂ} (hs : (1 / 2 : ℝ) ≤ s.re) :
    LSeries (⇑(a - algebraMap ℂ (WienerAlgebraAt (1 / 2)) c).toFn) s =
      LSeries (⇑a.toFn) s - c := by
  simp only [wienerLSeries_eq_character _ hs, map_sub, AlgHom.commutes,
    Algebra.algebraMap_self_apply]

/-- Every interior jet is a complex-linear functional on the full critical Wiener algebra. -/
def wienerJetLinear (s : ℂ) (hs : 1 / 2 < s.re) (n : ℕ) :
    WienerAlgebraAt (1 / 2) →ₗ[ℂ] ℂ where
  toFun a := iteratedDeriv n (LSeries (⇑a.toFn)) s
  map_add' a b := by
    have heq : LSeries (⇑(a + b).toFn) =ᶠ[𝓝 s]
        (LSeries (⇑a.toFn) + LSeries (⇑b.toFn)) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
      exact wienerLSeries_add a b hz.le
    rw [(heq.iteratedDeriv n).eq_of_nhds]
    exact iteratedDeriv_add ((analyticAt_wienerLSeries a hs).contDiffAt.of_le le_top)
      ((analyticAt_wienerLSeries b hs).contDiffAt.of_le le_top)
  map_smul' c a := by
    have heq : LSeries (⇑(c • a).toFn) =ᶠ[𝓝 s]
        (fun z => c * LSeries (⇑a.toFn) z) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
      exact wienerLSeries_smul c a hz.le
    rw [(heq.iteratedDeriv n).eq_of_nhds]
    change iteratedDeriv n (fun z => c * LSeries (⇑a.toFn) z) s =
      c * iteratedDeriv n (LSeries (⇑a.toFn)) s
    exact congrFun (iteratedDeriv_const_mul_field c (LSeries (⇑a.toFn)) n) s

/-- Multiplication of Wiener elements adds their local analytic orders. -/
theorem analyticOrderAt_wiener_mul (a b : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : 1 / 2 < s.re) :
    analyticOrderAt (LSeries (⇑(a * b).toFn)) s =
      analyticOrderAt (LSeries (⇑a.toFn)) s + analyticOrderAt (LSeries (⇑b.toFn)) s := by
  have heq : LSeries (⇑(a * b).toFn) =ᶠ[𝓝 s]
      LSeries (⇑a.toFn) * LSeries (⇑b.toFn) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact wienerLSeries_mul a b hz.le
  rw [analyticOrderAt_congr heq]
  exact analyticOrderAt_mul (analyticAt_wienerLSeries a hs) (analyticAt_wienerLSeries b hs)

/-- Powers of a Wiener element multiply its local analytic order. -/
theorem analyticOrderAt_wiener_pow (a : WienerAlgebraAt (1 / 2))
    {s : ℂ} (hs : 1 / 2 < s.re) (n : ℕ) :
    analyticOrderAt (LSeries (⇑(a ^ n).toFn)) s =
      n • analyticOrderAt (LSeries (⇑a.toFn)) s := by
  have heq : LSeries (⇑(a ^ n).toFn) =ᶠ[𝓝 s]
      (LSeries (⇑a.toFn)) ^ n := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    simp only [Pi.pow_apply, wienerLSeries_eq_character _ hz.le, map_pow]
  rw [analyticOrderAt_congr heq]
  exact analyticOrderAt_pow (analyticAt_wienerLSeries a hs) n

/-- A positive point mass has its exact entire Dirichlet exponential. -/
theorem wienerLSeries_pointMass {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    LSeries (⇑(pointMass (σ := 1 / 2) n).toFn) s = (n : ℂ) ^ (-s) := by
  rw [toFn_pointMass, LSeries, tsum_eq_single n]
  · rw [LSeries.term_of_ne_zero hn, pointMassFn_apply, if_pos ⟨hn, rfl⟩,
      one_div, Complex.cpow_neg]
  · intro m hm
    rcases eq_or_ne m 0 with rfl | hm0
    · simp
    · rw [LSeries.term_of_ne_zero hm0, pointMassFn_apply,
        if_neg (fun h => hm h.2), zero_div]

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.wienerJetLinear
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.analyticOrderAt_wiener_mul
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.analyticOrderAt_wiener_pow
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.wienerLSeries_pointMass
end
end

