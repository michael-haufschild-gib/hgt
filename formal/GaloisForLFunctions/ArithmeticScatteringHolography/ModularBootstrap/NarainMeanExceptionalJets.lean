import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainCentralExceptional
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanCentralJet
import GaloisForLFunctions.RHTower.ReflectedBiHeatMultiplicityTomography

/-!
# Leading exceptional averaged Narain jets

Vanishing lower target jets collapse the Leibniz sums and give the exact cubic and quintic averaged leading coefficients.
-/

open Complex RHTower Filter Topology
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The exceptional divided target factor has its first nonzero jet at degree two. -/
theorem dividedFilledNumeratorMean_exceptional_second_jet :
    iteratedDeriv 2 (dividedFilledNumeratorMean narainExceptionalHeight) 0 =
      (8 / 3 : ℂ) * (narainExceptionalHeight.val : ℂ) ^ (1 / 2 : ℂ) *
        (2 - deriv (deriv (logDeriv xi)) 1) := by
  have h := filledNumeratorMean_exceptional_third_jet
  rw [filledNumeratorMean_third_jet_eq_divided] at h
  linear_combination h / 3

private theorem exceptional_divided_lower_jets (j : ℕ) (hj : j < 2) :
    iteratedDeriv j (dividedFilledNumeratorMean narainExceptionalHeight) 0 = 0 := by
  interval_cases j
  · rw [iteratedDeriv_zero, ← filledNumeratorMean_first_jet_eq_divided]
    exact (filledNumeratorMean_deriv_zero_eq_zero_iff narainExceptionalHeight).mpr rfl
  · exact dividedFilledNumeratorMean_first_jet_zero _

private theorem id_lower_jet (j : ℕ) (hj : j < 1) :
    iteratedDeriv j (fun u : ℂ => u) 0 = 0 := by
  have : j = 0 := by omega
  subst j
  rfl

/-- One exceptional target forces a cubic leading jet with an explicit other-height factor. -/
theorem narainMellinMean_one_exceptional_third_jet (Z : Height) :
    iteratedDeriv 3 (narainMellinMean narainExceptionalHeight Z) 0 =
      32 * (narainExceptionalHeight.val : ℂ) ^ (1 / 2 : ℂ) *
        (Z.val : ℂ) ^ (1 / 2 : ℂ) *
        (2 - deriv (deriv (logDeriv xi)) 1) *
        (2 - 4 * deriv xi 1 - Complex.log (Z.val : ℂ)) := by
  let D : ℂ → ℂ := dividedFilledNumeratorMean narainExceptionalHeight
  have hD : AnalyticAt ℂ D 0 := (differentiable_dividedFilledNumeratorMean _).analyticAt 0
  have hZ := (differentiable_dividedFilledNumeratorMean Z).analyticAt 0
  have hU := analyticAt_narainMeanCentralUnit_zero
  have hf : AnalyticAt ℂ (fun u : ℂ => u * D u) 0 := (by fun_prop).mul hD
  have hvan : ∀ j < 3, iteratedDeriv j (fun u : ℂ => u * D u) 0 = 0 := by
    intro j hj
    exact complex_iteratedDeriv_mul_eq_zero_before_add_order
      (m := 1) (n := 2) (by fun_prop) hD.contDiffAt id_lower_jet exceptional_divided_lower_jets hj
  have hjet := complex_iteratedDeriv_mul_at_add_order
    (m := 1) (n := 2) (by fun_prop : ContDiffAt ℂ 3 (fun u : ℂ => u) 0)
    hD.contDiffAt id_lower_jet exceptional_divided_lower_jets
  have hgerm : narainMellinMean narainExceptionalHeight Z =ᶠ[𝓝 (0 : ℂ)]
      fun u => (u * D u) * (dividedFilledNumeratorMean Z u * narainMeanCentralUnit u) := by
    filter_upwards [narainMellinMean_central_germ narainExceptionalHeight Z] with u hu
    rw [hu]
    dsimp only [D]
    ring
  rw [hgerm.iteratedDeriv_eq]
  rw [complex_iteratedDeriv_mul_of_left_vanishing_below 3 hf.contDiffAt
    (hZ.mul hU).contDiffAt hvan]
  rw [hjet]
  norm_num only [Nat.reduceAdd, Nat.choose, Nat.cast_ofNat, iteratedDeriv_one,
    deriv_id, one_mul, mul_one, narainMeanCentralUnit_zero]
  change 3 * iteratedDeriv 2 (dividedFilledNumeratorMean narainExceptionalHeight) 0 *
    (dividedFilledNumeratorMean Z 0 * 4) = _
  rw [dividedFilledNumeratorMean_exceptional_second_jet,
    ← filledNumeratorMean_first_jet_eq_divided Z, filledNumeratorMean_deriv_zero]
  ring

/-- Two exceptional target factors give an exact fifth central jet. -/
theorem narainMellinMean_two_exceptional_fifth_jet :
    iteratedDeriv 5 (narainMellinMean narainExceptionalHeight narainExceptionalHeight) 0 =
      (2560 / 3 : ℂ) * (narainExceptionalHeight.val : ℂ) *
        (2 - deriv (deriv (logDeriv xi)) 1) ^ 2 := by
  let D : ℂ → ℂ := dividedFilledNumeratorMean narainExceptionalHeight
  have hD : AnalyticAt ℂ D 0 := (differentiable_dividedFilledNumeratorMean _).analyticAt 0
  have hP : AnalyticAt ℂ (fun u => D u * D u) 0 := hD.mul hD
  have hPvan : ∀ j < 4, iteratedDeriv j (fun u => D u * D u) 0 = 0 := by
    intro j hj
    exact complex_iteratedDeriv_mul_eq_zero_before_add_order
      (m := 2) (n := 2) hD.contDiffAt hD.contDiffAt
      exceptional_divided_lower_jets exceptional_divided_lower_jets hj
  have hPjet := complex_iteratedDeriv_mul_at_add_order (m := 2) (n := 2)
    hD.contDiffAt hD.contDiffAt exceptional_divided_lower_jets exceptional_divided_lower_jets
  have hf : AnalyticAt ℂ (fun u : ℂ => u * (D u * D u)) 0 := (by fun_prop).mul hP
  have hvan : ∀ j < 5, iteratedDeriv j (fun u : ℂ => u * (D u * D u)) 0 = 0 := by
    intro j hj
    exact complex_iteratedDeriv_mul_eq_zero_before_add_order
      (m := 1) (n := 4) (by fun_prop) hP.contDiffAt id_lower_jet hPvan hj
  have hjet := complex_iteratedDeriv_mul_at_add_order
    (m := 1) (n := 4) (by fun_prop : ContDiffAt ℂ 5 (fun u : ℂ => u) 0)
    hP.contDiffAt id_lower_jet hPvan
  have hgerm : narainMellinMean narainExceptionalHeight narainExceptionalHeight =ᶠ[𝓝 (0 : ℂ)]
      fun u => (u * (D u * D u)) * narainMeanCentralUnit u := by
    filter_upwards [narainMellinMean_central_germ narainExceptionalHeight narainExceptionalHeight] with u hu
    rw [hu]
    dsimp only [D]
    ring
  rw [hgerm.iteratedDeriv_eq]
  rw [complex_iteratedDeriv_mul_of_left_vanishing_below 5 hf.contDiffAt
    analyticAt_narainMeanCentralUnit_zero.contDiffAt hvan, hjet, hPjet,
    narainMeanCentralUnit_zero]
  norm_num only [Nat.reduceAdd, Nat.choose, Nat.cast_ofNat, iteratedDeriv_one,
    deriv_id, one_mul, mul_one]
  change 5 * (6 * iteratedDeriv 2 (dividedFilledNumeratorMean narainExceptionalHeight) 0 *
    iteratedDeriv 2 (dividedFilledNumeratorMean narainExceptionalHeight) 0) * 4 = _
  rw [dividedFilledNumeratorMean_exceptional_second_jet]
  have hs : ((narainExceptionalHeight.val : ℂ) ^ (1 / 2 : ℂ)) ^ 2 =
      (narainExceptionalHeight.val : ℂ) := by
    rw [pow_two, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr narainExceptionalHeight.property.ne')]
    norm_num
  calc
    _ = (2560 / 3 : ℂ) * ((narainExceptionalHeight.val : ℂ) ^ (1 / 2 : ℂ)) ^ 2 *
        (2 - deriv (deriv (logDeriv xi)) 1) ^ 2 := by ring
    _ = _ := by rw [hs]

#print axioms dividedFilledNumeratorMean_exceptional_second_jet
#print axioms narainMellinMean_one_exceptional_third_jet
#print axioms narainMellinMean_two_exceptional_fifth_jet

end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
