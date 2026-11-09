import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.PrimeOrbitLogarithmicDerivative
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization
import GaloisForLFunctions.HTGeometry.EntireQuotientNormalForm

/-!
# Common exponential clocks force equal divisors

For two incommensurable exponential coordinates, orbit preservation forces
proportional logarithmic derivatives. Integer residues then force every
numerator order to equal its denominator order. Thus neither coordinate
quotient has a genuine complex zero or pole.
-/

open Filter Topology Complex Set
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

/-- A nonzero entire function has finite analytic order everywhere. -/
theorem entire_order_ne_top_of_ne_zero {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {c : ℂ} (hc : f c ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  intro htop
  have heq := hf.eq_of_eventuallyEq analyticOnNhd_const
    (analyticOrderAt_eq_top.mp htop)
  exact hc (congrFun heq c)

/-- The analytic order, viewed as an integer, is the logarithmic residue. -/
theorem entire_meromorphicOrder_eq_natOrder {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {c : ℂ} (hc : f c ≠ 0) (z : ℂ) :
    meromorphicOrderAt f z = ((analyticOrderNatAt f z : ℕ) : ℤ) := by
  rw [(hf z trivial).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (entire_order_ne_top_of_ne_zero hf hc z)]
  rfl

/-- Incommensurable exponential coordinates cannot have zeros or poles in
their meromorphic quotient: logarithmic residues are integers. -/
theorem equal_divisors_of_common_exponential_clock
    {N D M E : ℂ → ℂ} {a b : ℂ}
    (hN : AnalyticOnNhd ℂ N Set.univ) (hD : AnalyticOnNhd ℂ D Set.univ)
    (hM : AnalyticOnNhd ℂ M Set.univ) (hE : AnalyticOnNhd ℂ E Set.univ)
    (hDr : ∀ t : ℝ, D t ≠ 0) (hEr : ∀ t : ℝ, E t ≠ 0)
    (hclock : ∀ t : ℝ, ∃ u : ℂ,
      N t / D t = Complex.exp (a * u) ∧ M t / E t = Complex.exp (b * u))
    (hind : ∀ n m : ℤ, b * (n : ℂ) = a * (m : ℂ) → n = 0 ∧ m = 0)
    (z : ℂ) :
    analyticOrderAt N z = analyticOrderAt D z ∧
      analyticOrderAt M z = analyticOrderAt E z := by
  have hN0 : N 0 ≠ 0 := by
    obtain ⟨u, hu, _⟩ := hclock 0
    intro hn
    simp only [Complex.ofReal_zero, hn, zero_div] at hu
    exact Complex.exp_ne_zero _ hu.symm
  have hM0 : M 0 ≠ 0 := by
    obtain ⟨u, _, hu⟩ := hclock 0
    intro hn
    simp only [Complex.ofReal_zero, hn, zero_div] at hu
    exact Complex.exp_ne_zero _ hu.symm
  have hD0 : D 0 ≠ 0 := by simpa only [Complex.ofReal_zero] using hDr 0
  have hE0 : E 0 ≠ 0 := by simpa only [Complex.ofReal_zero] using hEr 0
  have hNo := entire_meromorphicOrder_eq_natOrder hN hN0 z
  have hDo := entire_meromorphicOrder_eq_natOrder hD hD0 z
  have hMo := entire_meromorphicOrder_eq_natOrder hM hM0 z
  have hEo := entire_meromorphicOrder_eq_natOrder hE hE0 z
  have hnN : ∀ᶠ w in 𝓝[≠] z, N w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hN z trivial).meromorphicAt).mp
      (by rw [hNo]; exact WithTop.coe_ne_top)
  have hnD : ∀ᶠ w in 𝓝[≠] z, D w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hD z trivial).meromorphicAt).mp
      (by rw [hDo]; exact WithTop.coe_ne_top)
  have hnM : ∀ᶠ w in 𝓝[≠] z, M w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hM z trivial).meromorphicAt).mp
      (by rw [hMo]; exact WithTop.coe_ne_top)
  have hnE : ∀ᶠ w in 𝓝[≠] z, E w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hE z trivial).meromorphicAt).mp
      (by rw [hEo]; exact WithTop.coe_ne_top)
  have heq :
      (fun w => b * ((w - z) * logDeriv N w - (w - z) * logDeriv D w))
        =ᶠ[𝓝[≠] z]
      (fun w => a * ((w - z) * logDeriv M w - (w - z) * logDeriv E w)) := by
    filter_upwards [hnN, hnD, hnM, hnE] with w hwN hwD hwM hwE
    have h := common_exponential_clock_cross_identity hN hD hM hE hDr hEr hclock w
    simp only [logDeriv_apply]
    field_simp [hwN, hwD, hwM, hwE]
    linear_combination (w - z) * h
  have hlN := HTGeometry.logDeriv_residue_of_meromorphicOrder
    (hN z trivial).meromorphicAt hNo
  have hlD := HTGeometry.logDeriv_residue_of_meromorphicOrder
    (hD z trivial).meromorphicAt hDo
  have hlM := HTGeometry.logDeriv_residue_of_meromorphicOrder
    (hM z trivial).meromorphicAt hMo
  have hlE := HTGeometry.logDeriv_residue_of_meromorphicOrder
    (hE z trivial).meromorphicAt hEo
  have hlim := tendsto_nhds_unique ((hlN.sub hlD).const_mul b)
    (((hlM.sub hlE).const_mul a).congr' heq.symm)
  have horders := hind
    ((analyticOrderNatAt N z : ℤ) - analyticOrderNatAt D z)
    ((analyticOrderNatAt M z : ℤ) - analyticOrderNatAt E z)
    (by simpa only [Int.cast_sub] using hlim)
  have hND : analyticOrderNatAt N z = analyticOrderNatAt D z := by
    exact_mod_cast sub_eq_zero.mp horders.1
  have hME : analyticOrderNatAt M z = analyticOrderNatAt E z := by
    exact_mod_cast sub_eq_zero.mp horders.2
  constructor
  · rw [← Nat.cast_analyticOrderNatAt (entire_order_ne_top_of_ne_zero hN hN0 z),
      ← Nat.cast_analyticOrderNatAt (entire_order_ne_top_of_ne_zero hD hD0 z), hND]
  · rw [← Nat.cast_analyticOrderNatAt (entire_order_ne_top_of_ne_zero hM hM0 z),
      ← Nat.cast_analyticOrderNatAt (entire_order_ne_top_of_ne_zero hE hE0 z), hME]

#print axioms equal_divisors_of_common_exponential_clock
end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
