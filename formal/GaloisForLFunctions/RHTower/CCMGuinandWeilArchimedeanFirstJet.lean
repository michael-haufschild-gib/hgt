import GaloisForLFunctions.RHTower.CCMGuinandWeilArchimedeanOddSource
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Endpoint-renormalized archimedean first jet

The Gamma density is not an order-zero source at logarithmic position zero.  Its restricted-Weil
action instead subtracts the endpoint value before division by the hyperbolic denominator.  This
file proves that the resulting quotient is controlled exactly by the first jet of the test:
`F'(0) / 2 + F(0) / 4`.

For the weighted-cosine tests producing the CCM diagonal, the endpoint jet is universal across
all integer modes: the value is `2` and the derivative is `-1/a`.  Hence the renormalized endpoint
value is `1/2 - 1/(2a)`, independent of mode.  This is the order-one diagonal counterpart of the
order-lowering sine cancellation in `CCMGuinandWeilArchimedeanOddSource`.
-/

noncomputable section

open scoped BigOperators Interval

namespace RHTower

open Matrix MeasureTheory Set Filter Topology

/-- Universal first-jet law for the endpoint-renormalized Gamma quotient. -/
theorem ccmGuinandWeilArchimedeanFirstJet_limit
    {F : ℝ → ℝ} {F' : ℝ} (hF : HasDerivAt F F' 0) :
    Tendsto (fun h : ℝ =>
        (Real.exp (h / 2) * F h - F 0) /
          (Real.exp h - Real.exp (-h)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (F' / 2 + F 0 / 4)) := by
  let G : ℝ → ℝ := (fun h => Real.exp (h / 2)) * F
  let D : ℝ → ℝ := (fun h => Real.exp h) - fun h => Real.exp (-h)
  have hinner : HasDerivAt (fun h : ℝ => h / 2) (1 / 2 : ℝ) 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).div_const 2
  have hexp : HasDerivAt (fun h : ℝ => Real.exp (h / 2)) (1 / 2 : ℝ) 0 := by
    simpa using hinner.exp
  have hG : HasDerivAt G (F 0 / 2 + F') 0 := by
    dsimp only [G]
    exact (hexp.mul hF).congr_deriv (by
      norm_num
      ring)
  have hneg : HasDerivAt (fun h : ℝ => Real.exp (-h)) (-1) 0 := by
    have hi : HasDerivAt (fun h : ℝ => -h) (-1) 0 :=
      hasDerivAt_neg' (x := (0 : ℝ))
    simpa using hi.exp
  have hD : HasDerivAt D 2 0 := by
    dsimp only [D]
    have hpos : HasDerivAt (fun h : ℝ => Real.exp h) 1 0 := by
      simpa using Real.hasDerivAt_exp 0
    exact (hpos.sub hneg).congr_deriv (by norm_num)
  have hGslope := hG.tendsto_slope_zero_right
  have hDslope := hD.tendsto_slope_zero_right
  have hGslope' :
      Tendsto (fun h : ℝ => (G h - G 0) / h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (F 0 / 2 + F')) := by
    simpa [div_eq_mul_inv, mul_comm] using hGslope
  have hDslope' :
      Tendsto (fun h : ℝ => (D h - D 0) / h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
    simpa [div_eq_mul_inv, mul_comm] using hDslope
  have hquot := hGslope'.div hDslope' (by norm_num : (2 : ℝ) ≠ 0)
  have hquot' :
      Tendsto (fun h : ℝ =>
          ((G h - G 0) / h) / ((D h - D 0) / h))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (F' / 2 + F 0 / 4)) := by
    have hval : (F 0 / 2 + F') / 2 = F' / 2 + F 0 / 4 := by ring
    change Tendsto (fun h : ℝ =>
      ((G h - G 0) / h) / ((D h - D 0) / h))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((F 0 / 2 + F') / 2)) at hquot
    rw [← hval]
    exact hquot
  apply hquot'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  have hDne : D h - D 0 ≠ 0 := by
    simp only [D, Pi.sub_apply, Real.exp_zero, neg_zero, sub_self, sub_zero]
    exact sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (neg_lt_self hh)))
  simp only [D, Pi.sub_apply, Real.exp_zero, neg_zero, sub_self, sub_zero] at hDne
  simp only [G, D, Pi.mul_apply, Pi.sub_apply, Real.exp_zero, zero_div,
    neg_zero, one_mul, sub_self, sub_zero]
  field_simp [hh0, hDne]

/-- Physical frequency attached to an arbitrary integer Fourier mode. -/
def ccmGuinandWeilPhysicalFrequencyInt (a : ℝ) (mode : ℤ) : ℝ :=
  Real.pi * (mode : ℝ) / a

theorem ccmGuinandWeilPhysicalFrequencyInt_nat (a : ℝ) (n : ℕ) :
    ccmGuinandWeilPhysicalFrequencyInt a (n : ℤ) =
      ccmPublishedPhysicalFrequency a n := by
  rw [ccmGuinandWeilPhysicalFrequencyInt, ccmPublishedPhysicalFrequency]
  norm_cast

/-- Integer-mode sine coordinate after reflection from horizon to logarithmic position. -/
theorem ccmGuinandWeilSineCoordinate_logToHorizon_int {a : ℝ} (ha : 0 < a)
    (mode : ℤ) {h : ℝ} (hh : h ∈ Set.Icc (0 : ℝ) (2 * a)) :
    ccmGuinandWeilSineCoordinate mode (ccmGuinandWeilLogToHorizon a h) =
      -Real.sin (ccmGuinandWeilPhysicalFrequencyInt a mode * h) := by
  rw [show ccmGuinandWeilSineCoordinate mode (ccmGuinandWeilLogToHorizon a h) =
      Real.sin (2 * Real.pi * (ccmGuinandWeilLogToHorizon a h).1 * (mode : ℝ)) by
        rfl,
    ccmGuinandWeilLogToHorizon_coe_of_mem ha hh]
  have harg :
      2 * Real.pi * (1 - h / (2 * a)) * (mode : ℝ) =
        (mode : ℝ) * (2 * Real.pi) -
          ccmGuinandWeilPhysicalFrequencyInt a mode * h := by
    rw [ccmGuinandWeilPhysicalFrequencyInt]
    field_simp [ha.ne']
  rw [harg, Real.sin_int_mul_two_pi_sub]

/-- Logarithmic tent--cosine test transported from a weighted horizon coordinate. -/
def ccmGuinandWeilDiagonalLogTest (a : ℝ) (mode : ℤ) (h : ℝ) : ℝ :=
  2 * (1 - h / (2 * a)) *
    Real.cos (ccmGuinandWeilPhysicalFrequencyInt a mode * h)

/-- Exact transport of the weighted-cosine horizon coordinate to the logarithmic aperture. -/
theorem ccmGuinandWeilWeightedCosineCoordinate_logToHorizon
    {a : ℝ} (ha : 0 < a) (mode : ℤ) {h : ℝ}
    (hh : h ∈ Set.Icc (0 : ℝ) (2 * a)) :
    2 * ccmGuinandWeilWeightedCosineCoordinate mode
        (ccmGuinandWeilLogToHorizon a h) =
      ccmGuinandWeilDiagonalLogTest a mode h := by
  rw [show ccmGuinandWeilWeightedCosineCoordinate mode
        (ccmGuinandWeilLogToHorizon a h) =
      (ccmGuinandWeilLogToHorizon a h).1 *
        Real.cos (2 * Real.pi * (ccmGuinandWeilLogToHorizon a h).1 *
          (mode : ℝ)) by rfl,
    ccmGuinandWeilLogToHorizon_coe_of_mem ha hh]
  have harg :
      2 * Real.pi * (1 - h / (2 * a)) * (mode : ℝ) =
        (mode : ℝ) * (2 * Real.pi) -
          ccmGuinandWeilPhysicalFrequencyInt a mode * h := by
    rw [ccmGuinandWeilPhysicalFrequencyInt]
    field_simp [ha.ne']
  rw [harg, Real.cos_int_mul_two_pi_sub]
  simp only [ccmGuinandWeilDiagonalLogTest, mul_assoc]

/-- Every diagonal tent--cosine mode has the same first derivative at the singular endpoint. -/
theorem hasDerivAt_ccmGuinandWeilDiagonalLogTest_zero
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    HasDerivAt (ccmGuinandWeilDiagonalLogTest a mode) (-1 / a) 0 := by
  have hlinear :
      HasDerivAt (fun h : ℝ => 1 - h / (2 * a)) (-1 / (2 * a)) 0 := by
    have hraw :=
      (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
        ((hasDerivAt_id (x := (0 : ℝ))).div_const (2 * a))
    have hraw' : HasDerivAt
        ((fun _ : ℝ => 1) - fun h : ℝ => h / (2 * a))
        (-1 / (2 * a)) 0 := hraw.congr_deriv (by ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun h => by rfl)
  have hphase :
      HasDerivAt (fun h : ℝ => ccmGuinandWeilPhysicalFrequencyInt a mode * h)
        (ccmGuinandWeilPhysicalFrequencyInt a mode) 0 := by
    simpa using
      (hasDerivAt_id (x := (0 : ℝ))).const_mul
        (ccmGuinandWeilPhysicalFrequencyInt a mode)
  have hcos :
      HasDerivAt (fun h : ℝ =>
          Real.cos (ccmGuinandWeilPhysicalFrequencyInt a mode * h)) 0 0 := by
    have hraw :=
      (Real.hasDerivAt_cos
        (ccmGuinandWeilPhysicalFrequencyInt a mode * 0)).comp 0 hphase
    have hraw' : HasDerivAt
        (Real.cos ∘ fun h : ℝ =>
          ccmGuinandWeilPhysicalFrequencyInt a mode * h) 0 0 :=
      hraw.congr_deriv (by simp)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun h => by rfl)
  have hproduct := (hlinear.const_mul 2).mul hcos
  have hproduct' : HasDerivAt (ccmGuinandWeilDiagonalLogTest a mode)
      (2 * (-1 / (2 * a)) *
          Real.cos (ccmGuinandWeilPhysicalFrequencyInt a mode * 0) +
        2 * (1 - 0 / (2 * a)) * 0) 0 :=
    hproduct.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun h => by rfl)
  apply hproduct'.congr_deriv
  simp only [mul_zero, Real.cos_zero, zero_div, sub_zero, mul_one, add_zero]
  field_simp [ha.ne']

/-- The diagonal Gamma quotient has a mode-independent renormalized endpoint value. -/
theorem ccmGuinandWeilArchimedeanDiagonalFirstJet_limit
    {a : ℝ} (ha : 0 < a) (mode : ℤ) :
    Tendsto (fun h : ℝ =>
        (Real.exp (h / 2) * ccmGuinandWeilDiagonalLogTest a mode h -
            ccmGuinandWeilDiagonalLogTest a mode 0) /
          (Real.exp h - Real.exp (-h)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (1 / 2 - 1 / (2 * a))) := by
  have hlimit := ccmGuinandWeilArchimedeanFirstJet_limit
    (hasDerivAt_ccmGuinandWeilDiagonalLogTest_zero ha mode)
  convert hlimit using 1 <;> simp [ccmGuinandWeilDiagonalLogTest]
  field_simp [ha.ne']
  ring

end RHTower
