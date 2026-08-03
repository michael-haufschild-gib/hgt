import GaloisForLFunctions.HTGeometry.LabelledAtomicMeasure
import GaloisForLFunctions.RHTower.CCMCriticalMellinGrowingCumulative
import GaloisForLFunctions.RHTower.DeningerArithmeticTimeDistribution
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone
import GaloisForLFunctions.RHTower.WindingXi
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Critical half-density prime-tail resolvent law

This file realizes the infinite ordinary-integer source from the paper card as a locally finite
measure on positive logarithmic time, identifies its position moment, constructs its advanced
transport resolvent for `re z > 1`, and proves the distributional jump equation.  It also records
the multiplicity-exact Xi monodromy modes, all parameter jets, and the adjoint reflection law.

The displayed tail in the card uses the closed convention `L ≤ log n`; it is consequently
left-continuous at an atom.  The strict-tail representative is right-continuous, differs only on
the countable atom set, and defines the same regular distribution.  Both representatives and their
exact jump are retained below.
-/

open Complex Filter Function MeasureTheory Set TopologicalSpace
open scoped BigOperators Distributions ENNReal

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The parameter-independent forcing mass at the positive logarithmic time `log n`. -/
def criticalPrimeTailAtomWeight (n : DeningerPrimePowerIndex) : ℝ :=
  criticalMellinAtomWeight (n : ℕ) / deningerPrimePowerTime n

theorem criticalPrimeTailAtomWeight_nonneg (n : DeningerPrimePowerIndex) :
    0 ≤ criticalPrimeTailAtomWeight n := by
  apply div_nonneg
  · rw [criticalMellinAtomWeight]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) ArithmeticFunction.vonMangoldt_nonneg
  · exact (deningerPrimePowerTime_pos n).le

/-- Literal square-root/logarithm form of the forcing mass from the card. -/
theorem criticalPrimeTailAtomWeight_eq (n : DeningerPrimePowerIndex) :
    criticalPrimeTailAtomWeight n =
      ArithmeticFunction.vonMangoldt (n : ℕ) /
        (Real.sqrt (n : ℕ) * Real.log (n : ℕ)) := by
  have hn0 : (0 : ℝ) ≤ (n : ℕ) := by positivity
  have hsqrt : ((n : ℕ) : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt (n : ℕ))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hn0,
      ← Real.sqrt_eq_rpow]
  rw [criticalPrimeTailAtomWeight, criticalMellinAtomWeight, deningerPrimePowerTime,
    hsqrt]
  field_simp

/-- Logarithmic atom locations are pairwise distinct. -/
theorem deningerPrimePowerTime_injective :
    Function.Injective deningerPrimePowerTime := by
  intro m n h
  apply Subtype.ext
  have hmNat : 0 < (m : ℕ) := lt_of_lt_of_le Nat.zero_lt_two m.property
  have hnNat : 0 < (n : ℕ) := lt_of_lt_of_le Nat.zero_lt_two n.property
  have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast hmNat
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast hnNat
  have hexp := congrArg Real.exp h
  simpa [deningerPrimePowerTime, Real.exp_log hm, Real.exp_log hn] using hexp

/-- The infinite ordinary-integer forcing measure
`Σ_{n≥2} Λ(n)/(sqrt n log n) δ_{log n}`. -/
def criticalPrimeTailForcingMeasure : Measure ℝ :=
  labelledMeasure
    (fun n : DeningerPrimePowerIndex => ENNReal.ofReal (criticalPrimeTailAtomWeight n))
    deningerPrimePowerTime

/-- Every labelled logarithmic atom has exactly the asserted forcing mass. -/
theorem criticalPrimeTailForcingMeasure_singleton (n : DeningerPrimePowerIndex) :
    criticalPrimeTailForcingMeasure {deningerPrimePowerTime n} =
      ENNReal.ofReal (criticalPrimeTailAtomWeight n) := by
  exact labelledMeasure_singleton deningerPrimePowerTime_injective n

/-- Compact logarithmic windows meet only finitely many forcing atoms, hence the forcing measure is
finite on compact sets. -/
instance criticalPrimeTailForcingMeasure_isFiniteOnCompacts :
    IsFiniteMeasureOnCompacts criticalPrimeTailForcingMeasure where
  lt_top_of_isCompact := by
    intro K hK
    let C : Compacts ℝ := ⟨K, hK⟩
    rw [criticalPrimeTailForcingMeasure, labelledMeasure,
      Measure.sum_apply _ hK.measurableSet]
    rw [tsum_eq_sum (s := deningerPrimeActiveFinset C)]
    · apply ENNReal.sum_lt_top.mpr
      intro n hn
      simp only [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (measure_lt_top (Measure.dirac (deningerPrimePowerTime n)) K)
    · intro n hn
      have htime : deningerPrimePowerTime n ∉ K := by
        simpa [C] using hn
      simp [Measure.smul_apply, hK.measurableSet, htime]

/-- In particular the ordinary-integer forcing is a genuine locally finite Borel measure. -/
instance criticalPrimeTailForcingMeasure_isLocallyFinite :
    IsLocallyFiniteMeasure criticalPrimeTailForcingMeasure := inferInstance

/-- Literal multiplication of a measure by the positive logarithmic coordinate. -/
def criticalPrimeTailPositionMoment : Measure ℝ :=
  criticalPrimeTailForcingMeasure.withDensity (fun L => ENNReal.ofReal L)

/-- The unsquared nonarchimedean Weil current at critical half-density. -/
def criticalHalfDensityWeilPrimeMeasure : Measure ℝ :=
  labelledMeasure
    (fun n : DeningerPrimePowerIndex => ENNReal.ofReal (criticalMellinAtomWeight (n : ℕ)))
    deningerPrimePowerTime

theorem deningerPrimePowerTime_mul_criticalPrimeTailAtomWeight
    (n : DeningerPrimePowerIndex) :
    deningerPrimePowerTime n * criticalPrimeTailAtomWeight n =
      criticalMellinAtomWeight (n : ℕ) := by
  rw [criticalPrimeTailAtomWeight]
  exact mul_div_cancel₀ _ (deningerPrimePowerTime_pos n).ne'

/-- Position multiplication cancels the logarithmic denominator exactly. -/
theorem criticalPrimeTailPositionMoment_eq_weil :
    criticalPrimeTailPositionMoment = criticalHalfDensityWeilPrimeMeasure := by
  rw [criticalPrimeTailPositionMoment, criticalPrimeTailForcingMeasure,
    criticalHalfDensityWeilPrimeMeasure, labelledMeasure, withDensity_sum]
  congr 1
  funext n
  rw [withDensity_smul_measure, dirac_withDensity, smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (criticalPrimeTailAtomWeight_nonneg n)]
  congr 1
  rw [mul_comm, deningerPrimePowerTime_mul_criticalPrimeTailAtomWeight]

/-! ## Advanced prime-tail Green family -/

/-- Indicial rate of the half-density transport operator. -/
def criticalPrimeTailTransportRate (z : ℂ) : ℂ := z - 1 / 2

/-- The Dirichlet coefficient `aₙ n⁻ᶻ`, written with the entire exponential character. -/
def criticalPrimeTailDirichletCoefficient
    (z : ℂ) (n : DeningerPrimePowerIndex) : ℂ :=
  ((ArithmeticFunction.vonMangoldt (n : ℕ) / deningerPrimePowerTime n : ℝ) : ℂ) *
    Complex.exp (-z * (deningerPrimePowerTime n : ℂ))

/-- Absolute convergence of the divided-log prime coefficient series on `re z > 1`. -/
theorem summable_criticalPrimeTailDirichletCoefficient
    {z : ℂ} (hz : 1 < z.re) :
    Summable (criticalPrimeTailDirichletCoefficient z) := by
  have hshift : 1 / 2 < z.re - 1 / 2 := by linarith
  have hbaseNat := vonMangoldt_shifted_summable (z.re - 1 / 2) hshift
  have hbase : Summable (fun n : DeningerPrimePowerIndex =>
      ArithmeticFunction.vonMangoldt (n : ℕ) * ((n : ℝ) ^ (-z.re))) := by
    have hsub := hbaseNat.subtype (fun n : ℕ => 2 ≤ n)
    refine hsub.congr ?_
    intro n
    simp only [Function.comp_apply, sub_add_cancel]
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply Summable.of_norm_bounded (hbase.mul_left (Real.log 2)⁻¹)
  intro n
  have hnPos : (0 : ℝ) < (n : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two n.property)
  have hlogPos : 0 < deningerPrimePowerTime n := deningerPrimePowerTime_pos n
  have hlogLower : Real.log 2 ≤ deningerPrimePowerTime n := by
    rw [deningerPrimePowerTime]
    apply Real.log_le_log (by norm_num)
    exact_mod_cast n.property
  have hexp :
      Real.exp (-z.re * deningerPrimePowerTime n) = ((n : ℝ) ^ (-z.re)) := by
    rw [Real.rpow_def_of_pos hnPos, deningerPrimePowerTime]
    congr 1
    ring
  rw [criticalPrimeTailDirichletCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hlogPos.le),
    Complex.norm_exp]
  have hre :
      (-z * (deningerPrimePowerTime n : ℂ)).re =
        -z.re * deningerPrimePowerTime n := by simp
  rw [hre, hexp]
  have hinv : (deningerPrimePowerTime n)⁻¹ ≤ (Real.log 2)⁻¹ :=
    by simpa only [one_div] using one_div_le_one_div_of_le hlogTwo hlogLower
  calc
    ArithmeticFunction.vonMangoldt (n : ℕ) / deningerPrimePowerTime n *
        (n : ℝ) ^ (-z.re) =
      (deningerPrimePowerTime n)⁻¹ *
        (ArithmeticFunction.vonMangoldt (n : ℕ) * (n : ℝ) ^ (-z.re)) := by ring
    _ ≤ (Real.log 2)⁻¹ *
        (ArithmeticFunction.vonMangoldt (n : ℕ) * (n : ℝ) ^ (-z.re)) := by
      exact mul_le_mul_of_nonneg_right hinv
        (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hnPos.le _))

/-- Closed-tail representative from equation (3) of the card. -/
def criticalHalfDensityPrimeTail (z : ℂ) (L : ℝ) : ℂ :=
  Complex.exp (criticalPrimeTailTransportRate z * (L : ℂ)) *
    ∑' n : DeningerPrimePowerIndex,
      if L ≤ deningerPrimePowerTime n
      then criticalPrimeTailDirichletCoefficient z n
      else 0

/-- Strict-tail (right-continuous) representative of the same locally integrable function. -/
def criticalHalfDensityPrimeTailRC (z : ℂ) (L : ℝ) : ℂ :=
  Complex.exp (criticalPrimeTailTransportRate z * (L : ℂ)) *
    ∑' n : DeningerPrimePowerIndex,
      if L < deningerPrimePowerTime n
      then criticalPrimeTailDirichletCoefficient z n
      else 0

theorem summable_criticalPrimeTail_closedTerm {z : ℂ} (hz : 1 < z.re) (L : ℝ) :
    Summable (fun n : DeningerPrimePowerIndex =>
      if L ≤ deningerPrimePowerTime n
      then criticalPrimeTailDirichletCoefficient z n
      else 0) :=
  by
    refine ((summable_criticalPrimeTailDirichletCoefficient hz).indicator
      {n : DeningerPrimePowerIndex | L ≤ deningerPrimePowerTime n}).congr ?_
    intro n
    by_cases hn : L ≤ deningerPrimePowerTime n <;> simp [Set.indicator, hn]

theorem summable_criticalPrimeTail_strictTerm {z : ℂ} (hz : 1 < z.re) (L : ℝ) :
    Summable (fun n : DeningerPrimePowerIndex =>
      if L < deningerPrimePowerTime n
      then criticalPrimeTailDirichletCoefficient z n
      else 0) :=
  by
    refine ((summable_criticalPrimeTailDirichletCoefficient hz).indicator
      {n : DeningerPrimePowerIndex | L < deningerPrimePowerTime n}).congr ?_
    intro n
    by_cases hn : L < deningerPrimePowerTime n <;> simp [Set.indicator, hn]

/-- One advanced Green atom for `∂L - (z - 1/2)`. -/
def criticalPrimeTailAdvancedTerm
    (z : ℂ) (n : DeningerPrimePowerIndex) (L : ℝ) : ℂ :=
  if L ≤ deningerPrimePowerTime n then
    (criticalPrimeTailAtomWeight n : ℂ) *
      Complex.exp (criticalPrimeTailTransportRate z *
        ((L - deningerPrimePowerTime n : ℝ) : ℂ))
  else 0

theorem criticalPrimeTailAtomWeight_eq_exp
    (n : DeningerPrimePowerIndex) :
    (criticalPrimeTailAtomWeight n : ℂ) =
      ((ArithmeticFunction.vonMangoldt (n : ℕ) /
        deningerPrimePowerTime n : ℝ) : ℂ) *
        Complex.exp (-(1 / 2 : ℂ) * (deningerPrimePowerTime n : ℂ)) := by
  have hnPos : (0 : ℝ) < (n : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two n.property)
  have hlogNe : deningerPrimePowerTime n ≠ 0 := (deningerPrimePowerTime_pos n).ne'
  have hrpow :
      ((n : ℝ) ^ (-1 / 2 : ℝ)) =
        Real.exp (-(1 / 2 : ℝ) * deningerPrimePowerTime n) := by
    rw [Real.rpow_def_of_pos hnPos, deningerPrimePowerTime]
    congr 1
    ring
  rw [criticalPrimeTailAtomWeight, criticalMellinAtomWeight, hrpow]
  push_cast
  ring

/-- Each Dirichlet summand is exactly the corresponding advanced-resolvent atom. -/
theorem criticalPrimeTail_prefactor_mul_coefficient
    (z : ℂ) (n : DeningerPrimePowerIndex) (L : ℝ) :
    Complex.exp (criticalPrimeTailTransportRate z * (L : ℂ)) *
        criticalPrimeTailDirichletCoefficient z n =
      (criticalPrimeTailAtomWeight n : ℂ) *
        Complex.exp (criticalPrimeTailTransportRate z *
          ((L - deningerPrimePowerTime n : ℝ) : ℂ)) := by
  rw [criticalPrimeTailDirichletCoefficient, criticalPrimeTailAtomWeight_eq_exp]
  let A : ℂ :=
    (ArithmeticFunction.vonMangoldt (n : ℕ) / deningerPrimePowerTime n : ℝ)
  let r : ℂ := criticalPrimeTailTransportRate z
  let t : ℂ := deningerPrimePowerTime n
  calc
    Complex.exp (r * (L : ℂ)) * (A * Complex.exp (-z * t)) =
        A * (Complex.exp (r * (L : ℂ)) * Complex.exp (-z * t)) := by ring
    _ = A * Complex.exp (r * (L : ℂ) + (-z * t)) := by rw [Complex.exp_add]
    _ = A * Complex.exp (-(1 / 2 : ℂ) * t +
        r * ((L - deningerPrimePowerTime n : ℝ) : ℂ)) := by
      congr 2
      dsimp only [r, criticalPrimeTailTransportRate]
      dsimp only [t]
      push_cast
      ring
    _ = (A * Complex.exp (-(1 / 2 : ℂ) * t)) *
        Complex.exp (r * ((L - deningerPrimePowerTime n : ℝ) : ℂ)) := by
      rw [Complex.exp_add]
      ring

/-- Equation (6): the closed prime tail is the exact advanced resolvent of the fixed forcing
measure, here evaluated as its absolutely convergent atomic integral. -/
theorem criticalHalfDensityPrimeTail_eq_advancedResolvent
    {z : ℂ} (_hz : 1 < z.re) (L : ℝ) :
    criticalHalfDensityPrimeTail z L =
      ∑' n : DeningerPrimePowerIndex, criticalPrimeTailAdvancedTerm z n L := by
  rw [criticalHalfDensityPrimeTail]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [criticalPrimeTailAdvancedTerm]
  by_cases hn : L ≤ deningerPrimePowerTime n
  · rw [if_pos hn, if_pos hn, criticalPrimeTail_prefactor_mul_coefficient]
  · rw [if_neg hn, if_neg hn, mul_zero]

theorem measurable_criticalHalfDensityPrimeTail
    (z : ℂ) : Measurable (criticalHalfDensityPrimeTail z) := by
  classical
  change Measurable (fun L : ℝ =>
    Complex.exp (criticalPrimeTailTransportRate z * (L : ℂ)) *
      ∑' n : DeningerPrimePowerIndex,
        if L ≤ deningerPrimePowerTime n
        then criticalPrimeTailDirichletCoefficient z n
        else 0)
  apply Measurable.mul
  · fun_prop
  · apply Measurable.tsum
    intro n
    exact Measurable.ite (p := fun L : ℝ => L ≤ deningerPrimePowerTime n)
      (by
        change MeasurableSet (Iic (deningerPrimePowerTime n))
        exact measurableSet_Iic)
      measurable_const measurable_const

/-- On every compact positive-time window the infinite tail is bounded by the absolutely
convergent coefficient series.  Hence it is a genuine locally integrable function. -/
theorem criticalHalfDensityPrimeTail_locallyIntegrableOn
    {z : ℂ} (hz : 1 < z.re) :
    LocallyIntegrableOn (criticalHalfDensityPrimeTail z) (Ioi 0) volume := by
  rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K _hKsub hK
  obtain ⟨B, hB⟩ := bddAbove_def.mp hK.bddAbove
  let S : ℝ := ∑' n : DeningerPrimePowerIndex,
    ‖criticalPrimeTailDirichletCoefficient z n‖
  let C : ℝ := Real.exp ((criticalPrimeTailTransportRate z).re * B) * S
  have hcoeffNorm : Summable (fun n : DeningerPrimePowerIndex =>
      ‖criticalPrimeTailDirichletCoefficient z n‖) :=
    (summable_criticalPrimeTailDirichletCoefficient hz).norm
  have hS : 0 ≤ S := tsum_nonneg fun _ => norm_nonneg _
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le hS
  have hrate : 0 ≤ (criticalPrimeTailTransportRate z).re := by
    norm_num [criticalPrimeTailTransportRate]
    linarith
  have hbound : ∀ L ∈ K, ‖criticalHalfDensityPrimeTail z L‖ ≤ C := by
    intro L hLK
    have hLB : L ≤ B := hB L hLK
    have hexp :
        Real.exp ((criticalPrimeTailTransportRate z).re * L) ≤
          Real.exp ((criticalPrimeTailTransportRate z).re * B) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLB hrate)
    have hcutNorm : Summable (fun n : DeningerPrimePowerIndex =>
        ‖if L ≤ deningerPrimePowerTime n
          then criticalPrimeTailDirichletCoefficient z n
          else 0‖) :=
      (summable_criticalPrimeTail_closedTerm hz L).norm
    have htail :
        (∑' n : DeningerPrimePowerIndex,
            ‖if L ≤ deningerPrimePowerTime n
              then criticalPrimeTailDirichletCoefficient z n
              else 0‖) ≤ S := by
      exact hcutNorm.tsum_le_tsum (fun n => by
        by_cases hn : L ≤ deningerPrimePowerTime n <;> simp [hn]) hcoeffNorm
    rw [criticalHalfDensityPrimeTail, norm_mul, Complex.norm_exp]
    have hre :
        (criticalPrimeTailTransportRate z * (L : ℂ)).re =
          (criticalPrimeTailTransportRate z).re * L := by simp
    rw [hre]
    calc
      Real.exp ((criticalPrimeTailTransportRate z).re * L) *
          ‖∑' n : DeningerPrimePowerIndex,
            if L ≤ deningerPrimePowerTime n
            then criticalPrimeTailDirichletCoefficient z n
            else 0‖ ≤
        Real.exp ((criticalPrimeTailTransportRate z).re * L) *
          (∑' n : DeningerPrimePowerIndex,
            ‖if L ≤ deningerPrimePowerTime n
              then criticalPrimeTailDirichletCoefficient z n
              else 0‖) :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hcutNorm)
          (Real.exp_pos _).le
      _ ≤ Real.exp ((criticalPrimeTailTransportRate z).re * L) * S :=
        mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le
      _ ≤ C := by
        exact mul_le_mul hexp (le_refl S) hS (Real.exp_pos _).le
  have hconst : IntegrableOn (fun _ : ℝ => (C : ℂ)) K :=
    integrableOn_const hK.measure_lt_top.ne
  refine Integrable.mono hconst
    (measurable_criticalHalfDensityPrimeTail z).aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with L hLK
  simpa [Complex.norm_real, abs_of_nonneg hC] using hbound L hLK

/-- Regular distribution carried by the closed prime-tail representative. -/
noncomputable def criticalHalfDensityPrimeTailDistribution
    (z : ℂ) : DeningerTimeDistribution :=
  deningerRegularTimeDistribution (criticalHalfDensityPrimeTail z)

/-- Half-line integration by parts for one advanced Green atom.  Compact support of the test
function kills the endpoint at `-∞`; the endpoint at the atom is exactly its Dirac mass. -/
theorem integral_Iic_criticalPrimeTail_atom_transport
    (z : ℂ) (n : DeningerPrimePowerIndex)
    (φ : DeningerTimeTestFunction) :
    (∫ L : ℝ in Iic (deningerPrimePowerTime n),
      (deningerTimeTestDerivative φ L : ℂ) *
          Complex.exp (((L - deningerPrimePowerTime n : ℝ) : ℂ) *
            criticalPrimeTailTransportRate z) +
        (φ L : ℂ) *
          (criticalPrimeTailTransportRate z *
            Complex.exp (((L - deningerPrimePowerTime n : ℝ) : ℂ) *
              criticalPrimeTailTransportRate z))) =
      (φ (deningerPrimePowerTime n) : ℂ) := by
  let u : ℝ → ℂ := fun L => (φ L : ℂ)
  let v : ℝ → ℂ := fun L =>
    Complex.exp (((L - deningerPrimePowerTime n : ℝ) : ℂ) *
      criticalPrimeTailTransportRate z)
  let F : ℝ → ℂ := fun L => u L * v L
  have hu : ∀ L, HasDerivAt u (deningerTimeTestDerivative φ L : ℂ) L := by
    intro L
    have hφ : HasDerivAt (fun x : ℝ => φ x)
        (deriv (fun x : ℝ => φ x) L) L :=
      (φ.contDiff.differentiable (by simp)).differentiableAt.hasDerivAt
    simpa only [u, deningerTimeTestDerivative_apply_eq_deriv] using hφ.ofReal_comp
  have hv : ∀ L, HasDerivAt v (criticalPrimeTailTransportRate z * v L) L := by
    intro L
    have hlin : HasDerivAt
        (fun x : ℝ => ((x - deningerPrimePowerTime n : ℝ) : ℂ) *
          criticalPrimeTailTransportRate z)
        (criticalPrimeTailTransportRate z) L := by
      simpa using!
        (((hasDerivAt_id L).sub_const (deningerPrimePowerTime n)).ofReal_comp.mul_const
          (criticalPrimeTailTransportRate z))
    simpa only [v, mul_comm] using hlin.cexp
  have hFderiv : ∀ L, HasDerivAt F
      ((deningerTimeTestDerivative φ L : ℂ) * v L +
        u L * (criticalPrimeTailTransportRate z * v L)) L := by
    intro L
    exact (hu L).mul (hv L)
  have huContDiff : ContDiff ℝ 1 u := by
    simpa [u, Function.comp_def] using
      (Complex.ofRealCLM.contDiff.comp (φ.contDiff.of_le (by simp)))
  have hsubContDiff : ContDiff ℝ 1
      (fun L : ℝ => ((L - deningerPrimePowerTime n : ℝ) : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff.comp
        ((contDiff_id : ContDiff ℝ 1 (id : ℝ → ℝ)).sub contDiff_const))
  have hvContDiff : ContDiff ℝ 1 v := by
    dsimp only [v]
    exact (hsubContDiff.mul contDiff_const).cexp
  have hFcontDiff : ContDiff ℝ 1 F := by
    exact huContDiff.mul hvContDiff
  have huCompact : HasCompactSupport u := by
    simpa only [u, Function.comp_apply] using!
      (φ.hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  have hFCompact : HasCompactSupport F := by
    exact huCompact.mul_right
  have hFTC := HasCompactSupport.integral_Iic_deriv_eq hFcontDiff hFCompact
    (deningerPrimePowerTime n)
  have hderivEq : (fun L => deriv F L) = fun L =>
      (deningerTimeTestDerivative φ L : ℂ) * v L +
        u L * (criticalPrimeTailTransportRate z * v L) := by
    funext L
    exact (hFderiv L).deriv
  rw [hderivEq] at hFTC
  simpa only [F, u, v, sub_self, ofReal_zero, zero_mul,
    Complex.exp_zero, mul_one] using hFTC

/-- One advanced atom multiplied by a positive-time test function. -/
def criticalPrimeTailTestAdvancedTerm
    (z : ℂ) (φ : DeningerTimeTestFunction)
    (n : DeningerPrimePowerIndex) (L : ℝ) : ℂ :=
  (φ L : ℂ) * criticalPrimeTailAdvancedTerm z n L

theorem integrable_criticalPrimeTailTestAdvancedTerm
    (z : ℂ) (φ : DeningerTimeTestFunction)
    (n : DeningerPrimePowerIndex) :
    Integrable (criticalPrimeTailTestAdvancedTerm z φ n) := by
  classical
  let u : ℝ → ℂ := fun L => (φ L : ℂ)
  let v : ℝ → ℂ := fun L =>
    (criticalPrimeTailAtomWeight n : ℂ) *
      Complex.exp (criticalPrimeTailTransportRate z *
        ((L - deningerPrimePowerTime n : ℝ) : ℂ))
  have huCont : Continuous u := Complex.continuous_ofReal.comp φ.continuous
  have hvCont : Continuous v := by
    dsimp only [v]
    fun_prop
  have huCompact : HasCompactSupport u := by
    simpa only [u, Function.comp_apply] using!
      (φ.hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  have huvInt : Integrable (fun L => u L * v L) :=
    (huCont.mul hvCont).integrable_of_hasCompactSupport huCompact.mul_right
  have hind := huvInt.indicator (measurableSet_Iic :
    MeasurableSet (Iic (deningerPrimePowerTime n)))
  apply hind.congr
  filter_upwards [] with L
  by_cases hL : L ≤ deningerPrimePowerTime n <;>
    simp [criticalPrimeTailTestAdvancedTerm, criticalPrimeTailAdvancedTerm,
      Set.indicator, hL, u, v]

/-- Absolute integrals of all test-multiplied Green atoms form a summable family. -/
theorem summable_integral_norm_criticalPrimeTailTestAdvancedTerm
    {z : ℂ} (hz : 1 < z.re) (φ : DeningerTimeTestFunction) :
    Summable (fun n : DeningerPrimePowerIndex =>
      ∫ L : ℝ, ‖criticalPrimeTailTestAdvancedTerm z φ n L‖) := by
  obtain ⟨B, hB⟩ := bddAbove_def.mp φ.hasCompactSupport.bddAbove
  let D : ℝ := Real.exp ((criticalPrimeTailTransportRate z).re * B)
  let u : ℝ → ℂ := fun L => (φ L : ℂ)
  let A : ℝ := ∫ L : ℝ, ‖u L‖
  have hrate : 0 ≤ (criticalPrimeTailTransportRate z).re := by
    norm_num [criticalPrimeTailTransportRate]
    linarith
  have hD : 0 ≤ D := (Real.exp_pos _).le
  have huCont : Continuous u := Complex.continuous_ofReal.comp φ.continuous
  have huCompact : HasCompactSupport u := by
    simpa only [u, Function.comp_apply] using!
      (φ.hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  have huInt : Integrable u := huCont.integrable_of_hasCompactSupport huCompact
  have hA : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have hpoint : ∀ n L,
      ‖criticalPrimeTailTestAdvancedTerm z φ n L‖ ≤
        (D * ‖criticalPrimeTailDirichletCoefficient z n‖) * ‖u L‖ := by
    intro n L
    by_cases hn : L ≤ deningerPrimePowerTime n
    · by_cases hφ : φ L = 0
      · simp only [criticalPrimeTailTestAdvancedTerm, hφ, ofReal_zero, zero_mul, norm_zero]
        exact mul_nonneg
          (mul_nonneg hD (norm_nonneg (criticalPrimeTailDirichletCoefficient z n)))
          (norm_nonneg (u L))
      · have hsupport : L ∈ tsupport (fun x : ℝ => φ x) :=
          subset_tsupport _ (by simpa [Function.mem_support] using hφ)
        have hLB : L ≤ B := hB L hsupport
        have hexp :
            Real.exp ((criticalPrimeTailTransportRate z).re * L) ≤ D := by
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hLB hrate)
        rw [criticalPrimeTailTestAdvancedTerm, criticalPrimeTailAdvancedTerm, if_pos hn,
          ← criticalPrimeTail_prefactor_mul_coefficient, norm_mul, norm_mul,
          Complex.norm_exp]
        have hre :
            (criticalPrimeTailTransportRate z * (L : ℂ)).re =
              (criticalPrimeTailTransportRate z).re * L := by simp
        rw [hre]
        dsimp only [D, u]
        calc
          ‖(φ L : ℂ)‖ *
              (Real.exp ((criticalPrimeTailTransportRate z).re * L) *
                ‖criticalPrimeTailDirichletCoefficient z n‖) ≤
            ‖(φ L : ℂ)‖ *
              (D * ‖criticalPrimeTailDirichletCoefficient z n‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hexp (norm_nonneg _)) (norm_nonneg _)
          _ = D * ‖criticalPrimeTailDirichletCoefficient z n‖ * ‖(φ L : ℂ)‖ := by
            ring
    · simp only [criticalPrimeTailTestAdvancedTerm, criticalPrimeTailAdvancedTerm,
        if_neg hn, mul_zero, norm_zero]
      exact mul_nonneg
        (mul_nonneg hD (norm_nonneg (criticalPrimeTailDirichletCoefficient z n)))
        (norm_nonneg (u L))
  have hbound : ∀ n : DeningerPrimePowerIndex,
      (∫ L : ℝ, ‖criticalPrimeTailTestAdvancedTerm z φ n L‖) ≤
        (D * A) * ‖criticalPrimeTailDirichletCoefficient z n‖ := by
    intro n
    have hright : Integrable (fun L =>
        (D * ‖criticalPrimeTailDirichletCoefficient z n‖) * ‖u L‖) :=
      huInt.norm.const_mul _
    calc
      (∫ L : ℝ, ‖criticalPrimeTailTestAdvancedTerm z φ n L‖) ≤
          ∫ L : ℝ,
            (D * ‖criticalPrimeTailDirichletCoefficient z n‖) * ‖u L‖ :=
        integral_mono
          (integrable_criticalPrimeTailTestAdvancedTerm z φ n).norm
          hright (hpoint n)
      _ = (D * A) * ‖criticalPrimeTailDirichletCoefficient z n‖ := by
        rw [integral_const_mul]
        dsimp only [A]
        ring
  exact Summable.of_nonneg_of_le
    (fun n => integral_nonneg fun _ => norm_nonneg _)
    hbound
    ((summable_criticalPrimeTailDirichletCoefficient hz).norm.mul_left (D * A))

/-- Pairing the regular tail with any test function is the absolutely convergent sum of its
advanced atomic pairings. -/
theorem integral_mul_criticalHalfDensityPrimeTail_eq_tsum
    {z : ℂ} (hz : 1 < z.re) (φ : DeningerTimeTestFunction) :
    (∫ L : ℝ, (φ L : ℂ) * criticalHalfDensityPrimeTail z L) =
      ∑' n : DeningerPrimePowerIndex,
        ∫ L : ℝ, criticalPrimeTailTestAdvancedTerm z φ n L := by
  have hswap := integral_tsum_of_summable_integral_norm
    (fun n => integrable_criticalPrimeTailTestAdvancedTerm z φ n)
    (summable_integral_norm_criticalPrimeTailTestAdvancedTerm hz φ)
  rw [hswap]
  apply integral_congr_ae
  filter_upwards [] with L
  rw [criticalHalfDensityPrimeTail_eq_advancedResolvent hz]
  simp only [criticalPrimeTailTestAdvancedTerm, tsum_mul_left]

/-- The exponential definition of the Dirichlet coefficient is the ordinary complex power
`aₙ n⁻ᶻ` used in equation (3). -/
theorem criticalPrimeTailDirichletCoefficient_eq_cpow
    (z : ℂ) (n : DeningerPrimePowerIndex) :
    criticalPrimeTailDirichletCoefficient z n =
      ((ArithmeticFunction.vonMangoldt (n : ℕ) /
        Real.log (n : ℕ) : ℝ) : ℂ) * (((n : ℕ) : ℂ) ^ (-z)) := by
  have hnNe : (((n : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two n.property))
  rw [criticalPrimeTailDirichletCoefficient, deningerPrimePowerTime,
    Complex.cpow_def_of_ne_zero hnNe]
  have hlog : Complex.log (((n : ℕ) : ℂ)) = (Real.log (n : ℕ) : ℂ) := by
    exact Complex.natCast_log.symm
  rw [hlog]
  ring_nf

/-! ## The fixed forcing as a genuine distribution -/

/-- Finite forcing functional on one fixed-support Fréchet stage. -/
noncomputable def criticalPrimeTailForcingLocalCLM
    (K : Compacts ℝ) :
    𝓓_{K}(ℝ, ℝ) →L[ℝ] ℂ :=
  ∑ n ∈ deningerPrimeActiveFinset K,
    criticalPrimeTailAtomWeight n •
      Complex.ofRealCLM.comp
        (deningerSupportedTimeEval K (deningerPrimePowerTime n))

theorem criticalPrimeTailForcingLocalCLM_apply
    (K : Compacts ℝ) (φ : 𝓓_{K}(ℝ, ℝ)) :
    criticalPrimeTailForcingLocalCLM K φ =
      ∑ n ∈ deningerPrimeActiveFinset K,
        (criticalPrimeTailAtomWeight n : ℂ) *
          (φ (deningerPrimePowerTime n) : ℂ) := by
  simp [criticalPrimeTailForcingLocalCLM, deningerSupportedTimeEval]

/-- Algebraic action of the locally finite critical half-density source. -/
def criticalPrimeTailForcingFunctional
    (φ : DeningerTimeTestFunction) : ℂ :=
  ∑' n : DeningerPrimePowerIndex,
    (criticalPrimeTailAtomWeight n : ℂ) *
      (φ (deningerPrimePowerTime n) : ℂ)

theorem criticalPrimeTailForcingFunctional_ofSupportedIn
    (K : Compacts ℝ)
    (K_sub : (K : Set ℝ) ⊆ (deningerTimeDomain : Set ℝ))
    (φ : 𝓓_{K}(ℝ, ℝ)) :
    criticalPrimeTailForcingFunctional
        (TestFunction.ofSupportedIn K_sub φ) =
      criticalPrimeTailForcingLocalCLM K φ := by
  rw [criticalPrimeTailForcingFunctional,
    tsum_eq_sum (s := deningerPrimeActiveFinset K)]
  · simpa using (criticalPrimeTailForcingLocalCLM_apply K φ).symm
  · intro n hn
    have htime : deningerPrimePowerTime n ∉ (K : Set ℝ) := by
      simpa using hn
    have hzero : φ (deningerPrimePowerTime n) = 0 :=
      φ.zero_on_compl htime
    simp [hzero]

/-- Distribution attached to the locally finite forcing measure.  Continuity is proved stagewise
from the finite set of logarithmic atoms meeting each compact support. -/
noncomputable def criticalPrimeTailForcingDistribution :
    DeningerTimeDistribution :=
  TestFunction.limitCLM ℝ
    criticalPrimeTailForcingFunctional
    (fun K _K_sub => criticalPrimeTailForcingLocalCLM K)
    criticalPrimeTailForcingFunctional_ofSupportedIn

@[simp]
theorem criticalPrimeTailForcingDistribution_apply
    (φ : DeningerTimeTestFunction) :
    criticalPrimeTailForcingDistribution φ =
      ∑' n : DeningerPrimePowerIndex,
        (criticalPrimeTailAtomWeight n : ℂ) *
          (φ (deningerPrimePowerTime n) : ℂ) := by
  rw [criticalPrimeTailForcingDistribution]
  change
    (TestFunction.limitCLM ℝ
      criticalPrimeTailForcingFunctional
      (fun K _K_sub => criticalPrimeTailForcingLocalCLM K)
      criticalPrimeTailForcingFunctional_ofSupportedIn) φ =
        criticalPrimeTailForcingFunctional φ
  exact TestFunction.limitCLM_apply ℝ
    criticalPrimeTailForcingFunctional
    (fun K _K_sub => criticalPrimeTailForcingLocalCLM K)
    criticalPrimeTailForcingFunctional_ofSupportedIn φ

end

end RHTower
