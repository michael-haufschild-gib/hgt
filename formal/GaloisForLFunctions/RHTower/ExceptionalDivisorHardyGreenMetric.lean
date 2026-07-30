import GaloisForLFunctions.RHTower.FiniteOfflineCauchyEnergy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Hardy--Green capacity at the exceptional divisor boundary

The coefficient-two Cauchy mode attached to a point at transverse depth `a > 0` has energy
`2 / a`.  The ordinary Cayley/Jensen charge is `log ((1+a)/(1-a))`.  At the critical boundary
the first diverges while the second vanishes, and their product tends to four.  Consequently no
fixed multiple of the ordinary divisor charge controls the Hardy--Green energy near the boundary.

The one-point energy is identified directly with the existing finite off-line Cauchy energy.
-/

open Filter Set Topology

namespace GaloisForLFunctions

noncomputable section

/-- Coefficient-two Hardy--Green energy of a divisor point at transverse depth `a`. -/
def exceptionalHardyGreenEnergy (a : ℝ) : ℝ := 2 / a

/-- Ordinary one-point Jensen charge in the real Cayley coordinate. -/
def exceptionalJensenCharge (a : ℝ) : ℝ :=
  Real.log ((1 + a) / (1 - a))

theorem exceptionalHardyGreenEnergy_eq_cauchy_self
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) :
    exceptionalHardyGreenEnergy a =
      4 * RHTower.transverseCauchyKernel a a (gamma - gamma) := by
  rw [RHTower.transverseCauchyKernel_self ha gamma]
  simp [exceptionalHardyGreenEnergy, div_eq_mul_inv]
  ring

/-- The one-point finite Cauchy packet has exactly the Hardy--Green energy `2 / a`. -/
theorem finiteOfflineCauchyEnergy_one_eq_exceptionalHardyGreenEnergy
    {a : ℝ} (ha : 0 < a) (gamma : ℝ) :
    RHTower.finiteOfflineCauchyEnergy
        (fun _ : Fin 1 => a) (fun _ : Fin 1 => gamma) (fun _ : Fin 1 => 1) =
      exceptionalHardyGreenEnergy a := by
  rw [RHTower.finiteOfflineCauchyEnergy]
  simp only [Fin.sum_univ_one, Nat.cast_one, one_mul]
  rw [RHTower.transverseCauchyKernel_self ha gamma]
  simp [exceptionalHardyGreenEnergy, div_eq_mul_inv]
  ring

theorem hasDerivAt_exceptionalJensenCharge_zero :
    HasDerivAt exceptionalJensenCharge 2 0 := by
  have hnum : HasDerivAt (fun a : ℝ => 1 + a) 1 0 := by
    simpa using! (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add (hasDerivAt_id 0)
  have hden : HasDerivAt (fun a : ℝ => 1 - a) (-1) 0 := by
    simpa using! (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub (hasDerivAt_id 0)
  have hquot : HasDerivAt (fun a : ℝ => (1 + a) / (1 - a)) 2 0 := by
    convert! hnum.div hden (by norm_num) using 1
    all_goals norm_num
  simpa [exceptionalJensenCharge] using!
    (Real.hasDerivAt_log (by norm_num : ((1 + (0 : ℝ)) / (1 - 0)) ≠ 0)).comp 0 hquot

/-- Ordinary Jensen charge vanishes at the exceptional boundary. -/
theorem tendsto_exceptionalJensenCharge_nhdsGT_zero :
    Tendsto exceptionalJensenCharge (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  simpa [exceptionalJensenCharge] using!
    hasDerivAt_exceptionalJensenCharge_zero.continuousAt.tendsto.mono_left inf_le_left

/-- Hardy--Green energy diverges at the exceptional boundary. -/
theorem tendsto_exceptionalHardyGreenEnergy_nhdsGT_zero :
    Tendsto exceptionalHardyGreenEnergy (𝓝[>] (0 : ℝ)) atTop := by
  simpa [exceptionalHardyGreenEnergy, div_eq_mul_inv] using!
    tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num : (0 : ℝ) < 2)

/-- The Hardy--Green and Jensen metrics are asymptotic duals with product constant four. -/
theorem tendsto_exceptionalHardyGreenEnergy_mul_jensen_nhdsGT_zero :
    Tendsto (fun a => exceptionalHardyGreenEnergy a * exceptionalJensenCharge a)
      (𝓝[>] (0 : ℝ)) (𝓝 4) := by
  have hslope := hasDerivAt_exceptionalJensenCharge_zero.tendsto_slope_zero_right
  have hslope' : Tendsto (fun a : ℝ => exceptionalJensenCharge a / a)
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    simpa [exceptionalJensenCharge, div_eq_inv_mul, mul_comm] using hslope
  have h := hslope'.const_mul 2
  convert h using 1
  · funext a
    simp only [exceptionalHardyGreenEnergy, div_eq_mul_inv]
    ring
  · norm_num

/-- No fixed multiple of the ordinary Jensen charge controls the Hardy--Green energy in any
punctured right neighborhood of the exceptional boundary. -/
theorem not_forall_exceptionalHardyGreenEnergy_le_mul_jensen
    (C δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ a : ℝ, 0 < a → a < δ →
      exceptionalHardyGreenEnergy a ≤ C * exceptionalJensenCharge a := by
  intro hbound
  have henergy : ∀ᶠ a in 𝓝[>] (0 : ℝ), 1 < exceptionalHardyGreenEnergy a :=
    tendsto_exceptionalHardyGreenEnergy_nhdsGT_zero.eventually (eventually_gt_atTop 1)
  have hchargeLim :
      Tendsto (fun a : ℝ => C * exceptionalJensenCharge a)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_exceptionalJensenCharge_nhdsGT_zero.const_mul C
  have hcharge : ∀ᶠ a in 𝓝[>] (0 : ℝ),
      C * exceptionalJensenCharge a < 1 :=
    hchargeLim.eventually (eventually_lt_nhds (by norm_num))
  rcases (henergy.and (hcharge.and (Ioo_mem_nhdsGT hδ))).exists with
    ⟨a, henergyA, hchargeA, ha0, haδ⟩
  exact (not_lt_of_ge (hbound a ha0 haδ)) (hchargeA.trans henergyA)

end

end GaloisForLFunctions
