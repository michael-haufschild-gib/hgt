import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.BlockDeletion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.BoundaryThermometry

/-! # One phase-return probability is an equilibrium temperature coordinate -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- As temperature falls to zero the vacuum takes the full probability. -/
theorem clockReturn_cold (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) :
    Tendsto (fun β => gibbsClockReturn χ β p D) atTop (𝓝 1) := by
  let a := primeRayLabel p D.val
  have h1 : ¬ a ∣ 1 := fun h => (Nat.not_dvd_of_pos_of_lt Nat.zero_lt_one (clockBlock_gt_one p D)) (PNat.dvd_iff.mp h)
  have ht := (thermalEvent_cold (fun n => ¬ a ∣ n) h1).inv₀ one_ne_zero
  simp only [inv_one] at ht
  exact ht.congr' (Eventually.of_forall fun β => by rw [← clockReturn_inv_eq χ β p D,inv_inv])

theorem clockReturn_continuous (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) :
    Continuous (fun β => gibbsClockReturn χ β p D) := by
  have hb : Continuous (fun β : TraceTemperature => gibbsBlockRatio β p D) :=
    Real.continuous_exp.comp (continuous_subtype_val.neg.mul continuous_const)
  have hz : Continuous (fun β : TraceTemperature => (riemannZeta β.val).re) := by
    apply continuous_iff_continuousAt.mpr
    intro β
    have hne : (β.val:ℂ) ≠ 1 := fun he => β.property.ne' (by exact_mod_cast he)
    have hc : Tendsto (fun x : TraceTemperature => (x.val:ℂ)) (𝓝 β) (𝓝 (β.val:ℂ)) :=
      (Complex.continuous_ofReal.tendsto β.val).comp (continuous_subtype_val.tendsto β)
    exact Complex.continuous_re.continuousAt.tendsto.comp
      ((differentiableAt_riemannZeta hne).continuousAt.tendsto.comp hc)
  simp_rw [gibbsClockReturn_eq]
  exact ((continuous_const.sub hb).inv₀ (fun β => (sub_pos.mpr (clockRatio_lt_one β p D)).ne')).div
    hz (fun β => (gasPartition_pos β).ne')

theorem clockReturn_mem_unit (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    gibbsClockReturn χ β p D ∈ Ioo (0:ℝ) 1 := by
  refine ⟨clockReturn_positive χ β p D,?_⟩
  let γ : TraceTemperature := ⟨β.val+1,by linarith only [β.property]⟩
  have hγ : β < γ := by change β.val < β.val+1; linarith
  have hm := clockReturn_strictMono χ p D
  have hle : gibbsClockReturn χ γ p D ≤ 1 := le_of_tendsto_of_tendsto tendsto_const_nhds
    (clockReturn_cold χ p D) ((eventually_ge_atTop γ).mono (fun x hx => hm.monotone hx))
  exact (hm hγ).trans_le hle

/-- Every probability strictly between zero and one is produced by a unique inverse temperature. -/
theorem clockReturn_existsUnique (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) (u : Ioo (0:ℝ) 1) :
    ∃! β : TraceTemperature, gibbsClockReturn χ β p D = u.val := by
  letI : PreconnectedSpace TraceTemperature :=
    (isPreconnected_iff_preconnectedSpace (s := Ioi (1:ℝ))).mp isPreconnected_Ioi
  obtain ⟨x,hx⟩ := ((gibbsClockReturn_vanishes χ p D).eventually_lt_const u.property.1).exists
  obtain ⟨y,hy⟩ := ((clockReturn_cold χ p D).eventually_const_lt u.property.2).exists
  obtain ⟨β,hβ⟩ := intermediate_value_univ x y (clockReturn_continuous χ p D)
    (show u.val ∈ Icc _ _ from ⟨hx.le,hy.le⟩)
  exact ⟨β,hβ,fun γ hγ => (clockReturn_strictMono χ p D).injective (hγ.trans hβ.symm)⟩

/-- The measured return itself gives an order-preserving calibration of the entire temperature interval. -/
def clockCalibration (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) : TraceTemperature ≃o Ioo (0:ℝ) 1 :=
  StrictMono.orderIsoOfSurjective (fun β => ⟨gibbsClockReturn χ β p D,clockReturn_mem_unit χ β p D⟩)
    (clockReturn_strictMono χ p D) (fun u => by
      obtain ⟨β,hβ,_⟩ := clockReturn_existsUnique χ p D u
      exact ⟨β,Subtype.ext hβ⟩)

theorem clockCalibration_apply (χ : ℕ+ → Circle) (p : Nat.Primes) (D : ℕ+) (β : TraceTemperature) :
    (clockCalibration χ p D β).val = gibbsClockReturn χ β p D := rfl

#print axioms clockReturn_cold
#print axioms clockReturn_continuous
#print axioms clockReturn_mem_unit
#print axioms clockReturn_existsUnique
#print axioms clockCalibration_apply

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
