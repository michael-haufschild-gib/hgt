import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Gibbs
import GaloisForLFunctions.RHTower.MobiusPrimeApertureCriticalProfile

/-! # Joint reading of orientation energy and the largest marked prime -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime

open Filter Topology Set _root_.RHTower

/-- Energy in pole units; its largest summand comes from the largest marked prime. -/
def scaledEnergy (h : Ioi (0:ℝ)) (j : SquarefreeLabel) := h.val*energy j.val

def primeCut (c : ℝ) (h : Ioi (0:ℝ)) := ⌊Real.exp (c/h.val)⌋₊

/-- A label is retained precisely when every marked prime lies in the scaled interval. -/
theorem smooth_iff (c : ℝ) (h : Ioi (0:ℝ)) (j : SquarefreeLabel) :
    j.val.val ∈ (primeCut c h+1).smoothNumbers ↔
      ∀ p : ℕ, p.Prime → p ∣ j.val.val → h.val*Real.log p ≤ c := by
  rw [Nat.mem_smoothNumbers']
  have hp (p : ℕ) (hpp : p.Prime) : p < primeCut c h+1 ↔ h.val*Real.log p ≤ c := by
    rw [Nat.lt_succ_iff,primeCut,Nat.le_floor_iff (Real.exp_pos _).le,
      ← Real.log_le_log_iff (Nat.cast_pos.mpr hpp.pos) (Real.exp_pos _),Real.log_exp,
      le_div_iff₀ h.property,mul_comm]
  exact ⟨fun H p hpp hd => (hp p hpp).mp (H p hpp hd),
    fun H p hpp hd => (hp p hpp).mpr (H p hpp hd)⟩

/-- Laplace weight of the total energy, measured only on labels with no mark above the cutoff. -/
def jointReading (c t : ℝ) (h : Ioi (0:ℝ)) : ℝ := ∑' j : SquarefreeLabel,
  if j.val.val ∈ (primeCut c h+1).smoothNumbers then binaryMass h j*Real.exp (-t*scaledEnergy h j) else 0

private theorem thermal_tilt (t : ℝ) (h : Ioi (0:ℝ)) (j : SquarefreeLabel) :
    thermalWeight (labelTemperature h) j.val*Real.exp (-t*scaledEnergy h j) =
      squarefreeMobiusMass (1+(1+t)*h.val) j.val.val := by
  rw [thermalWeight,← Real.exp_add,squarefreeMobiusMass,if_pos j.property,
    Real.rpow_def_of_pos (Nat.cast_pos.mpr j.val.pos)]
  apply congrArg Real.exp
  change -(1+h.val)*Real.log (j.val.val:ℝ)+ -t*(h.val*Real.log (j.val.val:ℝ)) = _
  ring

/-- Tilting changes the temperature in the finite numerator and preserves the original normalization. -/
theorem joint_product (c t : ℝ) (ht : 0 < 1+t) (h : Ioi (0:ℝ)) :
    jointReading c t h =
      (∏ p ∈ (primeCut c h+1).primesBelow, (1+(p:ℝ)^(-(1+(1+t)*h.val))))/binaryPartition h := by
  classical
  let K := primeCut c h+1
  let σ := 1+(1+t)*h.val
  let g := K.smoothNumbers.indicator (squarefreeMobiusMass σ)
  let e := fun j : SquarefreeLabel => j.val.val
  have hs : Function.support g ⊆ range e := by
    intro n hn
    have hm : n ∈ K.smoothNumbers := by
      by_contra h
      exact hn (indicator_of_notMem h _)
    have hsq : Squarefree n := by
      by_contra h
      exact hn (by change K.smoothNumbers.indicator _ n = 0; rw [indicator_of_mem hm,squarefreeMobiusMass,if_neg h])
    exact ⟨⟨⟨n,Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hm)⟩,hsq⟩,rfl⟩
  have hi : Function.Injective e := PNat.coe_injective.comp Subtype.val_injective
  have hσ : 1 < σ := lt_add_of_pos_right 1 (mul_pos ht h.property)
  have hprod := prod_primesBelow_eq_tsum_smoothNumbers hσ K
  rw [tsum_subtype] at hprod
  change (∏ p ∈ K.primesBelow, (1+(p:ℝ)^(-σ))) = ∑' n, g n at hprod
  rw [← hi.tsum_eq hs] at hprod
  rw [jointReading,hprod,← tsum_div_const]
  apply tsum_congr
  intro j
  by_cases hm : e j ∈ K.smoothNumbers
  · rw [if_pos hm]
    change binaryMass h j*Real.exp (-t*scaledEnergy h j) =
      K.smoothNumbers.indicator _ (e j)/binaryPartition h
    rw [indicator_of_mem hm,binaryMass,div_mul_eq_mul_div,thermal_tilt]
  · rw [if_neg hm]
    change 0 = K.smoothNumbers.indicator _ (e j)/binaryPartition h
    rw [indicator_of_notMem hm,zero_div]

#print axioms smooth_iff
#print axioms joint_product

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime
