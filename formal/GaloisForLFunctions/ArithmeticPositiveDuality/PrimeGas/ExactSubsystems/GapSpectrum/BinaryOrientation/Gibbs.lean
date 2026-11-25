import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.Labels
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.FiniteResolution.Sandwich
import GaloisForLFunctions.HTGeometry.SquarefreeClockLaw

/-! # The common, bosonic excess, and binary orientation laws of two Gibbs samples -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation

open Set MeasureTheory

/-- If the original inverse temperature is 1+h, the common occupation has inverse temperature 2(1+h). -/
def pairedExcess (h : Ioi (0:ℝ)) : Ioi (0:ℝ) :=
  ⟨1+2*h.val,by change 0 < 1+2*h.val; linarith only [show 0 < h.val from h.property]⟩

private theorem paired_temperature (h : Ioi (0:ℝ)) :
    (labelTemperature (pairedExcess h)).val = 2*(labelTemperature h).val := by
  unfold labelTemperature pairedExcess
  ring

def binaryPartition (h : Ioi (0:ℝ)) : ℝ :=
  ∑' j : SquarefreeLabel, thermalWeight (labelTemperature h) j.val

theorem binaryWeight_summable (h : Ioi (0:ℝ)) :
    Summable (fun j : SquarefreeLabel => thermalWeight (labelTemperature h) j.val) :=
  (thermalWeight_summable (labelTemperature h)).comp_injective Subtype.val_injective

theorem binaryPartition_pos (h : Ioi (0:ℝ)) : 0 < binaryPartition h :=
  (thermalWeight_pos _ vacuum.val).trans_le ((binaryWeight_summable h).le_tsum vacuum fun j _ => (thermalWeight_pos _ j.val).le)

private theorem binaryPartition_eq_dirichlet (h : Ioi (0:ℝ)) :
    binaryPartition h = HTGeometry.dirichletTotal HTGeometry.squarefreeWeight (labelTemperature h).val := by
  let β := labelTemperature h
  let f := fun n : ℕ => HTGeometry.squarefreeWeight n*(n:ℝ)^(-β.val)
  let e := fun j : SquarefreeLabel => j.val.val
  have hs : Function.support f ⊆ range e := by
    intro n hn
    have hsq : Squarefree n := by
      by_contra hns
      exact hn (by dsimp [f]; rw [HTGeometry.squarefreeWeight_of_not_squarefree hns,zero_mul])
    have hp : 0 < n := by
      by_contra! h0
      have he : n = 0 := by omega
      subst n
      exact hn (by simp [f])
    exact ⟨⟨⟨n,hp⟩,hsq⟩,rfl⟩
  have hi : Function.Injective e := PNat.coe_injective.comp Subtype.val_injective
  calc
    _ = ∑' j : SquarefreeLabel, f (e j) := by
      apply tsum_congr
      intro j
      change thermalWeight β j.val = HTGeometry.squarefreeWeight j.val.val*(j.val.val:ℝ)^(-β.val)
      rw [HTGeometry.squarefreeWeight_of_squarefree j.property,one_mul,Real.rpow_def_of_pos (Nat.cast_pos.mpr j.val.pos)]
      exact congrArg Real.exp (mul_comm _ _)
    _ = _ := hi.tsum_eq hs

/-- The bosonic partition at doubled temperature parameter times the binary partition
is the ordinary bosonic partition at the original inverse temperature. -/
theorem binaryPartition_times_paired (h : Ioi (0:ℝ)) :
    binaryPartition h*labelPartition (pairedExcess h) = labelPartition h := by
  have z (u : Ioi (0:ℝ)) : (labelPartition u:ℂ) = riemannZeta ((labelTemperature u).val:ℂ) :=
    thermalWeight_partition (labelTemperature u)
  have he := HTGeometry.ofReal_dirichletTotal_squarefreeWeight_eq (labelTemperature h).property
  have harg : 2*((labelTemperature h).val:ℂ) = ((labelTemperature (pairedExcess h)).val:ℂ) := by
    rw [paired_temperature]
    push_cast
    rfl
  rw [← binaryPartition_eq_dirichlet h,harg,← z h,← z (pairedExcess h)] at he
  apply (eq_div_iff (labelPartition_pos (pairedExcess h)).ne').mp
  exact_mod_cast he

def binaryMass (h : Ioi (0:ℝ)) (j : SquarefreeLabel) :=
  thermalWeight (labelTemperature h) j.val / binaryPartition h

theorem binaryMass_hasSum (h : Ioi (0:ℝ)) : HasSum (binaryMass h) 1 := by
  have H := (binaryWeight_summable h).hasSum.div_const (binaryPartition h)
  change HasSum (binaryMass h) (binaryPartition h/binaryPartition h) at H
  rwa [div_self (binaryPartition_pos h).ne'] at H

private theorem pair_weight (h : Ioi (0:ℝ)) (q : ℕ+ × ℕ+) :
    thermalWeight (labelTemperature h) q.1*thermalWeight (labelTemperature h) q.2 =
      thermalWeight (labelTemperature (pairedExcess h)) (basis q).1*
      thermalWeight (labelTemperature h) (basis q).2.1*
      thermalWeight (labelTemperature h) (basis q).2.2.val := by
  simp only [thermalWeight,← Real.exp_add,paired_temperature]
  apply congrArg Real.exp
  rw [← mul_add,energy_identity]
  ring

/-- The three thermal marginals are independent, including the squarefree orientation. -/
theorem product_gibbs_weights (h : Ioi (0:ℝ)) (q : ℕ+ × ℕ+) :
    labelMass h q.1*labelMass h q.2 =
      labelMass (pairedExcess h) (basis q).1*labelMass h (basis q).2.1*binaryMass h (basis q).2.2 := by
  have hz : labelPartition (pairedExcess h)*labelPartition h*binaryPartition h =
      labelPartition h*labelPartition h := by
    rw [show labelPartition (pairedExcess h)*labelPartition h*binaryPartition h =
      labelPartition h*(binaryPartition h*labelPartition (pairedExcess h)) by ring,binaryPartition_times_paired]
  simp only [labelMass_eq,binaryMass,div_mul_div_comm]
  rw [pair_weight h q,hz]

/-- The probability measured on a two-copy basis state factors in the unitary normal coordinates. -/
theorem gibbs_normal_form (h : Ioi (0:ℝ)) (q : ℕ+ × ℕ+) :
    (gibbsPairLaw (excessDamping h) (excessDamping_gt h) : Measure (ℕ+ × ℕ+)).real {q} =
      labelMass (pairedExcess h) (basis q).1*labelMass h (basis q).2.1*binaryMass h (basis q).2.2 := by
  rw [← product_gibbs_weights]
  have hx := excessDamping_gt h
  have hp : 1/4 < excessDamping h/2 := by linarith only [hx]
  obtain ⟨u,hu,heu⟩ := commonScaleWeight_positive hp q.1
  obtain ⟨v,hv,hev⟩ := commonScaleWeight_positive hp q.2
  rw [measureReal_def,gibbsPairLaw_atom,gapAmplitude_product hx]
  simp only [labelMass,← heu,← hev,← Complex.ofReal_mul,Complex.ofReal_re,ENNReal.toReal_ofReal (mul_pos hu hv).le]

/-- The zero-gap probability is the joint vacuum probability of the two unpaired factors. -/
theorem collision_vacuum_product (h : Ioi (0:ℝ)) :
    collisionMass h = 1/(labelPartition h*binaryPartition h) := by
  have H (n : ℕ+) : labelMass h n*labelMass h n =
      labelMass (pairedExcess h) n*(labelMass h 1*binaryMass h vacuum) := by
    have he := product_gibbs_weights h (n,n)
    rw [diagonal_basis] at he
    exact he.trans (mul_assoc _ _ _)
  rw [collisionMass_as_sum,tsum_congr H,tsum_mul_right,(labelMass_hasSum (pairedExcess h)).tsum_eq,one_mul,labelMass_eq,binaryMass]
  have hw : thermalWeight (labelTemperature h) 1 = 1 := by simp [thermalWeight,energy]
  change (thermalWeight (labelTemperature h) 1/labelPartition h)*
    (thermalWeight (labelTemperature h) 1/binaryPartition h) = _
  rw [hw,div_mul_div_comm,one_mul]

#print axioms binaryWeight_summable
#print axioms binaryPartition_pos
#print axioms binaryPartition_times_paired
#print axioms binaryMass_hasSum
#print axioms product_gibbs_weights
#print axioms gibbs_normal_form
#print axioms collision_vacuum_product

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation
