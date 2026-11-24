import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.ExactFactors
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.BlockDeletion
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-! # Measured Gibbs marginals of exact finite tensor factors -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing
open _root_.HTGeometry (finiteGibbsPartition finiteGibbsStateWeight)

variable {ι κ : Type*}

/-- Born mass of all full-gas states with a given subsystem label. -/
def marginal (χ : ℕ+ → Circle) (β : TraceTemperature) (a : ι → ℕ+) (b : κ → ℕ+) (i : ι) :=
  selectedMass (fun n => ‖coherentVector χ β n‖^2) (fun n => n ∈ Set.range (fun j => a i*b j))

private theorem weight_mul (β : TraceTemperature) (x y : ℕ+) :
    thermalWeight β (x*y) = thermalWeight β x * thermalWeight β y := by
  rw [thermalWeight,energy_mul,mul_add,Real.exp_add]
  rfl

/-- The complementary thermal trace cancels from the normalized full-gas event. -/
theorem marginal_eq_gibbs [Fintype ι] (χ : ℕ+ → Circle) (β : TraceTemperature) {a : ι → ℕ+} {b : κ → ℕ+}
    (h : exactLabelProduct a b) (i : ι) :
    marginal χ β a b i = finiteGibbsStateWeight β.val (fun k => energy (a k)) i := by
  classical
  let Z := (riemannZeta β.val).re
  let B := ∑' j, thermalWeight β (b j)
  let A := ∑ k, thermalWeight β (a k)
  have hZ : Z ≠ 0 := (gasPartition_pos β).ne'
  let e := Equiv.ofBijective (fun v : ι × κ => a v.1*b v.2) h
  have hzsum : (∑' n, thermalWeight β n) = Z := congrArg Complex.re (thermalWeight_partition β)
  have hgas : HasSum (thermalWeight β) Z := hzsum ▸ (thermalWeight_summable β).hasSum
  have ht : HasSum (fun v : ι × κ => thermalWeight β (a v.1)*thermalWeight β (b v.2)) Z :=
    ((e.hasSum_iff (f := thermalWeight β)).mpr hgas).congr_fun (fun v => (weight_mul β _ _).symm)
  have hp : A*B = Z := by
    rw [← ht.tsum_eq,ht.summable.tsum_prod]
    simp only [A,B,tsum_mul_left,tsum_fintype,Finset.sum_mul]
  let F := fun j => a i*b j
  have hi : Function.Injective F := fun j k he => congrArg Prod.snd (h.1 (a₁ := (i,j)) (a₂ := (i,k)) he)
  let w := fun n => if n ∈ Set.range F then ‖coherentVector χ β n‖^2 else 0
  have hs : Function.support w ⊆ Set.range F := fun n hn => by
    by_contra hnot
    exact hn (if_neg hnot)
  change (∑' n, w n) = thermalWeight β (a i)/A
  rw [← hi.tsum_eq hs]
  have hw (j : κ) : w (F j) = (thermalWeight β (a i)/Z)*thermalWeight β (b j) := by
    rw [show w (F j) = ‖coherentVector χ β (F j)‖^2 from if_pos ⟨j,rfl⟩,coherentVector_shell]
    change thermalWeight β (a i*b j)/Z = _
    rw [weight_mul]
    ring
  simp only [hw,tsum_mul_left]
  change thermalWeight β (a i)/Z*B = thermalWeight β (a i)/A
  apply (eq_div_iff (mul_ne_zero_iff.mp (hp.trans_ne hZ)).1).mpr
  calc
    _ = thermalWeight β (a i)/Z * (A*B) := by ring
    _ = _ := by rw [hp,div_mul_cancel₀ _ hZ]

/-- The first coordinate of the unique pair of vacua. -/
def factorVacuum {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :=
  ((Equiv.ofBijective (fun v : ι × κ => a v.1*b v.2) h).symm 1).1

theorem factorVacuum_label {a : ι → ℕ+} {b : κ → ℕ+} (h : exactLabelProduct a b) :
    a (factorVacuum h) = 1 := by
  let e := Equiv.ofBijective (fun v : ι × κ => a v.1*b v.2) h
  have hv : (a (e.symm 1).1).val*(b (e.symm 1).2).val = 1 := congrArg PNat.val (e.apply_symm_apply 1)
  exact PNat.coe_injective (Nat.eq_one_of_mul_eq_one_right hv)

#print axioms marginal_eq_gibbs
#print axioms factorVacuum_label

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
