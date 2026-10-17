import GaloisForLFunctions.BiScaleUncertainty.TernaryPacketTrain
import GaloisForLFunctions.BiScaleUncertainty.FiniteIntegerTrainPolar

/-!
# Unconditional polar growth of the explicit diffuse train

The first two source packets alone force an exponential symbol product. Choosing
spacing at least packet count gives a linear lower bound for the polar multiplier.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

theorem ternaryPacketTrain_expSymbol_ge (n : ℕ) (S β : ℝ) (i : Fin ((n + 1) + 1)) :
    Real.exp (β * (((ternaryPacketTrain n).site i : ℝ) * S)) ≤
      (ternaryPacketTrain n).expSymbol S β := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => (ternaryPacketTrain n).coefficient j *
      Real.exp (β * (((ternaryPacketTrain n).site j : ℝ) * S)))
    (fun j _ => by simp only [ternaryPacketTrain, one_mul]; exact (Real.exp_pos _).le)
    (Finset.mem_univ i)
  simpa only [IntegerPacketTrain.expSymbol, ternaryPacketTrain, one_mul] using h

theorem ternaryPacketTrain_symbol_product_ge_exp (n : ℕ) (S : ℝ) :
    Real.exp S ≤ (ternaryPacketTrain n).expSymbol S (1 / 2) *
      (ternaryPacketTrain n).expSymbol S (-(1 / 2)) := by
  let i : Fin ((n + 1) + 1) := ⟨0, by omega⟩
  let j : Fin ((n + 1) + 1) := ⟨1, by omega⟩
  have hi : (ternaryPacketTrain n).site i = (1 : ℤ) := by
    change (3 : ℤ) ^ 0 = 1
    norm_num
  have hj : (ternaryPacketTrain n).site j = (3 : ℤ) := by
    change (3 : ℤ) ^ 1 = 3
    norm_num
  have hp : Real.exp (3 * S / 2) ≤ (ternaryPacketTrain n).expSymbol S (1 / 2) := by
    calc
      _ = Real.exp ((1 / 2) * (((ternaryPacketTrain n).site j : ℝ) * S)) := by
        congr 1
        rw [hj]
        norm_num
        ring
      _ ≤ _ := ternaryPacketTrain_expSymbol_ge n S (1 / 2) j
  have hm : Real.exp (-S / 2) ≤ (ternaryPacketTrain n).expSymbol S (-(1 / 2)) := by
    calc
      _ = Real.exp (-(1 / 2) * (((ternaryPacketTrain n).site i : ℝ) * S)) := by
        congr 1
        rw [hi]
        norm_num
        ring
      _ ≤ _ := ternaryPacketTrain_expSymbol_ge n S (-(1 / 2)) i
  calc
    _ = Real.exp (3 * S / 2) * Real.exp (-S / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul hp hm (Real.exp_pos _).le ((Real.exp_pos _).le.trans hp)

/-- An explicit linear polar amplification bound with no source or arithmetic premise. -/
theorem ternaryPacketTrain_polarMultiplier_ge {n : ℕ} {S : ℝ} (hS : (n : ℝ) + 2 ≤ S) :
    ((n : ℝ) + 2) / 4 ≤ (ternaryPacketTrain n).polarMultiplier S := by
  let q : ℝ := (n : ℝ) + 2
  have hq : 0 < q := by dsimp [q]; positivity
  have hh : q / 2 ≤ Real.exp (q / 2) := by
    have he := Real.add_one_le_exp (q / 2)
    linarith only [he]
  have he2 : (q / 2) * (q / 2) ≤ Real.exp q := by
    calc
      _ ≤ Real.exp (q / 2) * Real.exp (q / 2) :=
        mul_le_mul hh hh (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [IntegerPacketTrain.polarMultiplier, ternaryPacketTrain_mass]
  change q / 4 ≤ _ / q
  apply (le_div_iff₀ hq).mpr
  calc
    _ = (q / 2) * (q / 2) := by ring
    _ ≤ Real.exp q := he2
    _ ≤ Real.exp S := Real.exp_le_exp.mpr hS
    _ ≤ _ := ternaryPacketTrain_symbol_product_ge_exp n S

end
end GaloisForLFunctions.BiScaleUncertainty
