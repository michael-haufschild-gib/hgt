import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.SecularVector
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.ModeSums

/-! # One omitted direction prescribes one eigenvalue in each of finitely many gaps -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open InnerProductSpace ContinuousLinearMap

theorem occupationWeight_strictAnti : StrictAnti occupationWeight := by
  intro i j hij
  rw [occupationWeight_eq,occupationWeight_eq,inv_lt_inv₀ (by positivity) (by positivity)]
  exact add_lt_add_of_lt_of_le (Nat.cast_lt.mpr hij) le_rfl

/-- A single unit line in the first m+1 occupation modes produces all m prescribed strict gap eigenvalues. -/
theorem exists_prescribed_line {m : ℕ} (b : Fin m → ℝ)
    (hb : ∀ j, occupationWeight (j.val+1) < b j ∧ b j < occupationWeight j.val) :
    ∃ v : Gas, ‖v‖ = 1 ∧ ∀ j, ∃ y : Gas, y ≠ 0 ∧
      (projected (omitLine v)^2) y = (b j:ℂ) • y := by
  let a (i : Fin (m+1)) := occupationWeight i.val
  let d (i : Fin (m+1)) := attenuation (number i.val)
  have ha : StrictAnti a := fun _ _ h => occupationWeight_strictAnti h
  have hg (j : Fin m) : a j.succ < b j ∧ b j < a j.castSucc := hb j
  let c := missingCoeff a b
  let u (i : Fin (m+1)) := d i*c i
  let v := finiteModes c
  have hv : ‖v‖^2 = 1 := (finiteModes_norm_sq c).trans (missingCoeff_unit ha hg)
  have hu : criticalOperator v = finiteModes u := finiteModes_heat c
  refine ⟨v,?_,fun j => ?_⟩
  · nlinarith only [hv,norm_nonneg v]
  let e (i : Fin (m+1)) := u i/(a i-b j)
  let y := finiteModes e
  have he : inner ℂ (criticalOperator v) y = 1 := by
    rw [hu,finiteModes_inner,show (∑ i, u i*e i) = 1 from heated_resolvent_overlap ha (fun _ => rfl) hg j,
      Complex.ofReal_one]
  refine ⟨y,fun h => one_ne_zero (he.symm.trans (by rw [h,inner_zero_right])),?_⟩
  rw [line_square,hv,Complex.ofReal_one,inv_one,one_smul,sub_apply]
  change squareHeat.val y - inner ℂ (criticalOperator v) y • criticalOperator v = _
  rw [he,one_smul,hu,finiteModes_square,finiteModes_sub,finiteModes_smul]
  apply congrArg finiteModes
  funext i
  change a i*(u i/(a i-b j)) - u i = b j*(u i/(a i-b j))
  field_simp [sub_ne_zero.mpr (node_ne_gap ha hg i j)]
  ring

#print axioms exists_prescribed_line

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
