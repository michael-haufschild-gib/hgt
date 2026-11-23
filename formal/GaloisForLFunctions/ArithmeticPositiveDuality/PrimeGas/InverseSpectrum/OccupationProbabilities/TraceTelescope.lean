import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.HeatPair
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.OperatorTrace

/-! # Finite-rank telescoping of every integer trace loss -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace _root_.RHTower
open scoped InnerProductSpace

/-- Mixed native and surviving moments of the vector carried by the rank-one correction. -/
def mixedHeatMoment (v : MissingWave) (i j : ℕ) : ℂ :=
  inner ℂ ((squareHeat.val^i) (defectVector v)) (((survivingHeat v)^j) (defectVector v))

def nativeVectorMoment (v : MissingWave) (i : ℕ) : ℂ :=
  inner ℂ ((squareHeat.val^i) (defectVector v)) (defectVector v)

theorem mixedHeatMoment_zero (v : MissingWave) (i : ℕ) : mixedHeatMoment v i 0 = nativeVectorMoment v i := by
  rw [mixedHeatMoment,pow_zero,one_apply_eq_self,nativeVectorMoment]

/-- Moving one surviving factor across the inner product contributes exactly one product of lower moments. -/
theorem mixedHeatMoment_succ (v : MissingWave) (i j : ℕ) :
    mixedHeatMoment v i (j+1) = mixedHeatMoment v (i+1) j-nativeVectorMoment v i*mixedHeatMoment v 0 j := by
  let x := defectVector v
  let y := (squareHeat.val^i) x
  let t := (survivingHeat v^j) x
  change inner ℂ y ((survivingHeat v^(j+1)) x) = inner ℂ ((squareHeat.val^(i+1)) x) t - inner ℂ y x*inner ℂ ((squareHeat.val^0) x) t
  rw [pow_succ' (survivingHeat v),pow_succ' squareHeat.val,pow_zero,one_apply_eq_self]
  change inner ℂ y (survivingHeat v t) = inner ℂ (squareHeat.val y) t-inner ℂ y x*inner ℂ x t
  rw [survivingHeat_eq,sub_apply,inner_sub_right,inner_right_rankOne_apply]
  exact congrArg (fun z : ℂ => z-inner ℂ y x*inner ℂ x t) (squareHeat.property.1.isSymmetric y t).symm

private theorem right_rank (u x : Gas) (A : GasOp) (hA : IsSelfAdjoint A) :
    rankOne ℂ u x * A = rankOne ℂ u (A x) := by
  apply ContinuousLinearMap.ext
  intro y
  change inner ℂ x (A y) • u = inner ℂ (A x) y • u
  exact congrArg (fun z : ℂ => z • u) (hA.isSymmetric x y).symm

/-- Successive replacements of native heat by surviving heat yield one rank-one summand per position. -/
theorem heat_power_difference (v : MissingWave) (m : ℕ) :
    squareHeat.val^(m+1)-survivingHeat v^(m+1) = ∑ j ∈ Finset.range (m+1),
      rankOne ℂ ((survivingHeat v^j) (defectVector v)) ((squareHeat.val^(m-j)) (defectVector v)) := by
  let A := squareHeat.val
  let B := survivingHeat v
  let x := defectVector v
  let F (j : ℕ) := B^j*A^(m+1-j)
  have hstep (j : ℕ) (hj : j ∈ Finset.range (m+1)) :
      F j-F (j+1) = rankOne ℂ ((B^j) x) ((A^(m-j)) x) := by
    have hj' := Finset.mem_range.mp hj
    have h1 : m+1-j = (m-j)+1 := by omega
    have h2 : m+1-(j+1) = m-j := by omega
    have hr : A-B = rankOne ℂ x x := by change squareHeat.val-survivingHeat v = _; rw [survivingHeat_eq,sub_sub_cancel]
    calc
      F j-F (j+1) = B^j*(A-B)*A^(m-j) := by
        simp only [F,h1,h2,pow_succ' A (m-j),pow_succ B j,mul_sub,sub_mul,mul_assoc]
      _ = _ := by
        rw [hr,show B^j*rankOne ℂ x x = rankOne ℂ ((B^j) x) x from comp_rankOne x x (B^j),
          right_rank _ _ _ (squareHeat.property.1.pow _)]
  rw [← Finset.sum_congr rfl hstep,Finset.sum_range_sub']
  simp only [F,Nat.sub_zero,pow_zero,one_mul,Nat.sub_self,mul_one]
  rfl

private theorem trace_outer_sum {ι : Type*} (s : Finset ι) (u w : ι → Gas) :
    opTrace (∑ j ∈ s, rankOne ℂ (u j) (w j)) = ∑ j ∈ s, inner ℂ (w j) (u j) := by
  let e := hsBasis ℂ Gas
  have h := hasSum_sum (s := s) (fun j (_ : j ∈ s) => e.hasSum_inner_mul_inner (w j) (u j))
  rw [opTrace]
  simpa only [sum_apply,inner_sum,rankOne_apply,inner_smul_right] using h.tsum_eq

theorem mixedHeatMoment_sum (v : MissingWave) (m : ℕ) :
    ∑ j ∈ Finset.range (m+1), mixedHeatMoment v (m-j) j =
      opTrace (squareHeat.val^(m+1)-survivingHeat v^(m+1)) := by
  rw [heat_power_difference,trace_outer_sum]
  rfl

private theorem hs_power_mem (A : GasOp) (hA : A.IsHilbertSchmidt) (m : ℕ) :
    A^(m+2) ∈ HTGeometry.hsTraceIdeal Gas := by
  have he : A^(m+2) = A ∘L (A ∘L A^m) := by change A^(m+2) = A*(A*A^m); rw [pow_succ',pow_succ']
  rw [he]
  exact HTGeometry.comp_mem_hsTraceIdeal hA (hA.comp_right _)

theorem ordinary_gap_as_sum (v : MissingWave) (m : ℕ) :
    opTrace (squareHeat.val^(m+2)-survivingHeat v^(m+2)) =
      opTrace (squareHeat.val^(m+2))-((∑' n, (missingSpectrum v n).val^(m+2):ℝ):ℂ) := by
  rw [HTGeometry.opTrace_sub_of_mem (hs_power_mem _ squareHeat.property.2 _) (hs_power_mem _ (survivingHeat_hs v) _)]
  congr 1
  rw [survivingHeat,← pow_mul]
  exact projected_even_trace _ ((missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩)
    (((nonzero_line_conserves_iff _).mpr v.property).2) m

/-- From the fourth trace onward the difference is a difference of ordinary, separately defined traces. -/
theorem ordinary_gap_eq_of_levels {v w : MissingWave} (h : missingSpectrum v = missingSpectrum w) (m : ℕ) :
    opTrace (squareHeat.val^(m+2)-survivingHeat v^(m+2)) =
      opTrace (squareHeat.val^(m+2)-survivingHeat w^(m+2)) := by
  rw [ordinary_gap_as_sum,ordinary_gap_as_sum,h]

#print axioms mixedHeatMoment_zero
#print axioms mixedHeatMoment_succ
#print axioms heat_power_difference
#print axioms mixedHeatMoment_sum
#print axioms ordinary_gap_as_sum
#print axioms ordinary_gap_eq_of_levels

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
