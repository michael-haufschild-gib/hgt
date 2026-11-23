import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.EscapingWaves

/-! # Coordinate diagonal of a partially attenuated block -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set ContinuousLinearMap InnerProductSpace

/-- Surviving weight before rearrangement of the diagonal. -/
def retainedWeight (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) (k : ℕ) : ℝ :=
  if hk : N ≤ k ∧ k < N+r then (t ⟨k-N,by omega⟩).val * occupationWeight k else occupationWeight k

theorem retainedWeight_slot (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) (j : Fin r) :
    retainedWeight N t (N+j.val) = (t j).val * occupationWeight (N+j.val) := by
  have hj := j.isLt
  simp only [retainedWeight,dif_pos (show N ≤ N+j.val ∧ N+j.val < N+r by omega),Nat.add_sub_cancel_left]

theorem retainedWeight_outside {N r k : ℕ} (t : Fin r → Ioc (0:ℝ) 1) (hk : ¬(N ≤ k ∧ k < N+r)) :
    retainedWeight N t k = occupationWeight k := dif_neg hk

theorem retainedWeight_pos (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) (k : ℕ) : 0 < retainedWeight N t k := by
  unfold retainedWeight
  split
  · exact mul_pos (t _).property.1 (occupationWeight_pos k)
  · exact occupationWeight_pos _

private theorem mode_inner (i : ℕ+) (f : Gas) : inner ℂ (modeWave i) f = f i := by
  simp [modeWave,lp.inner_single_left]

private theorem mode_at (i : ℕ+) : modeWave i i = 1 := by simp [modeWave,lp.single_apply]
private theorem mode_away {i j : ℕ+} (h : j ≠ i) : modeWave i j = 0 := by
  simp [modeWave,lp.single_apply,Pi.single_eq_of_ne h]

private theorem visible_evaluation (N : ℕ) {r : ℕ} (j : Fin r) (t : Ioc (0:ℝ) 1) (f : Gas) (k : ℕ) :
    (rankOne ℂ (visibleMode N j t) (visibleMode N j t) f) (number k) =
      if k = N+j.val then (((1-t.val)*occupationWeight k:ℝ):ℂ)*f (number k) else 0 := by
  let i := number (N+j.val)
  let c := Real.sqrt (1-t.val)*attenuation i
  have hv : visibleMode N j t = (c:ℂ) • modeWave i := by
    rw [visibleMode,heat_modeWave,smul_smul,← Complex.ofReal_mul]
  have hc : c*c = (1-t.val)*occupationWeight (N+j.val) := by
    change (Real.sqrt (1-t.val)*attenuation i)*(Real.sqrt (1-t.val)*attenuation i) = (1-t.val)*attenuation i^2
    rw [← pow_two,mul_pow,Real.sq_sqrt (sub_nonneg.mpr t.property.2)]
  change (inner ℂ (visibleMode N j t) f • visibleMode N j t) (number k) = _
  rw [hv,inner_smul_left,mode_inner,Complex.conj_ofReal,smul_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul]
  by_cases hk : k = N+j.val
  · subst k
    rw [if_pos rfl,mode_at,mul_one,← hc,Complex.ofReal_mul c c]
    change ((c:ℂ)*f i)*(c:ℂ) = ((c:ℂ)*(c:ℂ))*f i
    ring
  · rw [if_neg hk,mode_away (fun he => hk (number_injective he)),mul_zero]

theorem attenuatedSquare_apply (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) (f : Gas) (k : ℕ) :
    attenuatedSquare N t f (number k) = (retainedWeight N t k:ℂ)*f (number k) := by
  have hs : squareHeat.val f (number k) = (occupationWeight k:ℂ)*f (number k) := by
    change criticalOperator (criticalOperator f) (number k) = _
    rw [critical_apply,critical_apply,← mul_assoc,← Complex.ofReal_mul,← pow_two]
    rfl
  simp only [attenuatedSquare,sub_apply,lp.coeFn_sub,Pi.sub_apply,sum_apply,lp.coeFn_sum,Finset.sum_apply,visible_evaluation,hs]
  by_cases hk : N ≤ k ∧ k < N+r
  · let j : Fin r := ⟨k-N,by omega⟩
    have hj : k = N+j.val := by dsimp [j]; omega
    rw [Finset.sum_eq_single j (fun l _ hl => if_neg (fun he => hl (Fin.ext (Nat.add_left_cancel (he.symm.trans hj)))))
      (fun h => (h (Finset.mem_univ j)).elim),if_pos hj,hj,retainedWeight_slot,
      Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_mul]
    ring
  · have hn (j : Fin r) : k ≠ N+j.val := by have h := j.isLt; omega
    simp only [if_neg (hn _),Finset.sum_const_zero,sub_zero,retainedWeight_outside t hk]

#print axioms attenuatedSquare_apply

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
