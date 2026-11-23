import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.PoleTrace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.TraceTelescope

/-! # Recovering all native moments of the omitted vector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace

private theorem mixed_difference (v w : MissingWave) (m : ℕ)
    (hp : ∀ k < m, nativeVectorMoment v k = nativeVectorMoment w k) (j : ℕ) :
    ∀ i, i+j ≤ m → mixedHeatMoment v i j-mixedHeatMoment w i j =
      nativeVectorMoment v (i+j)-nativeVectorMoment w (i+j) := by
  induction j with
  | zero => intro i _; simp only [mixedHeatMoment_zero,Nat.add_zero]
  | succ j ih =>
    intro i hij
    have hj : j < m := by omega
    have hi : i < m := by omega
    have hsmall := ih 0 (by omega)
    rw [Nat.zero_add,hp j hj,sub_self,sub_eq_zero] at hsmall
    have ha : (i+1)+j = i+(j+1) := by omega
    have htop := ih (i+1) (by omega)
    rw [ha] at htop
    rw [mixedHeatMoment_succ,mixedHeatMoment_succ,hp i hi,hsmall]
    linear_combination htop

/-- Equality of the first two eigenvalue lists gives the initial moment at the pole and all higher moments by triangular inversion. -/
theorem nativeVectorMoments_of_spectrum {v w : MissingWave} (he : missingSpectrum v = missingSpectrum w) :
    ∀ m, nativeVectorMoment v m = nativeVectorMoment w m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      have h : omissionPartition v 1 = omissionPartition w 1 := congrArg (fun b => relativePartition b 1) he
      rw [omissionPartition_pole,omissionPartition_pole,← defectVector_norm_sq,← defectVector_norm_sq] at h
      have hr : ‖defectVector v‖^2 = ‖defectVector w‖^2 := Complex.ofReal_injective h
      have hn := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hr
      simp only [nativeVectorMoment,pow_zero,one_apply_eq_self,inner_self_eq_norm_sq_to_K,hn]
    | succ k =>
      let m := k+1
      have hs : ∑ j ∈ Finset.range (m+1), mixedHeatMoment v (m-j) j =
          ∑ j ∈ Finset.range (m+1), mixedHeatMoment w (m-j) j := by
        rw [mixedHeatMoment_sum,mixedHeatMoment_sum]
        exact ordinary_gap_eq_of_levels he k
      have ht (j : ℕ) (hj : j ∈ Finset.range (m+1)) :
          mixedHeatMoment v (m-j) j-mixedHeatMoment w (m-j) j = nativeVectorMoment v m-nativeVectorMoment w m := by
        have hj' := Finset.mem_range.mp hj
        have hn : m-j+j = m := by omega
        simpa only [hn] using mixed_difference v w m ih j (m-j) hn.le
      have hz : ((m+1:ℕ):ℂ)*(nativeVectorMoment v m-nativeVectorMoment w m) = 0 := by
        calc
          _ = ∑ _j ∈ Finset.range (m+1), (nativeVectorMoment v m-nativeVectorMoment w m) := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
          _ = _ := (Finset.sum_congr rfl ht).symm
          _ = 0 := by rw [Finset.sum_sub_distrib,hs,sub_self]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)))

#print axioms nativeVectorMoments_of_spectrum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
