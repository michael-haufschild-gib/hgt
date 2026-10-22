import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspRatioTerminalReflectedAffine

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section

theorem amplitudeCross_coeff_above (n j : ℕ) (hj : n<j) :
    (amplitudeCross n).coeff j=0 := by
  unfold amplitudeCross
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_C_mul,amplitudePoly_coeff_above i j (by
    have hi' := Finset.mem_range.mp hi
    omega),mul_zero]

theorem amplitudeCross_degree (n : ℕ) : (amplitudeCross n).natDegree≤n := by
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (amplitudeCross_coeff_above n)

theorem amplitudeCross_top (n : ℕ) : (amplitudeCross n).coeff n=2 := by
  unfold amplitudeCross
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  rw [Finset.sum_eq_single n]
  · simp [signedBinomial,amplitudePoly_coeff_top]
  · intro i hi hin
    rw [amplitudePoly_coeff_above i n (by
      have hi' := Finset.mem_range.mp hi
      omega),mul_zero]
  · intro hn
    exact (hn (Finset.mem_range.mpr (by omega))).elim

theorem signedBinomial_penultimate (n : ℕ) :
    signedBinomial (n+1) n= -((n+1:ℕ):ℂ) := by
  have hc := Nat.choose_symm (show n≤n+1 by omega)
  simp only [Nat.add_sub_cancel_left,Nat.choose_one_right] at hc
  rw [signedBinomial,←hc]
  simp

theorem amplitudeCross_next (n : ℕ) :
    (amplitudeCross (n+1)).coeff n=
      ((n+1:ℕ):ℂ)*(((n+1:ℕ):ℂ)+1)+3 := by
  unfold amplitudeCross
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  rw [Finset.sum_range_succ]
  have hs : (∑ i ∈ Finset.range (n+1),
      (signedBinomial (n+1) i*(5/4:ℂ)^(n+1-i))*(amplitudePoly i).coeff n)=
      -((n+1:ℕ):ℂ)*(5/4)*2 := by
    rw [Finset.sum_eq_single n]
    · rw [signedBinomial_penultimate,amplitudePoly_coeff_top]
      simp
    · intro i hi hin
      rw [amplitudePoly_coeff_above i n (by
        have hi' := Finset.mem_range.mp hi
        omega),mul_zero]
    · intro hn
      exact (hn (Finset.mem_range.mpr (by omega))).elim
  rw [hs,amplitudePoly_coeff_next]
  simp [signedBinomial,amplitudeNext]
  ring

theorem amplitudeSelf_coeff_above (n j : ℕ) (hj : n<j) :
    (amplitudeSelf n).coeff j=0 := by
  unfold amplitudeSelf
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hd : (amplitudePoly i*amplitudePoly (n-i)).natDegree≤n := by
    have hb := Polynomial.natDegree_mul_le (p:=amplitudePoly i) (q:=amplitudePoly (n-i))
    have hA := amplitudePoly_degree i
    have hB := amplitudePoly_degree (n-i)
    omega
  rw [Polynomial.coeff_C_mul,Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hj),
    mul_zero]

theorem amplitudeSelf_degree {n : ℕ} (hn : 0<n) :
    (amplitudeSelf n).natDegree≤n-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  by_cases he : j=n
  · subst j
    exact amplitudeSelf_top hn
  · exact amplitudeSelf_coeff_above n j (by omega)

theorem amplitudeSelf_next_sum {n : ℕ} (hn : 1≤n) :
    (amplitudeSelf n).coeff (n-1)=
      ∑ i ∈ Finset.range (n+1), signedBinomial n i*
        (2*(amplitudeNextExact i+amplitudeNextExact (n-i))) := by
  unfold amplitudeSelf
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hh := amplitude_product_next i (n-i) (by omega)
  rw [Nat.add_sub_of_le hi'] at hh
  rw [hh]

theorem amplitudeSelf_next_two : (amplitudeSelf 2).coeff 1= -4 := by
  have hh := amplitudeSelf_next_sum (n:=2) (by omega)
  norm_num [Finset.sum_range_succ,signedBinomial,amplitudeNextExact,amplitudeNext,Nat.choose] at hh
  exact hh

theorem amplitudeSelf_next_even {n : ℕ} (he : Even n) (hn : 2≤n) :
    (amplitudeSelf n).coeff (n-1)= -12+(if n=2 then 8 else 0) := by
  by_cases hn2 : n=2
  · subst n
    norm_num [amplitudeSelf_next_two]
  · simp only [if_neg hn2,add_zero]
    exact amplitudeSelf_next he (by omega)

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
