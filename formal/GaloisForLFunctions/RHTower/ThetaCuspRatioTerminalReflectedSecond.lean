import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalReflectedLeading

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section

theorem signedBinomial_quartic {n : ℕ} (hn : 4<n) (a b c d e : ℂ) :
    ∑ i ∈ Finset.range (n+1), signedBinomial n i*
      (a*(i:ℂ)^4+b*(i:ℂ)^3+c*(i:ℂ)^2+d*(i:ℂ)+e)=0 := by
  have h0 := signedBinomial_sum_zero (n:=n) (by omega)
  have h1 := signedBinomial_pow_sum_zero (n:=n) (j:=1) (by omega)
  have h2 := signedBinomial_pow_sum_zero (n:=n) (j:=2) (by omega)
  have h3 := signedBinomial_pow_sum_zero (n:=n) (j:=3) (by omega)
  have h4 := signedBinomial_pow_sum_zero (n:=n) (j:=4) hn
  simp only [pow_one] at h1
  calc
    _ = a*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(i:ℂ)^4)+
        b*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(i:ℂ)^3)+
        c*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(i:ℂ)^2)+
        d*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(i:ℂ))+
        e*(∑ i ∈ Finset.range (n+1), signedBinomial n i) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [h0,h1,h2,h3,h4]; ring

theorem signedBinomial_amplitudeThird {n : ℕ} (hn : 4<n) :
    ∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeThird i=0 := by
  apply Eq.trans ?_ (signedBinomial_quartic hn (1/4) (13/12) (25/16) (41/48) 0)
  apply Finset.sum_congr rfl
  intro i _
  unfold amplitudeThird
  ring

theorem signedBinomial_one {n : ℕ} (he : Even n) (hn : 0<n) :
    signedBinomial n 1= -(n:ℂ) := by
  have hp := even_neg_one_pow he
  have hn1 : n-1+1=n := by omega
  rw [←hn1,pow_succ] at hp
  have hs : (-1:ℂ)^(n-1)= -1 := by linear_combination -hp
  simp [signedBinomial,hs]

theorem signedBinomial_amplitudeThirdExact {n : ℕ} (he : Even n) (hn : 4<n) :
    ∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeThirdExact i=
      (15/4)*(n:ℂ) := by
  simp only [amplitudeThirdExact,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero]
  rw [signedBinomial_amplitudeThird hn]
  simp [show 1<n+1 by omega,signedBinomial_one he (by omega)]
  ring

theorem signedBinomial_next_product {n : ℕ} (hn : 4<n) :
    ∑ i ∈ Finset.range (n+1),
      signedBinomial n i*(amplitudeNext i*amplitudeNext (n-i))=0 := by
  apply Eq.trans ?_ (signedBinomial_quartic hn 1 (-2*(n:ℂ))
    ((n:ℂ)^2-(7/2)*(n:ℂ)-25/4) ((7/2)*(n:ℂ)^2+(25/4)*(n:ℂ))
    (3*(n:ℂ)^2+(21/2)*(n:ℂ)+9))
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  unfold amplitudeNext
  rw [Nat.cast_sub hi']
  ring

theorem nextExact_product (n i : ℕ) (hn : 0<n) (hi : i≤n) :
    amplitudeNextExact i*amplitudeNextExact (n-i)=
      amplitudeNext i*amplitudeNext (n-i)-
        (if i=0 then 3*amplitudeNext n else 0)-
        (if i=n then 3*amplitudeNext n else 0) := by
  have hn0 : n≠0 := by omega
  by_cases hi0 : i=0
  · subst i
    simp [amplitudeNextExact,amplitudeNext,hn0,Ne.symm hn0]
  · by_cases hin : i=n
    · subst i
      simp [amplitudeNextExact,amplitudeNext,hn0]
      ring
    · have hni : n-i≠0 := by omega
      simp [amplitudeNextExact,hi0,hin,hni]

theorem signedBinomial_nextExact_product {n : ℕ} (he : Even n) (hn : 4<n) :
    ∑ i ∈ Finset.range (n+1),
      signedBinomial n i*(amplitudeNextExact i*amplitudeNextExact (n-i))=
        -6*amplitudeNext n := by
  calc
    _ = ∑ i ∈ Finset.range (n+1), signedBinomial n i*
        (amplitudeNext i*amplitudeNext (n-i)-
          (if i=0 then 3*amplitudeNext n else 0)-
          (if i=n then 3*amplitudeNext n else 0)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [nextExact_product n i (by omega)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    _ = -6*amplitudeNext n := by
      simp only [mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero]
      rw [signedBinomial_next_product hn]
      simp [signedBinomial]
      rw [even_neg_one_pow he]
      ring

theorem amplitudeSelf_second_sum {n : ℕ} (hn : 2≤n) :
    (amplitudeSelf n).coeff (n-2)=
      ∑ i ∈ Finset.range (n+1), signedBinomial n i*
        (2*(amplitudeThirdExact i+amplitudeThirdExact (n-i))+
          amplitudeNextExact i*amplitudeNextExact (n-i)) := by
  unfold amplitudeSelf
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hh := amplitude_product_third i (n-i) (by omega)
  rw [Nat.add_sub_of_le hi'] at hh
  rw [hh]

theorem amplitudeSelf_second_high {n : ℕ} (he : Even n) (hn : 4<n) :
    (amplitudeSelf n).coeff (n-2)= -6*((n:ℂ)*((n:ℂ)+1)+3) := by
  rw [amplitudeSelf_second_sum (by omega)]
  calc
    _ = 2*((∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeThirdExact i)+
        (∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeThirdExact (n-i)))+
        ∑ i ∈ Finset.range (n+1),
          signedBinomial n i*(amplitudeNextExact i*amplitudeNextExact (n-i)) := by
      rw [←Finset.sum_add_distrib,Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [signedBinomial_sum_reflect he,signedBinomial_amplitudeThirdExact he hn,
        signedBinomial_nextExact_product he hn]
      unfold amplitudeNext
      ring

theorem amplitudeSelf_second_two : (amplitudeSelf 2).coeff 0= -30 := by
  have hh := amplitudeSelf_second_sum (n:=2) (by omega)
  norm_num [Finset.sum_range_succ,signedBinomial,amplitudeThirdExact,amplitudeNextExact,
    amplitudeThird,amplitudeNext,Nat.choose] at hh
  exact hh

theorem amplitudeSelf_second_four : (amplitudeSelf 4).coeff 2= -90 := by
  have hh := amplitudeSelf_second_sum (n:=4) (by omega)
  norm_num [Finset.sum_range_succ,signedBinomial,amplitudeThirdExact,amplitudeNextExact,
    amplitudeThird,amplitudeNext,Nat.choose] at hh
  exact hh

theorem amplitudeSelf_second_even {n : ℕ} (he : Even n) (hn : 2≤n) :
    (amplitudeSelf n).coeff (n-2)= -6*((n:ℂ)*((n:ℂ)+1)+3)+
      (if n=2 then 24 else 0)+(if n=4 then 48 else 0) := by
  by_cases hn2 : n=2
  · subst n
    norm_num [amplitudeSelf_second_two]
  · by_cases hn4 : n=4
    · subst n
      norm_num [amplitudeSelf_second_four]
    · have hn5 : 4<n := by obtain ⟨m,hm⟩ := he; omega
      simp only [if_neg hn2,if_neg hn4,add_zero]
      exact amplitudeSelf_second_high he hn5

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
