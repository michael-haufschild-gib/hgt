import GaloisForLFunctions.RHTower.ThetaCuspRatioTerminalAmplitudeReverse
import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

namespace HTGeometry.ThetaRatioSource.TerminalKinetic
noncomputable section

def signedBinomial (n i : ℕ) : ℂ := (-1:ℂ)^(n-i)*(n.choose i:ℂ)

def amplitudeSelf (n : ℕ) : Polynomial ℂ :=
  ∑ i ∈ Finset.range (n+1),
    Polynomial.C (signedBinomial n i)*(amplitudePoly i*amplitudePoly (n-i))

theorem signedBinomial_pow_sum_zero {n j : ℕ} (hj : j<n) :
    ∑ i ∈ Finset.range (n+1), signedBinomial n i*(i:ℂ)^j=0 := by
  exact GaloisForLFunctions.HTGeometry.alternating_binomial_sum_pow_eq_zero hj

theorem signedBinomial_sum_zero {n : ℕ} (hn : 0<n) :
    ∑ i ∈ Finset.range (n+1), signedBinomial n i=0 := by
  simpa only [pow_zero,mul_one] using signedBinomial_pow_sum_zero (j:=0) hn

theorem even_neg_one_pow {n : ℕ} (hn : Even n) : (-1:ℂ)^n=1 := by
  obtain ⟨m,rfl⟩ := hn
  rw [pow_add,←mul_pow]
  norm_num

theorem signedBinomial_zero {n : ℕ} (hn : Even n) : signedBinomial n 0=1 := by
  simp [signedBinomial,even_neg_one_pow hn]

theorem signedBinomial_reflect {n i : ℕ} (hn : Even n) (hi : i≤n) :
    signedBinomial n (n-i)=signedBinomial n i := by
  have hp : (-1:ℂ)^i*(-1:ℂ)^(n-i)=1 := by
    rw [←pow_add,Nat.add_sub_of_le hi,even_neg_one_pow hn]
  have hs : (-1:ℂ)^(n-i)*(-1:ℂ)^(n-i)=1 := by
    rw [←mul_pow]
    norm_num
  have he : (-1:ℂ)^i=(-1:ℂ)^(n-i) := by
    linear_combination (-1:ℂ)^(n-i)*hp-(-1:ℂ)^i*hs
  simp only [signedBinomial,Nat.sub_sub_self hi,Nat.choose_symm hi,he]

theorem signedBinomial_sum_reflect {n : ℕ} (hn : Even n) (f : ℕ → ℂ) :
    (∑ i ∈ Finset.range (n+1), signedBinomial n i*f (n-i))=
      ∑ i ∈ Finset.range (n+1), signedBinomial n i*f i := by
  conv_rhs => rw [←Finset.sum_range_reflect (fun i => signedBinomial n i*f i) (n+1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [Nat.add_sub_cancel,signedBinomial_reflect hn hi']

theorem signedBinomial_amplitudeNext {n : ℕ} (hn : 2<n) :
    ∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeNext i=0 := by
  have h0 := signedBinomial_sum_zero (n:=n) (by omega)
  have h1 := signedBinomial_pow_sum_zero (n:=n) (j:=1) (by omega)
  have h2 := signedBinomial_pow_sum_zero (n:=n) (j:=2) hn
  simp only [pow_one] at h1
  calc
    _ = (∑ i ∈ Finset.range (n+1), signedBinomial n i*(i:ℂ)^2)+
        (7/2)*(∑ i ∈ Finset.range (n+1), signedBinomial n i*(i:ℂ))+
        3*(∑ i ∈ Finset.range (n+1), signedBinomial n i) := by
      simp only [Finset.mul_sum,←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      unfold amplitudeNext
      ring
    _ = 0 := by rw [h0,h1,h2]; ring

theorem signedBinomial_amplitudeNextExact {n : ℕ} (he : Even n) (hn : 2<n) :
    ∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeNextExact i= -3 := by
  simp only [amplitudeNextExact,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_zero]
  rw [signedBinomial_amplitudeNext hn]
  simp [signedBinomial_zero he]

theorem amplitudeSelf_top {n : ℕ} (hn : 0<n) : (amplitudeSelf n).coeff n=0 := by
  unfold amplitudeSelf
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  have hh : ∀ i ∈ Finset.range (n+1),
      (amplitudePoly i*amplitudePoly (n-i)).coeff n=4 := by
    intro i hi
    have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simpa only [Nat.add_sub_of_le hi'] using amplitude_product_top i (n-i)
  calc
    _ = ∑ i ∈ Finset.range (n+1), signedBinomial n i*4 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hh i hi]
    _ = 0 := by rw [←Finset.sum_mul,signedBinomial_sum_zero hn,zero_mul]

theorem amplitudeSelf_next {n : ℕ} (he : Even n) (hn : 2<n) :
    (amplitudeSelf n).coeff (n-1)= -12 := by
  unfold amplitudeSelf
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul]
  have hh : ∀ i ∈ Finset.range (n+1),
      (amplitudePoly i*amplitudePoly (n-i)).coeff (n-1)=
        2*(amplitudeNextExact i+amplitudeNextExact (n-i)) := by
    intro i hi
    have hi' : i≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simpa only [Nat.add_sub_of_le hi'] using
      amplitude_product_next i (n-i) (by omega)
  calc
    _ = 2*((∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeNextExact i)+
        (∑ i ∈ Finset.range (n+1), signedBinomial n i*amplitudeNextExact (n-i))) := by
      rw [←Finset.sum_add_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hh i hi]
      ring
    _ = -12 := by
      rw [signedBinomial_sum_reflect he, signedBinomial_amplitudeNextExact he hn]
      norm_num

end
end HTGeometry.ThetaRatioSource.TerminalKinetic
