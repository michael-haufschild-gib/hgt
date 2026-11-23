import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.Probes

/-! # One tail profile for every positive moment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Finset

private theorem uniform_gap_retention (k : ℕ) {S : ℝ} (hS : 0 < S) (hgap : 1/S ≤ occupationWeight (k+1)) :
    occupationWeight k*Real.exp (-(shortStep/S)) ∈ Icc (occupationWeight (k+1)) (occupationWeight k) := by
  have he : occupationWeight k*(1-occupationWeight (k+1)) = occupationWeight (k+1) := by
    simp only [occupationWeight_eq,Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  have hh := (short_retention_loss (R := S)).trans ((div_le_div_of_nonneg_right
    ((min_le_left _ _).trans (by norm_num : (1/4:ℝ)≤1)) hS.le).trans hgap)
  have hu : 1-occupationWeight (k+1) ≤ Real.exp (-(shortStep/S)) := by linarith only [hh]
  exact ⟨he.symm.trans_le (mul_le_mul_of_nonneg_left hu (occupationWeight_pos k).le),
    mul_le_of_le_one_right (occupationWeight_pos k).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_pos shortStep_pos hS).le))⟩

/-- The same limiting spectrum gives a large amplitude and meets every moment ceiling simultaneously. -/
theorem common_tail_profile {σ t R : ℝ} (hs : 0 < σ) (ht : 1 ≤ t) (hR : t ≤ R) :
    ∃ b : SpectralBand 1, (highWindowFactor σ/5)*(t/R^σ) < ‖relativePartition b (⟨σ,t⟩:ℂ)‖ ∧
      ∀ q : GibbsExponent, momentLoss q b < 1/R^q.val := by
  let N := ⌈R⌉₊
  let F := Finset.Ico N (2*N)
  let z : ℂ := ⟨σ,t⟩
  let u := Real.exp (-(shortStep/(5*R)))
  let w := 1/(5*R)
  let A := w^σ*(shortChordFactor σ*(t/(5*R)))
  have ht' := zero_lt_one.trans_le ht
  have h1 := ht.trans hR
  have hRp := ht'.trans_le hR
  have h5 : 0 < 5*R := mul_pos (by norm_num) hRp
  have htop : R ≤ 5*R := le_mul_of_one_le_left hRp.le (by norm_num)
  have hw : 0 < w := one_div_pos.mpr h5
  have hN : R ≤ (N:ℝ) := Nat.le_ceil _
  have hNu : (N:ℝ) < R+1 := Nat.ceil_lt_add_one hRp.le
  have hbase : w ≤ occupationWeight (2*N) := by
    rw [occupationWeight_eq,← one_div,Nat.cast_mul,Nat.cast_ofNat]
    apply (div_le_div_iff₀ h5 (show 0<2*(N:ℝ)+1 by positivity)).mpr
    linarith only [h1,hNu]
  have hx (k : ℕ) (hk : k ∈ F) : occupationWeight k*u ∈ Icc (occupationWeight (k+1)) (occupationWeight k) :=
    uniform_gap_retention k h5 (hbase.trans (occupationWeight_antitone (Nat.succ_le_of_lt (Finset.mem_Ico.mp hk).2)))
  have hshort := short_chord_lower hs.le ht'.le (h1.trans htop) (hR.trans htop)
  have hfactor := mul_pos (shortChordFactor_pos σ) (div_pos ht' h5)
  have hA : 0 < A := mul_pos (Real.rpow_pos_of_pos hw _) hfactor
  have hv (k : ℕ) (hk : k ∈ F) : A ≤ ‖(occupationWeight k:ℂ)^z-((occupationWeight k*u:ℝ):ℂ)^z‖ := by
    rw [norm_scaled_occupation_chord z (occupationWeight_pos _) (Real.exp_pos _)]
    exact mul_le_mul (Real.rpow_le_rpow hw.le (hbase.trans (occupationWeight_antitone (Finset.mem_Ico.mp hk).2.le)) hs.le)
      hshort hfactor.le (Real.rpow_nonneg (occupationWeight_pos _).le _)
  obtain ⟨b,hprefix,hvsum⟩ := coherent_tail_profile (z := z) N F (fun k hk => (Finset.mem_Ico.mp hk).1)
    (fun k => occupationWeight k*u) hx
  have hcard : F.card = N := (Nat.card_Ico N (2*N)).trans (by omega)
  have hsum := (sum_le_sum hv).trans hvsum
  rw [sum_const,hcard,nsmul_eq_mul] at hsum
  have hRsum := (mul_le_mul_of_nonneg_right hN hA.le).trans hsum
  have he : (highWindowFactor σ/5)*(t/R^σ) = R*A/8 := by
    have hw' : w = (1/5:ℝ)*R⁻¹ := by dsimp only [w]; ring
    dsimp only [A,highWindowFactor]
    rw [hw',Real.mul_rpow (by norm_num : (0:ℝ)≤1/5) (inv_nonneg.mpr hRp.le),Real.inv_rpow hRp.le]
    field_simp [hRp.ne']
  refine ⟨b,he.trans_lt (by linarith only [hRsum,mul_pos hRp hA]),?_⟩
  intro q
  have hocc : occupationWeight N < 1/R := by
    rw [occupationWeight_eq,← one_div]
    exact one_div_lt_one_div_of_lt hRp (hN.trans_lt (lt_add_one _))
  have hp := Real.rpow_lt_rpow (occupationWeight_pos N).le hocc q.property
  rw [one_div R,Real.inv_rpow hRp.le,← one_div] at hp
  exact (momentLoss_le_tail q b N hprefix).trans_lt hp

#print axioms common_tail_profile

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
