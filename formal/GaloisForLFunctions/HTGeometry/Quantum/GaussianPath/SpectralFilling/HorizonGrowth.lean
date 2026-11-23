import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.PrefixPhaseHorizon

/-! # Size of the all-labelings phase-filling horizon -/
open Real
namespace GaloisForLFunctions.HTGeometry
noncomputable section

private theorem cutoff_fixed_radius_le (d : ℕ) : phaseCubeFourierCutoff d (1/80) ≤ 2^(28+22*d) := by
  apply Nat.ceil_le.mpr
  have hp : (1/80:ℝ)/(4*π) = 1/(320*π) := by field_simp; ring
  have h : 2*π/((1/80:ℝ)*((1/(320*π))^d/16)) = (2560*π)*(320*π)^d := by
    rw [_root_.one_div_pow]; field_simp; ring
  have h1 : 2560*π ≤ (2:ℝ)^14 := by linarith only [pi_lt_four]
  have h2 : 320*π ≤ (2:ℝ)^11 := by linarith only [pi_lt_four]
  rw [hp,h]
  refine (pow_le_pow_left₀ (by positivity) (mul_le_mul h1 (pow_le_pow_left₀ (by positivity) h2 d) (by positivity) (by positivity)) 2).trans_eq ?_
  push_cast
  rw [← pow_mul,← pow_add,← pow_mul]
  congr 1
  omega

/-- Each phase coordinate contributes a pair of Fourier indices between zero and the cutoff. -/
theorem nonconstant_phase_packet_card_le (M d : ℕ) : (nonconstantPacketIndexSet M d).card ≤ (M+1)^(2*d) := by
  apply (Finset.card_le_card (Finset.sdiff_subset : nonconstantPacketIndexSet M d ⊆ _)).trans_eq
  simp only [Fintype.card_piFinset,Finset.card_product,Finset.card_range,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [← sq,← pow_mul]

private theorem lifted_mass_le {D d M : ℕ} (e : Fin D ≃ Fin (d+1)) (p : Fin d → ℕ × ℕ)
    (hp : p ∈ nonconstantPacketIndexSet M d) : ∑ i, |(liftedPhaseMode e p i:ℝ)| ≤ 2*(d:ℝ)*M := by
  have h (j) : |(packetCharacter p j:ℝ)| ≤ M := by
    have hh := Finset.mem_product.mp (Fintype.mem_piFinset.mp (Finset.mem_sdiff.mp hp).1 j)
    have h1 := Finset.mem_range.mp hh.1
    have h2 := Finset.mem_range.mp hh.2
    exact_mod_cast (abs_le.mpr ⟨by dsimp [packetCharacter]; omega,by dsimp [packetCharacter]; omega⟩ : |packetCharacter p j| ≤ (M:ℤ))
  have hs : ∑ j, |(packetCharacter p j:ℝ)| ≤ d*M := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun j _ => h j)
  rw [← Equiv.sum_comp e.symm (fun i => |(liftedPhaseMode e p i:ℝ)|),Fin.sum_univ_succ]
  simp only [liftedPhaseMode,e.apply_symm_apply,Fin.cases_zero,Fin.cases_succ,Int.cast_sum,Int.cast_neg,abs_neg]
  linarith only [Finset.abs_sum_le_sum_abs (fun j : Fin d => (packetCharacter p j:ℝ)) Finset.univ,hs]

/-- At dimension D−1, the Fourier packet size and each individual balanced
frequency mass are at most 2^(128D²). -/
theorem fixed_radius_phase_packet_envelope {D : ℕ} (hD : 1 ≤ D) (e : Fin D ≃ Fin (D-1+1)) :
    let d := D-1
    let M := phaseCubeFourierCutoff d (1/80)
    let A := 2^(128*D^2)
    (nonconstantPacketIndexSet M d).card ≤ A ∧ (phaseClockModes e (1/80)).card ≤ A ∧
      ∀ m ∈ phaseClockModes e (1/80), ∑ i, |(m i:ℝ)| ≤ (A:ℝ) := by
  intro d M A
  have hM := cutoff_fixed_radius_le d
  have hpos : 0 < (2:ℕ)^(28+22*d) := by positivity
  have hMs : M+1 ≤ 2^(28+22*d+1) := by rw [pow_succ]; omega
  have hpow : (28+22*d+1)*(2*d) ≤ 128*D^2 := by
    have hd : d ≤ D := Nat.sub_le _ _
    calc
      _ ≤ (29*D+22*D)*(2*D) := Nat.mul_le_mul (by omega) (by omega)
      _ = 102*D^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by decide : 102 ≤ 128)
  have hF : (nonconstantPacketIndexSet M d).card ≤ A := by
    apply (nonconstant_phase_packet_card_le M d).trans
    apply (Nat.pow_le_pow_left hMs _).trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hpow
  refine ⟨hF,Finset.card_image_le.trans hF,?_⟩
  intro m hm
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hm
  refine (lifted_mass_le e p hp).trans ?_
  have hd : d ≤ 2^d := (Nat.lt_two_pow_self (n := d)).le
  have hsmall : (2:ℕ)*d*M ≤ A := by
    calc
      _ ≤ 2*2^d*2^(28+22*d) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hd) hM
      _ = 2^(1+d+(28+22*d)) := by rw [pow_add 2 (1+d),pow_add 2 1 d,pow_one]
      _ ≤ _ := by
        apply Nat.pow_le_pow_right (by decide)
        have h1 : D ≤ D^2 := by simpa only [pow_two,mul_one] using Nat.mul_le_mul_left D hD
        dsimp [d]; omega
  exact_mod_cast hsmall

/-- A cutoff-independent numerical bound on the all-labelings certificate. -/
theorem pauliPrefixPhaseHorizon_triple_upper (k : ℕ) :
    pauliPrefixPhaseHorizon k ≤ (2:ℝ)^(2^(2^(2*(k+3)+9)):ℕ) := by
  let N := k+3
  let D := 2^N
  let d := D-1
  let e := prefixPhaseEnergyEquiv k
  let F := nonconstantPacketIndexSet (phaseCubeFourierCutoff d (1/80)) d
  let S := phaseClockModes e (1/80)
  let J := D.factorial
  let w (m : Fin D → ℤ) : ℝ := ∑ i, |(m i:ℝ)|
  let V : ℝ := 1+(N:ℝ)^2*∑ m ∈ S, w m
  let b : ℝ := 1+(S.card:ℝ)*(2*(J:ℝ))
  let x := 128*D^2
  let A := 2^x
  have hD : 1 ≤ D := Nat.one_le_two_pow
  obtain ⟨hF,hS,hm⟩ := fixed_radius_phase_packet_envelope hD e
  have hDsq : D ≤ D^2 := by simpa only [pow_two,mul_one] using Nat.mul_le_mul_left D hD
  have hx : 4 ≤ x := by dsimp [x]; omega
  have hA : 16 ≤ A := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hx
  have hAr : 16 ≤ (A:ℝ) := by exact_mod_cast hA
  have hA1 : 1 ≤ (A:ℝ) := by linarith only [hAr]
  have hN : N ≤ D := (Nat.lt_two_pow_self (n := N)).le
  have hR : (N:ℝ)^2 ≤ A := by
    exact_mod_cast (Nat.pow_le_pow_left hN 2).trans ((Nat.lt_two_pow_self (n := D^2)).le.trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by dsimp [x]; omega)))
  have hJ : J ≤ A := by
    apply (Nat.factorial_le_pow D).trans
    apply (Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := D)).le D).trans
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by dsimp [x]; rw [pow_two]; omega)
  have hk : 2^k ≤ A := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show k ≤ x by dsimp [x]; dsimp [N] at hN; omega)
  have hF' : (F.card:ℝ) ≤ A := by exact_mod_cast hF
  have hS' : (S.card:ℝ) ≤ A := by exact_mod_cast hS
  have hJ' : (J:ℝ) ≤ A := by exact_mod_cast hJ
  have hsum : ∑ m ∈ S, w m ≤ (A:ℝ)^2 := by
    calc
      _ ≤ ∑ _m ∈ S, (A:ℝ) := Finset.sum_le_sum fun m hm' => hm m hm'
      _ = (S.card:ℝ)*A := by simp
      _ ≤ _ := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hS' (Nat.cast_nonneg _)
  have hV0 : 0 ≤ V := by dsimp [V,w]; positivity
  have hV : V ≤ (A:ℝ)^4 := by
    calc
      _ ≤ 1+(A:ℝ)*A^2 := add_le_add le_rfl (mul_le_mul hR hsum (Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Nat.cast_nonneg A))
      _ ≤ 2*(A:ℝ)^3 := by linarith only [one_le_pow₀ (n := 3) hA1]
      _ ≤ _ := by rw [pow_succ _ 3,mul_comm _ (A:ℝ)]; exact mul_le_mul_of_nonneg_right (by linarith only [hAr]) (by positivity)
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hb : b ≤ (A:ℝ)^3 := by
    have hp := mul_le_mul hS' (mul_le_mul_of_nonneg_left hJ' (by norm_num : (0:ℝ) ≤ 2)) (by positivity) (Nat.cast_nonneg A)
    calc
      _ ≤ 3*(A:ℝ)^2 := by dsimp [b]; linarith only [hp,one_le_pow₀ (n := 2) hA1]
      _ ≤ _ := by rw [pow_succ _ 2,mul_comm _ (A:ℝ)]; exact mul_le_mul_of_nonneg_right (by linarith only [hAr]) (by positivity)
  have hprice : b*(2:ℝ)^k ≤ (A:ℝ)^4 := by
    simpa only [pow_succ _ 3] using mul_le_mul hb (show (2:ℝ)^k ≤ A by exact_mod_cast hk) (by positivity) (by positivity)
  have hpre : 8*((F.card:ℝ)+1) ≤ (A:ℝ)^2 := by
    have hmul := mul_le_mul_of_nonneg_right hAr (Nat.cast_nonneg A)
    linarith only [hF',hmul,hAr]
  change 8*((F.card:ℝ)+1)/(((1/2:ℝ)^k/b)^J/V^(J-1)) ≤ _
  rw [div_div_eq_mul_div,div_eq_mul_inv,← inv_pow,inv_div,one_div,inv_pow,div_inv_eq_mul]
  calc
    _ ≤ ((A:ℝ)^2*(A^4:ℝ)^J)*(A^4:ℝ)^J := by
      apply mul_le_mul _ (pow_le_pow_left₀ (by positivity) hprice _) (by positivity) (by positivity)
      apply mul_le_mul hpre _ (pow_nonneg hV0 _) (by positivity)
      exact (pow_le_pow_left₀ hV0 hV _).trans (pow_le_pow_right₀ (one_le_pow₀ hA1) (Nat.sub_le _ _))
    _ = (A:ℝ)^(2+4*J+4*J) := by rw [pow_add,pow_add,← pow_mul]
    _ = (2:ℝ)^(x*(2+4*J+4*J)) := by simp only [A,Nat.cast_pow,Nat.cast_ofNat,pow_mul]
    _ ≤ _ := by
      apply pow_le_pow_right₀ (by norm_num)
      have hxA : x ≤ A := (Nat.lt_two_pow_self (n := x)).le
      have he : x*(2+4*J+4*J) ≤ 2^(4+2*x) := by
        calc
          _ ≤ A*(16*A) := Nat.mul_le_mul hxA (by omega)
          _ = 2^(4+2*x) := by rw [pow_add,two_mul,pow_add]; dsimp only [A]; ring
      apply he.trans
      apply Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
      have hsq : D^2 = 2^(2*N) := by dsimp [D]; rw [← pow_mul,Nat.mul_comm]
      rw [show 2^(2*(k+3)+9) = D^2*512 by rw [hsq,pow_add]; rfl]
      dsimp [x]; omega

#print axioms pauliPrefixPhaseHorizon_triple_upper
end
end GaloisForLFunctions.HTGeometry
