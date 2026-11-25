import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns.SelectedTurn

/-! # Cost of suppressing every subsequent half-period scalar return -/

open Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
open PrescribedTimes WeakBonds WeakBonds.NormalizedRadius
noncomputable section

/-- Combined Hilbert dimensions on either side of a middle bond. -/
def blockDimension (n : ℕ) := 2^((n+2)/2)+2^(n+2-(n+2)/2)

/-- Beyond every proposed winding cutoff there is a deterministic full
turn with a scalar mass floor. Nine powers of the starting winding
come from the nine couplings on the cut, independently of register size. -/
theorem gaussian_full_turn_price {ε : ℝ} (hε : 0<ε) :
    ∃ B : ℕ, 1≤B ∧ ∃ c>(0:ℝ), ∀ n m : ℕ,
      let M := B^(blockDimension n)
      ∃ w∈Icc (m+1) ((m+1)*M), c ≤
        ((m:ℝ)+1)^9*(M:ℝ)^10*fullTurnMass n w ε := by
  obtain ⟨Q,hQ⟩ := exists_nat_gt (8*π/ε)
  let η := min ε 1
  have hη : 0<η := lt_min hε zero_lt_one
  have hcut : 4*π/(Q+1:ℝ)≤ε/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h := (div_lt_iff₀ hε).mp hQ
    nlinarith only [h,hε]
  let c := bulkMass*(gaussianDensityFloor*η/(9*π))^9
  refine ⟨Q+1,Nat.succ_le_succ (Nat.zero_le _),c,mul_pos bulkMass_pos
    (pow_pos (div_pos (mul_pos gaussianDensityFloor_pos hη) (by positivity)) _),?_⟩
  intro n m M
  let N := n+2
  let h := N/2
  let a : Fin (n+1) := ⟨h-1,by dsimp only [h,N]; omega⟩
  have hl : (leftBlock a).card=h := by rw [leftBlock,Fin.card_Iic]; change h-1+1=h; dsimp [h,N]; omega
  have hr : (rightBlock a).card=N-h := by rw [rightBlock,Fin.card_Ioi]; change n+2-1-(h-1)=_; dsimp [h,N]; omega
  have hd : 2^(leftBlock a).card+2^(rightBlock a).card=blockDimension n := by rw [hl,hr]; rfl
  let T := π*((m:ℝ)+1)*(M:ℝ)
  have hM : 1≤M := Nat.one_le_pow _ _ (Nat.succ_pos Q)
  have hM' : 1≤(M:ℝ) := by exact_mod_cast hM
  have ht₁ : 1≤T := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith only [pi_gt_three]) (by positivity)) hM'
  have ht : 0<T := zero_lt_one.trans_le ht₁
  let δ := η/(18*T)
  have hδ : 0<δ := div_pos hη (by positivity)
  have hδ₁ : δ≤1 := (div_le_one (by positivity)).mpr <|
    (min_le_right ε 1).trans (by linarith only [ht₁])
  have hh := gaussian_selected_full_turn n m Q a hδ.le hδ₁
  dsimp only at hh
  rw [hd] at hh
  obtain ⟨q,hq,hqM,hmass⟩ := hh
  let w := (m+1)*q
  change bulkMass*(2*gaussianDensityFloor*δ)^9 ≤ (M:ℝ)*fullTurnMass n w (4*π/(Q+1:ℝ)+9*T*δ) at hmass
  have herr : 4*π/(Q+1:ℝ)+9*T*δ≤ε := by
    have he : 9*T*δ=η/2 := by dsimp only [δ]; field_simp [ht.ne']; ring
    rw [he]
    linarith only [hcut,min_le_left ε 1]
  have hmono : fullTurnMass n w (4*π/(Q+1:ℝ)+9*T*δ)≤fullTurnMass n w ε :=
    measureReal_mono fun _ hx => ⟨hx.1,hx.2.trans herr⟩
  have hf : 2*gaussianDensityFloor*δ*((m:ℝ)+1)*(M:ℝ)=gaussianDensityFloor*η/(9*π) := by
    dsimp only [δ,T]; field_simp [pi_ne_zero,show (M:ℝ)≠0 from (zero_lt_one.trans_le hM').ne']; ring
  refine ⟨w,⟨Nat.le_mul_of_pos_right _ hq,Nat.mul_le_mul_left _ hqM⟩,?_⟩
  change bulkMass*(gaussianDensityFloor*η/(9*π))^9 ≤ _
  rw [←hf]
  have hh' := mul_le_mul_of_nonneg_left (hmass.trans
    (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg M))) (show 0≤((m:ℝ)+1)^9*(M:ℝ)^9 by positivity)
  convert hh' using 1 <;> ring

#print axioms gaussian_full_turn_price
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SelectedDates.AlgebraicCurves.SingleHarmonics.WindingConfidence.SplitReturns
