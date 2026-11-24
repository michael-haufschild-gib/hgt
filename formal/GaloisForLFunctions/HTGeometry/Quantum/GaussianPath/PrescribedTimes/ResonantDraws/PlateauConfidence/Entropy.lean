import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Entropy

/-! # Gaussian dilation cost at the near-Hilbert gate budget -/
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
noncomputable section

/-- The circuit net and Gaussian dilation still leave one quarter of
the Hilbert dimension in the exponent of the failure probability. -/
theorem complete_budget_price {N m : ℕ} (hN : 64≤N) (hm : m≤12*N) :
    let D : ℕ := 2^N
    let P := nearHilbertContinuousCircuitBudget N
    let Q := (atMostQuarterCircuitNet N P).card
    (2:ℝ)^m*(2*(Q:ℝ)/(2:ℝ)^(D-1)+3*(1/2:ℝ)^D) ≤ (9/10:ℝ)^D := by
  intro D P Q
  let d := 2^(N-2)
  let M := 33*N*P+N+1
  have hd : d*4=D := by
    change 2^(N-2)*2^2=2^N
    rw [←pow_add,Nat.sub_add_cancel (by omega : 2≤N)]
  have hQ : Q≤2^M := ReturnExcursions.full_budget_net_card hN
  have hbudget : 64*(N+1)*P ≤ D := Nat.mul_div_le _ _
  have hquad := ReturnExcursions.dimension_dominates_speed hN
  have hM : m+d+(3+M)≤D := by
    dsimp only [M]
    change 64*(N+1)^2≤D at hquad
    nlinarith only [hm,hd,hbudget,hquad,Nat.zero_le (N*N),Nat.zero_le P]
  have hQ' : (Q:ℝ)≤(2:ℝ)^M := by exact_mod_cast hQ
  have hbase : 1≤(2:ℝ)^M := one_le_pow₀ (by norm_num)
  have hnum : 4*(Q:ℝ)+3 ≤ 8*(2:ℝ)^M := by linarith only [hQ',hbase]
  have hprod : (2:ℝ)^m*(4*Q+3)*2^d ≤ (2:ℝ)^D := calc
    _ ≤ (2:ℝ)^m*(8*2^M)*2^d := by gcongr
    _ = (2:ℝ)^(m+d+(3+M)) := by rw [pow_add,pow_add,pow_add]; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hM
  have hD : 1≤D := Nat.one_le_two_pow
  have hp : (2:ℝ)^D=(2:ℝ)^(D-1)*2 := by
    rw [←pow_succ,Nat.sub_add_cancel hD]
  have he : (2:ℝ)^m*(2*(Q:ℝ)/(2:ℝ)^(D-1)+3*(1/2:ℝ)^D) =
      (2:ℝ)^m*(4*Q+3)/(2:ℝ)^D := by
    rw [one_div,inv_pow,hp]
    field_simp
    <;> ring
  rw [he]
  calc
    _ ≤ 1/(2:ℝ)^d := by
      rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]; exact hprod
    _ = (1/2:ℝ)^d := by rw [one_div,one_div,inv_pow]
    _ ≤ ((9/10:ℝ)^4)^d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
    _ = (9/10:ℝ)^D := by rw [←pow_mul,Nat.mul_comm 4,hd]

#print axioms complete_budget_price
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.PlateauConfidence
