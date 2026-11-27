import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.DeficitProfile.RadiusBound

/-! # Uniform tenth-power bound on the signed gate deficit -/
open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
noncomputable section

/-- The cost of every fitting circuit exceeds the quartic one-sweep
floor up to a deficit whose tenth power times t⁹ is O(K). This
tradeoff is uniform through the transition at exactly one sweep. -/
theorem gaussian_quartic_gate_deficit :
    ∃ b>(0:ℝ), ∃ A>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ t∈Icc (0:ℝ) 1, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (max 0 ((1+b*t^4)*N-(k:ℝ)))^10*t^9≤A*N := by
  obtain ⟨b,hb,C,hC,hw⟩ := gaussian_balanced_gate_cost
  let A := max ((1+b)^10) (C^10)
  refine ⟨b,hb,A,(pow_pos hC 10).trans_le (le_max_right ..),?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hn
  intro N t ht k hk
  have hN : 0<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have ht₀ := ht.1
  have hk₀ : 0≤(k:ℝ) := Nat.cast_nonneg _
  let v := max 0 ((1+b*t^4)*N-(k:ℝ))
  change v^10*t^9≤A*N
  by_cases h : N*t≤1
  · have hsmall := mul_le_mul_of_nonneg_left (pow_le_one₀ ht₀ ht.2 (n:=4)) hb.le
    have hv : v≤(1+b)*N := max_le (mul_nonneg (by positivity) hN.le)
      (by linarith only [mul_le_mul_of_nonneg_right hsmall hN.le,hk₀])
    calc
      _ ≤ ((1+b)*N)^10*t^9 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_left ..) hv 10) (pow_nonneg ht₀ 9)
      _ = ((1+b)^10*N)*(N*t)^9 := by ring
      _ ≤ (1+b)^10*N := mul_le_of_le_one_right (by positivity) (pow_le_one₀ (mul_nonneg hN.le ht₀) h)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left ..) hN.le
  have hp := zero_lt_one.trans (lt_of_not_ge h)
  have ht' : 0<t := lt_of_not_ge fun hle => hp.not_ge (mul_nonpos_of_nonneg_of_nonpos hN.le hle)
  let r := (1/(N*t))^(1/10:ℝ)
  have hr : 0<r := rpow_pos_of_pos (one_div_pos.mpr hp) _
  have hr₁ : r≤1 := rpow_le_one (one_div_pos.mpr hp).le ((div_le_one hp).mpr (lt_of_not_ge h).le) (by norm_num)
  have he : N*t*r^10=1 := by
    dsimp only [r]
    rw [←rpow_natCast,←rpow_mul (one_div_pos.mpr hp).le,show (1/10:ℝ)*(10:ℕ)=1 by norm_num,
      rpow_one,one_div,mul_inv_cancel₀ hp.ne']
  have hfit := hn t ⟨ht',ht.2⟩ r ⟨hr,hr₁⟩ he k hk
  have hv : v≤C*N*r^9 := max_le (by positivity) (sub_le_iff_le_add.mpr (hfit.trans_eq (add_comm ..)))
  calc
    _ ≤ (C*N*r^9)^10*t^9 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_max_left ..) hv 10) (pow_nonneg ht₀ 9)
    _ = (C^10*N)*(N*t*r^10)^9 := by ring
    _ = C^10*N := by rw [he,one_pow,mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right ..) hN.le

#print axioms gaussian_quartic_gate_deficit
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
