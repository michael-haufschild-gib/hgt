import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Spacing.Bandwidth

/-! # An order-independent limit of the circuit-net spacing estimate -/
open Filter Set Finset MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
noncomputable section

private theorem geometric_price {x : ℝ} (hx : 0 ≤ x) (hx₁ : x ≤ 1) (q : ℕ) :
    q*((1-x)*x^q) ≤ 1 := by
  have h : ∑ _i ∈ range q, x^q ≤ ∑ i ∈ range q, x^i :=
    sum_le_sum fun i hi => pow_le_pow_of_le_one hx hx₁ (mem_range.mp hi).le
  rw [sum_const,card_range,nsmul_eq_mul] at h
  linarith only [mul_le_mul_of_nonneg_right h (sub_nonneg.mpr hx₁),geom_sum_mul x q,pow_nonneg hx q]

private theorem time_price {f γ W T τ : ℝ} (hf : 0 < f) (hγ : 0 < γ) (hW : 0 ≤ W)
    (hT : 0 < T) (hτ : 0 < τ) (hτ₁ : τ ≤ 1) (q : ℕ) (hB : f⁻¹ ≤ q*W/γ+1) :
    (1-τ^2)/(1+T*W) ≤ f*max 1 (T*γ)⁻¹/τ^(2*q) := by
  let A := max 1 (T*γ)⁻¹
  let x := τ^2
  have hx : 0 ≤ x := sq_nonneg _
  have hx₁ : x ≤ 1 := pow_le_one₀ hτ.le hτ₁
  have hA : 1 ≤ A := le_max_left ..
  have hγ' : γ⁻¹ ≤ T*A := by
    calc _ = T*(T*γ)⁻¹ := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_right ..) hT.le
  have hscale : q*W/γ+1 ≤ A*(1+T*q*W) := by
    rw [div_eq_mul_inv]
    linarith only [mul_le_mul_of_nonneg_left hγ' (mul_nonneg (Nat.cast_nonneg q) hW),hA]
  have hnorm : 1 ≤ (f*A)*(1+T*q*W) := by
    have h := mul_le_mul_of_nonneg_left (hB.trans hscale) hf.le
    rwa [mul_inv_cancel₀ hf.ne',←mul_assoc] at h
  let z := (1-x)*x^q
  have hz : 0 ≤ z := mul_nonneg (sub_nonneg.mpr hx₁) (pow_nonneg hx _)
  have hzone : z ≤ 1 := mul_le_one₀ (by linarith only [hx]) (pow_nonneg hx _)
    (pow_le_one₀ hx hx₁)
  have hzq : (q:ℝ)*z ≤ 1 := geometric_price hx hx₁ q
  have hcost : z*(1+T*q*W) ≤ 1+T*W := by
    linarith only [hzone,mul_le_mul_of_nonneg_left hzq (mul_nonneg hT.le hW)]
  have hden : 0 < 1+T*W := by positivity
  apply (div_le_div_iff₀ hden (pow_pos hτ _)).mpr
  rw [pow_mul]
  exact (le_mul_of_one_le_right hz hnorm).trans ((le_of_eq (by ring :
    z*((f*A)*(1+T*q*W))=(f*A)*(z*(1+T*q*W)))).trans
      (mul_le_mul_of_nonneg_left hcost (mul_nonneg hf.le (zero_le_one.trans hA))))

/-- For a dictionary of J targets, even the measured inverse-spacing
estimate has a bandwidth-limited price at every replica order. -/
theorem gaussian_all_order_price_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let K := k+3
      let D := 2^K
      let u := pathPauliDisorderShell ω (k+1)
      let H : selfAdjoint (SharpOccupation.Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      let E := H.2.isHermitian.eigenvalues ∘ (qubitConfigFin K).symm
      ∀ q J : ℕ, ∀ T > (0:ℝ), ∀ τ ∈ Ioc (0:ℝ) 1,
        J*((1-τ^2)/(1+T*circuitHamiltonianSpectralWidth H)) ≤
          J*((((q.factorial:ℝ)/(D:ℝ)^q)*max 1 (T*recordGap k E q)⁻¹)/τ^(2*q)) := by
  filter_upwards [gaussian_spacing_bandwidth] with ω hw
  filter_upwards [hw] with k hk
  intro K D u H E q J T hT τ hτ
  have hD : 0 < D := by dsimp only [D]; positivity
  have hf : 0 < (q.factorial:ℝ)/(D:ℝ)^q := div_pos (by exact_mod_cast q.factorial_pos)
    (pow_pos (by exact_mod_cast hD) _)
  apply mul_le_mul_of_nonneg_left (time_price hf (recordGap_pos k E q)
    (circuitHamiltonianSpectralWidth_nonneg H) hT hτ.1 hτ.2 q ?_) (Nat.cast_nonneg J)
  rw [inv_div]
  exact (inverse_factorial_le_multisets hD q).trans (hk q)

#print axioms gaussian_all_order_price_floor
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
