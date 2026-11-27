import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.EighthPower.MergerSlack.Physical
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.PhysicalBand

/-! # Adding a repeat charge to the physical bond sweep -/
open Filter MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- Every repeat charge of order K tᵖ with p≤8 outweighs the polynomial
merger loss. A fixed positive-time band covers the rest of the interval. -/
theorem polynomial_band_of_repeats {p : ℕ} (hp : p≤8) {c : ℝ} (hc : 0<c)
    (hrep : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ∀ t∈Ioc (0:ℝ) 1,
      ∀ (C : TwoQubitCircuit (n+2)) (z : ℂ), ‖z‖=1 →
        ‖unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-z • C.eval.val‖≤1/4 →
        c*((n+1:ℕ):ℝ)*t^p≤(redundant (circuitWord C):ℝ)+1) :
    ∃ b>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let j := prefixIndex n
      let s := (1/(j:ℝ))^12
      0<s ∧ s≤1 ∧ 4*j^256≤n+1 ∧ n+2≤4*(2*j)^256 ∧
        ∀ t∈Icc s 1, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (1/4) k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
          (1+b*t^p)*((n+1:ℕ):ℝ)<(k:ℝ) := by
  obtain ⟨T,hT,_,hmer⟩ := gaussian_eighth_merger_slack hc
  obtain ⟨b,hb,hfix⟩ := gaussian_fixed_band_eighth_power
  let β := min (c/2) (b*T^8)
  refine ⟨β,lt_min (half_pos hc) (mul_pos hb (pow_pos hT 8)),?_⟩
  filter_upwards [hrep,hmer,hfix] with ω hr hm hf
  filter_upwards [hr,hm,hf T hT] with n hr hm hf
  intro j s
  obtain ⟨hs,hs₁,hN,hK,hm⟩ := hm
  refine ⟨hs,hs₁,hN,hK,?_⟩
  intro t ht k hk
  let N : ℝ := (n+1:ℕ)
  have htp := hs.trans_le ht.1
  have hN₀ : 0≤N := Nat.cast_nonneg _
  have hp₀ := pow_nonneg htp.le p
  change (1+β*t^p)*N<(k:ℝ)
  by_cases h : t≤T
  · obtain ⟨z,hz,C,hC,he⟩ := hk
    have h₁ := hm t ⟨ht.1,h⟩ C z hz he
    have h₂ := hr t ⟨htp,ht.2⟩ C z hz he
    change N+_+1<(C.gateCount:ℝ)+c/2*N*t^8 at h₁
    change c*N*t^p≤_ at h₂
    have he₁ := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one htp.le ht.2 hp)
      (mul_nonneg (half_pos hc).le hN₀)
    have he₂ := mul_le_mul_of_nonneg_right (min_le_left (c/2) (b*T^8)) (mul_nonneg hp₀ hN₀)
    dsimp only [β]
    linarith only [h₁,h₂,he₁,he₂,(Nat.cast_le (α:=ℝ)).mpr hC]
  · have hlate := hf t ⟨(lt_of_not_ge h).le,ht.2⟩ k hk
    have hscale : β*t^p≤b*t^8 := calc
      _ ≤ (b*T^8)*1 := mul_le_mul (min_le_right ..) (pow_le_one₀ htp.le ht.2) hp₀
        (mul_nonneg hb.le (pow_nonneg hT.le 8))
      _ ≤ b*t^8 := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT.le (lt_of_not_ge h).le 8) hb.le
    exact (mul_le_mul_of_nonneg_right (add_le_add le_rfl hscale) hN₀).trans_lt hlate

#print axioms polynomial_band_of_repeats
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
