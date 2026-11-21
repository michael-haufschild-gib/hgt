import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.ReturnSpacing
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PositiveDensityBudget
import GaloisForLFunctions.QuantumAlg.Util.Complex

/-! # Return rates in the physical projective operator error -/
open Filter Set MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- Fraction of one spectral turn covered at projective error ε. -/
def physicalArc (ε : ℝ) := 2*Real.arcsin (ε/2)/Real.pi

theorem physicalArc_spec {ε : ℝ} (hε : 0 < ε) (hsmall : ε < Real.sqrt 2) :
    physicalArc ε ∈ Ioo (0:ℝ) (1/2) ∧ zeroGateArcTolerance (physicalArc ε) = ε := by
  have hε' : ε/2 < Real.sin (Real.pi/4) := by
    rw [Real.sin_pi_div_four]
    linarith only [hsmall]
  have hn : -1 ≤ ε/2 := by linarith only [hε]
  have h1 := hε'.le.trans (Real.sin_le_one _)
  have hlt := Real.arcsin_lt_arcsin hn hε' (Real.sin_le_one _)
  rw [Real.arcsin_sin (by linarith only [Real.pi_pos]) (by linarith only [Real.pi_pos])] at hlt
  have hpos := Real.arcsin_pos.mpr (half_pos hε)
  constructor
  · constructor
    · exact div_pos (mul_pos zero_lt_two hpos) Real.pi_pos
    · exact (div_lt_iff₀ Real.pi_pos).mpr (by linarith only [hlt])
  · unfold zeroGateArcTolerance physicalArc
    rw [show Real.pi*(2*Real.arcsin (ε/2)/Real.pi)/2 = Real.arcsin (ε/2) by field_simp [Real.pi_ne_zero],
      Real.sin_arcsin hn h1]
    ring

/-- The typical-chain occupation and mean-spacing estimates at the same
physical tolerance and for the same gate budget and time origin. -/
theorem gaussian_physical_return_rates :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (s : ℕ → ℕ), subcriticalBudget s →
      ∀ ε ∈ Ioo (0:ℝ) (Real.sqrt 2), ∀ l b : ℝ, 0 < l → l < physicalArc ε → physicalArc ε < b →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let D := 2^N
        let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
        ∀ j ≤ s N, ∀ a : ℝ,
          (∀ᶠ T : ℝ in atTop, l^D < visitFraction H j ε a T ∧ visitFraction H j ε a T < b^D) ∧
          ∃ t, records H j ε a t ∧ ∀ᶠ i : ℕ in atTop, 1/b^D < (t i-a)/i ∧ (t i-a)/i < 1/l^D := by
  filter_upwards [gaussian_cheap_occupation_rate,gaussian_resolved_return_spacing_rate] with ω ho hr
  intro s hs ε he l b hl hx hb
  obtain ⟨harc,htol⟩ := physicalArc_spec he.1 he.2
  filter_upwards [ho s hs _ harc l b hl.le hx hb,hr s hs _ harc l b hl hx hb] with k hocc hret
  intro N D H j hj a
  rw [←htol]
  exact ⟨(hocc a).mono fun _ h => h j hj,hret j hj a⟩

/-- The sine chord from zero to π/6 gives a linear lower bound on the
operator tolerance for enclosing arcs up to one third of a turn. -/
theorem three_mul_le_arcTolerance {x : ℝ} (hx : 0 ≤ x) (hthird : x ≤ 1/3) :
    3*x ≤ zeroGateArcTolerance x := by
  have hs := QuantumAlg.sin_ge_slope_mul_of_nonneg_of_le (A := Real.pi/6) (x := Real.pi*x/2)
    (by positivity) (by linarith only [Real.pi_pos]) (by positivity)
    (by linarith only [mul_le_mul_of_nonneg_left hthird Real.pi_pos.le])
  rw [Real.sin_pi_div_six] at hs
  have hslope : (1/2/(Real.pi/6))*(Real.pi*x/2) = 3*x/2 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hslope] at hs
  dsimp [zeroGateArcTolerance]
  linarith only [hs]

/-- At error 1/8 even D/[8(N+1)] gates cover a fraction below (4/5)^D
in all sufficiently long observations from each fixed origin. -/
theorem gaussian_eighth_budget_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let D := 2^N
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, ∀ᶠ T : ℝ in atTop, ∀ j ≤ D/(8*(N+1)),
        visitFraction H j (1/8) a T < (4/5:ℝ)^D := by
  let x : ℝ := 3/64
  have hx : x ∈ Ioo (0:ℝ) (1/2) := by norm_num [x]
  have htol : 1/8 ≤ zeroGateArcTolerance x :=
    (by norm_num [x] : 1/8 ≤ 3*x).trans (three_mul_le_arcTolerance hx.1.le (by norm_num [x]))
  have hl : Real.log x+32*Real.log 2/(8:ℕ) < Real.log (4/5) := by
    have hlog := Real.log_lt_log (by norm_num [x] : 0 < x*(2:ℝ)^4)
      (by norm_num [x] : x*(2:ℝ)^4 < 4/5)
    rw [Real.log_mul (by norm_num [x]) (by norm_num),Real.log_pow] at hlog
    norm_num only [Nat.cast_ofNat] at *
    linarith only [hlog]
  filter_upwards [gaussian_hilbert_budget_occupation] with ω hw
  filter_upwards [hw 8 (by decide) x hx (4/5) (by norm_num) hl] with k hk
  intro N D H a
  filter_upwards [hk a,eventually_gt_atTop a] with T ht hT j hj
  apply lt_of_le_of_lt _ (ht j hj)
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hT.le)
  apply measureReal_mono _ (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)
  apply inter_subset_inter_left
  rintro t ⟨c,hc,C,hC,he⟩
  exact ⟨c,hc,C,hC,he.trans htol⟩

#print axioms gaussian_physical_return_rates
#print axioms gaussian_eighth_budget_occupation
end
end GaloisForLFunctions.HTGeometry.SharpOccupation
