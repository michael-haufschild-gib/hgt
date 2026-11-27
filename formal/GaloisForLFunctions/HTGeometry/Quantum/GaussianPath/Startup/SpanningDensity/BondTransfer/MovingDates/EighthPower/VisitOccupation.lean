import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.EighthPower.PhysicalBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.HalfDensity

/-! # Polynomial residence widths at half of one bond sweep -/
open Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks
noncomputable section

/-- Even at exactly half of one bond sweep, all visits in a fixed horizon
have polynomially small span. For budgets above half, d⁸ gives the
allowed excess fraction. Counting clusters controls every interval origin. -/
theorem gaussian_half_sweep_cluster_width {H : ℝ} (hH : 1≤H) :
    ∃ b>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      let s := (1/(prefixIndex n:ℝ))^12
      ∀ d∈Icc s 1, ∀ r : ℕ, ((2*r:ℕ):ℝ)≤(1+b*d^8)*N → ∀ ε : ℝ, ε≤1/8 →
        let E := {v : ℝ | HasProjectiveCircuitApproximation (n+2) ε r
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) v)}
        (∀ v∈E, ∀ w∈E, |w-v|<d ∨ H < |w-v|) ∧
          ∀ a T : ℝ, 0≤T → volume.real (E∩Icc a (a+T))≤(1+T/H)*d := by
  obtain ⟨b,hb,hband⟩ := gaussian_polynomial_eighth_power_band
  obtain ⟨c,hc,hlate⟩ := gaussian_excluded_compact_lags (T:=H) zero_lt_one
  refine ⟨min b c,lt_min hb hc,?_⟩
  filter_upwards [hband,hlate] with ω hw hl
  filter_upwards [hw,hl] with n hn hlong
  intro N s d hd r hbudget ε hε E
  obtain ⟨hs,_,_,_,hfit⟩ := hn
  let G := (⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩ :
    selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ))
  have hN : 0≤N := Nat.cast_nonneg _
  have hd₀ := hs.le.trans hd.1
  have gap (v : ℝ) (hv : v∈E) (w : ℝ) (hw : w∈E) : |w-v|<d ∨ H < |w-v| := by
    by_contra! hh
    have hprice : ((r+r:ℕ):ℝ)≤(1+min b c*d^8)*N := by rwa [←two_mul]
    rcases le_total |w-v| 1 with hshort|hafter
    · have h := affordable_add_time G (x := -v) (y := w) (i:=r) (j:=r) (hv.neg_time G) hw
      rw [show -v+w=w-v by ring] at h
      have hab : HasProjectiveCircuitApproximation (n+2) (ε+ε) (r+r) (unitaryEvolution G.val |w-v|) := by
        rcases le_total 0 (w-v) with h'|h'
        · rwa [abs_of_nonneg h']
        · rw [abs_of_nonpos h']; exact h.neg_time G
      obtain ⟨z,hz,C,hC,he⟩ := hab
      have hg := hfit |w-v| ⟨hd.1.trans hh.1,hshort⟩ (r+r) ⟨z,hz,C,hC,he.trans (by linarith only [hε])⟩
      have hp := mul_le_mul (min_le_left b c) (pow_le_pow_left₀ hd₀ hh.1 8) (pow_nonneg hd₀ 8) hb.le
      exact hg.not_ge (hprice.trans (mul_le_mul_of_nonneg_right (add_le_add_right hp 1) hN))
    · have hg := hlong v w ⟨hafter,hh.2⟩ r r ε ε (by linarith only [hε]) hv hw
      have hp := mul_le_mul (min_le_right b c) (pow_le_one₀ hd₀ hd.2 (n:=8)) (pow_nonneg hd₀ 8) hc.le
      rw [mul_one] at hp
      exact hg.not_ge (hprice.trans (mul_le_mul_of_nonneg_right (add_le_add_right hp 1) hN))
  exact ⟨gap,LocalEcho.occupation_of_forbidden_lags E d H hd₀ (zero_lt_one.trans_le hH) gap⟩

#print axioms gaussian_half_sweep_cluster_width
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
