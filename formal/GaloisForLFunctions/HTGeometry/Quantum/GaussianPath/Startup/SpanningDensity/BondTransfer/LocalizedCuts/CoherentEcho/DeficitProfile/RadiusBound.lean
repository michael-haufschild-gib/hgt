import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.PhysicalBand
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.LocalizedCuts.CoherentEcho.DeficitProfile.PrefixScale

/-! # A lower bound retaining both weak-bond savings and repeated gates -/
open Set Filter MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- With the balanced radius N t h¹⁰=1, every quarter-error circuit
pays the quartic repeat charge up to a loss of at most A N h⁹ gates.
This includes the interval between the pruned-sweep and excess regimes. -/
theorem gaussian_balanced_gate_cost :
    ∃ b>(0:ℝ), ∃ A>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ t∈Ioc (0:ℝ) 1, ∀ h∈Ioc (0:ℝ) 1, N*t*h^10=1 → ∀ k : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (1+b*t^4)*N≤(k:ℝ)+A*N*h^9 := by
  obtain ⟨b,hb,L,hL,hu⟩ := gaussian_coherent_quartic_band
  obtain ⟨c,hc,hrep⟩ := gaussian_fourth_power_repeats
  obtain ⟨d,hd,C,hC,hweak⟩ := gaussian_relative_weak_upper
  obtain ⟨B,_,hcap⟩ := gaussian_coordinate_window
  refine ⟨min b c,lt_min hb hc,C+5,by positivity,?_⟩
  filter_upwards [hu,hrep,hweak,hcap] with ω hu hr hw hx
  filter_upwards [hu,hr,hw,hx,balanced_radius_scales (L:=L) hd] with n hu hr hw hx hs
  intro N t ht h hh he k hk
  have hN : 0≤N := Nat.cast_nonneg _
  have mono {v w : ℝ} (hle : v≤w) : (1+v*t^4)*N≤(1+w*t^4)*N :=
    mul_le_mul_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_right hle (pow_nonneg ht.1.le 4))) hN
  obtain ⟨hsize,hlog,hvar|hdate⟩ := hs t ht h hh he
  · have hweak' := hw h hh hsize hlog
    have hp := mul_pos ht.1 hh.1
    have hth : t*h≤1 := (mul_le_mul ht.2 hh.2 hh.1.le zero_le_one).trans_eq (one_mul 1)
    have hrec : 1/(t*h)=N*h^9 := (div_eq_iff hp.ne').mpr (by linarith only [he])
    have htwo : 2/(t*h)=2*(N*h^9) := by rw [←hrec]; ring
    have hunit : 1≤N*h^9 := ((le_div_iff₀ hp).mpr (by simpa only [one_mul] using hth)).trans_eq hrec
    let u := pathPauliDisorderShell ω n
    obtain ⟨z,hz,F,hF,hfit⟩ := hk
    have hB : 0≤coordinateCap B n := by unfold coordinateCap; positivity
    have hJ : 43*coordinateCap B n≤(prefixIndex n:ℝ) := by linarith only [hx.2,hB]
    have hvar' : 2000000*(43*coordinateCap B n)^2*t≤h := by
      have hp' := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0:ℝ)≤43) hB) hJ 2
      linarith only [hvar,mul_le_mul_of_nonneg_right hp' ht.1.le]
    have hg := echo_reciprocal_allowance u F ht.1 hh.1 hB hx.1 hth hvar' z hz hfit
    have hr' := hr t ht F z hz hfit
    change N+_≤(F.gateCount:ℝ)+((weakEdges u h).card:ℝ)+2/(t*h)+2 at hg
    change ((weakEdges u h).card:ℝ)≤C*N*h^9 at hweak'
    rw [htwo] at hg
    apply (mono (min_le_right b c)).trans
    linarith only [hr',hg,hweak',hunit,(Nat.cast_le (α:=ℝ)).mpr hF]
  · apply ((mono (min_le_left b c)).trans_lt (hu t ht hdate k hk)).le.trans
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by positivity) hN) (pow_nonneg hh.1.le 9))

#print axioms gaussian_balanced_gate_cost
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
