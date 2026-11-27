import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.QuadraticPrecision.MergerAllowance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.QuadraticPrecision.RequiredCalls
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.Sampling.GuardedFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.PhysicalBand

/-! # Uniform positive gate excess at quadratic precision -/
open Filter MeasureTheory Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open WeakBondDeficit RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback
open RepeatedGates.PhysicalBlocks RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- Almost surely every sufficiently long frozen prefix needs a fixed
positive fraction more than a sweep at error t²/64, simultaneously at
all dates from zero (excluded) through one. -/
theorem gaussian_quadratic_precision_excess :
    ∃ b>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t∈Ioc (0:ℝ) 1, ∀ k : ℕ, HasProjectiveCircuitApproximation (n+2) (t^2/64) k
        (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
        (1+b)*((n+1:ℕ):ℝ)<(k:ℝ) := by
  obtain ⟨c,hc,hfamily⟩ := gaussian_guarded_family
  obtain ⟨h,hh,hcuts⟩ := gaussian_merger_allowance hc
  obtain ⟨b,hb,hfixed⟩ := gaussian_fixed_band_eighth_power
  refine ⟨min (c/4) (b*h^8),lt_min (by positivity) (mul_pos hb (pow_pos hh.1 _)),?_⟩
  filter_upwards [hfamily,hcuts,hfixed] with ω hw hx hl
  filter_upwards [hw,hx,hl h hh.1] with n hn hcut hlate
  intro t ht k hfit
  let u := pathPauliDisorderShell ω n
  let N : ℝ := (n+1:ℕ)
  have hN : 0<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have ht₂ := pow_le_one₀ ht.1.le ht.2 (n:=2)
  obtain ⟨z,hz,F,hF,he⟩ := hfit
  rcases le_total t h with hshort|hbig
  · have hsignal : 2*(t^2/64)≤t*h := by
      linarith only [mul_le_mul_of_nonneg_left hshort ht.1.le,sq_nonneg t]
    have hg := hcut t ⟨ht.1,hshort⟩ _ hsignal F z hz he
    obtain ⟨G,e,f,hcount,ha,hdis,hcal⟩ := hn
    have hforce := quadratic_required_calls e f ha u t ht F z hz he hdis hcal
    rw [Fintype.card_coe] at hforce
    have hr := (Nat.cast_le (α:=ℝ)).mpr hforce
    push_cast only [Nat.cast_mul,Nat.cast_ofNat] at hr
    change N+(redundant (circuitWord F):ℝ)≤(F.gateCount:ℝ)+c*N/16 at hg
    change c*N≤(G.card:ℝ) at hcount
    change (1+min (c/4) (b*h^8))*N<(k:ℝ)
    linarith only [hg,hr,hcount,(Nat.cast_le (α:=ℝ)).mpr hF,
      mul_le_mul_of_nonneg_right (min_le_left (c/4) (b*h^8)) hN.le,mul_pos hc hN]
  · have hcirc := hlate t ⟨hbig,ht.2⟩ k ⟨z,hz,F,hF,he.trans (by linarith only [ht₂])⟩
    have hb' := (min_le_right (c/4) (b*h^8)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.1.le hbig 8) hb.le)
    exact (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) hb') hN.le).trans_lt hcirc

#print axioms gaussian_quadratic_precision_excess
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
