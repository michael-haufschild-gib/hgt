import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.QuadraticPrecision.MergerAllowance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.QuadraticPrecision.CollectiveError
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.Sampling.GuardedFamily
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.FixedWidth.PhysicalBand

/-! # Squared projective error trades against physical gate count -/
open MeasureTheory Set Filter Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates RepeatedGates.Temporal RepeatedGates.Temporal.Feedback RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- Below a fixed multiple of time in operator error, losing g calls
from the indicated above-sweep threshold costs order g t⁴ in squared
error. This holds simultaneously at all dates up to one. -/
theorem gaussian_gate_error_exchange :
    ∃ a>(0:ℝ), ∃ b>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ t∈Ioc (0:ℝ) 1, ∀ (ε : ℝ) (k : ℕ), ε≤a*t →
        HasProjectiveCircuitApproximation (n+2) ε k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
          ((1+b)*N-(k:ℝ))*t^4<2048*ε^2 := by
  obtain ⟨c,hc,hfamily⟩ := gaussian_guarded_family
  obtain ⟨h,hh,hcuts⟩ := gaussian_merger_allowance hc
  obtain ⟨d,hd,hfixed⟩ := gaussian_fixed_band_eighth_power
  let a := min (h/2) (1/8)
  let b := min (c/4) (d*h^8)
  have ha : 0<a := lt_min (half_pos hh.1) (by norm_num)
  have hb : 0<b := lt_min (by positivity) (mul_pos hd (pow_pos hh.1 8))
  refine ⟨a,ha,b,hb,?_⟩
  filter_upwards [hfamily,hcuts,hfixed] with ω hw hx hl
  filter_upwards [hw,hx,hl h hh.1] with n hn hcut hlate
  intro N t ht ε k hε hfit
  obtain ⟨z,hz,C,hC,he⟩ := hfit
  have hN : 0<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have ht4 := pow_pos ht.1 4
  have hε' : ε≤t/8 := hε.trans ((mul_le_mul_of_nonneg_right (min_le_right ..) ht.1.le).trans_eq (by ring))
  rcases le_total t h with hs|hl
  · have hsignal : 2*ε≤t*h := by linarith only [hε,mul_le_mul_of_nonneg_right (min_le_left (h/2) (1/8)) ht.1.le]
    obtain ⟨F,e,f,hcount,hadj,hdis,hcal⟩ := hn
    have hmerge := hcut t ⟨ht.1,hs⟩ ε hsignal C z hz he
    have hrep := collective_error_charge e f hadj _ t ht C z hz hε' he hdis hcal
    rw [Fintype.card_coe] at hrep
    change c*N≤(F.card:ℝ) at hcount
    change N+(redundant (circuitWord C):ℝ)≤(C.gateCount:ℝ)+c*N/16 at hmerge
    have hg := hmerge.trans (add_le_add (Nat.cast_le.mpr hC) le_rfl)
    have hbN := mul_le_mul_of_nonneg_right (min_le_left (c/4) (d*h^8)) hN.le
    change b*N≤c/4*N at hbN
    linarith only [mul_le_mul_of_nonneg_right hcount ht4.le,hrep,mul_le_mul_of_nonneg_right hg ht4.le,
      mul_le_mul_of_nonneg_right hbN ht4.le,mul_pos (mul_pos hc hN) ht4]
  · have hlate' := hlate t ⟨hl,ht.2⟩ k ⟨z,hz,C,hC,he.trans (by linarith only [ht.2,hε'])⟩
    have hb' := (min_le_right (c/4) (d*h^8)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh.1.le hl 8) hd.le)
    have hk : (1+b)*N<(k:ℝ) := (mul_le_mul_of_nonneg_right (add_le_add le_rfl hb') hN.le).trans_lt hlate'
    exact (mul_neg_of_neg_of_pos (sub_neg.mpr hk) ht4).trans_le (by positivity)

/-- The entire interval has a positive gate excess at precision
proportional to the smaller of t and √(K−1)t². -/
theorem gaussian_collective_precision_excess :
    ∃ γ>(0:ℝ), ∃ β>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ t∈Ioc (0:ℝ) 1, ∀ k : ℕ,
        HasProjectiveCircuitApproximation (n+2) (γ*min t (sqrt N*t^2)) k
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) →
          (1+β)*N<(k:ℝ) := by
  obtain ⟨a,ha,b,hb,hw⟩ := gaussian_gate_error_exchange
  let s := sqrt (b/4096)
  let l := min a s
  have hs : 0<s := sqrt_pos.mpr (by positivity)
  have hl : 0<l := lt_min ha hs
  refine ⟨l,hl,b/2,half_pos hb,?_⟩
  filter_upwards [hw] with ω hw
  filter_upwards [hw] with n hn
  intro N t ht k hfit
  let ε := l*min t (sqrt N*t^2)
  have hN : 0≤N := Nat.cast_nonneg _
  have hm : 0≤ min t (sqrt N*t^2) := le_min ht.1.le (mul_nonneg (sqrt_nonneg _) (sq_nonneg _))
  have hε : ε≤a*t := mul_le_mul (min_le_left ..) (min_le_left ..) hm ha.le
  have hx := hn t ht ε k hε hfit
  have hup : ε≤ s*(sqrt N*t^2) := mul_le_mul (min_le_right ..) (min_le_right ..) hm hs.le
  have hs' : s^2=b/4096 := sq_sqrt (by positivity)
  have hq := pow_le_pow_left₀ (mul_nonneg hl.le hm) hup 2
  change ε^2≤(s*(sqrt N*t^2))^2 at hq
  have hcoef : (s*(sqrt N*t^2))^2=(b/4096)*N*t^4 := by
    rw [mul_pow (s:ℝ),mul_pow (sqrt N),hs',sq_sqrt hN]; ring
  rw [hcoef] at hq
  change ((1+b)*N-(k:ℝ))*t^4<2048*ε^2 at hx
  by_contra! hk
  linarith only [mul_le_mul_of_nonneg_right hk (pow_nonneg ht.1.le 4),hq,hx]

#print axioms gaussian_gate_error_exchange
#print axioms gaussian_collective_precision_excess
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
