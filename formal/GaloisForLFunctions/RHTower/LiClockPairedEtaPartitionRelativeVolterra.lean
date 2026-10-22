import GaloisForLFunctions.RHTower.LiClockPairedEtaRelativeVolterraSeries
import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousPartitionVolterra
import GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionMixedSource
import GaloisForLFunctions.RHTower.LiClockPairedEtaArithmeticCancellation
import GaloisForLFunctions.RHTower.LiClockPairedEtaCompletionMoments
import GaloisForLFunctions.RHTower.LiClockPairedEtaContiguousComparison

/-!
# Relative Volterra law for the finite paired-eta gap clock

Let `Z_N(s) = ∑_{n<N} ∫_{log(2n+1)}^{log(2n+2)} e^{-su} du` be the finite paired-eta Laplace
partition and `U_L(s) = ∫_0^L e^{-su} du` its filled contiguous model with `L = log(2N)`. Their
half-tilted, normalized difference measures have even Borel kernels `K_N` and `K_L`; the
independent mixed source has Borel kernel `M_N(t) = ∑_j E[(X+Y)^{2j}] t^{2j}/((2j)!)²` and signed
forcing `F_N(t) = ∑_j E[(X-Y)(X+Y)^{2j+1}] t^{2j+2}/((2j+2)!(2j+1)!)`. This module identifies
`M_N` and `F_N` as derivatives of Volterra convolutions of `K_N` and `K_L`, splits the clock of
the gap ratio `Z_N/U_L` as partition clock minus contiguous clock, and combines the two
individual clock Volterra laws into the relative law `2 ∫_0^t Re(gap clock)(s) M_N(t-s) ds = F_N(t)`.

## Main results

- `hasDerivAt_liClockPairedEtaPartitionMixedPrimitive`: `(K_N ⋆ K_L)' = M_N`.
- `hasDerivAt_liClockPairedEtaPartitionSignedConvolution`:
  `((s K_N'(s)) ⋆ K_L - K_N ⋆ (s K_L'(s)))' = F_N`.
- `liClockPairedEtaFiniteGapClockResponse_eq_partition_sub_contiguous`: gap clock = partition
  clock minus contiguous partition clock, on a zero-free disk.
- `liClockPairedEtaPartitionRelativeForcing_volterra`: the relative Volterra identity for `t ≥ 0`.
- `liClockPairedEtaPartition_exists_relative_forcing_radius`: for every `N > 0` some radius
  `r ∈ (0, 1/2)` makes both partitions zero-free on the closed disk and the relative identity hold.

## Hypotheses

All results take `0 < N`. The clock identities additionally take a radius `0 < r < 1/2` and the
hypothesis `hclosed` that `Z_N(1/2 + z i) ≠ 0` for `|z| ≤ r`; this is a genuine contour
precondition, and `liClockPairedEtaPartition_exists_relative_forcing_radius` discharges it
unconditionally by producing such a radius.
-/

open Complex Filter Set Metric Topology MeasureTheory ProbabilityTheory RiemannGaussian
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower
noncomputable section

private theorem relLogLength_pos {N : ℕ} (hN : 0<N) :
    0<Real.log (2*(N:ℝ)) := by
  have hN1 : (1:ℝ)≤(N:ℝ) := by
    exact_mod_cast (show 1≤N by omega)
  exact Real.log_pos (by linarith)

private theorem relActualBorel_eq_generic (N : ℕ) :
    liClockPairedEtaPartitionBorelKernel N =
      relEvenBorelSeries (liClockPairedEtaSymmetrizedEvenMoment N) := by
  funext t
  exact liClockPairedEtaPartitionBorelKernel_eq_tsum N t

private theorem relReferenceBorel_eq_generic (L : ℝ) :
    liClockPairedEtaContiguousBorelKernel L =
      relEvenBorelSeries (liClockPairedEtaContiguousSymmetrizedEvenMoment L) := by
  funext t
  exact liClockPairedEtaContiguousBorelKernel_eq_tsum L t

private theorem relActualMoment_norm {N : ℕ} (hN : 0<N) (j : ℕ) :
    ‖liClockPairedEtaSymmetrizedEvenMoment N j‖ ≤
      Real.log (2*(N:ℝ))^(2*j) := by
  rw [Real.norm_of_nonneg (liClockPairedEtaSymmetrizedEvenMoment_pos hN j).le]
  exact liClockPairedEtaSymmetrizedEvenMoment_le_log_power hN j

private theorem relReferenceMoment_norm {L : ℝ} (hL : 0<L) (j : ℕ) :
    ‖liClockPairedEtaContiguousSymmetrizedEvenMoment L j‖ ≤ L^(2*j) := by
  rw [Real.norm_of_nonneg (liClockPairedEtaContiguousSymmetrizedEvenMoment_pos hL j).le]
  exact liClockPairedEtaContiguousSymmetrizedEvenMoment_le_power hL j

private theorem relSignedSeries_shift {c s : ℕ → ℝ} (hzero : c 0=0)
    (hnext : ∀j, c (j+1)=(2*j+2:ℝ)*s j) (t : ℝ)
    (hs : Summable (fun j => ‖s j*t^(2*j+2)/
      (((2*j+2).factorial:ℝ)*((2*j+1).factorial:ℝ))‖)) :
    (∑'n, c n*t^(2*n)/((2*n).factorial:ℝ)^2) =
      ∑'j, s j*t^(2*j+2)/(((2*j+2).factorial:ℝ)*((2*j+1).factorial:ℝ)) := by
  have heq : ∀j, c (j+1)*t^(2*(j+1))/((2*(j+1)).factorial:ℝ)^2 =
      s j*t^(2*j+2)/(((2*j+2).factorial:ℝ)*((2*j+1).factorial:ℝ)) := by
    intro j
    have hfac : ((2*j+2).factorial:ℝ) =
        (2*j+2:ℝ)*((2*j+1).factorial:ℝ) := by
      rw [show 2*j+2=(2*j+1)+1 by omega, Nat.factorial_succ]
      push_cast
      ring
    have hn : (2*j+2:ℝ)≠0 := by positivity
    have hf : ((2*j+1).factorial:ℝ)≠0 := by
      exact_mod_cast Nat.factorial_ne_zero (2*j+1)
    rw [hnext, show 2*(j+1)=2*j+2 by omega, hfac]
    field_simp
  have hshift : Summable (fun j => c (j+1)*t^(2*(j+1))/((2*(j+1)).factorial:ℝ)^2) :=
    hs.of_norm.congr (fun j => (heq j).symm)
  have hfull : Summable (fun n => c n*t^(2*n)/((2*n).factorial:ℝ)^2) :=
    (summable_nat_add_iff 1).mp hshift
  rw [hfull.tsum_eq_zero_add]
  simp only [hzero, zero_mul, zero_div, zero_add]
  exact tsum_congr heq

private theorem relSkew_zero (d e : ℕ → ℝ) :
    relEvenBinomialSkew d e 0=0 := by
  simp [relEvenBinomialSkew]

private theorem relSkew_succ_expansion (d e : ℕ → ℝ) (j : ℕ) :
    relEvenBinomialSkew d e (j+1) =
      ∑a∈Finset.range (j+2), ((2*a:ℝ)-2*((j+1-a:ℕ):ℝ))*
        (Nat.choose (2*j+2) (2*a):ℝ)*d a*e (j+1-a) := by
  unfold relEvenBinomialSkew
  rw [show j+1+1=j+2 by omega, show 2*(j+1)=2*j+2 by omega]
  apply Finset.sum_congr rfl
  intro a ha
  have haj : a≤j+1 := by
    simp only [Finset.mem_range] at ha
    omega
  rw [Nat.cast_sub haj]

private theorem relMixedBorel_eq_generic {N : ℕ} (hN : 0<N) :
    liClockPairedEtaPartitionMixedBorelKernel N =
      relEvenBorelSeries (relEvenBinomialMoment
        (liClockPairedEtaSymmetrizedEvenMoment N)
        (liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))))) := by
  funext t
  simp only [liClockPairedEtaPartitionMixedBorelKernel, relEvenBorelSeries,
    relEvenBinomialMoment, liClockPairedEtaPartitionMixedEvenMoment_eq_sum hN]

private theorem relSignedForcing_eq_generic {N : ℕ} (hN : 0<N) :
    liClockPairedEtaPartitionRelativeForcing N =
      relEvenBorelSeries (relEvenBinomialSkew
        (liClockPairedEtaSymmetrizedEvenMoment N)
        (liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ))))) := by
  funext t
  symm
  apply relSignedSeries_shift
    (relSkew_zero (liClockPairedEtaSymmetrizedEvenMoment N)
      (liClockPairedEtaContiguousSymmetrizedEvenMoment (Real.log (2*(N:ℝ)))))
  · intro j
    rw [relSkew_succ_expansion,
      ← liClockPairedEtaPartitionMixedSignedMoment_mul_eq_sum hN j]
  · apply (summable_norm_liClockPairedEtaPartitionRelativeForcingTerm hN (t:ℂ)).congr
    intro j
    norm_cast

private theorem relEtaSphereGuard {N : ℕ} {r : ℝ} (hrhalf : r<1/2)
    (hclosed : ∀z∈closedBall (0:ℂ) r,
      pairedEtaFiniteLaplacePartition N (1/2+z*I)≠0) :
    ∀z∈sphere (0:ℂ) r, pairedEtaCorePartialSum N (1/2+z*I)≠0 := by
  intro z hz
  have hn : ‖z‖=r := by
    simpa only [mem_sphere, dist_zero_right] using hz
  have hi := abs_le.mp ((Complex.abs_im_le_norm z).trans hn.le)
  have hspos : 0<(1/2+z*I : ℂ).re := by
    have heq : (1/2+z*I : ℂ).re=(1/2:ℝ)-z.im := by
      norm_num [Complex.add_re, Complex.mul_re]
      ring
    rw [heq]
    linarith [hi.2]
  have hsne : (1/2+z*I : ℂ)≠0 := by
    intro hs
    rw [hs] at hspos
    norm_num at hspos
  rw [pairedEtaCorePartialSum_eq_mul_finiteLaplacePartition]
  exact mul_ne_zero hsne (hclosed z (by
    simpa only [mem_closedBall, dist_zero_right] using hn.le))


/-- For `N > 0`, the Volterra convolution of the actual Borel kernel `K_N` with the contiguous
kernel `K_L` (`L = log 2N`) has derivative the mixed Borel kernel `M_N(t)` at every `t`. -/
theorem hasDerivAt_liClockPairedEtaPartitionMixedPrimitive
    {N : ℕ} (hN : 0<N) (t : ℝ) :
  HasDerivAt (GaloisForLFunctions.HTGeometry.volterraConv
    (liClockPairedEtaPartitionBorelKernel N)
    (liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ)))))
    (liClockPairedEtaPartitionMixedBorelKernel N t) t := by
  have hL := relLogLength_pos hN
  have h := (relEvenBorelSeries_convolution hL.le hL.le
    (relActualMoment_norm hN) (relReferenceMoment_norm hL) t).2.2.1
  simpa only [← relActualBorel_eq_generic N,
    ← relReferenceBorel_eq_generic (Real.log (2*(N:ℝ))),
    ← relMixedBorel_eq_generic hN] using h

/-- For `N > 0`, the skew convolution `(s K_N'(s)) ⋆ K_L - K_N ⋆ (s K_L'(s))` has derivative
the signed relative forcing `F_N(t)` at every `t`. -/
theorem hasDerivAt_liClockPairedEtaPartitionSignedConvolution
    {N : ℕ} (hN : 0<N) (t : ℝ) :
  HasDerivAt (fun u =>
    GaloisForLFunctions.HTGeometry.volterraConv
      (fun s => s*deriv (liClockPairedEtaPartitionBorelKernel N) s)
      (liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ)))) u -
    GaloisForLFunctions.HTGeometry.volterraConv
      (liClockPairedEtaPartitionBorelKernel N)
      (fun s : ℝ => s*deriv
        (fun v : ℝ => liClockPairedEtaContiguousBorelKernel (Real.log (2*(N:ℝ))) v) s) u)
    (liClockPairedEtaPartitionRelativeForcing N t) t := by
  have hL := relLogLength_pos hN
  have h := (relEvenBorelSeries_skew_convolution hL.le hL.le
    (relActualMoment_norm hN) (relReferenceMoment_norm hL) t).2.1
  simpa only [← relActualBorel_eq_generic N,
    ← relReferenceBorel_eq_generic (Real.log (2*(N:ℝ))),
    ← relSignedForcing_eq_generic hN] using h

/-- For `N > 0`, `0 < r < 1/2`, and assuming `hclosed` (`Z_N(1/2 + z i) ≠ 0` on `|z| ≤ r`), the
clock of the gap ratio `Z_N/U_{log 2N}` is the partition clock minus the contiguous clock. -/
theorem liClockPairedEtaFiniteGapClockResponse_eq_partition_sub_contiguous
    {N : ℕ} (hN : 0<N) {r : ℝ} (hr : 0<r) (hrhalf : r<1/2)
    (hclosed : ∀z∈closedBall (0:ℂ) r,
      pairedEtaFiniteLaplacePartition N (1/2+z*I)≠0) (t : ℂ) :
  liClockPairedEtaFiniteGapClockResponse N r t =
    liClockPairedEtaPartitionClockResponse N r t-
      liClockPairedEtaContiguousPartitionClock (Real.log (2*(N:ℝ))) r t := by
  have hN1 : (1:ℝ)≤(N:ℝ) := by
    exact_mod_cast (show 1≤N by omega)
  have hL : 0<Real.log (2*(N:ℝ)) := Real.log_pos (by linarith)
  have heta := relEtaSphereGuard hrhalf hclosed
  have hA := liClockPairedEtaFiniteClockResponse_eq_neg_two_sinh_add_partition_add_completion
    N hr hrhalf heta t
  have hF := liClockPairedEtaFiniteClockResponse_eq_completion_sub_contiguous_add_gap
    hN hr hrhalf heta t
  have hU := liClockPairedEtaContiguousPartitionClock_eq_two_sinh_sub_clock
    hL hr hrhalf t
  linear_combination hA - hF + hU

private theorem relVolterra_orientation (f g : ℝ → ℝ) (t : ℝ) :
    volterraConv f g t = ∫s in (0:ℝ)..t, f s*g (t-s) := by
  rw [volterraConv_comm]
  change (∫s in (0:ℝ)..t, g (t-s)*f s) = ∫s in (0:ℝ)..t, f s*g (t-s)
  apply intervalIntegral.integral_congr
  intro s _
  ring

/-- Relative Volterra law: for `N > 0`, `0 < r < 1/2`, assuming `hclosed` (zero-free closed
disk for `Z_N`), and `t ≥ 0`, `2 ∫_0^t Re(gap clock)(s) M_N(t - s) ds = F_N(t)`. -/
theorem liClockPairedEtaPartitionRelativeForcing_volterra
    {N : ℕ} (hN : 0<N) {r : ℝ} (hr : 0<r) (hrhalf : r<1/2)
    (hclosed : ∀z∈closedBall (0:ℂ) r,
      pairedEtaFiniteLaplacePartition N (1/2+z*I)≠0)
    {t : ℝ} (ht : 0≤t) :
  2*(∫s in (0:ℝ)..t,
    (liClockPairedEtaFiniteGapClockResponse N r (s:ℂ)).re*
      liClockPairedEtaPartitionMixedBorelKernel N (t-s)) =
    liClockPairedEtaPartitionRelativeForcing N t := by
  have hL := relLogLength_pos hN
  have hA : ∀u:ℝ, 0≤u →
      2*volterraConv (liClockPairedEtaPartitionClockResponseReal N r)
        (relEvenBorelSeries (liClockPairedEtaSymmetrizedEvenMoment N)) u =
      u*deriv (relEvenBorelSeries (liClockPairedEtaSymmetrizedEvenMoment N)) u := by
    intro u hu
    simpa only [relActualBorel_eq_generic N, relVolterra_orientation] using
      liClockPairedEtaPartitionClockResponse_volterra hN hr hclosed hu
  have hU : ∀u:ℝ, 0≤u →
      2*volterraConv (liClockPairedEtaContiguousPartitionClockReal (Real.log (2*(N:ℝ))) r)
        (relEvenBorelSeries (liClockPairedEtaContiguousSymmetrizedEvenMoment
          (Real.log (2*(N:ℝ))))) u =
      u*deriv (relEvenBorelSeries (liClockPairedEtaContiguousSymmetrizedEvenMoment
        (Real.log (2*(N:ℝ))))) u := by
    intro u hu
    simpa only [relReferenceBorel_eq_generic (Real.log (2*(N:ℝ))), relVolterra_orientation] using
      liClockPairedEtaContiguousPartitionClock_volterra hL hr hrhalf hu
  have h := relEvenBorelSeries_relative_volterra hL.le hL.le
    (relActualMoment_norm hN) (relReferenceMoment_norm hL)
    (liClockPairedEtaPartitionClockResponseReal N r)
    (liClockPairedEtaContiguousPartitionClockReal (Real.log (2*(N:ℝ))) r)
    (continuous_liClockPairedEtaPartitionClockResponseReal hr hclosed)
    (continuous_liClockPairedEtaContiguousPartitionClockReal hL hr hrhalf) hA hU ht
  rw [← relMixedBorel_eq_generic hN, ← relSignedForcing_eq_generic hN,
    relVolterra_orientation] at h
  simpa only [liClockPairedEtaFiniteGapClockResponse_eq_partition_sub_contiguous
      hN hr hrhalf hclosed, Complex.sub_re, liClockPairedEtaPartitionClockResponseReal,
    liClockPairedEtaContiguousPartitionClockReal] using h

/-- Unconditionally, for every `N > 0` there is `r ∈ (0, 1/2)` with `Z_N` and `U_{log 2N}` both
nonzero at `1/2 + z i` for `|z| ≤ r`, and the relative Volterra law holds for all `t ≥ 0`. -/
theorem liClockPairedEtaPartition_exists_relative_forcing_radius
    {N : ℕ} (hN : 0<N) :
  ∃r:ℝ, 0<r ∧ r<1/2 ∧
    (∀z∈closedBall (0:ℂ) r,
      pairedEtaFiniteLaplacePartition N (1/2+z*I)≠0) ∧
    (∀z∈closedBall (0:ℂ) r,
      liClockPairedEtaContiguousPartition (Real.log (2*(N:ℝ))) (1/2+z*I)≠0) ∧
    ∀t:ℝ, 0≤t →
      2*(∫s in (0:ℝ)..t,
        (liClockPairedEtaFiniteGapClockResponse N r (s:ℂ)).re*
          liClockPairedEtaPartitionMixedBorelKernel N (t-s)) =
        liClockPairedEtaPartitionRelativeForcing N t := by
  obtain ⟨r, hr, hrhalf, hA, hU⟩ := liClockPairedEtaPartition_exists_common_regular_radius hN
  exact ⟨r, hr, hrhalf, hA, hU,
    fun t ht => liClockPairedEtaPartitionRelativeForcing_volterra hN hr hrhalf hA ht⟩

end
end RHTower
