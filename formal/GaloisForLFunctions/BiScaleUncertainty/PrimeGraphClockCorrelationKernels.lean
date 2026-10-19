import GaloisForLFunctions.BiScaleUncertainty.PrimeGraphClockOffDiagonalSynthesisAndStationaryEnergyProducer

/-!
# Mass and edge correlation kernels for the literal prime clocks

For positive `N`, `p`, and `q`, put `t = log (N/q)` and `lag = log (q/p)`.
The mass and edge pairings of the canonical clock atoms are respectively
`N/(p*q)` times the two kernels below. Their difference is exactly the signed
source pairing, with no discarded diagonal, cutoff or measure term.

These are explicit integral readouts in the literal critical Abel profile.
They retain the center `t`, cutoff `k`, and the nontranslation-invariant mass
and edge measures. They do not assert a lag-only reduction, evaluate the
integrals in closed form, or prove the sign/estimate needed for RH.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty
open _root_.RHTower _root_.RHTower.CHMDDoobGraph
noncomputable section
set_option autoImplicit false

/-- The compactly cut off critical Abel profile at logarithmic center `t`. -/
def primeClockProfile (k : ℕ) (t x : ℝ) : ℝ :=
  cutoff k x * criticalAbelLogProfile (t - x)

/-- Mass correlation at a common center and a logarithmic lag. -/
def primeClockMassKernel (k : ℕ) (t lag : ℝ) : ℝ :=
  ∫ x, primeClockProfile k (t + lag) x * primeClockProfile k t x ∂massMeasure

/-- Edge correlation, retaining every archimedean and prime-power edge. -/
def primeClockEdgeKernel (k : ℕ) (t lag : ℝ) : ℝ :=
  ∫ e, difference (primeClockProfile k (t + lag)) e *
    difference (primeClockProfile k t) e ∂edgeMeasure

/-- Vertex readout with the scalar clock normalization separated. -/
theorem canonicalPrimeGraphClockAtom_fst_profile_ae (k N p : ℕ) :
    (canonicalPrimeGraphClockAtom k N p).val.fst =ᵐ[massMeasure]
      fun x => (Real.sqrt N / p) * primeClockProfile k (Real.log ((N : ℝ) / p)) x := by
  filter_upwards [canonicalPrimeGraphClockAtom_fst_ae k N p] with x hx
  simpa only [primeClockProfile, mul_assoc] using hx

/-- The edge component is the literal difference of the vertex profile. -/
theorem canonicalPrimeGraphClockAtom_snd_profile_ae (k N p : ℕ) :
    (canonicalPrimeGraphClockAtom k N p).val.snd =ᵐ[edgeMeasure]
      fun e => (Real.sqrt N / p) *
        difference (primeClockProfile k (Real.log ((N : ℝ) / p))) e := by
  have hg := (canonicalPrimeGraphClockAtom k N p).property
  filter_upwards [hg,
    nonsingular_left.ae (canonicalPrimeGraphClockAtom_fst_profile_ae k N p),
    nonsingular_right.ae (canonicalPrimeGraphClockAtom_fst_profile_ae k N p)]
    with e he hl hr
  change _ = _ - _ at he
  rw [he, hl, hr]
  simp only [difference, mul_sub]

private theorem clock_scale_product (N p q : ℕ) :
    (Real.sqrt (N : ℝ) / p) * (Real.sqrt (N : ℝ) / q) =
      (N : ℝ) / ((p : ℝ) * q) := by
  rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg N)]

/-- Exact mass pairing, including the common center and normalization. -/
theorem canonicalPrimeGraphClockAtom_mass_inner_eq_kernel {k N p q : ℕ}
    (hN : 0 < N) (hp : 0 < p) (hq : 0 < q) :
    ⟪(canonicalPrimeGraphClockAtom k N p).val.fst,
      (canonicalPrimeGraphClockAtom k N q).val.fst⟫_ℝ =
      ((N : ℝ) / ((p : ℝ) * q)) *
        primeClockMassKernel k (Real.log ((N : ℝ) / q)) (Real.log ((q : ℝ) / p)) := by
  have hlag : Real.log ((N : ℝ) / p) =
      Real.log ((N : ℝ) / q) + Real.log ((q : ℝ) / p) := by
    simpa using (primeClock_log_lag_identity hN hp hq 0).2
  rw [L2.inner_def, primeClockMassKernel, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [canonicalPrimeGraphClockAtom_fst_profile_ae k N p,
    canonicalPrimeGraphClockAtom_fst_profile_ae k N q] with x hx hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy, hlag]
  calc _ = ((Real.sqrt ↑N / ↑p) * (Real.sqrt ↑N / ↑q)) *
      (primeClockProfile k (Real.log (↑N / ↑q) + Real.log (↑q / ↑p)) x *
        primeClockProfile k (Real.log (↑N / ↑q)) x) := by ring
    _ = _ := by rw [clock_scale_product]

/-- Exact edge pairing under the full arithmetic edge measure. -/
theorem canonicalPrimeGraphClockAtom_edge_inner_eq_kernel {k N p q : ℕ}
    (hN : 0 < N) (hp : 0 < p) (hq : 0 < q) :
    ⟪(canonicalPrimeGraphClockAtom k N p).val.snd,
      (canonicalPrimeGraphClockAtom k N q).val.snd⟫_ℝ =
      ((N : ℝ) / ((p : ℝ) * q)) *
        primeClockEdgeKernel k (Real.log ((N : ℝ) / q)) (Real.log ((q : ℝ) / p)) := by
  have hlag : Real.log ((N : ℝ) / p) =
      Real.log ((N : ℝ) / q) + Real.log ((q : ℝ) / p) := by
    simpa using (primeClock_log_lag_identity hN hp hq 0).2
  rw [L2.inner_def, primeClockEdgeKernel, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [canonicalPrimeGraphClockAtom_snd_profile_ae k N p,
    canonicalPrimeGraphClockAtom_snd_profile_ae k N q] with e hx hy
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hx, hy, hlag]
  calc _ = ((Real.sqrt ↑N / ↑p) * (Real.sqrt ↑N / ↑q)) *
      (difference (primeClockProfile k (Real.log (↑N / ↑q) + Real.log (↑q / ↑p))) e *
        difference (primeClockProfile k (Real.log (↑N / ↑q))) e) := by ring
    _ = _ := by rw [clock_scale_product]

/-- The complete signed pairing is edge correlation minus mass correlation. -/
theorem canonicalPrimeGraphClockAtom_sourcePair_eq_kernel {k N p q : ℕ}
    (hN : 0 < N) (hp : 0 < p) (hq : 0 < q) :
    sourcePair (canonicalPrimeGraphClockAtom k N p) (canonicalPrimeGraphClockAtom k N q) =
      ((N : ℝ) / ((p : ℝ) * q)) *
        (primeClockEdgeKernel k (Real.log ((N : ℝ) / q)) (Real.log ((q : ℝ) / p)) -
          primeClockMassKernel k (Real.log ((N : ℝ) / q)) (Real.log ((q : ℝ) / p))) := by
  change ⟪(canonicalPrimeGraphClockAtom k N p).val.snd,
      (canonicalPrimeGraphClockAtom k N q).val.snd⟫_ℝ -
    ⟪(canonicalPrimeGraphClockAtom k N p).val.fst,
      (canonicalPrimeGraphClockAtom k N q).val.fst⟫_ℝ = _
  rw [canonicalPrimeGraphClockAtom_edge_inner_eq_kernel hN hp hq,
    canonicalPrimeGraphClockAtom_mass_inner_eq_kernel hN hp hq, mul_sub]

end
end GaloisForLFunctions.BiScaleUncertainty
