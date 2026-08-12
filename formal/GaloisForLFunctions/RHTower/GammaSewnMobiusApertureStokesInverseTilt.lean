import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction
import GaloisForLFunctions.RHTower.SquarefreeCoronaCodiagonal
import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet

/-!
# Gamma-sewn Möbius aperture Stokes inverse tilt

The actual Gamma-sewn Möbius aperture feature vanishes at zero aperture, so its difference from
the lossless boundary is a literal pre-Gram Stokes edge.  On every positive real aperture there is
a source-defined inverse tilt: divide by the sewn multiplier, the fixed-critical Möbius damping,
and the aperture increment, then insert the prime-log clock and one moving disk node.

The resulting coefficient is exactly

`log p * p^(-s(e+1))`,

not merely asymptotic to it.  Hence on `s>1` the complete prime--valuation current is the
von Mangoldt Euler flux `-ζ'/ζ`.  This passes the first coefficientwise falsifier in the
Gamma-sewn Rees--Stokes route.

The inverse is not regular at the Euler wall.  For every fixed `s>1` it decays to zero along the
cofinite prime filter, with an explicit `O(log p * p^(1-s))` majorant.  At `s=1` it instead
dominates `log p` and tends to infinity.  Thus the safe Euler producer cannot be specialized to
the critical boundary as a bounded prime-diagonal operator.  Any continuation must use the
projective/corona boundary topology and the fixed Gamma correction; pointwise inversion at the
wall is ruled out.

No Xi zero, target response, positivity premise, or RH-equivalent hypothesis occurs here.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Source-defined inverse tilt of the Gamma-sewn aperture Stokes edge. -/
def gammaSewnMobiusApertureStokesInverseTilt
    (s : ℝ) (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) * xiMobiusContinuousApertureDiskNode s p /
    (gammaSewnMobiusValuationContractionMultiplier s p *
      (xiTransversePrimeApertureDiskNode 1 p /
        (1 + xiTransversePrimeApertureDiskNode 1 p)) *
      (1 - xiMobiusContinuousApertureDiskNode s p))

/-- The sewn feature vanishes at the lossless zero-aperture boundary. -/
@[simp] theorem gammaSewnMobiusContinuousApertureFeature_zero
    (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusContinuousApertureFeature 0 p e = 0 := by
  rw [gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  simp [xiMobiusContinuousApertureDiskNode]

/-- **Exact pre-Gram Stokes inversion.**  Source inversion of one sewn aperture edge produces
one real von Mangoldt prime-power coefficient. -/
theorem gammaSewnMobiusApertureStokesInverseTilt_mul_edge
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) (e : ℕ) :
    gammaSewnMobiusApertureStokesInverseTilt s p *
        (gammaSewnMobiusContinuousApertureFeature s p e -
          gammaSewnMobiusContinuousApertureFeature 0 p e) =
      Real.log (p : ℝ) *
        xiMobiusContinuousApertureDiskNode s p ^ (e + 1) := by
  have hc : gammaSewnMobiusValuationContractionMultiplier s p ≠ 0 :=
    (gammaSewnMobiusValuationContractionMultiplier_pos s p).ne'
  have hq : xiTransversePrimeApertureDiskNode 1 p ≠ 0 :=
    (xiTransversePrimeApertureDiskNode_pos 1 p).ne'
  have hqden : 1 + xiTransversePrimeApertureDiskNode 1 p ≠ 0 := by
    exact ne_of_gt (by
      linarith [xiTransversePrimeApertureDiskNode_pos 1 p])
  have hr : 1 - xiMobiusContinuousApertureDiskNode s p ≠ 0 :=
    sub_ne_zero.mpr (xiMobiusContinuousApertureDiskNode_lt_one hs p).ne'
  rw [gammaSewnMobiusContinuousApertureFeature_zero, sub_zero,
    gammaSewnMobiusContinuousApertureFeature,
    xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric,
    gammaSewnMobiusApertureStokesInverseTilt]
  field_simp [hc, hq, hqden, hr]
  ring

/-- The real aperture disk node is the real-axis value of the complex prime power. -/
theorem ofReal_xiMobiusContinuousApertureDiskNode
    (s : ℝ) (p : Nat.Primes) :
    (xiMobiusContinuousApertureDiskNode s p : ℂ) =
      ((p : ℕ) : ℂ) ^ (-(s : ℂ)) := by
  have hp0 : 0 ≤ (((p : ℕ) : ℝ)) := by positivity
  have hp : 0 < (((p : ℕ) : ℝ)) := by exact_mod_cast p.2.pos
  have hnode : xiMobiusContinuousApertureDiskNode s p =
      (((p : ℕ) : ℝ) ^ (-s)) := by
    rw [xiMobiusContinuousApertureDiskNode, Real.rpow_def_of_pos hp]
    congr 1
    ring
  rw [hnode, Complex.ofReal_cpow hp0]
  norm_cast

/-- Complex prime--valuation current obtained from the real source Stokes edge. -/
def gammaSewnMobiusApertureStokesFluxTerm
    (s : ℝ) (pk : Nat.Primes × ℕ) : ℂ :=
  (gammaSewnMobiusApertureStokesInverseTilt s pk.1 *
      (gammaSewnMobiusContinuousApertureFeature s pk.1 pk.2 -
        gammaSewnMobiusContinuousApertureFeature 0 pk.1 pk.2) : ℝ)

/-- The inverse tilt is strictly positive on every open positive aperture. -/
theorem gammaSewnMobiusApertureStokesInverseTilt_pos
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) :
    0 < gammaSewnMobiusApertureStokesInverseTilt s p := by
  rw [gammaSewnMobiusApertureStokesInverseTilt]
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hc := gammaSewnMobiusValuationContractionMultiplier_pos s p
  have hqt := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr := xiMobiusContinuousApertureDiskNode_pos s p
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one hs p
  exact div_pos (mul_pos (Real.log_pos hp) hr)
    (mul_pos
      (mul_pos hc (div_pos hqt (by linarith)))
      (sub_pos.mpr hr1))

/-- At critical aperture the inverse tilt already dominates the unbounded prime-log generator. -/
theorem real_log_lt_gammaSewnMobiusApertureStokesInverseTilt_one
    (p : Nat.Primes) :
    Real.log (p : ℝ) <
      gammaSewnMobiusApertureStokesInverseTilt 1 p := by
  let q := xiMobiusContinuousApertureDiskNode 1 p
  let c := gammaSewnMobiusValuationContractionMultiplier 1 p
  have hnode : xiTransversePrimeApertureDiskNode 1 p = q := by
    simp only [q, xiMobiusContinuousApertureDiskNode,
      xiTransversePrimeApertureDiskNode]
    congr 1
    ring
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiMobiusContinuousApertureDiskNode_lt_one (by norm_num) p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos 1 p
  have hc1 : c < 1 :=
    gammaSewnMobiusValuationContractionMultiplier_lt_one (by norm_num) p
  have hlog : 0 < Real.log (p : ℝ) := by
    apply Real.log_pos
    exact_mod_cast p.2.one_lt
  have ha0 : 0 < q / (1 + q) * (1 - q) := by positivity
  have ha_lt : q / (1 + q) * (1 - q) < q := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith : 0 < 1 + q)]
    nlinarith
  have hca_lt : c * (q / (1 + q) * (1 - q)) < q :=
    lt_trans (mul_lt_of_lt_one_left ha0 hc1) ha_lt
  have hden : 0 < c * (q / (1 + q)) * (1 - q) := by positivity
  rw [gammaSewnMobiusApertureStokesInverseTilt, hnode]
  change Real.log (p : ℝ) < Real.log (p : ℝ) * q /
    (c * (q / (1 + q)) * (1 - q))
  rw [lt_div_iff₀ hden]
  exact (mul_lt_mul_of_pos_left (by simpa [mul_assoc] using hca_lt) hlog)

/-- **Critical chamber wall.**  The inverse tilt escapes every bound on every cofinite prime
tail at `s=1`. -/
theorem tendsto_gammaSewnMobiusApertureStokesInverseTilt_one_cofinite_atTop :
    Tendsto (gammaSewnMobiusApertureStokesInverseTilt 1)
      cofinite atTop := by
  refine tendsto_atTop_mono' cofinite
    (Eventually.of_forall fun p =>
      (real_log_lt_gammaSewnMobiusApertureStokesInverseTilt_one p).le)
    GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop

/-- In the open Euler chamber the inverse tilt is bounded by an exponentially decaying
prime-log profile. -/
theorem gammaSewnMobiusApertureStokesInverseTilt_le_safe_majorant
    {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesInverseTilt s p ≤
      8 * Real.log (p : ℝ) * Real.exp (-(s - 1) * Real.log (p : ℝ)) := by
  let q := xiMobiusContinuousApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode s p
  let c := gammaSewnMobiusValuationContractionMultiplier s p
  let L := Real.log (p : ℝ)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp
  have hq0 : 0 < q := xiMobiusContinuousApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos s p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one (by linarith) p
  have hc0 : 0 < c := gammaSewnMobiusValuationContractionMultiplier_pos s p
  have hc : 1 / 2 < c :=
    one_half_lt_gammaSewnMobiusValuationContractionMultiplier s p
  have hnode : xiTransversePrimeApertureDiskNode 1 p = q := by
    simp only [q, xiMobiusContinuousApertureDiskNode,
      xiTransversePrimeApertureDiskNode]
    congr 1
    ring
  have hqle : q ≤ 1 / 2 := by
    rw [← hnode, xiTransversePrimeApertureDiskNode_one_eq_inv]
    rw [inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
    exact_mod_cast p.2.two_le
  have hrq : r < q := by
    simp only [r, q, xiMobiusContinuousApertureDiskNode]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hrle : r ≤ 1 / 2 := hrq.le.trans hqle
  have hfactor : (1 + q) / (c * (1 - r)) ≤ 8 := by
    rw [div_le_iff₀ (mul_pos hc0 (sub_pos.mpr hr1))]
    nlinarith
  have hratio : r / q = Real.exp (-(s - 1) * L) := by
    simp only [r, q, L, xiMobiusContinuousApertureDiskNode]
    rw [← Real.exp_sub]
    congr 1
    ring
  have hrewrite :
      L * r / (c * (q / (1 + q)) * (1 - r)) =
        (L * (r / q)) * ((1 + q) / (c * (1 - r))) := by
    field_simp [hq0.ne', hc0.ne', sub_ne_zero.mpr hr1.ne']
  rw [gammaSewnMobiusApertureStokesInverseTilt, hnode]
  change L * r / (c * (q / (1 + q)) * (1 - r)) ≤
    8 * L * Real.exp (-(s - 1) * L)
  rw [hrewrite, ← hratio]
  nlinarith [mul_le_mul_of_nonneg_left hfactor
    (mul_nonneg hL.le (div_nonneg hr0.le hq0.le))]

/-- **Sharp open/closed chamber transition.**  At each fixed `s>1` the inverse tilt vanishes
along the cofinite prime filter, opposite to its critical divergence. -/
theorem tendsto_gammaSewnMobiusApertureStokesInverseTilt_cofinite_zero
    {s : ℝ} (hs : 1 < s) :
    Tendsto (gammaSewnMobiusApertureStokesInverseTilt s)
      cofinite (𝓝 0) := by
  have hdecay : Tendsto (fun p : Nat.Primes =>
      8 * (Real.log (p : ℝ) *
        Real.exp (-(s - 1) * Real.log (p : ℝ)))) cofinite (𝓝 0) := by
    have hδ : 0 < s - 1 := by linarith
    have hmul : Tendsto (fun t : ℝ => (s - 1) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hδ tendsto_id
    have hcomp : Tendsto (fun t : ℝ =>
        ((s - 1) * t) ^ 1 * Real.exp (-((s - 1) * t))) atTop (𝓝 0) := by
      simpa only [Function.comp_def] using
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hmul
    have hscaled := hcomp.const_mul (s - 1)⁻¹
    have hcore : Tendsto (fun t : ℝ =>
        t * Real.exp (-(s - 1) * t)) atTop (𝓝 0) := by
      convert hscaled using 1
      funext t
      simp only [pow_one]
      field_simp [hδ.ne']
      ring
    have hprime := hcore.comp
      GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop
    simpa only [Function.comp_apply, mul_zero, mul_assoc] using hprime.const_mul 8
  exact squeeze_zero
    (fun p => (gammaSewnMobiusApertureStokesInverseTilt_pos (by linarith) p).le)
    (fun p => gammaSewnMobiusApertureStokesInverseTilt_le_safe_majorant hs p)
    (by simpa [mul_assoc] using hdecay)

/-- The inverted source edge is coefficientwise the existing complex von Mangoldt flux family. -/
theorem gammaSewnMobiusApertureStokesFluxTerm_eq
    {s : ℝ} (hs : 0 < s) (pk : Nat.Primes × ℕ) :
    gammaSewnMobiusApertureStokesFluxTerm s pk =
      primePowerFluxTerm (s : ℂ) pk := by
  rw [gammaSewnMobiusApertureStokesFluxTerm,
    gammaSewnMobiusApertureStokesInverseTilt_mul_edge hs,
    primePowerFluxTerm]
  push_cast
  rw [ofReal_xiMobiusContinuousApertureDiskNode]

/-- The complete source Stokes current is summable throughout the open Euler chamber. -/
theorem summable_gammaSewnMobiusApertureStokesFluxTerm
    {s : ℝ} (hs : 1 < s) :
    Summable (gammaSewnMobiusApertureStokesFluxTerm s) := by
  apply (summable_primePowerFluxTerm (s := (s : ℂ)) (by simpa)).congr
  exact fun pk => (gammaSewnMobiusApertureStokesFluxTerm_eq (by linarith) pk).symm

/-- **Euler landing.**  The complete inverted Stokes current is exactly `-ζ'/ζ` on `s>1`. -/
theorem tsum_gammaSewnMobiusApertureStokesFluxTerm
    {s : ℝ} (hs : 1 < s) :
    ∑' pk : Nat.Primes × ℕ, gammaSewnMobiusApertureStokesFluxTerm s pk =
      infinitePrimeFlux (s : ℂ) := by
  rw [tsum_congr (gammaSewnMobiusApertureStokesFluxTerm_eq (by linarith))]
  exact tsum_primePowerFluxTerm (by simpa)

end RHTower
