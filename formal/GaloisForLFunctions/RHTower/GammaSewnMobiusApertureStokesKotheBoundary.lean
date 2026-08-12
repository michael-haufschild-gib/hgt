import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesInverseTilt
import GaloisForLFunctions.RHTower.DeningerPrimeLogHeightGreen

/-!
# Gamma-sewn Stokes inverse on the prime-log height Köthe boundary

The Gamma-sewn Stokes inverse is unbounded on the ambient prime Hilbert carrier at critical
aperture.  That chamber wall is not a wall in the source-derived nuclear topology.  Uniformly on
the closed Euler chamber `s ≥ 1`, the inverse costs at most one prime-log height step.  Its signed
extension to the full Kummer lattice therefore acts continuously on the existing Deninger height
Köthe source.

This separates the genuine obstruction from an artefact of ambient Hilbert topology.  No Xi zero,
target response, positivity premise, or RH-equivalent hypothesis occurs here.
-/

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions

/-- Uniform prime-log bound on the entire closed Euler chamber. -/
theorem gammaSewnMobiusApertureStokesInverseTilt_le_eight_log
    {s : ℝ} (hs : 1 ≤ s) (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesInverseTilt s p ≤
      8 * Real.log (p : ℝ) := by
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
  have hrq : r ≤ q := by
    simp only [r, q, xiMobiusContinuousApertureDiskNode]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hrle : r ≤ 1 / 2 := hrq.trans hqle
  have hfactor : (1 + q) / (c * (1 - r)) ≤ 8 := by
    rw [div_le_iff₀ (mul_pos hc0 (sub_pos.mpr hr1))]
    nlinarith
  have hratio : r / q ≤ 1 := (div_le_one hq0).2 hrq
  have hrewrite :
      L * r / (c * (q / (1 + q)) * (1 - r)) =
        (L * (r / q)) * ((1 + q) / (c * (1 - r))) := by
    field_simp [hq0.ne', hc0.ne', sub_ne_zero.mpr hr1.ne']
  rw [gammaSewnMobiusApertureStokesInverseTilt, hnode]
  change L * r / (c * (q / (1 + q)) * (1 - r)) ≤ 8 * L
  rw [hrewrite]
  calc
    (L * (r / q)) * ((1 + q) / (c * (1 - r)))
        ≤ (L * (r / q)) * 8 :=
          mul_le_mul_of_nonneg_left hfactor
            (mul_nonneg hL.le (div_nonneg hr0.le hq0.le))
    _ ≤ L * 8 := mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right hL.le hratio) (by norm_num)
    _ = 8 * L := by ring

/-- Signed extension of the source inverse tilt from prime coordinates to the Kummer lattice. -/
def gammaSewnMobiusApertureStokesKotheFrequency
    (s : ℝ) (m : DeningerPrimeLattice) : ℝ :=
  m.sum fun p z => (z : ℝ) * gammaSewnMobiusApertureStokesInverseTilt s p

@[simp] theorem gammaSewnMobiusApertureStokesKotheFrequency_zero (s : ℝ) :
    gammaSewnMobiusApertureStokesKotheFrequency s 0 = 0 := by
  simp [gammaSewnMobiusApertureStokesKotheFrequency]

/-- The full-lattice Stokes frequency has one-step prime-log height growth, uniformly for
`s ≥ 1`. -/
theorem abs_gammaSewnMobiusApertureStokesKotheFrequency_le_log_height
    {s : ℝ} (hs : 1 ≤ s) (m : DeningerPrimeLattice) :
    |gammaSewnMobiusApertureStokesKotheFrequency s m| ≤
      8 * Real.log (deningerHeight m) := by
  have hlog : Real.log (deningerHeight m) =
      m.sum fun p z => |(z : ℝ)| * Real.log (p : ℕ) := by
    rw [deningerHeight, deningerHeightNat, log_primeProduct]
    unfold deningerAbsExponent
    rw [Finsupp.sum_mapRange_index (by simp)]
    refine Finsupp.sum_congr ?_
    intro p _
    congr 1
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [gammaSewnMobiusApertureStokesKotheFrequency, Finsupp.sum]
  calc
    |∑ p ∈ m.support,
        (m p : ℝ) * gammaSewnMobiusApertureStokesInverseTilt s p|
        ≤ ∑ p ∈ m.support,
          |(m p : ℝ) * gammaSewnMobiusApertureStokesInverseTilt s p| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ m.support, 8 * (|(m p : ℝ)| * Real.log (p : ℕ)) := by
      refine Finset.sum_le_sum fun p hp => ?_
      rw [abs_mul, abs_of_pos
        (gammaSewnMobiusApertureStokesInverseTilt_pos (by linarith) p)]
      nlinarith [gammaSewnMobiusApertureStokesInverseTilt_le_eight_log hs p,
        abs_nonneg (m p : ℝ)]
    _ = 8 * Real.log (deningerHeight m) := by
      rw [hlog, Finsupp.sum]
      rw [Finset.mul_sum]

/-- Height form of the uniform one-step growth estimate. -/
theorem abs_gammaSewnMobiusApertureStokesKotheFrequency_le_height
    {s : ℝ} (hs : 1 ≤ s) (m : DeningerPrimeLattice) :
    |gammaSewnMobiusApertureStokesKotheFrequency s m| ≤
      8 * deningerHeight m :=
  le_trans
    (abs_gammaSewnMobiusApertureStokesKotheFrequency_le_log_height hs m)
    (mul_le_mul_of_nonneg_left (log_deningerHeight_le_height m) (by norm_num))

/-- The source inverse tilt is continuous at every positive aperture. -/
theorem continuousAt_gammaSewnMobiusApertureStokesInverseTilt
    {s : ℝ} (hs : 0 < s) (p : Nat.Primes) :
    ContinuousAt (fun t => gammaSewnMobiusApertureStokesInverseTilt t p) s := by
  have hnode : ContinuousAt
      (fun t => xiMobiusContinuousApertureDiskNode t p) s := by
    unfold xiMobiusContinuousApertureDiskNode
    fun_prop
  have hchar : ContinuousAt (fun t =>
      semilocalArchimedeanCharacteristic (2 * t * Real.log (p : ℝ))) s := by
    unfold semilocalArchimedeanCharacteristic
    exact (by fun_prop : ContinuousAt
      (fun t => Real.cosh (2 * t * Real.log (p : ℝ))) s).rpow_const
        (Or.inl (Real.cosh_pos (2 * s * Real.log (p : ℝ))).ne')
  have hgamma : ContinuousAt
      (fun t => gammaSewnMobiusValuationContractionMultiplier t p) s := by
    unfold gammaSewnMobiusValuationContractionMultiplier
      xiMobiusPrimeSchurApertureValuationRecovery
    exact (continuousAt_const.mul
      (Real.continuous_sqrt.continuousAt.comp hchar)).mul
        ((continuousAt_const.add hnode).div
          (Real.continuous_sqrt.continuousAt.comp hnode)
          (Real.sqrt_pos.2
            (xiMobiusContinuousApertureDiskNode_pos s p)).ne')
  have hc : gammaSewnMobiusValuationContractionMultiplier s p ≠ 0 :=
    (gammaSewnMobiusValuationContractionMultiplier_pos s p).ne'
  have hq : xiTransversePrimeApertureDiskNode 1 p ≠ 0 :=
    (xiTransversePrimeApertureDiskNode_pos 1 p).ne'
  have hqden : 1 + xiTransversePrimeApertureDiskNode 1 p ≠ 0 := by
    exact ne_of_gt (by linarith [xiTransversePrimeApertureDiskNode_pos 1 p])
  have hr : 1 - xiMobiusContinuousApertureDiskNode s p ≠ 0 :=
    sub_ne_zero.mpr (xiMobiusContinuousApertureDiskNode_lt_one hs p).ne'
  unfold gammaSewnMobiusApertureStokesInverseTilt
  apply ContinuousAt.div
  · exact continuousAt_const.mul hnode
  · exact (hgamma.mul continuousAt_const).mul (continuousAt_const.sub hnode)
  · exact mul_ne_zero (mul_ne_zero hc (div_ne_zero hq hqden)) hr

/-- Every Kummer-lattice Stokes frequency is continuous at positive aperture. -/
theorem continuousAt_gammaSewnMobiusApertureStokesKotheFrequency
    {s : ℝ} (hs : 0 < s) (m : DeningerPrimeLattice) :
    ContinuousAt
      (fun t => gammaSewnMobiusApertureStokesKotheFrequency t m) s := by
  change ContinuousAt (fun t => ∑ p ∈ m.support,
    (m p : ℝ) * gammaSewnMobiusApertureStokesInverseTilt t p) s
  induction m.support using Finset.induction_on with
  | empty => exact continuousAt_const
  | @insert p u hp ih =>
      have heq :
          (fun t => ∑ q ∈ insert p u,
            (m q : ℝ) * gammaSewnMobiusApertureStokesInverseTilt t q) =
          (fun t => (m p : ℝ) * gammaSewnMobiusApertureStokesInverseTilt t p +
            ∑ q ∈ u, (m q : ℝ) *
              gammaSewnMobiusApertureStokesInverseTilt t q) := by
        funext t
        rw [Finset.sum_insert hp]
      rw [heq]
      exact (continuousAt_const.mul
        (continuousAt_gammaSewnMobiusApertureStokesInverseTilt hs p)).add ih

/-- The `k`-th height-Köthe seminorm of the coefficientwise difference between aperture `s`
and the critical Stokes connection. -/
def gammaSewnMobiusApertureStokesKotheBoundarySeminorm
    (s : ℝ) (k : ℕ) (a : DeningerHeightKothe) : ℝ :=
  ∑' m : DeningerPrimeLattice,
    deningerHeight m ^ k *
      ‖((gammaSewnMobiusApertureStokesKotheFrequency s m -
          gammaSewnMobiusApertureStokesKotheFrequency 1 m : ℝ) : ℂ) *
        (a : DeningerPrimeLattice → ℂ) m‖

/-- **Projective crossing of the Hilbert chamber wall.**  Although the prime diagonal changes
from cofinite-zero to cofinite-infinite, its action on every vector of the nuclear height-Köthe
source converges in every defining seminorm as `s → 1` from the Euler chamber. -/
theorem tendsto_gammaSewnMobiusApertureStokesKotheBoundarySeminorm
    (k : ℕ) (a : DeningerHeightKothe) :
    Tendsto
      (fun s : ℝ => gammaSewnMobiusApertureStokesKotheBoundarySeminorm s k a)
      (nhdsWithin (1 : ℝ) (Set.Ici 1)) (𝓝 0) := by
  let bound : DeningerPrimeLattice → ℝ := fun m =>
    16 * (deningerHeight m ^ (k + 1) *
      ‖(a : DeningerPrimeLattice → ℂ) m‖)
  have hbound_summable : Summable bound := by
    exact (deningerHeightSeminorm_summable a (k + 1)).mul_left 16
  have hlim (m : DeningerPrimeLattice) : Tendsto
      (fun s : ℝ => deningerHeight m ^ k *
        ‖((gammaSewnMobiusApertureStokesKotheFrequency s m -
            gammaSewnMobiusApertureStokesKotheFrequency 1 m : ℝ) : ℂ) *
          (a : DeningerPrimeLattice → ℂ) m‖)
      (nhdsWithin (1 : ℝ) (Set.Ici 1)) (𝓝 0) := by
    have hf := continuousAt_gammaSewnMobiusApertureStokesKotheFrequency
      (s := 1) (by norm_num) m
    have hterm : ContinuousAt
        (fun s : ℝ => deningerHeight m ^ k *
          ‖((gammaSewnMobiusApertureStokesKotheFrequency s m -
              gammaSewnMobiusApertureStokesKotheFrequency 1 m : ℝ) : ℂ) *
            (a : DeningerPrimeLattice → ℂ) m‖) 1 := by
      exact continuousAt_const.mul
        (((Complex.continuous_ofReal.continuousAt.comp
          (hf.sub continuousAt_const)).mul continuousAt_const).norm)
    have hwithin : ContinuousWithinAt
        (fun s : ℝ => deningerHeight m ^ k *
          ‖((gammaSewnMobiusApertureStokesKotheFrequency s m -
              gammaSewnMobiusApertureStokesKotheFrequency 1 m : ℝ) : ℂ) *
            (a : DeningerPrimeLattice → ℂ) m‖) (Set.Ici 1) 1 :=
      hterm.continuousWithinAt
    simpa [ContinuousWithinAt] using hwithin
  have hdom : ∀ᶠ s : ℝ in nhdsWithin (1 : ℝ) (Set.Ici 1),
      ∀ m : DeningerPrimeLattice,
        ‖deningerHeight m ^ k *
          ‖((gammaSewnMobiusApertureStokesKotheFrequency s m -
              gammaSewnMobiusApertureStokesKotheFrequency 1 m : ℝ) : ℂ) *
            (a : DeningerPrimeLattice → ℂ) m‖‖ ≤ bound m := by
    filter_upwards [self_mem_nhdsWithin] with s hs m
    have hs1 : 1 ≤ s := hs
    have hfreqs :=
      abs_gammaSewnMobiusApertureStokesKotheFrequency_le_height hs1 m
    have hfreq1 :=
      abs_gammaSewnMobiusApertureStokesKotheFrequency_le_height
        (s := 1) (by norm_num) m
    have hdiff :
        |gammaSewnMobiusApertureStokesKotheFrequency s m -
          gammaSewnMobiusApertureStokesKotheFrequency 1 m| ≤
            16 * deningerHeight m := by
      calc
        |gammaSewnMobiusApertureStokesKotheFrequency s m -
            gammaSewnMobiusApertureStokesKotheFrequency 1 m|
            ≤ |gammaSewnMobiusApertureStokesKotheFrequency s m| +
              |gammaSewnMobiusApertureStokesKotheFrequency 1 m| := abs_sub _ _
        _ ≤ 8 * deningerHeight m + 8 * deningerHeight m := add_le_add hfreqs hfreq1
        _ = 16 * deningerHeight m := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (pow_nonneg (deningerHeight_pos m).le _) (norm_nonneg _))]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      deningerHeight m ^ k *
          (|gammaSewnMobiusApertureStokesKotheFrequency s m -
              gammaSewnMobiusApertureStokesKotheFrequency 1 m| *
            ‖(a : DeningerPrimeLattice → ℂ) m‖)
          ≤ deningerHeight m ^ k *
            ((16 * deningerHeight m) *
              ‖(a : DeningerPrimeLattice → ℂ) m‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdiff (norm_nonneg _))
          (pow_nonneg (deningerHeight_pos m).le _)
      _ = bound m := by
        simp only [bound, pow_succ]
        ring
  have hmain := tendsto_tsum_of_dominated_convergence hbound_summable hlim hdom
  simpa [gammaSewnMobiusApertureStokesKotheBoundarySeminorm] using hmain

/-- The Stokes connection normalized by its uniform constant is a one-step height multiplier. -/
def gammaSewnMobiusApertureStokesKotheNormalizedMultiplier
    (s : ℝ) (m : DeningerPrimeLattice) : ℂ :=
  ((gammaSewnMobiusApertureStokesKotheFrequency s m / 8 : ℝ) : ℂ)

theorem norm_gammaSewnMobiusApertureStokesKotheNormalizedMultiplier_le
    {s : ℝ} (hs : 1 ≤ s) (m : DeningerPrimeLattice) :
    ‖gammaSewnMobiusApertureStokesKotheNormalizedMultiplier s m‖ ≤
      deningerHeight m ^ 1 := by
  have h := abs_gammaSewnMobiusApertureStokesKotheFrequency_le_height hs m
  rw [gammaSewnMobiusApertureStokesKotheNormalizedMultiplier,
    Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8),
    pow_one]
  nlinarith [deningerHeight_pos m]

/-- Actual Gamma-sewn Stokes connection on the nuclear prime-log height source.  The factor eight
undoes normalization used to reuse the established one-step multiplier calculus. -/
def gammaSewnMobiusApertureStokesKotheOperator
    (s : ℝ) (hs : 1 ≤ s) :
    DeningerHeightKothe →ₗ[ℂ] DeningerHeightKothe :=
  (8 : ℂ) • deningerHeightMul
    (gammaSewnMobiusApertureStokesKotheNormalizedMultiplier s) 1
    (norm_gammaSewnMobiusApertureStokesKotheNormalizedMultiplier_le hs)

/-- The packaged source operator acts by the unnormalized signed Stokes frequency. -/
theorem gammaSewnMobiusApertureStokesKotheOperator_coe
    {s : ℝ} (hs : 1 ≤ s) (a : DeningerHeightKothe)
    (m : DeningerPrimeLattice) :
    ((gammaSewnMobiusApertureStokesKotheOperator s hs a : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ) m =
      (gammaSewnMobiusApertureStokesKotheFrequency s m : ℂ) *
        (a : DeningerPrimeLattice → ℂ) m := by
  rw [gammaSewnMobiusApertureStokesKotheOperator]
  change (8 : ℂ) *
      (gammaSewnMobiusApertureStokesKotheNormalizedMultiplier s m *
        (a : DeningerPrimeLattice → ℂ) m) = _
  rw [gammaSewnMobiusApertureStokesKotheNormalizedMultiplier]
  push_cast
  ring

/-- The actual Stokes connection costs exactly one defining seminorm step, up to its uniform
constant eight. -/
theorem deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheOperator_le
    {s : ℝ} (hs : 1 ≤ s) (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k
      (gammaSewnMobiusApertureStokesKotheOperator s hs a) ≤
        8 * deningerHeightSeminorm (k + 1) a := by
  rw [gammaSewnMobiusApertureStokesKotheOperator]
  change deningerHeightSeminorm k
      ((8 : ℂ) • deningerHeightMul
        (gammaSewnMobiusApertureStokesKotheNormalizedMultiplier s) 1
        (norm_gammaSewnMobiusApertureStokesKotheNormalizedMultiplier_le hs) a) ≤ _
  rw [map_smul_eq_mul]
  norm_num
  have h := deningerHeightSeminorm_mul_le
    (norm_gammaSewnMobiusApertureStokesKotheNormalizedMultiplier_le hs) k a
  nlinarith

/-- On the closed Euler chamber, the dominated-convergence expression is literally the defining
Köthe seminorm distance between the packaged source operators. -/
theorem deningerHeightSeminorm_gammaSewnMobiusApertureStokesKotheOperator_sub_one
    {s : ℝ} (hs : 1 ≤ s) (k : ℕ) (a : DeningerHeightKothe) :
    deningerHeightSeminorm k
      (gammaSewnMobiusApertureStokesKotheOperator s hs a -
        gammaSewnMobiusApertureStokesKotheOperator 1 (by norm_num) a) =
      gammaSewnMobiusApertureStokesKotheBoundarySeminorm s k a := by
  rw [deningerHeightSeminorm_apply,
    gammaSewnMobiusApertureStokesKotheBoundarySeminorm]
  refine tsum_congr fun m => ?_
  congr 1
  rw [Submodule.coe_sub, Pi.sub_apply,
    gammaSewnMobiusApertureStokesKotheOperator_coe hs,
    gammaSewnMobiusApertureStokesKotheOperator_coe (by norm_num : (1 : ℝ) ≤ 1)]
  congr 1
  push_cast
  ring

end RHTower
