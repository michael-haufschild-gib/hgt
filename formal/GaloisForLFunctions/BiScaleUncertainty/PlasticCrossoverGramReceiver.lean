import GaloisForLFunctions.BiScaleUncertainty.HyperbolicJumpEnergyTransfer
import GaloisForLFunctions.RHTower.WeilLevyCoshPlasticCrossover

/-!
# The signed plastic crossover as a multiplier-Gram receiver

The actual piecewise plastic kernel splits into half the secant kernel and a
positive remainder. Its original signed pair functional therefore equals secant
energy plus a nonnegative remainder and the exact hyperbolic moment form.
This transfers the full source-support-weighted sine Gram bound into the actual
plastic crossover. Canonical odd sources retain their negative sine moment.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm
open _root_.RHTower.WeilLevyCoshCrossover _root_.RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.RHTower
noncomputable section

/-- The exact hyperbolic moment form of a compact source. -/
def hyperbolicMomentEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  2 * ((∫ u, f u * Real.cosh (u / 2)) ^ 2 - (∫ u, f u * Real.sinh (u / 2)) ^ 2)

/-- The actual signed plastic crossover, with its origin potential retained.
Any separately imposed gamma-origin term is not part of this definition. -/
def plasticCrossover (f : C_c(ℝ, ℝ)) : ℝ :=
  levyCoshPotential screwSignThreshold * autocorr f 0 +
    ∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|)

def plasticJumpEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  ∫ x in Ioi 0, (autocorr f 0 - autocorr f x) * levyCoshKernel screwSignThreshold x

/-- The excess over the secant kernel in twice the actual plastic kernel. -/
def plasticRemainderWeight (x : ℝ) : ℝ :=
  2 * levyCoshKernel screwSignThreshold x - archSechHalfWeight x

def plasticRemainderEnergy (f : C_c(ℝ, ℝ)) : ℝ :=
  ∫ x in Ioi 0, (autocorr f 0 - autocorr f x) * plasticRemainderWeight x

/-- The remainder is an elementary core followed by the dual Lévy tail. -/
theorem plasticRemainderWeight_eq (x : ℝ) :
    plasticRemainderWeight x = if x ≤ screwSignThreshold then
      4 * Real.cosh (x / 2) - archSechHalfWeight x else archDualLevySinhWeight x := by
  unfold plasticRemainderWeight levyCoshKernel
  by_cases hx : x ≤ screwSignThreshold
  · simp only [if_pos hx]
    ring
  · simp only [if_neg hx]
    have hx0 : 0 < x := lt_trans screwSignThreshold_pos (not_le.mp hx)
    have he := exp_half_div_sinh_eq hx0
    change archLevySinhWeight x = 2 * _root_.RHTower.archLevyDensity x at he
    have hs := archLevySinhWeight_eq_sech_add_dual hx0.ne'
    linarith

/-- Positivity holds on the whole real line; the tail branch starts beyond a
strictly positive source-independent threshold. -/
theorem plasticRemainderWeight_pos (x : ℝ) : 0 < plasticRemainderWeight x := by
  rw [plasticRemainderWeight_eq]
  split_ifs with hx
  · have hw : archSechHalfWeight x ≤ 1 := by
      unfold archSechHalfWeight
      apply (div_le_iff₀ (Real.cosh_pos _)).mpr
      simpa only [one_mul] using Real.one_le_cosh (x / 2)
    linarith [Real.one_le_cosh (x / 2)]
  · exact archDualLevySinhWeight_pos (lt_trans screwSignThreshold_pos (not_le.mp hx))

/-- Compact continuity alone admits the actual plastic jump energy. -/
theorem integrableOn_plasticJumpIntegrand (f : C_c(ℝ, ℝ)) :
    IntegrableOn (fun x => (autocorr f 0 - autocorr f x) *
      levyCoshKernel screwSignThreshold x) (Ioi 0) := by
  have hR := autocorr_zero_nonneg (f : ℝ → ℝ)
  have hg : IntegrableOn (fun x => (2 * autocorr f 0) *
      levyCoshKernel screwSignThreshold x) (Ioi 0) :=
    (integrableOn_levyCoshKernel_Ioi screwSignThreshold_pos).const_mul _
  refine hg.mono' (((continuous_const.sub (continuous_autocorr_compact f)).measurable.mul
    (measurable_levyCoshKernel screwSignThreshold)).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hΔ := autocorr_sub_nonneg f.hasCompactSupport f.continuous x
  have hk := (levyCoshKernel_pos (c := screwSignThreshold) hx).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hΔ hk)]
  have hupper : autocorr f 0 - autocorr f x ≤ 2 * autocorr f 0 := by
    have ha := abs_autocorr_le_zero f.hasCompactSupport f.continuous x
    linarith [neg_abs_le (autocorr f x)]
  exact mul_le_mul_of_nonneg_right hupper hk

theorem integrableOn_plasticRemainderIntegrand (f : C_c(ℝ, ℝ)) :
    IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * plasticRemainderWeight x)
      (Ioi 0) := by
  have h := ((integrableOn_plasticJumpIntegrand f).const_mul 2).sub
    (integrableOn_secantJumpIntegrand_compact f)
  apply h.congr
  filter_upwards [] with x
  dsimp
  unfold plasticRemainderWeight
  ring

theorem plasticRemainderEnergy_nonneg (f : C_c(ℝ, ℝ)) :
    0 ≤ plasticRemainderEnergy f := by
  unfold plasticRemainderEnergy
  exact setIntegral_nonneg measurableSet_Ioi fun x _ =>
    mul_nonneg (autocorr_sub_nonneg f.hasCompactSupport f.continuous x)
      (plasticRemainderWeight_pos x).le

private theorem integrable_coshPair (f : C_c(ℝ, ℝ)) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) := by
  have hs : HasCompactSupport (fun p : ℝ × ℝ =>
      f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) := by
    refine HasCompactSupport.intro (f.hasCompactSupport.isCompact.prod
      f.hasCompactSupport.isCompact) fun p hp => ?_
    rcases not_and_or.mp (show ¬(p.1 ∈ tsupport (f : ℝ → ℝ) ∧
        p.2 ∈ tsupport (f : ℝ → ℝ)) from hp) with h1 | h2
    · rw [image_eq_zero_of_notMem_tsupport h1]
      ring
    · rw [image_eq_zero_of_notMem_tsupport h2]
      ring
  exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
    f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)).integrable_of_hasCompactSupport hs

/-- No signed pair integral is admitted without an integrability proof. -/
theorem integrable_plasticResidualPair (f : C_c(ℝ, ℝ)) :
    Integrable (fun p : ℝ × ℝ => f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|)) := by
  obtain ⟨B, C, hB⟩ := exists_bddSupp_of_hasCompactSupport
    (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have h := ((integrable_coshPair f).const_mul 2).sub
    (integrable_pair_levyCoshKernel hB screwSignThreshold_pos)
  apply h.congr
  filter_upwards [] with p
  dsimp
  ring

/-- Exact signed-pair reduction; the hyperbolic moment has its original sign. -/
theorem plasticCrossover_eq_jump_add_moment (f : C_c(ℝ, ℝ)) :
    plasticCrossover f = 2 * plasticJumpEnergy f + hyperbolicMomentEnergy f := by
  obtain ⟨B, C, hB⟩ := exists_bddSupp_of_hasCompactSupport
    (f := (f : ℝ → ℝ)) f.continuous f.hasCompactSupport
  have hj := integral_levyCoshKernel_mul_jump_sq hB screwSignThreshold_pos
  simp_rw [integral_sub_shift_sq (f := (f : ℝ → ℝ)) f.hasCompactSupport f.continuous] at hj
  have heq : (∫ x in Ioi (0 : ℝ), levyCoshKernel screwSignThreshold x *
      (2 * (autocorr f 0 - autocorr f x))) = 2 * plasticJumpEnergy f := by
    unfold plasticJumpEnergy
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    ring
  rw [heq, integral_sq_eq_autocorr_zero] at hj
  have hpair : (∫ p : ℝ × ℝ, f p.1 * f p.2 *
      (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|)) =
      2 * (∫ p : ℝ × ℝ, f p.1 * f p.2 * Real.cosh ((p.1 - p.2) / 2)) -
        ∫ p : ℝ × ℝ, f p.1 * f p.2 * levyCoshKernel screwSignThreshold |p.1 - p.2| := by
    rw [← integral_const_mul, ← integral_sub ((integrable_coshPair f).const_mul 2)
      (integrable_pair_levyCoshKernel hB screwSignThreshold_pos)]
    apply integral_congr_ae
    filter_upwards [] with p
    ring
  unfold plasticCrossover hyperbolicMomentEnergy
  rw [hpair, integral_prod_cosh_eq_sq (f := (f : ℝ → ℝ)) f.hasCompactSupport f.continuous]
  linarith

/-- Exact positive-remainder decomposition into the original secant energy and
the actual signed hyperbolic moment. -/
theorem plasticCrossover_eq_secant_add_remainder_add_moment (f : C_c(ℝ, ℝ)) :
    plasticCrossover f = biScaleSecantEnergy f + plasticRemainderEnergy f +
      hyperbolicMomentEnergy f := by
  have hs : biScaleSecantEnergy f + plasticRemainderEnergy f = 2 * plasticJumpEnergy f := by
    unfold biScaleSecantEnergy plasticRemainderEnergy plasticJumpEnergy
    rw [← integral_add (integrableOn_secantJumpIntegrand_compact f)
      (integrableOn_plasticRemainderIntegrand f), ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    unfold plasticRemainderWeight
    ring
  rw [plasticCrossover_eq_jump_add_moment, ← hs]

/-- The original plastic crossover receives every secant lower bound, with its
signed moment retained. -/
theorem plasticCrossover_ge_secant_add_moment (f : C_c(ℝ, ℝ)) :
    biScaleSecantEnergy f + hyperbolicMomentEnergy f ≤ plasticCrossover f := by
  rw [plasticCrossover_eq_secant_add_remainder_add_moment]
  linarith [plasticRemainderEnergy_nonneg f]

/-- The full positive plastic remainder can be retained alongside the multiplier
Gram bound; only the secant component is replaced by its finite-collar estimate. -/
theorem plasticCrossover_ge_sinhJumpGram_add_remainder (f : C_c(ℝ, ℝ)) (δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, sinhJumpGramBound f (Finset.range K) (fun _ => 1)
      (fun k => (k : ℝ) * |δ|) (-y)) + plasticRemainderEnergy f + hyperbolicMomentEnergy f ≤
      plasticCrossover f := by
  have h := biScaleSecantEnergy_ge_sinhJumpGram f δ K
  rw [plasticCrossover_eq_secant_add_remainder_add_moment]
  linarith

/-- Multi-node multiplier Gram information transferred into the actual signed
plastic crossover. All source-support and measured-Gram dependence is explicit. -/
theorem plasticCrossover_ge_sinhJumpGram (f : C_c(ℝ, ℝ)) (δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, sinhJumpGramBound f (Finset.range K) (fun _ => 1)
      (fun k => (k : ℝ) * |δ|) (-y)) + hyperbolicMomentEnergy f ≤ plasticCrossover f := by
  have h := biScaleSecantEnergy_ge_sinhJumpGram f δ K
  have hp := plasticCrossover_ge_secant_add_moment f
  linarith

/-- A genuine compact odd source constructed from arbitrary compact continuous data. -/
def oddCompactSource (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => (f u - f (-u)) / 2, (f.continuous.sub
    (f.continuous.comp continuous_neg)).div_const 2⟩, by
    have href : HasCompactSupport (fun u : ℝ => f (-u)) :=
      f.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)
    have hs : HasCompactSupport (fun u : ℝ => f u - f (-u)) := f.hasCompactSupport.sub href
    change HasCompactSupport (fun u : ℝ => (f u - f (-u)) * (2 : ℝ)⁻¹)
    exact hs.mul_right⟩

theorem oddCompactSource_odd (f : C_c(ℝ, ℝ)) (u : ℝ) :
    oddCompactSource f (-u) = -oddCompactSource f u := by
  change (f (-u) - f (-(-u))) / 2 = -((f u - f (-u)) / 2)
  rw [neg_neg]
  ring

theorem sinhCompact_oddSource_even (f : C_c(ℝ, ℝ)) (u : ℝ) :
    sinhCompact (1 / 2) (oddCompactSource f) (-u) =
      sinhCompact (1 / 2) (oddCompactSource f) u :=
  sinhMultiplier_even_of_odd (1 / 2) (oddCompactSource_odd f) u

theorem oddCompactSource_cosh_moment_zero (f : C_c(ℝ, ℝ)) :
    (∫ u, oddCompactSource f u * Real.cosh (u / 2)) = 0 := by
  have h := integral_neg_eq_self (fun u => oddCompactSource f u * Real.cosh (u / 2)) volume
  simp only [oddCompactSource_odd, neg_div, Real.cosh_neg, neg_mul, integral_neg] at h
  linarith

theorem hyperbolicMomentEnergy_oddSource (f : C_c(ℝ, ℝ)) :
    hyperbolicMomentEnergy (oddCompactSource f) =
      -2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 := by
  unfold hyperbolicMomentEnergy
  rw [oddCompactSource_cosh_moment_zero]
  ring

/-- Unconditional odd-source receiver: the multiplier is even, and the original
plastic functional retains its precise negative sine-moment term. -/
theorem plasticCrossover_oddSource_ge_sinhJumpGram (f : C_c(ℝ, ℝ)) (δ : ℝ) (K : ℕ) :
    (∫ y in (0 : ℝ)..|δ|, sinhJumpGramBound (oddCompactSource f) (Finset.range K) (fun _ => 1)
      (fun k => (k : ℝ) * |δ|) (-y)) -
        2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 ≤
      plasticCrossover (oddCompactSource f) := by
  have h := plasticCrossover_ge_sinhJumpGram (oddCompactSource f) δ K
  rw [hyperbolicMomentEnergy_oddSource] at h
  linarith

/-- The same bound in the original crossover expression, including an arbitrary
origin coefficient. In particular the existing gamma-origin constant is admissible. -/
theorem plasticCrossoverWithOrigin_ge_sinhJumpGram
    (f : C_c(ℝ, ℝ)) (a δ : ℝ) (K : ℕ) :
    a * autocorr f 0 + hyperbolicMomentEnergy f +
      (∫ y in (0 : ℝ)..|δ|, sinhJumpGramBound f (Finset.range K) (fun _ => 1)
        (fun k => (k : ℝ) * |δ|) (-y)) ≤
      (a + levyCoshPotential screwSignThreshold) * (∫ u, f u ^ 2) +
        ∫ p : ℝ × ℝ, f p.1 * f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  rw [integral_sq_eq_autocorr_zero]
  have h := plasticCrossover_ge_sinhJumpGram f δ K
  unfold plasticCrossover at h
  linarith

/-- Full odd crossover receiver with its origin coefficient and negative moment,
using the even sine multiplier of a constructed odd source. -/
theorem plasticCrossoverWithOrigin_oddSource_ge_sinhJumpGram
    (f : C_c(ℝ, ℝ)) (a δ : ℝ) (K : ℕ) :
    a * autocorr (oddCompactSource f) 0 -
      2 * (∫ u, oddCompactSource f u * Real.sinh (u / 2)) ^ 2 +
      (∫ y in (0 : ℝ)..|δ|, sinhJumpGramBound (oddCompactSource f) (Finset.range K) (fun _ => 1)
        (fun k => (k : ℝ) * |δ|) (-y)) ≤
      (a + levyCoshPotential screwSignThreshold) * (∫ u, oddCompactSource f u ^ 2) +
        ∫ p : ℝ × ℝ, oddCompactSource f p.1 * oddCompactSource f p.2 *
          (2 * Real.cosh ((p.1 - p.2) / 2) - levyCoshKernel screwSignThreshold |p.1 - p.2|) := by
  have h := plasticCrossoverWithOrigin_ge_sinhJumpGram (oddCompactSource f) a δ K
  rw [hyperbolicMomentEnergy_oddSource] at h
  linarith

end
end GaloisForLFunctions.BiScaleUncertainty
