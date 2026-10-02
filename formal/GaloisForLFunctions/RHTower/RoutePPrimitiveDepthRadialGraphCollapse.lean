import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardResolvedGeneratorGraph
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerSecantGraphCompletion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Primitive depth coefficients are invisible to polynomial radial graph completion

At one fixed prime, an explicit finite binomial packet has original-depth coefficient one
but tends to zero in every polynomial radial graph seminorm. Equivalently, strictly higher
depths approximate the original column in all these seminorms. The packet uses the literal
Burnol columns and their exact von Mangoldt amplitudes.

This identifies a source-domain obstruction: radial generator powers alone cannot provide
continuous recovery of primitive coefficients. It does not assert the RP history floor or
convergence in the completed-Xi jet carrier.
-/

open Complex Set MeasureTheory Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact coefficient of depth `e+j` in the binomial residual packet. -/
def routePDepthBinomialCoefficient (p : Nat.Primes) (e N j : ℕ) : ℂ :=
  (-1) ^ j * (N.choose j : ℂ) *
    (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)) /
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e + j)))

/-- Finite packet on the actual depths `e, ..., e+N`; no fitted source columns. -/
def routePDepthBinomialPacket (p : Nat.Primes) (e N : ℕ) (L : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1),
    routePDepthBinomialCoefficient p e N j *
      routePPrimitiveBurnolWindowFeature (p, e + j) 0 L

@[simp] theorem routePDepthBinomialCoefficient_zero (p : Nat.Primes) (e N : ℕ) :
    routePDepthBinomialCoefficient p e N 0 = 1 := by
  simp [routePDepthBinomialCoefficient,
    finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero]

private theorem feature_zero_clock (pe : Nat.Primes × ℕ) (L : ℝ) :
    routePPrimitiveBurnolWindowFeature pe 0 L =
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat pe) *
        (L : ℂ) * (Real.exp (-xiGammaEulerPrimitiveLogFrequency pe * L) : ℂ) := by
  rw [routePPrimitiveBurnolWindowFeature_eq_resolvedRadialGeneratorMode]
  simp [xiWardResolvedRadialGeneratorMode, xiWardResolvedRadialMode,
    Complex.ofReal_exp, mul_assoc]

private theorem frequency_add (p : Nat.Primes) (e j : ℕ) :
    xiGammaEulerPrimitiveLogFrequency (p, e + j) =
      xiGammaEulerPrimitiveLogFrequency (p, e) + j * Real.log (p : ℝ) := by
  simp only [xiGammaEulerPrimitiveLogFrequency, xiGammaEulerValuationNat,
    Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  ring

private theorem normalized_depth_shift (p : Nat.Primes) (e j : ℕ) (L : ℝ) :
    (finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e)) /
      finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e + j))) *
        routePPrimitiveBurnolWindowFeature (p, e + j) 0 L =
      routePPrimitiveBurnolWindowFeature (p, e) 0 L *
        (Real.exp (-Real.log (p : ℝ) * L) : ℂ) ^ j := by
  rw [feature_zero_clock, feature_zero_clock, frequency_add]
  have hexp : Real.exp
      (-(xiGammaEulerPrimitiveLogFrequency (p, e) + j * Real.log (p : ℝ)) * L) =
      Real.exp (-xiGammaEulerPrimitiveLogFrequency (p, e) * L) *
        Real.exp (-Real.log (p : ℝ) * L) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  push_cast
  field_simp [finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero (p, e + j)]

/-- Exact binomial cancellation on the literal prime-depth source. -/
theorem routePDepthBinomialPacket_eq (p : Nat.Primes) (e N : ℕ) (L : ℝ) :
    routePDepthBinomialPacket p e N L =
      routePPrimitiveBurnolWindowFeature (p, e) 0 L *
        ((1 - Real.exp (-Real.log (p : ℝ) * L)) ^ N : ℝ) := by
  let x : ℂ := (Real.exp (-Real.log (p : ℝ) * L) : ℂ)
  have hbin : (1 - x) ^ N =
      ∑ j ∈ Finset.range (N + 1), (-1 : ℂ) ^ j * (N.choose j : ℂ) * x ^ j := by
    rw [show 1 - x = -x + 1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    rw [neg_eq_neg_one_mul, mul_pow]
    simp only [one_pow, mul_one]
    ring
  simp only [Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  change _ = routePPrimitiveBurnolWindowFeature (p, e) 0 L * (1 - x) ^ N
  rw [hbin, Finset.mul_sum, routePDepthBinomialPacket]
  apply Finset.sum_congr rfl
  intro j hj
  rw [routePDepthBinomialCoefficient]
  rw [mul_assoc, normalized_depth_shift]
  dsimp [x]
  ring

/-- Square of the graph seminorm for the `r`-th radial position generator. -/
def routePRadialGraphEnergy (r : ℕ) (f : ℝ → ℂ) : ℝ :=
  ∫ L : ℝ in Ioi 0, L ^ (2 * r) * ‖f L‖ ^ 2

private theorem integrable_graph_column (p : Nat.Primes) (e r : ℕ) :
    IntegrableOn (fun L : ℝ => L ^ (2 * r) *
      ‖routePPrimitiveBurnolWindowFeature (p, e) 0 L‖ ^ 2) (Ioi 0) := by
  let a := xiGammaEulerPrimitiveLogFrequency (p, e)
  let A := finiteVonMangoldtDepthOneAmplitude (xiGammaEulerValuationNat (p, e))
  have ha : 0 < a := xiGammaEulerPrimitiveLogFrequency_pos (p, e)
  have hi : IntegrableOn
      (fun L : ℝ => L ^ (2 * r + 2) * Real.exp (-(2 * a) * L)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := ((2 * r + 2 : ℕ) : ℝ)) (p := 1) (b := 2 * a)
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg _))
      le_rfl (by positivity)
    simpa only [Real.rpow_natCast, Real.rpow_one] using h
  have hs : IntegrableOn
      (fun L : ℝ => ‖A‖ ^ 2 *
        (L ^ (2 * r + 2) * Real.exp (-(2 * a) * L))) (Ioi 0) :=
    hi.const_mul (‖A‖ ^ 2)
  refine hs.congr_fun ?_ measurableSet_Ioi
  intro L hL
  have hL0 : 0 ≤ L := le_of_lt hL
  dsimp only
  rw [feature_zero_clock]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hL0, abs_of_pos (Real.exp_pos _), mul_pow]
  have he : Real.exp (-a * L) ^ 2 = Real.exp (-(2 * a) * L) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  change ‖A‖ ^ 2 * (L ^ (2 * r + 2) * Real.exp (-(2 * a) * L)) = _
  rw [← he, pow_add]
  dsimp [A, a]
  ring

/-- One packet tends to zero in every polynomial radial graph seminorm, while its
original-depth coefficient remains exactly one. -/
theorem tendsto_routePRadialGraphEnergy_depthBinomialPacket
    (p : Nat.Primes) (e r : ℕ) :
    Tendsto (fun N => routePRadialGraphEnergy r (routePDepthBinomialPacket p e N))
      atTop (nhds 0) := by
  let b : ℝ → ℝ := fun L => L ^ (2 * r) *
    ‖routePPrimitiveBurnolWindowFeature (p, e) 0 L‖ ^ 2
  let q : ℝ → ℝ := fun L => 1 - Real.exp (-Real.log (p : ℝ) * L)
  have hq (L : ℝ) (hL : 0 < L) : 0 ≤ q L ∧ q L < 1 := by
    have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
    have hx : Real.exp (-Real.log (p : ℝ) * L) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    dsimp [q]
    constructor
    · linarith
    · linarith [Real.exp_pos (-Real.log (p : ℝ) * L)]
  have heq (N : ℕ) (L : ℝ) :
      L ^ (2 * r) * ‖routePDepthBinomialPacket p e N L‖ ^ 2 =
        b L * (q L ^ N) ^ 2 := by
    rw [routePDepthBinomialPacket_eq, norm_mul, mul_pow,
      Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (mul_assoc _ _ _).symm
  have hm (N : ℕ) : AEStronglyMeasurable (fun L => b L * (q L ^ N) ^ 2)
      (volume.restrict (Ioi 0)) := by
    have hc : Continuous (fun L => b L * (q L ^ N) ^ 2) := by
      dsimp [b, q]
      exact (continuous_id.pow _ |>.mul
        ((continuous_routePPrimitiveBurnolWindowFeature (p, e) 0).norm.pow 2)).mul
          ((continuous_const.sub (Real.continuous_exp.comp
            (continuous_const.mul continuous_id))).pow N |>.pow 2)
    exact hc.aestronglyMeasurable
  have hb : Integrable b (volume.restrict (Ioi 0)) := integrable_graph_column p e r
  have hbound (N : ℕ) : ∀ᵐ L ∂volume.restrict (Ioi (0 : ℝ)),
      ‖b L * (q L ^ N) ^ 2‖ ≤ b L := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
    have hb0 : 0 ≤ b L := mul_nonneg (pow_nonneg hL.le _) (sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb0 (sq_nonneg _))]
    exact mul_le_of_le_one_right hb0
      (pow_le_one₀ (pow_nonneg (hq L hL).1 N) (pow_le_one₀ (hq L hL).1 (hq L hL).2.le) )
  have hlim : ∀ᵐ L ∂volume.restrict (Ioi (0 : ℝ)),
      Tendsto (fun N => b L * (q L ^ N) ^ 2) atTop (nhds (0 : ℝ)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with L hL
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one
      (hq L hL).1 (hq L hL).2).pow 2).const_mul (b L)
  have h := tendsto_integral_of_dominated_convergence b hm hb hbound hlim
  simpa only [integral_zero, routePRadialGraphEnergy, heq] using h

/-- The approximating packet has only strictly higher depths. -/
def routePDepthHigherPacket (p : Nat.Primes) (e N : ℕ) (L : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N,
    -routePDepthBinomialCoefficient p e N (j + 1) *
      routePPrimitiveBurnolWindowFeature (p, e + (j + 1)) 0 L

theorem routePDepthHigherPacket_residual (p : Nat.Primes) (e N : ℕ) (L : ℝ) :
    routePPrimitiveBurnolWindowFeature (p, e) 0 L -
      routePDepthHigherPacket p e N L = routePDepthBinomialPacket p e N L := by
  simp only [routePDepthHigherPacket, routePDepthBinomialPacket,
    Finset.sum_range_succ', Nat.add_zero, routePDepthBinomialCoefficient_zero,
    one_mul, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Every original column is approximated by the displayed strictly higher-depth packets
in all polynomial radial graph seminorms simultaneously. -/
theorem tendsto_routePRadialGraphEnergy_higherDepth_approximation
    (p : Nat.Primes) (e r : ℕ) :
    Tendsto (fun N => routePRadialGraphEnergy r (fun L =>
      routePPrimitiveBurnolWindowFeature (p, e) 0 L - routePDepthHigherPacket p e N L))
      atTop (nhds 0) := by
  simp only [routePDepthHigherPacket_residual]
  exact tendsto_routePRadialGraphEnergy_depthBinomialPacket p e r

/-- No finite collection of radial graph energies controls even the original-depth
coefficient of these actual finite packets. -/
theorem not_routePDepthCoefficient_controlled_by_radialGraph
    (p : Nat.Primes) (e : ℕ) :
    ¬ ∃ (R : ℕ) (C : ℝ), ∀ N : ℕ,
      ‖routePDepthBinomialCoefficient p e N 0‖ ^ 2 ≤
        C * ∑ r ∈ Finset.range (R + 1),
          routePRadialGraphEnergy r (routePDepthBinomialPacket p e N) := by
  rintro ⟨R, C, hC⟩
  have hs := tendsto_finsetSum (Finset.range (R + 1))
    (fun r _ => tendsto_routePRadialGraphEnergy_depthBinomialPacket p e r)
  have ht : Tendsto (fun N => C * ∑ r ∈ Finset.range (R + 1),
      routePRadialGraphEnergy r (routePDepthBinomialPacket p e N)) atTop (nhds 0) := by
    simpa using hs.const_mul C
  obtain ⟨N, hN⟩ := (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1)).exists
  have h := hC N
  simp only [routePDepthBinomialCoefficient_zero, norm_one, one_pow] at h
  exact (not_lt_of_ge h) hN

/-- The coefficient lost by every polynomial graph norm survives at the far radial boundary.
Thus the graph limit and this source boundary trace do not commute. -/
theorem tendsto_routePDepthBinomialPacket_boundary_ratio
    (p : Nat.Primes) (e N : ℕ) :
    Tendsto (fun L : ℝ => routePDepthBinomialPacket p e N L /
      routePPrimitiveBurnolWindowFeature (p, e) 0 L) atTop (nhds 1) := by
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hx : Tendsto (fun L : ℝ => Real.exp (-Real.log (p : ℝ) * L))
      atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hp)).2
      tendsto_id)
  have hr : Tendsto (fun L : ℝ => (1 - Real.exp (-Real.log (p : ℝ) * L)) ^ N)
      atTop (nhds 1) := by
    simpa using (hx.const_sub 1).pow N
  have hc := (Complex.continuous_ofReal.tendsto 1).comp hr
  apply hc.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hf : routePPrimitiveBurnolWindowFeature (p, e) 0 L ≠ 0 := by
    rw [feature_zero_clock]
    exact mul_ne_zero
      (mul_ne_zero (finiteVonMangoldtDepthOneAmplitude_primitive_ne_zero (p, e))
        (Complex.ofReal_ne_zero.mpr hL.ne'))
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  rw [routePDepthBinomialPacket_eq]
  dsimp only [Function.comp_apply]
  field_simp

end

end RHTower
