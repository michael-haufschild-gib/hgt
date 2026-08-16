import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyLimit

/-!
# P-G105V: fixed-carrier SP-E cubic-kernel wall limit

The positive square root of the normalized cubic coherence is the exact phase-bearing child
kernel after diagonal normalization.  Pulling the atomic wall laws back by their quantiles places
every aperture on the fixed unit-square carrier.  These pulled-back kernels converge in `L²` to
the unit-exponential wall kernel.  Thus prime-coordinate mass escape is replaced by genuine
fixed-carrier Hilbert--Schmidt convergence data, without deleting any off-diagonal incidence.

Determinant transport through the atomic quantile isometry and the Xi-divisor identification
remain separate gates.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

def routePPrimitiveGammaJuliaStokesWallCubicKernel (a b : ℝ) : ℝ :=
  8 * Real.sqrt a ^ 3 * Real.sqrt b ^ 3 / (a + b) ^ 3

theorem routePPrimitiveGammaJuliaStokesWallCubicKernel_sq
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    routePPrimitiveGammaJuliaStokesWallCubicKernel a b ^ 2 =
      routePPrimitiveGammaJuliaStokesWallCubicCoherence a b := by
  rw [routePPrimitiveGammaJuliaStokesWallCubicKernel,
    routePPrimitiveGammaJuliaStokesWallCubicCoherence,
    routePBaseCauchyCubicNormalizedCoherenceSq]
  norm_num
  by_cases hab : a + b = 0
  · have ha0 : a = 0 := by nlinarith
    have hb0 : b = 0 := by nlinarith
    simp [ha0, hb0]
  · rw [div_pow]
    field_simp [hab]
    ring_nf
    rw [show Real.sqrt a ^ 6 = a ^ 3 by
      rw [show 6 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt ha]]
    rw [show Real.sqrt b ^ 6 = b ^ 3 by
      rw [show 6 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hb]]

theorem routePPrimitiveGammaJuliaStokesWallCubicKernel_zero_le_one
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ routePPrimitiveGammaJuliaStokesWallCubicKernel a b ∧ routePPrimitiveGammaJuliaStokesWallCubicKernel a b ≤ 1 := by
  have hsq := routePPrimitiveGammaJuliaStokesWallCubicKernel_sq ha hb
  have hc := wallCubicCoherence_zero_le_one ha hb
  have hk0 : 0 ≤ routePPrimitiveGammaJuliaStokesWallCubicKernel a b := by
    rw [routePPrimitiveGammaJuliaStokesWallCubicKernel]
    positivity
  constructor
  · exact hk0
  · nlinarith [sq_nonneg (routePPrimitiveGammaJuliaStokesWallCubicKernel a b - 1)]

theorem measurable_routePPrimitiveGammaJuliaStokesWallCubicKernel :
    Measurable (fun z : ℝ × ℝ => routePPrimitiveGammaJuliaStokesWallCubicKernel z.1 z.2) := by
  unfold routePPrimitiveGammaJuliaStokesWallCubicKernel
  fun_prop

theorem tendsto_routePPrimitiveGammaJuliaStokesWallCubicKernel
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ} {A B : ℝ}
    (ha : Tendsto a l (𝓝 A)) (hb : Tendsto b l (𝓝 B))
    (hA : 0 < A) (hB : 0 < B) :
    Tendsto (fun i => routePPrimitiveGammaJuliaStokesWallCubicKernel (a i) (b i)) l
      (𝓝 (routePPrimitiveGammaJuliaStokesWallCubicKernel A B)) := by
  unfold routePPrimitiveGammaJuliaStokesWallCubicKernel
  apply Tendsto.div
  · exact ((tendsto_const_nhds.mul
      ((Real.continuous_sqrt.continuousAt.tendsto.comp ha).pow 3)).mul
        ((Real.continuous_sqrt.continuousAt.tendsto.comp hb).pow 3))
  · exact (ha.add hb).pow 3
  · positivity

theorem routePPrimitiveGammaJuliaStokesWallCubicKernel_scale
    {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b) :
    routePPrimitiveGammaJuliaStokesWallCubicKernel (c * a) (c * b) = routePPrimitiveGammaJuliaStokesWallCubicKernel a b := by
  rw [routePPrimitiveGammaJuliaStokesWallCubicKernel, routePPrimitiveGammaJuliaStokesWallCubicKernel]
  rw [Real.sqrt_mul hc.le, Real.sqrt_mul hc.le]
  have hcsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  field_simp [(add_pos ha hb).ne', hc.ne']
  ring_nf
  calc
    Real.sqrt c ^ 6 = (Real.sqrt c ^ 2) ^ 3 := by ring
    _ = c ^ 3 := by rw [hcsq]

theorem routePPrimitiveGammaJuliaStokesWallCubicKernel_logCoordinate_eq_primeLog
    {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallCubicKernel
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p)
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d q) =
      routePPrimitiveGammaJuliaStokesWallCubicKernel (Real.log (p : ℝ)) (Real.log (q : ℝ)) := by
  rw [routePPrimitiveGammaJuliaStokesWallLogCoordinate,
    routePPrimitiveGammaJuliaStokesWallLogCoordinate]
  change routePPrimitiveGammaJuliaStokesWallCubicKernel ((2 * d) * Real.log (p : ℝ))
      ((2 * d) * Real.log (q : ℝ)) = _
  exact routePPrimitiveGammaJuliaStokesWallCubicKernel_scale (by positivity)
    (Real.log_pos (by exact_mod_cast p.property.one_lt))
    (Real.log_pos (by exact_mod_cast q.property.one_lt))

def routePPrimitiveGammaJuliaStokesWallQuantileKernel (μ : Measure ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.1 ∈ Ioo (0 : ℝ) 1 ∧ z.2 ∈ Ioo (0 : ℝ) 1 then
    routePPrimitiveGammaJuliaStokesWallCubicKernel
      (GaloisForLFunctions.HTGeometry.quantile μ z.1)
      (GaloisForLFunctions.HTGeometry.quantile μ z.2)
  else 0

theorem measurable_routePPrimitiveGammaJuliaStokesWallQuantileKernel
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (routePPrimitiveGammaJuliaStokesWallQuantileKernel μ) := by
  unfold routePPrimitiveGammaJuliaStokesWallQuantileKernel
  refine Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_Ioo.preimage measurable_fst).inter
      (measurableSet_Ioo.preimage measurable_snd)
  · let q : ℝ → ℝ := GaloisForLFunctions.HTGeometry.quantile μ
    have hq : Measurable q := GaloisForLFunctions.HTGeometry.measurable_quantile μ
    have hq1 : Measurable (fun z : ℝ × ℝ => q z.1) := hq.comp measurable_fst
    have hq2 : Measurable (fun z : ℝ × ℝ => q z.2) := hq.comp measurable_snd
    unfold routePPrimitiveGammaJuliaStokesWallCubicKernel
    exact (((measurable_const.mul ((hq1.sqrt).pow_const 3)).mul
      ((hq2.sqrt).pow_const 3)).div ((hq1.add hq2).pow_const 3))

theorem routePPrimitiveGammaJuliaStokesWallQuantileKernel_zero_le_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    (z : ℝ × ℝ) :
    0 ≤ routePPrimitiveGammaJuliaStokesWallQuantileKernel μ z ∧ routePPrimitiveGammaJuliaStokesWallQuantileKernel μ z ≤ 1 := by
  unfold routePPrimitiveGammaJuliaStokesWallQuantileKernel
  split_ifs with hz
  · exact routePPrimitiveGammaJuliaStokesWallCubicKernel_zero_le_one
      (GaloisForLFunctions.HTGeometry.quantile_nonneg hsupp hz.1.1 hz.1.2)
      (GaloisForLFunctions.HTGeometry.quantile_nonneg hsupp hz.2.1 hz.2.2)
  · exact ⟨le_rfl, zero_le_one⟩

theorem tendsto_routePPrimitiveGammaJuliaStokesWallQuantileKernel_nhdsGT_zero (z : ℝ × ℝ) :
    Tendsto
      (fun d : ℝ => routePPrimitiveGammaJuliaStokesWallQuantileKernel
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z)) := by
  unfold routePPrimitiveGammaJuliaStokesWallQuantileKernel
  split_ifs with hz
  · apply tendsto_routePPrimitiveGammaJuliaStokesWallCubicKernel
    · exact tendsto_wallHalfLineQuantile_nhdsGT_zero hz.1.1 hz.1.2
    · exact tendsto_wallHalfLineQuantile_nhdsGT_zero hz.2.1 hz.2.2
    · rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hz.1.1 hz.1.2]
      exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hz.1.2) (by linarith [hz.1.1]))
    · rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hz.2.1 hz.2.2]
      exact neg_pos.mpr (Real.log_neg (sub_pos.mpr hz.2.2) (by linarith [hz.2.1]))
  · exact tendsto_const_nhds

theorem tendsto_integral_routePPrimitiveGammaJuliaStokesWallQuantileKernel_sub_sq_nhdsGT_zero :
    Tendsto
      (fun d : ℝ => ∫ z : ℝ × ℝ,
        ‖routePPrimitiveGammaJuliaStokesWallQuantileKernel
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z -
          routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z‖ ^ 2
        ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  have hmain : Tendsto
      (fun d : ℝ => ∫ z : ℝ × ℝ,
        ‖routePPrimitiveGammaJuliaStokesWallQuantileKernel
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z -
          routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z‖ ^ 2
        ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ _z : ℝ × ℝ, (0 : ℝ)
        ∂routePPrimitiveGammaJuliaStokesWallUnitSquareMeasure)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (4 : ℝ))
    · exact Filter.Eventually.of_forall fun d =>
        (((measurable_routePPrimitiveGammaJuliaStokesWallQuantileKernel
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)).sub
            (measurable_routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1))).norm.pow_const 2).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun d =>
        Filter.Eventually.of_forall fun z => by
        have hd := routePPrimitiveGammaJuliaStokesWallQuantileKernel_zero_le_one
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
          (wallHalfLineLaw_Iio_zero d) z
        have h0 := routePPrimitiveGammaJuliaStokesWallQuantileKernel_zero_le_one
          (expMeasure 1)
          GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero z
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have hxd : ‖routePPrimitiveGammaJuliaStokesWallQuantileKernel
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg hd.1]
          exact hd.2
        have hx0 : ‖routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z‖ ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_nonneg h0.1]
          exact h0.2
        have habs : ‖routePPrimitiveGammaJuliaStokesWallQuantileKernel
              (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z -
            routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z‖ ≤ 2 := by
          calc
            ‖_ - _‖ ≤ ‖routePPrimitiveGammaJuliaStokesWallQuantileKernel
                (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z‖ +
                ‖routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z‖ := norm_sub_le _ _
            _ ≤ 1 + 1 := add_le_add hxd hx0
            _ = 2 := by norm_num
        exact (pow_le_pow_left₀ (norm_nonneg _) habs 2).trans_eq (by norm_num)
    · exact integrable_const 4
    · exact Filter.Eventually.of_forall fun z => by
        have h := (tendsto_routePPrimitiveGammaJuliaStokesWallQuantileKernel_nhdsGT_zero z).sub
          (tendsto_const_nhds : Tendsto
            (fun _ : ℝ => routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z)
            (𝓝[>] (0 : ℝ))
            (𝓝 (routePPrimitiveGammaJuliaStokesWallQuantileKernel (expMeasure 1) z)))
        have hs := h.norm.pow 2
        simpa using hs
  simpa using hmain

private theorem wallCubicKernel_weight_factorization
    {sp sq lp lq P Q : ℝ}
    (hsp : 0 ≤ sp) (hsq : 0 ≤ sq)
    (hlp : 0 < lp) (hlq : 0 < lq) (hP : 0 < P) (hQ : 0 < Q) :
    Real.sqrt sp * lp *
          (Real.sqrt lp / Real.sqrt P * (2 / (lp + lq) ^ 3) *
            (Real.sqrt lq / Real.sqrt Q)) *
        lq * Real.sqrt sq =
      Real.sqrt (sp * (1 / 4 * (1 / P))) *
        Real.sqrt (sq * (1 / 4 * (1 / Q))) *
          routePPrimitiveGammaJuliaStokesWallCubicKernel lp lq := by
  rw [Real.sqrt_mul hsp, Real.sqrt_mul hsq]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
  norm_num [routePPrimitiveGammaJuliaStokesWallCubicKernel]
  field_simp [(Real.sqrt_pos.2 hP).ne', (Real.sqrt_pos.2 hQ).ne',
    (add_pos hlp hlq).ne']
  ring_nf
  rw [Real.sq_sqrt hlp.le, Real.sq_sqrt hlq.le]
  ring

theorem routePPrimitiveGammaJuliaStokesCofinalChildKernel_eq_wallCubicKernel
    {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesCofinalChildKernel d (p, q) =
      ((Real.sqrt
          (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d p) *
        Real.sqrt
          (routePPrimitiveGammaJuliaStokesTransportedPrimeWeight d q) *
        routePPrimitiveGammaJuliaStokesWallCubicKernel (Real.log (p : ℝ)) (Real.log (q : ℝ)) : ℝ) : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesCofinalChildKernel]
  rw [xiGammaEulerPrimitiveLogFrequency_prime_zero,
    xiGammaEulerPrimitiveLogFrequency_prime_zero]
  rw [finiteVonMangoldtDepthOneAmplitude, finiteVonMangoldtDepthOneAmplitude]
  simp only [xiGammaEulerValuationNat, zero_add, pow_one]
  rw [ArithmeticFunction.vonMangoldt_apply_prime p.property,
    ArithmeticFunction.vonMangoldt_apply_prime q.property]
  rw [routePBaseCauchyCubicKernel, routePCollisionPairFrequency]
  norm_num
  rw [routePPrimitiveGammaJuliaStokesTransportedPrimeWeight,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero,
    routePPrimitiveGammaJuliaLogCofinalTraceWeight_prime_zero,
    routePPrimitiveGammaJuliaStokesWallCubicKernel]
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hq : (0 : ℝ) < (q : ℝ) := by exact_mod_cast q.property.pos
  have hlp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hlq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  have hreal := wallCubicKernel_weight_factorization
    (sp := routePPrimitiveGammaJuliaStokesApertureScaleSq d p)
    (sq := routePPrimitiveGammaJuliaStokesApertureScaleSq d q)
    (lp := Real.log (p : ℝ)) (lq := Real.log (q : ℝ))
    (P := (p : ℝ)) (Q := (q : ℝ))
    (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd p).le
    (routePPrimitiveGammaJuliaStokesApertureScaleSq_pos hd q).le
    hlp hlq hp hq
  exact_mod_cast hreal

end
end RHTower
