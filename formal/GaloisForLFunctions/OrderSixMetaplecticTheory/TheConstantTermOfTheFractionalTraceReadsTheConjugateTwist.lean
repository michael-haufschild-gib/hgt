import GaloisForLFunctions.OrderSixMetaplecticTheory.TheFractionalTracePhasesSumToJacobiAndGaussSums

/-!
# The constant term of the fractional trace reads the conjugate twist

For the projected theta function θ_s (Fourier series Σ_k b(v, k) e(ξ_kz)) and an odd primary prime q, the constant
term of the fractional trace is (`integral_sourceFracTrace`)

∫_P Tr G(z, v) dz = |P| (Σ_k b(v, k)b(v, −k)(N² + N − J + NJ[q ∣ k])
    + N² χ(−4)χ(9)⁻¹ Σ_k b(v/N, k)b(v/N, −k) g_χ(k)),

g_χ(k) = Σ_u χ(u)ψ(uk) the cubic Gauss sum at k, J the Jacobi sum of χ and the quadratic character:

* the cusp ∞ (G itself) reads the q-divisible frequencies: N Σ_{q ∣ k};
* the N − 1 middle cusps read N − J + (J − 1)N[q ∣ k] (Jacobi phases), their high points cancel;
* the cusp 0 reads N²Σ_k plus the low points of low points, whose Gauss sums g_χ(k) = χ̄(k)g_χ make the
  **conjugate twist** Σ_k χ̄(k)b(v/N, k)b(v/N, −k).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

/-! ### Products of translated cusp series -/

theorem summable_mul_neg {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖))
    (φ : O → ℂ) (hφ : ∀ k, ‖φ k‖ ≤ 1) : Summable (fun k => c k * d (-k) * φ k) := by
  have h := (summable_conv_family hc hd).prod_factor 0
  refine Summable.of_norm_bounded h fun k => ?_
  simp only [zero_sub, norm_mul]
  exact mul_le_of_le_one_right (by positivity) (hφ k)

/-- **Parseval for translates.** ∫_P S_c(z + α)S_d(z + β) = |P| Σ_k c(k)d(−k)e(ξ_k(α − β)). -/
theorem integral_translate_mul (c d : O → ℂ) (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖))
    (α β : ℂ) :
    ∫ z in periodDomain, cuspCharacterSeries c (z + α) * cuspCharacterSeries d (z + β) =
      periodArea * ∑' k : O, c k * d (-k) * tracePhase (cuspFrequency k * (α - β)) := by
  set c' : O → ℂ := fun h => c h * tracePhase (cuspFrequency h * α)
  set d' : O → ℂ := fun h => d h * tracePhase (cuspFrequency h * β)
  have hc' : Summable (fun h => ‖c' h‖) := by simpa only [c', norm_mul, tracePhase_norm, mul_one] using hc
  have hd' : Summable (fun h => ‖d' h‖) := by simpa only [d', norm_mul, tracePhase_norm, mul_one] using hd
  simp_rw [cuspCharacterSeries_translate]
  change ∫ z in periodDomain, cuspCharacterSeries c' z * cuspCharacterSeries d' z = _
  simp_rw [cuspCharacterSeries_mul hc' hd']
  rw [PrimaryPrime.integral_cuspCharacterSeries _ (summable_cuspConv hc' hd')]
  congr 1
  unfold cuspConv
  refine tsum_congr fun k => ?_
  simp only [c', d', zero_sub, cuspFrequency, map_neg]
  rw [mul_sub, AddChar.map_sub_eq_div,
    show -ringComplex k / (3 * ringComplex traceLambda) * β = -(ringComplex k / (3 * ringComplex traceLambda) * β) by ring,
    AddChar.map_neg_eq_inv]
  ring


namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- The fractional trace of the projected theta function. -/
abbrev sourceFracTrace : HyperbolicSpace → ℂ := P.fracTrace sourceTheta

theorem sourceTheta_fracShift (t : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceTheta (P.fracShift t • upperPoint z v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude v) (z + 3 * ringComplex t / ringComplex P.p) := by
  rw [fracShift, complexTranslation_action, sourceTheta, cubicSourceResidualFunction_fourier_expansion]

theorem psi_eq_traceChar (k : O) (r : P.Res) : P.psi k r = P.traceChar (r * P.res k) := by
  have e : cuspFrequency k * (-(3 * ringComplex (-P.lift r)) / ringComplex P.p) =
      cuspFrequency k * (3 * ringComplex (P.lift r) / ringComplex P.p) := by
    rw [map_neg]
    ring
  calc P.psi k r = P.psi k (P.res (-(-P.lift r))) := by rw [neg_neg, res_lift]
    _ = tracePhase (cuspFrequency k * (-(3 * ringComplex (-P.lift r)) / ringComplex P.p)) := (P.phase_eq_psi k _).symm
    _ = P.traceChar (r * P.res k) := by rw [e, P.tracePhase_low, res_lift]

theorem res_eq_zero_iff_two (h2 : (2 : P.Res) ≠ 0) (k : O) : 2 * P.res k = 0 ↔ P.p ∣ k := by
  rw [← P.res_eq_zero_iff]
  exact ⟨fun h => (mul_eq_zero.mp h).resolve_left h2, fun h => by rw [h, mul_zero]⟩

/-- Finite sums of products of translates. -/
theorem integral_sum_translate_mul {ι : Type*} [Fintype ι] (c d : O → ℂ) (hc : Summable (fun h => ‖c h‖))
    (hd : Summable (fun h => ‖d h‖)) (α β : ι → ℂ) :
    ∫ z in periodDomain, ∑ i, cuspCharacterSeries c (z + α i) * cuspCharacterSeries d (z + β i) =
      periodArea * ∑' k : O, c k * d (-k) * ∑ i, tracePhase (cuspFrequency k * (α i - β i)) := by
  have hcont : ∀ i, Continuous (fun z : ℂ => cuspCharacterSeries c (z + α i) * cuspCharacterSeries d (z + β i)) :=
    fun i => ((cuspCharacterSeries_continuous c hc).comp (continuous_id.add continuous_const)).mul
      ((cuspCharacterSeries_continuous d hd).comp (continuous_id.add continuous_const))
  have hs : ∀ i, Summable (fun k => c k * d (-k) * tracePhase (cuspFrequency k * (α i - β i))) := fun i =>
    summable_mul_neg hc hd _ (fun k => (tracePhase_norm _).le)
  rw [integral_finsetSum _ (fun i _ => integrableOn_periodDomain_of_continuous _ (hcont i))]
  simp_rw [integral_translate_mul c d hc hd]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hs i)]
  congr 1
  refine tsum_congr fun k => ?_
  rw [Finset.mul_sum]

/-- **The cusp ∞.** ∫_P G = |P| Σ_k b(k)b(−k) N[q ∣ k]. -/
theorem integral_fracSum_source (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.fracSum sourceTheta (upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (if P.p ∣ k then P.normC else 0) := by
  set b := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have e : ∀ z, P.fracSum sourceTheta (upperPoint z v hv) = ∑ x : P.Res,
      cuspCharacterSeries b (z + 3 * ringComplex (P.lift x) / ringComplex P.p) *
        cuspCharacterSeries b (z + 3 * ringComplex (-P.lift x) / ringComplex P.p) := by
    intro z
    unfold fracSum fracCorrelation
    simp_rw [P.sourceTheta_fracShift]
    rfl
  simp_rw [e]
  rw [integral_sum_translate_mul b b hb hb]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  have hsum : ∑ x : P.Res, tracePhase (cuspFrequency k * (3 * ringComplex (P.lift x) / ringComplex P.p -
      3 * ringComplex (-P.lift x) / ringComplex P.p)) = ∑ x : P.Res, P.traceChar (x * (2 * P.res k)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show 3 * ringComplex (P.lift x) / ringComplex P.p - 3 * ringComplex (-P.lift x) / ringComplex P.p =
        3 * ringComplex (2 * P.lift x) / ringComplex P.p by rw [map_neg, map_mul, map_ofNat]; ring,
      P.tracePhase_low, show P.res (2 * P.lift x) = 2 * x by rw [map_mul, res_lift, map_ofNat]]
    congr 1
    ring
  rw [hsum, P.sum_traceChar_mul, if_congr (P.res_eq_zero_iff_two h2 k) rfl rfl]

/-- **The high points.** ∫_P θ(A_q²w)θ(T_uw) does not depend on u. -/
theorem integral_high_mul (u : O) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, sourceTheta (P.dilation • P.dilation • upperPoint z v hv) *
        sourceTheta (P.fracShift u • upperPoint z v hv) =
      periodArea * ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * (‖ringComplex P.p‖ * v)) h *
        rationalSourceModeAmplitude v (-(h * P.p ^ 2)) := by
  set a := rationalSourceModeAmplitude (‖ringComplex P.p‖ * (‖ringComplex P.p‖ * v))
  set b := rationalSourceModeAmplitude v
  have hP := P.ringComplex_ne_zero
  have ha : Summable (fun h => ‖a h‖) :=
    rationalSourceModeAmplitude_summable _ (mul_pos P.norm_pos (mul_pos P.norm_pos hv))
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  set b' : O → ℂ := fun h => b h * tracePhase (cuspFrequency h * (3 * ringComplex u / ringComplex P.p))
  have hb' : Summable (fun h => ‖b' h‖) := by simpa only [b', norm_mul, tracePhase_norm, mul_one] using hb
  have e : ∀ z, sourceTheta (P.dilation • P.dilation • upperPoint z v hv) *
      sourceTheta (P.fracShift u • upperPoint z v hv) =
      cuspCharacterSeries a (ringComplex (P.p ^ 2) * z) * cuspCharacterSeries b' z := by
    intro z
    rw [P.dilation_upperPoint, P.dilation_upperPoint, P.sourceTheta_fracShift, sourceTheta,
      cubicSourceResidualFunction_fourier_expansion, cuspCharacterSeries_translate]
    congr 2
    rw [map_pow]
    ring
  simp_rw [e]
  rw [integral_cuspCharacterSeries_mul_dilate (P.p ^ 2) a b' ha hb']
  congr 1
  refine tsum_congr fun h => ?_
  simp only [b']
  have hph : tracePhase (cuspFrequency (-(h * P.p ^ 2)) * (3 * ringComplex u / ringComplex P.p)) = 1 := by
    rw [show -(h * P.p ^ 2) = -(h * P.p) * P.p by ring, cuspFrequency_mul_right,
      show cuspFrequency (-(h * P.p)) * ringComplex P.p * (3 * ringComplex u / ringComplex P.p) =
        cuspFrequency (-(h * P.p)) * (3 * ringComplex u) by field_simp, cuspFrequency_period]
  rw [hph, mul_one]

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
