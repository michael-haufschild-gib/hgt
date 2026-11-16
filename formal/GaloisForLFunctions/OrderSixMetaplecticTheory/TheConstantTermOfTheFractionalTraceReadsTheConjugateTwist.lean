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

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-! ### Continuity in the horizontal variable -/

theorem continuous_upperPoint_z (v : ℝ) (hv : 0 < v) : Continuous (fun z : ℂ => upperPoint z v hv) := by
  have hcoord : Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) := by fun_prop
  exact upperCoordinatesHomeomorph.continuous.comp hcoord

theorem continuous_fracSum_source : Continuous (P.fracSum sourceTheta) := by
  unfold fracSum fracCorrelation
  exact continuous_finsetSum _ fun x _ =>
    (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).mul
      (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _))

theorem continuous_fracCorrelation_source (t : O) : Continuous (P.fracCorrelation sourceTheta t) := by
  unfold fracCorrelation
  exact (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _)).mul
    (cubicSourceResidualFunction_continuous.comp (continuous_hyperbolic_action _))

/-- The constant term of the high pairs, \`|P| Σ_h b(N(q)v, h)b(v, −q²h)\`. -/
def highTerm (v : ℝ) : ℂ :=
  periodArea * ∑' h : O, rationalSourceModeAmplitude (‖ringComplex P.p‖ * (‖ringComplex P.p‖ * v)) h *
    rationalSourceModeAmplitude v (-(h * P.p ^ 2))

theorem norm_chi_le (u : P.Res) : ‖P.chi u‖ ≤ 1 := by
  by_cases hu : u = 0
  · rw [hu, MulChar.map_zero, norm_zero]
    exact zero_le_one
  · have h := P.chi_cube u hu
    have h3 : ‖P.chi u‖ ^ 3 = 1 := by rw [← norm_pow, h, norm_one]
    have h0 : 0 ≤ ‖P.chi u‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖P.chi u‖ - 1), sq_nonneg ‖P.chi u‖]

theorem norm_traceChar (r : P.Res) : ‖P.traceChar r‖ = 1 := AddChar.norm_apply _ _

/-- **One pair over a middle cusp.** -/
theorem integral_fracCorrelation_middle (h2 : (2 : P.Res) ≠ 0) (x : {x : P.Res // x ≠ 0}) (t : P.Res) (v : ℝ)
    (hv : 0 < v) :
    ∫ z in periodDomain, P.fracCorrelation sourceTheta (P.lift t)
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * P.highTerm v else 0) +
        P.chi (1 - (9 * t * x.1) ^ 2) * (periodArea * ∑' k : O, rationalSourceModeAmplitude v k *
          rationalSourceModeAmplitude v (-k) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k)) := by
  have hb : Summable (fun h => ‖rationalSourceModeAmplitude v h‖) := rationalSourceModeAmplitude_summable v hv
  simp_rw [P.fracCorrelation_lowerThree sourceTheta sourceTheta_automorphy h2 x t]
  by_cases h₁ : 1 + 9 * t * x.1 = 0
  · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 - 9 * t * x.1) * h₁
    simp_rw [if_pos h₁]
    rw [if_pos (Or.inl h₁), hsq, MulChar.map_zero, zero_mul, add_zero, integral_const_mul, P.integral_high_mul,
      highTerm]
  · by_cases h₂ : 1 - 9 * t * x.1 = 0
    · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 = 0 := by linear_combination (1 + 9 * t * x.1) * h₂
      simp_rw [if_neg h₁, if_pos h₂]
      rw [if_pos (Or.inr h₂), hsq, MulChar.map_zero, zero_mul, add_zero, integral_const_mul, P.integral_high_mul,
        highTerm]
    · have hsq : (1 : P.Res) - (9 * t * x.1) ^ 2 ≠ 0 := by
        rw [show (1 : P.Res) - (9 * t * x.1) ^ 2 = (1 + 9 * t * x.1) * (1 - 9 * t * x.1) by ring]
        exact mul_ne_zero h₁ h₂
      simp_rw [if_neg h₁, if_neg h₂]
      rw [if_neg (not_or.mpr ⟨h₁, h₂⟩), zero_add, integral_const_mul]
      simp_rw [P.sourceTheta_fracShift]
      rw [integral_translate_mul _ _ hb hb]
      congr 2
      refine tsum_congr fun k => ?_
      congr 1
      rw [show 3 * ringComplex (P.lift (t / (1 + 9 * t * x.1))) / ringComplex P.p -
          3 * ringComplex (P.lift (-t / (1 - 9 * t * x.1))) / ringComplex P.p =
          3 * ringComplex (P.lift (t / (1 + 9 * t * x.1)) - P.lift (-t / (1 - 9 * t * x.1))) / ringComplex P.p by
        rw [map_sub]; ring, P.tracePhase_low, map_sub, res_lift, res_lift]
      congr 1
      have ha : (1 + 9 * t * x.1) ≠ 0 := h₁
      have hb' : (1 - 9 * t * x.1) ≠ 0 := h₂
      have key : t / (1 + 9 * t * x.1) - -t / (1 - 9 * t * x.1) = 2 * t / (1 - (9 * t * x.1) ^ 2) := by
        rw [neg_div, sub_neg_eq_add, div_add_div _ _ ha hb']
        congr 1 <;> ring
      rw [key]

/-! ### Low points of low points -/

/-- **Averaging over \`O/q²\`.** The pairs of low points of low points average to a cusp series in \`z\`. -/
theorem sum_lowLow (r₁ r₂ : O) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    ∑ s : P.Res × P.Res, P.heckeLow sourceTheta r₁
        (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
      P.heckeLow sourceTheta r₂ (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * cuspCharacterSeries (fun m => cuspConv (P.shiftedLow (v / ‖ringComplex P.p‖) (r₂ - r₁))
        (rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)) (m * P.p * P.p)) z := by
  have hn := P.norm_pos
  have hP := P.ringComplex_ne_zero
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv hn
  set b := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv1 hn)
  set g := cuspConv (P.shiftedLow (v / ‖ringComplex P.p‖) (r₂ - r₁)) b
  have hg : Summable (fun h => ‖g h‖) := summable_cuspConv (P.summable_shiftedLow _ hv1 _) hb
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  have hg1 : Summable (fun m => ‖g (m * P.p)‖) := hg.comp_injective hinj
  have hpt : ∀ s : P.Res × P.Res, P.heckeLow sourceTheta r₁
      (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) *
      P.heckeLow sourceTheta r₂ (P.contraction • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      cuspCharacterSeries g ((((z + 3 * ringComplex (P.lift s.1)) / ringComplex P.p + 3 * ringComplex r₂) +
        3 * ringComplex (P.lift s.2)) / ringComplex P.p) := by
    intro s
    rw [transThree_smul_upperPoint, P.contraction_upperPoint, P.heckeLow_source, P.heckeLow_source]
    have e1 : ((z + 3 * ringComplex (P.sqLift s)) / ringComplex P.p + 3 * ringComplex r₁) / ringComplex P.p =
        (((z + 3 * ringComplex (P.lift s.1)) / ringComplex P.p + 3 * ringComplex r₂) + 3 * ringComplex (P.lift s.2)) /
          ringComplex P.p + -(3 * ringComplex (r₂ - r₁)) / ringComplex P.p := by
      simp only [sqLift, map_add, map_mul, map_sub]
      field_simp
      ring
    have e2 : ((z + 3 * ringComplex (P.sqLift s)) / ringComplex P.p + 3 * ringComplex r₂) / ringComplex P.p =
        (((z + 3 * ringComplex (P.lift s.1)) / ringComplex P.p + 3 * ringComplex r₂) + 3 * ringComplex (P.lift s.2)) /
          ringComplex P.p := by
      simp only [sqLift, map_add, map_mul]
      field_simp
      ring
    rw [e1, e2, cuspCharacterSeries_translate]
    exact cuspCharacterSeries_mul (P.summable_shiftedLow _ hv1 _) hb _
  simp_rw [hpt]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ s₀ : P.Res, ∑ s₁ : P.Res, cuspCharacterSeries g
      ((((z + 3 * ringComplex (P.lift s₀)) / ringComplex P.p + 3 * ringComplex r₂) + 3 * ringComplex (P.lift s₁)) /
        ringComplex P.p) =
      P.normC * cuspCharacterSeries (fun m => g (m * P.p)) ((z + 3 * ringComplex (P.lift s₀)) / ringComplex P.p) := by
    intro s₀
    rw [P.sum_cuspCharacterSeries_low g hg, cuspCharacterSeries_period]
  simp_rw [hinner]
  rw [← Finset.mul_sum, P.sum_cuspCharacterSeries_low _ hg1]
  ring

end PrimaryPrime

theorem summable_mul_neg_bdd {c d : O → ℂ} (hc : Summable (fun h => ‖c h‖)) (hd : Summable (fun h => ‖d h‖))
    (φ : O → ℂ) (M : ℝ) (hφ : ∀ k, ‖φ k‖ ≤ M) : Summable (fun k => c k * d (-k) * φ k) := by
  have h := ((summable_conv_family hc hd).prod_factor 0).mul_right M
  refine Summable.of_norm_bounded h fun k => ?_
  simp only [zero_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (hφ k) (by positivity)

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem sum_tsum_swap {ι : Type*} [Fintype ι] (c d : O → ℂ) (hc : Summable (fun h => ‖c h‖))
    (hd : Summable (fun h => ‖d h‖)) (g : ι → O → ℂ) (M : ℝ) (hg : ∀ i k, ‖g i k‖ ≤ M) :
    ∑ i, ∑' k : O, c k * d (-k) * g i k = ∑' k : O, c k * d (-k) * ∑ i, g i k := by
  rw [← Summable.tsum_finsetSum (fun i _ => summable_mul_neg_bdd hc hd _ M (hg i))]
  refine tsum_congr fun k => ?_
  rw [Finset.mul_sum]

theorem norm_chi_traceChar_le (a r : P.Res) : ‖P.chi a * P.traceChar r‖ ≤ 1 := by
  rw [norm_mul, P.norm_traceChar, mul_one]
  exact P.norm_chi_le _

theorem norm_sum_chi_traceChar_le (f g : P.Res → P.Res) :
    ‖∑ t : P.Res, P.chi (f t) * P.traceChar (g t)‖ ≤ Fintype.card P.Res := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ t : P.Res, ‖P.chi (f t) * P.traceChar (g t)‖ ≤ ∑ _t : P.Res, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ => P.norm_chi_traceChar_le _ _
    _ = Fintype.card P.Res := by simp

/-- **The middle cusps.** Σ_{x ≢ 0} ∫_P G(L_{qx}w) = |P| Σ_k b(k)b(−k)(N − J + (J − 1)N[q ∣ k]); the high points
cancel. -/
theorem integral_middle_sum (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∑ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
        P.fracSum sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (P.normC - P.fracJacobi + (P.fracJacobi - 1) * (if P.p ∣ k then P.normC else 0)) := by
  set b := rationalSourceModeAmplitude v with hbdef
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have h9 := P.nine_ne_zero'
  have hsplit : ∀ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
      P.fracSum sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      ∑ t : P.Res, ∫ z in periodDomain, P.fracCorrelation sourceTheta (P.lift t)
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) := fun x => by
    unfold fracSum
    exact integral_finsetSum _ (fun t _ => integrableOn_periodDomain_of_continuous _
      ((P.continuous_fracCorrelation_source _).comp
        ((continuous_hyperbolic_action (complexMatrix (lowerThree (P.p * P.lift x.1)))).comp
          (continuous_upperPoint_z v hv))))
  simp_rw [hsplit, P.integral_fracCorrelation_middle h2 _ _ v hv, Finset.sum_add_distrib]
  simp only [← hbdef]
  have hhigh : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res,
      (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * P.highTerm v else 0) = 0 := by
    set c0 : ℂ := ∑ s : P.Res, if 1 + s = 0 ∨ 1 - s = 0 then (1 : ℂ) else 0
    have hK : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res,
        (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * P.highTerm v else 0) =
        P.chi 2 * P.highTerm v * c0 * (P.chi (3 * x.1))⁻¹ := by
      intro x
      have hbij := (mulRight_bijective₀ (9 * x.1) (mul_ne_zero h9 x.2)).sum_comp
        (fun s => if 1 + s = 0 ∨ 1 - s = 0 then (1 : ℂ) else 0)
      rw [show P.chi 2 * P.highTerm v * c0 * (P.chi (3 * x.1))⁻¹ =
          P.chi 2 * (P.chi (3 * x.1))⁻¹ * P.highTerm v * c0 by ring,
        show c0 = ∑ i : P.Res, (if 1 + i * (9 * x.1) = 0 ∨ 1 - i * (9 * x.1) = 0 then (1 : ℂ) else 0) from hbij.symm,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [show t * (9 * x.1) = 9 * t * x.1 by ring]
      split_ifs <;> ring
    simp_rw [hK]
    rw [← Finset.mul_sum, P.sum_chi_three_inv, mul_zero]
  rw [hhigh, zero_add]
  have hgen : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.chi (1 - (9 * t * x.1) ^ 2) *
      (periodArea * ∑' k : O, b k * b (-k) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k)) =
      periodArea * ∑' k : O, b k * b (-k) * ∑ t : P.Res, P.chi (1 - (9 * t * x.1) ^ 2) *
        P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k) := by
    intro x
    rw [← sum_tsum_swap b b hb hb _ 1 (fun t k => P.norm_chi_traceChar_le _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (∑' k : O, b k * b (-k) * (P.chi (1 - (9 * t * x.1) ^ 2) *
        P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k))) = P.chi (1 - (9 * t * x.1) ^ 2) *
        ∑' k : O, b k * b (-k) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k) by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => by ring]
    ring
  simp_rw [hgen]
  rw [← Finset.mul_sum, sum_tsum_swap b b hb hb _ _ (fun x k => P.norm_sum_chi_traceChar_le _ _)]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  rw [P.jacobi_double_sum h2 (P.res k), if_congr (P.res_eq_zero_iff k) rfl rfl]

/-- **The cusp 0.** Σ_{s ∈ O/q²} ∫_P G(ST(3s)w) = N²|P| Σ_k b(k)b(−k)
+ N²|P| χ(−4)χ(9)⁻¹ Σ_k b(v/N, k)b(v/N, −k) g_χ(k). -/
theorem integral_cuspZero_sum (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∑ s : P.Res × P.Res, ∫ z in periodDomain, P.fracSum sourceTheta
        (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * (periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k)) +
        P.normC ^ 2 * (periodArea * (P.chi (-4) * (P.chi 9)⁻¹ *
          ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) *
              ∑ u : P.Res, P.chi u * P.traceChar (u * P.res k))) := by
  have hn := P.norm_pos
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv hn
  set b := rationalSourceModeAmplitude v with hbdef
  set b₂ := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hb₂ : Summable (fun h => ‖b₂ h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv1 hn)
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  set g : {x : P.Res // x ≠ 0} → O → ℂ := fun x =>
    cuspConv (P.shiftedLow (v / ‖ringComplex P.p‖) (-P.lowBeta (P.lift x.1) - -P.lowBeta (-P.lift x.1))) b₂
  have hg : ∀ x, Summable (fun h => ‖g x h‖) := fun x => summable_cuspConv (P.summable_shiftedLow _ hv1 _) hb₂
  have hg2 : ∀ x, Summable (fun m => ‖g x (m * P.p * P.p)‖) := fun x =>
    ((hg x).comp_injective hinj).comp_injective hinj
  have hpt : ∀ z, ∑ s : P.Res × P.Res, P.fracSum sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * (cuspCharacterSeries b (z + 0) * cuspCharacterSeries b (z + 0)) +
        ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 *
          cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z) := by
    intro z
    rw [P.sum_fracSum_cuspZero sourceTheta sourceTheta_automorphy sourceTheta_rational_inv, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, P.sum_lowLow]
    rw [sourceTheta, cubicSourceResidualFunction_fourier_expansion, add_zero, ← hbdef]
    ring
  have hcont : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.fracSum sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s =>
    P.continuous_fracSum_source.comp ((continuous_hyperbolic_action _).comp
      ((continuous_hyperbolic_action _).comp (continuous_upperPoint_z v hv)))
  rw [← integral_finsetSum _ (fun s _ => integrableOn_periodDomain_of_continuous _ (hcont s))]
  simp_rw [hpt]
  have hc1 : Continuous (fun z : ℂ => P.normC ^ 2 * (cuspCharacterSeries b (z + 0) * cuspCharacterSeries b (z + 0))) :=
    continuous_const.mul (((cuspCharacterSeries_continuous b hb).comp (continuous_id.add continuous_const)).mul
      ((cuspCharacterSeries_continuous b hb).comp (continuous_id.add continuous_const)))
  have hc2 : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 *
      cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z)) := fun x =>
    continuous_const.mul (continuous_const.mul (cuspCharacterSeries_continuous _ (hg2 x)))
  rw [integral_add (integrableOn_periodDomain_of_continuous _ hc1)
      (integrable_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hc2 x)),
    integral_const_mul, integral_translate_mul b b hb hb,
    integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hc2 x)]
  have hI : ∀ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain, P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 *
      cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z) = P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 * (periodArea * g x 0)) := by
    intro x
    rw [integral_const_mul, integral_const_mul, PrimaryPrime.integral_cuspCharacterSeries _ (hg2 x), zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun x _ => hI x]
  have hph : ∀ k : O, tracePhase (cuspFrequency k * (0 - 0)) = 1 := by
    intro k
    rw [sub_zero, mul_zero, AddChar.map_zero_eq_one]
  simp_rw [hph, mul_one]
  congr 1
  have hg0 : ∀ x : {x : P.Res // x ≠ 0}, g x 0 = ∑' k : O, b₂ k * b₂ (-k) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k) := by
    intro x
    have hx : ¬ P.p ∣ P.lift x.1 := P.not_dvd_lift x
    have hx' : ¬ P.p ∣ -P.lift x.1 := fun h => hx (dvd_neg.mp h)
    simp only [g, cuspConv, zero_sub, shiftedLow]
    refine tsum_congr fun k => ?_
    have hβ : P.res (-(-P.lowBeta (P.lift x.1) - -P.lowBeta (-P.lift x.1))) = -2 * (9 * x.1)⁻¹ := by
      have h1 := P.res_neg_lowBeta (-P.lift x.1) hx'
      have h2' := P.res_neg_lowBeta (P.lift x.1) hx
      simp only [map_neg, res_lift] at h1 h2'
      simp only [map_neg, map_sub, neg_sub]
      rw [show P.res (P.lowBeta (P.lift x.1)) = -(9 * x.1)⁻¹ by rw [← h2', neg_neg],
        show P.res (P.lowBeta (-P.lift x.1)) = -(9 * -x.1)⁻¹ by rw [← h1, neg_neg], mul_neg, inv_neg]
      ring
    rw [P.phase_eq_psi, P.psi_eq_traceChar, hβ]
    ring
  simp_rw [hg0]
  have hsw : ∑ x : {x : P.Res // x ≠ 0}, P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 * (periodArea *
      ∑' k : O, b₂ k * b₂ (-k) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k))) =
      P.normC ^ 2 * (periodArea * ∑ x : {x : P.Res // x ≠ 0},
        ∑' k : O, b₂ k * b₂ (-k) * (P.chi (-9 * x.1 ^ 2) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (∑' k : O, b₂ k * b₂ (-k) * (P.chi (-9 * x.1 ^ 2) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k))) =
        P.chi (-9 * x.1 ^ 2) * ∑' k : O, b₂ k * b₂ (-k) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k) by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      ring]
    ring
  rw [hsw, sum_tsum_swap b₂ b₂ hb₂ hb₂ _ 1 (fun x k => P.norm_chi_traceChar_le _ _)]
  congr 2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [P.gauss_low_sum h2 (P.res k)]
  ring

/-- The weight of the cusp series of θ_s²: N² + N − J + NJ[q ∣ k]. -/
def fracWeight (k : O) : ℂ :=
  P.normC ^ 2 + P.normC - P.fracJacobi + if P.p ∣ k then P.normC * P.fracJacobi else 0

/-- **The constant term of the fractional trace.** -/
theorem integral_sourceFracTrace (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.sourceFracTrace (upperPoint z v hv) =
      periodArea * (∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) * P.fracWeight k +
        P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹) *
          ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) *
              ∑ u : P.Res, P.chi u * P.traceChar (u * P.res k)) := by
  set b := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hu := continuous_upperPoint_z v hv
  have e : ∀ z, P.sourceFracTrace (upperPoint z v hv) = P.fracSum sourceTheta (upperPoint z v hv) +
      (∑ x : {x : P.Res // x ≠ 0}, P.fracSum sourceTheta
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) +
        ∑ s : P.Res × P.Res, P.fracSum sourceTheta
          (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun z =>
    P.fracTrace_eq sourceTheta sourceTheta_automorphy sourceTheta_rational_inv _
  simp_rw [e]
  have hA : Continuous (fun z : ℂ => P.fracSum sourceTheta (upperPoint z v hv)) := P.continuous_fracSum_source.comp hu
  have hB : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.fracSum sourceTheta
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := fun x =>
    P.continuous_fracSum_source.comp ((continuous_hyperbolic_action _).comp hu)
  have hC : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.fracSum sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s =>
    P.continuous_fracSum_source.comp ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp hu))
  have hBs : Continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0}, P.fracSum sourceTheta
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := continuous_finsetSum _ fun x _ => hB x
  have hCs : Continuous (fun z : ℂ => ∑ s : P.Res × P.Res, P.fracSum sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) :=
    continuous_finsetSum _ fun s _ => hC s
  rw [integral_add (integrableOn_periodDomain_of_continuous _ hA)
      (integrableOn_periodDomain_of_continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0}, P.fracSum sourceTheta
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) + ∑ s : P.Res × P.Res, P.fracSum sourceTheta
          (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) (hBs.add hCs)),
    integral_add (integrableOn_periodDomain_of_continuous _ hBs) (integrableOn_periodDomain_of_continuous _ hCs),
    integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hB x),
    integral_finsetSum _ fun s _ => integrableOn_periodDomain_of_continuous _ (hC s),
    P.integral_fracSum_source h2 v hv, P.integral_middle_sum h2 v hv, P.integral_cuspZero_sum h2 v hv]
  have hφ₁ : ∀ k : O, ‖(if P.p ∣ k then P.normC else 0)‖ ≤ ‖P.normC‖ := by
    intro k
    split_ifs <;> simp
  have hφ₂ : ∀ k : O, ‖P.normC - P.fracJacobi + (P.fracJacobi - 1) * (if P.p ∣ k then P.normC else 0)‖ ≤
      ‖P.normC - P.fracJacobi‖ + ‖P.fracJacobi - 1‖ * ‖P.normC‖ := by
    intro k
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hφ₁ k) (norm_nonneg _)
  have s₁ := summable_mul_neg_bdd hb hb _ _ hφ₁
  have s₂ := summable_mul_neg_bdd hb hb _ _ hφ₂
  have s₃ : Summable (fun k => P.normC ^ 2 * (b k * b (-k))) := by
    have := summable_mul_neg_bdd hb hb (fun _ => (1 : ℂ)) 1 (fun _ => by simp)
    simpa using this.mul_left (P.normC ^ 2)
  have hsum : (∑' k : O, b k * b (-k) * (if P.p ∣ k then P.normC else 0)) +
      (∑' k : O, b k * b (-k) * (P.normC - P.fracJacobi + (P.fracJacobi - 1) * (if P.p ∣ k then P.normC else 0))) +
      P.normC ^ 2 * ∑' k : O, b k * b (-k) = ∑' k : O, b k * b (-k) * P.fracWeight k := by
    rw [← s₁.tsum_add s₂, ← tsum_mul_left, ← (s₁.add s₂).tsum_add s₃]
    refine tsum_congr fun k => ?_
    simp only [fracWeight]
    split_ifs <;> ring
  linear_combination periodArea * hsum

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
