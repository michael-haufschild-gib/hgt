import GaloisForLFunctions.OrderSixMetaplecticTheory.TheQuadraticWeightOfTheFractionalTraceSumsToSexticGaussSums

/-!
# The constant term of the quadratic fractional trace reads the sextic twist

For the quadratic character λ = λ_q (q odd) the trace Tr G_λ of G_λ(w) = Σ_t λ(t)θ(T_tw)θ(T_{−t}w) has constant term
(`integral_sourceFracTraceW`)

∫_P Tr G_λ(z + vj) = |P| (g_λJ₆ Σ_k b(k)b(−k)λ(2k) + N²χ(−4)χ(9)⁻¹λ(−2) Σ_k b₂(k)b₂(−k) g_{χλ}(k)),

b = b_v, b₂ = b_{v/N}, J₆ = Σ_s(χλ)(1 − s²), g_{χλ}(k) = Σ_u(χλ)(u)ψ(uk). The cusp ∞ and the middle cusps read the
quadratic twist of θ² (weights g_λλ(2k) and g_λλ(2k)(J₆ − 1)); the cusp 0 reads the sextic Gauss sums. There is no
θ² term: λ(0) = 0, and the high pairs of the middle cusps cancel against λ.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

open MeasureTheory

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover
  MetaplecticMobiusDescent.CubicEisenstein.RationalSource

namespace PrimaryPrime

variable (P : PrimaryPrime)

/-- **Weighted Parseval for translates.** -/
theorem integral_wsum_translate_mul {ι : Type*} [Fintype ι] (c d : O → ℂ) (hc : Summable (fun h => ‖c h‖))
    (hd : Summable (fun h => ‖d h‖)) (φ α β : ι → ℂ) :
    ∫ z in periodDomain, ∑ i, φ i * (cuspCharacterSeries c (z + α i) * cuspCharacterSeries d (z + β i)) =
      periodArea * ∑' k : O, c k * d (-k) * ∑ i, φ i * tracePhase (cuspFrequency k * (α i - β i)) := by
  have hcont : ∀ i, Continuous (fun z : ℂ =>
      φ i * (cuspCharacterSeries c (z + α i) * cuspCharacterSeries d (z + β i))) :=
    fun i => continuous_const.mul (((cuspCharacterSeries_continuous c hc).comp (continuous_id.add continuous_const)).mul
      ((cuspCharacterSeries_continuous d hd).comp (continuous_id.add continuous_const)))
  have hbd : ∀ i k, ‖φ i * tracePhase (cuspFrequency k * (α i - β i))‖ ≤ ∑ j, ‖φ j‖ := by
    intro i k
    rw [norm_mul, tracePhase_norm, mul_one]
    exact Finset.single_le_sum (f := fun j => ‖φ j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  rw [integral_finsetSum _ (fun i _ => integrableOn_periodDomain_of_continuous _ (hcont i))]
  simp_rw [integral_const_mul, integral_translate_mul c d hc hd]
  rw [← sum_tsum_swap c d hc hd (fun i k => φ i * tracePhase (cuspFrequency k * (α i - β i))) _ hbd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  exact tsum_congr fun k => by ring

theorem norm_lam_le (x : P.Res) : ‖P.lam x‖ ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, MulChar.map_zero, norm_zero]
    exact zero_le_one
  · have h : ‖P.lam x‖ ^ 2 = 1 := by rw [← norm_pow, P.lam_sq x hx, norm_one]
    have h0 : 0 ≤ ‖P.lam x‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖P.lam x‖ - 1)]

theorem norm_lam_chi_traceChar_le (t a r : P.Res) : ‖P.lam t * (P.chi a * P.traceChar r)‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ (P.norm_lam_le t) (norm_nonneg _) (P.norm_chi_traceChar_le a r)

theorem norm_sum_lam_chi_traceChar_le (f g : P.Res → P.Res) :
    ‖∑ t : P.Res, P.lam t * (P.chi (f t) * P.traceChar (g t))‖ ≤ Fintype.card P.Res := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ t : P.Res, ‖P.lam t * (P.chi (f t) * P.traceChar (g t))‖ ≤ ∑ _t : P.Res, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ => P.norm_lam_chi_traceChar_le _ _ _
    _ = Fintype.card P.Res := by simp

/-- The λ-weighted fractional trace of the projected theta function. -/
abbrev sourceFracTraceW : HyperbolicSpace → ℂ := P.fracTraceW P.lam sourceTheta

theorem continuous_fracSumW_source : Continuous (P.fracSumW P.lam sourceTheta) := by
  unfold fracSumW
  exact continuous_finsetSum _ fun t _ => continuous_const.mul (P.continuous_fracCorrelation_source _)

/-- **The cusp ∞.** ∫_P G_λ = |P| Σ_k b(k)b(−k) g_λλ(2k). -/
theorem integral_fracSumW_source (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.fracSumW P.lam sourceTheta (upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (P.lam (2 * P.res k) * gaussSum P.lam P.traceChar) := by
  set b := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have e : ∀ z, P.fracSumW P.lam sourceTheta (upperPoint z v hv) = ∑ x : P.Res, P.lam x *
      (cuspCharacterSeries b (z + 3 * ringComplex (P.lift x) / ringComplex P.p) *
        cuspCharacterSeries b (z + 3 * ringComplex (-P.lift x) / ringComplex P.p)) := by
    intro z
    unfold fracSumW fracCorrelation
    simp_rw [P.sourceTheta_fracShift]
    rfl
  simp_rw [e]
  rw [integral_wsum_translate_mul b b hb hb]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  have hsum : ∑ x : P.Res, P.lam x * tracePhase (cuspFrequency k * (3 * ringComplex (P.lift x) / ringComplex P.p -
      3 * ringComplex (-P.lift x) / ringComplex P.p)) = ∑ x : P.Res, P.lam x * P.traceChar (x * (2 * P.res k)) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show 3 * ringComplex (P.lift x) / ringComplex P.p - 3 * ringComplex (-P.lift x) / ringComplex P.p =
        3 * ringComplex (2 * P.lift x) / ringComplex P.p by rw [map_neg, map_mul, map_ofNat]; ring,
      P.tracePhase_low, show P.res (2 * P.lift x) = 2 * x by rw [map_mul, res_lift, map_ofNat]]
    congr 2
    ring
  rw [hsum, P.sum_lam_traceChar h2]

/-- **The middle cusps.** Σ_{x ≢ 0} ∫_P G_λ(L_{qx}w) = |P| Σ_k b(k)b(−k) g_λλ(2k)(J₆ − 1); the high pairs cancel. -/
theorem integral_middle_sumW (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∑ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
        P.fracSumW P.lam sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      periodArea * ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) *
        (gaussSum P.lam P.traceChar * P.lam (2 * P.res k) * (P.lamJacobi - 1)) := by
  set b := rationalSourceModeAmplitude v with hbdef
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hsplit : ∀ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain,
      P.fracSumW P.lam sourceTheta (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) =
      ∑ t : P.Res, P.lam t * ∫ z in periodDomain, P.fracCorrelation sourceTheta (P.lift t)
        (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) := fun x => by
    unfold fracSumW
    rw [integral_finsetSum _ (fun t _ => integrableOn_periodDomain_of_continuous _
      (continuous_const.mul ((P.continuous_fracCorrelation_source _).comp
        ((continuous_hyperbolic_action (complexMatrix (lowerThree (P.p * P.lift x.1)))).comp
          (continuous_upperPoint_z v hv)))))]
    simp_rw [integral_const_mul]
  simp_rw [hsplit, P.integral_fracCorrelation_middle h2 _ _ v hv, mul_add, Finset.sum_add_distrib]
  simp only [← hbdef]
  have hhigh : ∑ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t *
      (if 1 + 9 * t * x.1 = 0 ∨ 1 - 9 * t * x.1 = 0 then P.chi 2 * (P.chi (3 * x.1))⁻¹ * P.highTerm v else 0) = 0 := by
    rw [← P.sum_lam_middleMain h2 (P.highTerm v) 0]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
    congr 1
    unfold middleMain
    by_cases h₁ : 1 + 9 * t * x.1 = 0
    · rw [if_pos (Or.inl h₁), if_pos h₁]
    · by_cases h₂ : 1 - 9 * t * x.1 = 0
      · rw [if_pos (Or.inr h₂), if_neg h₁, if_pos h₂]
      · rw [if_neg (not_or.mpr ⟨h₁, h₂⟩), if_neg h₁, if_neg h₂, mul_zero]
  rw [hhigh, zero_add]
  have hgen : ∀ x : {x : P.Res // x ≠ 0}, ∑ t : P.Res, P.lam t * (P.chi (1 - (9 * t * x.1) ^ 2) *
      (periodArea * ∑' k : O, b k * b (-k) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k))) =
      periodArea * ∑' k : O, b k * b (-k) * ∑ t : P.Res, P.lam t * (P.chi (1 - (9 * t * x.1) ^ 2) *
        P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k)) := by
    intro x
    rw [← sum_tsum_swap b b hb hb _ 1 (fun t k => P.norm_lam_chi_traceChar_le _ _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show (∑' k : O, b k * b (-k) * (P.lam t * (P.chi (1 - (9 * t * x.1) ^ 2) *
        P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k)))) = P.lam t * P.chi (1 - (9 * t * x.1) ^ 2) *
        ∑' k : O, b k * b (-k) * P.traceChar (2 * t / (1 - (9 * t * x.1) ^ 2) * P.res k) by
      rw [← tsum_mul_left]
      exact tsum_congr fun k => by ring]
    ring
  simp_rw [hgen]
  rw [← Finset.mul_sum, sum_tsum_swap b b hb hb _ _ (fun x k => P.norm_sum_lam_chi_traceChar_le _ _)]
  congr 1
  refine tsum_congr fun k => ?_
  congr 1
  rw [P.jacobi_double_sum_lam h2 (P.res k)]

/-- **The cusp 0.** Σ_{s ∈ O/q²} ∫_P G_λ(ST(3s)w) = N²|P|χ(−4)χ(9)⁻¹λ(−2) Σ_k b₂(k)b₂(−k) g_{χλ}(k). -/
theorem integral_cuspZero_sumW (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∑ s : P.Res × P.Res, ∫ z in periodDomain, P.fracSumW P.lam sourceTheta
        (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      P.normC ^ 2 * (periodArea * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2) *
        ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
          rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) *
            ∑ u : P.Res, P.chi u * P.lam u * P.traceChar (u * P.res k))) := by
  have hn := P.norm_pos
  have hv1 : 0 < v / ‖ringComplex P.p‖ := div_pos hv hn
  set b₂ := rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖)
  have hb₂ : Summable (fun h => ‖b₂ h‖) := rationalSourceModeAmplitude_summable _ (div_pos hv1 hn)
  have hinj : Function.Injective (fun m : O => m * P.p) := fun x y h => mul_right_cancel₀ P.ne_zero h
  set g : {x : P.Res // x ≠ 0} → O → ℂ := fun x =>
    cuspConv (P.shiftedLow (v / ‖ringComplex P.p‖) (-P.lowBeta (P.lift x.1) - -P.lowBeta (-P.lift x.1))) b₂
  have hg : ∀ x, Summable (fun h => ‖g x h‖) := fun x => summable_cuspConv (P.summable_shiftedLow _ hv1 _) hb₂
  have hg2 : ∀ x, Summable (fun m => ‖g x (m * P.p * P.p)‖) := fun x =>
    ((hg x).comp_injective hinj).comp_injective hinj
  have hpt : ∀ z, ∑ s : P.Res × P.Res, P.fracSumW P.lam sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv) =
      ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 *
        cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z)) := by
    intro z
    simp_rw [P.fracSumW_sO sourceTheta sourceTheta_automorphy sourceTheta_rational_inv, MulChar.map_zero, zero_mul,
      zero_add]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, P.sum_lowLow]
  have hcont : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.fracSumW P.lam sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s =>
    P.continuous_fracSumW_source.comp ((continuous_hyperbolic_action _).comp
      ((continuous_hyperbolic_action _).comp (continuous_upperPoint_z v hv)))
  have hc2 : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.lam x.1 * (P.chi (-9 * x.1 ^ 2) *
      (P.normC ^ 2 * cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z))) := fun x =>
    continuous_const.mul (continuous_const.mul (continuous_const.mul (cuspCharacterSeries_continuous _ (hg2 x))))
  rw [← integral_finsetSum _ (fun s _ => integrableOn_periodDomain_of_continuous _ (hcont s))]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hc2 x)]
  have hI : ∀ x : {x : P.Res // x ≠ 0}, ∫ z in periodDomain, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) *
      (P.normC ^ 2 * cuspCharacterSeries (fun m => g x (m * P.p * P.p)) z)) =
      P.lam x.1 * (P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 * (periodArea * g x 0))) := by
    intro x
    rw [integral_const_mul, integral_const_mul, integral_const_mul,
      PrimaryPrime.integral_cuspCharacterSeries _ (hg2 x), zero_mul, zero_mul]
  rw [Finset.sum_congr rfl fun x _ => hI x]
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
  have hsw : ∑ x : {x : P.Res // x ≠ 0}, P.lam x.1 * (P.chi (-9 * x.1 ^ 2) * (P.normC ^ 2 * (periodArea *
      ∑' k : O, b₂ k * b₂ (-k) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k)))) =
      P.normC ^ 2 * (periodArea * ∑ x : {x : P.Res // x ≠ 0},
        ∑' k : O, b₂ k * b₂ (-k) * (P.lam x.1 * (P.chi (-9 * x.1 ^ 2) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k)))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show (∑' k : O, b₂ k * b₂ (-k) * (P.lam x.1 * (P.chi (-9 * x.1 ^ 2) *
        P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k)))) = P.lam x.1 * P.chi (-9 * x.1 ^ 2) *
        ∑' k : O, b₂ k * b₂ (-k) * P.traceChar (-2 * (9 * x.1)⁻¹ * P.res k) by
      rw [← tsum_mul_left]
      refine tsum_congr fun k => ?_
      ring]
    ring
  rw [hsw, sum_tsum_swap b₂ b₂ hb₂ hb₂ _ 1 (fun x k => P.norm_lam_chi_traceChar_le _ _ _)]
  congr 2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [P.gauss_low_sum_lam h2 (P.res k)]
  simp only [mul_assoc]
  ring

/-- The sextic Gauss sum g_{χλ}(h) = Σ_u (χλ)(u)ψ(uh). -/
def sexticGaussAt (h : O) : ℂ := ∑ u : P.Res, P.chi u * P.lam u * P.traceChar (u * P.res h)

/-- **The constant term of the quadratic fractional trace.** -/
theorem integral_sourceFracTraceW (h2 : (2 : P.Res) ≠ 0) (v : ℝ) (hv : 0 < v) :
    ∫ z in periodDomain, P.sourceFracTraceW (upperPoint z v hv) =
      periodArea * (gaussSum P.lam P.traceChar * P.lamJacobi *
          ∑' k : O, rationalSourceModeAmplitude v k * rationalSourceModeAmplitude v (-k) * P.lam (2 * P.res k) +
        P.normC ^ 2 * (P.chi (-4) * (P.chi 9)⁻¹ * P.lam (-2)) *
          ∑' k : O, rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) k *
            rationalSourceModeAmplitude (v / ‖ringComplex P.p‖ / ‖ringComplex P.p‖) (-k) * P.sexticGaussAt k) := by
  set b := rationalSourceModeAmplitude v
  have hb : Summable (fun h => ‖b h‖) := rationalSourceModeAmplitude_summable v hv
  have hu := continuous_upperPoint_z v hv
  have e : ∀ z, P.sourceFracTraceW (upperPoint z v hv) = P.fracSumW P.lam sourceTheta (upperPoint z v hv) +
      (∑ x : {x : P.Res // x ≠ 0}, P.fracSumW P.lam sourceTheta
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) +
        ∑ s : P.Res × P.Res, P.fracSumW P.lam sourceTheta
          (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun z =>
    P.fracTraceW_eq sourceTheta sourceTheta_automorphy sourceTheta_rational_inv _ P.lam_squareInvariant _
  simp_rw [e]
  have hA : Continuous (fun z : ℂ => P.fracSumW P.lam sourceTheta (upperPoint z v hv)) :=
    P.continuous_fracSumW_source.comp hu
  have hB : ∀ x : {x : P.Res // x ≠ 0}, Continuous (fun z : ℂ => P.fracSumW P.lam sourceTheta
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := fun x =>
    P.continuous_fracSumW_source.comp ((continuous_hyperbolic_action _).comp hu)
  have hC : ∀ s : P.Res × P.Res, Continuous (fun z : ℂ => P.fracSumW P.lam sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) := fun s =>
    P.continuous_fracSumW_source.comp ((continuous_hyperbolic_action _).comp ((continuous_hyperbolic_action _).comp hu))
  have hBs : Continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0}, P.fracSumW P.lam sourceTheta
      (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv)) := continuous_finsetSum _ fun x _ => hB x
  have hCs : Continuous (fun z : ℂ => ∑ s : P.Res × P.Res, P.fracSumW P.lam sourceTheta
      (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) :=
    continuous_finsetSum _ fun s _ => hC s
  rw [integral_add (integrableOn_periodDomain_of_continuous _ hA)
      (integrableOn_periodDomain_of_continuous (fun z : ℂ => ∑ x : {x : P.Res // x ≠ 0}, P.fracSumW P.lam sourceTheta
          (complexMatrix (lowerThree (P.p * P.lift x.1)) • upperPoint z v hv) + ∑ s : P.Res × P.Res,
          P.fracSumW P.lam sourceTheta
          (integralComplexMatrix sO • complexMatrix (transThree (P.sqLift s)) • upperPoint z v hv)) (hBs.add hCs)),
    integral_add (integrableOn_periodDomain_of_continuous _ hBs) (integrableOn_periodDomain_of_continuous _ hCs),
    integral_finsetSum _ fun x _ => integrableOn_periodDomain_of_continuous _ (hB x),
    integral_finsetSum _ fun s _ => integrableOn_periodDomain_of_continuous _ (hC s),
    P.integral_fracSumW_source h2 v hv, P.integral_middle_sumW h2 v hv, P.integral_cuspZero_sumW h2 v hv]
  have hφ : ∀ k : O, ‖P.lam (2 * P.res k)‖ ≤ 1 := fun k => P.norm_lam_le _
  have s₀ := summable_mul_neg_bdd hb hb _ _ hφ
  have s₁ := s₀.mul_right (gaussSum P.lam P.traceChar)
  have s₂ := s₀.mul_right (gaussSum P.lam P.traceChar * (P.lamJacobi - 1))
  have hsum : (∑' k : O, b k * b (-k) * (P.lam (2 * P.res k) * gaussSum P.lam P.traceChar)) +
      (∑' k : O, b k * b (-k) * (gaussSum P.lam P.traceChar * P.lam (2 * P.res k) * (P.lamJacobi - 1))) =
      gaussSum P.lam P.traceChar * P.lamJacobi * ∑' k : O, b k * b (-k) * P.lam (2 * P.res k) := by
    have e1 : (∑' k : O, b k * b (-k) * (P.lam (2 * P.res k) * gaussSum P.lam P.traceChar)) =
        ∑' k : O, b k * b (-k) * P.lam (2 * P.res k) * gaussSum P.lam P.traceChar :=
      tsum_congr fun k => by ring
    have e2 : (∑' k : O, b k * b (-k) * (gaussSum P.lam P.traceChar * P.lam (2 * P.res k) * (P.lamJacobi - 1))) =
        ∑' k : O, b k * b (-k) * P.lam (2 * P.res k) * (gaussSum P.lam P.traceChar * (P.lamJacobi - 1)) :=
      tsum_congr fun k => by ring
    rw [e1, e2, ← s₁.tsum_add s₂, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  unfold sexticGaussAt
  linear_combination periodArea * hsum

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
