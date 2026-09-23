import GaloisForLFunctions.RHTower.InfiniteMobiusCausalShift
import GaloisForLFunctions.RHTower.MobiusCriticalClockMoments
import GaloisForLFunctions.RHTower.VectorSignedChannelCoisometry

/-!
# The coupled floor--Möbius feature and its exact norm

`mobius-signed-channel-coisometry-incidence-law.md`, equations `(11)`--`(17)` and `(20)`--`(23)`.

For a causal vector `k` of `L²(R)` (the normalized floor remainder of the card) and the truncated
constant boundary mode `(I - P_d) 1 = 1_{[0, log d)}`, the coupled feature at the divisor channel `d`
is

```text
B_{omega,d} = V_{log d} k - c_omega (I - P_d) 1 .
```

Its two terms have disjoint supports, so

```text
||B_{omega,d}||^(2 : ℕ) = ||k||^(2 : ℕ) + c_omega^(2 : ℕ) log d ,                              (15)
||Y_omega||^(2 : ℕ)     = ||k||^(2 : ℕ) + c_omega^(2 : ℕ) E_{P_omega}[log d] ,                 (17)
```

and the exact logarithmic moment is the squarefree fixed current
`-zeta'/zeta(sigma) + 2 zeta'/zeta(2 sigma)`, already formalized as
`squarefreeMobiusLogMoment 1`.

Feeding `Y_omega` through the signed coisometry recovers the coupled error and gives the exact
cancellation law `(23)`.
-/

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

noncomputable section
namespace RHTower

/-! ### The truncated constant boundary mode -/

private theorem volume_Ico_ne_top (a : ℝ) : (volume (Ico (0 : ℝ) a)) ≠ ⊤ := by
  rw [Real.volume_Ico]
  exact ENNReal.ofReal_ne_top

/-- Card `(13)`: the truncated constant boundary mode `(I - P_d) 1 = 1_{[0, a)}`. -/
def truncatedConstant (a : ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 measurableSet_Ico (volume_Ico_ne_top a) (1 : ℂ)

theorem norm_truncatedConstant_sq {a : ℝ} (ha : 0 ≤ a) :
    ‖truncatedConstant a‖ ^ 2 = a := by
  have hnorm : ‖truncatedConstant a‖ =
      ‖(1 : ℂ)‖ * (volume.real (Ico (0 : ℝ) a)) ^ (1 / (2 : ℝ≥0∞).toReal) :=
    norm_indicatorConstLp (by norm_num) (by norm_num)
  have hmeas : volume.real (Ico (0 : ℝ) a) = a := by
    rw [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hnorm, hmeas, norm_one, one_mul, show (1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) by norm_num]
  rw [← Real.rpow_natCast (a ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul ha]
  norm_num

/-- The truncated constant vanishes above its cutoff. -/
theorem truncatedConstant_ae_eq_zero_of_le {a : ℝ} :
    ∀ᵐ t : ℝ, a ≤ t → (truncatedConstant a) t = 0 := by
  filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := (volume : Measure ℝ))
    (hs := measurableSet_Ico (a := (0 : ℝ)) (b := a)) (hμs := volume_Ico_ne_top a)
    (c := (1 : ℂ))] with t ht hta
  rw [truncatedConstant] at *
  rw [ht, Set.indicator_of_notMem (by simp; intro _; exact hta)]

/-! ### The coupled feature at one divisor channel -/

/-- Card `(13)`: the coupled floor--tail feature at the divisor channel `d`. -/
def coupledFeature (omega : ℝ) (k : Lp ℂ 2 (volume : Measure ℝ)) (d : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  MellinL2.additiveTranslationUnitary (-Real.log d) k -
    ((1 / (1 + omega) : ℝ) : ℂ) • truncatedConstant (Real.log d)

/-- The right shift of a causal vector has lower support at the shift. -/
theorem additiveTranslationUnitary_hasAELowerSupport_shift
    {h : ℝ} (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : HasAELowerSupport (fun t : ℝ => f t) 0) :
    HasAELowerSupport
      (fun t : ℝ => MellinL2.additiveTranslationUnitary (-h) f t) h := by
  have hcoe := Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving (-h))
  have htrans :
      (fun t : ℝ => MellinL2.additiveTranslationUnitary (-h) f t) =ᵐ[volume]
        fun t : ℝ => f (t - h) := by
    simpa [MellinL2.additiveTranslationUnitary,
      MellinL2.lpCompMeasurePreservingEquiv, Function.comp_apply,
      MellinL2.realTranslationEquiv] using! hcoe
  have hfshift :=
    (MellinL2.realTranslation_measurePreserving (-h)).quasiMeasurePreserving.ae hf
  filter_upwards [htrans, hfshift] with t ht hsupp
  intro ht0
  rw [ht]
  have hsupp' : t - h < 0 → f (t - h) = 0 := by
    simpa [MellinL2.realTranslationEquiv] using! hsupp
  exact hsupp' (by linarith)

/-- The two components of the coupled feature are orthogonal. -/
theorem inner_shift_truncatedConstant_eq_zero
    (a : ℝ) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    inner ℂ (MellinL2.additiveTranslationUnitary (-a) k) (truncatedConstant a) = 0 := by
  rw [L2.inner_def]
  have hshift := additiveTranslationUnitary_hasAELowerSupport_shift (h := a) k hk
  have htrunc := truncatedConstant_ae_eq_zero_of_le (a := a)
  have hzero : ∀ᵐ t : ℝ,
      inner ℂ ((MellinL2.additiveTranslationUnitary (-a) k) t) ((truncatedConstant a) t)
        = (0 : ℂ) := by
    filter_upwards [hshift, htrunc] with t hs htz
    rcases lt_or_ge t a with h | h
    · rw [hs (by linarith)]
      simp
    · rw [htz h]
      simp
  rw [integral_congr_ae hzero, integral_zero]

/-- **Card `(15)`.**  Exact norm of the coupled feature at one divisor channel. -/
theorem norm_coupledFeature_sq
    {omega : ℝ} (d : ℕ) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ‖coupledFeature omega k d‖ ^ 2 =
      ‖k‖ ^ 2 + (1 / (1 + omega)) ^ 2 * Real.log d := by
  have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
  have hinner : inner ℂ (MellinL2.additiveTranslationUnitary (-Real.log d) k)
      (((1 / (1 + omega) : ℝ) : ℂ) • truncatedConstant (Real.log d)) = 0 := by
    rw [inner_smul_right, inner_shift_truncatedConstant_eq_zero _ k hk, mul_zero]
  rw [coupledFeature, norm_sub_sq (𝕜 := ℂ), hinner]
  rw [LinearIsometryEquiv.norm_map, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    norm_truncatedConstant_sq hlog, sq_abs]
  simp


/-! ### The pointed coupled feature and the exact cancellation law -/

/-- Card `(14)`: the pointed coupled feature in the divisor channel space. -/
def coupledFeatureCoord (sigma omega : ℝ) (k : Lp ℂ 2 (volume : Measure ℝ)) (d : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ((Real.sqrt (squarefreeMobiusProbability sigma d) : ℝ) : ℂ) • coupledFeature omega k d

theorem norm_coupledFeatureCoord_sq
    {sigma omega : ℝ} (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) (d : ℕ) :
    ‖coupledFeatureCoord sigma omega k d‖ ^ 2 =
      squarefreeMobiusProbability sigma d * ‖k‖ ^ 2 +
        (1 / (1 + omega)) ^ 2 *
          (squarefreeMobiusProbability sigma d * Real.log d) := by
  have hP : 0 ≤ squarefreeMobiusProbability sigma d := squarefreeMobiusProbability_nonneg hsigma d
  rw [coupledFeatureCoord, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hP,
    norm_coupledFeature_sq d k hk]
  ring

theorem summable_norm_coupledFeatureCoord_sq
    {sigma omega : ℝ} (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    Summable (fun d : ℕ => ‖coupledFeatureCoord sigma omega k d‖ ^ 2) := by
  have h1 : Summable (fun d : ℕ => squarefreeMobiusProbability sigma d * ‖k‖ ^ 2) :=
    (summable_squarefreeMobiusProbability hsigma).mul_right _
  have h2 : Summable (fun d : ℕ =>
      (1 / (1 + omega)) ^ 2 * (squarefreeMobiusProbability sigma d * Real.log d)) := by
    have := summable_squarefreeMobiusLogMoment 1 hsigma
    simp only [pow_one] at this
    exact this.mul_left _
  refine (h1.add h2).congr fun d => ?_
  exact (norm_coupledFeatureCoord_sq hsigma k hk d).symm

/-- The pointed coupled feature is a genuine vector of the divisor-channel Hilbert space. -/
def coupledFeatureVector
    (sigma omega : ℝ) (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    lp (fun _ : ℕ => Lp ℂ 2 (volume : Measure ℝ)) 2 :=
  ⟨fun d => coupledFeatureCoord sigma omega k d, by
    refine (memℓp_gen_iff (by norm_num)).mpr ?_
    have := summable_norm_coupledFeatureCoord_sq (omega := omega) hsigma k hk
    refine this.congr fun d => ?_
    rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, rpow_two_eq_sq]⟩

/-- **Card `(17)`.**  Exact norm of the pointed coupled feature. -/
theorem norm_coupledFeatureVector_sq
    {sigma omega : ℝ} (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ‖coupledFeatureVector sigma omega hsigma k hk‖ ^ 2 =
      ‖k‖ ^ 2 + (1 / (1 + omega)) ^ 2 * squarefreeMobiusLogMoment 1 sigma := by
  have h2r : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hn := lp.norm_rpow_eq_tsum h2r (coupledFeatureVector sigma omega hsigma k hk)
  rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num] at hn
  rw [rpow_two_eq_sq] at hn
  rw [hn]
  have hcongr : (∑' d : ℕ,
        ‖(coupledFeatureVector sigma omega hsigma k hk : ℕ → Lp ℂ 2 (volume : Measure ℝ)) d‖
          ^ (2 : ℝ))
      = ∑' d : ℕ, (squarefreeMobiusProbability sigma d * ‖k‖ ^ 2 +
          (1 / (1 + omega)) ^ 2 * (squarefreeMobiusProbability sigma d * Real.log d)) := by
    refine tsum_congr fun d => ?_
    rw [rpow_two_eq_sq]
    exact norm_coupledFeatureCoord_sq hsigma k hk d
  rw [hcongr]
  have h1 : Summable (fun d : ℕ => squarefreeMobiusProbability sigma d * ‖k‖ ^ 2) :=
    (summable_squarefreeMobiusProbability hsigma).mul_right _
  have hlog := summable_squarefreeMobiusLogMoment 1 hsigma
  simp only [pow_one] at hlog
  have h2 : Summable (fun d : ℕ =>
      (1 / (1 + omega)) ^ 2 * (squarefreeMobiusProbability sigma d * Real.log d)) :=
    hlog.mul_left _
  have hmom : squarefreeMobiusLogMoment 1 sigma
      = ∑' n : ℕ, squarefreeMobiusProbability sigma n * Real.log n := by
    rw [squarefreeMobiusLogMoment]
    exact tsum_congr fun n : ℕ => by rw [pow_one]
  rw [h1.tsum_add h2, tsum_mul_right, tsum_squarefreeMobiusProbability hsigma, one_mul,
    tsum_mul_left, hmom]


/-! ### Card `(20)`--`(23)`: the exact cancellation law -/

private theorem conj_infiniteMobiusSignedWeight (sigma : ℝ) (d : ℕ) :
    (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma d) = infiniteMobiusSignedWeight sigma d := by
  rw [infiniteMobiusSignedWeight, map_mul, Complex.conj_ofReal]
  congr 1
  rw [← Complex.ofReal_intCast, Complex.conj_ofReal]

private theorem signedWeight_smul_coord
    {sigma omega : ℝ} (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ)) (d : ℕ) :
    (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma d) • coupledFeatureCoord sigma omega k d
      = signedMobiusProbability sigma d • coupledFeature omega k d := by
  rw [conj_infiniteMobiusSignedWeight, coupledFeatureCoord, smul_smul,
    infiniteMobiusSignedWeight, signedMobiusProbability]
  congr 1
  rw [mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt
    (squarefreeMobiusProbability_nonneg hsigma d)]

/-- **Card `(20)`.**  Feeding the pointed feature through the signed coisometry produces the signed
Möbius superposition of the channel features. -/
theorem vectorSignedSynthesis_coupledFeatureVector
    {sigma omega : ℝ} (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma)
        (coupledFeatureVector sigma omega hsigma k hk)
      = ∑' d : ℕ, signedMobiusProbability sigma d • coupledFeature omega k d := by
  rw [vectorSignedSynthesis]
  exact tsum_congr fun d => signedWeight_smul_coord hsigma k d

/-- The unnormalized arithmetic coefficient of the signed superposition. -/
theorem squarefreeMobiusTotal_smul_signedMobiusProbability
    {sigma : ℝ} (hsigma : 1 < sigma) (d : ℕ) :
    ((squarefreeMobiusTotal sigma : ℝ) : ℂ) * signedMobiusProbability sigma d
      = (((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-sigma) : ℝ) := by
  have hZ : (squarefreeMobiusTotal sigma) ≠ 0 := ne_of_gt (squarefreeMobiusTotal_pos hsigma)
  have hZC : ((squarefreeMobiusTotal sigma : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hZ
  rw [signedMobiusProbability, squarefreeMobiusProbability]
  by_cases hsq : Squarefree d
  · rw [squarefreeMobiusMass, if_pos hsq]
    push_cast
    field_simp
  · rw [squarefreeMobiusMass, if_neg hsq,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- **Card `(21)`.**  The coupled error is the signed superposition of the channel features. -/
theorem coupledError_eq_tsum
    {sigma omega : ℝ} (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ((squarefreeMobiusTotal sigma : ℝ) : ℂ) •
        vectorSignedSynthesis (infiniteMobiusSignedWeightLp sigma hsigma)
          (coupledFeatureVector sigma omega hsigma k hk)
      = ∑' d : ℕ,
          ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-sigma) : ℝ) : ℂ) •
            coupledFeature omega k d := by
  have hsummable : Summable (fun d : ℕ =>
      signedMobiusProbability sigma d • coupledFeature omega k d) := by
    refine (summable_vectorSignedSynthesisTerm (infiniteMobiusSignedWeightLp sigma hsigma)
      (coupledFeatureVector sigma omega hsigma k hk)).congr fun d => ?_
    exact signedWeight_smul_coord hsigma k d
  rw [vectorSignedSynthesis_coupledFeatureVector hsigma k hk,
    ← hsummable.tsum_const_smul ((squarefreeMobiusTotal sigma : ℝ) : ℂ)]
  refine tsum_congr fun d => ?_
  rw [smul_smul, squarefreeMobiusTotal_smul_signedMobiusProbability hsigma d]

/-- **Card `(23)`.**  The exact cancellation law: the norm of the coupled error is the squarefree
partition times the norm of the projected pointed feature. -/
theorem norm_coupledError_eq
    {sigma omega : ℝ} (hsigma : 1 < sigma) (k : Lp ℂ 2 (volume : Measure ℝ))
    (hk : HasAELowerSupport (fun t : ℝ => k t) 0) :
    ‖∑' d : ℕ,
        ((((ArithmeticFunction.moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-sigma) : ℝ) : ℂ) •
          coupledFeature omega k d‖
      = squarefreeMobiusTotal sigma *
        ‖vectorSignedProjection (infiniteMobiusSignedWeightLp sigma hsigma)
          (coupledFeatureVector sigma omega hsigma k hk)‖ := by
  rw [← coupledError_eq_tsum hsigma k hk, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (squarefreeMobiusTotal_pos hsigma).le,
    norm_vectorSignedSynthesis_eq_norm_projection (norm_infiniteMobiusSignedWeightLp hsigma)]

end RHTower
