import GaloisForLFunctions.RHTower.EvenL2LogUnitary
import GaloisForLFunctions.RHTower.PerronCarrierFlankMass

/-!
# Sonin source support transfers to Perron arithmetic support

Membership in the even Sonin carrier forces a physical support gap.  In logarithmic coordinates
this becomes a lower support constraint, which gives geometric bounds for all negatively weighted
source norms.  The normalized Fourier--Mellin unitary transfers those bounds to spectral `L²`
traces.

The essential new constraint is **cross-line Mellin coherence**: one analytic function must realize
all of those separately constructed `L²` traces.  Under coherence and the coefficient-independent
horizontal mass from `PerronCarrierFlankMass.lean`, the physical cutoff `q` bounds arithmetic
Dirichlet support by `q⁻¹`.  For `q>1`, every positive-index coefficient vanishes.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Filter Topology Set
open scoped ENNReal Topology

/-- A measurable source vanishes almost everywhere strictly below the logarithmic threshold `τ`. -/
def HasAELowerSupport (g : ℝ → ℂ) (τ : ℝ) : Prop :=
  ∀ᵐ t : ℝ ∂volume, t < τ → g t = 0

/-- The physical half of the Sonin constraint becomes lower support at `log a` after the exact
logarithmic unitary. -/
theorem logEvenUnitary_hasAELowerSupport
    {a : ℝ} (ha : 0 < a) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier a) :
    HasAELowerSupport (fun t => logEvenUnitary f t) (Real.log a) := by
  have hphys : (f : evenSubspace).1 ∈ (centralPhysicalForbidden a)ᗮ := by
    exact hf.1
  have hcut : indicatorCutoff (centralInterval a) (measurableSet_centralInterval a) f.1 = 0 := by
    rw [indicatorCutoff_eq_physicalForbidden_starProjection]
    apply (Submodule.starProjection_apply_eq_zero_iff
      (K := physicalForbidden (centralInterval a) (measurableSet_centralInterval a))).mpr
    simpa [centralPhysicalForbidden, centralInterval] using hphys
  have hcutAE := indicatorCutoff_ae (centralInterval a) (measurableSet_centralInterval a) f.1
  rw [hcut] at hcutAE
  have hphysicalZero : ∀ᵐ x : ℝ ∂volume, x ∈ centralInterval a → f.1 x = 0 := by
    filter_upwards [hcutAE, Lp.coeFn_zero ℂ 2 volume] with x hx hzero
    intro hxmem
    rw [Set.indicator_of_mem hxmem] at hx
    exact hx.symm.trans hzero
  have hphysicalExp := realExp_quasiMeasurePreserving.ae hphysicalZero
  filter_upwards [logEvenUnitary_ae f, hphysicalExp] with t hlog hzero
  intro ht
  rw [hlog, hzero]
  · simp
  · rw [centralInterval, Set.mem_Icc]
    constructor
    · linarith [Real.exp_pos t]
    · rw [← Real.exp_log ha]
      exact Real.exp_le_exp.mpr ht.le

/-- The source multiplier corresponding to the negative Mellin line `Re s=-M`. -/
def negativeLogWeight (M : ℕ) (t : ℝ) : ℝ := Real.exp (-(M : ℝ) * t)

/-- A logarithmic source weighted for the negative Mellin line `Re s=-M`. -/
def negativeMellinSourceFun (M : ℕ) (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (negativeLogWeight M t : ℂ) * g t

/-- **Lower support gives geometric negative moments.**  If `g` vanishes below `τ`, then weighting
by `exp(-Mt)` preserves `L²` and costs at most `exp(-Mτ)`. -/
theorem negativeMellinSource_memLp_and_lpNorm_le
    {g : ℝ → ℂ} {τ : ℝ} (hg : MemLp g 2 volume)
    (hsupp : HasAELowerSupport g τ) (M : ℕ) :
    MemLp (negativeMellinSourceFun M g) 2 volume ∧
      lpNorm (negativeMellinSourceFun M g) 2 volume ≤
        Real.exp (-(M : ℝ) * τ) * lpNorm g 2 volume := by
  let C : ℝ := Real.exp (-(M : ℝ) * τ)
  have hC0 : 0 ≤ C := (Real.exp_pos _).le
  have hmeas : AEStronglyMeasurable (negativeMellinSourceFun M g) := by
    have hwcont : Continuous (fun t : ℝ => (negativeLogWeight M t : ℂ)) := by
      unfold negativeLogWeight
      fun_prop
    exact hwcont.aestronglyMeasurable.mul hg.1
  have hdom : ∀ᵐ t : ℝ ∂volume,
      ‖negativeMellinSourceFun M g t‖ ≤
        ‖(C : ℂ) * g t‖ := by
    filter_upwards [hsupp] with t htzero
    by_cases ht : t < τ
    · rw [negativeMellinSourceFun, htzero ht, mul_zero]
      simp
    · have hτt : τ ≤ t := le_of_not_gt ht
      have hexp : negativeLogWeight M t ≤ C := by
        unfold negativeLogWeight C
        apply Real.exp_le_exp.mpr
        have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
        nlinarith
      rw [negativeMellinSourceFun, norm_mul, negativeLogWeight, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hC0]
      exact mul_le_mul_of_nonneg_right hexp (norm_nonneg _)
  have hCg : MemLp (fun t : ℝ => (C : ℂ) * g t) 2 volume := hg.const_mul C
  have hw : MemLp (negativeMellinSourceFun M g) 2 volume :=
    hCg.of_le hmeas hdom
  refine ⟨hw, ?_⟩
  have he : eLpNorm (negativeMellinSourceFun M g) 2 volume ≤
      eLpNorm (fun t : ℝ => (C : ℂ) * g t) 2 volume := eLpNorm_mono_ae hdom
  have hreal := ENNReal.toReal_mono hCg.eLpNorm_ne_top he
  rw [toReal_eLpNorm hw.1, toReal_eLpNorm hCg.1] at hreal
  rw [show (fun t : ℝ => (C : ℂ) * g t) = (C : ℂ) • g by rfl,
    lpNorm_const_smul] at hreal
  norm_cast at hreal
  rw [Real.norm_of_nonneg hC0] at hreal
  simpa only [C] using hreal

/-- The real square-root energy used by the Perron interface is exactly the `L²` seminorm. -/
theorem sqrt_integral_norm_sq_eq_lpNorm
    {g : ℝ → ℂ} (hg : MemLp g 2 volume) :
    Real.sqrt (∫ t : ℝ, ‖g t‖ ^ 2) = lpNorm g 2 volume := by
  have hnorm := hg.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ∞)
  have hreal := congrArg ENNReal.toReal hnorm
  rw [toReal_eLpNorm hg.1] at hreal
  norm_num only [ENNReal.toReal_ofNat] at hreal
  simp only [Real.rpow_two] at hreal
  have hint0 : 0 ≤ ∫ t : ℝ, ‖g t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  let I : ℝ := ∫ t : ℝ, ‖g t‖ ^ 2
  have hreal' : lpNorm g 2 volume =
      (ENNReal.ofReal (I ^ (1 / (2 : ℝ)))).toReal := by
    simpa only [I] using hreal
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hint0 _)] at hreal'
  simpa [I, Real.sqrt_eq_rpow] using hreal'.symm

/-- The normalized Fourier--Mellin unitary from logarithmic source coordinate to standard spectral
coordinate. -/
def logMellinUnitary : SoninL2 ≃ₗᵢ[ℂ] SoninL2 :=
  fourierUnitary.trans
    (dilationUnitary MellinL2.spectralNormalization MellinL2.spectralNormalization_pos)

/-- The canonical `L²` class of the negatively weighted source. -/
def negativeMellinSourceLp
    (g : SoninL2) (τ : ℝ) (hsupp : HasAELowerSupport (fun t => g t) τ)
    (M : ℕ) : SoninL2 :=
  (negativeMellinSource_memLp_and_lpNorm_le (Lp.memLp g) hsupp M).1.toLp
    (negativeMellinSourceFun M fun t => g t)

/-- The canonical source class is represented by the explicit negative weight almost everywhere. -/
theorem negativeMellinSourceLp_ae
    (g : SoninL2) (τ : ℝ) (hsupp : HasAELowerSupport (fun t => g t) τ)
    (M : ℕ) :
    negativeMellinSourceLp g τ hsupp M =ᵐ[volume]
      negativeMellinSourceFun M fun t => g t :=
  (negativeMellinSource_memLp_and_lpNorm_le (Lp.memLp g) hsupp M).1.coeFn_toLp

/-- The normalized spectral `L²` trace produced from the source at `Re s=-M`. -/
def negativeMellinL2Trace
    (g : SoninL2) (τ : ℝ) (hsupp : HasAELowerSupport (fun t => g t) τ)
    (M : ℕ) : SoninL2 :=
  logMellinUnitary (negativeMellinSourceLp g τ hsupp M)

/-- The normalized Mellin trace inherits the geometric source norm bound exactly. -/
theorem negativeMellinL2Trace_norm_le
    (g : SoninL2) (τ : ℝ) (hsupp : HasAELowerSupport (fun t => g t) τ)
    (M : ℕ) :
    ‖negativeMellinL2Trace g τ hsupp M‖ ≤
      Real.exp (-(M : ℝ) * τ) * ‖g‖ := by
  rw [negativeMellinL2Trace, LinearIsometryEquiv.norm_map]
  rw [negativeMellinSourceLp, Lp.norm_toLp,
    toReal_eLpNorm
      (negativeMellinSource_memLp_and_lpNorm_le (Lp.memLp g) hsupp M).1.1]
  have hbound :=
    (negativeMellinSource_memLp_and_lpNorm_le (Lp.memLp g) hsupp M).2
  rw [Lp.norm_def, toReal_eLpNorm (Lp.aestronglyMeasurable g)]
  exact hbound

/-- **Cross-line Mellin coherence.**  Every negative integer line of one analytic carrier agrees
almost everywhere with the normalized `L²` trace of the correspondingly weighted common source. -/
def HasCoherentNegativeMellinTraces
    (F : ℂ → ℂ) (g : SoninL2) (τ : ℝ)
    (hsupp : HasAELowerSupport (fun t => g t) τ) : Prop :=
  ∀ M : ℕ, (fun t : ℝ => F (↑(-(M : ℝ)) + ↑t * I)) =ᵐ[volume]
    fun t => negativeMellinL2Trace g τ hsupp M t

/-- Coherent negative Mellin traces discharge the Perron vertical-energy Prop. -/
theorem HasCoherentNegativeMellinTraces.hasPerronCarrierFlankL2Energy
    {F : ℂ → ℂ} {g : SoninL2} {τ : ℝ}
    (hsupp : HasAELowerSupport (fun t => g t) τ)
    (hcoh : HasCoherentNegativeMellinTraces F g τ hsupp) :
    HasPerronCarrierFlankL2Energy F
      (fun M => Real.exp (-(M : ℝ) * τ) * ‖g‖) := by
  refine Eventually.of_forall fun M => ?_
  let T : SoninL2 := negativeMellinL2Trace g τ hsupp M
  let line : ℝ → ℂ := fun t => F (↑(-(M : ℝ)) + ↑t * I)
  have hlineTrace : line =ᵐ[volume] fun t => T t := hcoh M
  have htraceMem : MemLp (fun t => T t) 2 volume := Lp.memLp T
  have hlineMem : MemLp line 2 volume := htraceMem.ae_eq hlineTrace.symm
  refine ⟨(memLp_two_iff_integrable_sq_norm hlineMem.1).1 hlineMem, ?_⟩
  rw [sqrt_integral_norm_sq_eq_lpNorm hlineMem]
  have hlp : lpNorm line 2 volume = ‖T‖ := by
    calc
      lpNorm line 2 volume = (eLpNorm line 2 volume).toReal :=
        (toReal_eLpNorm hlineMem.1).symm
      _ = (eLpNorm (fun t => T t) 2 volume).toReal := by
        rw [eLpNorm_congr_ae hlineTrace]
      _ = ‖T‖ := by rw [Lp.norm_def]
  rw [hlp]
  exact negativeMellinL2Trace_norm_le g τ hsupp M

/-- A physical cutoff `a` gives the exact geometric radius `a⁻¹` on negative integer lines. -/
theorem exp_neg_nat_mul_log_eq_inv_pow
    {a : ℝ} (ha : 0 < a) (M : ℕ) :
    Real.exp (-(M : ℝ) * Real.log a) = a⁻¹ ^ M := by
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos (inv_pos.mpr ha), Real.log_inv]
  congr 1
  ring

/-- Sonin membership plus cross-line coherence supplies geometric Perron flank energy of radius
`a⁻¹`. -/
theorem soninCoherentNegativeMellinTraces_hasPerronCarrierFlankL2Energy
    {F : ℂ → ℂ} {a : ℝ} (ha : 0 < a) (f : evenSubspace)
    (hf : f ∈ evenCentralSoninCarrier a)
    (hcoh : HasCoherentNegativeMellinTraces F (logEvenUnitary f) (Real.log a)
      (logEvenUnitary_hasAELowerSupport ha f hf)) :
    HasPerronCarrierFlankL2Energy F
      (fun M => a⁻¹ ^ M * ‖logEvenUnitary f‖) := by
  have henergy := HasCoherentNegativeMellinTraces.hasPerronCarrierFlankL2Energy
    (logEvenUnitary_hasAELowerSupport ha f hf) hcoh
  simpa only [exp_neg_nat_mul_log_eq_inv_pow ha] using henergy

/-- **Sonin--Perron cross-support theorem.**  Under coherent negative Mellin traces and finite
horizontal carrier mass, every nonzero Dirichlet coefficient index is at most the reciprocal
physical cutoff. -/
theorem coefficient_index_le_inv_sonin_cutoff
    {F : ℂ → ℂ} {q c : ℝ} {coeff : ℕ → ℂ} {n : ℕ}
    (hq : 0 < q) (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier q)
    (hcoh : HasCoherentNegativeMellinTraces F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf))
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) (han : coeff n ≠ 0) :
    (n : ℝ) ≤ q⁻¹ := by
  let B : ℕ → ℝ := fun M => q⁻¹ ^ M * ‖logEvenUnitary f‖
  have henergy : HasPerronCarrierFlankL2Energy F B := by
    exact soninCoherentNegativeMellinTraces_hasPerronCarrierFlankL2Energy hq f hf hcoh
  have hR : 0 ≤ q⁻¹ := (inv_pos.mpr hq).le
  have hB0 : ∀ᶠ M : ℕ in atTop, 0 ≤ B M := by
    exact Eventually.of_forall fun M => mul_nonneg (pow_nonneg hR M) (norm_nonneg _)
  have hB : ∀ᶠ M : ℕ in atTop,
      B M ≤ ‖logEvenUnitary f‖ * q⁻¹ ^ M := by
    exact Eventually.of_forall fun M => by
      dsimp [B]
      rw [mul_comm]
  exact coefficient_index_le_exact_flank_radius_of_carrierL2StripMass
    henergy hhorizontal hc0 hsum hF hFeq hn hR hB0 hB han

/-- **Coherence obstruction above unit cutoff.**  If `q>1`, an analytic Dirichlet carrier coherent
with a Sonin source at cutoff `q` has every positive-index coefficient equal to zero. -/
theorem coefficient_eq_zero_of_one_lt_sonin_cutoff
    {F : ℂ → ℂ} {q c : ℝ} {coeff : ℕ → ℂ} {n : ℕ}
    (hq : 1 < q) (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier q)
    (hcoh : HasCoherentNegativeMellinTraces F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport (lt_trans zero_lt_one hq) f hf))
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hn : 1 ≤ n) :
    coeff n = 0 := by
  by_contra han
  have hle := coefficient_index_le_inv_sonin_cutoff
    (lt_trans zero_lt_one hq) f hf hcoh hhorizontal hc0 hsum hF hFeq hn han
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hqinv : q⁻¹ < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq)).2 hq
  linarith

/-- **Sonin--Perron incompatibility above unit cutoff.**  The coefficient obstruction propagates
from the Dirichlet half-plane to the entire carrier: if `q>1`, cross-line coherence and finite
horizontal carrier mass force `F` to vanish identically. -/
theorem entire_eq_zero_of_one_lt_sonin_cutoff
    {F : ℂ → ℂ} {q c : ℝ} {coeff : ℕ → ℂ}
    (hq : 1 < q) (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier q)
    (hcoh : HasCoherentNegativeMellinTraces F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport (lt_trans zero_lt_one hq) f hf))
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s) :
    F = 0 := by
  have hcoeff : ∀ n : ℕ, n ≠ 0 → coeff n = 0 := by
    intro n hn
    exact coefficient_eq_zero_of_one_lt_sonin_cutoff hq f hf hcoh hhorizontal hc0
      hsum hF hFeq (Nat.one_le_iff_ne_zero.mpr hn)
  have hL : ∀ s : ℂ, LSeries coeff s = 0 := by
    intro s
    calc
      LSeries coeff s = LSeries (0 : ℕ → ℂ) s :=
        LSeries_congr (fun {n} hn => by simpa using hcoeff n hn) s
      _ = 0 := congrFun LSeries_zero s
  have hFan : AnalyticOnNhd ℂ F Set.univ :=
    hF.differentiableOn.analyticOnNhd isOpen_univ
  let z0 : ℂ := ((c + 1 : ℝ) : ℂ)
  have hz0 : c < z0.re := by simp [z0]
  have hright : ∀ᶠ z : ℂ in 𝓝 z0, c < z.re :=
    Complex.continuous_re.continuousAt.eventually (isOpen_Ioi.mem_nhds hz0)
  have hev : F =ᶠ[𝓝 z0] 0 := by
    filter_upwards [hright] with z hz
    simpa [hL z] using hFeq z hz.le
  funext z
  exact hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z0) hev (Set.mem_univ z)

/-- A nonzero Dirichlet carrier with finite horizontal mass cannot satisfy the proposed cross-line
Mellin coherence with a Sonin source at cutoff `q>1`.  This is the direct seam obstruction. -/
theorem not_coherent_of_nonzero_one_lt_sonin_cutoff
    {F : ℂ → ℂ} {q c : ℝ} {coeff : ℕ → ℂ}
    (hq : 1 < q) (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier q)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hFne : F ≠ 0) :
    ¬ HasCoherentNegativeMellinTraces F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport (lt_trans zero_lt_one hq) f hf) := by
  intro hcoh
  exact hFne (entire_eq_zero_of_one_lt_sonin_cutoff hq f hf hcoh hhorizontal
    hc0 hsum hF hFeq)

/-- **Finite-support rigidity at every positive cutoff.**  Cross-line coherence and horizontal
carrier mass force the full coefficient support (including the irrelevant index zero) to be finite.
The quantitative theorem places every positive support index below `q⁻¹`. -/
theorem coefficient_support_finite_of_sonin_coherence
    {F : ℂ → ℂ} {q c : ℝ} {coeff : ℕ → ℂ}
    (hq : 0 < q) (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier q)
    (hcoh : HasCoherentNegativeMellinTraces F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf))
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s) :
    (Function.support coeff).Finite := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt q⁻¹
  have hN0 : 0 < N := by
    exact_mod_cast (lt_trans (inv_pos.mpr hq) hN)
  refine (Finset.finite_toSet (Finset.range N)).subset ?_
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [hN0]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    have hnR : (n : ℝ) ≤ q⁻¹ := coefficient_index_le_inv_sonin_cutoff
      hq f hf hcoh hhorizontal hc0 hsum hF hFeq hn1 hn
    have hnN : n < N := by exact_mod_cast (lt_of_le_of_lt hnR hN)
    simpa using hnN

/-- An infinite-support Dirichlet carrier with finite horizontal mass cannot be cross-line coherent
with a Sonin source at any positive cutoff. -/
theorem not_coherent_of_infinite_coefficient_support
    {F : ℂ → ℂ} {q c : ℝ} {coeff : ℕ → ℂ}
    (hq : 0 < q) (f : evenSubspace) (hf : f ∈ evenCentralSoninCarrier q)
    (hhorizontal : HasPerronCarrierHorizontalMass F c)
    (hc0 : 0 < c) (hsum : LSeriesSummable coeff c) (hF : Differentiable ℂ F)
    (hFeq : ∀ s : ℂ, c ≤ s.re → F s = LSeries coeff s)
    (hinf : (Function.support coeff).Infinite) :
    ¬ HasCoherentNegativeMellinTraces F (logEvenUnitary f) (Real.log q)
      (logEvenUnitary_hasAELowerSupport hq f hf) := by
  intro hcoh
  exact hinf (coefficient_support_finite_of_sonin_coherence hq f hf hcoh
    hhorizontal hc0 hsum hF hFeq)

end RHTower
