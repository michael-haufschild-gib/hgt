import GaloisForLFunctions.RHTower.MobiusThetaStrictTailXiJetRetention
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Complete strict tails escape the leading Xi source line

Exact successor transport identifies the rescaled complete arithmetic tail with
an increasingly translated residual. Plancherel and Riemann–Lebesgue make its
pairing with every fixed Hilbert vector tend to zero, while its norm tends to
the nonzero successor Xi norm. One fixed orthogonal projection consequently
retains that entire limiting norm and annihilates the leading Xi source.

The actual countertransported Gamma-six source, including its forced
half-density and complete tail, is eventually detected by this projection.
Its pure quadratic form is not bounded by any scalar multiple of the pure
leading source's form. This constructs a positive source feature and rules
out that particular domination argument. It does not identify the projection
with the prescribed physical reader or prove the missing cyclic/physical
comparison at the original horizontal anchor.
-/

open Complex MeasureTheory Filter Topology
open scoped FourierTransform InnerProductSpace
namespace RHTower
noncomputable section

private theorem inner_translate_neg_tendsto_zero (g f : MobiusThetaSourceL2) :
    Tendsto (fun a : ℝ => inner ℂ g (MellinL2.additiveTranslationUnitary (-a) f))
      atTop (𝓝 0) := by
  let F : MobiusThetaSourceL2 := 𝓕 f
  let G : MobiusThetaSourceL2 := 𝓕 g
  have hRL := (Real.tendsto_integral_exp_smul_cocompact
    (fun x : ℝ => inner ℂ (G x) (F x))).mono_left
      (show (atTop : Filter ℝ) ≤ cocompact ℝ by
        rw [cocompact_eq_atBot_atTop]; exact le_sup_right)
  refine hRL.congr fun a => ?_
  rw [← (Lp.fourierTransformₗᵢ ℝ ℂ).inner_map_map]
  change _ = inner ℂ G (𝓕 (MellinL2.additiveTranslationUnitary (-a) f))
  rw [MellinL2.fourier_additiveTranslation, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MellinL2.fourierPhaseMulAux_ae (-a) F] with x hx
  change _ = inner ℂ (G x) (MellinL2.fourierPhaseMulAux (-a) F x)
  rw [hx, Circle.smul_def, smul_eq_mul]
  simp only [RCLike.inner_apply, MellinL2.fourierPhase]
  rw [show -a * x = -(x * a) by ring]
  ring

private theorem translate_zero (f : MobiusThetaSourceL2) :
    MellinL2.additiveTranslationUnitary 0 f = f := by
  change Lp.compMeasurePreserving (MellinL2.realTranslationEquiv 0)
    (MellinL2.realTranslation_measurePreserving 0) f = f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving 0)] with x hx
  rw [hx]
  simp [MellinL2.realTranslationEquiv, Function.comp_apply]

/-- The forced successor rescaling of the complete strict source tail. -/
def mobiusThetaStrictTailSuccessorNormalized (p : MobiusPositiveIndex) (m : ℕ) :
    MobiusThetaSourceL2 :=
  ((((mobiusSuccessor p : ℝ) / p) ^ ((m : ℝ) / 2) : ℝ) : ℂ) •
    mobiusThetaStrictTailL2 p m

private def successorShift (p : MobiusPositiveIndex) (m : ℕ) : ℝ :=
  (m : ℝ) * Real.log ((mobiusSuccessor p : ℝ) / p) * MellinL2.spectralNormalization

private theorem normalizedTail_eq_translate (p : MobiusPositiveIndex)
    (m : MobiusHonestDepth) :
    mobiusThetaStrictTailSuccessorNormalized p m =
      MellinL2.additiveTranslationUnitary (-successorShift p m)
        (mobiusThetaPrimeNormalResidual (mobiusSuccessor p) m) := by
  have ht : MellinL2.additiveTranslationUnitary (successorShift p m)
      (mobiusThetaStrictTailSuccessorNormalized p m) =
        mobiusThetaPrimeNormalResidual (mobiusSuccessor p) m := by
    simpa only [mobiusThetaStrictTailSuccessorNormalized, map_smul,
      mobiusThetaSuccessorBlowup, mobiusThetaStrictTailL2, successorShift]
      using mobiusTheta_successor_transport p m
  rw [← ht, additiveTranslationUnitary_add_apply, neg_add_cancel, translate_zero]

private theorem successorShift_tendsto (p : MobiusPositiveIndex) :
    Tendsto (successorShift p) atTop atTop := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (by have := p.property; omega : 0 < p.val)
  have hratio : (1 : ℝ) < (mobiusSuccessor p : ℝ) / p := by
    rw [one_lt_div hp]
    exact_mod_cast lt_mobiusSuccessor p
  exact (tendsto_natCast_atTop_atTop.atTop_mul_const (Real.log_pos hratio)).atTop_mul_const
    MellinL2.spectralNormalization_pos

/-- Every fixed Hilbert reader loses the forced, norm-retaining successor tail. -/
theorem tendsto_inner_mobiusThetaStrictTailSuccessorNormalized
    (p : MobiusPositiveIndex) (g : MobiusThetaSourceL2) :
    Tendsto (fun m : ℕ => inner ℂ g (mobiusThetaStrictTailSuccessorNormalized p m))
      atTop (𝓝 0) := by
  let v : MobiusThetaSourceL2 :=
    (((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) • xiThetaSourceL2
  have hres : Tendsto (mobiusThetaPrimeNormalResidual (mobiusSuccessor p)) atTop (𝓝 v) :=
    tendsto_mobiusThetaPrimeNormalResidual
      (Nat.one_le_iff_ne_zero.mpr (mobiusSuccessor_pos p.property).ne_zero)
  have herr : Tendsto (fun m : ℕ =>
      mobiusThetaStrictTailSuccessorNormalized p m -
        MellinL2.additiveTranslationUnitary (-successorShift p m) v) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hnorm := (hres.sub (tendsto_const_nhds (x := v))).norm
    simp only [sub_self, norm_zero] at hnorm
    apply hnorm.congr'
    filter_upwards [eventually_ge_atTop 3] with m hm
    rw [normalizedTail_eq_translate p ⟨m, hm⟩, ← map_sub]
    exact (MellinL2.additiveTranslationUnitary (-successorShift p m)).norm_map _ |>.symm
  have hweak := (inner_translate_neg_tendsto_zero g v).comp (successorShift_tendsto p)
  have hread := (tendsto_const_nhds (x := g)).inner herr (𝕜 := ℂ)
  simpa only [Function.comp_def, inner_sub_right, inner_zero_right, sub_add_cancel, zero_add]
    using hread.add hweak

/-- Successor normalization keeps a strictly positive source norm. -/
theorem tendsto_norm_mobiusThetaStrictTailSuccessorNormalized
    (p : MobiusPositiveIndex) :
    Tendsto (fun m : ℕ => ‖mobiusThetaStrictTailSuccessorNormalized p m‖) atTop
      (𝓝 ‖(((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) •
        xiThetaSourceL2‖) := by
  have ht := (tendsto_mobiusThetaPrimeNormalResidual
    (Nat.one_le_iff_ne_zero.mpr (mobiusSuccessor_pos p.property).ne_zero)).norm
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with m hm
  rw [normalizedTail_eq_translate p ⟨m, hm⟩]
  exact (MellinL2.additiveTranslationUnitary (-successorShift p m)).norm_map _ |>.symm

/-- Fixed source projection; no depth or Xi divisor enters its definition. -/
def xiThetaLeadingComplement : MobiusThetaSourceL2 →L[ℂ] MobiusThetaSourceL2 :=
  (ℂ ∙ xiThetaSourceL2)ᗮ.starProjection

@[simp] theorem xiThetaLeadingComplement_self :
    xiThetaLeadingComplement xiThetaSourceL2 = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero xiThetaSourceL2

private theorem norm_complement_limit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (u : ℕ → E) (v : E) (L : ℝ)
    (hi : Tendsto (fun m => inner ℂ v (u m)) atTop (𝓝 0))
    (hn : Tendsto (fun m => ‖u m‖) atTop (𝓝 L)) :
    Tendsto (fun m => ‖(ℂ ∙ v)ᗮ.starProjection (u m)‖) atTop (𝓝 L) := by
  have hscalar : Tendsto (fun m => inner ℂ v (u m) / ((‖v‖ ^ 2 : ℝ) : ℂ))
      atTop (𝓝 (0 : ℂ)) := by
    simpa only [zero_div] using hi.div_const ((‖v‖ ^ 2 : ℝ) : ℂ)
  have hv : Tendsto (fun m => (inner ℂ v (u m) / ((‖v‖ ^ 2 : ℝ) : ℂ)) • v)
      atTop (𝓝 (0 : E)) := by
    simpa only [zero_smul] using hscalar.smul_const v
  have hproj : Tendsto (fun m => (ℂ ∙ v).starProjection (u m)) atTop (𝓝 (0 : E)) :=
    hv.congr (fun m => (Submodule.starProjection_singleton ℂ (u m)).symm)
  apply hn.congr_dist
  have hnorm := hproj.norm
  simp only [norm_zero] at hnorm
  apply squeeze_zero (fun _ => dist_nonneg) _ hnorm
  intro m
  calc
    dist ‖u m‖ ‖(ℂ ∙ v)ᗮ.starProjection (u m)‖
      ≤ ‖u m - (ℂ ∙ v)ᗮ.starProjection (u m)‖ := dist_norm_norm_le _ _
    _ = ‖(ℂ ∙ v).starProjection (u m)‖ := by
      simp only [Submodule.starProjection_orthogonal_val, sub_sub_cancel]

/-- The same fixed projection retains the entire limiting normalized tail norm. -/
theorem tendsto_norm_xiThetaLeadingComplement_normalizedTail
    (p : MobiusPositiveIndex) :
    Tendsto (fun m : ℕ =>
      ‖xiThetaLeadingComplement (mobiusThetaStrictTailSuccessorNormalized p m)‖) atTop
      (𝓝 ‖(((ArithmeticFunction.moebius (mobiusSuccessor p) : ℝ) : ℂ)) •
        xiThetaSourceL2‖) :=
  norm_complement_limit (mobiusThetaStrictTailSuccessorNormalized p) xiThetaSourceL2 _
    (tendsto_inner_mobiusThetaStrictTailSuccessorNormalized p xiThetaSourceL2)
    (tendsto_norm_mobiusThetaStrictTailSuccessorNormalized p)

/-- Strict tails eventually have a nonzero component outside the leading source line. -/
theorem eventually_xiThetaLeadingComplement_strictTail_ne_zero
    (p : MobiusPositiveIndex) :
    ∀ᶠ m : ℕ in atTop, xiThetaLeadingComplement (mobiusThetaStrictTailL2 p m) ≠ 0 := by
  have hpos := (tendsto_norm_xiThetaLeadingComplement_normalizedTail p).eventually
    (eventually_gt_nhds (mobiusThetaStrictTailL2_normalized_limit_pos p))
  filter_upwards [hpos] with m hm
  intro hz
  have hne := norm_pos_iff.mp hm
  apply hne
  simp only [mobiusThetaStrictTailSuccessorNormalized, map_smul, hz, smul_zero]

/-- The actual source tail is eventually linearly independent of the leading Xi direction. -/
theorem eventually_mobiusThetaStrictTailL2_not_mem_leadingLine
    (p : MobiusPositiveIndex) :
    ∀ᶠ m : ℕ in atTop, mobiusThetaStrictTailL2 p m ∉ (ℂ ∙ xiThetaSourceL2) := by
  filter_upwards [eventually_xiThetaLeadingComplement_strictTail_ne_zero p] with m hm
  intro hmem
  exact hm (Submodule.starProjection_orthogonal_apply_eq_zero hmem)

@[simp] theorem xiThetaLeadingComplement_gammaSixLeading (m : MobiusHonestDepth) :
    xiThetaLeadingComplement (deningerGammaSixCountertransportedLeadingSource m) = 0 := by
  simp only [deningerGammaSixCountertransportedLeadingSource, map_smul,
    xiThetaLeadingComplement_self, smul_zero]

/-- Positive event for the complete Gamma-six source, with its forced half-density retained. -/
theorem eventually_xiThetaLeadingComplement_gammaSixSource_ne_zero :
    ∀ᶠ n : ℕ in atTop,
      xiThetaLeadingComplement
        (deningerGammaSixCountertransportedSource ⟨n + 3, by omega⟩) ≠ 0 := by
  have ht := (tendsto_add_atTop_nat 3).eventually
    (eventually_xiThetaLeadingComplement_strictTail_ne_zero ⟨6, by norm_num⟩)
  filter_upwards [ht] with n hn
  rw [deningerGammaSixCountertransportedSource_eq_leading_add_tail, map_add,
    xiThetaLeadingComplement_gammaSixLeading, zero_add,
    deningerGammaSixCountertransportedTail_eq_strictTail, map_smul]
  apply smul_ne_zero
  · exact_mod_cast (deningerGammaSixHalfWeight_pos ⟨n + 3, by omega⟩).ne'
  · exact hn

/-- A fixed orthogonal source event supplies an explicit separating test vector. -/
private theorem leadingComplement_separates {s : MobiusThetaSourceL2}
    (hs : xiThetaLeadingComplement s ≠ 0) :
    inner ℂ (xiThetaLeadingComplement s) xiThetaSourceL2 = 0 ∧
      inner ℂ (xiThetaLeadingComplement s) s ≠ 0 := by
  constructor
  · rw [xiThetaLeadingComplement, Submodule.inner_starProjection_left_eq_right]
    change inner ℂ s (xiThetaLeadingComplement xiThetaSourceL2) = 0
    rw [xiThetaLeadingComplement_self, inner_zero_right]
  · intro hz
    have h := (ℂ ∙ xiThetaSourceL2)ᗮ.re_inner_starProjection_eq_normSq s
    change (inner ℂ (xiThetaLeadingComplement s) s).re =
      ‖(ℂ ∙ xiThetaSourceL2)ᗮ.orthogonalProjectionOnto s‖ ^ 2 at h
    rw [hz, zero_re] at h
    have hnorm : ‖xiThetaLeadingComplement s‖ = 0 := by
      change ‖(ℂ ∙ xiThetaSourceL2)ᗮ.orthogonalProjectionOnto s‖ = 0
      nlinarith [norm_nonneg ((ℂ ∙ xiThetaSourceL2)ᗮ.orthogonalProjectionOnto s)]
    exact hs (norm_eq_zero.mp hnorm)

/-- The full pure source cannot be dominated by any scalar multiple of its pure leading state.
The witness is the actual source's component under one fixed, divisor-independent projection. -/
theorem eventually_gammaSixSource_not_dominated_by_pure_leading :
    ∀ᶠ n : ℕ in atTop, ∀ C : ℝ, ¬ ∀ g : MobiusThetaSourceL2,
      ‖inner ℂ g (deningerGammaSixCountertransportedSource ⟨n + 3, by omega⟩)‖ ^ 2 ≤
        C * ‖inner ℂ g
          (deningerGammaSixCountertransportedLeadingSource ⟨n + 3, by omega⟩)‖ ^ 2 := by
  filter_upwards [eventually_xiThetaLeadingComplement_gammaSixSource_ne_zero] with n hn
  obtain ⟨hdark, hbright⟩ := leadingComplement_separates hn
  intro C hC
  have h := hC (xiThetaLeadingComplement
    (deningerGammaSixCountertransportedSource ⟨n + 3, by omega⟩))
  simp only [deningerGammaSixCountertransportedLeadingSource,
    inner_smul_right, hdark, mul_zero, norm_zero, zero_pow (by omega : 2 ≠ 0)] at h
  exact (not_le_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hbright))) h

end
end RHTower
