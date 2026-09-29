import GaloisForLFunctions.RHTower.DeckPointPairGradient
import GaloisForLFunctions.RHTower.MaassFiniteDeckCuspidalFriedrichs

/-!
# Point-pair operators on the cuspidal finite-deck carrier

For a continuous deck-equivariant `F` the translates of the modular cell unfold the point-pair
operator to a single integral over the upper half-plane,

  `L_φ F(z) = ∫_ℍ φ(u(z, w)) F(w) dμ(w)`,

because the fibres of `SL(2,ℤ) → PSL(2,ℤ)` have two elements.  Hyperbolic measure and `u` are
invariant under real translations, so the horocycle average of `L_φ F` at height `y` equals
`∫_ℍ φ(u(iy, w)) (∫_a^{a+N+1} F(x + w) dx) dμ(w)`; vanishing level horocycle averages are therefore
preserved.  Together with the gradient bounds this gives a bounded map from cuspidal `L²` into the
completed cuspidal form domain, and the compact Rellich embedding makes `L_φ` a compact symmetric
operator on cuspidal `L²`.
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology
open scoped MatrixGroups ENNReal

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

local instance gammaNormalPPC (N : ℕ) : (CongruenceSubgroup.Gamma (N + 1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N + 1)

/-- `x ≤ cosh x` for `x ≥ 0`. -/
theorem le_cosh_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.cosh x := by
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  have h2 := Real.exp_pos (-x)
  rw [Real.cosh_eq]
  nlinarith [sq_nonneg (x - 1)]

/-- The kernel support is inside a hyperbolic ball: `u(z, w) ≤ R ⇒ d(z, w) ≤ 1 + 2R`. -/
theorem dist_le_of_pairU_le {z w : ℍ} {R : ℝ} (h : pairU z w ≤ R) : dist z w ≤ 1 + 2 * R := by
  have h1 := pairU_eq_cosh z w
  have h2 := le_cosh_of_nonneg (dist_nonneg (x := z) (y := w))
  linarith

/-- The fibre of `SL(2,ℤ) → PSL(2,ℤ)` has exactly two elements. -/
theorem natCard_fiber_PSL2Z (b : PSL2Z) :
    Nat.card ((QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}) = 2 := by
  have h := tsum_fiber_PSL2Z (fun _ => (1 : ℝ≥0∞)) b
  rw [ENNReal.tsum_const, mul_one, mul_one] at h
  have hE : ENat.card ((QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}) = 2 :=
    ENat.toENNReal_inj.mp (by simpa using h)
  have : Finite ((QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}) :=
    ENat.card_lt_top.1 (by rw [hE]; decide)
  rw [ENat.card_eq_coe_natCard] at hE
  exact_mod_cast hE

section Unfold

variable {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
include hφc hφR

/-- The unfolded point-pair integrand is integrable on `ℍ`: it is continuous and supported in a
compact hyperbolic ball. -/
theorem integrable_pairKernel_smul {F : ℍ → DeckSpace N} (hFc : Continuous F) (z : ℍ) :
    Integrable (fun w : ℍ => ((φ (pairU z w) : ℝ) : ℂ) • F w) := by
  have hcont : Continuous (fun w : ℍ => ((φ (pairU z w) : ℝ) : ℂ) • F w) :=
    (Complex.continuous_ofReal.comp (hφc.comp (continuous_pairU_right z))).smul hFc
  refine (integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall z (1 + 2 * R))
    ?_).1 (hcont.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
  intro w hw
  by_contra hwK
  apply hw
  have : R < pairU z w := by
    by_contra h
    push Not at h
    exact hwK (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le h))
  simp [hφR _ this]

/-- **Unfolding.** For a continuous deck-equivariant `F`,
`L_φ F(z) = ∫_ℍ φ(u(z, w)) F(w) dμ(w)`. -/
theorem ppApply_eq_integral {F : ℍ → DeckSpace N} (hFc : Continuous F)
    (hFe : deckEquivariant N F) (z : ℍ) :
    ppApply φ F z = ∫ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) • F w := by
  rw [isFundamentalDomain_fd.integral_eq_tsum'' _ (integrable_pairKernel_smul hφc hφR hFc z)]
  have hterm : ∀ B : SL(2, ℤ), ppTerm φ F z B =
      ∫ x in fd, ((φ (pairU z ((QuotientGroup.mk B : PSL2Z) • x)) : ℝ) : ℂ) •
        F ((QuotientGroup.mk B : PSL2Z) • x) := by
    intro B
    unfold ppTerm
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [PSL2Z_mk_smul]
    rw [hFe B x]
  have hsum : HasSum (fun B => ppTerm φ F z B) (∑ B ∈ ppNearSet z R, ppTerm φ F z B) :=
    hasSum_sum_of_ne_finset_zero fun B hB => ppTerm_eq_zero hφR F z (by simpa [ppNearSet] using hB)
  have hfib := hsum.tsum_fiberwise (QuotientGroup.mk : SL(2, ℤ) → PSL2Z)
  have hfibre : ∀ b : PSL2Z,
      ∑' B : ((QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}), ppTerm φ F z B =
        (2 : ℂ) • ∫ x in fd, ((φ (pairU z (b • x)) : ℝ) : ℂ) • F (b • x) := by
    intro b
    have hc : ∀ B : ((QuotientGroup.mk : SL(2, ℤ) → PSL2Z) ⁻¹' {b}), ppTerm φ F z B =
        ∫ x in fd, ((φ (pairU z (b • x)) : ℝ) : ℂ) • F (b • x) := fun B => by
      rw [hterm, show (QuotientGroup.mk (B : SL(2, ℤ)) : PSL2Z) = b from B.2]
    rw [tsum_congr hc, tsum_const, natCard_fiber_PSL2Z b, two_smul, two_smul]
  simp_rw [hfibre] at hfib
  have h1 := hfib.const_smul (1 / 2 : ℂ)
  simp only [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at h1
  unfold ppApply
  rw [hsum.tsum_eq, h1.tsum_eq]

end Unfold

/-- The real translation `z ↦ z + x` as an element of `SL(2,ℝ)`. -/
def translationSL (x : ℝ) : SL(2, ℝ) :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem translationSL_smul (x : ℝ) (w : ℍ) : translationSL x • w = x +ᵥ w := by
  ext1
  rw [coe_specialLinearGroup_apply, coe_vadd]
  simp [translationSL]
  ring

/-- Hyperbolic measure is invariant under real translations. -/
theorem integral_comp_vadd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : ℝ)
    (g : ℍ → E) : ∫ w : ℍ, g (x +ᵥ w) = ∫ w : ℍ, g w := by
  have hmp := measurePreserving_smul ((translationSL x : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  have e : ∀ w : ℍ, ((translationSL x : GL (Fin 2) ℝ)) • w = x +ᵥ w := fun w =>
    translationSL_smul x w
  rw [← hmp.integral_comp (measurableEmbedding_const_smul _) g]
  simp only [e]

theorem pairU_vadd (x : ℝ) (z w : ℍ) : pairU (x +ᵥ z) (x +ᵥ w) = pairU z w := by
  unfold pairU
  rw [coe_vadd, coe_vadd, vadd_im, vadd_im, dist_add_left]

theorem continuous_vadd_upper : Continuous (fun p : ℝ × ℍ => p.1 +ᵥ p.2) := by
  refine isOpenEmbedding_coe.isInducing.continuous_iff.2 ?_
  simp only [Function.comp_def, coe_vadd]
  exact (Complex.continuous_ofReal.comp continuous_fst).add (continuous_coe.comp continuous_snd)

theorem vadd_eq_ofComplex_point (x : ℝ) (w : ℍ) :
    x +ᵥ w = ofComplex (SelbergMaassMean.point (x + w.re) w.im) := by
  have him : 0 < (SelbergMaassMean.point (x + w.re) w.im).im := by
    simp [SelbergMaassMean.point, w.im_pos]
  rw [ofComplex_apply_of_im_pos him]
  ext1
  rw [coe_vadd]
  change (x : ℂ) + (w : ℂ) = SelbergMaassMean.point (x + w.re) w.im
  apply Complex.ext <;> simp [SelbergMaassMean.point]

section CuspZero

variable {φ : ℝ → ℝ} {R : ℝ} (hφc : Continuous φ) (hφR : KernelSupport φ R)
include hφc hφR

theorem ppApply_vadd {F : ℍ → DeckSpace N} (hFc : Continuous F) (hFe : deckEquivariant N F)
    (x : ℝ) (z : ℍ) :
    ppApply φ F (x +ᵥ z) = ∫ w : ℍ, ((φ (pairU z w) : ℝ) : ℂ) • F (x +ᵥ w) := by
  rw [ppApply_eq_integral hφc hφR hFc hFe, ← integral_comp_vadd x]
  simp_rw [pairU_vadd]

/-- The horocycle-slab integrand `(x, w) ↦ φ(u(z, w)) F(x + w)_q` is integrable over
`[a, b] × ℍ`. -/
theorem integrable_slab {F : ℍ → DeckSpace N} (hFc : Continuous F) (z : ℍ) (q : Deck N)
    (a b : ℝ) :
    Integrable (Function.uncurry fun (x : ℝ) (w : ℍ) =>
      ((φ (pairU z w) : ℝ) : ℂ) * F (x +ᵥ w) q) ((volume.restrict (Ioc a b)).prod volume) := by
  have hg : Continuous (Function.uncurry fun (x : ℝ) (w : ℍ) =>
      ((φ (pairU z w) : ℝ) : ℂ) * F (x +ᵥ w) q) := by
    refine (Complex.continuous_ofReal.comp (hφc.comp ((continuous_pairU_right z).comp
      continuous_snd))).mul ?_
    exact (continuous_apply q).comp ((PiLp.continuous_ofLp 2 _).comp
      (hFc.comp continuous_vadd_upper))
  rw [← Measure.restrict_univ (μ := (volume : Measure ℍ)), Measure.prod_restrict]
  have hK : IntegrableOn (Function.uncurry fun (x : ℝ) (w : ℍ) =>
      ((φ (pairU z w) : ℝ) : ℂ) * F (x +ᵥ w) q)
      (Icc a b ×ˢ Metric.closedBall z (1 + 2 * R)) (volume.prod volume) :=
    hg.continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_closedBall _ _))
  refine IntegrableOn.integrable_of_ae_notMem_eq_zero
    (hK.mono_measure Measure.restrict_le_self) ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with p hp hps
  have hw : p.2 ∉ Metric.closedBall z (1 + 2 * R) := fun hw =>
    hps ⟨Ioc_subset_Icc_self hp.1, hw⟩
  have : R < pairU z p.2 := by
    by_contra h
    push Not at h
    exact hw (Metric.mem_closedBall.2 (by rw [dist_comm]; exact dist_le_of_pairU_le h))
  simp [Function.uncurry, hφR _ this]

/-- **Cusp-zero preservation.** For a continuous deck-equivariant `F` with vanishing level
horocycle averages, `L_φ F` again has vanishing level horocycle averages: the average of `L_φ F`
over `x ∈ [a, a + N + 1]` at height `y` is `∫_ℍ φ(u(iy, w)) (∫_a^{a+N+1} F(x + w) dx) dμ(w)`. -/
theorem levelCuspZero_ppApply {F : ℍ → DeckSpace N} (hFc : Continuous F)
    (hFe : deckEquivariant N F) (hF0 : levelCuspZero N F) :
    levelCuspZero N (ppApply φ F) := by
  intro q y hy a
  have hz₀ : 0 < (SelbergMaassMean.point 0 y).im := by simp [SelbergMaassMean.point, hy]
  obtain ⟨z₀, hz₀def⟩ : ∃ z₀ : ℍ, z₀ = ofComplex (SelbergMaassMean.point 0 y) := ⟨_, rfl⟩
  have hpt : ∀ x : ℝ, ofComplex (SelbergMaassMean.point x y) = x +ᵥ z₀ := by
    intro x
    rw [hz₀def, vadd_eq_ofComplex_point, ofComplex_apply_of_im_pos hz₀]
    congr 2 <;> simp [SelbergMaassMean.point]
  have hcomp : ∀ x : ℝ, ppApply φ F (ofComplex (SelbergMaassMean.point x y)) q =
      ∫ w : ℍ, ((φ (pairU z₀ w) : ℝ) : ℂ) * F (x +ᵥ w) q := by
    intro x
    rw [hpt, ppApply_vadd hφc hφR hFc hFe]
    have hint := integrable_pairKernel_smul hφc hφR
      (hFc.comp (continuous_vadd_upper.comp (Continuous.prodMk_right x))) z₀
    have h := (EuclideanSpace.proj q : DeckSpace N →L[ℂ] ℂ).integral_comp_comm hint
    simp only [Function.comp_def] at h
    calc (∫ w : ℍ, ((φ (pairU z₀ w) : ℝ) : ℂ) • F (x +ᵥ w)) q
        = EuclideanSpace.proj q (∫ w : ℍ, ((φ (pairU z₀ w) : ℝ) : ℂ) • F (x +ᵥ w)) := rfl
      _ = ∫ w : ℍ, EuclideanSpace.proj q (((φ (pairU z₀ w) : ℝ) : ℂ) • F (x +ᵥ w)) := h.symm
      _ = _ := integral_congr_ae (Eventually.of_forall fun w => by
          change EuclideanSpace.proj q (((φ (pairU z₀ w) : ℝ) : ℂ) • F (x +ᵥ w)) = _
          rw [map_smul, smul_eq_mul]; rfl)
  have hP : a ≤ a + ((N + 1 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  simp_rw [hcomp]
  rw [intervalIntegral.integral_of_le hP,
    integral_integral_swap (integrable_slab hφc hφR hFc z₀ q a _)]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
  change (∫ x in Ioc a (a + ((N + 1 : ℕ) : ℝ)),
    ((φ (pairU z₀ w) : ℝ) : ℂ) * F (x +ᵥ w) q) = 0
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hP]
  have hshift : (∫ x in a..a + ((N + 1 : ℕ) : ℝ), F (x +ᵥ w) q) =
      ∫ x in (a + w.re)..(a + w.re) + ((N + 1 : ℕ) : ℝ),
        F (ofComplex (SelbergMaassMean.point x w.im)) q := by
    simp_rw [vadd_eq_ofComplex_point]
    rw [intervalIntegral.integral_comp_add_right
      (fun x => F (ofComplex (SelbergMaassMean.point x w.im)) q) w.re]
    congr 1
    ring
  rw [hshift, hF0 q w.im_pos (a + w.re), mul_zero]

end CuspZero

/-! ## Bundled profiles and compactness on the cuspidal carrier -/

theorem eLpNorm_normLift (F : ℍ → DeckSpace N) :
    eLpNorm (normLift F) 2 cellMeasure = eLpNorm F 2 cellMeasure :=
  eLpNorm_congr_norm_ae (Eventually.of_forall fun z => norm_normLift F z)

/-- A `C¹` point-pair profile vanishing beyond `R ≥ 0`, with bounded value and derivative. -/
structure PairProfile where
  toFun : ℝ → ℝ
  radius : ℝ
  bound : ℝ
  derivBound : ℝ
  radius_nonneg : 0 ≤ radius
  differentiable : Differentiable ℝ toFun
  continuous_deriv : Continuous (deriv toFun)
  abs_le : ∀ u, |toFun u| ≤ bound
  abs_deriv_le : ∀ u, |deriv toFun u| ≤ derivBound
  support : KernelSupport toFun radius

namespace PairProfile

variable (P : PairProfile)

/-- The point-pair operator of a profile on finite-deck `L²`. -/
def op (N : ℕ) : DeckL2 N →L[ℂ] DeckL2 N :=
  ppL2 P.differentiable.continuous P.abs_le P.radius_nonneg P.support

theorem op_isSymmetric (N : ℕ) :
    ((P.op N : DeckL2 N →L[ℂ] DeckL2 N) : DeckL2 N →ₗ[ℂ] DeckL2 N).IsSymmetric :=
  ppL2_isSymmetric P.differentiable.continuous P.abs_le P.radius_nonneg P.support

theorem op_coeFn (f : DeckL2 N) :
    (P.op N f : ℍ → DeckSpace N) =ᵐ[cellMeasure] ppApply P.toFun f :=
  ppL2_coeFn P.differentiable.continuous P.abs_le P.radius_nonneg P.support f

theorem ppApply_mem (f : DeckL2 N) : ppApply P.toFun f ∈ formPreDomain N :=
  ppApply_mem_formPreDomain P.differentiable P.continuous_deriv P.abs_le P.abs_deriv_le
    P.radius_nonneg P.support (Lp.memLp f)

/-- `L_φ f` as a vector of the form pre-domain. -/
def pre (f : DeckL2 N) : formPreDomain N := ⟨ppApply P.toFun f, P.ppApply_mem f⟩

theorem pre_add (f g : DeckL2 N) : P.pre (f + g) = P.pre f + P.pre g := by
  apply Subtype.ext
  change ppApply P.toFun ⇑(f + g) = ppApply P.toFun ⇑f + ppApply P.toFun ⇑g
  rw [ppApply_congr_ae _ (Lp.coeFn_add f g),
    ppApply_add P.differentiable.continuous P.abs_le P.support (Lp.memLp f) (Lp.memLp g)]

theorem pre_smul (c : ℂ) (f : DeckL2 N) : P.pre (c • f) = c • P.pre f := by
  apply Subtype.ext
  change ppApply P.toFun ⇑(c • f) = c • ppApply P.toFun ⇑f
  rw [ppApply_congr_ae _ (Lp.coeFn_smul c f), ppApply_smul]

/-- `f ↦ (L_φ f, y∂ₓL_φ f, y∂ᵧL_φ f)` into the form triple. -/
def formLinear (N : ℕ) : DeckL2 N →ₗ[ℂ] FormTriple N where
  toFun f := formEmbeddingMap N (P.pre f)
  map_add' f g := by rw [P.pre_add, map_add]
  map_smul' c f := by rw [P.pre_smul, map_smul, RingHom.id_apply]

/-- The mass constant of the form map. -/
def formConst : ℝ :=
  (ppKernelMass P.toFun).toReal +
    (5 * P.radius + 3) * (ppKernelMass (fun u => |deriv P.toFun u|)).toReal

theorem kernelMass_deriv_lt_top : ppKernelMass (fun u => |deriv P.toFun u|) < ⊤ :=
  kernelMass_lt_top P.radius_nonneg (fun u => by rw [abs_abs]; exact P.abs_deriv_le u)
    (kernelSupport_abs_deriv P.support)

theorem norm_gradCoord_le {G : ℍ → DeckSpace N} (hG : MemLp G 2 cellMeasure) {c : ℝ} (hc : 0 ≤ c)
    (f : DeckL2 N) (hle : ∀ z, ‖G z‖ ≤ c * ‖ppApply (fun u => |deriv P.toFun u|) (normLift ⇑f) z‖) :
    ‖toDeckL2 G hG‖ ≤ c * (ppKernelMass (fun u => |deriv P.toFun u|)).toReal * ‖f‖ := by
  rw [toDeckL2, Lp.norm_toLp, Lp.norm_def]
  have h1 := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall hle) 2 (μ := cellMeasure)
  have h2 := eLpNorm_ppApply_le (φ := fun u => |deriv P.toFun u|) P.continuous_deriv.abs
    (fun u => by rw [abs_abs]; exact P.abs_deriv_le u) P.radius_nonneg
    (kernelSupport_abs_deriv P.support) (memLp_normLift (Lp.memLp f))
  rw [eLpNorm_normLift] at h2
  have h3 := h1.trans (mul_le_mul_right h2 _)
  rw [← mul_assoc] at h3
  have hfin : ENNReal.ofReal c * ppKernelMass (fun u => |deriv P.toFun u|) *
      eLpNorm (⇑f) 2 cellMeasure ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.kernelMass_deriv_lt_top.ne)
      (Lp.eLpNorm_ne_top f)
  refine (ENNReal.toReal_mono hfin h3).trans_eq ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]

theorem norm_formLinear_le (f : DeckL2 N) : ‖P.formLinear N f‖ ≤ P.formConst * ‖f‖ := by
  set K₁ := (ppKernelMass (fun u => |deriv P.toFun u|)).toReal
  have hR := P.radius_nonneg
  have h0 : ‖(P.formLinear N f).ofLp 0‖ ≤ (ppKernelMass P.toFun).toReal * ‖f‖ :=
    norm_ppLinear_le P.differentiable.continuous P.abs_le P.radius_nonneg P.support f
  have h1 : ‖(P.formLinear N f).ofLp 1‖ ≤ (2 * P.radius + 1) * K₁ * ‖f‖ :=
    P.norm_gradCoord_le (formPreDomain.memLp_gradX (P.pre f)) (by linarith) f fun z =>
      norm_hypGradX_ppApply_le P.differentiable P.continuous_deriv P.abs_le P.abs_deriv_le
        P.radius_nonneg P.support (Lp.memLp f) z
  have h2 : ‖(P.formLinear N f).ofLp 2‖ ≤ (3 * P.radius + 2) * K₁ * ‖f‖ :=
    P.norm_gradCoord_le (formPreDomain.memLp_gradY (P.pre f)) (by linarith) f fun z =>
      norm_hypGradY_ppApply_le P.differentiable P.continuous_deriv P.abs_le P.abs_deriv_le
        P.radius_nonneg P.support (Lp.memLp f) z
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_three]
  have e : P.formConst * ‖f‖ = (ppKernelMass P.toFun).toReal * ‖f‖ +
      (2 * P.radius + 1) * K₁ * ‖f‖ + (3 * P.radius + 2) * K₁ * ‖f‖ := by
    unfold formConst; ring
  rw [e]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  have a0 := norm_nonneg ((P.formLinear N f).ofLp 0)
  have a1 := norm_nonneg ((P.formLinear N f).ofLp 1)
  have a2 := norm_nonneg ((P.formLinear N f).ofLp 2)
  nlinarith [mul_le_mul h0 h1 a1 (a0.trans h0), mul_le_mul h0 h2 a2 (a0.trans h0),
    mul_le_mul h1 h2 a2 (a1.trans h1), mul_le_mul h0 h0 a0 (a0.trans h0),
    mul_le_mul h1 h1 a1 (a1.trans h1), mul_le_mul h2 h2 a2 (a2.trans h2)]

/-- The bounded form map of a profile. -/
def formMap (N : ℕ) : DeckL2 N →L[ℂ] FormTriple N :=
  LinearMap.mkContinuous (P.formLinear N) P.formConst P.norm_formLinear_le

theorem formMap_ofLp_zero (f : DeckL2 N) : (P.formMap N f).ofLp 0 = P.op N f := rfl

/-- On cuspidal pre-domain vectors the form map lands in the embedded cuspidal pre-domain. -/
theorem formMap_toDeckL2_mem (G : cuspidalFormPreDomain N) :
    P.formMap N (toDeckL2 (G : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp G)) ∈
      LinearMap.range (cuspidalFormEmbeddingMap N) := by
  have hae : ppApply P.toFun ⇑(toDeckL2 (G : ℍ → DeckSpace N) (cuspidalFormPreDomain.memLp G)) =
      ppApply P.toFun (G : ℍ → DeckSpace N) :=
    ppApply_congr_ae _ (MemLp.coeFn_toLp _)
  have hGc : Continuous (G : ℍ → DeckSpace N) := continuous_of_isChartC1 (cuspidalFormPreDomain.c1 G)
  have hmem : ppApply P.toFun (G : ℍ → DeckSpace N) ∈ cuspidalFormPreDomain N := by
    refine ⟨?_, levelCuspZero_ppApply P.differentiable.continuous P.support hGc
      (fun A z => (cuspidalFormPreDomain.toFormPreDomain N G).2.2.1 A z)
      (cuspidalFormPreDomain.cusp_zero G)⟩
    rw [← hae]
    exact P.ppApply_mem _
  refine ⟨⟨_, hmem⟩, ?_⟩
  change formEmbeddingMap N _ = formEmbeddingMap N (P.pre _)
  congr 1
  exact Subtype.ext hae.symm

/-- The form map sends the cuspidal `L²` carrier into the completed cuspidal form domain. -/
theorem formMap_mem_cuspidal (f : CuspidalL2 N) :
    P.formMap N (f : DeckL2 N) ∈ cuspidalFormDomainClosure N := by
  have hclosed : IsClosed (cuspidalFormDomainClosure N : Set (FormTriple N)) :=
    Submodule.isClosed_topologicalClosure _
  have hT : (cuspidalFormDomainClosure N : Set (FormTriple N)) ⊆
      (fun x : FormTriple N => P.formMap N (x.ofLp 0)) ⁻¹' (cuspidalFormDomainClosure N) := by
    have hpre : IsClosed ((fun x : FormTriple N => P.formMap N (x.ofLp 0)) ⁻¹'
        (cuspidalFormDomainClosure N : Set (FormTriple N))) :=
      hclosed.preimage ((P.formMap N).continuous.comp (PiLp.continuous_apply 2 _ 0))
    refine closure_minimal ?_ hpre
    rintro _ ⟨G, rfl⟩
    exact subset_closure (P.formMap_toDeckL2_mem G)
  have hU : (cuspidalL2Closure N : Set (DeckL2 N)) ⊆
      (P.formMap N) ⁻¹' (cuspidalFormDomainClosure N) := by
    refine closure_minimal ?_ (hclosed.preimage (P.formMap N).continuous)
    rintro _ ⟨v, rfl⟩
    exact hT v.2
  exact hU f.2

/-- The form map of a profile, corestricted to the completed cuspidal form domain. -/
def cuspFormMap (N : ℕ) : CuspidalL2 N →L[ℂ] CuspidalFormDomain N :=
  ((P.formMap N).comp (cuspidalL2Closure N).subtypeL).codRestrict (cuspidalFormDomainClosure N)
    fun f => P.formMap_mem_cuspidal f

/-- **The point-pair operator on the cuspidal carrier.** -/
def cuspOp (N : ℕ) : CuspidalL2 N →L[ℂ] CuspidalL2 N :=
  (cuspidalFormInclusionClosure N).comp (P.cuspFormMap N)

theorem coe_cuspOp (f : CuspidalL2 N) : (P.cuspOp N f : DeckL2 N) = P.op N f := rfl

/-- **Compactness.** The point-pair operator factors through the compact cuspidal Rellich
embedding. -/
theorem isCompactOperator_cuspOp : IsCompactOperator (P.cuspOp N) :=
  (isCompactOperator_cuspidalFormInclusionClosure N).comp_clm (P.cuspFormMap N)

theorem cuspOp_isSymmetric :
    ((P.cuspOp N : CuspidalL2 N →L[ℂ] CuspidalL2 N) : CuspidalL2 N →ₗ[ℂ] CuspidalL2 N).IsSymmetric :=
  fun f g => by
    change inner ℂ (P.cuspOp N f : DeckL2 N) (g : DeckL2 N) =
      inner ℂ (f : DeckL2 N) (P.cuspOp N g : DeckL2 N)
    rw [coe_cuspOp, coe_cuspOp]
    exact P.op_isSymmetric N f g

end PairProfile

end

end GaloisForLFunctions.RHTower.DeckPointPair
