import GaloisForLFunctions.RHTower.XiCTaylorThetaTailArithmeticTranslate
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCorrelation

/-!
# Arithmetic atom expansion of the theta-tail core current

This module keeps the complete canonical density while resolving it into its exact logarithmic
integer translates.  The first theorem supplies the missing `L¹` justification for exchanging
the positive atom sum with every raw moment integral.  Subsequent definitions package the value
and derivative contributed by a single atom; their absolutely convergent pair expansion is the
correct starting point for any theta-specific cancellation argument.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Every raw moment of the complete differentiated theta-tail density is the sum of the
corresponding positive-index atom moments.  In particular, the atom moment sequence is summable;
this is the `L¹` input needed for finite core atom expansions. -/
theorem integral_pow_mul_thetaCuspTailSecondDensity_eq_tsum_atomMoment
    (m : ℕ) :
    (∫ x : ℝ in Ioi 0, x ^ m * thetaCuspTailSecondDensity x) =
      ∑' n : ℕ, thetaCuspTailSecondDensityAtomMoment (n + 1) m := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℝ := fun n x =>
    x ^ m * thetaCuspTailSecondDensityAtom (n + 1) x
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact ((by
      dsimp [F]
      unfold thetaCuspTailSecondDensityAtom thetaCuspPolynomialAtom
      fun_prop : Continuous (F n))).aestronglyMeasurable
  have hfull : Integrable
      (fun x : ℝ => x ^ m * thetaCuspTailSecondDensity x) mu :=
    integrableOn_pow_mul_thetaCuspTailSecondDensity m
  have hnormsum : ∀ᵐ x ∂mu,
      (∑' n : ℕ, ‖F n x‖₊) =
        ‖x ^ m * thetaCuspTailSecondDensity x‖₊ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hterm (n : ℕ) : 0 ≤ F n x :=
      mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos n) hx.le).le
    have hatom : Summable
        (fun n : ℕ => thetaCuspTailSecondDensityAtom (n + 1) x) := by
      unfold thetaCuspTailSecondDensityAtom
      simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
    have hsum : Summable (fun n : ℕ => F n x) := by
      simpa only [F] using hatom.mul_left (x ^ m)
    apply NNReal.eq
    rw [NNReal.coe_tsum]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    simp_rw [abs_of_nonneg (hterm _)]
    rw [abs_of_nonneg]
    · calc
        (∑' n : ℕ, F n x) =
            x ^ m * (∑' n : ℕ,
              thetaCuspTailSecondDensityAtom (n + 1) x) := by
                simpa only [F] using
                  Summable.tsum_mul_left (x ^ m) hatom
        _ = x ^ m * thetaCuspTailSecondDensity x := by
          rw [thetaCuspTailSecondDensity_eq_tsum_atom]
    · exact mul_nonneg (pow_nonneg hx.le _)
        (thetaCuspTailSecondDensity_pos hx).le
  have hnormsumE : ∀ᵐ x ∂mu,
      (∑' n : ℕ, ‖F n x‖ₑ) =
        ‖x ^ m * thetaCuspTailSecondDensity x‖ₑ := by
    filter_upwards [hnormsum] with x hx
    have hatom : Summable
        (fun n : ℕ => thetaCuspTailSecondDensityAtom (n + 1) x) := by
      unfold thetaCuspTailSecondDensityAtom
      simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
    have hsum : Summable (fun n : ℕ => F n x) := by
      simpa only [F] using hatom.mul_left (x ^ m)
    have hnorm : Summable (fun n : ℕ => ‖F n x‖₊) := by
      exact NNReal.summable_coe.mp (by
        simpa only [coe_nnnorm] using hsum.norm)
    calc
      (∑' n : ℕ, ‖F n x‖ₑ) =
          ((∑' n : ℕ, ‖F n x‖₊ : NNReal) : ENNReal) := by
            exact (ENNReal.coe_tsum hnorm).symm
      _ = (‖x ^ m * thetaCuspTailSecondDensity x‖₊ : ENNReal) := by
        rw [hx]
      _ = ‖x ^ m * thetaCuspTailSecondDensity x‖ₑ := rfl
  have hfinite : (∑' n : ℕ, ∫⁻ x, ‖F n x‖ₑ ∂mu) ≠ ⊤ := by
    rw [← lintegral_tsum (fun n => (hFmeas n).enorm)]
    rw [lintegral_congr_ae hnormsumE]
    exact ne_of_lt hfull.hasFiniteIntegral
  have hswap := integral_tsum hFmeas hfinite
  change (∫ x : ℝ, x ^ m * thetaCuspTailSecondDensity x ∂mu) = _
  rw [show (fun x : ℝ => x ^ m * thetaCuspTailSecondDensity x) =
      fun x => ∑' n, F n x by
    funext x
    have hatom : Summable
        (fun n : ℕ => thetaCuspTailSecondDensityAtom (n + 1) x) := by
      unfold thetaCuspTailSecondDensityAtom
      simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4
    calc
      x ^ m * thetaCuspTailSecondDensity x =
          x ^ m * (∑' n : ℕ,
            thetaCuspTailSecondDensityAtom (n + 1) x) := by
              rw [thetaCuspTailSecondDensity_eq_tsum_atom]
      _ = ∑' n : ℕ, F n x := by
        simpa only [F] using
          (Summable.tsum_mul_left (x ^ m) hatom).symm]
  rw [hswap]
  apply tsum_congr
  intro n
  rfl

/-- The symmetric correlation kernel is integrable against the product of the two positive
half-line measures. -/
theorem integrable_xiCTaylorThetaTailCoreSymmetricCorrelationKernel
    (d : ℕ) (z : ℂ) :
    Integrable (xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  let g : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensity x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x
  have hf : Integrable f mu :=
    integrableOn_thetaCuspTailSecondDensity_mul_coreAtomDerivative d z
  have hg : Integrable g mu :=
    integrableOn_thetaCuspTailSecondDensity_mul_coreAtom d z
  have hgconj : Integrable (fun x => (starRingEnd ℂ) (g x)) mu :=
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg
  have hcorr : Integrable (xiCTaylorThetaTailCoreCorrelationKernel d z)
      (mu.prod mu) := by
    have hprod : Integrable (fun p : ℝ × ℝ =>
        f p.1 * (starRingEnd ℂ) (g p.2)) (mu.prod mu) :=
      hf.mul_prod hgconj
    simpa only [f, g, xiCTaylorThetaTailCoreCorrelationKernel] using hprod.im
  have hswap : Integrable
      (fun p : ℝ × ℝ => xiCTaylorThetaTailCoreCorrelationKernel d z p.swap)
      (mu.prod mu) := by
    simpa only [Function.comp_apply] using hcorr.swap
  rw [show xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z =
      fun p => (1 / 2 : ℝ) *
        (xiCTaylorThetaTailCoreCorrelationKernel d z p +
          xiCTaylorThetaTailCoreCorrelationKernel d z p.swap) by
    funext p
    unfold xiCTaylorThetaTailCoreSymmetricCorrelationKernel
    ring]
  exact (hcorr.add hswap).const_mul (1 / 2 : ℝ)

/-- The contribution of one ordered pair of positive-index theta atoms to the symmetric core
correlation. -/
def xiCTaylorThetaTailCoreAtomPairCorrelationKernel
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  thetaCuspTailSecondDensityAtom (q.1 + 1) p.1 *
    thetaCuspTailSecondDensityAtom (q.2 + 1) p.2 *
      xiCTaylorThetaTailCorePairCurrent d z p

theorem summable_thetaCuspTailSecondDensityAtom (x : ℝ) :
    Summable (fun n : ℕ => thetaCuspTailSecondDensityAtom (n + 1) x) := by
  unfold thetaCuspTailSecondDensityAtom
  simpa only using (summable_thetaCuspTailDerivative 2 x).mul_left 4

theorem summable_thetaCuspTailSecondDensityAtom_pair (x y : ℝ) :
    Summable (fun q : ℕ × ℕ =>
      thetaCuspTailSecondDensityAtom (q.1 + 1) x *
        thetaCuspTailSecondDensityAtom (q.2 + 1) y) :=
  summable_mul_of_summable_norm
    (summable_thetaCuspTailSecondDensityAtom x).norm
    (summable_thetaCuspTailSecondDensityAtom y).norm

/-- The product of the two complete densities is the absolutely convergent ordered atom-pair
sum. -/
theorem thetaCuspTailSecondDensity_mul_eq_tsum_atomPair
    (x y : ℝ) :
    thetaCuspTailSecondDensity x * thetaCuspTailSecondDensity y =
      ∑' q : ℕ × ℕ,
        thetaCuspTailSecondDensityAtom (q.1 + 1) x *
          thetaCuspTailSecondDensityAtom (q.2 + 1) y := by
  have hx := summable_thetaCuspTailSecondDensityAtom x
  have hy := summable_thetaCuspTailSecondDensityAtom y
  rw [thetaCuspTailSecondDensity_eq_tsum_atom,
    thetaCuspTailSecondDensity_eq_tsum_atom]
  exact tsum_mul_tsum_of_summable_norm hx.norm hy.norm

/-- Pointwise, the full symmetric correlation is exactly the ordered atom-pair sum. -/
theorem xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_atomPair
    (d : ℕ) (z : ℂ) (p : ℝ × ℝ) :
    xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p =
      ∑' q : ℕ × ℕ,
        xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p := by
  rw [xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul]
  unfold xiCTaylorThetaTailCoreAtomPairCorrelationKernel
  rw [thetaCuspTailSecondDensity_mul_eq_tsum_atomPair]
  exact (summable_mul_of_summable_norm
    (summable_thetaCuspTailSecondDensityAtom p.1).norm
    (summable_thetaCuspTailSecondDensityAtom p.2).norm).tsum_mul_right
      (xiCTaylorThetaTailCorePairCurrent d z p) |>.symm

/-- The full symmetric correlation integral is the ordered sum of its exact atom-pair
integrals.  The proof uses the full density as the `L¹` majorant, so no sign is discarded. -/
theorem integral_xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_atomPair
    (d : ℕ) (z : ℂ) :
    (∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ∑' q : ℕ × ℕ,
        ∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let mu : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))
  let F : (ℕ × ℕ) → (ℝ × ℝ) → ℝ := fun q p =>
    xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
  have hFmeas : ∀ q, AEStronglyMeasurable (F q) mu := by
    intro q
    exact ((by
      dsimp [F]
      unfold xiCTaylorThetaTailCoreAtomPairCorrelationKernel
        xiCTaylorThetaTailCorePairCurrent
        thetaCuspTailSecondCoreAtomDerivative
        thetaCuspTailSecondCoreAtom
        thetaCuspTailSecondSectionDerivative
        thetaCuspTailSecondSection
        thetaCuspTailSecondDensityAtom thetaCuspPolynomialAtom
      fun_prop : Continuous (F q))).aestronglyMeasurable
  have hfull : Integrable
      (xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z) mu :=
    integrable_xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z
  have hmem : ∀ᵐ p ∂mu, p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
    dsimp [mu]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hnormsum : ∀ᵐ p ∂mu,
      (∑' q : ℕ × ℕ, ‖F q p‖₊) =
        ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖₊ := by
    filter_upwards [hmem] with p hp
    have hx : 0 < p.1 := hp.1
    have hy : 0 < p.2 := hp.2
    let A : (ℕ × ℕ) → ℝ := fun q =>
      thetaCuspTailSecondDensityAtom (q.1 + 1) p.1 *
        thetaCuspTailSecondDensityAtom (q.2 + 1) p.2
    let K : ℝ := xiCTaylorThetaTailCorePairCurrent d z p
    have hA0 (q : ℕ × ℕ) : 0 ≤ A q := by
      exact mul_nonneg
        (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos q.1) hx.le).le
        (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos q.2) hy.le).le
    have hAsum : Summable A := by
      exact summable_thetaCuspTailSecondDensityAtom_pair p.1 p.2
    have hAnn : Summable (fun q => (A q).toNNReal) := by
      apply NNReal.summable_coe.mp
      simpa only [Real.coe_toNNReal _ (hA0 _)] using hAsum
    have hFnorm (q : ℕ × ℕ) :
        ‖F q p‖₊ = (A q).toNNReal * ‖K‖₊ := by
      apply NNReal.eq
      change |A q * K| = ↑((A q).toNNReal * ‖K‖₊)
      rw [abs_mul, abs_of_nonneg (hA0 q)]
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (hA0 q), coe_nnnorm,
        Real.norm_eq_abs]
    have hAtsum : (∑' q, A q) =
        thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 := by
      exact (thetaCuspTailSecondDensity_mul_eq_tsum_atomPair p.1 p.2).symm
    have hfull0 :
        0 ≤ thetaCuspTailSecondDensity p.1 * thetaCuspTailSecondDensity p.2 :=
      mul_nonneg (thetaCuspTailSecondDensity_pos hx).le
        (thetaCuspTailSecondDensity_pos hy).le
    have hAnnTsum : (∑' q, (A q).toNNReal) =
        (thetaCuspTailSecondDensity p.1 *
          thetaCuspTailSecondDensity p.2).toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_tsum]
      · simp only [Real.coe_toNNReal _ (hA0 _), Real.coe_toNNReal _ hfull0]
        exact hAtsum
    calc
      (∑' q, ‖F q p‖₊) =
          ∑' q, (A q).toNNReal * ‖K‖₊ := by
            apply tsum_congr
            exact hFnorm
      _ = (∑' q, (A q).toNNReal) * ‖K‖₊ :=
        hAnn.tsum_mul_right ‖K‖₊
      _ = (thetaCuspTailSecondDensity p.1 *
          thetaCuspTailSecondDensity p.2).toNNReal * ‖K‖₊ := by
        rw [hAnnTsum]
      _ = ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖₊ := by
        apply NNReal.eq
        rw [xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_density_mul]
        simp only [NNReal.coe_mul, Real.coe_toNNReal _ hfull0, coe_nnnorm,
          Real.norm_eq_abs, abs_mul, abs_of_nonneg hfull0]
        rfl
  have hnormsumE : ∀ᵐ p ∂mu,
      (∑' q : ℕ × ℕ, ‖F q p‖ₑ) =
        ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖ₑ := by
    filter_upwards [hnormsum, hmem] with p hpNorm hp
    have hx : 0 < p.1 := hp.1
    have hy : 0 < p.2 := hp.2
    let A : (ℕ × ℕ) → ℝ := fun q =>
        thetaCuspTailSecondDensityAtom (q.1 + 1) p.1 *
          thetaCuspTailSecondDensityAtom (q.2 + 1) p.2
    let K : ℝ := xiCTaylorThetaTailCorePairCurrent d z p
    have hA0 (q : ℕ × ℕ) : 0 ≤ A q := by
      exact mul_nonneg
        (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos q.1) hx.le).le
        (thetaCuspTailSecondDensityAtom_pos (Nat.succ_pos q.2) hy.le).le
    have hAsum : Summable A := by
      exact summable_thetaCuspTailSecondDensityAtom_pair p.1 p.2
    have hAnn : Summable (fun q => (A q).toNNReal) := by
      apply NNReal.summable_coe.mp
      simpa only [Real.coe_toNNReal _ (hA0 _)] using hAsum
    have hFnorm (q : ℕ × ℕ) :
        ‖F q p‖₊ = (A q).toNNReal * ‖K‖₊ := by
      apply NNReal.eq
      change |A q * K| = ↑((A q).toNNReal * ‖K‖₊)
      rw [abs_mul, abs_of_nonneg (hA0 q)]
      simp only [NNReal.coe_mul, Real.coe_toNNReal _ (hA0 q), coe_nnnorm,
        Real.norm_eq_abs]
    have hnorm : Summable (fun q => ‖F q p‖₊) := by
      exact (hAnn.mul_right ‖K‖₊).congr (fun q => hFnorm q |>.symm)
    calc
      (∑' q : ℕ × ℕ, ‖F q p‖ₑ) =
          ((∑' q : ℕ × ℕ, ‖F q p‖₊ : NNReal) : ENNReal) := by
            exact (ENNReal.coe_tsum hnorm).symm
      _ = (‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖₊ : ENNReal) := by
        rw [hpNorm]
      _ = ‖xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p‖ₑ := rfl
  have hfinite : (∑' q : ℕ × ℕ, ∫⁻ p, ‖F q p‖ₑ ∂mu) ≠ ⊤ := by
    rw [← lintegral_tsum (fun q => (hFmeas q).enorm)]
    rw [lintegral_congr_ae hnormsumE]
    exact ne_of_lt hfull.hasFiniteIntegral
  have hswap := integral_tsum hFmeas hfinite
  change (∫ p : ℝ × ℝ,
      xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z p ∂mu) = _
  rw [show xiCTaylorThetaTailCoreSymmetricCorrelationKernel d z =
      fun p => ∑' q, F q p by
    funext p
    exact xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_atomPair d z p]
  exact hswap

/-- Exact ordered atom-pair expansion of the theta-tail core current. -/
theorem xiCTaylorThetaTailCore_current_eq_tsum_atomPairIntegral
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∑' q : ℕ × ℕ,
          ∫ p : ℝ × ℝ,
            xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
              ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  rw [xiCTaylorThetaTailCore_current_eq_symmetricCorrelationIntegral,
    integral_xiCTaylorThetaTailCoreSymmetricCorrelationKernel_eq_tsum_atomPair]

/-- The one-profile logarithmic-translate kernel attached to an ordered pair of positive
integers.  The arithmetic weights are kept outside this definition. -/
def xiCTaylorThetaTailCoreArithmeticTranslatePairKernel
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  thetaCuspTailSecondDensityAtom 1
      (p.1 + Real.log (q.1 + 1 : ℕ)) *
    thetaCuspTailSecondDensityAtom 1
      (p.2 + Real.log (q.2 + 1 : ℕ)) *
      xiCTaylorThetaTailCorePairCurrent d z p

/-- Each atom-pair kernel is exactly one shifted canonical profile pair with the two critical
weights. -/
theorem xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_arithmeticTranslate
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) (p : ℝ × ℝ) :
    xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p =
      ((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          xiCTaylorThetaTailCoreArithmeticTranslatePairKernel d z q p := by
  unfold xiCTaylorThetaTailCoreAtomPairCorrelationKernel
    xiCTaylorThetaTailCoreArithmeticTranslatePairKernel
  rw [thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate (Nat.succ_pos q.1),
    thetaCuspTailSecondDensityAtom_eq_rpow_mul_translate (Nat.succ_pos q.2)]
  ring

/-- Integrated arithmetic-translate form of one exact atom-pair contribution. -/
theorem integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_arithmeticTranslate
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) :
    (∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      (((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
        ∫ p : ℝ × ℝ,
          xiCTaylorThetaTailCoreArithmeticTranslatePairKernel d z q p
            ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  rw [show (fun p : ℝ × ℝ =>
      xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p) =
      fun p => (((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          xiCTaylorThetaTailCoreArithmeticTranslatePairKernel d z q p by
    funext p
    rw [xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_arithmeticTranslate]]
  exact MeasureTheory.integral_const_mul _ _

/-- Exact one-profile arithmetic-translate pair expansion of the theta-tail core current.  This
identity retains all cancellations among the logarithmic integer shifts. -/
theorem xiCTaylorThetaTailCore_current_eq_tsum_arithmeticTranslatePairIntegral
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∑' q : ℕ × ℕ,
          (((q.1 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
            ((q.2 + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
              ∫ p : ℝ × ℝ,
                xiCTaylorThetaTailCoreArithmeticTranslatePairKernel d z q p
                  ∂((volume.restrict (Ioi 0)).prod
                    (volume.restrict (Ioi 0))) := by
  rw [xiCTaylorThetaTailCore_current_eq_tsum_atomPairIntegral]
  congr 1
  apply tsum_congr
  intro q
  exact integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_arithmeticTranslate d z q

end

end RHTower
