import GaloisForLFunctions.ArithmeticIndexDescent.GammaBoundaryHasAnExactSchurWeight

/-!
# Exact square reserve in the arithmetic Gamma boundary bound

The exact positive Schur row turns the mixed boundary bound into an identity.
Its reserve is the integral of the squared difference of the two profiles after
division by the boundary weight. All terms are integrable for arbitrary inputs
of the existing positive-half-line L2 space.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProduct
open RHTower

namespace GaloisForLFunctions.ArithmeticIndexDescent

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

private theorem measurable_boundaryWeight : Measurable gammaBoundarySchurWeight := by
  unfold gammaBoundarySchurWeight
  fun_prop

private theorem ae_positive_pair :
    ∀ᵐ p : ℝ × ℝ ∂(μ₊.prod μ₊), 0 < p.1 ∧ 0 < p.2 := by
  rw [Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)

private theorem integral_boundary_norm_sq (f : SuzukiPositiveL2) :
    (∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2) = ‖f‖ ^ 2 := by
  have h₁ : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [L2.inner_def] at h₁
  have h₂ : (∫ t in Ioi (0 : ℝ), inner ℂ (f t) (f t)) =
      ((∫ t in Ioi (0 : ℝ), ‖f t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h₂] at h₁
  exact_mod_cast h₁

private def boundaryDiagonal (f : SuzukiPositiveL2) (p : ℝ × ℝ) : ℝ :=
  (‖f p.1‖ ^ 2 / gammaBoundarySchurWeight p.1) *
    (archLevyDensity (p.1 + p.2) * gammaBoundarySchurWeight p.2)

private theorem boundaryDiagonal_nonneg (f : SuzukiPositiveL2) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) : 0 ≤ boundaryDiagonal f (s, t) :=
  mul_nonneg (div_nonneg (sq_nonneg _) (gammaBoundarySchurWeight_pos hs).le)
    (mul_nonneg (archLevyDensity_pos (add_pos hs ht)).le
      (gammaBoundarySchurWeight_pos ht).le)

private theorem integral_boundaryDiagonal_row (f : SuzukiPositiveL2) {s : ℝ}
    (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), boundaryDiagonal f (s, t)) =
      (Real.pi / 2) * ‖f s‖ ^ 2 := by
  change (∫ t in Ioi (0 : ℝ), (‖f s‖ ^ 2 / gammaBoundarySchurWeight s) *
    (archLevyDensity (s + t) * gammaBoundarySchurWeight t)) = _
  rw [integral_const_mul, integral_gammaBoundarySchurRow hs]
  field_simp [(gammaBoundarySchurWeight_pos hs).ne']

private theorem integrable_boundaryDiagonal (f : SuzukiPositiveL2) :
    Integrable (boundaryDiagonal f) (μ₊.prod μ₊) := by
  have hf := (Lp.stronglyMeasurable f).measurable
  have hm : Measurable (boundaryDiagonal f) :=
    (((hf.comp measurable_fst).norm.pow_const 2).div
      (measurable_boundaryWeight.comp measurable_fst)).mul
      ((measurable_archLevyDensity.comp (measurable_fst.add measurable_snd)).mul
        (measurable_boundaryWeight.comp measurable_snd))
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (integrableOn_gammaBoundarySchurRow hs).const_mul
      (‖f s‖ ^ 2 / gammaBoundarySchurWeight s)
  · have hi : Integrable (fun s => ‖f s‖ ^ 2) μ₊ :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
    refine (hi.const_mul (Real.pi / 2)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    rw [← integral_boundaryDiagonal_row f hs]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Real.norm_of_nonneg (boundaryDiagonal_nonneg f hs ht)).symm

private theorem integral_boundaryDiagonal (f : SuzukiPositiveL2) :
    (∫ p, boundaryDiagonal f p ∂(μ₊.prod μ₊)) = (Real.pi / 2) * ‖f‖ ^ 2 := by
  rw [integral_prod _ (integrable_boundaryDiagonal f)]
  calc
    _ = ∫ s in Ioi (0 : ℝ), (Real.pi / 2) * ‖f s‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact integral_boundaryDiagonal_row f hs
    _ = _ := by rw [integral_const_mul, integral_boundary_norm_sq]

private theorem integral_boundaryDiagonal_swap (f : SuzukiPositiveL2) :
    (∫ p, boundaryDiagonal f p.swap ∂(μ₊.prod μ₊)) = (Real.pi / 2) * ‖f‖ ^ 2 := by
  rw [integral_prod_swap, integral_boundaryDiagonal]

private def boundaryRealPair (f g : SuzukiPositiveL2) (p : ℝ × ℝ) : ℝ :=
  ((starRingEnd ℂ) (g p.1) * (ccmGammaTranslationDensity (p.1 + p.2) : ℂ) * f p.2).re

private theorem integrable_boundaryRealPair (f g : SuzukiPositiveL2) :
    Integrable (boundaryRealPair f g) (μ₊.prod μ₊) :=
  (integrable_ccmGammaBoundary_pair f g).re

private theorem integral_boundaryRealPair (f g : SuzukiPositiveL2) :
    (∫ p, boundaryRealPair f g p ∂(μ₊.prod μ₊)) =
      (inner ℂ g (ccmGammaBoundaryCLM f)).re := by
  have hre := integral_re (integrable_ccmGammaBoundary_pair f g)
  simp only [RCLike.re_to_complex] at hre
  unfold boundaryRealPair
  rw [hre,
    integral_prod _ (integrable_ccmGammaBoundary_pair f g), ← inner_ccmGammaBoundaryCLM]

private theorem weighted_complex_difference (z v : ℂ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    a * b * ‖z / (a : ℂ) - v / (b : ℂ)‖ ^ 2 =
      b / a * ‖z‖ ^ 2 + a / b * ‖v‖ ^ 2 - 2 * ((starRingEnd ℂ) z * v).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  field_simp [ha.ne', hb.ne']
  ring

/-- The nonnegative mixed reserve of the exact Gamma boundary bound. -/
def gammaBoundaryPairReserveDensity (f g : SuzukiPositiveL2) (p : ℝ × ℝ) : ℝ :=
  archLevyDensity (p.1 + p.2) * gammaBoundarySchurWeight p.1 *
    gammaBoundarySchurWeight p.2 *
      ‖g p.1 / (gammaBoundarySchurWeight p.1 : ℂ) -
        f p.2 / (gammaBoundarySchurWeight p.2 : ℂ)‖ ^ 2 / 2

theorem gammaBoundaryPairReserveDensity_nonneg (f g : SuzukiPositiveL2) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) : 0 ≤ gammaBoundaryPairReserveDensity f g (s, t) := by
  exact div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (archLevyDensity_pos (add_pos hs ht)).le
      (gammaBoundarySchurWeight_pos hs).le) (gammaBoundarySchurWeight_pos ht).le)
        (sq_nonneg _)) (by norm_num)

private theorem boundaryPairReserve_eq (f g : SuzukiPositiveL2) {s t : ℝ}
    (hs : 0 < s) (ht : 0 < t) :
    gammaBoundaryPairReserveDensity f g (s, t) =
      (boundaryDiagonal g (s, t) + boundaryDiagonal f (t, s)) / 2 -
        boundaryRealPair f g (s, t) := by
  have h := weighted_complex_difference (g s) (f t)
    (gammaBoundarySchurWeight_pos hs) (gammaBoundarySchurWeight_pos ht)
  have hden : ccmGammaTranslationDensity (s + t) = archLevyDensity (s + t) := by
    simp only [ccmGammaTranslationDensity, archLevyDensity, neg_div, neg_mul]
  unfold gammaBoundaryPairReserveDensity boundaryDiagonal boundaryRealPair
  dsimp only
  rw [show archLevyDensity (s + t) * gammaBoundarySchurWeight s *
      gammaBoundarySchurWeight t *
        ‖g s / (gammaBoundarySchurWeight s : ℂ) -
          f t / (gammaBoundarySchurWeight t : ℂ)‖ ^ 2 / 2 =
      (archLevyDensity (s + t) / 2) *
        (gammaBoundarySchurWeight s * gammaBoundarySchurWeight t *
          ‖g s / (gammaBoundarySchurWeight s : ℂ) -
            f t / (gammaBoundarySchurWeight t : ℂ)‖ ^ 2) by ring, h, hden, add_comm t s]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, mul_zero, sub_zero, zero_add]
  ring

private theorem boundaryPairReserve_ae (f g : SuzukiPositiveL2) :
    gammaBoundaryPairReserveDensity f g =ᵐ[μ₊.prod μ₊]
      fun p => (boundaryDiagonal g p + boundaryDiagonal f p.swap) / 2 -
        boundaryRealPair f g p := by
  filter_upwards [ae_positive_pair] with p hp
  exact boundaryPairReserve_eq f g hp.1 hp.2

/-- The exact square reserve is finite for every pair in the original L2 carrier. -/
theorem integrable_gammaBoundaryPairReserveDensity (f g : SuzukiPositiveL2) :
    Integrable (gammaBoundaryPairReserveDensity f g) (μ₊.prod μ₊) :=
  (((integrable_boundaryDiagonal g).add (integrable_boundaryDiagonal f).swap).div_const 2
    |>.sub (integrable_boundaryRealPair f g)).congr (boundaryPairReserve_ae f g).symm

/-- Exact mixed Schur payment: the unused mass bound is a weighted difference square. -/
theorem integral_gammaBoundaryPairReserveDensity (f g : SuzukiPositiveL2) :
    (∫ p, gammaBoundaryPairReserveDensity f g p ∂(μ₊.prod μ₊)) =
      (Real.pi / 4) * (‖f‖ ^ 2 + ‖g‖ ^ 2) -
        (inner ℂ g (ccmGammaBoundaryCLM f)).re := by
  have hs : Integrable (fun p : ℝ × ℝ => boundaryDiagonal f p.swap) (μ₊.prod μ₊) :=
    (integrable_boundaryDiagonal f).swap
  have ha : Integrable
      (fun p : ℝ × ℝ => boundaryDiagonal g p + boundaryDiagonal f p.swap)
      (μ₊.prod μ₊) := (integrable_boundaryDiagonal g).add hs
  have hd : Integrable
      (fun p : ℝ × ℝ => (boundaryDiagonal g p + boundaryDiagonal f p.swap) / 2)
      (μ₊.prod μ₊) := ha.div_const 2
  rw [integral_congr_ae (boundaryPairReserve_ae f g),
    integral_sub hd (integrable_boundaryRealPair f g), integral_div,
    integral_add (integrable_boundaryDiagonal g) hs,
    integral_boundaryDiagonal, integral_boundaryDiagonal_swap, integral_boundaryRealPair]
  ring

/-- The quadratic Gamma deficit on the actual L2 space retains its entire square reserve. -/
theorem gammaBoundary_quadratic_deficit (f : SuzukiPositiveL2) :
    (Real.pi / 2) * ‖f‖ ^ 2 - (inner ℂ f (ccmGammaBoundaryCLM f)).re =
      ∫ p, gammaBoundaryPairReserveDensity f f p ∂(μ₊.prod μ₊) := by
  rw [integral_gammaBoundaryPairReserveDensity]
  ring

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integrable_gammaBoundaryPairReserveDensity
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.integral_gammaBoundaryPairReserveDensity
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.gammaBoundary_quadratic_deficit
