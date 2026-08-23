import GaloisForLFunctions.HTGeometry.CirclePoissonProductSingularity
import GaloisForLFunctions.HTGeometry.L2PairingEnergy
import GaloisForLFunctions.HTGeometry.BohrMultiFejerOperator
import GaloisForLFunctions.HTGeometry.NevanlinnaTransferMinimalType

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

noncomputable section

local instance : MeasurableSpace Circle :=
  instMeasurableSpaceCircle_galoisForLFunctions

theorem circlePoissonHalfDensity_pos (a : CirclePoissonParameter) (z : Circle) :
    0 < circlePoissonHalfDensity a z := by
  apply Real.sqrt_pos.2
  exact poissonKernel_pos (c := 0) (R := 1)
    (by rw [mem_sphere_iff_norm, sub_zero, Circle.norm_coe]) a.2

theorem circlePoissonHellingerAffinity_comm
    (a b : CirclePoissonParameter) :
    circlePoissonHellingerAffinity a b = circlePoissonHellingerAffinity b a := by
  simp only [circlePoissonHellingerAffinity, mul_comm]

/-- Real-valued integration against a circle Poisson law is Haar integration weighted by its
Poisson density. -/
theorem integral_circlePoissonMeasure_real_eq (b : CirclePoissonParameter)
    (f : Circle → ℝ) :
    ∫ z, f z ∂circlePoissonMeasure b =
      ∫ z, f z * poissonKernel 0 (b : ℂ) (z : ℂ) ∂circleLebesgue := by
  have hdens : AEMeasurable (circlePoissonDensity b) circleLebesgue :=
    (ENNReal.continuous_ofReal.comp (continuous_circlePoissonDensity_real b)).measurable.aemeasurable
  have hdensTop : ∀ᵐ z ∂circleLebesgue, circlePoissonDensity b z < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [circlePoissonMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hdens hdensTop]
  apply integral_congr_ae
  filter_upwards with z
  rw [circlePoissonDensity, ENNReal.toReal_ofReal (circlePoissonDensity_nonneg b z)]
  simp only [smul_eq_mul]
  ring

/-- Square root of the local Radon--Nikodym likelihood. -/
def circlePoissonHalfLikelihood
    (a b : CirclePoissonParameter) (z : Circle) : ℝ :=
  circlePoissonHalfDensity a z / circlePoissonHalfDensity b z

theorem continuous_circlePoissonHalfLikelihood (a b : CirclePoissonParameter) :
    Continuous (circlePoissonHalfLikelihood a b) := by
  exact (continuous_circlePoissonHalfDensity a).div
    (continuous_circlePoissonHalfDensity b) (fun z => ne_of_gt (circlePoissonHalfDensity_pos b z))

theorem circlePoissonHalfLikelihood_pos
    (a b : CirclePoissonParameter) (z : Circle) :
    0 < circlePoissonHalfLikelihood a b z :=
  div_pos (circlePoissonHalfDensity_pos a z) (circlePoissonHalfDensity_pos b z)

theorem integral_sq_circlePoissonHalfLikelihood
    (a b : CirclePoissonParameter) :
    ∫ z, circlePoissonHalfLikelihood a b z ^ 2 ∂circlePoissonMeasure b = 1 := by
  rw [integral_circlePoissonMeasure_real_eq b]
  have hpoint : (fun z : Circle => circlePoissonHalfLikelihood a b z ^ 2 *
      poissonKernel 0 (b : ℂ) (z : ℂ)) =
      fun z => circlePoissonHalfDensity a z ^ 2 := by
    funext z
    rw [circlePoissonHalfLikelihood, ← circlePoissonHalfDensity_sq b z]
    field_simp [ne_of_gt (circlePoissonHalfDensity_pos b z)]
  rw [hpoint, integral_sq_circlePoissonHalfDensity]

theorem integral_circlePoissonHalfLikelihood
    (a b : CirclePoissonParameter) :
    ∫ z, circlePoissonHalfLikelihood a b z ∂circlePoissonMeasure b =
      circlePoissonHellingerAffinity a b := by
  rw [integral_circlePoissonMeasure_real_eq b]
  have hpoint : (fun z : Circle => circlePoissonHalfLikelihood a b z *
      poissonKernel 0 (b : ℂ) (z : ℂ)) =
      fun z => circlePoissonHalfDensity a z * circlePoissonHalfDensity b z := by
    funext z
    rw [circlePoissonHalfLikelihood, ← circlePoissonHalfDensity_sq b z]
    field_simp [ne_of_gt (circlePoissonHalfDensity_pos b z)]
  rw [hpoint]
  rfl

/-- A finite coordinate product integrates against an infinite product law as the product of its
local integrals. -/
theorem integral_finset_coordProd_natCirclePoissonProduct
    (b : ℕ → CirclePoissonParameter) (S : Finset ℕ)
    (f : ↑S → Circle → ℝ) (hf : ∀ n, Continuous (f n)) :
    ∫ x, ∏ n : ↑S, f n (x n) ∂natCirclePoissonProductMeasure b =
      ∏ n : ↑S, ∫ z, f n z ∂circlePoissonMeasure (b n) := by
  have hfinite : Continuous (fun y : ↑S → Circle => ∏ n : ↑S, f n (y n)) := by
    exact continuous_finsetProd Finset.univ fun n _ => (hf n).comp (continuous_apply n)
  rw [natCirclePoissonProductMeasure]
  change (∫ x, (fun y : ↑S → Circle => ∏ n : ↑S, f n (y n)) (S.restrict x)
      ∂Measure.infinitePi fun n => circlePoissonMeasure (b n)) = _
  rw [integral_restrict_infinitePi (fun n => circlePoissonMeasure (b n))
    hfinite.aestronglyMeasurable]
  exact integral_fintype_prod_eq_prod f

/-- Finite-prefix square-root likelihood, viewed on the full natural-index product. -/
def circlePoissonPrefixHalfLikelihood
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) (x : ℕ → Circle) : ℝ :=
  ∏ n : ↑(Finset.range N), circlePoissonHalfLikelihood (a n) (b n) (x n)

theorem continuous_circlePoissonPrefixHalfLikelihood
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    Continuous (circlePoissonPrefixHalfLikelihood a b N) := by
  unfold circlePoissonPrefixHalfLikelihood
  exact continuous_finsetProd Finset.univ fun n _ =>
    (continuous_circlePoissonHalfLikelihood (a n) (b n)).comp
      (continuous_apply (n : ℕ))

theorem circlePoissonPrefixHalfLikelihood_pos
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) (x : ℕ → Circle) :
    0 < circlePoissonPrefixHalfLikelihood a b N x :=
  Finset.prod_pos fun n _ => circlePoissonHalfLikelihood_pos (a n) (b n) (x n)

theorem integral_sq_circlePoissonPrefixHalfLikelihood
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    ∫ x, circlePoissonPrefixHalfLikelihood a b N x ^ 2
        ∂natCirclePoissonProductMeasure b = 1 := by
  have h := integral_finset_coordProd_natCirclePoissonProduct b (Finset.range N)
    (fun n z => circlePoissonHalfLikelihood (a n) (b n) z ^ 2)
    (fun n => (continuous_circlePoissonHalfLikelihood (a n) (b n)).pow 2)
  rw [show (fun x : ℕ → Circle => circlePoissonPrefixHalfLikelihood a b N x ^ 2) =
      fun x => ∏ n : ↑(Finset.range N),
        circlePoissonHalfLikelihood (a n) (b n) (x n) ^ 2 by
    funext x
    simp only [circlePoissonPrefixHalfLikelihood, pow_two, Finset.prod_mul_distrib]]
  rw [h]
  simp_rw [integral_sq_circlePoissonHalfLikelihood]
  simp

theorem memLp_two_circlePoissonPrefixHalfLikelihood
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    MemLp (circlePoissonPrefixHalfLikelihood a b N) 2
      (natCirclePoissonProductMeasure b) := by
  rw [memLp_two_iff_integrable_sq_norm
    (continuous_circlePoissonPrefixHalfLikelihood a b N).aestronglyMeasurable]
  have heq : (fun x => ‖circlePoissonPrefixHalfLikelihood a b N x‖ ^ 2) =
      fun x => circlePoissonPrefixHalfLikelihood a b N x ^ 2 := by
    funext x
    rw [Real.norm_eq_abs, sq_abs]
  rw [heq]
  exact ((continuous_circlePoissonPrefixHalfLikelihood a b N).pow 2).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

private theorem circlePoissonPrefixHalfLikelihood_eq_prod_range
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) (x : ℕ → Circle) :
    circlePoissonPrefixHalfLikelihood a b N x =
      ∏ n ∈ Finset.range N, circlePoissonHalfLikelihood (a n) (b n) (x n) :=
  Finset.prod_attach (Finset.range N)
    (fun n => circlePoissonHalfLikelihood (a n) (b n) (x n))

private def circlePoissonCrossLocal
    (a b : ℕ → CirclePoissonParameter) (M n : ℕ) (z : Circle) : ℝ :=
  if n < M then circlePoissonHalfLikelihood (a n) (b n) z ^ 2
  else circlePoissonHalfLikelihood (a n) (b n) z

private theorem continuous_circlePoissonCrossLocal
    (a b : ℕ → CirclePoissonParameter) (M n : ℕ) :
    Continuous (circlePoissonCrossLocal a b M n) := by
  by_cases h : n < M
  · have heq : circlePoissonCrossLocal a b M n =
        (circlePoissonHalfLikelihood (a n) (b n)) ^ 2 := by
      funext z
      simp [circlePoissonCrossLocal, h]
    rw [heq]
    exact (continuous_circlePoissonHalfLikelihood (a n) (b n)).pow 2
  · have heq : circlePoissonCrossLocal a b M n =
        circlePoissonHalfLikelihood (a n) (b n) := by
      funext z
      simp [circlePoissonCrossLocal, h]
    rw [heq]
    exact continuous_circlePoissonHalfLikelihood (a n) (b n)

private theorem prefixHalfLikelihood_mul_eq_crossLocal_prod
    (a b : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) (x : ℕ → Circle) :
    circlePoissonPrefixHalfLikelihood a b M x *
        circlePoissonPrefixHalfLikelihood a b N x =
      ∏ n : ↑(Finset.range N), circlePoissonCrossLocal a b M n (x n) := by
  rw [circlePoissonPrefixHalfLikelihood_eq_prod_range,
    circlePoissonPrefixHalfLikelihood_eq_prod_range]
  rw [show (∏ n : ↑(Finset.range N), circlePoissonCrossLocal a b M n (x n)) =
      ∏ n ∈ Finset.range N, circlePoissonCrossLocal a b M n (x n) from
    Finset.prod_attach (Finset.range N)
      (fun n => circlePoissonCrossLocal a b M n (x n))]
  let L : ℕ → ℝ := fun n => circlePoissonHalfLikelihood (a n) (b n) (x n)
  have hsub : Finset.range M ⊆ Finset.range N := Finset.range_mono hMN
  have hdiff : Finset.range N \ Finset.range M = Finset.Ico M N := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
    omega
  have hsplit := Finset.prod_sdiff (f := L) hsub
  rw [hdiff] at hsplit
  change (∏ n ∈ Finset.range M, L n) * (∏ n ∈ Finset.range N, L n) = _
  rw [← hsplit]
  have hcross : (∏ n ∈ Finset.range N, circlePoissonCrossLocal a b M n (x n)) =
      (∏ n ∈ Finset.range M, L n ^ 2) * ∏ n ∈ Finset.Ico M N, L n := by
    have hunion : Finset.range M ∪ Finset.Ico M N = Finset.range N := by
      ext n
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (Finset.range M) (Finset.Ico M N) :=
      Finset.disjoint_left.2 fun n hn hIco => by
        simp only [Finset.mem_range] at hn
        simp only [Finset.mem_Ico] at hIco
        omega
    rw [← hunion, Finset.prod_union hdisj]
    congr 1
    · apply Finset.prod_congr rfl
      intro n hn
      have hlt : n < M := Finset.mem_range.mp hn
      simp [circlePoissonCrossLocal, hlt, L]
    · apply Finset.prod_congr rfl
      intro n hn
      have hnmem := Finset.mem_Ico.mp hn
      simp [circlePoissonCrossLocal, show ¬ n < M by omega, L]
  rw [hcross]
  rw [show (∏ n ∈ Finset.range M, L n ^ 2) =
      (∏ n ∈ Finset.range M, L n) * ∏ n ∈ Finset.range M, L n by
    simp only [pow_two, Finset.prod_mul_distrib]]
  ring

/-- Hellinger affinity accumulated over a coordinate interval. -/
def circlePoissonIntervalAffinity
    (a b : ℕ → CirclePoissonParameter) (M N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Ico M N, circlePoissonHellingerAffinity (a n) (b n)

theorem integral_prefixHalfLikelihood_mul_prefixHalfLikelihood
    (a b : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) :
    ∫ x, circlePoissonPrefixHalfLikelihood a b M x *
        circlePoissonPrefixHalfLikelihood a b N x
        ∂natCirclePoissonProductMeasure b =
      circlePoissonIntervalAffinity a b M N := by
  rw [integral_congr_ae (Eventually.of_forall fun x =>
    prefixHalfLikelihood_mul_eq_crossLocal_prod a b hMN x)]
  have h := integral_finset_coordProd_natCirclePoissonProduct b (Finset.range N)
    (fun n z => circlePoissonCrossLocal a b M n z)
    (fun n => continuous_circlePoissonCrossLocal a b M n)
  rw [h]
  rw [show (∏ n : ↑(Finset.range N),
      ∫ z, circlePoissonCrossLocal a b M n z ∂circlePoissonMeasure (b n)) =
      ∏ n ∈ Finset.range N,
        ∫ z, circlePoissonCrossLocal a b M n z ∂circlePoissonMeasure (b n) from
    Finset.prod_attach (Finset.range N)
      (fun n => ∫ z, circlePoissonCrossLocal a b M n z ∂circlePoissonMeasure (b n))]
  have hlocal (n : ℕ) :
      (∫ z, circlePoissonCrossLocal a b M n z ∂circlePoissonMeasure (b n)) =
        if n < M then 1 else circlePoissonHellingerAffinity (a n) (b n) := by
    by_cases hn : n < M
    · simp only [circlePoissonCrossLocal, hn, if_true,
        integral_sq_circlePoissonHalfLikelihood]
    · simp only [circlePoissonCrossLocal, hn, if_false,
        integral_circlePoissonHalfLikelihood]
  simp_rw [hlocal]
  have hunion : Finset.range M ∪ Finset.Ico M N = Finset.range N := by
    ext n
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range M) (Finset.Ico M N) :=
    Finset.disjoint_left.2 fun n hn hIco => by
      simp only [Finset.mem_range] at hn
      simp only [Finset.mem_Ico] at hIco
      omega
  rw [← hunion, Finset.prod_union hdisj]
  have hhead : (∏ n ∈ Finset.range M,
      if n < M then 1 else circlePoissonHellingerAffinity (a n) (b n)) = 1 := by
    apply Finset.prod_eq_one
    intro n hn
    simp [Finset.mem_range.mp hn]
  have htail : (∏ n ∈ Finset.Ico M N,
      if n < M then 1 else circlePoissonHellingerAffinity (a n) (b n)) =
      circlePoissonIntervalAffinity a b M N := by
    unfold circlePoissonIntervalAffinity
    apply Finset.prod_congr rfl
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    simp [show ¬ n < M by omega]
  rw [hhead, htail, one_mul]

theorem integral_sq_prefixHalfLikelihood_sub
    (a b : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) :
    ∫ x, (circlePoissonPrefixHalfLikelihood a b M x -
        circlePoissonPrefixHalfLikelihood a b N x) ^ 2
        ∂natCirclePoissonProductMeasure b =
      2 * (1 - circlePoissonIntervalAffinity a b M N) := by
  let gM := circlePoissonPrefixHalfLikelihood a b M
  let gN := circlePoissonPrefixHalfLikelihood a b N
  have hMint : Integrable (fun x => gM x ^ 2) (natCirclePoissonProductMeasure b) :=
    ((continuous_circlePoissonPrefixHalfLikelihood a b M).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hNint : Integrable (fun x => gN x ^ 2) (natCirclePoissonProductMeasure b) :=
    ((continuous_circlePoissonPrefixHalfLikelihood a b N).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hcrossInt : Integrable (fun x => gM x * gN x)
      (natCirclePoissonProductMeasure b) :=
    ((continuous_circlePoissonPrefixHalfLikelihood a b M).mul
      (continuous_circlePoissonPrefixHalfLikelihood a b N)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hpoint : (fun x => (gM x - gN x) ^ 2) =
      fun x => gM x ^ 2 + gN x ^ 2 - 2 * (gM x * gN x) := by
    funext x
    ring
  rw [show (fun x => (circlePoissonPrefixHalfLikelihood a b M x -
      circlePoissonPrefixHalfLikelihood a b N x) ^ 2) =
      (fun x => (gM x - gN x) ^ 2) by rfl, hpoint]
  have hcalc :
      (∫ x, gM x ^ 2 + gN x ^ 2 - 2 * (gM x * gN x)
        ∂natCirclePoissonProductMeasure b) =
      (∫ x, gM x ^ 2 ∂natCirclePoissonProductMeasure b) +
        (∫ x, gN x ^ 2 ∂natCirclePoissonProductMeasure b) -
          2 * ∫ x, gM x * gN x ∂natCirclePoissonProductMeasure b := by
    calc
      (∫ x, gM x ^ 2 + gN x ^ 2 - 2 * (gM x * gN x)
          ∂natCirclePoissonProductMeasure b) =
          (∫ x, gM x ^ 2 + gN x ^ 2 ∂natCirclePoissonProductMeasure b) -
            ∫ x, 2 * (gM x * gN x) ∂natCirclePoissonProductMeasure b :=
        integral_sub (hMint.add hNint) (hcrossInt.const_mul 2)
      _ = _ := by rw [integral_add hMint hNint, integral_const_mul]
  rw [hcalc,
    show (∫ x, gM x ^ 2 ∂natCirclePoissonProductMeasure b) = 1 by
      exact integral_sq_circlePoissonPrefixHalfLikelihood a b M,
    show (∫ x, gN x ^ 2 ∂natCirclePoissonProductMeasure b) = 1 by
      exact integral_sq_circlePoissonPrefixHalfLikelihood a b N,
    show (∫ x, gM x * gN x ∂natCirclePoissonProductMeasure b) =
        circlePoissonIntervalAffinity a b M N by
      exact integral_prefixHalfLikelihood_mul_prefixHalfLikelihood a b hMN]
  ring

/-- `L²` class of the finite-prefix square-root likelihood. -/
def circlePoissonPrefixHalfLikelihoodLp
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    Lp ℝ 2 (natCirclePoissonProductMeasure b) :=
  (memLp_two_circlePoissonPrefixHalfLikelihood a b N).toLp
    (circlePoissonPrefixHalfLikelihood a b N)

theorem norm_sq_prefixHalfLikelihoodLp_sub
    (a b : ℕ → CirclePoissonParameter) {M N : ℕ} (hMN : M ≤ N) :
    ‖circlePoissonPrefixHalfLikelihoodLp a b M -
        circlePoissonPrefixHalfLikelihoodLp a b N‖ ^ 2 =
      2 * (1 - circlePoissonIntervalAffinity a b M N) := by
  let fM := circlePoissonPrefixHalfLikelihood a b M
  let fN := circlePoissonPrefixHalfLikelihood a b N
  let hM := memLp_two_circlePoissonPrefixHalfLikelihood a b M
  let hN := memLp_two_circlePoissonPrefixHalfLikelihood a b N
  unfold circlePoissonPrefixHalfLikelihoodLp
  change ‖hM.toLp fM - hN.toLp fN‖ ^ 2 = _
  rw [← MemLp.toLp_sub, HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  have hsub : MemLp (fM - fN) 2 (natCirclePoissonProductMeasure b) := hM.sub hN
  calc
    (∫ x, ‖(hsub.toLp (fM - fN)) x‖ ^ 2
        ∂natCirclePoissonProductMeasure b) =
        ∫ x, ‖fM x - fN x‖ ^ 2 ∂natCirclePoissonProductMeasure b := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hsub] with x hx
      rw [hx]
      rfl
    _ = ∫ x, (fM x - fN x) ^ 2 ∂natCirclePoissonProductMeasure b := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, sq_abs]
    _ = _ := integral_sq_prefixHalfLikelihood_sub a b hMN

/-- Summable local Hellinger defect makes the prefix half-likelihoods Cauchy in `L²` of the second
product law. -/
theorem cauchySeq_circlePoissonPrefixHalfLikelihoodLp
    (a b : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n =>
      1 - circlePoissonHellingerAffinity (a n) (b n))) :
    CauchySeq (circlePoissonPrefixHalfLikelihoodLp a b) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let d : ℕ → ℝ := fun n => 1 - circlePoissonHellingerAffinity (a n) (b n)
  have hd0 : ∀ n, 0 ≤ d n := fun n =>
    sub_nonneg.mpr (circlePoissonHellingerAffinity_le_one (a n) (b n))
  have hH0 : ∀ n, 0 ≤ circlePoissonHellingerAffinity (a n) (b n) := fun n =>
    circlePoissonHellingerAffinity_nonneg (a n) (b n)
  have hH1 : ∀ n, circlePoissonHellingerAffinity (a n) (b n) ≤ 1 := fun n =>
    circlePoissonHellingerAffinity_le_one (a n) (b n)
  have hδ : 0 < ε ^ 2 / 8 := by positivity
  obtain ⟨K, hK⟩ := HTGeometry.exists_forall_Ico_sum_le
    (c := d) (by simpa [d] using hsum) hd0 hδ
  refine ⟨K, ?_⟩
  have hord : ∀ m ≥ K, ∀ n ≥ K, m ≤ n →
      dist (circlePoissonPrefixHalfLikelihoodLp a b m)
        (circlePoissonPrefixHalfLikelihoodLp a b n) < ε := by
    intro m hm n hn hmn
    have hsub : Finset.Ico m n ⊆ Finset.Ico K n := by
      intro j hj
      simp only [Finset.mem_Ico] at hj ⊢
      omega
    have hsumTail : (∑ j ∈ Finset.Ico m n, d j) ≤ ε ^ 2 / 8 := by
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun j _ _ => hd0 j)).trans (hK n)
    have hprod : 1 - circlePoissonIntervalAffinity a b m n ≤
        ∑ j ∈ Finset.Ico m n, d j := by
      unfold circlePoissonIntervalAffinity
      simpa [d] using one_sub_prod_le_sum_one_sub (Finset.Ico m n)
        (fun j => circlePoissonHellingerAffinity (a j) (b j)) hH0 hH1
    have hnormsq := norm_sq_prefixHalfLikelihoodLp_sub a b hmn
    rw [dist_eq_norm]
    have hnorm0 : 0 ≤ ‖circlePoissonPrefixHalfLikelihoodLp a b m -
        circlePoissonPrefixHalfLikelihoodLp a b n‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖circlePoissonPrefixHalfLikelihoodLp a b m -
      circlePoissonPrefixHalfLikelihoodLp a b n‖ - ε)]
  intro m hm n hn
  rcases le_total m n with hmn | hnm
  · exact hord m hm n hn hmn
  · rw [dist_comm]
    exact hord n hn m hm hnm

theorem exists_tendsto_circlePoissonPrefixHalfLikelihoodLp
    (a b : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n =>
      1 - circlePoissonHellingerAffinity (a n) (b n))) :
    ∃ G : Lp ℝ 2 (natCirclePoissonProductMeasure b),
      Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G) :=
  cauchySeq_tendsto_of_complete
    (cauchySeq_circlePoissonPrefixHalfLikelihoodLp a b hsum)

theorem norm_circlePoissonPrefixHalfLikelihoodLp
    (a b : ℕ → CirclePoissonParameter) (N : ℕ) :
    ‖circlePoissonPrefixHalfLikelihoodLp a b N‖ = 1 := by
  have hsq : ‖circlePoissonPrefixHalfLikelihoodLp a b N‖ ^ 2 = 1 := by
    unfold circlePoissonPrefixHalfLikelihoodLp
    rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
    have hmem := memLp_two_circlePoissonPrefixHalfLikelihood a b N
    calc
      (∫ x, ‖(hmem.toLp (circlePoissonPrefixHalfLikelihood a b N)) x‖ ^ 2
          ∂natCirclePoissonProductMeasure b) =
          ∫ x, circlePoissonPrefixHalfLikelihood a b N x ^ 2
            ∂natCirclePoissonProductMeasure b := by
        apply integral_congr_ae
        filter_upwards [MemLp.coeFn_toLp hmem] with x hx
        rw [hx, Real.norm_eq_abs, sq_abs]
      _ = 1 := integral_sq_circlePoissonPrefixHalfLikelihood a b N
  nlinarith [norm_nonneg (circlePoissonPrefixHalfLikelihoodLp a b N)]

theorem norm_circlePoissonHalfLikelihoodLimitLp
    (a b : ℕ → CirclePoissonParameter)
    {G : Lp ℝ 2 (natCirclePoissonProductMeasure b)}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    ‖G‖ = 1 := by
  have hn := hG.norm
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have heq : (fun N => ‖circlePoissonPrefixHalfLikelihoodLp a b N‖) =
      fun _ : ℕ => (1 : ℝ) := by
    funext N
    exact norm_circlePoissonPrefixHalfLikelihoodLp a b N
  rw [heq] at hn
  exact tendsto_nhds_unique hn hone

theorem integral_sq_circlePoissonHalfLikelihoodLimitLp
    (a b : ℕ → CirclePoissonParameter)
    {G : Lp ℝ 2 (natCirclePoissonProductMeasure b)}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    ∫ x, (G x) ^ 2 ∂natCirclePoissonProductMeasure b = 1 := by
  have hnorm := norm_circlePoissonHalfLikelihoodLimitLp a b hG
  have henergy := HTGeometry.norm_l2_sq_eq_integral_norm_sq
    (natCirclePoissonProductMeasure b) G
  rw [hnorm, one_pow] at henergy
  calc
    (∫ x, (G x) ^ 2 ∂natCirclePoissonProductMeasure b) =
        ∫ x, ‖G x‖ ^ 2 ∂natCirclePoissonProductMeasure b := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.norm_eq_abs, sq_abs]
    _ = 1 := henergy.symm

theorem integral_abs_sq_sub_sq_le_lpNorm_mul_lpNorm
    (a b : ℕ → CirclePoissonParameter) (N : ℕ)
    (G : Lp ℝ 2 (natCirclePoissonProductMeasure b)) :
    (∫ x, |circlePoissonPrefixHalfLikelihood a b N x ^ 2 - (G x) ^ 2|
        ∂natCirclePoissonProductMeasure b) ≤
      ‖circlePoissonPrefixHalfLikelihoodLp a b N - G‖ *
        ‖circlePoissonPrefixHalfLikelihoodLp a b N + G‖ := by
  let μ := natCirclePoissonProductMeasure b
  let f := circlePoissonPrefixHalfLikelihood a b N
  let F := circlePoissonPrefixHalfLikelihoodLp a b N
  have hfMem : MemLp f 2 μ := memLp_two_circlePoissonPrefixHalfLikelihood a b N
  have hsubMem : MemLp (f - fun x => G x) 2 μ := hfMem.sub (Lp.memLp G)
  have haddMem : MemLp (f + fun x => G x) 2 μ := hfMem.add (Lp.memLp G)
  let u : (ℕ → Circle) → ℂ := fun x => ((f x - G x : ℝ) : ℂ)
  let v : (ℕ → Circle) → ℂ := fun x => ((f x + G x : ℝ) : ℂ)
  have huMeas : AEStronglyMeasurable u μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hsubMem.1
  have hvMeas : AEStronglyMeasurable v μ :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable haddMem.1
  have hsubIntReal : Integrable (fun x => ‖(f - fun y => G y) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hsubMem.1).mp hsubMem
  have haddIntReal : Integrable (fun x => ‖(f + fun y => G y) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm haddMem.1).mp haddMem
  have huInt : Integrable (fun x => ‖u x‖ ^ 2) μ := by
    refine hsubIntReal.congr (Eventually.of_forall fun x => ?_)
    dsimp only [u, Pi.sub_apply]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hvInt : Integrable (fun x => ‖v x‖ ^ 2) μ := by
    refine haddIntReal.congr (Eventually.of_forall fun x => ?_)
    dsimp only [v, Pi.add_apply]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hcs := integral_mul_le_sqrt_mul_sqrt_measure huMeas hvMeas huInt hvInt
  have hleft : (∫ x, |f x ^ 2 - (G x) ^ 2| ∂μ) =
      ∫ x, ‖u x‖ * ‖v x‖ ∂μ := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [u, v]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [← abs_mul]
    congr 1
    ring
  have hFcoe : ∀ᵐ x ∂μ, F x = f x :=
    MemLp.coeFn_toLp hfMem
  have hsubCoe : ∀ᵐ x ∂μ, (F - G) x = F x - G x := Lp.coeFn_sub F G
  have haddCoe : ∀ᵐ x ∂μ, (F + G) x = F x + G x := Lp.coeFn_add F G
  have huEnergy : (∫ x, ‖u x‖ ^ 2 ∂μ) = ‖F - G‖ ^ 2 := by
    calc
      (∫ x, ‖u x‖ ^ 2 ∂μ) = ∫ x, ‖(F - G) x‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hFcoe, hsubCoe] with x hxF hxsub
        rw [hxsub, hxF]
        dsimp only [u]
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = ‖F - G‖ ^ 2 := (HTGeometry.norm_l2_sq_eq_integral_norm_sq μ (F - G)).symm
  have hvEnergy : (∫ x, ‖v x‖ ^ 2 ∂μ) = ‖F + G‖ ^ 2 := by
    calc
      (∫ x, ‖v x‖ ^ 2 ∂μ) = ∫ x, ‖(F + G) x‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hFcoe, haddCoe] with x hxF hxadd
        rw [hxadd, hxF]
        dsimp only [v]
        simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ = ‖F + G‖ ^ 2 := (HTGeometry.norm_l2_sq_eq_integral_norm_sq μ (F + G)).symm
  rw [huEnergy, hvEnergy,
    Real.sqrt_sq (norm_nonneg (F - G)), Real.sqrt_sq (norm_nonneg (F + G))] at hcs
  simpa [μ, f, F] using hleft.trans_le hcs

theorem tendsto_integral_abs_sq_prefixHalfLikelihood_sub_limit
    (a b : ℕ → CirclePoissonParameter)
    {G : Lp ℝ 2 (natCirclePoissonProductMeasure b)}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    Tendsto (fun N =>
      ∫ x, |circlePoissonPrefixHalfLikelihood a b N x ^ 2 - (G x) ^ 2|
        ∂natCirclePoissonProductMeasure b) atTop (𝓝 0) := by
  have hsub : Tendsto (fun N =>
      ‖circlePoissonPrefixHalfLikelihoodLp a b N - G‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hG
  have hadd : Tendsto (fun N =>
      ‖circlePoissonPrefixHalfLikelihoodLp a b N + G‖) atTop (𝓝 ‖G + G‖) :=
    (hG.add tendsto_const_nhds).norm
  have hprod : Tendsto (fun N =>
      ‖circlePoissonPrefixHalfLikelihoodLp a b N - G‖ *
        ‖circlePoissonPrefixHalfLikelihoodLp a b N + G‖) atTop (𝓝 0) := by
    simpa using hsub.mul hadd
  exact squeeze_zero'
    (Eventually.of_forall fun N => integral_nonneg fun _ => abs_nonneg _)
    (Eventually.of_forall fun N =>
      integral_abs_sq_sub_sq_le_lpNorm_mul_lpNorm a b N G)
    hprod

/-- Complex-valued integration against a circle Poisson law is Haar integration weighted by its
Poisson density. -/
theorem integral_circlePoissonMeasure_complex_eq (b : CirclePoissonParameter)
    (f : Circle → ℂ) :
    ∫ z, f z ∂circlePoissonMeasure b =
      ∫ z, poissonKernel 0 (b : ℂ) (z : ℂ) • f z ∂circleLebesgue := by
  have hdens : AEMeasurable (circlePoissonDensity b) circleLebesgue :=
    (ENNReal.continuous_ofReal.comp (continuous_circlePoissonDensity_real b)).measurable.aemeasurable
  have hdensTop : ∀ᵐ z ∂circleLebesgue, circlePoissonDensity b z < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [circlePoissonMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hdens hdensTop]
  apply integral_congr_ae
  filter_upwards with z
  rw [circlePoissonDensity, ENNReal.toReal_ofReal (circlePoissonDensity_nonneg b z)]

/-- Tilting one local Poisson law by the squared half-likelihood changes all Laurent moments to
those of the target law. -/
theorem integral_zpow_mul_sq_circlePoissonHalfLikelihood
    (a b : CirclePoissonParameter) (q : ℤ) :
    ∫ z, (z : ℂ) ^ q * (circlePoissonHalfLikelihood a b z : ℂ) ^ 2
        ∂circlePoissonMeasure b = circlePoissonFourierMoment a q := by
  rw [integral_circlePoissonMeasure_complex_eq b]
  have hpoint : (fun z : Circle => poissonKernel 0 (b : ℂ) (z : ℂ) •
      ((z : ℂ) ^ q * (circlePoissonHalfLikelihood a b z : ℂ) ^ 2)) =
      fun z : Circle => poissonKernel 0 (a : ℂ) (z : ℂ) • ((z : ℂ) ^ q) := by
    funext z
    rw [circlePoissonHalfLikelihood, ← circlePoissonHalfDensity_sq a z,
      ← circlePoissonHalfDensity_sq b z]
    push_cast
    simp only [Complex.real_smul]
    field_simp [ne_of_gt (circlePoissonHalfDensity_pos b z)]
    push_cast
    ring
  rw [hpoint, ← integral_circlePoissonMeasure_complex_eq a]
  exact integral_circlePoissonMeasure_coe_zpow a q

/-- Complex finite-coordinate products factor under the natural infinite Poisson product. -/
theorem integral_finset_coordProd_natCirclePoissonProduct_complex
    (b : ℕ → CirclePoissonParameter) (S : Finset ℕ)
    (f : ↑S → Circle → ℂ) (hf : ∀ n, Continuous (f n)) :
    ∫ x, ∏ n : ↑S, f n (x n) ∂natCirclePoissonProductMeasure b =
      ∏ n : ↑S, ∫ z, f n z ∂circlePoissonMeasure (b n) := by
  have hfinite : Continuous (fun y : ↑S → Circle => ∏ n : ↑S, f n (y n)) := by
    exact continuous_finsetProd Finset.univ fun n _ => (hf n).comp (continuous_apply n)
  rw [natCirclePoissonProductMeasure]
  change (∫ x, (fun y : ↑S → Circle => ∏ n : ↑S, f n (y n)) (S.restrict x)
      ∂Measure.infinitePi fun n => circlePoissonMeasure (b n)) = _
  rw [integral_restrict_infinitePi (fun n => circlePoissonMeasure (b n))
    hfinite.aestronglyMeasurable]
  exact integral_fintype_prod_eq_prod f

/-- Finite-support Laurent character on a countable multiplicative circle product. -/
def infiniteCircleFourier (n : ℕ →₀ ℤ) : C((ℕ → Circle), ℂ) where
  toFun x := n.prod fun i q => (x i : ℂ) ^ q
  continuous_toFun := by
    classical
    unfold Finsupp.prod
    apply continuous_finsetProd n.support
    intro i _
    exact Continuous.zpow₀
      (by fun_prop : Continuous fun x : ℕ → Circle => (x i : ℂ)) (n i)
      (fun x => Or.inl (Circle.coe_ne_zero (x i)))

@[simp]
theorem norm_infiniteCircleFourier (n : ℕ →₀ ℤ) (x : ℕ → Circle) :
    ‖infiniteCircleFourier n x‖ = 1 := by
  classical
  simp [infiniteCircleFourier, Finsupp.prod, norm_zpow]

/-- Exact finite-support Laurent moments of the natural-index circle Poisson product. -/
theorem integral_infiniteCircleFourier_natCirclePoissonProductMeasure
    (a : ℕ → CirclePoissonParameter) (n : ℕ →₀ ℤ) :
    ∫ x, infiniteCircleFourier n x ∂natCirclePoissonProductMeasure a =
      n.prod fun i q => circlePoissonFourierMoment (a i) q := by
  classical
  have hfun : (fun x : ℕ → Circle => infiniteCircleFourier n x) =
      fun x => ∏ i : ↑n.support, (x i : ℂ) ^ n i := by
    funext x
    rw [show (∏ i : ↑n.support, (x i : ℂ) ^ n i) =
        ∏ i ∈ n.support, (x i : ℂ) ^ n i from
      Finset.prod_attach n.support (fun i => (x i : ℂ) ^ n i)]
    rfl
  rw [hfun, integral_finset_coordProd_natCirclePoissonProduct_complex a n.support
    (fun i z => (z : ℂ) ^ n i)]
  · simp_rw [integral_circlePoissonMeasure_coe_zpow]
    change (∏ i : ↑n.support, circlePoissonFourierMoment (a i) (n i)) =
      ∏ i ∈ n.support, circlePoissonFourierMoment (a i) (n i)
    exact Finset.prod_attach n.support
      (fun i => circlePoissonFourierMoment (a i) (n i))
  · intro i
    exact Continuous.zpow₀ (by fun_prop : Continuous fun z : Circle => (z : ℂ)) (n i)
      (fun z => Or.inl (Circle.coe_ne_zero z))

private theorem infiniteCircleFourier_eq_prod_range
    (n : ℕ →₀ ℤ) (N : ℕ) (hn : n.support ⊆ Finset.range N) (x : ℕ → Circle) :
    infiniteCircleFourier n x = ∏ i : ↑(Finset.range N), (x i : ℂ) ^ n i := by
  classical
  rw [show (∏ i : ↑(Finset.range N), (x i : ℂ) ^ n i) =
      ∏ i ∈ Finset.range N, (x i : ℂ) ^ n i from
    Finset.prod_attach (Finset.range N) (fun i => (x i : ℂ) ^ n i)]
  change (∏ i ∈ n.support, (x i : ℂ) ^ n i) = _
  apply Finset.prod_subset hn
  intro i _ hi
  have hzero : n i = 0 := by simpa [Finsupp.mem_support_iff] using hi
  rw [hzero, zpow_zero]

/-- Once a prefix contains a character's support, its squared half-likelihood tilt has exactly the
target product-Poisson Fourier moment. -/
theorem integral_infiniteCircleFourier_mul_sq_prefixHalfLikelihood
    (a b : ℕ → CirclePoissonParameter) (n : ℕ →₀ ℤ) (N : ℕ)
    (hn : n.support ⊆ Finset.range N) :
    ∫ x, infiniteCircleFourier n x *
        (circlePoissonPrefixHalfLikelihood a b N x : ℂ) ^ 2
        ∂natCirclePoissonProductMeasure b =
      n.prod fun i q => circlePoissonFourierMoment (a i) q := by
  classical
  have hpoint : (fun x : ℕ → Circle => infiniteCircleFourier n x *
      (circlePoissonPrefixHalfLikelihood a b N x : ℂ) ^ 2) =
      fun x => ∏ i : ↑(Finset.range N),
        (x i : ℂ) ^ n i *
          (circlePoissonHalfLikelihood (a i) (b i) (x i) : ℂ) ^ 2 := by
    funext x
    rw [infiniteCircleFourier_eq_prod_range n N hn x]
    simp only [circlePoissonPrefixHalfLikelihood]
    push_cast
    simp only [pow_two, Finset.prod_mul_distrib]
  rw [hpoint, integral_finset_coordProd_natCirclePoissonProduct_complex b
    (Finset.range N)
    (fun i z => (z : ℂ) ^ n i *
      (circlePoissonHalfLikelihood (a i) (b i) z : ℂ) ^ 2)]
  · simp_rw [integral_zpow_mul_sq_circlePoissonHalfLikelihood]
    rw [show (∏ i : ↑(Finset.range N), circlePoissonFourierMoment (a i) (n i)) =
        ∏ i ∈ Finset.range N, circlePoissonFourierMoment (a i) (n i) from
      Finset.prod_attach (Finset.range N)
        (fun i => circlePoissonFourierMoment (a i) (n i))]
    change (∏ i ∈ Finset.range N, circlePoissonFourierMoment (a i) (n i)) =
      ∏ i ∈ n.support, circlePoissonFourierMoment (a i) (n i)
    symm
    apply Finset.prod_subset hn
    intro i _ hi
    have hzero : n i = 0 := by simpa [Finsupp.mem_support_iff] using hi
    rw [hzero]
    simp [circlePoissonFourierMoment]
  · intro i
    exact (Continuous.mul
      (Continuous.zpow₀ (by fun_prop : Continuous fun z : Circle => (z : ℂ)) (n i)
        (fun z => Or.inl (Circle.coe_ne_zero z)))
      ((Complex.continuous_ofReal.comp
        (continuous_circlePoissonHalfLikelihood (a i) (b i))).pow 2))

theorem integrable_sq_circlePoissonHalfLikelihoodLimitLp
    (b : ℕ → CirclePoissonParameter)
    (G : Lp ℝ 2 (natCirclePoissonProductMeasure b)) :
    Integrable (fun x => (G x) ^ 2) (natCirclePoissonProductMeasure b) := by
  have hnorm : Integrable (fun x => ‖G x‖ ^ 2)
      (natCirclePoissonProductMeasure b) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable G)).mp (Lp.memLp G)
  refine hnorm.congr (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Real.norm_eq_abs, sq_abs]

/-- Measure having the `L²`-limit square as density against the reference product law. -/
def circlePoissonLimitDensityMeasure
    (b : ℕ → CirclePoissonParameter)
    (G : Lp ℝ 2 (natCirclePoissonProductMeasure b)) : Measure (ℕ → Circle) :=
  (natCirclePoissonProductMeasure b).withDensity fun x => ENNReal.ofReal ((G x) ^ 2)

theorem isProbabilityMeasure_circlePoissonLimitDensityMeasure
    (a b : ℕ → CirclePoissonParameter)
    {G : Lp ℝ 2 (natCirclePoissonProductMeasure b)}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    IsProbabilityMeasure (circlePoissonLimitDensityMeasure b G) := by
  rw [isProbabilityMeasure_iff, circlePoissonLimitDensityMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hmass := ofReal_integral_eq_lintegral_ofReal
    (integrable_sq_circlePoissonHalfLikelihoodLimitLp b G)
    (Eventually.of_forall fun x => sq_nonneg (G x))
  rw [integral_sq_circlePoissonHalfLikelihoodLimitLp a b hG] at hmass
  simpa using hmass.symm

/-- Bundled probability measure represented by the limiting squared half-likelihood. -/
def circlePoissonLimitDensityProbabilityMeasure
    (a b : ℕ → CirclePoissonParameter)
    (G : Lp ℝ 2 (natCirclePoissonProductMeasure b))
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    ProbabilityMeasure (ℕ → Circle) :=
  ⟨circlePoissonLimitDensityMeasure b G,
    isProbabilityMeasure_circlePoissonLimitDensityMeasure a b hG⟩

/-- Multiplication by a unit-modulus finite character transfers `L¹` convergence of real densities
to convergence of their complex Fourier integrals. -/
theorem tendsto_integral_infiniteCircleFourier_mul_sq_prefixHalfLikelihood
    (a b : ℕ → CirclePoissonParameter) (n : ℕ →₀ ℤ)
    {G : Lp ℝ 2 (natCirclePoissonProductMeasure b)}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    Tendsto (fun N => ∫ x, infiniteCircleFourier n x *
        (circlePoissonPrefixHalfLikelihood a b N x : ℂ) ^ 2
        ∂natCirclePoissonProductMeasure b) atTop
      (𝓝 (∫ x, infiniteCircleFourier n x * ((G x : ℝ) : ℂ) ^ 2
        ∂natCirclePoissonProductMeasure b)) := by
  let μ := natCirclePoissonProductMeasure b
  let χ : (ℕ → Circle) → ℂ := infiniteCircleFourier n
  let fN : ℕ → (ℕ → Circle) → ℝ := circlePoissonPrefixHalfLikelihood a b
  have hL1 := tendsto_integral_abs_sq_prefixHalfLikelihood_sub_limit a b hG
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun N => ?_) hL1
  have hsqN : Integrable (fun x => fN N x ^ 2) μ :=
    ((continuous_circlePoissonPrefixHalfLikelihood a b N).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsqG : Integrable (fun x => (G x) ^ 2) μ :=
    integrable_sq_circlePoissonHalfLikelihoodLimitLp b G
  have hcN : Integrable (fun x => ((fN N x ^ 2 : ℝ) : ℂ)) μ :=
    Complex.ofRealCLM.integrable_comp hsqN
  have hcG : Integrable (fun x => (((G x) ^ 2 : ℝ) : ℂ)) μ :=
    Complex.ofRealCLM.integrable_comp hsqG
  have hχMeas : AEStronglyMeasurable χ μ :=
    (infiniteCircleFourier n).continuous.aestronglyMeasurable
  have hχNorm : ∀ᵐ x ∂μ, ‖χ x‖ ≤ 1 :=
    Eventually.of_forall fun x => by rw [norm_infiniteCircleFourier]
  have hmulN : Integrable (fun x => χ x * ((fN N x ^ 2 : ℝ) : ℂ)) μ :=
    hcN.bdd_mul hχMeas hχNorm
  have hmulG : Integrable (fun x => χ x * (((G x) ^ 2 : ℝ) : ℂ)) μ :=
    hcG.bdd_mul hχMeas hχNorm
  calc
    ‖(∫ x, infiniteCircleFourier n x * (fN N x : ℂ) ^ 2 ∂μ) -
        ∫ x, infiniteCircleFourier n x * ((G x : ℝ) : ℂ) ^ 2 ∂μ‖ =
        ‖∫ x, χ x * (((fN N x) ^ 2 - (G x) ^ 2 : ℝ) : ℂ) ∂μ‖ := by
      have hcastN : (fun x => infiniteCircleFourier n x * (fN N x : ℂ) ^ 2) =
          fun x => χ x * ((fN N x ^ 2 : ℝ) : ℂ) := by
        funext x
        dsimp only [χ]
        push_cast
        rfl
      have hcastG : (fun x => infiniteCircleFourier n x * ((G x : ℝ) : ℂ) ^ 2) =
          fun x => χ x * (((G x) ^ 2 : ℝ) : ℂ) := by
        funext x
        dsimp only [χ]
        push_cast
        rfl
      rw [hcastN, hcastG]
      rw [← integral_sub hmulN hmulG]
      congr 2
      funext x
      dsimp only [χ]
      push_cast
      ring
    _ ≤ ∫ x, ‖χ x * (((fN N x) ^ 2 - (G x) ^ 2 : ℝ) : ℂ)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, |fN N x ^ 2 - (G x) ^ 2| ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [norm_mul, norm_infiniteCircleFourier, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
    _ = ∫ x, |circlePoissonPrefixHalfLikelihood a b N x ^ 2 - (G x) ^ 2|
        ∂natCirclePoissonProductMeasure b := rfl

theorem integral_infiniteCircleFourier_circlePoissonLimitDensityMeasure
    (a b : ℕ → CirclePoissonParameter) (n : ℕ →₀ ℤ)
    {G : Lp ℝ 2 (natCirclePoissonProductMeasure b)}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    ∫ x, infiniteCircleFourier n x ∂circlePoissonLimitDensityMeasure b G =
      n.prod fun i q => circlePoissonFourierMoment (a i) q := by
  let μ := natCirclePoissonProductMeasure b
  let target : ℂ := n.prod fun i q => circlePoissonFourierMoment (a i) q
  have hprefix : ∀ᶠ N in atTop,
      (∫ x, infiniteCircleFourier n x *
          (circlePoissonPrefixHalfLikelihood a b N x : ℂ) ^ 2 ∂μ) = target := by
    refine Filter.eventually_atTop.2 ⟨n.support.sup id + 1, fun N hN => ?_⟩
    apply integral_infiniteCircleFourier_mul_sq_prefixHalfLikelihood a b n N
    intro i hi
    rw [Finset.mem_range]
    exact lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi)) hN
  have htarget : Tendsto (fun N => ∫ x, infiniteCircleFourier n x *
      (circlePoissonPrefixHalfLikelihood a b N x : ℂ) ^ 2 ∂μ) atTop (𝓝 target) :=
    tendsto_const_nhds.congr' (hprefix.mono fun _ h => h.symm)
  have hlimit :=
    tendsto_integral_infiniteCircleFourier_mul_sq_prefixHalfLikelihood a b n hG
  have heq : (∫ x, infiniteCircleFourier n x * ((G x : ℝ) : ℂ) ^ 2 ∂μ) = target :=
    tendsto_nhds_unique hlimit htarget
  have hdensReal : AEMeasurable (fun x => (G x) ^ 2) μ :=
    ((Lp.aestronglyMeasurable G).pow 2).aemeasurable
  have hdens : AEMeasurable (fun x => ENNReal.ofReal ((G x) ^ 2)) μ :=
    hdensReal.ennreal_ofReal
  have hdensTop : ∀ᵐ x ∂μ, ENNReal.ofReal ((G x) ^ 2) < ∞ :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [circlePoissonLimitDensityMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hdens hdensTop]
  calc
    (∫ x, (ENNReal.ofReal ((G x) ^ 2)).toReal • infiniteCircleFourier n x ∂μ) =
        ∫ x, infiniteCircleFourier n x * ((G x : ℝ) : ℂ) ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (sq_nonneg (G x)), Complex.real_smul]
      push_cast
      ring
    _ = target := heq

/-- Coordinatewise equivalence between multiplicative circles and the additive unit torus. -/
def circleProductHomeomorphUnitTorus :
    (ℕ → Circle) ≃ₜ (ℕ → UnitAddCircle) :=
  Homeomorph.piCongrRight fun _ =>
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

theorem infiniteTorusFourier_circleProductHomeomorphUnitTorus
    (n : ℕ →₀ ℤ) (x : ℕ → Circle) :
    infiniteTorusFourier n (circleProductHomeomorphUnitTorus x) =
      infiniteCircleFourier n x := by
  classical
  simp only [infiniteTorusFourier, infiniteCircleFourier, ContinuousMap.coe_mk,
    Finsupp.prod]
  apply Finset.prod_congr rfl
  intro i _
  change fourier (n i)
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (x i)) =
    (x i : ℂ) ^ n i
  rw [fourier_apply, AddCircle.toCircle_zsmul]
  have he : AddCircle.toCircle
      ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm (x i)) = x i := by
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply (x i)
  rw [he]
  exact Circle.coe_zpow (x i) (n i)

/-- Probability measures on a countable multiplicative circle product are determined by every
finite-support Laurent character. -/
theorem probabilityMeasure_ext_of_infiniteCircleFourier_integral_eq
    (μ ν : ProbabilityMeasure (ℕ → Circle))
    (h : ∀ n : ℕ →₀ ℤ,
      (∫ x, infiniteCircleFourier n x ∂(μ : Measure (ℕ → Circle))) =
        ∫ x, infiniteCircleFourier n x ∂(ν : Measure (ℕ → Circle))) :
    μ = ν := by
  let e := circleProductHomeomorphUnitTorus
  let μ' : ProbabilityMeasure (ℕ → UnitAddCircle) :=
    ProbabilityMeasure.map μ e.continuous.aemeasurable
  let ν' : ProbabilityMeasure (ℕ → UnitAddCircle) :=
    ProbabilityMeasure.map ν e.continuous.aemeasurable
  have hfourier : ∀ n : ℕ →₀ ℤ,
      (∫ y, infiniteTorusFourier n y ∂(μ' : Measure (ℕ → UnitAddCircle))) =
        ∫ y, infiniteTorusFourier n y ∂(ν' : Measure (ℕ → UnitAddCircle)) := by
    intro n
    dsimp only [μ', ν']
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map]
    rw [integral_map e.continuous.aemeasurable
      (infiniteTorusFourier n).continuous.aestronglyMeasurable]
    rw [integral_map e.continuous.aemeasurable
      (infiniteTorusFourier n).continuous.aestronglyMeasurable]
    change (∫ x, infiniteTorusFourier n (circleProductHomeomorphUnitTorus x)
        ∂(μ : Measure (ℕ → Circle))) =
      ∫ x, infiniteTorusFourier n (circleProductHomeomorphUnitTorus x)
        ∂(ν : Measure (ℕ → Circle))
    simpa only [infiniteTorusFourier_circleProductHomeomorphUnitTorus] using h n
  have hmapped := probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq μ' ν' hfourier
  have hmaps := congrArg (fun ρ : ProbabilityMeasure (ℕ → UnitAddCircle) =>
    (ρ : Measure (ℕ → UnitAddCircle))) hmapped
  change Measure.map e (μ : Measure (ℕ → Circle)) =
    Measure.map e (ν : Measure (ℕ → Circle)) at hmaps
  have hpull := congrArg (Measure.map e.symm) hmaps
  have hcomp : e.symm ∘ e = id := by
    funext x
    exact e.symm_apply_apply x
  rw [Measure.map_map e.symm.measurable e.measurable, hcomp, Measure.map_id,
    Measure.map_map e.symm.measurable e.measurable, hcomp, Measure.map_id] at hpull
  exact ProbabilityMeasure.toMeasure_injective hpull

/-- The `L²` limit square is the exact Radon--Nikodym density of the target product law. -/
theorem natCirclePoissonProductMeasure_eq_circlePoissonLimitDensityMeasure
    (a b : ℕ → CirclePoissonParameter)
    {G : Lp ℝ 2 (natCirclePoissonProductMeasure b)}
    (hG : Tendsto (circlePoissonPrefixHalfLikelihoodLp a b) atTop (𝓝 G)) :
    natCirclePoissonProductMeasure a = circlePoissonLimitDensityMeasure b G := by
  let μa : ProbabilityMeasure (ℕ → Circle) :=
    ⟨natCirclePoissonProductMeasure a, inferInstance⟩
  let μG : ProbabilityMeasure (ℕ → Circle) :=
    circlePoissonLimitDensityProbabilityMeasure a b G hG
  have heq : μa = μG := by
    apply probabilityMeasure_ext_of_infiniteCircleFourier_integral_eq
    intro n
    change (∫ x, infiniteCircleFourier n x ∂natCirclePoissonProductMeasure a) =
      ∫ x, infiniteCircleFourier n x ∂circlePoissonLimitDensityMeasure b G
    rw [integral_infiniteCircleFourier_natCirclePoissonProductMeasure,
      integral_infiniteCircleFourier_circlePoissonLimitDensityMeasure a b n hG]
  exact congrArg (fun ρ : ProbabilityMeasure (ℕ → Circle) =>
    (ρ : Measure (ℕ → Circle))) heq

/-- Summable local Hellinger defect gives absolute continuity of the first product law with respect
to the second. -/
theorem natCirclePoissonProductMeasure_absolutelyContinuous_of_summable_hellingerDefect
    (a b : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n =>
      1 - circlePoissonHellingerAffinity (a n) (b n))) :
    natCirclePoissonProductMeasure a ≪ natCirclePoissonProductMeasure b := by
  obtain ⟨G, hG⟩ := exists_tendsto_circlePoissonPrefixHalfLikelihoodLp a b hsum
  rw [natCirclePoissonProductMeasure_eq_circlePoissonLimitDensityMeasure a b hG]
  exact withDensity_absolutelyContinuous _ _

/-- Summable local Hellinger defect puts the two Poisson products in the same measure class. -/
theorem natCirclePoissonProductMeasure_mutuallyAbsolutelyContinuous_of_summable_hellingerDefect
    (a b : ℕ → CirclePoissonParameter)
    (hsum : Summable (fun n =>
      1 - circlePoissonHellingerAffinity (a n) (b n))) :
    (natCirclePoissonProductMeasure a ≪ natCirclePoissonProductMeasure b) ∧
      natCirclePoissonProductMeasure b ≪ natCirclePoissonProductMeasure a := by
  refine ⟨natCirclePoissonProductMeasure_absolutelyContinuous_of_summable_hellingerDefect
    a b hsum, ?_⟩
  apply natCirclePoissonProductMeasure_absolutelyContinuous_of_summable_hellingerDefect b a
  simpa only [circlePoissonHellingerAffinity_comm] using hsum

/-- For disk parameters tending to zero, square-summable displacement makes the local Hellinger
defect summable. -/
theorem summable_circlePoissonHellingerDefect_of_tendsto_zero_of_summable_normSq
    (a b : ℕ → CirclePoissonParameter)
    (ha : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => (b n : ℂ)) atTop (𝓝 0))
    (hsq : Summable (fun n => ‖(a n : ℂ) - (b n : ℂ)‖ ^ 2)) :
    Summable (fun n => 1 - circlePoissonHellingerAffinity (a n) (b n)) := by
  have haHalf : ∀ᶠ n in atTop, ‖(a n : ℂ)‖ ≤ 1 / 2 := by
    have hevent := ha.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 : ℝ) / 2))
    filter_upwards [hevent] with n hn
    simpa only [dist_zero_right] using hn.le
  have hbHalf : ∀ᶠ n in atTop, ‖(b n : ℂ)‖ ≤ 1 / 2 := by
    have hevent := hb.eventually (Metric.ball_mem_nhds (0 : ℂ) (by norm_num : 0 < (1 : ℝ) / 2))
    filter_upwards [hevent] with n hn
    simpa only [dist_zero_right] using hn.le
  apply Summable.of_norm_bounded_eventually (hsq.mul_left 1352)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [haHalf, hbHalf] with n han hbn
  rw [Real.norm_eq_abs, abs_of_nonneg
    (sub_nonneg.mpr (circlePoissonHellingerAffinity_le_one (a n) (b n)))]
  exact one_sub_circlePoissonHellingerAffinity_le_norm_sq_halfDisk (a n) (b n) han hbn

/-- Exact Kakutani classification for circle-Poisson parameter sequences tending to the disk
origin. -/
theorem natCirclePoissonProductMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
    (a b : ℕ → CirclePoissonParameter)
    (ha : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => (b n : ℂ)) atTop (𝓝 0)) :
    ((natCirclePoissonProductMeasure a ≪ natCirclePoissonProductMeasure b) ∧
        natCirclePoissonProductMeasure b ≪ natCirclePoissonProductMeasure a) ↔
      Summable (fun n => ‖(a n : ℂ) - (b n : ℂ)‖ ^ 2) := by
  constructor
  · rintro ⟨hab, _⟩
    by_contra hdiv
    have hzero := Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hab
      (natCirclePoissonProductMeasure_mutuallySingular_of_not_summable_normSq a b hdiv)
    have huniv : natCirclePoissonProductMeasure a Set.univ = 1 := measure_univ
    rw [hzero] at huniv
    simp at huniv
  · intro hsq
    exact natCirclePoissonProductMeasure_mutuallyAbsolutelyContinuous_of_summable_hellingerDefect
      a b (summable_circlePoissonHellingerDefect_of_tendsto_zero_of_summable_normSq
        a b ha hb hsq)

/-- The exact circle-Poisson Kakutani dichotomy: square-summable displacement gives equivalent
products; every other displacement gives mutual singularity. -/
theorem natCirclePoissonProductMeasure_equivalent_or_mutuallySingular
    (a b : ℕ → CirclePoissonParameter)
    (ha : Tendsto (fun n => (a n : ℂ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => (b n : ℂ)) atTop (𝓝 0)) :
    ((natCirclePoissonProductMeasure a ≪ natCirclePoissonProductMeasure b) ∧
        natCirclePoissonProductMeasure b ≪ natCirclePoissonProductMeasure a) ∨
      (natCirclePoissonProductMeasure a).MutuallySingular
        (natCirclePoissonProductMeasure b) := by
  by_cases hsq : Summable (fun n => ‖(a n : ℂ) - (b n : ℂ)‖ ^ 2)
  · exact Or.inl
      ((natCirclePoissonProductMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq
        a b ha hb).2 hsq)
  · exact Or.inr
      (natCirclePoissonProductMeasure_mutuallySingular_of_not_summable_normSq a b hsq)

end
end GaloisForLFunctions.HTGeometry
