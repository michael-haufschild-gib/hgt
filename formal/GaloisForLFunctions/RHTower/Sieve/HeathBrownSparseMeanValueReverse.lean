import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBasic
import GaloisForLFunctions.RHTower.Sieve.GallagherTail

noncomputable section

namespace RHTower.Sieve

open Complex MeasureTheory Set Finset
open scoped FourierTransform

private theorem integral_phase_mul_triC_eq_fourier {D : ℝ} (hD : 0 < D) (y : ℝ) :
    (∫ t : ℝ, Complex.exp (((2 * Real.pi * (t * y) : ℝ) : ℂ) * Complex.I) * triC D t)
      = 𝓕 (triC D) y := by
  rw [← fourier_triC_even hD y, Real.fourier_real_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [Real.fourierChar_apply, Circle.smul_def]
  congr 1
  push_cast
  ring_nf

private theorem sum_nnrealFrequencyPhase_eq_normSq {ι : Type*} (a : ι → NNReal)
    (s : Finset ι) (x : ι → ℝ) (t : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, ((((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ))
        * Complex.exp (((2 * Real.pi * (t * (x i - x j)) : ℝ) : ℂ) * Complex.I))
      = ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ) := by
  have hzc : ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ)
      = finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t
          * (starRingEnd ℂ) (finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hzc, finiteFrequencyPoly, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [phase_sub, map_mul, Complex.conj_ofReal]
  push_cast
  ring

private noncomputable def finiteFrequencyReverseTerm {ι : Type*} (a : ι → NNReal)
    (x : ι → ℝ) (D : ℝ) (i j : ι) (t : ℝ) : ℂ :=
  ((((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ))
    * (Complex.exp (((2 * Real.pi * (t * (x i - x j)) : ℝ) : ℂ) * Complex.I) * triC D t)

private theorem integrable_finiteFrequencyReverseTerm {ι : Type*} {D : ℝ} (hD : 0 < D)
    (a : ι → NNReal) (x : ι → ℝ) (i j : ι) :
    Integrable (finiteFrequencyReverseTerm a x D i j) := by
  refine Integrable.const_mul ?_ _
  refine (integrable_triC hD.le).bdd_mul (c := 1) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  · exact Filter.Eventually.of_forall fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I _)

private theorem integral_finiteFrequencyReverseTerm {ι : Type*} {D : ℝ} (hD : 0 < D)
    (a : ι → NNReal) (x : ι → ℝ) (i j : ι) :
    (∫ t : ℝ, finiteFrequencyReverseTerm a x D i j t)
      = ((((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ)) * 𝓕 (triC D) (x i - x j) := by
  simp only [finiteFrequencyReverseTerm]
  rw [integral_const_mul, integral_phase_mul_triC_eq_fourier hD]

private theorem sum_finiteFrequencyReverseTerm {ι : Type*} (a : ι → NNReal)
    (s : Finset ι) (x : ι → ℝ) (D : ℝ) (t : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, finiteFrequencyReverseTerm a x D i j t)
      = triC D t * ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ) := by
  rw [← sum_nnrealFrequencyPhase_eq_normSq a s x t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [finiteFrequencyReverseTerm]
  ring

private theorem integrable_triC_mul_nnrealFrequencyNormSq {ι : Type*} {D : ℝ}
    (hD : 0 < D) (a : ι → NNReal) (s : Finset ι) (x : ι → ℝ) :
    Integrable fun t : ℝ =>
      triC D t * ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ) := by
  have hsum : Integrable fun t : ℝ =>
      ∑ i ∈ s, ∑ j ∈ s, finiteFrequencyReverseTerm a x D i j t :=
    integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => integrable_finiteFrequencyReverseTerm hD a x i j
  exact hsum.congr (Filter.Eventually.of_forall (sum_finiteFrequencyReverseTerm a s x D))

/-- Exact compact-triangle mean square for a finite nonnegative frequency family. -/
theorem integral_tri_normSq_nnrealFrequencyPoly_eq {ι : Type*} {D : ℝ} (hD : 0 < D)
    (a : ι → NNReal) (s : Finset ι) (x : ι → ℝ) :
    (∫ t : ℝ, tri D t * ‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2)
      = ∑ i ∈ s, ∑ j ∈ s, (a i : ℝ) * (a j : ℝ) * (𝓕 (triC D) (x i - x j)).re := by
  have hcomplex := integrable_triC_mul_nnrealFrequencyNormSq hD a s x
  have hre := integral_re (μ := volume) hcomplex
  simp only [RCLike.re_to_complex] at hre
  have hcomplexEq :
      (∫ t : ℝ,
        triC D t * ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ))
        = ∑ i ∈ s, ∑ j ∈ s,
            ((((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ)) * 𝓕 (triC D) (x i - x j) := by
    calc
      (∫ t : ℝ,
          triC D t * ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ))
          = ∫ t : ℝ, ∑ i ∈ s, ∑ j ∈ s, finiteFrequencyReverseTerm a x D i j t := by
              exact integral_congr_ae (Filter.Eventually.of_forall fun t =>
                (sum_finiteFrequencyReverseTerm a s x D t).symm)
      _ = ∑ i ∈ s, ∑ j ∈ s, ∫ t : ℝ, finiteFrequencyReverseTerm a x D i j t := by
              rw [integral_finsetSum _ fun i _ =>
                integrable_finsetSum _ fun j _ => integrable_finiteFrequencyReverseTerm hD a x i j]
              exact Finset.sum_congr rfl fun i _ =>
                integral_finsetSum _ fun j _ => integrable_finiteFrequencyReverseTerm hD a x i j
      _ = ∑ i ∈ s, ∑ j ∈ s,
            ((((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ)) * 𝓕 (triC D) (x i - x j) := by
              exact Finset.sum_congr rfl fun i _ =>
                Finset.sum_congr rfl fun j _ => integral_finiteFrequencyReverseTerm hD a x i j
  have hreEq' :
      (∫ t : ℝ,
        (triC D t * ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ)).re)
        = ∑ i ∈ s, ∑ j ∈ s, (a i : ℝ) * (a j : ℝ) * (𝓕 (triC D) (x i - x j)).re := by
    calc
      (∫ t : ℝ,
          (triC D t * ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ)).re)
          = (∫ t : ℝ,
              triC D t * ((‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 : ℝ) : ℂ)).re := hre
      _ = (∑ i ∈ s, ∑ j ∈ s,
            ((((a i : ℝ) * (a j : ℝ) : ℝ) : ℂ)) * 𝓕 (triC D) (x i - x j)).re :=
          congrArg Complex.re hcomplexEq
      _ = ∑ i ∈ s, ∑ j ∈ s,
            (a i : ℝ) * (a j : ℝ) * (𝓕 (triC D) (x i - x j)).re := by
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.re_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_comm, re_mul_ofReal]
          ring
  rw [← hreEq']
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [triC, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

private theorem finiteFrequencyCollisionWeight_nnreal_eq {ι : Type*} (a : ι → NNReal)
    (s : Finset ι) (x : ι → ℝ) (δ : ℝ) :
    finiteFrequencyCollisionWeight (fun i => (((a i : ℝ) : ℂ))) s x δ
      = ∑ i ∈ s, ∑ j ∈ s,
          if |x i - x j| < δ then (a i : ℝ) * (a j : ℝ) else 0 := by
  rw [finiteFrequencyCollisionWeight]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases h : |x i - x j| < δ
  · rw [if_pos h, if_pos h, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (a i).coe_nonneg,
      abs_of_nonneg (a j).coe_nonneg]
  · simp [h]

private theorem integral_tri_normSq_nnrealFrequencyPoly_le_Icc {ι : Type*} {D : ℝ}
    (hD : 0 < D) (a : ι → NNReal) (s : Finset ι) (x : ι → ℝ) :
    (∫ t : ℝ, tri D t * ‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2)
      ≤ D * ∫ t in Set.Icc (-D) D,
          ‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 := by
  let F : ℝ → ℝ := fun t => ‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2
  have hFcont : Continuous F := ((continuous_finiteFrequencyPoly
    (fun i => (((a i : ℝ) : ℂ))) s x).norm).pow 2
  have htriComplex := integrable_triC_mul_nnrealFrequencyNormSq hD a s x
  have htriInt : Integrable fun t : ℝ => tri D t * F t := by
    exact htriComplex.re.congr (Filter.Eventually.of_forall fun t => by
      change ((tri D t : ℂ) * ((F t : ℝ) : ℂ)).re = tri D t * F t
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      have hFreal : (((F t : ℝ) : ℂ)).re = F t := rfl
      rw [hFreal]
      ring)
  have hsupp : (fun t : ℝ => tri D t * F t)
      = Set.indicator (Set.Icc (-D) D) (fun t : ℝ => tri D t * F t) := by
    funext t
    by_cases ht : t ∈ Set.Icc (-D) D
    · rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht]
      have habs : D ≤ |t| := by
        by_cases hleft : t < -D
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · have hright : D < t := by
            by_contra hn
            exact ht ⟨le_of_not_gt hleft, le_of_not_gt hn⟩
          rw [abs_of_nonneg (by linarith)]
          exact hright.le
      rw [tri_eq_zero habs, zero_mul]
  have hwhole : (∫ t : ℝ, tri D t * F t)
      = ∫ t in Set.Icc (-D) D, tri D t * F t := by
    calc
      (∫ t : ℝ, tri D t * F t)
          = ∫ t : ℝ, Set.indicator (Set.Icc (-D) D) (fun t : ℝ => tri D t * F t) t := by
              exact integral_congr_ae (Filter.Eventually.of_forall fun t => congrFun hsupp t)
      _ = ∫ t in Set.Icc (-D) D, tri D t * F t :=
          MeasureTheory.integral_indicator measurableSet_Icc
  rw [hwhole]
  calc
    (∫ t in Set.Icc (-D) D, tri D t * F t)
        ≤ ∫ t in Set.Icc (-D) D, D * F t := by
          refine setIntegral_mono_on htriInt.integrableOn
            ((hFcont.const_mul D).integrableOn_Icc) measurableSet_Icc fun t _ => ?_
          have htri : tri D t ≤ D := by
            rw [tri]
            rcases le_total (D - |t|) 0 with h | h
            · rw [max_eq_right h]
              exact hD.le
            · rw [max_eq_left h]
              linarith [abs_nonneg t]
          exact mul_le_mul_of_nonneg_right htri (by positivity)
    _ = D * ∫ t in Set.Icc (-D) D, F t := by
          rw [MeasureTheory.integral_const_mul]

/-- **Reverse finite-frequency sparse mean value.**  For intrinsically nonnegative coefficients,
the near-collision mass is controlled by the same finite-window mean square. -/
theorem finiteFrequencyCollisionWeight_le_integral_Icc_nnreal {ι : Type*}
    (a : ι → NNReal) (s : Finset ι) (x : ι → ℝ) {δ D : ℝ}
    (hD : 0 < D) (hscale : 2 * Real.pi * D * δ ≤ 1) :
    finiteFrequencyCollisionWeight (fun i => (((a i : ℝ) : ℂ))) s x δ
      ≤ (5 / (4 * D))
          * ∫ t in Set.Icc (-D) D,
              ‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2 := by
  have hlower : (4 / 5) * D ^ 2
        * finiteFrequencyCollisionWeight (fun i => (((a i : ℝ) : ℂ))) s x δ
      ≤ ∑ i ∈ s, ∑ j ∈ s,
          (a i : ℝ) * (a j : ℝ) * (𝓕 (triC D) (x i - x j)).re := by
    rw [finiteFrequencyCollisionWeight_nnreal_eq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hclose : |x i - x j| < δ
    · rw [if_pos hclose]
      have hpos : (0 : ℝ) < 2 * Real.pi * D := by positivity
      have hbound : |2 * Real.pi * D * (x i - x j)| ≤ 1 := by
        rw [abs_mul, abs_of_pos hpos]
        exact (mul_le_mul_of_nonneg_left hclose.le hpos.le).trans hscale
      have hfourier := le_fourier_triC_re hD hbound
      have hmul := mul_le_mul_of_nonneg_left hfourier
        (mul_nonneg (a i).coe_nonneg (a j).coe_nonneg)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
    · rw [if_neg hclose, mul_zero]
      exact mul_nonneg (mul_nonneg (a i).coe_nonneg (a j).coe_nonneg)
        (fourier_triC_re_nonneg hD _)
  have htriangle := integral_tri_normSq_nnrealFrequencyPoly_le_Icc hD a s x
  rw [← integral_tri_normSq_nnrealFrequencyPoly_eq hD a s x] at hlower
  have hcombine := hlower.trans htriangle
  have hfactor : (0 : ℝ) < (4 / 5) * D ^ 2 := by positivity
  have hrhs : (5 / (4 * D))
          * ∫ t in Set.Icc (-D) D,
              ‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2
      = (D * ∫ t in Set.Icc (-D) D,
              ‖finiteFrequencyPoly (fun i => (((a i : ℝ) : ℂ))) s x t‖ ^ 2)
          / ((4 / 5) * D ^ 2) := by
    field_simp
  rw [hrhs, le_div_iff₀ hfactor]
  simpa only [mul_comm] using hcombine

/-- The nonnegative pair coefficient attached to `(m,n)`. -/
noncomputable def heathBrownPositivePairWeight (q : ℕ → Set.Icc (0 : ℝ) 1)
    (p : PNat × PNat) : NNReal :=
  ⟨q (p.2 : ℕ), (q (p.2 : ℕ)).property.1⟩

/-- Literal coefficient-weighted ordered near-product collision mass. -/
noncomputable def heathBrownPositiveWeightedCollision (A B : Finset PNat)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ)) : ℝ :=
  ∑ p ∈ A.product B, ∑ r ∈ A.product B,
    if |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ)
        - Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹
    then (q (p.2 : ℕ) : ℝ) * (q (r.2 : ℕ) : ℝ) else 0

private theorem heathBrownPositiveFrequency_close_iff (p r : PNat × PNat)
    (T : Set.Ioi (0 : ℝ)) :
    |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r|
        < 1 / (2 * Real.pi * (T : ℝ)) ↔
      |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ)
          - Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| < ((T : ℝ))⁻¹ := by
  have hden : (0 : ℝ) < 2 * Real.pi := by positivity
  have hleft :
      |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r|
        = |Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ)
            - Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)| / (2 * Real.pi) := by
    rw [heathBrownPositiveProductFrequency, heathBrownProductFrequency,
      heathBrownPositiveProductFrequency, heathBrownProductFrequency]
    rw [show -Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ) / (2 * Real.pi)
          - -Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ) / (2 * Real.pi)
        = -(Real.log ((p.1 : ℕ) * (p.2 : ℕ) : ℕ)
            - Real.log ((r.1 : ℕ) * (r.2 : ℕ) : ℕ)) / (2 * Real.pi) by ring,
      abs_div, abs_neg, abs_of_pos hden]
  have hright : 1 / (2 * Real.pi * (T : ℝ)) = ((T : ℝ))⁻¹ / (2 * Real.pi) := by
    field_simp
  rw [hleft, hright, div_lt_div_iff₀ hden hden]
  constructor <;> intro h <;> nlinarith [hden]

private theorem heathBrownPositiveCollisionWeight_eq_weighted (A B : Finset PNat)
    (ε : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ)) :
    finiteFrequencyCollisionWeight (heathBrownPositiveCoefficient ε q) (A.product B)
        heathBrownPositiveProductFrequency (1 / (2 * Real.pi * (T : ℝ)))
      = heathBrownPositiveWeightedCollision A B q T := by
  rw [finiteFrequencyCollisionWeight, heathBrownPositiveWeightedCollision]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
  have hp : ‖heathBrownPositiveCoefficient ε q p‖ = (q (p.2 : ℕ) : ℝ) := by
    rw [heathBrownPositiveCoefficient, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (q (p.2 : ℕ)).property.1]
  have hr : ‖heathBrownPositiveCoefficient ε q r‖ = (q (r.2 : ℕ) : ℝ) := by
    rw [heathBrownPositiveCoefficient, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (q (r.2 : ℕ)).property.1]
  rw [hp, hr]
  by_cases h : |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r|
      < 1 / (2 * Real.pi * (T : ℝ))
  · rw [if_pos h, if_pos ((heathBrownPositiveFrequency_close_iff p r T).mp h)]
  · rw [if_neg h, if_neg (mt (heathBrownPositiveFrequency_close_iff p r T).mpr h)]

private theorem finiteFrequencyPoly_pairWeight_eq_positiveProduct (A B : Finset PNat)
    (q : ℕ → Set.Icc (0 : ℝ) 1) (t : ℝ) :
    finiteFrequencyPoly (fun p => (((heathBrownPositivePairWeight q p : ℝ) : ℂ)))
        (A.product B) heathBrownPositiveProductFrequency t
      = heathBrownPositiveProductPoly A B (fun _ => 1) q t := by
  rw [heathBrownPositiveProductPoly, finiteFrequencyPoly, finiteFrequencyPoly]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [heathBrownPositiveCoefficient, heathBrownPositivePairWeight]
  change (((q (p.2 : ℕ) : ℝ) : ℂ))
      * Complex.exp (((2 * Real.pi * (t * heathBrownPositiveProductFrequency p) : ℝ) : ℂ)
          * Complex.I)
    = (1 : ℂ) * (((q (p.2 : ℕ) : ℝ) : ℂ))
        * Complex.exp (((2 * Real.pi * (t * heathBrownPositiveProductFrequency p) : ℝ) : ℂ)
            * Complex.I)
  ring

/-- Forward half of Heath--Brown's sparse mean-value comparison, with the exact coefficient-weighted
collision mass and no analytic premise. -/
theorem integral_Icc_normSq_heathBrown_factors_le_weightedCollision
    (A B : Finset PNat) (ε : ℕ → Circle) (q : ℕ → Set.Icc (0 : ℝ) 1)
    (T : Set.Ioi (0 : ℝ)) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ 2)
      ≤ (5 * Real.pi / 2) * (T : ℝ) * heathBrownPositiveWeightedCollision A B q T := by
  have hδ : (0 : ℝ) < 1 / (2 * Real.pi * (T : ℝ)) := by
    exact one_div_pos.mpr (mul_pos (by positivity) T.property)
  have hscale : 2 * Real.pi * (1 / (2 * Real.pi * (T : ℝ))) * (T : ℝ) ≤ 1 := by
    have hT : (0 : ℝ) < (T : ℝ) := T.property
    field_simp
    exact le_rfl
  have hbase := integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (heathBrownPositiveCoefficient ε q) (A.product B) heathBrownPositiveProductFrequency
    hδ hscale
  have hpoly : ∀ t : ℝ,
      finiteFrequencyPoly (heathBrownPositiveCoefficient ε q) (A.product B)
          heathBrownPositiveProductFrequency t
        = heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t := fun t =>
    heathBrownPositiveProductPoly_eq_mul A B ε q t
  have hbase' :
      (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A ε t * heathBrownDenseFactor B q t‖ ^ 2)
        ≤ (5 / (4 * (1 / (2 * Real.pi * (T : ℝ)))))
            * heathBrownPositiveWeightedCollision A B q T := by
    simpa only [hpoly, heathBrownPositiveCollisionWeight_eq_weighted] using hbase
  refine hbase'.trans_eq ?_
  field_simp
  ring

/-- Reverse half for nonnegative sparse coefficients (`ε_m = 1`), again with no analytic premise. -/
theorem heathBrownPositiveWeightedCollision_le_integral_Icc_factors
    (A B : Finset PNat) (q : ℕ → Set.Icc (0 : ℝ) 1) (T : Set.Ioi (0 : ℝ)) :
    heathBrownPositiveWeightedCollision A B q T
      ≤ (5 / (4 * (T : ℝ)))
          * ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
              ‖heathBrownSparseFactor A (fun _ => 1) t * heathBrownDenseFactor B q t‖ ^ 2 := by
  have hscale : 2 * Real.pi * (T : ℝ) * (1 / (2 * Real.pi * (T : ℝ))) ≤ 1 := by
    have hT : (0 : ℝ) < (T : ℝ) := T.property
    field_simp
    exact le_rfl
  have hbase := finiteFrequencyCollisionWeight_le_integral_Icc_nnreal
    (heathBrownPositivePairWeight q) (A.product B) heathBrownPositiveProductFrequency
    T.property hscale
  have hcollision :
      finiteFrequencyCollisionWeight
          (fun p => (((heathBrownPositivePairWeight q p : ℝ) : ℂ))) (A.product B)
          heathBrownPositiveProductFrequency (1 / (2 * Real.pi * (T : ℝ)))
        = heathBrownPositiveWeightedCollision A B q T := by
    rw [finiteFrequencyCollisionWeight_nnreal_eq, heathBrownPositiveWeightedCollision]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
    rw [heathBrownPositivePairWeight, heathBrownPositivePairWeight]
    by_cases h : |heathBrownPositiveProductFrequency p - heathBrownPositiveProductFrequency r|
        < 1 / (2 * Real.pi * (T : ℝ))
    · rw [if_pos h, if_pos ((heathBrownPositiveFrequency_close_iff p r T).mp h)]
      rfl
    · rw [if_neg h, if_neg (mt (heathBrownPositiveFrequency_close_iff p r T).mpr h)]
  rw [hcollision] at hbase
  have hpoly : ∀ t : ℝ,
      finiteFrequencyPoly (fun p => (((heathBrownPositivePairWeight q p : ℝ) : ℂ)))
          (A.product B) heathBrownPositiveProductFrequency t
        = heathBrownSparseFactor A (fun _ => 1) t * heathBrownDenseFactor B q t := by
    intro t
    rw [finiteFrequencyPoly_pairWeight_eq_positiveProduct,
      heathBrownPositiveProductPoly_eq_mul]
  simpa only [hpoly] using hbase

end RHTower.Sieve
