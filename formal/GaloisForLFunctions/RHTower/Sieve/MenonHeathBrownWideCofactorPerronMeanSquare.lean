import GaloisForLFunctions.RHTower.Sieve.MenonPerronFiniteFamilyCauchy
import GaloisForLFunctions.RHTower.Sieve.MenonHeathBrownWideIntervalHandoff

/-!
# Wide Perron mean square with an unshifted cofactor

The common-width smoothing used in Menon's wide Case II is compatible with the finite-family
Perron Cauchy argument.  This file keeps an arbitrary finite Dirichlet cofactor at its original
ordinate through that handoff, then restores the literal sharp interval with the two transition
windows charged once.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction Complex MeasureTheory Set Filter
open GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 800000

/-- Common-width smoothed twisted von Mangoldt interval. -/
def menonWideVonMangoldtTwistInterval (tau : ℝ) (a b : ℕ) (H : ℝ) : ℂ :=
  (∑' n : ℕ, vonMangoldtTwist tau n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (b : ℝ) H (n : ℝ) : ℝ) : ℂ)) -
    (∑' n : ℕ, vonMangoldtTwist tau n *
      ((GaloisForLFunctions.HTGeometry.smoothWeight
        (a : ℝ) H (n : ℝ) : ℝ) : ℂ))

/-- Named form of the exact wide Perron identity. -/
theorem smul_menonWideVonMangoldtTwistInterval_eq_integral_windowRelevantAggregate
    (L X k a b : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b) (tau : ℝ)
    (T0 t : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {H sigma : ℝ} (hH : 0 < H) (hsupport : (b : ℝ) + H ≤ X)
    (hsigma : 1 < sigma) :
    (2 * Real.pi : ℝ) • menonWideVonMangoldtTwistInterval tau a b H =
      ∫ y : ℝ,
        heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
            ((sigma : ℂ) + ((y + tau : ℝ) : ℂ) * Complex.I) *
          menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y := by
  simpa only [menonWideVonMangoldtTwistInterval] using
    smul_tsum_vonMangoldtTwist_wideInterval_eq_integral_windowRelevantAggregate
      L X k a b hXL hab tau T0 t hT0 hscale hH hsupport hsigma

/-- Named transition-window estimate for the common-width interval. -/
theorem norm_menonWideVonMangoldtTwistInterval_sub_sum_Ioc_le
    (tau : ℝ) {a b : ℕ} (hab : a ≤ b) {H : ℝ} (hH : 0 < H)
    (haH : 1 ≤ (a : ℝ) + H) (hbH : 1 ≤ (b : ℝ) + H) :
    ‖menonWideVonMangoldtTwistInterval tau a b H -
        ∑ n ∈ Finset.Ioc a b, vonMangoldtTwist tau n‖ ≤
      (H + 1) * Real.log ((b : ℝ) + H) +
        (H + 1) * Real.log ((a : ℝ) + H) := by
  simpa only [menonWideVonMangoldtTwistInterval] using
    norm_tsum_vonMangoldtTwist_wideInterval_sub_sum_Ioc_le tau hab hH haH hbH

/-- A common-width Mellin difference has integrable modulus under a Lorentzian majorant. -/
theorem integrable_norm_menonWideIntervalMellinKernel
    {a b H sigma C : ℝ} (hH : 0 < H) (hsigma : 0 < sigma) (hC : 0 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonWideIntervalMellinKernel a b H sigma y‖ ≤ C * (1 + y ^ 2)⁻¹) :
    Integrable fun y : ℝ => ‖menonWideIntervalMellinKernel a b H sigma y‖ := by
  have hmajor : Integrable fun y : ℝ => C * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul C
  refine Integrable.mono' hmajor
    (continuous_menonWideIntervalMellinKernel hH hsigma).norm.aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hkernel y

/-- Finite-family weighted Cauchy for the wide kernel, with the kernel replaced by its
Lorentzian majorant and every fixed shift retained under the integral. -/
theorem sum_norm_integral_menonWideIntervalMellinKernel_sq_le
    {alpha : Type*} (S : Finset alpha) (F : alpha → ℝ → ℂ)
    {a b H sigma C : ℝ} (hH : 0 < H) (hsigma : 0 < sigma) (hC : 0 ≤ C)
    (hF : ∀ r ∈ S, AEStronglyMeasurable (F r) volume)
    (hkernel : ∀ y : ℝ,
      ‖menonWideIntervalMellinKernel a b H sigma y‖ ≤ C * (1 + y ^ 2)⁻¹)
    (hE : ∀ r ∈ S,
      Integrable fun y : ℝ => ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) :
    ∑ r ∈ S,
        ‖∫ y : ℝ, F r y * menonWideIntervalMellinKernel a b H sigma y‖ ^ 2 ≤
      C ^ 2 * Real.pi *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
  let K : ℝ → ℂ := menonWideIntervalMellinKernel a b H sigma
  have hKm : AEStronglyMeasurable K volume :=
    (continuous_menonWideIntervalMellinKernel hH hsigma).aestronglyMeasurable
  have hKint : Integrable fun y : ℝ => ‖K y‖ :=
    integrable_norm_menonWideIntervalMellinKernel hH hsigma hC hkernel
  have hEr : ∀ r ∈ S, Integrable fun y : ℝ => ‖F r y‖ ^ 2 * ‖K y‖ := by
    intro r hr
    have hmajor : Integrable fun y : ℝ => C *
        (‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) := (hE r hr).const_mul C
    refine Integrable.mono' hmajor ((hF r hr).norm.pow 2 |>.mul hKm.norm) ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ‖F r y‖ ^ 2 * ‖K y‖)]
    have hm := mul_le_mul_of_nonneg_left (hkernel y) (sq_nonneg ‖F r y‖)
    calc
      ‖F r y‖ ^ 2 * ‖K y‖ ≤ ‖F r y‖ ^ 2 * (C * (1 + y ^ 2)⁻¹) := hm
      _ = C * (‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by ring
  have hbase := sum_norm_integral_mul_sq_le S F K hF hKm hKint hEr
  have hKmass : (∫ y : ℝ, ‖K y‖) ≤ C * Real.pi := by
    have hmajor : Integrable fun y : ℝ => C * (1 + y ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul C
    have hmono := integral_mono hKint hmajor hkernel
    rw [integral_const_mul, show (∫ y : ℝ, (1 + y ^ 2)⁻¹) = Real.pi by
      simpa using (integral_inv_sq_add_sq (a := (1 : ℝ)) (by norm_num))] at hmono
    exact hmono
  have henergy :
      ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ ≤
        C * ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
    calc
      ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ ≤
          ∑ r ∈ S, C * ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hmono := integral_mono (hEr r hr) ((hE r hr).const_mul C) (fun y => by
          have hm := mul_le_mul_of_nonneg_left (hkernel y) (sq_nonneg ‖F r y‖)
          calc
            ‖F r y‖ ^ 2 * ‖K y‖ ≤
                ‖F r y‖ ^ 2 * (C * (1 + y ^ 2)⁻¹) := hm
            _ = C * (‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) := by ring)
        simpa only [integral_const_mul] using hmono
      _ = C * ∑ r ∈ S, ∫ y : ℝ,
          ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by rw [Finset.mul_sum]
  have hmass0 : 0 ≤ ∫ y : ℝ, ‖K y‖ := integral_nonneg fun _ => norm_nonneg _
  have henergy0 : 0 ≤ ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ := by
    positivity
  calc
    _ ≤ (∫ y : ℝ, ‖K y‖) *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * ‖K y‖ := hbase
    _ ≤ (C * Real.pi) *
        (C * ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) :=
      mul_le_mul hKmass henergy henergy0 (mul_nonneg hC Real.pi_pos.le)
    _ = C ^ 2 * Real.pi *
        ∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by ring

/-- Exact common-width Perron handoff for a finite family, with an arbitrary finite Dirichlet
cofactor retained at the unshifted ordinate. -/
theorem sum_normSq_wideVonMangoldtTwist_mul_dirPoly_le_fixedShiftPerron
    (L X k a b M : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b)
    (T0 t : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {H sigma C : ℝ} (hH : 0 < H) (hsupport : (b : ℝ) + H ≤ X)
    (hsigma : 1 < sigma) (hC : 0 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (S : Finset ℕ) (tau : ℕ → ℝ) (d : Fin M → ℂ) :
    ∑ r ∈ S,
        ‖((2 * Real.pi : ℝ) •
            menonWideVonMangoldtTwistInterval (tau r) a b H) *
          dirPoly M d (-tau r)‖ ^ 2 ≤
      C ^ 2 * Real.pi *
        ∫ y : ℝ,
          (∑ r ∈ S,
            ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
                ((sigma : ℂ) + ((y + tau r : ℝ) : ℂ) * Complex.I) *
              dirPoly M d (-tau r)‖ ^ 2) * (1 + y ^ 2)⁻¹ := by
  let A : ℕ → ℝ → ℂ := fun r y =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
      ((sigma : ℂ) + ((y + tau r : ℝ) : ℂ) * Complex.I)
  let D : ℕ → ℂ := fun r => dirPoly M d (-tau r)
  let F : ℕ → ℝ → ℂ := fun r y => A r y * D r
  have haR : (0 : ℝ) < (a : ℝ) := by
    have hleft : (0 : ℝ) < ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t := by
      exact mul_pos (by positivity) (Real.rpow_pos_of_pos (by linarith) _)
    exact hleft.trans_le hscale
  have haPos : 0 < a := by exact_mod_cast haR
  have hbPos : 0 < b := haPos.trans_le hab
  have hX : 1 ≤ X := by
    have hbX : b ≤ X := by
      have hbR : (b : ℝ) ≤ (X : ℝ) := by linarith
      exact_mod_cast hbR
    exact (Nat.succ_le_iff.mpr haPos).trans (hab.trans hbX)
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X k (a : ℝ) sigma
  have hFcont : ∀ r : ℕ, Continuous (F r) := by
    intro r
    have hshift : Continuous (fun y : ℝ => y + tau r) :=
      continuous_id.add continuous_const
    have hAcont : Continuous (A r) :=
      (continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
        L X k T0 t (a : ℝ) sigma).comp hshift
    exact hAcont.mul continuous_const
  have hAbound : ∀ r y, ‖A r y‖ ≤ P := by
    intro r y
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X k hX T0 t (a : ℝ) sigma (y + tau r) haR (by linarith)
  have hE : ∀ r ∈ S,
      Integrable fun y : ℝ => ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹ := by
    intro r _hr
    have hweightCont : Continuous fun y : ℝ => (1 + y ^ 2)⁻¹ :=
      (continuous_const.add (continuous_id.pow 2)).inv₀ (fun y => by
        simp only [Pi.add_apply, Pi.pow_apply, id_eq]
        exact ne_of_gt (by positivity))
    have hmajor : Integrable fun y : ℝ =>
        (P * ‖D r‖) ^ 2 * (1 + y ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul ((P * ‖D r‖) ^ 2)
    refine Integrable.mono' hmajor
      (((hFcont r).norm.pow 2).mul hweightCont).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹)]
    have hFnorm : ‖F r y‖ ≤ P * ‖D r‖ := by
      rw [show ‖F r y‖ = ‖A r y‖ * ‖D r‖ by simp only [F, norm_mul]]
      exact mul_le_mul_of_nonneg_right (hAbound r y) (norm_nonneg _)
    have hsq := pow_le_pow_left₀ (norm_nonneg (F r y)) hFnorm 2
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  have hbase :=
    sum_norm_integral_menonWideIntervalMellinKernel_sq_le S F hH (by linarith) hC
      (fun r _hr => (hFcont r).aestronglyMeasurable) hkernel hE
  have hperron : ∀ r : ℕ,
      ((2 * Real.pi : ℝ) •
          menonWideVonMangoldtTwistInterval (tau r) a b H) * D r =
        ∫ y : ℝ, F r y *
          menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y := by
    intro r
    rw [smul_menonWideVonMangoldtTwistInterval_eq_integral_windowRelevantAggregate
      L X k a b hXL hab (tau r) T0 t hT0 hscale hH hsupport hsigma]
    rw [← MeasureTheory.integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    simp only [F, A, D]
    ring
  have hleft :
      (∑ r ∈ S,
        ‖((2 * Real.pi : ℝ) •
            menonWideVonMangoldtTwistInterval (tau r) a b H) *
          dirPoly M d (-tau r)‖ ^ 2) =
        ∑ r ∈ S, ‖∫ y : ℝ, F r y *
          menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro r _hr
    rw [show dirPoly M d (-tau r) = D r by rfl, hperron r]
  have hswap :
      (∑ r ∈ S, ∫ y : ℝ, ‖F r y‖ ^ 2 * (1 + y ^ 2)⁻¹) =
        ∫ y : ℝ, (∑ r ∈ S, ‖F r y‖ ^ 2) * (1 + y ^ 2)⁻¹ := by
    rw [← MeasureTheory.integral_finset_sum]
    · apply integral_congr_ae
      filter_upwards with y
      rw [Finset.sum_mul]
    · intro r hr
      exact hE r hr
  rw [hleft]
  refine hbase.trans ?_
  rw [hswap]

/-- Restoring the sharp von Mangoldt interval costs only the two literal common-width transition
windows, even after multiplication by an arbitrary finite cofactor. -/
theorem sum_normSq_vonMangoldtTwist_mul_dirPoly_le_wideFixedShiftPerron
    (L X k a b M : ℕ) (hXL : X < (L + 1) ^ k) (hab : a ≤ b)
    (T0 t : ℝ) (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ (a : ℝ))
    {H sigma C : ℝ} (hH : 0 < H) (haH : 1 ≤ (a : ℝ) + H)
    (hbH : 1 ≤ (b : ℝ) + H) (hsupport : (b : ℝ) + H ≤ X)
    (hsigma : 1 < sigma) (hC : 0 ≤ C)
    (hkernel : ∀ y : ℝ,
      ‖menonWideIntervalMellinKernel (a : ℝ) (b : ℝ) H sigma y‖ ≤
        C * (1 + y ^ 2)⁻¹)
    (S : Finset ℕ) (tau : ℕ → ℝ) (d : Fin M → ℂ) :
    ∑ r ∈ S,
        ‖((2 * Real.pi : ℝ) •
            (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist (tau r) n)) *
          dirPoly M d (-tau r)‖ ^ 2 ≤
      2 * (C ^ 2 * Real.pi *
        ∫ y : ℝ,
          (∑ r ∈ S,
            ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
                ((sigma : ℂ) + ((y + tau r : ℝ) : ℂ) * Complex.I) *
              dirPoly M d (-tau r)‖ ^ 2) * (1 + y ^ 2)⁻¹) +
      8 * Real.pi ^ 2 *
        (((H + 1) * Real.log ((b : ℝ) + H) +
          (H + 1) * Real.log ((a : ℝ) + H)) ^ 2) *
        ∑ r ∈ S, ‖dirPoly M d (-tau r)‖ ^ 2 := by
  let W : ℕ → ℂ := fun r =>
    menonWideVonMangoldtTwistInterval (tau r) a b H
  let P : ℕ → ℂ := fun r => ∑ n ∈ Finset.Ioc a b, vonMangoldtTwist (tau r) n
  let D : ℕ → ℂ := fun r => dirPoly M d (-tau r)
  let E : ℝ := (H + 1) * Real.log ((b : ℝ) + H) +
    (H + 1) * Real.log ((a : ℝ) + H)
  have hwide := sum_normSq_wideVonMangoldtTwist_mul_dirPoly_le_fixedShiftPerron
    L X k a b M hXL hab T0 t hT0 hscale hH hsupport hsigma hC hkernel S tau d
  have herr : ∀ r : ℕ, ‖P r - W r‖ ≤ E := by
    intro r
    have hraw := norm_menonWideVonMangoldtTwistInterval_sub_sum_Ioc_le
      (tau r) hab hH haH hbH
    rw [norm_sub_rev] at hraw
    simpa only [P, W, E] using hraw
  have hpoint : ∀ r : ℕ,
      ‖((2 * Real.pi : ℝ) • P r) * D r‖ ^ 2 ≤
        2 * ‖((2 * Real.pi : ℝ) • W r) * D r‖ ^ 2 +
          8 * Real.pi ^ 2 * E ^ 2 * ‖D r‖ ^ 2 := by
    intro r
    have hdecomp : ((2 * Real.pi : ℝ) • P r) * D r =
        ((2 * Real.pi : ℝ) • W r) * D r +
          ((2 * Real.pi : ℝ) • (P r - W r)) * D r := by
      rw [smul_sub]
      ring
    have htri := norm_add_le
      (((2 * Real.pi : ℝ) • W r) * D r)
      (((2 * Real.pi : ℝ) • (P r - W r)) * D r)
    rw [← hdecomp] at htri
    have hsq := pow_le_pow_left₀
      (norm_nonneg (((2 * Real.pi : ℝ) • P r) * D r)) htri 2
    have hsum :
        ‖((2 * Real.pi : ℝ) • P r) * D r‖ ^ 2 ≤
          2 * ‖((2 * Real.pi : ℝ) • W r) * D r‖ ^ 2 +
            2 * ‖((2 * Real.pi : ℝ) • (P r - W r)) * D r‖ ^ 2 := by
      nlinarith [sq_nonneg
        (‖((2 * Real.pi : ℝ) • W r) * D r‖ -
          ‖((2 * Real.pi : ℝ) • (P r - W r)) * D r‖)]
    have herrTerm :
        ‖((2 * Real.pi : ℝ) • (P r - W r)) * D r‖ ^ 2 ≤
          4 * Real.pi ^ 2 * E ^ 2 * ‖D r‖ ^ 2 := by
      rw [norm_mul, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
      have hsquare := pow_le_pow_left₀ (norm_nonneg (P r - W r)) (herr r) 2
      have hmul := mul_le_mul_of_nonneg_right hsquare (sq_nonneg ‖D r‖)
      nlinarith
    calc
      ‖((2 * Real.pi : ℝ) • P r) * D r‖ ^ 2 ≤
          2 * ‖((2 * Real.pi : ℝ) • W r) * D r‖ ^ 2 +
            2 * ‖((2 * Real.pi : ℝ) • (P r - W r)) * D r‖ ^ 2 := hsum
      _ ≤ 2 * ‖((2 * Real.pi : ℝ) • W r) * D r‖ ^ 2 +
          2 * (4 * Real.pi ^ 2 * E ^ 2 * ‖D r‖ ^ 2) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left herrTerm (by norm_num))
      _ = _ := by ring
  calc
    ∑ r ∈ S,
        ‖((2 * Real.pi : ℝ) •
            (∑ n ∈ Finset.Ioc a b, vonMangoldtTwist (tau r) n)) *
          dirPoly M d (-tau r)‖ ^ 2 =
        ∑ r ∈ S, ‖((2 * Real.pi : ℝ) • P r) * D r‖ ^ 2 := by rfl
    _ ≤ ∑ r ∈ S,
        (2 * ‖((2 * Real.pi : ℝ) • W r) * D r‖ ^ 2 +
          8 * Real.pi ^ 2 * E ^ 2 * ‖D r‖ ^ 2) :=
      Finset.sum_le_sum fun r _hr => hpoint r
    _ = 2 * ∑ r ∈ S, ‖((2 * Real.pi : ℝ) • W r) * D r‖ ^ 2 +
        8 * Real.pi ^ 2 * E ^ 2 * ∑ r ∈ S, ‖D r‖ ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (C ^ 2 * Real.pi *
          ∫ y : ℝ,
            (∑ r ∈ S,
              ‖heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t (a : ℝ)
                  ((sigma : ℂ) + ((y + tau r : ℝ) : ℂ) * Complex.I) *
                dirPoly M d (-tau r)‖ ^ 2) * (1 + y ^ 2)⁻¹) +
        8 * Real.pi ^ 2 * E ^ 2 * ∑ r ∈ S, ‖D r‖ ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hwide (by norm_num)) le_rfl
    _ = _ := by simp only [E, D]

end RHTower.Sieve
