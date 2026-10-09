import GaloisForLFunctions.RHTower.StretchedBoseSeparator
import GaloisForLFunctions.RHTower.ChronologicalRiemannEquivalence

/-!
# RH as a completeness problem for stretched Bose kernels

For `a > 0` let `f_a(t) = e^{-t^a}` and `D_a(t) = Γ(1/a+1)/t - Σ_{n ≥ 1} f_a(nt)`.

**Theorem** (`riemannHypothesis_iff_kernelL2_mem_closure`).  For every `a > 1`, RH holds iff `f_a`
lies in the closed linear span of the integer dilates `D_a(k·)`, `k ≥ 1`, in `L²(0,∞)`.

* `⟹` (`kernelL2_mem_closure_of_riemannHypothesis`, valid for every `a > 0`).  For a finite row
  `c`, `f_a + Σ c_k D_a(k·)` has Mellin transform `F_a(s)(1 - ζ(s)C(s))`, `F_a(s) = Γ(s/a)/a`.
  Since `|F_a(1/2+it)| ≤ C e^{-(π/(4a))|t|}`, the Báez-Duarte Riesz rows make it small under RH,
  exactly as for the Bose kernel `a = 1`.
* `⟸` is `riemannHypothesis_of_kernelL2_mem_closure` (sinc separator).

At `a = 1` the span is dense unconditionally (`boseDilateL2_span_dense`), and RH is the size of the
coefficients instead.  The dividing line is the decay rate `π/(2a)` of `F_a` against the
Carlson rate `π/2` of `log ℕ`.
-/

open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate InnerProductSpace

noncomputable section

namespace RHTower.StretchedBose

open GaloisForLFunctions.HTGeometry
open RHTower.SincSeparator

variable {a : ℝ}

theorem mellinFactor_half (a t : ℝ) (ha : a ≠ 0) :
    mellinFactor a (1 / 2 + (t : ℂ) * I) =
      Complex.Gamma (((1 / (2 * a) : ℝ) : ℂ) + ((t / a : ℝ) : ℂ) * I) / a := by
  unfold mellinFactor
  congr 2
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  push_cast
  field_simp

/-- `|F_a(1/2 + it)| ≤ C e^{-(π/(4a))|t|}`. -/
theorem exists_norm_mellinFactor_half_le (ha0 : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖mellinFactor a (1 / 2 + (t : ℂ) * I)‖ ≤
      C * Real.exp (-(Real.pi / (4 * a) * |t|)) := by
  set x : ℝ := 1 / (2 * a) with hx
  have hx0 : 0 < x := by positivity
  obtain ⟨C₁, N, hC₁, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip x x
  have hδ : (0 : ℝ) < Real.pi / 4 := by positivity
  obtain ⟨M, hM⟩ := exists_pow_mul_exp_neg_le hδ N
  have hM0 : 0 ≤ M := by
    have h0 : 0 < |(1 : ℝ)| ^ N * Real.exp (-(Real.pi / 4 * |(1 : ℝ)|)) := by positivity
    have h1 : 0 < (1 + (1 : ℝ) ^ 2)⁻¹ := by positivity
    have h2 := lt_of_lt_of_le h0 (hM 1 (by norm_num))
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg.le h1.le
    linarith
  refine ⟨(C₁ * M + Real.Gamma x * Real.exp (Real.pi / 4)) / a, by positivity, fun t => ?_⟩
  rw [mellinFactor_half a t ha0.ne', norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ha0]
  set y : ℝ := t / a with hy
  have hyt : Real.pi / 4 * |y| = Real.pi / (4 * a) * |t| := by
    rw [hy, abs_div, abs_of_pos ha0]; field_simp
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha0]
  have hz : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have hzim : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  rcases le_or_gt 1 |y| with hbig | hsmall
  · have h1 := hΓ _ (by rw [hz]) (by rw [hz]) (by rw [hzim]; exact hbig)
    rw [hzim] at h1
    have hpow : |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) ≤ M * Real.exp (-(Real.pi / 4 * |y|)) := by
      have h2 := hM y hbig
      have hsplit : Real.exp (-(Real.pi * |y| / 2)) =
          Real.exp (-(Real.pi / 4 * |y|)) * Real.exp (-(Real.pi / 4 * |y|)) := by
        rw [← Real.exp_add]; ring_nf
      rw [hsplit, ← mul_assoc]
      have hinv : (1 + y ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg y])
      have h3 : |y| ^ N * Real.exp (-(Real.pi / 4 * |y|)) ≤ M :=
        h2.trans (by nlinarith)
      exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    calc ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖
        ≤ C₁ * |y| ^ N * Real.exp (-(Real.pi * |y| / 2)) := h1
      _ = C₁ * (|y| ^ N * Real.exp (-(Real.pi * |y| / 2))) := by ring
      _ ≤ C₁ * (M * Real.exp (-(Real.pi / 4 * |y|))) := by gcongr
      _ ≤ (C₁ * M + Real.Gamma x * Real.exp (Real.pi / 4)) * Real.exp (-(Real.pi / 4 * |y|)) := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have : 0 ≤ Real.Gamma x * Real.exp (Real.pi / 4) :=
            mul_nonneg (Real.Gamma_pos_of_pos hx0).le (Real.exp_pos _).le
          linarith
      _ = _ := by rw [hyt]
  · have h1 : ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ Real.Gamma x := by
      have := GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re (s := (x : ℂ) + (y : ℂ) * I)
        (by rw [hz]; exact hx0)
      rwa [hz] at this
    have hexp : 1 ≤ Real.exp (Real.pi / 4) * Real.exp (-(Real.pi / 4 * |y|)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [Real.pi_pos, abs_nonneg y])
    calc ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ ≤ Real.Gamma x := h1
      _ ≤ Real.Gamma x * (Real.exp (Real.pi / 4) * Real.exp (-(Real.pi / 4 * |y|))) :=
          le_mul_of_one_le_right (Real.Gamma_pos_of_pos hx0).le hexp
      _ ≤ (C₁ * M + Real.Gamma x * Real.exp (Real.pi / 4)) * Real.exp (-(Real.pi / 4 * |y|)) := by
          rw [← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have : 0 ≤ C₁ * M := mul_nonneg hC₁ hM0
          linarith
      _ = _ := by rw [hyt]

/-- `|F_a(1/2 + it)|² ≤ K/(1/4 + t²)`. -/
theorem exists_norm_sq_mellinFactor_half_le (ha0 : 0 < a) :
    ∃ K : ℝ, ∀ t : ℝ, ‖mellinFactor a (1 / 2 + (t : ℂ) * I)‖ ^ 2 ≤ K / (1 / 4 + t ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellinFactor_half_le ha0
  refine ⟨C ^ 2 * (1 / 4 + 8 * a ^ 2 / Real.pi ^ 2), fun t => ?_⟩
  have hden : 0 < 1 / 4 + t ^ 2 := by positivity
  rw [le_div_iff₀ hden]
  set y : ℝ := Real.pi / (2 * a) * |t| with hy
  have hy0 : 0 ≤ y := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy0
  have hE : Real.exp (-(Real.pi / (4 * a) * |t|)) ^ 2 = Real.exp (-y) := by
    rw [← Real.exp_nat_mul]; congr 1; rw [hy]; push_cast; ring
  have hsq := pow_le_pow_left₀ (norm_nonneg _) (hC t) 2
  rw [mul_pow, hE] at hsq
  have ht2 : t ^ 2 * Real.exp (-y) ≤ 8 * a ^ 2 / Real.pi ^ 2 := by
    have hyt : t ^ 2 = (2 * a / Real.pi) ^ 2 * y ^ 2 := by
      rw [hy, mul_pow, div_pow, sq_abs]; field_simp
    rw [hyt, Real.exp_neg]
    have hEpos : 0 < Real.exp y := Real.exp_pos y
    rw [mul_inv_le_iff₀ hEpos]
    have : y ^ 2 ≤ 2 * Real.exp y := by nlinarith
    calc (2 * a / Real.pi) ^ 2 * y ^ 2 ≤ (2 * a / Real.pi) ^ 2 * (2 * Real.exp y) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 8 * a ^ 2 / Real.pi ^ 2 * Real.exp y := by ring
  have hE1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  calc ‖mellinFactor a (1 / 2 + (t : ℂ) * I)‖ ^ 2 * (1 / 4 + t ^ 2)
      ≤ C ^ 2 * Real.exp (-y) * (1 / 4 + t ^ 2) := mul_le_mul_of_nonneg_right hsq hden.le
    _ = C ^ 2 * (1 / 4 * Real.exp (-y) + t ^ 2 * Real.exp (-y)) := by ring
    _ ≤ C ^ 2 * (1 / 4 + 8 * a ^ 2 / Real.pi ^ 2) := by
        gcongr
        · linarith

/-- `‖ζ(1/2 + it)‖ ≤ 18 (1 + |t|)`. -/
theorem norm_riemannZeta_half_le (t : ℝ) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ 18 * (1 + |t|) := by
  set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hsep : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have h1 : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have h2 : (s - 1).re = -(1 / 2) := by simp [hs]; norm_num
    rw [h2] at h1; norm_num at h1; linarith
  have hb := norm_riemannZeta_le_sqrt_norm_add_two_half (s := s) (by rw [hre])
    (by norm_num : (0 : ℝ) < 1 / 2) hsep
  have hsn : ‖s‖ ≤ 1 / 2 + |t| := by
    calc ‖s‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 1 / 2 + |t| := by simp
  have hsqrt : Real.sqrt (‖s‖ + 2) ≤ 3 * (1 + |t|) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [abs_nonneg t, norm_nonneg s]
  calc ‖riemannZeta s‖ ≤ (2 + 1 / (1 / 2) + 2) * Real.sqrt (‖s‖ + 2) := hb
    _ ≤ 6 * (3 * (1 + |t|)) := by norm_num; nlinarith [Real.sqrt_nonneg (‖s‖ + 2)]
    _ = 18 * (1 + |t|) := by ring

theorem continuous_mellinFactor_mul_zeta_mellinLinePoint (ha0 : 0 < a) :
    Continuous fun ξ : ℝ => mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  have hF : ContinuousAt (mellinFactor a) (mellinLinePoint ξ) :=
    (analyticAt_mellinFactor ha0 (by rw [mellinLinePoint_re]; norm_num)).continuousAt
  have hZ : ContinuousAt riemannZeta (mellinLinePoint ξ) :=
    (differentiableAt_riemannZeta (mellinLinePoint_ne_one ξ)).continuousAt
  exact (hF.comp continuous_mellinLinePoint.continuousAt).mul
    (hZ.comp continuous_mellinLinePoint.continuousAt)

/-- `ξ ↦ |F_a ζ(s(ξ))|²` is integrable. -/
theorem integrable_norm_mellinFactor_mul_zeta_sq (ha0 : 0 < a) :
    Integrable fun ξ : ℝ =>
      ‖mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellinFactor_half_le ha0
  set δ : ℝ := Real.pi / (4 * a) * (2 * Real.pi) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨M, hM⟩ := exists_pow_mul_exp_neg_le hδ 2
  have hM0 : 0 ≤ M := by
    have h0 : 0 < |(1 : ℝ)| ^ 2 * Real.exp (-(δ * |(1 : ℝ)|)) := by positivity
    have h1 : 0 < (1 + (1 : ℝ) ^ 2)⁻¹ := by positivity
    have h2 := lt_of_lt_of_le h0 (hM 1 (by norm_num))
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg.le h1.le
    linarith
  set B : ℝ := (18 * C) ^ 2 * (2 * (1 + 4 * Real.pi ^ 2) * M + 2 * (1 + 2 * Real.pi) ^ 2) with hB
  refine (integrable_inv_one_add_sq.const_mul B).mono'
    ((continuous_mellinFactor_mul_zeta_mellinLinePoint ha0).norm.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mellinLinePoint_eq]
  set t : ℝ := -(2 * Real.pi * ξ) with ht
  have hat : |t| = 2 * Real.pi * |ξ| := by
    rw [ht, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  set E : ℝ := Real.exp (-(δ * |ξ|)) with hE
  have hexp : Real.exp (-(Real.pi / (4 * a) * |t|)) = E := by
    rw [hE, hat, hδdef]; ring_nf
  have hprod : ‖mellinFactor a (1 / 2 + (t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤
      18 * C * ((1 + |t|) * E) := by
    rw [norm_mul, ← hexp]
    calc ‖mellinFactor a (1 / 2 + (t : ℂ) * I)‖ * ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖
        ≤ (C * Real.exp (-(Real.pi / (4 * a) * |t|))) * (18 * (1 + |t|)) :=
          mul_le_mul (hC t) (norm_riemannZeta_half_le t) (norm_nonneg _) (by positivity)
      _ = 18 * C * ((1 + |t|) * Real.exp (-(Real.pi / (4 * a) * |t|))) := by ring
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hprod 2
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ δ * |ξ| := by positivity
    linarith)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hpos : 0 < 1 + ξ ^ 2 := by positivity
  have hcore : ((1 + |t|) * E) ^ 2 ≤
      (2 * (1 + 4 * Real.pi ^ 2) * M + 2 * (1 + 2 * Real.pi) ^ 2) * (1 + ξ ^ 2)⁻¹ := by
    have hEE : E ^ 2 ≤ E := by rw [sq]; exact mul_le_of_le_one_left hE0 hE1
    rcases le_or_gt 1 |ξ| with hξ | hξ
    · have hm := hM ξ hξ
      have hξsq : 1 ≤ |ξ| ^ 2 := by nlinarith
      have h1 : (1 + |t|) ^ 2 ≤ 2 * (1 + 4 * Real.pi ^ 2) * |ξ| ^ 2 := by
        rw [hat]; nlinarith [sq_nonneg (2 * Real.pi * |ξ| - 1), Real.pi_pos, abs_nonneg ξ]
      calc ((1 + |t|) * E) ^ 2 = (1 + |t|) ^ 2 * E ^ 2 := by ring
        _ ≤ (2 * (1 + 4 * Real.pi ^ 2) * |ξ| ^ 2) * E :=
            mul_le_mul h1 hEE (by positivity) (by positivity)
        _ = 2 * (1 + 4 * Real.pi ^ 2) * (|ξ| ^ 2 * E) := by ring
        _ ≤ 2 * (1 + 4 * Real.pi ^ 2) * (M * (1 + ξ ^ 2)⁻¹) := by gcongr
        _ ≤ _ := by
            rw [← mul_assoc]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : 0 ≤ 2 * (1 + 2 * Real.pi) ^ 2 := by positivity
            linarith
    · have ht' : |t| ≤ 2 * Real.pi := by rw [hat]; nlinarith [Real.pi_pos]
      have hinv : 1 ≤ 2 * (1 + ξ ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        have : ξ ^ 2 ≤ 1 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
        linarith
      calc ((1 + |t|) * E) ^ 2 ≤ (1 + 2 * Real.pi) ^ 2 * 1 := by
            rw [mul_pow]
            exact mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) 2)
              (pow_le_one₀ hE0 hE1) (by positivity) (by positivity)
        _ ≤ (1 + 2 * Real.pi) ^ 2 * (2 * (1 + ξ ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ ≤ _ := by
            rw [← mul_assoc, mul_comm ((1 + 2 * Real.pi) ^ 2) 2]
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            have : 0 ≤ 2 * (1 + 4 * Real.pi ^ 2) * M := by positivity
            linarith
  calc ‖mellinFactor a (1 / 2 + (t : ℂ) * I) * riemannZeta (1 / 2 + (t : ℂ) * I)‖ ^ 2
      ≤ (18 * C * ((1 + |t|) * E)) ^ 2 := hsq
    _ = (18 * C) ^ 2 * ((1 + |t|) * E) ^ 2 := by ring
    _ ≤ (18 * C) ^ 2 * ((2 * (1 + 4 * Real.pi ^ 2) * M + 2 * (1 + 2 * Real.pi) ^ 2) *
          (1 + ξ ^ 2)⁻¹) := by gcongr
    _ = B * (1 + ξ ^ 2)⁻¹ := by rw [hB]; ring

/-! ## The approximants -/

theorem Lp_coeFn_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 (volume : Measure ℝ)) :
    ((∑ i ∈ s, f i : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume]
      fun x => ∑ i ∈ s, (f i : ℝ → ℂ) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert hi]

/-- `f_a + Σ_{k ≤ N} c_k D_a(k·)` as a vector of `L²((0,∞))`. -/
def approxL2 (ha0 : 0 < a) (c : ℕ → ℝ) (N : ℕ) : HalfLineL2 :=
  kernelL2 ha0 + ∑ k ∈ Finset.Ioc 0 N, ((c k : ℝ) : ℂ) • defectDilateL2 ha0 (k - 1)

theorem halfLineMellinUnitary_approxL2 (ha0 : 0 < a) (c : ℕ → ℝ) (N : ℕ) :
    (halfLineMellinUnitary (approxL2 ha0 c N) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mellinFactor a (mellinLinePoint ξ) *
        (1 - riemannZeta (mellinLinePoint ξ) * chronologicalRowPoly c N (mellinLinePoint ξ)) := by
  unfold approxL2
  rw [map_add, map_sum]
  simp only [map_smul]
  have hterms : ∀ k ∈ Finset.Ioc 0 N,
      (((((c k : ℝ) : ℂ) • halfLineMellinUnitary (defectDilateL2 ha0 (k - 1)) :
        Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) =ᵐ[volume]
        fun ξ => ((c k : ℝ) : ℂ) * -((k : ℂ) ^ (-mellinLinePoint ξ) *
          mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) := by
    intro k hk
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Finset.mem_Ioc.mp hk).1
    filter_upwards [Lp.coeFn_smul ((c k : ℝ) : ℂ) (halfLineMellinUnitary (defectDilateL2 ha0 (k - 1))),
      halfLineMellinUnitary_defectDilateL2 ha0 (k - 1)] with ξ h1 h2
    rw [h1, Pi.smul_apply, h2, hk1, smul_eq_mul]
  have hsum : ((∑ k ∈ Finset.Ioc 0 N, ((c k : ℝ) : ℂ) •
      halfLineMellinUnitary (defectDilateL2 ha0 (k - 1)) : Lp ℂ 2 (volume : Measure ℝ)) :
        ℝ → ℂ) =ᵐ[volume] fun ξ => ∑ k ∈ Finset.Ioc 0 N, ((c k : ℝ) : ℂ) *
          -((k : ℂ) ^ (-mellinLinePoint ξ) * mellinFactor a (mellinLinePoint ξ) *
            riemannZeta (mellinLinePoint ξ)) := by
    refine (Lp_coeFn_finset_sum _ _).trans ?_
    have hall : ∀ᵐ ξ ∂(volume : Measure ℝ), ∀ k ∈ Finset.Ioc 0 N,
        ((((((c k : ℝ) : ℂ) • halfLineMellinUnitary (defectDilateL2 ha0 (k - 1)) :
          Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)) ξ) =
        ((c k : ℝ) : ℂ) * -((k : ℂ) ^ (-mellinLinePoint ξ) *
          mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)) :=
      (ae_ball_iff (Finset.Ioc 0 N).countable_toSet).mpr fun k hk => hterms k hk
    filter_upwards [hall] with ξ hξ
    exact Finset.sum_congr rfl hξ
  filter_upwards [Lp.coeFn_add (halfLineMellinUnitary (kernelL2 ha0)) _,
    halfLineMellinUnitary_kernelL2 ha0, hsum] with ξ h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  unfold chronologicalRowPoly
  rw [mul_sub, mul_one, Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem norm_approxL2_sq (ha0 : 0 < a) (c : ℕ → ℝ) (N : ℕ) :
    ‖approxL2 ha0 c N‖ ^ 2 = ∫ ξ : ℝ, ‖mellinFactor a (mellinLinePoint ξ) *
      (1 - riemannZeta (mellinLinePoint ξ) * chronologicalRowPoly c N (mellinLinePoint ξ))‖ ^ 2 := by
  rw [← halfLineMellinUnitary.norm_map, Lp_two_norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [halfLineMellinUnitary_approxL2 ha0 c N] with ξ hξ
  rw [hξ]

/-! ## Báez-Duarte rows -/

/-- The Riesz rows control `‖f_a + Σ c_k D_a(k·)‖²` by the Báez-Duarte line integral. -/
theorem norm_approxL2_bdRiesz_sq_le (ha0 : 0 < a) {K : ℝ}
    (hK : ∀ t : ℝ, ‖mellinFactor a (1 / 2 + (t : ℂ) * I)‖ ^ 2 ≤ K / (1 / 4 + t ^ 2)) (N : ℕ) (δ : ℝ) :
    ‖approxL2 ha0 (fun k => -bdRieszCoeff N δ k) N‖ ^ 2 ≤
      K / Real.pi * (∫ t : ℝ, ‖1 + riemannZeta (1 / 2 + t * I) *
          bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) +
        2 * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2 * ∫ ξ : ℝ,
          ‖mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
  set Q := moebiusRieszPoly N (1 + δ) with hQ
  set P := bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) with hP
  set H : ℝ → ℝ := fun t => ‖1 + riemannZeta (1 / 2 + t * I) * P (1 / 2 + t * I)‖ ^ 2 /
    (1 / 4 + t ^ 2) with hH
  have hS : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  obtain ⟨hHint, -⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS (bdRieszCoeff N δ)
  have hHint' : Integrable H := hHint
  have hFZ := integrable_norm_mellinFactor_mul_zeta_sq ha0
  have hK0 : 0 ≤ K := by
    have := (sq_nonneg ‖mellinFactor a (1 / 2 + ((0 : ℝ) : ℂ) * I)‖).trans (hK 0)
    have hpos : (0 : ℝ) < 1 / 4 + 0 ^ 2 := by norm_num
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hpos))
  have hcov : (∫ ξ : ℝ, H (-(2 * Real.pi) * ξ)) = (2 * Real.pi)⁻¹ * ∫ t : ℝ, H t := by
    rw [Measure.integral_comp_mul_left H (-(2 * Real.pi))]
    rw [smul_eq_mul, inv_neg, abs_neg, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hHcomp : Integrable fun ξ : ℝ => H (-(2 * Real.pi) * ξ) :=
    hHint'.comp_mul_left' (neg_ne_zero.mpr (by positivity))
  rw [norm_approxL2_sq]
  have hpt : ∀ ξ : ℝ, ‖mellinFactor a (mellinLinePoint ξ) *
      (1 - riemannZeta (mellinLinePoint ξ) *
        chronologicalRowPoly (fun k => -bdRieszCoeff N δ k) N (mellinLinePoint ξ))‖ ^ 2 ≤
      2 * K * H (-(2 * Real.pi) * ξ) +
        2 * ‖Q‖ ^ 2 * ‖mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
    intro ξ
    rw [one_sub_riemannZeta_mul_chronologicalRowPoly_bdRiesz]
    set s := mellinLinePoint ξ with hsdef
    have hs : s = 1 / 2 + ((-(2 * Real.pi) * ξ : ℝ) : ℂ) * I := by
      rw [hsdef, mellinLinePoint_eq]; push_cast; ring
    set u := 1 + riemannZeta s * P s with hu
    set v := riemannZeta s * Q with hv
    have hG := hK (-(2 * Real.pi) * ξ)
    rw [← hs] at hG
    have hHval : H (-(2 * Real.pi) * ξ) = ‖u‖ ^ 2 / (1 / 4 + (-(2 * Real.pi) * ξ) ^ 2) := by
      simp only [hH, hu, hP]
      rw [hs]
    have hden : 0 < 1 / 4 + (-(2 * Real.pi) * ξ) ^ 2 := by positivity
    calc ‖mellinFactor a s * (u - v)‖ ^ 2
        = ‖mellinFactor a s‖ ^ 2 * ‖u - v‖ ^ 2 := by rw [norm_mul, mul_pow]
      _ ≤ ‖mellinFactor a s‖ ^ 2 * (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) := by
          gcongr
          have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le u v) 2
          nlinarith [norm_nonneg u, norm_nonneg v, sq_nonneg (‖u‖ - ‖v‖)]
      _ = 2 * (‖mellinFactor a s‖ ^ 2 * ‖u‖ ^ 2) +
            2 * ‖Q‖ ^ 2 * ‖mellinFactor a s * riemannZeta s‖ ^ 2 := by
          rw [hv, norm_mul, norm_mul, mul_pow, mul_pow]; ring
      _ ≤ 2 * (K / (1 / 4 + (-(2 * Real.pi) * ξ) ^ 2) * ‖u‖ ^ 2) +
            2 * ‖Q‖ ^ 2 * ‖mellinFactor a s * riemannZeta s‖ ^ 2 := by
          gcongr
      _ = 2 * K * H (-(2 * Real.pi) * ξ) +
            2 * ‖Q‖ ^ 2 * ‖mellinFactor a s * riemannZeta s‖ ^ 2 := by
          rw [hHval]; field_simp
  calc (∫ ξ : ℝ, ‖mellinFactor a (mellinLinePoint ξ) *
        (1 - riemannZeta (mellinLinePoint ξ) *
          chronologicalRowPoly (fun k => -bdRieszCoeff N δ k) N (mellinLinePoint ξ))‖ ^ 2)
      ≤ ∫ ξ : ℝ, (2 * K * H (-(2 * Real.pi) * ξ) +
          2 * ‖Q‖ ^ 2 * ‖mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity)
          ((hHcomp.const_mul _).add (hFZ.const_mul _)) (Eventually.of_forall hpt)
    _ = 2 * K * ((2 * Real.pi)⁻¹ * ∫ t : ℝ, H t) +
          2 * ‖Q‖ ^ 2 * ∫ ξ : ℝ,
            ‖mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2 := by
        rw [integral_add (hHcomp.const_mul _) (hFZ.const_mul _), integral_const_mul,
          integral_const_mul, hcov]
    _ = _ := by
        have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
        field_simp

/-- **Converse.**  Under RH, `f_a + Σ c_k D_a(k·)` is arbitrarily small for suitable rows. -/
theorem exists_norm_approxL2_lt_of_riemannHypothesis (ha0 : 0 < a) (hRH : RiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, ∃ c : ℕ → ℝ, ‖approxL2 ha0 c N‖ < ε := by
  obtain ⟨K, hK⟩ := exists_norm_sq_mellinFactor_half_le ha0
  obtain ⟨B₂, hB₂0, hB⟩ := exists_norm_sq_bdTarget_sub_bdRiesz_le_of_rh hRH
  set M := ∫ ξ : ℝ, ‖mellinFactor a (mellinLinePoint ξ) * riemannZeta (mellinLinePoint ξ)‖ ^ 2
    with hMdef
  have hK0 : 0 ≤ K := by
    have := (sq_nonneg ‖mellinFactor a (1 / 2 + ((0 : ℝ) : ℂ) * I)‖).trans (hK 0)
    have hpos : (0 : ℝ) < 1 / 4 + 0 ^ 2 := by norm_num
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hpos))
  set L : ℝ := K / Real.pi with hL
  have hL0 : 0 ≤ L := by positivity
  have hRlim : Tendsto (fun δ : ℝ => L * (3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2)) +
      2 * ‖invZetaCont (1 + δ)‖ ^ 2 * M) (𝓝[>] 0) (𝓝 0) := by
    have hF : Tendsto zetaShiftDefect (𝓝[>] 0) (𝓝 0) :=
      tendsto_integral_one_sub_riemannZeta_ratio_of_rh hRH
    have hI := (tendsto_invZetaCont_one_add_of_rh hRH).norm.pow 2
    have := (((hF.add (hI.const_mul B₂)).const_mul 3).const_mul L).add ((hI.const_mul 2).mul_const M)
    simpa using this
  obtain ⟨δ, hδR, hδ0, hδ1⟩ :=
    ((hRlim.eventually (gt_mem_nhds (pow_pos hε 2))).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num))).exists
  obtain ⟨B₁, hB₁⟩ := hB δ hδ0 hδ1.le
  have hG : Tendsto (fun N : ℕ => L * (3 * (zetaShiftDefect δ + B₁ * perronLength N ^ (-δ) +
      B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2)) + 2 * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2 * M) atTop
      (𝓝 (L * (3 * (zetaShiftDefect δ + B₂ * ‖invZetaCont (1 + δ)‖ ^ 2)) +
        2 * ‖invZetaCont (1 + δ)‖ ^ 2 * M)) := by
    have h1 := (tendsto_perronLength_rpow_neg hδ0).const_mul B₁
    have h2 := (tendsto_moebiusRieszPoly_one_add_of_rh hRH hδ0 (by linarith)).norm.pow 2
    have := (((((tendsto_const_nhds (x := zetaShiftDefect δ)).add h1).add
      (h2.const_mul B₂)).const_mul 3).const_mul L).add ((h2.const_mul 2).mul_const M)
    simpa using this
  obtain ⟨N, hN⟩ := (hG.eventually (gt_mem_nhds hδR)).exists
  refine ⟨N, fun k => -bdRieszCoeff N δ k, ?_⟩
  have hS : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  obtain ⟨-, heq⟩ := integrable_and_norm_sq_bdTarget_sub_sum_bdGen hS (bdRieszCoeff N δ)
  have hle := norm_approxL2_bdRiesz_sq_le ha0 hK N δ
  have hd := hB₁ N
  rw [heq] at hd
  have hπ : 0 < 2 * Real.pi := by positivity
  have hint_le : (∫ t : ℝ, ‖1 + riemannZeta (1 / 2 + t * I) *
      bdMollPoly (Finset.Icc 1 N) (bdRieszCoeff N δ) (1 / 2 + t * I)‖ ^ 2 / (1 / 4 + t ^ 2)) ≤
      3 * (zetaShiftDefect δ + B₁ * perronLength N ^ (-δ) +
        B₂ * ‖moebiusRieszPoly N (1 + δ)‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hd hπ.le
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul, one_mul] at this
    exact this
  have hKπ : 0 ≤ K / Real.pi := by positivity
  have hsq : ‖approxL2 ha0 (fun k => -bdRieszCoeff N δ k) N‖ ^ 2 < ε ^ 2 := by
    rw [← hMdef] at hle
    have h1 := mul_le_mul_of_nonneg_left hint_le hKπ
    linarith
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).mp hsq

/-- Under RH, `f_a` lies in the closed span of the integer dilates of `D_a` (every `a > 0`). -/
theorem kernelL2_mem_closure_of_riemannHypothesis (ha0 : 0 < a) (hRH : RiemannHypothesis) :
    kernelL2 ha0 ∈ (Submodule.span ℂ (Set.range (defectDilateL2 ha0))).topologicalClosure := by
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, c, hlt⟩ := exists_norm_approxL2_lt_of_riemannHypothesis ha0 hRH hε
  refine ⟨-∑ k ∈ Finset.Ioc 0 N, ((c k : ℝ) : ℂ) • defectDilateL2 ha0 (k - 1), ?_, ?_⟩
  · refine Submodule.neg_mem _ (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_)
    exact Submodule.subset_span ⟨k - 1, rfl⟩
  · rw [dist_eq_norm, sub_neg_eq_add]
    exact hlt

/-- **RH as a completeness problem.**  For every `a > 1`, RH holds iff `e^{-t^a}` lies in the closed
linear span of the integer dilates `D_a(k·)` of the stretched Bose defect. -/
theorem riemannHypothesis_iff_kernelL2_mem_closure (ha : 1 < a) :
    RiemannHypothesis ↔ kernelL2 (a := a) (by linarith) ∈
      (Submodule.span ℂ (Set.range (defectDilateL2 (a := a) (by linarith)))).topologicalClosure :=
  ⟨kernelL2_mem_closure_of_riemannHypothesis (by linarith), riemannHypothesis_of_kernelL2_mem_closure ha⟩

end RHTower.StretchedBose
