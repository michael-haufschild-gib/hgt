import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gauss multiplication for the Gamma function (up to constant)

The signed archimedean Gamma orbit-charge card reduces a scaled factor `Γ(λ s + μ)` to common-scale
factors `Γ((s + a)/H)` via Gauss multiplication `(6)`.  mathlib has only the `n = 2` doubling case;
the general finite-`n` formula is a stated mathlib TODO.  This file proves the general real formula
*up to its multiplicative constant* — which is all the orbit-charge reduction uses — by the
Bohr–Mollerup characterization: the product `∏_{k<n} Γ((s+k)/n) · n^s`, normalized to value `1` at
`s = 1`, satisfies the Gamma functional equation and log-convexity, hence equals `Γ`.
-/

open Real Finset
open scoped BigOperators

namespace GaloisForLFunctions

/-- The Gauss-multiplication product `∏_{k<n} Γ((s+k)/n) · n^s`.  Its normalization to value `1` at
`s = 1` is shown below to equal `Γ`. -/
noncomputable def multGammaProd (n : ℕ) (s : ℝ) : ℝ :=
  (∏ k ∈ Finset.range n, Real.Gamma ((s + k) / n)) * (n : ℝ) ^ s

/-- Each common-scale argument `(s+k)/n` is positive when `s > 0`. -/
theorem arg_pos {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 < (s + k) / n := by
  apply div_pos
  · positivity
  · exact_mod_cast hn

/-- Positivity of the Gauss product on `s > 0`. -/
theorem multGammaProd_pos {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) : 0 < multGammaProd n s := by
  apply mul_pos
  · apply Finset.prod_pos
    intro k _
    exact Real.Gamma_pos_of_pos (arg_pos hn hs k)
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hn) s

/-- **Functional equation of the Gauss product:** `P(s+1) = s · P(s)` for `s > 0`.  The product
telescopes (`Finset.prod_range_succ`/`prod_range_succ'` peel the endpoints `Γ(s/n)` and
`Γ(s/n + 1) = (s/n)Γ(s/n)`), and the extra `n` from `n^{s+1}` cancels the `1/n`. -/
theorem multGammaProd_functional {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    multGammaProd n (s + 1) = s * multGammaProd n s := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set F : ℕ → ℝ := fun j => Real.Gamma ((s + j) / n) with hF
  -- telescoping: (∏_{k<n} F(k+1)) * F 0 = (∏_{k<n} F k) * F n
  have htel : (∏ k ∈ Finset.range n, F (k + 1)) * F 0
      = (∏ k ∈ Finset.range n, F k) * F n := by
    rw [← Finset.prod_range_succ, ← Finset.prod_range_succ' F n]
  have hF0 : 0 < F 0 := Real.Gamma_pos_of_pos (by simpa using arg_pos hn hs 0)
  -- F n = (s/n) * F 0
  have hFn : F n = (s / n) * F 0 := by
    have : (s + (n : ℝ)) / n = s / n + 1 := by field_simp
    simp only [hF, Nat.cast_zero, add_zero]
    rw [this, Real.Gamma_add_one (by positivity)]
  -- so ∏ F(k+1) = (s/n) * ∏ F k
  have hprod : (∏ k ∈ Finset.range n, F (k + 1)) = (s / n) * (∏ k ∈ Finset.range n, F k) := by
    have h2 : (∏ k ∈ Finset.range n, F (k + 1)) * F 0
        = ((s / n) * (∏ k ∈ Finset.range n, F k)) * F 0 := by
      rw [htel, hFn]; ring
    exact mul_right_cancel₀ (ne_of_gt hF0) h2
  -- reindex the (s+1) product to F(k+1)
  have hreindex : (∏ k ∈ Finset.range n, Real.Gamma ((s + 1 + k) / n))
      = (∏ k ∈ Finset.range n, F (k + 1)) := by
    apply Finset.prod_congr rfl
    intro k _
    simp only [hF]
    congr 1
    push_cast
    ring
  rw [multGammaProd, multGammaProd, hreindex, hprod,
    Real.rpow_add hnR, Real.rpow_one]
  simp only [hF]
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp

/-- Value at `1`: `P(1) = (∏_{k<n} Γ((1+k)/n)) · n`. -/
theorem multGammaProd_one (n : ℕ) :
    multGammaProd n 1 = (∏ k ∈ Finset.range n, Real.Gamma ((1 + k) / n)) * (n : ℝ) := by
  rw [multGammaProd, Real.rpow_one]

/-- Each shifted-scaled log-Gamma summand `s ↦ log Γ((s+k)/n)` is convex on `s > 0`, by composing
`convexOn_log_Gamma` with the affine map `s ↦ n⁻¹ s + k/n`. -/
theorem logGamma_shiftScale_convexOn {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun s => Real.log (Real.Gamma ((s + k) / n))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hcomp := convexOn_log_Gamma.comp_affineMap
    ((DistribSMul.toLinearMap ℝ ℝ ((n : ℝ)⁻¹)).toAffineMap + AffineMap.const ℝ ℝ ((k : ℝ) / n))
  refine (hcomp.subset ?_ (convex_Ioi _)).congr ?_
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    show (0 : ℝ) < (n : ℝ)⁻¹ • x + (k : ℝ) / n
    rw [smul_eq_mul]
    positivity
  · intro x _
    show Real.log (Real.Gamma ((n : ℝ)⁻¹ • x + (k : ℝ) / n)) = Real.log (Real.Gamma ((x + k) / n))
    rw [smul_eq_mul, show (n : ℝ)⁻¹ * x + (k : ℝ) / n = (x + k) / n by field_simp]

/-- The Gauss product is log-convex on `s > 0`. -/
theorem multGammaProd_log_convexOn {n : ℕ} (hn : 0 < n) :
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (Real.log ∘ multGammaProd n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h1n : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- log P(s) = ∑ log Γ((s+k)/n) + s·log n on Ioi 0
  have hEq : Set.EqOn (Real.log ∘ multGammaProd n)
      (fun s => (∑ k ∈ Finset.range n, Real.log (Real.Gamma ((s + k) / n))) + s * Real.log n)
      (Set.Ioi 0) := by
    intro s hs
    have hprodpos : (0 : ℝ) < ∏ k ∈ Finset.range n, Real.Gamma ((s + k) / n) :=
      Finset.prod_pos fun k _ => Real.Gamma_pos_of_pos (arg_pos hn hs k)
    have hnpow : (0 : ℝ) < (n : ℝ) ^ s := Real.rpow_pos_of_pos hnR s
    rw [Function.comp_apply, multGammaProd, Real.log_mul (ne_of_gt hprodpos) (ne_of_gt hnpow),
      Real.log_prod (fun k _ => (Real.Gamma_pos_of_pos (arg_pos hn hs k)).ne'), Real.log_rpow hnR]
  -- convexity of the sum by induction, plus the linear term
  have hsum : ConvexOn ℝ (Set.Ioi (0 : ℝ))
      (fun s => ∑ k ∈ Finset.range n, Real.log (Real.Gamma ((s + k) / n))) := by
    induction Finset.range n using Finset.induction with
    | empty => simpa using convexOn_const (0 : ℝ) (convex_Ioi 0)
    | insert a t ha ih =>
        simp only [Finset.sum_insert ha]
        exact (logGamma_shiftScale_convexOn hn a).add ih
  have hlin : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun s => s * Real.log n) := by
    have hsmul :=
      (convexOn_id (convex_Ioi (0 : ℝ))).smul (Real.log_nonneg h1n)
    have hfun : (fun s : ℝ => Real.log n • id s) =
        (fun s : ℝ => s * Real.log n) := by
      apply _root_.funext
      intro s
      simp only [id_eq, smul_eq_mul, mul_comm]
    rw [← hfun]
    exact hsmul
  exact (hsum.add hlin).congr hEq.symm

/-- **Gauss multiplication (up to constant), real positive form.**  For `n ≥ 1` and `s > 0`,
`∏_{k<n} Γ((s+k)/n) · n^s = C_n · Γ(s)` with `C_n = P(1) = (∏_{k<n} Γ((1+k)/n))·n`.  Proof: the
normalized product is log-convex, satisfies the Gamma functional equation, is positive and `= 1` at
`s = 1`, so by Bohr–Mollerup it equals `Γ`. -/
theorem multGammaProd_eq {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    multGammaProd n s = multGammaProd n 1 * Real.Gamma s := by
  have hP1 : 0 < multGammaProd n 1 := multGammaProd_pos hn one_pos
  set C := multGammaProd n 1 with hC
  -- normalized `s ↦ P s / C` matches Γ by Bohr–Mollerup
  have hnorm : Set.EqOn (fun s => multGammaProd n s / C) Real.Gamma (Set.Ioi 0) := by
    refine eq_Gamma_of_log_convex ?_ (fun {y} hy => ?_) (fun {y} hy => ?_) ?_
    · -- log-convexity of the normalized product
      have hconv := multGammaProd_log_convexOn hn
      have hEq : Set.EqOn (Real.log ∘ fun s => multGammaProd n s / C)
          (fun s => (Real.log ∘ multGammaProd n) s + (-Real.log C)) (Set.Ioi 0) := by
        intro x hx
        simp only [Function.comp_apply]
        rw [Real.log_div (ne_of_gt (multGammaProd_pos hn hx)) (ne_of_gt hP1), sub_eq_add_neg]
      exact (hconv.add_const (-Real.log C)).congr hEq.symm
    · rw [multGammaProd_functional hn hy, mul_div_assoc]
    · exact div_pos (multGammaProd_pos hn hy) hP1
    · rw [div_self (ne_of_gt hP1)]
  have hval := hnorm hs
  have hCne : C ≠ 0 := ne_of_gt hP1
  simp only [] at hval
  rw [← hval]
  field_simp

/-- **Gauss multiplication in standard form (up to constant).**  For `n ≥ 1` and `s > 0`,
`∏_{k<n} Γ((s+k)/n) = C_n · n^{-s} · Γ(s)`, exhibiting a scaled Gamma factor as a nonzero constant
times a real exponential `n^{-s}` times common-scale Gamma factors — the §2 orbit normal-form step. -/
theorem gauss_multiplication {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    (∏ k ∈ Finset.range n, Real.Gamma ((s + k) / n))
      = multGammaProd n 1 * (n : ℝ) ^ (-s) * Real.Gamma s := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := multGammaProd_eq hn hs
  rw [multGammaProd] at h
  rw [Real.rpow_neg (le_of_lt hnR)]
  have hns : (n : ℝ) ^ s ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnR s)
  field_simp
  linear_combination h

open Complex in
/-- **Gauss multiplication, complex meromorphic form (reciprocal, up to constant).**  The
reciprocal-Gamma product `∏_{k<n} Γ((s+k)/n)⁻¹` (entire) equals `C_n⁻¹ · n^s · Γ(s)⁻¹` for every
complex `s`, by analytic continuation from the real positive case.  This is the §2 orbit normal form
in the meromorphic category the card uses. -/
theorem gauss_multiplication_complex {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (∏ k ∈ Finset.range n, (Complex.Gamma ((s + k) / n))⁻¹)
      = (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ s * (Complex.Gamma s)⁻¹ := by
  have hnne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hFdiff : Differentiable ℂ
      (fun s : ℂ => ∏ k ∈ Finset.range n, (Complex.Gamma ((s + k) / n))⁻¹) := by
    have heq : (fun s : ℂ => ∏ k ∈ Finset.range n, (Complex.Gamma ((s + k) / n))⁻¹)
        = ∏ k ∈ Finset.range n, (fun s : ℂ => (Complex.Gamma ((s + k) / n))⁻¹) := by
      funext s; simp [Finset.prod_apply]
    rw [heq]
    exact Differentiable.finsetProd fun k _ =>
      Complex.differentiable_one_div_Gamma.comp
        ((differentiable_id.add (differentiable_const _)).div_const _)
  have hGdiff : Differentiable ℂ
      (fun s : ℂ => (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ s * (Complex.Gamma s)⁻¹) :=
    ((differentiable_const _).mul
      (fun x => differentiableAt_id.const_cpow (Or.inl hnne))).mul Complex.differentiable_one_div_Gamma
  have hF := analyticOnNhd_univ_iff_differentiable.mpr hFdiff
  have hG := analyticOnNhd_univ_iff_differentiable.mpr hGdiff
  have h3 : Filter.Tendsto ((↑) : ℝ → ℂ) (nhdsWithin 1 {1}ᶜ) (nhdsWithin 1 {1}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds continuous_ofReal.continuousAt, ?_⟩
    exact eventually_nhdsWithin_iff.mpr (Filter.Eventually.of_forall fun t ht => by
      simpa using Complex.ofReal_ne_one.mpr ht)
  have hkey : (fun s : ℂ => ∏ k ∈ Finset.range n, (Complex.Gamma ((s + k) / n))⁻¹)
      = fun s : ℂ => (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ s * (Complex.Gamma s)⁻¹ := by
    refine AnalyticOnNhd.eq_of_frequently_eq hF hG (h3.frequently ?_)
    refine ((Filter.Eventually.filter_mono nhdsWithin_le_nhds) ?_).frequently
    refine (eventually_gt_nhds zero_lt_one).mp (Filter.Eventually.of_forall fun t ht => ?_)
    -- real positive agreement
    have hreal := gauss_multiplication hn ht
    have hprodR : (∏ k ∈ Finset.range n, (Real.Gamma ((t + k) / n))⁻¹)
        = (multGammaProd n 1)⁻¹ * (n : ℝ) ^ t * (Real.Gamma t)⁻¹ := by
      rw [Finset.prod_inv_distrib, hreal, Real.rpow_neg (le_of_lt hnR)]
      field_simp
    have hcastarg : ∀ k : ℕ, ((t : ℂ) + (k : ℂ)) / (n : ℂ) = (((t + k) / n : ℝ) : ℂ) := by
      intro k; push_cast; ring
    have hLHS : (∏ k ∈ Finset.range n, (Complex.Gamma (((t : ℂ) + (k : ℂ)) / (n : ℂ)))⁻¹)
        = ((∏ k ∈ Finset.range n, (Real.Gamma ((t + k) / n))⁻¹ : ℝ) : ℂ) := by
      rw [Complex.ofReal_prod]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [hcastarg k, Complex.Gamma_ofReal, Complex.ofReal_inv]
    have hRHS : (multGammaProd n 1 : ℂ)⁻¹ * (n : ℂ) ^ (t : ℂ) * (Complex.Gamma (t : ℂ))⁻¹
        = (((multGammaProd n 1)⁻¹ * (n : ℝ) ^ t * (Real.Gamma t)⁻¹ : ℝ) : ℂ) := by
      rw [Complex.Gamma_ofReal]
      push_cast [Complex.ofReal_cpow (le_of_lt hnR)]
      ring
    rw [hLHS, hRHS]
    exact_mod_cast hprodR
  exact congrFun hkey s

end GaloisForLFunctions
