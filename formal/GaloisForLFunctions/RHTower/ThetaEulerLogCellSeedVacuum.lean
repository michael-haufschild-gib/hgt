import GaloisForLFunctions.RHTower.QuasiPolynomialBlaschkeIsometry
import GaloisForLFunctions.RHTower.ThetaEulerLogCellResidueChannels
import GaloisForLFunctions.RHTower.ThetaSeedHalfLineDivision
import GaloisForLFunctions.RHTower.ThetaZeroDivisionRateDerivativeWitness
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeFluxWindow
import GaloisForLFunctions.HTGeometry.SechSquareConvolutionKernel

/-!
# The literal theta seed keeps the Euler vacuum visible

The literal atoms `C e_n = n^{-1/2} h(· + log n)` of the completed theta source, with
`h(x) = 2π e^{5x/2}(2π e^{2x} − 3) e^{−π e^{2x}}`, are, in `u = e^{2x}`,
`2π n² u^{5/4}(2λ_n u − 3) e^{−λ_n u}`, `λ_n = π n²`.  On the positive half-line:

* `C : ℓ²(ℕ₊) → L²(0,∞)` is Hilbert–Schmidt and intertwines Euler multiplication with the literal
  source shift: `C S_p = p^{-1/2} L_{log p} C`, `(L_a f)(x) = f(x + a)`.
* **Vacuum separation.**  `C e_1` lies outside the closed span of `{C e_n : n ≥ 2}`, so some
  `g ∈ L²(0,∞)` has `⟪g, C e_n⟫ = 0` for `n ≥ 2` and `⟪g, C e_1⟫ ≠ 0`.  The Euler source
  `k = Σ_n C e_n` converges absolutely in `L²(0,∞)` and `⟪g, k⟫ = ⟪g, h⟫ ≠ 0`.

The separation uses separators `g_k(x) = conj(r_k(e^{2x} − 1)) e^{−x/2}`, for which
`⟪g_k, C e_n⟫ = π n² e^{−λ_n}((2λ_n − 3) ℒr_k(λ_n) + 2λ_n ℒ(v r_k)(λ_n))`.  The quasi-polynomials
`r_k = B_{λ_{k+1}}² ⋯ B_{λ_2}² r₀`, `ℒr₀(q) = (q − λ₁)/(q + 1)²`, carry finite Blaschke products:
they have the energy of `r₀` (Blaschke steps are `L²` isometries), their Laplace transforms have
double zeros at `λ_2, …, λ_{k+1}` and a simple zero at `λ₁` with derivative
`∏_j b_j(λ₁)²/(λ₁+1)² ≥ e^{−8}/(λ₁+1)²`.  Uniformly bounded separators with a uniform gap at `C e_1`
that eventually annihilate every finite combination of higher atoms exclude `C e_1` from their
closure.

On the whole line the synthesis `e_n ↦ n^{-1/2} h(· + log n)` is bounded: `|h(y)| ≤ K e^{−5|y|/2}`
gives the Gram bound `|⟪a_n, a_m⟫| ≤ 4K² (nm)^{-1/2} e^{−2|log n − log m|}`, and the Schur sums
`Σ_m (nm)^{-1/2} e^{−2|log n − log m|} ≤ 3` bound the Gram form.  The separator extended by zero
separates the same full-line atoms.
-/

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry (QuasiPolynomial halfLineMeasure halfLineExtend halfLineRestrict
  halfLineExtend_coeFn halfLineRestrict_coeFn indicator_ae_eq_of_halfLine)

namespace RHTower

noncomputable section

/-! ## The separator quasi-polynomials -/

/-- The Gaussian rates `λ_n = π n²` of the theta atoms. -/
def gaussRate (n : ℕ) : ℝ := Real.pi * n ^ 2

theorem gaussRate_pos {n : ℕ} (hn : 0 < n) : 0 < gaussRate n := by
  unfold gaussRate; have : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- The Blaschke factor `(λ − t)/(λ + t)`. -/
def rateBlaschkeFactor (lam t : ℝ) : ℝ := (lam - t) / (lam + t)

/-- `r₀(v) = (1 − (λ₁ + 1) v) e^{−v}`, with `ℒr₀(q) = (q − λ₁)/(q + 1)²`. -/
def seedSeparatorBase : QuasiPolynomial :=
  Finsupp.single (-1) (Polynomial.C 1 - Polynomial.C (((gaussRate 1 + 1 : ℝ)) : ℂ) * Polynomial.X)

/-- `r_k = B_{λ_{k+1}}² ⋯ B_{λ_2}² r₀`. -/
def seedSeparator : ℕ → QuasiPolynomial
  | 0 => seedSeparatorBase
  | k + 1 => blaschkeStep (gaussRate (k + 2)) (blaschkeStep (gaussRate (k + 2)) (seedSeparator k))

theorem isDecaying_seedSeparatorBase : IsDecayingQP seedSeparatorBase := fun μ hμ => by
  have := Finsupp.support_single_subset hμ
  rw [Finset.mem_singleton] at this
  rw [this]; norm_num

theorem isDecaying_seedSeparator (k : ℕ) : IsDecayingQP (seedSeparator k) := by
  induction k with
  | zero => exact isDecaying_seedSeparatorBase
  | succ k ih =>
    exact (ih.blaschkeStep (gaussRate_pos (by omega))).blaschkeStep (gaussRate_pos (by omega))

/-- All separators have the energy of `r₀`. -/
theorem integral_norm_sq_seedSeparator (k : ℕ) :
    ∫ s in Ioi (0 : ℝ), ‖(seedSeparator k).eval s‖ ^ 2 =
      ∫ s in Ioi (0 : ℝ), ‖seedSeparatorBase.eval s‖ ^ 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [seedSeparator, integral_norm_sq_blaschkeStep
      ((isDecaying_seedSeparator k).blaschkeStep (gaussRate_pos (by omega)))
      (gaussRate_pos (by omega)), integral_norm_sq_blaschkeStep (isDecaying_seedSeparator k)
      (gaussRate_pos (by omega)), ih]

theorem laplace_seedSeparatorBase {t : ℝ} (ht : 0 < t) :
    seedSeparatorBase.laplace t = (((t - gaussRate 1) / (t + 1) ^ 2 : ℝ) : ℂ) := by
  have hdeg : (Polynomial.C (1 : ℂ) - Polynomial.C (((gaussRate 1 + 1 : ℝ)) : ℂ) * Polynomial.X).natDegree < 2 := by
    have := Polynomial.natDegree_sub_le (Polynomial.C (1 : ℂ))
      (Polynomial.C (((gaussRate 1 + 1 : ℝ)) : ℂ) * Polynomial.X)
    have h2 := (Polynomial.natDegree_C_mul_le (((gaussRate 1 + 1 : ℝ)) : ℂ) Polynomial.X).trans
      Polynomial.natDegree_X_le
    rw [Polynomial.natDegree_C] at this
    omega
  rw [seedSeparatorBase, QuasiPolynomial.laplace_single, QuasiPolynomial.laplaceTerm_eq_range _ hdeg]
  have ht1 : (t : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : t + 1 ≠ 0)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_zero, Polynomial.coeff_X_one,
    Polynomial.coeff_C, Nat.factorial, sub_neg_eq_add]
  push_cast
  field_simp
  ring

theorem laplace_seedSeparator_succ (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (seedSeparator (k + 1)).laplace t =
      ((rateBlaschkeFactor (gaussRate (k + 2)) t ^ 2 : ℝ) : ℂ) * (seedSeparator k).laplace t := by
  have hlam := gaussRate_pos (show 0 < k + 2 by omega)
  have htq : 0 < ((t : ℂ)).re := by simpa using ht
  rw [seedSeparator, laplace_blaschkeStep ((isDecaying_seedSeparator k).blaschkeStep hlam) hlam htq,
    laplace_blaschkeStep (isDecaying_seedSeparator k) hlam htq, rateBlaschkeFactor]
  push_cast
  ring

/-- The derivative `−ℒ(s r_k)` of the Laplace transform of `r_k`. -/
def seedDeriv (k : ℕ) (t : ℝ) : ℂ := -(qpMulX (seedSeparator k)).laplace t

theorem hasDerivAt_laplace_seedSeparator (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => (seedSeparator k).laplace s) (seedDeriv k t) t := by
  have hnot : (t : ℂ) ∉ (seedSeparator k).support := fun h => by
    have := isDecaying_seedSeparator k _ h
    simp at this; linarith
  exact (hasDerivAt_laplace _ hnot).comp_ofReal

theorem hasDerivAt_rateBlaschkeFactor (lam t : ℝ) (h : lam + t ≠ 0) :
    HasDerivAt (fun s => rateBlaschkeFactor lam s) (-(2 * lam) / (lam + t) ^ 2) t := by
  unfold rateBlaschkeFactor
  have := ((hasDerivAt_id t).const_sub lam).div ((hasDerivAt_id t).const_add lam) h
  refine this.congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- **Derivative recursion.**  `D_{k+1} = 2 b b' L_k + b² D_k`. -/
theorem seedDeriv_succ (k : ℕ) {t : ℝ} (ht : 0 < t) :
    seedDeriv (k + 1) t =
      ((2 * rateBlaschkeFactor (gaussRate (k + 2)) t *
        (-(2 * gaussRate (k + 2)) / (gaussRate (k + 2) + t) ^ 2) : ℝ) : ℂ) *
          (seedSeparator k).laplace t +
        ((rateBlaschkeFactor (gaussRate (k + 2)) t ^ 2 : ℝ) : ℂ) * seedDeriv k t := by
  have hlam := gaussRate_pos (show 0 < k + 2 by omega)
  have hb := hasDerivAt_rateBlaschkeFactor (gaussRate (k + 2)) t (by linarith)
  have hb2 : HasDerivAt (fun s => ((rateBlaschkeFactor (gaussRate (k + 2)) s ^ 2 : ℝ) : ℂ))
      (((2 * rateBlaschkeFactor (gaussRate (k + 2)) t *
        (-(2 * gaussRate (k + 2)) / (gaussRate (k + 2) + t) ^ 2) : ℝ) : ℂ)) t := by
    have := (hb.pow 2).ofReal_comp
    refine this.congr_deriv ?_
    push_cast
    ring
  have hprod := hb2.mul (hasDerivAt_laplace_seedSeparator k ht)
  have heq : (fun s : ℝ => (seedSeparator (k + 1)).laplace s) =ᶠ[𝓝 t]
      fun s => ((rateBlaschkeFactor (gaussRate (k + 2)) s ^ 2 : ℝ) : ℂ) * (seedSeparator k).laplace s := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact laplace_seedSeparator_succ k hs
  exact (hasDerivAt_laplace_seedSeparator (k + 1) ht).unique (hprod.congr_of_eventuallyEq heq)

theorem seedDeriv_zero_gaussRate_one :
    seedDeriv 0 (gaussRate 1) = ((1 / (gaussRate 1 + 1) ^ 2 : ℝ) : ℂ) := by
  have h1 := gaussRate_pos (show 0 < 1 by omega)
  have hL : HasDerivAt (fun s : ℝ => ((((s - gaussRate 1) / (s + 1) ^ 2 : ℝ)) : ℂ))
      ((1 / (gaussRate 1 + 1) ^ 2 : ℝ) : ℂ) (gaussRate 1) := by
    have hne : (gaussRate 1 + 1) ^ 2 ≠ 0 := by positivity
    have := (((hasDerivAt_id (gaussRate 1)).sub_const (gaussRate 1)).div
      (((hasDerivAt_id (gaussRate 1)).add_const 1).pow 2) hne).ofReal_comp
    refine this.congr_deriv ?_
    simp only [id, Pi.pow_apply, sub_self, zero_mul, sub_zero, one_mul]
    push_cast
    field_simp
  have heq : (fun s : ℝ => (seedSeparator 0).laplace s) =ᶠ[𝓝 (gaussRate 1)]
      fun s => ((((s - gaussRate 1) / (s + 1) ^ 2 : ℝ)) : ℂ) := by
    filter_upwards [Ioi_mem_nhds h1] with s hs
    exact laplace_seedSeparatorBase hs
  exact (hasDerivAt_laplace_seedSeparator 0 h1).unique (hL.congr_of_eventuallyEq heq)

/-- **Zeros of the separators.**  `ℒr_k` has a double zero at `λ_n`, `2 ≤ n ≤ k+1`, a simple zero at
`λ₁`, and `(ℒr_k)'(λ₁) = ∏_{j=2}^{k+1} b_j(λ₁)² / (λ₁+1)²`. -/
theorem seedSeparator_zeros (k : ℕ) :
    (∀ n, 2 ≤ n → n ≤ k + 1 →
      (seedSeparator k).laplace (gaussRate n) = 0 ∧ seedDeriv k (gaussRate n) = 0) ∧
    (seedSeparator k).laplace (gaussRate 1) = 0 ∧
    seedDeriv k (gaussRate 1) =
      (((∏ j ∈ Finset.range k, rateBlaschkeFactor (gaussRate (j + 2)) (gaussRate 1) ^ 2) /
        (gaussRate 1 + 1) ^ 2 : ℝ) : ℂ) := by
  have h1 := gaussRate_pos (show 0 < 1 by omega)
  induction k with
  | zero =>
    refine ⟨fun n h2 h3 => by omega, ?_, ?_⟩
    · rw [seedSeparator, laplace_seedSeparatorBase h1]; simp
    · rw [seedDeriv_zero_gaussRate_one]; simp
  | succ k ih =>
    obtain ⟨ihn, ih1, ihd⟩ := ih
    refine ⟨fun n h2 h3 => ?_, ?_, ?_⟩
    · have hn := gaussRate_pos (show 0 < n by omega)
      rw [laplace_seedSeparator_succ k hn, seedDeriv_succ k hn]
      rcases Nat.lt_or_ge n (k + 2) with hlt | hge
      · obtain ⟨hL, hD⟩ := ihn n h2 (by omega)
        rw [hL, hD]; simp
      · have hnk : n = k + 2 := by omega
        subst hnk
        simp [rateBlaschkeFactor]
    · rw [laplace_seedSeparator_succ k h1, ih1, mul_zero]
    · rw [seedDeriv_succ k h1, ih1, ihd, Finset.prod_range_succ]
      push_cast
      ring

/-! ## A uniform lower bound for the Blaschke product at `λ₁` -/

theorem blaschkeFactor_gaussRate_one {n : ℕ} :
    rateBlaschkeFactor (gaussRate n) (gaussRate 1) = ((n : ℝ) ^ 2 - 1) / ((n : ℝ) ^ 2 + 1) := by
  unfold rateBlaschkeFactor gaussRate
  have hπ := Real.pi_pos
  push_cast
  rw [show Real.pi * (n : ℝ) ^ 2 - Real.pi * 1 ^ 2 = Real.pi * ((n : ℝ) ^ 2 - 1) by ring,
    show Real.pi * (n : ℝ) ^ 2 + Real.pi * 1 ^ 2 = Real.pi * ((n : ℝ) ^ 2 + 1) by ring,
    mul_div_mul_left _ _ hπ.ne']

theorem exp_neg_two_mul_le_one_sub_of_le_half {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    Real.exp (-(2 * y)) ≤ 1 - y := by
  have h1 : 0 < 1 - y := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos h1
  have h2 : -(2 * y) ≤ 1 - (1 - y)⁻¹ := by
    rw [show 1 - (1 - y)⁻¹ = -(y / (1 - y)) by field_simp; ring, neg_le_neg_iff,
      div_le_iff₀ h1]
    nlinarith
  calc Real.exp (-(2 * y)) ≤ Real.exp (Real.log (1 - y)) := Real.exp_le_exp.2 (h2.trans hlog)
    _ = 1 - y := Real.exp_log h1

theorem exp_le_rateBlaschkeFactor_sq {j : ℕ} (hj : 2 ≤ j) :
    Real.exp (-(8 / (((j : ℝ) - 1) * j))) ≤ rateBlaschkeFactor (gaussRate j) (gaussRate 1) ^ 2 := by
  have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : (0 : ℝ) < (j : ℝ) ^ 2 + 1 := by positivity
  set y : ℝ := 2 / ((j : ℝ) ^ 2 + 1)
  have hy0 : 0 ≤ y := by positivity
  have hy : y ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]; nlinarith
  have hb : rateBlaschkeFactor (gaussRate j) (gaussRate 1) = 1 - y := by
    rw [blaschkeFactor_gaussRate_one]; simp only [y]; field_simp; ring
  rw [hb]
  have h1 := exp_neg_two_mul_le_one_sub_of_le_half hy0 hy
  have h2 : Real.exp (-(8 / (((j : ℝ) - 1) * j))) ≤ Real.exp (-(2 * y)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    have hden : 0 < ((j : ℝ) - 1) * j := by nlinarith
    simp only [y]
    rw [neg_le, show -((2 : ℕ) * -(2 * (2 / ((j : ℝ) ^ 2 + 1)))) = 8 / ((j : ℝ) ^ 2 + 1) by
      push_cast; ring]
    exact div_le_div_of_nonneg_left (by norm_num) hden (by nlinarith)
  exact h2.trans (pow_le_pow_left₀ (Real.exp_pos _).le h1 2)

/-- `∏_{j=2}^{k+1} b_j(λ₁)² ≥ e^{−8 + 8/(k+1)} ≥ e^{−8}`. -/
theorem exp_le_prod_rateBlaschkeFactor_sq (k : ℕ) :
    Real.exp (-8 + 8 / (k + 1)) ≤
      ∏ j ∈ Finset.range k, rateBlaschkeFactor (gaussRate (j + 2)) (gaussRate 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ]
    have hstep := exp_le_rateBlaschkeFactor_sq (show 2 ≤ k + 2 by omega)
    have hk : (0 : ℝ) < k + 1 := by positivity
    calc Real.exp (-8 + 8 / (((k + 1 : ℕ) : ℝ) + 1))
        = Real.exp (-8 + 8 / (k + 1)) * Real.exp (-(8 / ((((k + 2 : ℕ) : ℝ) - 1) * ((k + 2 : ℕ) : ℝ)))) := by
          rw [← Real.exp_add]
          congr 1
          rw [show ((k + 2 : ℕ) : ℝ) - 1 = (k : ℝ) + 1 by push_cast; ring,
            show ((k + 2 : ℕ) : ℝ) = (k : ℝ) + 2 by push_cast; ring,
            show ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 by push_cast; ring]
          have h2 : (0 : ℝ) < k + 2 := by positivity
          field_simp
          ring
      _ ≤ _ := mul_le_mul ih hstep (Real.exp_pos _).le
          (Finset.prod_nonneg fun _ _ => sq_nonneg _)

theorem exp_neg_eight_le_prod_rateBlaschkeFactor_sq (k : ℕ) :
    Real.exp (-8) ≤ ∏ j ∈ Finset.range k, rateBlaschkeFactor (gaussRate (j + 2)) (gaussRate 1) ^ 2 := by
  have h : (0 : ℝ) ≤ 8 / (k + 1) := by positivity
  exact (Real.exp_le_exp.2 (by linarith)).trans (exp_le_prod_rateBlaschkeFactor_sq k)

/-! ## The literal seed atoms on the half-line -/

local notation "ℓ²₊" => lp (fun _ : ℕ+ => ℂ) 2
local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-- The literal atom `n^{-1/2} h(x + log n)` of the theta source. -/
def seedAtomFun (n : ℕ+) (x : ℝ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspLogSeed (x + Real.log (n : ℕ))

theorem seedAtomFun_eq (n : ℕ+) (x : ℝ) :
    seedAtomFun n x = 2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (5 * x / 2) *
      (2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x) - 3) *
        Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))) := by
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have e2 : Real.exp (2 * (x + Real.log (n : ℕ))) = ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x) := by
    rw [mul_add, Real.exp_add, show 2 * Real.log ((n : ℕ) : ℝ) = Real.log (((n : ℕ) : ℝ) ^ 2) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity), mul_comm]
  have e5 : Real.exp (5 * (x + Real.log (n : ℕ)) / 2) =
      Real.exp (5 * x / 2) * ((n : ℕ) : ℝ) ^ (5 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hn, ← Real.exp_add]
    congr 1
    ring
  have epow : ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℕ) : ℝ) ^ (5 / 2 : ℝ) = ((n : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_add hn]; norm_num
  rw [seedAtomFun, thetaCuspLogSeed_eq, e2, e5]
  rw [show ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * (2 * Real.pi * (Real.exp (5 * x / 2) *
      ((n : ℕ) : ℝ) ^ (5 / 2 : ℝ)) * (2 * Real.pi * (((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)) - 3) *
        Real.exp (-(Real.pi * (((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))))) =
      (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℕ) : ℝ) ^ (5 / 2 : ℝ)) * (2 * Real.pi *
        Real.exp (5 * x / 2) * (2 * Real.pi * (((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)) - 3) *
          Real.exp (-(Real.pi * (((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))))) by ring, epow]
  ring_nf

theorem continuous_seedAtomFun (n : ℕ+) : Continuous (seedAtomFun n) :=
  continuous_const.mul (continuous_thetaCuspLogSeed.comp (continuous_id.add continuous_const))

/-- `h_n(x)² ≤ K n⁸ e^{−πn²} · e^{9x} e^{−π e^{2x}}` on `x ≥ 0`. -/
theorem sq_seedAtomFun_le (n : ℕ+) {x : ℝ} (hx : 0 ≤ x) :
    seedAtomFun n x ^ 2 ≤ (2 * Real.pi * (2 * Real.pi + 3)) ^ 2 * ((n : ℕ) : ℝ) ^ 8 *
      Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2)) *
        (Real.exp (9 * x) * Real.exp (-Real.pi * (Real.exp (2 * x) * 1))) := by
  have hn1 : (1 : ℝ) ≤ (n : ℕ) := by exact_mod_cast n.pos
  have hπ := Real.pi_pos
  set N : ℝ := ((n : ℕ) : ℝ) ^ 2
  set E : ℝ := Real.exp (2 * x)
  have hN1 : 1 ≤ N := one_le_pow₀ hn1
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hw : 1 ≤ N * E := one_le_mul_of_one_le_of_one_le hN1 hE1
  have habs : |2 * Real.pi * N * E - 3| ≤ (2 * Real.pi + 3) * (N * E) := by
    rw [abs_le]; constructor <;> nlinarith
  have h5 : Real.exp (5 * x / 2) ^ 2 * E ^ 2 = Real.exp (9 * x) := by
    simp only [E]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hexp : Real.exp (-(Real.pi * N * E)) ^ 2 ≤
      Real.exp (-(Real.pi * N)) * Real.exp (-Real.pi * (E * 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    push_cast
    nlinarith [mul_nonneg (sub_nonneg.2 hN1) (sub_nonneg.2 hE1), mul_pos hπ (lt_of_lt_of_le one_pos hw)]
  rw [seedAtomFun_eq]
  calc (2 * Real.pi * N * Real.exp (5 * x / 2) * (2 * Real.pi * N * E - 3) *
        Real.exp (-(Real.pi * N * E))) ^ 2
      = (2 * Real.pi) ^ 2 * N ^ 2 * Real.exp (5 * x / 2) ^ 2 * |2 * Real.pi * N * E - 3| ^ 2 *
          Real.exp (-(Real.pi * N * E)) ^ 2 := by rw [sq_abs]; ring
    _ ≤ (2 * Real.pi) ^ 2 * N ^ 2 * Real.exp (5 * x / 2) ^ 2 * ((2 * Real.pi + 3) * (N * E)) ^ 2 *
          (Real.exp (-(Real.pi * N)) * Real.exp (-Real.pi * (E * 1))) := by
        gcongr
    _ = (2 * Real.pi * (2 * Real.pi + 3)) ^ 2 * N ^ 4 * Real.exp (-(Real.pi * N)) *
          ((Real.exp (5 * x / 2) ^ 2 * E ^ 2) * Real.exp (-Real.pi * (E * 1))) := by ring
    _ = _ := by rw [h5]; simp only [N]; ring

theorem memLp_seedAtomFun (n : ℕ+) :
    MemLp (fun x => ((seedAtomFun n x : ℝ) : ℂ)) 2 halfLineMeasure := by
  have hmeas : AEStronglyMeasurable (fun x => ((seedAtomFun n x : ℝ) : ℂ)) halfLineMeasure :=
    (Complex.continuous_ofReal.comp (continuous_seedAtomFun n)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  have hI := (integrableOn_exp_mul_gaussRate 9 (t := 1) one_pos).const_mul
    ((2 * Real.pi * (2 * Real.pi + 3)) ^ 2 * ((n : ℕ) : ℝ) ^ 8 * Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2)))
  have hI' : IntegrableOn (fun x => (2 * Real.pi * (2 * Real.pi + 3)) ^ 2 * ((n : ℕ) : ℝ) ^ 8 *
      Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2)) *
        (Real.exp (9 * x) * Real.exp (-Real.pi * (Real.exp (2 * x) * 1)))) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 hI
  refine Integrable.mono' hI' ((continuous_norm.comp (Complex.continuous_ofReal.comp
    (continuous_seedAtomFun n))).pow 2).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ici).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact sq_seedAtomFun_le n hx

/-- The atom `C e_n` as a vector of `L²(0,∞)`. -/
def seedAtomLp (n : ℕ+) : L²₊ := (memLp_seedAtomFun n).toLp _

theorem seedAtomLp_coeFn (n : ℕ+) :
    (seedAtomLp n : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => ((seedAtomFun n x : ℝ) : ℂ) :=
  MemLp.coeFn_toLp _

theorem norm_sq_halfLine (u : L²₊) : ‖u‖ ^ 2 = ∫ x, ‖(u : ℝ → ℂ) x‖ ^ 2 ∂halfLineMeasure := by
  have h := MeasureTheory.L2.inner_def (𝕜 := ℂ) u u
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ∀ x, inner ℂ ((u : ℝ → ℂ) x) ((u : ℝ → ℂ) x) = ((‖(u : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  simp_rw [h2] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective (by push_cast; exact h)

/-- The seed-atom energy constant `M = ∫₀^∞ e^{9x} e^{−π e^{2x}} dx`. -/
def seedAtomEnergyConst : ℝ := ∫ x in Ici (0 : ℝ), Real.exp (9 * x) * Real.exp (-Real.pi * (Real.exp (2 * x) * 1))

theorem norm_sq_seedAtomLp_le (n : ℕ+) :
    ‖seedAtomLp n‖ ^ 2 ≤ (2 * Real.pi * (2 * Real.pi + 3)) ^ 2 * ((n : ℕ) : ℝ) ^ 8 *
      Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2)) * seedAtomEnergyConst := by
  rw [norm_sq_halfLine, seedAtomEnergyConst, ← integral_const_mul]
  have hI := (integrableOn_Ici_iff_integrableOn_Ioi).2 ((integrableOn_exp_mul_gaussRate 9 (t := 1)
    one_pos).const_mul ((2 * Real.pi * (2 * Real.pi + 3)) ^ 2 * ((n : ℕ) : ℝ) ^ 8 *
      Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2))))
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hI ?_
  filter_upwards [seedAtomLp_coeFn n, (ae_restrict_iff' measurableSet_Ici).2
    (Eventually.of_forall fun x (hx : x ∈ Ici (0 : ℝ)) => hx)] with x h1 h2
  rw [h1, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact sq_seedAtomFun_le n h2

theorem seedAtomEnergyConst_nonneg : 0 ≤ seedAtomEnergyConst :=
  setIntegral_nonneg measurableSet_Ici fun _ _ => by positivity

theorem summable_norm_seedAtomLp : Summable fun n : ℕ+ => ‖seedAtomLp n‖ := by
  set K := (2 * Real.pi * (2 * Real.pi + 3)) ^ 2 * seedAtomEnergyConst
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) seedAtomEnergyConst_nonneg
  have hb : ∀ n : ℕ+, ‖seedAtomLp n‖ ≤ Real.sqrt K * (((n : ℕ) : ℝ) ^ 4 *
      Real.exp (-(Real.pi / 2) * ((n : ℕ) : ℝ) ^ 2)) := fun n => by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    have hsq : (Real.sqrt K * (((n : ℕ) : ℝ) ^ 4 * Real.exp (-(Real.pi / 2) * ((n : ℕ) : ℝ) ^ 2))) ^ 2 =
        K * (((n : ℕ) : ℝ) ^ 8 * Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2))) := by
      rw [mul_pow, Real.sq_sqrt hK, mul_pow, ← pow_mul, ← Real.exp_nat_mul]
      congr 2; push_cast; ring_nf
    rw [← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt K * (((n : ℕ) : ℝ) ^ 4 *
      Real.exp (-(Real.pi / 2) * ((n : ℕ) : ℝ) ^ 2)))]
    refine Real.sqrt_le_sqrt ?_
    rw [hsq]
    have := norm_sq_seedAtomLp_le n
    simp only [K]
    nlinarith [this]
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb ?_
  refine Summable.mul_left _ ?_
  have := (summable_pow_mul_exp_neg_nat_sq 4 (sigma := Real.pi / 2) (by positivity))
  exact (GaloisForLFunctions.HTGeometry.PNatBlock.summable_pnat_iff
    (fun n : ℕ => (n : ℝ) ^ 4 * Real.exp (-(Real.pi / 2) * (n : ℝ) ^ 2))).2 this

/-! ## The synthesis operator `C` -/

section Synthesis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem summable_smul_of_summable_norm {v : ℕ+ → E} (hv : Summable fun n => ‖v n‖) (f : ℓ²₊) :
    Summable fun n => (f : ℕ+ → ℂ) n • v n :=
  Summable.of_norm_bounded (hv.mul_left ‖f‖) fun n => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm two_ne_zero f n) (norm_nonneg _)

/-- The synthesis operator `f ↦ Σ_n f(n) v_n` of an absolutely summable family. -/
def pnatSynthesis (v : ℕ+ → E) (hv : Summable fun n => ‖v n‖) : ℓ²₊ →L[ℂ] E :=
  LinearMap.mkContinuous
    { toFun := fun f => ∑' n, (f : ℕ+ → ℂ) n • v n
      map_add' := fun f g => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul_of_summable_norm hv f).tsum_add (summable_smul_of_summable_norm hv g)
      map_smul' := fun c f => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (summable_smul_of_summable_norm hv f).tsum_const_smul c }
    (∑' n, ‖v n‖) fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have hle : ∀ n, ‖(f : ℕ+ → ℂ) n • v n‖ ≤ ‖f‖ * ‖v n‖ := fun n => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm two_ne_zero f n) (norm_nonneg _)
      have hsn : Summable fun n => ‖(f : ℕ+ → ℂ) n • v n‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hv.mul_left _)
      calc ‖∑' n, (f : ℕ+ → ℂ) n • v n‖ ≤ ∑' n, ‖(f : ℕ+ → ℂ) n • v n‖ := norm_tsum_le_tsum_norm hsn
        _ ≤ ∑' n, ‖f‖ * ‖v n‖ := Summable.tsum_le_tsum hle hsn (hv.mul_left _)
        _ = (∑' n, ‖v n‖) * ‖f‖ := by rw [tsum_mul_left, mul_comm]

theorem pnatSynthesis_apply (v : ℕ+ → E) (hv : Summable fun n => ‖v n‖) (f : ℓ²₊) :
    pnatSynthesis v hv f = ∑' n, (f : ℕ+ → ℂ) n • v n := rfl

theorem pnatSynthesis_single (v : ℕ+ → E) (hv : Summable fun n => ‖v n‖) (n : ℕ+) :
    pnatSynthesis v hv (lp.single 2 n (1 : ℂ)) = v n := by
  classical
  rw [pnatSynthesis_apply, tsum_eq_single n fun m hm => by
    rw [lp.single_apply, Pi.single_eq_of_ne hm, zero_smul]]
  rw [lp.single_apply, Pi.single_eq_same, one_smul]

end Synthesis

/-- The literal seed synthesis `C e_n = n^{-1/2} h(· + log n)` on the positive half-line. -/
def seedSynthesis : ℓ²₊ →L[ℂ] L²₊ := pnatSynthesis seedAtomLp summable_norm_seedAtomLp

theorem seedSynthesis_single (n : ℕ+) : seedSynthesis (lp.single 2 n (1 : ℂ)) = seedAtomLp n :=
  pnatSynthesis_single _ _ n

/-- **(9)** `C` is Hilbert–Schmidt. -/
theorem isHilbertSchmidt_seedSynthesis : ContinuousLinearMap.IsHilbertSchmidt seedSynthesis := by
  classical
  refine ContinuousLinearMap.isHilbertSchmidt_of_summable (HilbertSchmidt.lpBasis ℕ+) ?_
  simp_rw [HilbertSchmidt.lpBasis_apply, seedSynthesis_single]
  have hv := summable_norm_seedAtomLp
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_) (hv.mul_left (∑' m, ‖seedAtomLp m‖))
  rw [sq]
  exact mul_le_mul_of_nonneg_right (hv.le_tsum n fun _ _ => norm_nonneg _) (norm_nonneg _)

/-- The left translation `(L_a f)(x) = f(x + a)` on the half-line. -/
def halfLineLeftShift (a : ℝ) : L²₊ →L[ℂ] L²₊ :=
  halfLineRestrict ∘L (Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ => x + a)
    (measurePreserving_add_right volume a)).toContinuousLinearMap ∘L halfLineExtend

theorem halfLineLeftShift_coeFn (a : ℝ) (u : L²₊) :
    (halfLineLeftShift a u : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (halfLineExtend u : ℝ → ℂ) (x + a) := by
  refine (halfLineRestrict_coeFn _).trans (ae_restrict_of_ae ?_)
  exact Lp.coeFn_compMeasurePreserving _ _

theorem halfLineExtend_seedAtomLp (n : ℕ+) :
    (halfLineExtend (seedAtomLp n) : ℝ → ℂ) =ᵐ[volume]
      (Ici 0).indicator fun x => ((seedAtomFun n x : ℝ) : ℂ) :=
  (halfLineExtend_coeFn _).trans (indicator_ae_eq_of_halfLine (seedAtomLp_coeFn n))

theorem seedAtomFun_shift {p : ℕ} (hp : 0 < p) (n : ℕ+) (x : ℝ) :
    (Real.sqrt p)⁻¹ * seedAtomFun n (x + Real.log p) = seedAtomFun (⟨p, hp⟩ * n) x := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hn' : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  simp only [seedAtomFun, PNat.mul_coe, PNat.mk_coe]
  push_cast
  rw [Real.mul_rpow hp'.le hn'.le, Real.log_mul hp'.ne' hn'.ne', Real.sqrt_eq_rpow,
    ← Real.rpow_neg hp'.le, show x + Real.log p + Real.log (n : ℕ) = x + (Real.log p + Real.log (n : ℕ))
      by ring]
  ring_nf

/-- The literal source shift on atoms: `p^{-1/2} L_{log p} (C e_n) = C e_{pn}`. -/
theorem sourceShift_seedAtomLp {p : ℕ} (hp : 0 < p) (n : ℕ+) :
    (((Real.sqrt p)⁻¹ : ℝ) : ℂ) • halfLineLeftShift (Real.log p) (seedAtomLp n) =
      seedAtomLp (⟨p, hp⟩ * n) := by
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp)
  refine Lp.ext ?_
  have hcomp := (measurePreserving_add_right volume (Real.log p)).quasiMeasurePreserving.ae_eq_comp
    (halfLineExtend_seedAtomLp n)
  filter_upwards [Lp.coeFn_smul (((Real.sqrt p)⁻¹ : ℝ) : ℂ) (halfLineLeftShift (Real.log p) (seedAtomLp n)),
    halfLineLeftShift_coeFn (Real.log p) (seedAtomLp n), ae_restrict_of_ae hcomp,
    seedAtomLp_coeFn (⟨p, hp⟩ * n), (ae_restrict_iff' measurableSet_Ici).2
      (Eventually.of_forall fun x (hx : x ∈ Ici (0 : ℝ)) => hx)] with x h1 h2 h3 h4 h5
  rw [h1, Pi.smul_apply, h2, h4]
  simp only [Function.comp] at h3
  rw [h3, Set.indicator_of_mem (show x + Real.log p ∈ Ici 0 from
    le_add_of_le_of_nonneg h5 hlog), smul_eq_mul, ← Complex.ofReal_mul, seedAtomFun_shift hp]

/-- **(9)** `C S_p = T_p C` with the literal source shift `T_p = p^{-1/2} L_{log p}`. -/
theorem seedSynthesis_comp_eulerLabelShift {p : ℕ} (hp : 0 < p) :
    seedSynthesis ∘L eulerLabelShift p =
      (((Real.sqrt p)⁻¹ : ℝ) : ℂ) • (halfLineLeftShift (Real.log p) ∘L seedSynthesis) := by
  refine clm_ext_single fun n => ?_
  rw [ContinuousLinearMap.comp_apply, eulerLabelShift_single hp, seedSynthesis_single]
  show _ = (((Real.sqrt p)⁻¹ : ℝ) : ℂ) • halfLineLeftShift (Real.log p)
    (seedSynthesis (lp.single 2 n (1 : ℂ)))
  rw [seedSynthesis_single, sourceShift_seedAtomLp hp]

/-! ## The separator vectors -/

/-- The logarithmic substitution `v = e^{2x} − 1`. -/
def logSubst (x : ℝ) : ℝ := Real.exp (2 * x) - 1

theorem hasDerivAt_logSubst (x : ℝ) : HasDerivAt logSubst (2 * Real.exp (2 * x)) x := by
  have := ((hasDerivAt_id x).const_mul 2).exp.sub_const 1
  refine this.congr_deriv ?_
  simp [mul_comm]

theorem image_logSubst_Ioi : logSubst '' Ioi 0 = Ioi 0 := by
  ext v
  simp only [mem_image, mem_Ioi, logSubst]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have := Real.exp_lt_exp.2 (by linarith : (0 : ℝ) < 2 * x)
    rw [Real.exp_zero] at this
    linarith
  · intro hv
    refine ⟨Real.log (v + 1) / 2, by
      have := Real.log_pos (by linarith : 1 < v + 1); positivity, ?_⟩
    rw [show 2 * (Real.log (v + 1) / 2) = Real.log (v + 1) by ring, Real.exp_log (by linarith)]
    ring

theorem injOn_logSubst : InjOn logSubst (Ioi 0) := fun x _ y _ h => by
  have h' : Real.exp (2 * x) = Real.exp (2 * y) := by
    have := h; unfold logSubst at this; linarith
  have := Real.exp_injective h'
  linarith

/-- **Change of variables** `∫₀^∞ |f'| G(f x) dx = ∫₀^∞ G(v) dv` for `f = e^{2x} − 1`. -/
theorem integral_logSubst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : ℝ → F) :
    ∫ x in Ioi (0 : ℝ), (2 * Real.exp (2 * x)) • G (logSubst x) = ∫ v in Ioi (0 : ℝ), G v := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := logSubst)
    (f' := fun x => 2 * Real.exp (2 * x)) measurableSet_Ioi
    (fun x _ => (hasDerivAt_logSubst x).hasDerivWithinAt) injOn_logSubst G
  rw [image_logSubst_Ioi] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [abs_of_pos (by positivity)]

theorem integrableOn_logSubst {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (G : ℝ → F) :
    IntegrableOn (fun x => (2 * Real.exp (2 * x)) • G (logSubst x)) (Ioi 0) ↔
      IntegrableOn G (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ)) (f := logSubst)
    (f' := fun x => 2 * Real.exp (2 * x)) measurableSet_Ioi
    (fun x _ => (hasDerivAt_logSubst x).hasDerivWithinAt) injOn_logSubst G
  rw [image_logSubst_Ioi] at h
  rw [h]
  refine integrableOn_congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [abs_of_pos (by positivity)]

/-- The separator profile `g(x) = conj(r(e^{2x} − 1)) e^{−x/2}`. -/
def separatorFun (r : QuasiPolynomial) (x : ℝ) : ℂ :=
  (starRingEnd ℂ) (r.eval (logSubst x)) * (Real.exp (-(x / 2)) : ℂ)

theorem continuous_separatorFun (r : QuasiPolynomial) : Continuous (separatorFun r) := by
  unfold separatorFun logSubst
  exact (Complex.continuous_conj.comp ((QuasiPolynomial.continuous_eval r).comp (by fun_prop))).mul
    (by fun_prop)

/-- The separator energy density in the substituted variable. -/
def separatorDensity (r : QuasiPolynomial) (v : ℝ) : ℝ :=
  ‖r.eval v‖ ^ 2 * (v + 1) ^ (-(3 / 2 : ℝ)) / 2

theorem norm_sq_separatorFun (r : QuasiPolynomial) (x : ℝ) :
    ‖separatorFun r x‖ ^ 2 = (2 * Real.exp (2 * x)) • separatorDensity r (logSubst x) := by
  have hsub : logSubst x + 1 = Real.exp (2 * x) := by simp [logSubst]
  have h1 : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h2 : Real.exp (2 * x) ^ (-(3 / 2 : ℝ)) = Real.exp (-(3 * x)) := by
    rw [← Real.exp_mul]; congr 1; ring
  have h3 : Real.exp (2 * x) * Real.exp (-(3 * x)) = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [separatorDensity, hsub, smul_eq_mul, separatorFun, norm_mul, Complex.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow, h1, h2,
    show 2 * Real.exp (2 * x) * (‖r.eval (logSubst x)‖ ^ 2 * Real.exp (-(3 * x)) / 2) =
      ‖r.eval (logSubst x)‖ ^ 2 * (Real.exp (2 * x) * Real.exp (-(3 * x))) by ring, h3]

theorem continuousOn_separatorDensity (r : QuasiPolynomial) :
    ContinuousOn (separatorDensity r) (Ioi 0) := by
  unfold separatorDensity
  refine ContinuousOn.div_const (((continuous_norm.comp
    (QuasiPolynomial.continuous_eval r)).pow 2).continuousOn.mul ?_) 2
  exact ContinuousOn.rpow_const (continuousOn_id.add continuousOn_const)
    (fun v hv => Or.inl (by simp only [mem_Ioi] at hv; linarith))

theorem separatorDensity_le {r : QuasiPolynomial} {v : ℝ} (hv : 0 < v) :
    separatorDensity r v ≤ ‖r.eval v‖ ^ 2 / 2 := by
  have hv' : (1 : ℝ) ≤ v + 1 := by linarith
  have hrp : (v + 1) ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hv' (by norm_num)
  unfold separatorDensity
  gcongr
  exact mul_le_of_le_one_right (sq_nonneg _) hrp

theorem separatorDensity_nonneg (r : QuasiPolynomial) {v : ℝ} (hv : 0 < v) :
    0 ≤ separatorDensity r v := by
  unfold separatorDensity
  have : 0 ≤ (v + 1) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  positivity

theorem integrableOn_separatorDensity {r : QuasiPolynomial} (hr : IsDecayingQP r) :
    IntegrableOn (separatorDensity r) (Ioi 0) := by
  refine Integrable.mono' (hr.integrableOn_norm_sq.div_const 2)
    ((continuousOn_separatorDensity r).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' (measurableSet_Ioi (a := (0 : ℝ)))).2 (Eventually.of_forall fun v hv => ?_)
  rw [Real.norm_of_nonneg (separatorDensity_nonneg r hv)]
  exact separatorDensity_le hv

theorem memLp_separatorFun {r : QuasiPolynomial} (hr : IsDecayingQP r) :
    MemLp (separatorFun r) 2 halfLineMeasure := by
  refine (memLp_two_iff_integrable_sq_norm (continuous_separatorFun r).aestronglyMeasurable).2 ?_
  change IntegrableOn (fun x => ‖separatorFun r x‖ ^ 2) (Ici (0 : ℝ))
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp_rw [norm_sq_separatorFun]
  exact (integrableOn_logSubst (separatorDensity r)).2 (integrableOn_separatorDensity hr)

/-- The separator vector `g_r ∈ L²(0,∞)`. -/
def separatorVec {r : QuasiPolynomial} (hr : IsDecayingQP r) : L²₊ := (memLp_separatorFun hr).toLp _

theorem separatorVec_coeFn {r : QuasiPolynomial} (hr : IsDecayingQP r) :
    (separatorVec hr : ℝ → ℂ) =ᵐ[halfLineMeasure] separatorFun r := MemLp.coeFn_toLp _

/-- **Energy of a separator**: `‖g_r‖² ≤ ½ ∫₀^∞ |r|²`. -/
theorem norm_sq_separatorVec_le {r : QuasiPolynomial} (hr : IsDecayingQP r) :
    ‖separatorVec hr‖ ^ 2 ≤ (∫ v in Ioi (0 : ℝ), ‖r.eval v‖ ^ 2) / 2 := by
  rw [norm_sq_halfLine, integral_congr_ae (by
    filter_upwards [separatorVec_coeFn hr] with x hx; rw [hx])]
  change ∫ x in Ici (0 : ℝ), ‖separatorFun r x‖ ^ 2 ≤ _
  rw [integral_Ici_eq_integral_Ioi]
  simp_rw [norm_sq_separatorFun]
  rw [integral_logSubst, ← integral_div]
  exact setIntegral_mono_on (integrableOn_separatorDensity hr) (hr.integrableOn_norm_sq.div_const 2)
    measurableSet_Ioi fun v hv => separatorDensity_le hv

/-! ## The pairing of a separator with the literal atoms -/

/-- The substituted pairing density `Ψ(v) = π n² r(v) (2λ(v+1) − 3) e^{−λ(v+1)}`. -/
def pairingDensity (r : QuasiPolynomial) (n : ℕ+) (v : ℝ) : ℂ :=
  ((Real.pi * ((n : ℕ) : ℝ) ^ 2 : ℝ) : ℂ) * r.eval v *
    (((2 * gaussRate n * (v + 1) - 3) * Real.exp (-(gaussRate n * (v + 1))) : ℝ) : ℂ)

theorem conj_separatorFun_mul_seedAtomFun (r : QuasiPolynomial) (n : ℕ+) (x : ℝ) :
    (starRingEnd ℂ) (separatorFun r x) * ((seedAtomFun n x : ℝ) : ℂ) =
      (2 * Real.exp (2 * x)) • pairingDensity r n (logSubst x) := by
  have hsub : logSubst x + 1 = Real.exp (2 * x) := by simp [logSubst]
  have he : Real.exp (-(x / 2)) * Real.exp (5 * x / 2) = Real.exp (2 * x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [separatorFun, map_mul, Complex.conj_conj, Complex.conj_ofReal, seedAtomFun_eq, pairingDensity,
    hsub, gaussRate, Complex.real_smul]
  have : ((Real.exp (-(x / 2)) : ℝ) : ℂ) * ((2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (5 * x / 2) *
      (2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x) - 3) *
        Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))) : ℝ) : ℂ) =
      ((2 * Real.exp (2 * x) * (Real.pi * ((n : ℕ) : ℝ) ^ 2) *
        ((2 * (Real.pi * ((n : ℕ) : ℝ) ^ 2) * Real.exp (2 * x) - 3) *
          Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x))))) : ℝ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [show Real.exp (-(x / 2)) * (2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (5 * x / 2) *
      (2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x) - 3) *
        Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)))) =
      (Real.exp (-(x / 2)) * Real.exp (5 * x / 2)) * (2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 *
      (2 * Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x) - 3) *
        Real.exp (-(Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (2 * x)))) by ring, he]
    ring_nf
  rw [mul_assoc, this]
  push_cast
  ring_nf

theorem pairingDensity_eq (r : QuasiPolynomial) (n : ℕ+) (v : ℝ) :
    pairingDensity r n v = ((Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (-gaussRate n) : ℝ) : ℂ) *
      ((((2 * gaussRate n - 3 : ℝ)) : ℂ) * (r.eval v * Complex.exp (-(((gaussRate n : ℝ) : ℂ) * v))) +
        (((2 * gaussRate n : ℝ)) : ℂ) * ((v : ℂ) * r.eval v * Complex.exp (-(((gaussRate n : ℝ) : ℂ) * v)))) := by
  rw [pairingDensity, show -(gaussRate n * (v + 1)) = -gaussRate n + -(gaussRate n * v) by ring,
    Real.exp_add]
  push_cast
  rw [show Complex.exp (-(↑(gaussRate n) * ↑v)) = ((Real.exp (-(gaussRate n * v)) : ℝ) : ℂ) by
    push_cast; ring_nf]
  push_cast
  ring

/-- **Pairing formula.**  `⟪g_r, C e_n⟫ = π n² e^{−λ_n} ((2λ_n − 3) ℒr(λ_n) + 2λ_n ℒ(v r)(λ_n))`. -/
theorem inner_separatorVec_seedAtomLp {r : QuasiPolynomial} (hr : IsDecayingQP r) (n : ℕ+) :
    inner ℂ (separatorVec hr) (seedAtomLp n) =
      ((Real.pi * ((n : ℕ) : ℝ) ^ 2 * Real.exp (-gaussRate n) : ℝ) : ℂ) *
        ((((2 * gaussRate n - 3 : ℝ)) : ℂ) * r.laplace (gaussRate n) +
          (((2 * gaussRate n : ℝ)) : ℂ) * (qpMulX r).laplace (gaussRate n)) := by
  have hlam := gaussRate_pos n.pos
  have hq : ∀ μ ∈ r.support, μ.re < (((gaussRate n : ℝ) : ℂ)).re := fun μ hμ => by
    simpa using (hr μ hμ).trans hlam
  rw [MeasureTheory.L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [separatorVec_coeFn hr, seedAtomLp_coeFn n] with x h1 h2
    rw [h1, h2, RCLike.inner_apply, mul_comm])]
  change ∫ x in Ici (0 : ℝ), (starRingEnd ℂ) (separatorFun r x) * ((seedAtomFun n x : ℝ) : ℂ) = _
  rw [integral_Ici_eq_integral_Ioi]
  simp_rw [conj_separatorFun_mul_seedAtomFun]
  rw [integral_logSubst]
  simp_rw [pairingDensity_eq]
  have h1 := QuasiPolynomial.integral_eval_mul_cexp r hq
  have h2 := integral_eval_qpMulX_mul_cexp r hq
  have i1 := h1.1
  have i2 := integrableOn_eval_qpMulX_mul_cexp r hq
  rw [integral_const_mul, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul,
    integral_const_mul, h1.2, h2]

/-! ## The literal seed keeps the vacuum visible -/

/-- The separator family `g_k = g_{r_k}`. -/
def seedSeparatorVec (k : ℕ) : L²₊ := separatorVec (isDecaying_seedSeparator k)

theorem inner_seedSeparatorVec_seedAtomLp_eq_zero {k : ℕ} {n : ℕ+} (h2 : 2 ≤ (n : ℕ))
    (hk : (n : ℕ) ≤ k + 1) : inner ℂ (seedSeparatorVec k) (seedAtomLp n) = 0 := by
  obtain ⟨hL, hD⟩ := (seedSeparator_zeros k).1 n h2 hk
  rw [seedSeparatorVec, inner_separatorVec_seedAtomLp, hL,
    show (qpMulX (seedSeparator k)).laplace (gaussRate n) = -seedDeriv k (gaussRate n) by
      rw [seedDeriv, neg_neg], hD]
  simp

/-- The separator constant `κ = 2π λ₁ e^{−λ₁} e^{−8}/(λ₁+1)²`. -/
def separatorGap : ℝ :=
  2 * Real.pi * gaussRate 1 * Real.exp (-gaussRate 1) * Real.exp (-8) / (gaussRate 1 + 1) ^ 2

theorem separatorGap_pos : 0 < separatorGap := by
  have := gaussRate_pos (show 0 < 1 by omega)
  unfold separatorGap; positivity

theorem separatorGap_le_norm_inner (k : ℕ) :
    separatorGap ≤ ‖inner ℂ (seedSeparatorVec k) (seedAtomLp 1)‖ := by
  have h1 := gaussRate_pos (show 0 < 1 by omega)
  obtain ⟨-, hL, hD⟩ := seedSeparator_zeros k
  have hval : inner ℂ (seedSeparatorVec k) (seedAtomLp 1) =
      ((-(2 * Real.pi * gaussRate 1 * Real.exp (-gaussRate 1) *
        ((∏ j ∈ Finset.range k, rateBlaschkeFactor (gaussRate (j + 2)) (gaussRate 1) ^ 2) /
          (gaussRate 1 + 1) ^ 2)) : ℝ) : ℂ) := by
    rw [seedSeparatorVec, inner_separatorVec_seedAtomLp]
    simp only [PNat.one_coe, Nat.cast_one]
    rw [hL, show (qpMulX (seedSeparator k)).laplace (gaussRate 1) = -seedDeriv k (gaussRate 1) by
      rw [seedDeriv, neg_neg], hD]
    push_cast
    ring
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by
    have := Finset.prod_nonneg fun j (_ : j ∈ Finset.range k) =>
      sq_nonneg (rateBlaschkeFactor (gaussRate (j + 2)) (gaussRate 1))
    positivity), separatorGap]
  have hP := exp_neg_eight_le_prod_rateBlaschkeFactor_sq k
  have hc : 0 ≤ 2 * Real.pi * gaussRate 1 * Real.exp (-gaussRate 1) := by positivity
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  exact div_le_div_of_nonneg_right hP (by positivity)

/-- The uniform separator energy `B = √(½ ∫₀^∞ |r₀|²)`. -/
def separatorEnergy : ℝ := Real.sqrt ((∫ v in Ioi (0 : ℝ), ‖seedSeparatorBase.eval v‖ ^ 2) / 2)

theorem norm_seedSeparatorVec_le (k : ℕ) : ‖seedSeparatorVec k‖ ≤ separatorEnergy := by
  rw [separatorEnergy, ← Real.sqrt_sq (norm_nonneg _)]
  refine Real.sqrt_le_sqrt ?_
  have := norm_sq_separatorVec_le (isDecaying_seedSeparator k)
  rwa [integral_norm_sq_seedSeparator] at this

/-- Vectors of the span of the higher atoms are eventually annihilated by the separators. -/
theorem eventually_inner_seedSeparatorVec_eq_zero {v : L²₊}
    (hv : v ∈ Submodule.span ℂ (Set.range fun n : {n : ℕ+ // n ≠ 1} => seedAtomLp n)) :
    ∃ K, ∀ k, K ≤ k → inner ℂ (seedSeparatorVec k) v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨n, hn⟩, rfl⟩ := hx
    have h1 : (n : ℕ) ≠ 1 := fun h => hn (PNat.eq h)
    have h0 := n.pos
    refine ⟨n, fun k hk => ?_⟩
    show inner ℂ (seedSeparatorVec k) (seedAtomLp n) = 0
    exact inner_seedSeparatorVec_seedAtomLp_eq_zero (by omega) (by omega)
  | zero => exact ⟨0, fun k _ => inner_zero_right _⟩
  | add x y _ _ hx hy =>
    obtain ⟨K₁, h₁⟩ := hx
    obtain ⟨K₂, h₂⟩ := hy
    exact ⟨max K₁ K₂, fun k hk => by
      rw [inner_add_right, h₁ k (le_of_max_le_left hk), h₂ k (le_of_max_le_right hk), add_zero]⟩
  | smul c x _ hx =>
    obtain ⟨K, h⟩ := hx
    exact ⟨K, fun k hk => by rw [inner_smul_right, h k hk, mul_zero]⟩

/-- **(10) `C e_1` lies outside the closed span of every higher literal theta atom.** -/
theorem seedAtomLp_one_not_mem_closure :
    seedAtomLp 1 ∉
      (Submodule.span ℂ (Set.range fun n : {n : ℕ+ // n ≠ 1} => seedAtomLp n)).topologicalClosure := by
  intro hmem
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  have hB := norm_nonneg (seedSeparatorVec 0)
  have hB0 : 0 ≤ separatorEnergy := hB.trans (norm_seedSeparatorVec_le 0)
  obtain ⟨v, hv, hdist⟩ := hmem (separatorGap / (separatorEnergy + 1))
    (div_pos separatorGap_pos (by linarith))
  obtain ⟨K, hK⟩ := eventually_inner_seedSeparatorVec_eq_zero hv
  have h1 := separatorGap_le_norm_inner K
  have h2 : inner ℂ (seedSeparatorVec K) (seedAtomLp 1) =
      inner ℂ (seedSeparatorVec K) (seedAtomLp 1 - v) := by
    rw [inner_sub_right, hK K le_rfl, sub_zero]
  have h3 : ‖inner ℂ (seedSeparatorVec K) (seedAtomLp 1 - v)‖ ≤
      separatorEnergy * (separatorGap / (separatorEnergy + 1)) := by
    refine (norm_inner_le_norm _ _).trans (mul_le_mul (norm_seedSeparatorVec_le K) ?_
      (norm_nonneg _) hB0)
    rw [← dist_eq_norm]; exact hdist.le
  rw [h2] at h1
  have h4 : separatorEnergy * (separatorGap / (separatorEnergy + 1)) < separatorGap := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith [separatorGap_pos]
  linarith

/-- **(10) The vacuum separator.**  There is `g ∈ L²(0,∞)` with `⟪g, C e_n⟫ = 0` for `n ≥ 2` and
`⟪g, C e_1⟫ ≠ 0`. -/
theorem exists_seed_vacuum_separator :
    ∃ g : L²₊, (∀ n : ℕ+, n ≠ 1 → inner ℂ g (seedSynthesis (lp.single 2 n (1 : ℂ))) = 0) ∧
      inner ℂ g (seedSynthesis (lp.single 2 1 (1 : ℂ))) ≠ 0 := by
  set M := (Submodule.span ℂ (Set.range fun n : {n : ℕ+ // n ≠ 1} => seedAtomLp n)).topologicalClosure
  have hnot := seedAtomLp_one_not_mem_closure
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal] at hnot
  push Not at hnot
  obtain ⟨g, hg, hne⟩ := hnot
  refine ⟨g, fun n hn => ?_, by rwa [seedSynthesis_single]⟩
  rw [seedSynthesis_single]
  have hmem : seedAtomLp n ∈ Submodule.span ℂ (Set.range fun n : {n : ℕ+ // n ≠ 1} => seedAtomLp n) :=
    Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
  rw [Submodule.mem_orthogonal] at hg
  exact inner_eq_zero_symm.1 (hg _ hmem)

/-! ## The Euler source on the half-line -/

theorem seedAtomFun_eq_sourceTerm (n : ℕ+) (x : ℝ) :
    seedAtomFun n x = thetaCuspSourceTerm x (n : ℕ) :=
  rpow_neg_half_mul_thetaCuspLogSeed (n : ℕ) x

theorem seedAtomFun_one (x : ℝ) : seedAtomFun 1 x = thetaCuspLogSeed x := by
  simp [seedAtomFun]

theorem hasSum_seedAtomFun (x : ℝ) :
    HasSum (fun n : ℕ+ => ((seedAtomFun n x : ℝ) : ℂ)) (thetaCuspFullSource x : ℂ) := by
  rw [Complex.hasSum_ofReal]
  have hs := summable_thetaCuspSourceTerm x
  have h0 : thetaCuspSourceTerm x 0 = 0 := by simp [thetaCuspSourceTerm, thetaCuspSeed]
  have hsp : Summable fun n : ℕ+ => seedAtomFun n x := by
    simp_rw [seedAtomFun_eq_sourceTerm]
    exact (GaloisForLFunctions.HTGeometry.PNatBlock.summable_pnat_iff
      (fun n : ℕ => thetaCuspSourceTerm x n)).2 hs
  convert hsp.hasSum using 1
  simp_rw [seedAtomFun_eq_sourceTerm]
  rw [GaloisForLFunctions.HTGeometry.PNatBlock.tsum_pnat (fun n : ℕ => thetaCuspSourceTerm x n) h0,
    thetaCuspFullSource]

/-- The half-line Euler source `k = Σ_n n^{-1/2} h(· + log n)` as a vector of `L²(0,∞)`. -/
def eulerSourceLp : L²₊ := ∑' n, seedAtomLp n

theorem hasSum_seedAtomLp : HasSum seedAtomLp eulerSourceLp :=
  (Summable.of_norm summable_norm_seedAtomLp).hasSum

/-- **The actual Euler source converges absolutely in half-line `L²`**, to the literal source. -/
theorem eulerSourceLp_coeFn :
    (eulerSourceLp : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (thetaCuspFullSource x : ℂ) := by
  have hne : ∑' n, ‖seedAtomLp n‖ₑ ≠ ⊤ := by
    simp_rw [enorm_eq_nnnorm]
    refine ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 ?_)
    simpa using summable_norm_seedAtomLp
  filter_upwards [Lp.hasSum_coeFn_tsum hne, ae_all_iff.2 fun n => seedAtomLp_coeFn n] with x h1 h2
  simp_rw [h2] at h1
  exact h1.unique (hasSum_seedAtomFun x)

/-- **(10a)** A vector annihilating every higher atom pairs with the source exactly as with its
unit term: `⟪g, k⟫ = Σ_n ⟪g, C e_n⟫ = ⟪g, h⟫`. -/
theorem inner_eulerSourceLp_of_separator {g : L²₊}
    (hg : ∀ n : ℕ+, n ≠ 1 → inner ℂ g (seedAtomLp n) = 0) :
    inner ℂ g eulerSourceLp = inner ℂ g (seedAtomLp 1) := by
  have h := hasSum_seedAtomLp.mapL (innerSL ℂ g)
  simp only [innerSL_apply_apply] at h
  rw [← h.tsum_eq, tsum_eq_single 1 hg]

/-- **(10), (10a)** The literal seed keeps the vacuum visible: some `g ∈ L²(0,∞)` annihilates every
`C e_n`, `n ≥ 2`, pairs non-trivially with `C e_1 = h`, and extracts that unit term from the Euler
source `k`. -/
theorem exists_seed_vacuum_separator_source :
    ∃ g : L²₊, (∀ n : ℕ+, n ≠ 1 → inner ℂ g (seedSynthesis (lp.single 2 n (1 : ℂ))) = 0) ∧
      inner ℂ g (seedSynthesis (lp.single 2 1 (1 : ℂ))) ≠ 0 ∧
      inner ℂ g eulerSourceLp = inner ℂ g (seedSynthesis (lp.single 2 1 (1 : ℂ))) := by
  obtain ⟨g, hg, hne⟩ := exists_seed_vacuum_separator
  refine ⟨g, hg, hne, ?_⟩
  rw [seedSynthesis_single]
  exact inner_eulerSourceLp_of_separator fun n hn => by
    have := hg n hn; rwa [seedSynthesis_single] at this

theorem seedAtomLp_one_coeFn :
    (seedAtomLp 1 : ℝ → ℂ) =ᵐ[halfLineMeasure] fun x => (thetaCuspLogSeed x : ℂ) := by
  filter_upwards [seedAtomLp_coeFn 1] with x hx
  rw [hx, seedAtomFun_one]

/-! ## The full-line synthesis is bounded -/

local notation "L²ℝ" => Lp ℂ 2 (volume : Measure ℝ)

/-- The two-sided seed constant. -/
def seedTwoSidedConst : ℝ := 2 * Real.pi * (2 * Real.pi + 3) * (1 + 24 / Real.pi ^ 4)

/-- **Two-sided decay of the seed**: `|h(y)| ≤ K e^{−5|y|/2}`. -/
theorem abs_thetaCuspLogSeed_le (y : ℝ) :
    |thetaCuspLogSeed y| ≤ seedTwoSidedConst * Real.exp (-(5 / 2 * |y|)) := by
  have hπ := Real.pi_pos
  rw [thetaCuspLogSeed_eq]
  set w := Real.exp (2 * y)
  have hw0 : 0 < w := Real.exp_pos _
  have hK1 : 2 * Real.pi * (2 * Real.pi + 3) ≤ seedTwoSidedConst := by
    unfold seedTwoSidedConst
    have : (0 : ℝ) ≤ 24 / Real.pi ^ 4 := by positivity
    nlinarith [mul_pos (mul_pos two_pos hπ) (by linarith : (0:ℝ) < 2 * Real.pi + 3)]
  rcases le_or_gt y 0 with hy | hy
  · have hw1 : w ≤ 1 := by simpa [w] using Real.exp_le_one_iff.2 (by linarith : 2 * y ≤ 0)
    have habs : |2 * Real.pi * w - 3| ≤ 2 * Real.pi + 3 := by
      rw [abs_le]; constructor <;> nlinarith
    have hexp : Real.exp (-(Real.pi * w)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [abs_of_nonpos hy, show -(5 / 2 * -y) = 5 * y / 2 by ring, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi * Real.exp (5 * y / 2)),
      abs_of_pos (Real.exp_pos _)]
    calc 2 * Real.pi * Real.exp (5 * y / 2) * |2 * Real.pi * w - 3| * Real.exp (-(Real.pi * w))
        ≤ 2 * Real.pi * Real.exp (5 * y / 2) * (2 * Real.pi + 3) * 1 := by gcongr
      _ = 2 * Real.pi * (2 * Real.pi + 3) * Real.exp (5 * y / 2) := by ring
      _ ≤ seedTwoSidedConst * Real.exp (5 * y / 2) := by gcongr
  · have hw1 : 1 ≤ w := by simpa [w] using Real.one_le_exp (by linarith : 0 ≤ 2 * y)
    have habs : |2 * Real.pi * w - 3| ≤ (2 * Real.pi + 3) * w := by
      rw [abs_le]; constructor <;> nlinarith
    have hfact := Real.pow_div_factorial_le_exp (Real.pi * w) (by positivity) 4
    have h24 : w ^ 4 * Real.exp (-(Real.pi * w)) ≤ 24 / Real.pi ^ 4 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
      have : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
      rw [this, div_le_iff₀ (by norm_num), mul_pow] at hfact
      nlinarith
    have h5 : Real.exp (5 * y / 2) * Real.exp (5 / 2 * y) ≤ w ^ 3 := by
      rw [← Real.exp_add, show w ^ 3 = Real.exp (6 * y) by
        simp only [w]; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
      exact Real.exp_le_exp.2 (by linarith)
    rw [abs_of_pos hy, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi *
      Real.exp (5 * y / 2)), abs_of_pos (Real.exp_pos _)]
    have key : 2 * Real.pi * Real.exp (5 * y / 2) * |2 * Real.pi * w - 3| *
        Real.exp (-(Real.pi * w)) * Real.exp (5 / 2 * y) ≤ seedTwoSidedConst := by
      calc 2 * Real.pi * Real.exp (5 * y / 2) * |2 * Real.pi * w - 3| *
            Real.exp (-(Real.pi * w)) * Real.exp (5 / 2 * y)
          = 2 * Real.pi * (Real.exp (5 * y / 2) * Real.exp (5 / 2 * y)) * |2 * Real.pi * w - 3| *
              Real.exp (-(Real.pi * w)) := by ring
        _ ≤ 2 * Real.pi * w ^ 3 * ((2 * Real.pi + 3) * w) * Real.exp (-(Real.pi * w)) := by gcongr
        _ = 2 * Real.pi * (2 * Real.pi + 3) * (w ^ 4 * Real.exp (-(Real.pi * w))) := by ring
        _ ≤ 2 * Real.pi * (2 * Real.pi + 3) * (24 / Real.pi ^ 4) := by gcongr
        _ ≤ seedTwoSidedConst := by
            unfold seedTwoSidedConst
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc 2 * Real.pi * Real.exp (5 * y / 2) * |2 * Real.pi * w - 3| * Real.exp (-(Real.pi * w))
        = (2 * Real.pi * Real.exp (5 * y / 2) * |2 * Real.pi * w - 3| * Real.exp (-(Real.pi * w)) *
            Real.exp (5 / 2 * y)) * Real.exp (-(5 / 2 * y)) := by
          rw [mul_assoc _ (Real.exp (5 / 2 * y)), ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ seedTwoSidedConst * Real.exp (-(5 / 2 * y)) := by gcongr

theorem seedTwoSidedConst_nonneg : 0 ≤ seedTwoSidedConst := by
  unfold seedTwoSidedConst; have := Real.pi_pos; positivity

theorem abs_seedAtomFun_le (n : ℕ+) (x : ℝ) :
    |seedAtomFun n x| ≤ seedTwoSidedConst * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
      Real.exp (-(5 / 2 * |x + Real.log (n : ℕ)|)) := by
  rw [seedAtomFun, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  calc ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * |thetaCuspLogSeed (x + Real.log (n : ℕ))|
      ≤ ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * (seedTwoSidedConst *
          Real.exp (-(5 / 2 * |x + Real.log (n : ℕ)|))) := by
        gcongr; exact abs_thetaCuspLogSeed_le _
    _ = _ := by ring

theorem integrable_exp_abs_shift {β : ℝ} (hβ : 0 < β) (a : ℝ) :
    Integrable fun x : ℝ => Real.exp (-(β * |x + a|)) := by
  refine (GaloisForLFunctions.HTGeometry.integrable_exp_neg_mul_abs_sub hβ (-a)).congr
    (Eventually.of_forall fun x => ?_)
  simp only
  rw [show -a - x = -(x + a) by ring, abs_neg]

theorem integral_exp_abs_shift {β : ℝ} (hβ : 0 < β) (a : ℝ) :
    ∫ x : ℝ, Real.exp (-(β * |x + a|)) = 2 / β := by
  rw [← GaloisForLFunctions.HTGeometry.integral_exp_neg_mul_abs_sub hβ (-a)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  rw [show -a - x = -(x + a) by ring, abs_neg]

theorem memLp_seedAtomFun_line (n : ℕ+) :
    MemLp (fun x => ((seedAtomFun n x : ℝ) : ℂ)) 2 (volume : Measure ℝ) := by
  have hmeas : AEStronglyMeasurable (fun x => ((seedAtomFun n x : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.comp (continuous_seedAtomFun n)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine Integrable.mono' ((integrable_exp_abs_shift (by norm_num : (0 : ℝ) < 5)
    (Real.log (n : ℕ))).const_mul ((seedTwoSidedConst * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2))
    ((continuous_norm.comp (Complex.continuous_ofReal.comp (continuous_seedAtomFun n))).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs]
  calc |seedAtomFun n x| ^ 2 ≤ (seedTwoSidedConst * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (-(5 / 2 * |x + Real.log (n : ℕ)|))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_seedAtomFun_le n x) 2
    _ = (seedTwoSidedConst * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 *
        Real.exp (-(5 * |x + Real.log (n : ℕ)|)) := by
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring

/-- The full-line atom `n^{-1/2} h(· + log n) ∈ L²(ℝ)`. -/
def seedAtomLine (n : ℕ+) : L²ℝ := (memLp_seedAtomFun_line n).toLp _

theorem seedAtomLine_coeFn (n : ℕ+) :
    (seedAtomLine n : ℝ → ℂ) =ᵐ[volume] fun x => ((seedAtomFun n x : ℝ) : ℂ) := MemLp.coeFn_toLp _

/-- The Gram bound `|⟪a_n, a_m⟫| ≤ 4K² (nm)^{-1/2} e^{−2|log n − log m|}`. -/
def seedGramBound (n m : ℕ+) : ℝ :=
  4 * seedTwoSidedConst ^ 2 * (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
    Real.exp (-(2 * |Real.log (n : ℕ) - Real.log (m : ℕ)|))

theorem seedGramBound_comm (n m : ℕ+) : seedGramBound n m = seedGramBound m n := by
  unfold seedGramBound; rw [abs_sub_comm]; ring

theorem seedGramBound_nonneg (n m : ℕ+) : 0 ≤ seedGramBound n m := by
  unfold seedGramBound
  have := Real.rpow_nonneg (Nat.cast_nonneg ((n : ℕ))) (-(1 / 2 : ℝ))
  have := Real.rpow_nonneg (Nat.cast_nonneg ((m : ℕ))) (-(1 / 2 : ℝ))
  positivity

theorem exp_abs_add_abs_le (u t : ℝ) :
    Real.exp (-(5 / 2 * |u|)) * Real.exp (-(5 / 2 * |u + t|)) ≤
      Real.exp (-(2 * |t|)) * Real.exp (-(1 / 2 * |u|)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : |t| ≤ |u| + |u + t| := by
    calc |t| = |(u + t) - u| := by ring_nf
      _ ≤ |u + t| + |u| := abs_sub _ _
      _ = |u| + |u + t| := by ring
  nlinarith [abs_nonneg (u + t), abs_nonneg u]

theorem norm_inner_seedAtomLine_le (n m : ℕ+) :
    ‖inner ℂ (seedAtomLine n) (seedAtomLine m)‖ ≤ seedGramBound n m := by
  rw [MeasureTheory.L2.inner_def]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : ∀ᵐ x ∂(volume : Measure ℝ),
      ‖inner ℂ ((seedAtomLine n : ℝ → ℂ) x) ((seedAtomLine m : ℝ → ℂ) x)‖ ≤
        seedTwoSidedConst ^ 2 * (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          (Real.exp (-(2 * |Real.log (n : ℕ) - Real.log (m : ℕ)|)) *
            Real.exp (-(1 / 2 * |x + Real.log (n : ℕ)|))) := by
    filter_upwards [seedAtomLine_coeFn n, seedAtomLine_coeFn m] with x h1 h2
    rw [h1, h2, RCLike.inner_apply, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hsplit : x + Real.log (m : ℕ) = (x + Real.log (n : ℕ)) + (Real.log (m : ℕ) - Real.log (n : ℕ)) := by
      ring
    have hK := seedTwoSidedConst_nonneg
    have hn := Real.rpow_nonneg (Nat.cast_nonneg ((n : ℕ))) (-(1 / 2 : ℝ))
    have hm := Real.rpow_nonneg (Nat.cast_nonneg ((m : ℕ))) (-(1 / 2 : ℝ))
    calc |seedAtomFun m x| * |seedAtomFun n x|
        ≤ (seedTwoSidedConst * ((m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(5 / 2 * |x + Real.log (m : ℕ)|))) *
          (seedTwoSidedConst * ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
            Real.exp (-(5 / 2 * |x + Real.log (n : ℕ)|))) :=
          mul_le_mul (abs_seedAtomFun_le m x) (abs_seedAtomFun_le n x) (abs_nonneg _) (by positivity)
      _ = seedTwoSidedConst ^ 2 * (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          (Real.exp (-(5 / 2 * |x + Real.log (n : ℕ)|)) *
            Real.exp (-(5 / 2 * |(x + Real.log (n : ℕ)) + (Real.log (m : ℕ) - Real.log (n : ℕ))|))) := by
          rw [← hsplit]; ring
      _ ≤ seedTwoSidedConst ^ 2 * (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
          (Real.exp (-(2 * |Real.log (m : ℕ) - Real.log (n : ℕ)|)) *
            Real.exp (-(1 / 2 * |x + Real.log (n : ℕ)|))) := by
          exact mul_le_mul_of_nonneg_left (exp_abs_add_abs_le _ _) (by positivity)
      _ = _ := by rw [abs_sub_comm]
  have hI := (integrable_exp_abs_shift (by norm_num : (0 : ℝ) < 1 / 2) (Real.log (n : ℕ))).const_mul
    (seedTwoSidedConst ^ 2 * (((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) *
      Real.exp (-(2 * |Real.log (n : ℕ) - Real.log (m : ℕ)|)))
  refine (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hI.congr
    (Eventually.of_forall fun x => by ring)) hbound).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_const_mul, integral_exp_abs_shift (by norm_num : (0 : ℝ) < 1 / 2),
    seedGramBound]
  ring

/-- The Schur weight `(nm)^{-1/2} e^{−2|log n − log m|}`. -/
def schurWeight (n m : ℕ+) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * ((m : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
    Real.exp (-(2 * |Real.log (n : ℕ) - Real.log (m : ℕ)|))

theorem schurWeight_le (n m : ℕ+) :
    schurWeight n m ≤ (if m ≤ n then 1 / ((n : ℕ) : ℝ) else ((n : ℕ) : ℝ) / ((m : ℕ) : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  have hm : (0 : ℝ) < (m : ℕ) := by exact_mod_cast m.pos
  set a := Real.log (n : ℕ)
  set b := Real.log (m : ℕ)
  have hpow : ∀ k : ℕ+, ((k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = Real.exp (-(1 / 2) * Real.log (k : ℕ)) := by
    intro k
    rw [Real.rpow_def_of_pos (by exact_mod_cast k.pos), mul_comm]
  have hw : schurWeight n m = Real.exp (-(1 / 2) * a - 1 / 2 * b - 2 * |a - b|) := by
    rw [schurWeight, hpow, hpow, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hw]
  split_ifs with h
  · have hba : b ≤ a := Real.log_le_log hm (by exact_mod_cast h)
    rw [abs_of_nonneg (by linarith), show 1 / ((n : ℕ) : ℝ) = Real.exp (-a) by
      rw [Real.exp_neg, Real.exp_log hn, one_div]]
    exact Real.exp_le_exp.2 (by linarith)
  · have hab : a < b := Real.log_lt_log hn (by exact_mod_cast (lt_of_not_ge h))
    rw [abs_of_neg (by linarith), show ((n : ℕ) : ℝ) / ((m : ℕ) : ℝ) ^ 2 = Real.exp (a - 2 * b) by
      rw [Real.exp_sub, Real.exp_log hn, show 2 * b = Real.log (((m : ℕ) : ℝ) ^ 2) by
        rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]]
    exact Real.exp_le_exp.2 (by linarith)

/-- **Schur test.**  `Σ_{m ∈ s} (nm)^{-1/2} e^{−2|log n − log m|} ≤ 3` for every finite `s`. -/
theorem sum_schurWeight_le (n : ℕ+) (s : Finset ℕ+) : ∑ m ∈ s, schurWeight n m ≤ 3 := by
  classical
  have hn : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
  refine (Finset.sum_le_sum fun m _ => schurWeight_le n m).trans ?_
  rw [Finset.sum_ite]
  have h1 : ∑ m ∈ s.filter (· ≤ n), (1 / ((n : ℕ) : ℝ)) ≤ 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (s.filter (· ≤ n)).card ≤ (n : ℕ) := by
      calc (s.filter (· ≤ n)).card = ((s.filter (· ≤ n)).map ⟨PNat.val, PNat.coe_injective⟩).card :=
            (Finset.card_map _).symm
        _ ≤ (Finset.Icc 1 (n : ℕ)).card := Finset.card_le_card fun i hi => by
            simp only [Finset.mem_map, Finset.mem_filter, Function.Embedding.coeFn_mk] at hi
            obtain ⟨m, ⟨_, hm⟩, rfl⟩ := hi
            simp only [Finset.mem_Icc]
            exact ⟨m.pos, hm⟩
        _ = (n : ℕ) := by simp
    rw [mul_one_div, div_le_one hn]
    exact_mod_cast hcard
  have h2 : ∑ m ∈ s.filter (fun m => ¬ m ≤ n), ((n : ℕ) : ℝ) / ((m : ℕ) : ℝ) ^ 2 ≤ 2 := by
    set t := s.filter (fun m => ¬ m ≤ n)
    set N := (t.sup fun m => (m : ℕ)) + 1
    have hsub : t.map ⟨PNat.val, PNat.coe_injective⟩ ⊆ Finset.Ioo (n : ℕ) N := fun i hi => by
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hi
      obtain ⟨m, hm, rfl⟩ := hi
      have hmn : ¬ m ≤ n := (Finset.mem_filter.1 hm).2
      simp only [Finset.mem_Ioo]
      refine ⟨by exact_mod_cast lt_of_not_ge hmn, Nat.lt_succ_of_le ?_⟩
      exact Finset.le_sup (f := fun m : ℕ+ => (m : ℕ)) hm
    calc ∑ m ∈ t, ((n : ℕ) : ℝ) / ((m : ℕ) : ℝ) ^ 2
        = ((n : ℕ) : ℝ) * ∑ i ∈ t.map ⟨PNat.val, PNat.coe_injective⟩, ((i : ℝ) ^ 2)⁻¹ := by
          rw [Finset.sum_map, Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          simp [div_eq_mul_inv]
      _ ≤ ((n : ℕ) : ℝ) * ∑ i ∈ Finset.Ioo (n : ℕ) N, ((i : ℝ) ^ 2)⁻¹ := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity) hn.le
      _ ≤ ((n : ℕ) : ℝ) * (2 / ((n : ℕ) + 1)) := by gcongr; exact sum_Ioo_inv_sq_le _ _
      _ ≤ 2 := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]; linarith
  linarith

theorem seedGramBound_eq (n m : ℕ+) :
    seedGramBound n m = 4 * seedTwoSidedConst ^ 2 * schurWeight n m := by
  rw [seedGramBound, schurWeight]; ring

/-- **The Gram quadratic form is bounded**: `‖Σ_{n∈s} f_n a_n‖² ≤ 12K² Σ_{n∈s} |f_n|²`. -/
theorem norm_sq_sum_seedAtomLine_le (s : Finset ℕ+) (f : ℕ+ → ℂ) :
    ‖∑ n ∈ s, f n • seedAtomLine n‖ ^ 2 ≤ 12 * seedTwoSidedConst ^ 2 * ∑ n ∈ s, ‖f n‖ ^ 2 := by
  have hinner : inner ℂ (∑ n ∈ s, f n • seedAtomLine n) (∑ m ∈ s, f m • seedAtomLine m) =
      ∑ n ∈ s, ∑ m ∈ s, (starRingEnd ℂ) (f n) * f m * inner ℂ (seedAtomLine n) (seedAtomLine m) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [inner_smul_left, inner_smul_right]; ring
  have hG := fun n m => norm_inner_seedAtomLine_le n m
  calc ‖∑ n ∈ s, f n • seedAtomLine n‖ ^ 2
      = (inner ℂ (∑ n ∈ s, f n • seedAtomLine n) (∑ m ∈ s, f m • seedAtomLine m)).re := by
        rw [inner_self_eq_norm_sq_to_K]; norm_cast
    _ ≤ ‖inner ℂ (∑ n ∈ s, f n • seedAtomLine n) (∑ m ∈ s, f m • seedAtomLine m)‖ :=
        Complex.re_le_norm _
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ‖f n‖ * ‖f m‖ * seedGramBound n m := by
        rw [hinner]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
        rw [norm_mul, norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (hG n m) (by positivity)
    _ ≤ ∑ n ∈ s, ∑ m ∈ s, ((‖f n‖ ^ 2 + ‖f m‖ ^ 2) / 2) * seedGramBound n m := by
        refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => ?_
        exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg (‖f n‖ - ‖f m‖)])
          (seedGramBound_nonneg n m)
    _ = ∑ n ∈ s, ‖f n‖ ^ 2 * ∑ m ∈ s, seedGramBound n m := by
        have hsym : ∑ n ∈ s, ∑ m ∈ s, ‖f m‖ ^ 2 / 2 * seedGramBound n m =
            ∑ n ∈ s, ∑ m ∈ s, ‖f n‖ ^ 2 / 2 * seedGramBound n m := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
          rw [seedGramBound_comm]
        have hsplit : ∑ n ∈ s, ∑ m ∈ s, ((‖f n‖ ^ 2 + ‖f m‖ ^ 2) / 2) * seedGramBound n m =
            ∑ n ∈ s, ∑ m ∈ s, ‖f n‖ ^ 2 / 2 * seedGramBound n m +
              ∑ n ∈ s, ∑ m ∈ s, ‖f m‖ ^ 2 / 2 * seedGramBound n m := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
        rw [hsplit, hsym, ← two_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ ∑ n ∈ s, ‖f n‖ ^ 2 * (12 * seedTwoSidedConst ^ 2) := by
        refine Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        simp_rw [seedGramBound_eq, ← Finset.mul_sum]
        have := sum_schurWeight_le n s
        have hK := sq_nonneg seedTwoSidedConst
        nlinarith
    _ = 12 * seedTwoSidedConst ^ 2 * ∑ n ∈ s, ‖f n‖ ^ 2 := by
        rw [← Finset.sum_mul, mul_comm]

theorem norm_sq_lp_pnat (f : ℓ²₊) : ‖f‖ ^ 2 = ∑' n, ‖(f : ℕ+ → ℂ) n‖ ^ 2 := by
  have h : ‖f‖ ^ (2 : ℝ) = ∑' n : ℕ+, ‖(f : ℕ+ → ℂ) n‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℕ+ => ℂ) (by norm_num) f
  simpa only [Real.rpow_two] using h

/-- The Gram constant `12 K²`. -/
def seedLineConst : ℝ := 12 * seedTwoSidedConst ^ 2

theorem seedLineConst_nonneg : 0 ≤ seedLineConst := by unfold seedLineConst; positivity

theorem norm_sum_seedAtomLine_le (s : Finset ℕ+) (f : ℓ²₊) :
    ‖∑ n ∈ s, (f : ℕ+ → ℂ) n • seedAtomLine n‖ ≤ Real.sqrt seedLineConst * ‖f‖ := by
  have h1 := norm_sq_sum_seedAtomLine_le s (f : ℕ+ → ℂ)
  have h2 : ∑ n ∈ s, ‖(f : ℕ+ → ℂ) n‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [norm_sq_lp_pnat]
    exact Summable.sum_le_tsum s (fun _ _ => sq_nonneg _) (GaloisForLFunctions.HTGeometry.summable_norm_sq_lp f)
  have h3 : ‖∑ n ∈ s, (f : ℕ+ → ℂ) n • seedAtomLine n‖ ^ 2 ≤ (Real.sqrt seedLineConst * ‖f‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt seedLineConst_nonneg]
    exact h1.trans (mul_le_mul_of_nonneg_left h2 seedLineConst_nonneg)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3

theorem summable_smul_seedAtomLine (f : ℓ²₊) :
    Summable fun n => (f : ℕ+ → ℂ) n • seedAtomLine n := by
  rw [summable_iff_vanishing_norm]
  intro ε hε
  have hs := GaloisForLFunctions.HTGeometry.summable_norm_sq_lp f
  rw [summable_iff_vanishing_norm] at hs
  obtain ⟨s₀, hs₀⟩ := hs (ε ^ 2 / (seedLineConst + 1)) (by
    have := seedLineConst_nonneg; positivity)
  refine ⟨s₀, fun t ht => ?_⟩
  have h1 := norm_sq_sum_seedAtomLine_le t (f : ℕ+ → ℂ)
  have h2 := hs₀ t ht
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
  have hC := seedLineConst_nonneg
  have h3 : ‖∑ n ∈ t, (f : ℕ+ → ℂ) n • seedAtomLine n‖ ^ 2 < ε ^ 2 := by
    calc ‖∑ n ∈ t, (f : ℕ+ → ℂ) n • seedAtomLine n‖ ^ 2
        ≤ seedLineConst * ∑ n ∈ t, ‖(f : ℕ+ → ℂ) n‖ ^ 2 := h1
      _ ≤ seedLineConst * (ε ^ 2 / (seedLineConst + 1)) := mul_le_mul_of_nonneg_left h2.le hC
      _ < ε ^ 2 := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith [sq_pos_of_pos hε]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 h3

/-- **The full-line synthesis is bounded on `H`**: `C_ℝ f = Σ_n f(n) n^{-1/2} h(· + log n)` in
`L²(ℝ)`, with `‖C_ℝ‖ ≤ √(12) K` (Gram matrix Schur test). -/
def seedLineSynthesis : ℓ²₊ →L[ℂ] L²ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∑' n, (f : ℕ+ → ℂ) n • seedAtomLine n
      map_add' := fun f g => by
        simp only [lp.coeFn_add, Pi.add_apply, add_smul]
        exact (summable_smul_seedAtomLine f).tsum_add (summable_smul_seedAtomLine g)
      map_smul' := fun c f => by
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (summable_smul_seedAtomLine f).tsum_const_smul c }
    (Real.sqrt seedLineConst) fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      have hlim := (summable_smul_seedAtomLine f).hasSum.norm
      exact le_of_tendsto' hlim fun s => norm_sum_seedAtomLine_le s f

theorem seedLineSynthesis_single (n : ℕ+) :
    seedLineSynthesis (lp.single 2 n (1 : ℂ)) = seedAtomLine n := by
  classical
  change ∑' m, ((lp.single 2 n (1 : ℂ) : ℓ²₊) : ℕ+ → ℂ) m • seedAtomLine m = _
  rw [tsum_eq_single n fun m hm => by rw [lp.single_apply, Pi.single_eq_of_ne hm, zero_smul]]
  rw [lp.single_apply, Pi.single_eq_same, one_smul]

theorem halfLineRestrict_seedAtomLine (n : ℕ+) : halfLineRestrict (seedAtomLine n) = seedAtomLp n := by
  refine Lp.ext ?_
  filter_upwards [halfLineRestrict_coeFn (seedAtomLine n), ae_restrict_of_ae (seedAtomLine_coeFn n),
    seedAtomLp_coeFn n] with x h1 h2 h3
  rw [h1, h2, h3]

/-- The zero extension of a half-line vector pairs with the full-line atoms as with the half-line
ones. -/
theorem inner_halfLineExtend_seedAtomLine (g : L²₊) (n : ℕ+) :
    inner ℂ (halfLineExtend g) (seedAtomLine n) = inner ℂ g (seedAtomLp n) := by
  rw [← ContinuousLinearMap.adjoint_inner_right, GaloisForLFunctions.HTGeometry.adjoint_halfLineExtend,
    halfLineRestrict_seedAtomLine]

/-- **The separator extended by zero separates the full-line atoms.** -/
theorem exists_seed_vacuum_separator_line :
    ∃ g : L²₊, (∀ n : ℕ+, n ≠ 1 →
        inner ℂ (halfLineExtend g) (seedLineSynthesis (lp.single 2 n (1 : ℂ))) = 0) ∧
      inner ℂ (halfLineExtend g) (seedLineSynthesis (lp.single 2 1 (1 : ℂ))) ≠ 0 := by
  obtain ⟨g, hg, hne⟩ := exists_seed_vacuum_separator
  refine ⟨g, fun n hn => ?_, ?_⟩
  · rw [seedLineSynthesis_single, inner_halfLineExtend_seedAtomLine, ← seedSynthesis_single]
    exact hg n hn
  · rw [seedLineSynthesis_single, inner_halfLineExtend_seedAtomLine, ← seedSynthesis_single]
    exact hne

end

end RHTower
