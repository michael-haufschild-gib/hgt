import GaloisForLFunctions.ZeroConfigurationGeometry.TheOneOffsAreFiniteOscillationsOfThePrimeError
import GaloisForLFunctions.ZeroConfigurationGeometry.AsymptoticAbscissaSpectralGapAndTopAnnihilator
import GaloisForLFunctions.RHTower.GelfondSchneider
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Multiplicative Dilation Annihilation of a Finite Prime-Error Oscillation

To any polynomial `P ∈ ℝ[X]` and scale `b > 0` we associate the multiplicative dilation operator

`(dilationPolyOp b P f)(x) = ∑_{k=0}^{deg P} P_k f(x / b^k)`.

For a finite frequency set `S ⊂ ℝ` and abscissa `β ∈ ℝ`, let
`dilationPairPoly b β ω (X) = 1 − 2 b^β cos(ω log b) X + b^{2β} X²` and
`dilationSetPoly b β S = ∏_{ω ∈ S} dilationPairPoly b β ω`.

This module proves four unconditional theorems connecting `x`-space Chebyshev dilations to the
asymptotic abscissa law:

1. **Exact `x`-space top-oscillation annihilation and linear main-term survival**
   (`dilationSetOp_rpow_mul_finiteOscillation_eq_zero`, `dilationSetOp_id_eq`,
   `mainTermFactor_pos`, `abs_dilationSetOp_psi_sub_mainTerm_le`):
   For every `b > 1` and `x > 0`, `dilationSetOp b β S` annihilates
   `y ↦ y^β finiteOscillation S c (log y)` identically while multiplying `y ↦ y` by
   `mainTermFactor b β S = (dilationSetPoly b β S).eval b⁻¹ ≥ (1 − b^{β−1})^{2|S|} > 0` (`β < 1`),
   collapsing any finite-oscillation prime error to `dilationSetOp b β S ψ (x) = κ_b x + O(x^{β−η})`.

2. **Exact Mellin clearing identity without boundary terms**
   (`integral_Ioi_one_psi_div_mul_cpow`, `mul_mellin_dilationRemainder`,
   `neg_dilationSymbol_mul_deriv_zetaResidueUnit_eq`):
   Because `ψ(u) = 0` on `(0, 1]`, rescaling `t = b^k u` on `(1, ∞)` produces zero boundary error at
   `1`. Clearing the `s = 1` simple pole via `dslope` yields a holomorphic identity for
   `zetaResidueUnit` across `{Re s > σ₀}` even when `σ₀ < 1`.

3. **Single-base periodic ordinate pinning**
   (`dilationSymbol_eq_zero_of_zeta_eq_zero`, `re_eq_and_im_mem_periodic_of_dilation_bound`):
   Any bound `|dilationSetOp b β S ψ (x) − mainTermFactor b β S · x| ≤ C x^{σ₀}` (`b > 1`) confines
   every zero `ρ ≠ 1` of `ζ` in `{Re s > σ₀}` to the single vertical line `Re ρ = β` and the union
   of arithmetic progressions `α + (2π / log b)ℤ` (`α ∈ S ∪ (−S)`).

4. **Two-prime incommensurable dilation equivalence**
   (`finite_zeta_zeros_of_twoPrime_dilation_bound`,
   `not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation`):
   For any distinct primes `p ≠ q`, irrationality of `log q / log p` restricts each pair of periodic
   ordinate lattices to at most one common point, giving an exact characterization of
   `¬ AsymptoticAbscissaLaw` (`PrimeErrorIsFiniteOscillation`) purely by `O(x^{β−η})` dilation
   collapse of `ψ` at bases `p` and `q`.
-/

open Complex Filter Topology MeasureTheory Set
open ArithmeticFunction (vonMangoldt)
open RHTower

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-! ### 1. Polynomial multiplicative dilation operators and exact `x`-space annihilation -/

/-- The `x`-space multiplicative dilation operator `(dilationPolyOp b P f)(x) = ∑_k P_k f(x / b^k)`. -/
def dilationPolyOp (b : ℝ) (P : Polynomial ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * f (x / b ^ k)

/-- Complex extension `(dilationPolyOpC b P F)(x) = ∑_k P_k F(x / b^k)`. -/
def dilationPolyOpC (b : ℝ) (P : Polynomial ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k : ℂ) * F (x / b ^ k)

/-- Conjugate-pair dilation polynomial `1 − 2 b^β cos(ω log b) X + b^{2β} X²`. -/
def dilationPairPoly (b β ω : ℝ) : Polynomial ℝ :=
  1 - Polynomial.C (2 * b ^ β * Real.cos (ω * Real.log b)) * Polynomial.X +
    Polynomial.C (b ^ (2 * β)) * Polynomial.X ^ 2

/-- Finite-layer dilation polynomial `∏_{ω ∈ S} dilationPairPoly b β ω`. -/
def dilationSetPoly (b β : ℝ) (S : Finset ℝ) : Polynomial ℝ :=
  ∏ ω ∈ S, dilationPairPoly b β ω

/-- Finite-layer multiplicative dilation operator on `ℝ → ℝ`. -/
def dilationSetOp (b β : ℝ) (S : Finset ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  dilationPolyOp b (dilationSetPoly b β S) f x

/-- Linear PNT main-term survival factor `(dilationSetPoly b β S).eval b⁻¹`. -/
def mainTermFactor (b β : ℝ) (S : Finset ℝ) : ℝ :=
  (dilationSetPoly b β S).eval b⁻¹

/-- Complex Dirichlet-polynomial symbol `D(s) = P(b^{−s})`. -/
def dilationSymbol (b : ℝ) (P : Polynomial ℝ) (s : ℂ) : ℂ :=
  P.eval₂ (algebraMap ℝ ℂ) ((b : ℂ) ^ (-s))

theorem dilationPolyOpC_ofReal (b : ℝ) (P : Polynomial ℝ) (f : ℝ → ℝ) (x : ℝ) :
    dilationPolyOpC b P (fun y => (f y : ℂ)) x = (dilationPolyOp b P f x : ℂ) := by
  simp [dilationPolyOpC, dilationPolyOp]

theorem dilationPolyOp_sub (b : ℝ) (P : Polynomial ℝ) (f g : ℝ → ℝ) (x : ℝ) :
    dilationPolyOp b P (fun y => f y - g y) x =
      dilationPolyOp b P f x - dilationPolyOp b P g x := by
  simp only [dilationPolyOp, mul_sub, Finset.sum_sub_distrib]

/-- Action of `dilationPolyOp b P` on the linear function `y ↦ y`. -/
theorem dilationPolyOp_id_eq (b : ℝ) (P : Polynomial ℝ) (x : ℝ) :
    dilationPolyOp b P id x = P.eval b⁻¹ * x := by
  rw [dilationPolyOp, Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [id_eq, div_eq_mul_inv, inv_pow]
  ring

/-- Action of `dilationSetOp b β S` on `y ↦ y`. -/
theorem dilationSetOp_id_eq (b β : ℝ) (S : Finset ℝ) (x : ℝ) :
    dilationSetOp b β S id x = mainTermFactor b β S * x :=
  dilationPolyOp_id_eq b (dilationSetPoly b β S) x

/-- Action of `dilationPolyOpC b P` on `y ↦ (y : ℂ)^s` (`b > 0`, `x > 0`). -/
theorem dilationPolyOpC_cpow_eq {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (P : Polynomial ℝ) (s : ℂ) :
    dilationPolyOpC b P (fun y => (y : ℂ) ^ s) x = dilationSymbol b P s * (x : ℂ) ^ s := by
  rw [dilationPolyOpC, dilationSymbol, Polynomial.eval₂_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hbk_pos : 0 < b ^ k := pow_pos hb k
  have hdiv_pos : 0 < x / b ^ k := div_pos hx hbk_pos
  have hdiv0 : ((x / b ^ k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdiv_pos.ne'
  have hpow_eq : ((x / b ^ k : ℝ) : ℂ) ^ s = ((b : ℂ) ^ (-s)) ^ k * (x : ℂ) ^ s := by
    rw [Complex.cpow_def_of_ne_zero hdiv0, Complex.cpow_def_of_ne_zero hb0,
      Complex.cpow_def_of_ne_zero hx0, ← Complex.ofReal_log hdiv_pos.le,
      ← Complex.ofReal_log hb.le, ← Complex.ofReal_log hx.le,
      Real.log_div hx.ne' hbk_pos.ne', Real.log_pow, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hpow_eq]
  simp only [RCLike.algebraMap_eq_ofReal]
  ring

/-- Complex factorization of `dilationPairPoly b β ω` at `z ∈ ℂ` (`b > 0`). -/
theorem eval₂_dilationPairPoly_eq {b : ℝ} (hb : 0 < b) (β ω : ℝ) (z : ℂ) :
    (dilationPairPoly b β ω).eval₂ (algebraMap ℝ ℂ) z =
      (1 - ((b ^ β : ℝ) : ℂ) * cexp (I * ω * Real.log b) * z) *
        (1 - ((b ^ β : ℝ) : ℂ) * cexp (-I * ω * Real.log b) * z) := by
  have hexp_mul : cexp (I * ω * Real.log b) * cexp (-I * ω * Real.log b) = 1 := by
    rw [← Complex.exp_add]
    have : I * (ω : ℂ) * (Real.log b : ℂ) + -I * (ω : ℂ) * (Real.log b : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero]
  have hexp_add : cexp (I * ω * Real.log b) + cexp (-I * ω * Real.log b) =
      2 * (Real.cos (ω * Real.log b) : ℂ) := by
    rw [Complex.ofReal_cos, Complex.cos]
    have h1 : (ω * Real.log b : ℂ) * I = I * ω * Real.log b := by push_cast; ring
    have h2 : -((ω * Real.log b : ℂ) * I) = -I * ω * Real.log b := by push_cast; ring
    rw [h1, h2]
    ring
  have hb2 : (((b ^ β : ℝ) : ℂ)) ^ 2 = ((b ^ (2 * β) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast (b ^ β) 2, ← Real.rpow_mul hb.le]
    congr 2
    ring
  simp only [dilationPairPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_one,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow,
    RCLike.algebraMap_eq_ofReal]
  push_cast
  calc (1 : ℂ) - 2 * ((b ^ β : ℝ) : ℂ) * (Real.cos (ω * Real.log b) : ℂ) * z +
        ((b ^ (2 * β) : ℝ) : ℂ) * z ^ 2
      = 1 - ((b ^ β : ℝ) : ℂ) * (cexp (I * ω * Real.log b) + cexp (-I * ω * Real.log b)) * z +
          (((b ^ β : ℝ) : ℂ)) ^ 2 *
            (cexp (I * ω * Real.log b) * cexp (-I * ω * Real.log b)) * z ^ 2 := by
        rw [hexp_add, hexp_mul, hb2]
        ring
    _ = (1 - ((b ^ β : ℝ) : ℂ) * cexp (I * ω * Real.log b) * z) *
          (1 - ((b ^ β : ℝ) : ℂ) * cexp (-I * ω * Real.log b) * z) := by ring

/-- Spectral factorization of `dilationSymbol b (dilationSetPoly b β S) s` (`b > 0`). -/
theorem dilationSymbol_dilationSetPoly_eq {b : ℝ} (hb : 0 < b) (β : ℝ) (S : Finset ℝ) (s : ℂ) :
    dilationSymbol b (dilationSetPoly b β S) s =
      ∏ ω ∈ S,
        (1 - (b : ℂ) ^ (((β : ℂ) + I * ω) - s)) *
          (1 - (b : ℂ) ^ (((β : ℂ) - I * ω) - s)) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [dilationSymbol, dilationSetPoly, Polynomial.eval₂_finsetProd]
  refine Finset.prod_congr rfl fun ω _ => ?_
  rw [eval₂_dilationPairPoly_eq hb]
  have hfactor : ∀ sgn : ℂ, sgn = 1 ∨ sgn = -1 →
      ((b ^ β : ℝ) : ℂ) * cexp (sgn * I * ω * Real.log b) * (b : ℂ) ^ (-s) =
        (b : ℂ) ^ (((β : ℂ) + sgn * I * ω) - s) := by
    intro sgn _
    rw [← Complex.ofReal_cpow hb.le, Complex.cpow_def_of_ne_zero hb0,
      Complex.cpow_def_of_ne_zero hb0, Complex.cpow_def_of_ne_zero hb0,
      ← Complex.ofReal_log hb.le, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hpos := hfactor 1 (Or.inl rfl)
  have hneg := hfactor (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at hpos hneg
  rw [hpos, show (β : ℂ) + -(I * ↑ω) - s = (β : ℂ) - I * ↑ω - s by ring] at hneg ⊢
  rw [hneg]

/-- `dilationSymbol b (dilationSetPoly b β S)` vanishes at `β + iμ` for every `μ ∈ S ∪ (−S)`. -/
theorem dilationSymbol_dilationSetPoly_eq_zero_of_mem {b : ℝ} (hb : 0 < b) (β : ℝ) (S : Finset ℝ)
    {μ : ℝ} (hμ : μ ∈ oscillationFrequencies S) :
    dilationSymbol b (dilationSetPoly b β S) ((β : ℂ) + I * μ) = 0 := by
  rw [dilationSymbol_dilationSetPoly_eq hb]
  rcases Finset.mem_union.mp hμ with hS | hnegS
  · refine Finset.prod_eq_zero hS ?_
    rw [sub_self, Complex.cpow_zero, sub_self, zero_mul]
  · obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hnegS
    refine Finset.prod_eq_zero hω ?_
    have : (β : ℂ) - I * (ω : ℂ) - ((β : ℂ) + I * ((-ω : ℝ) : ℂ)) = 0 := by push_cast; ring
    rw [this, Complex.cpow_zero, sub_self, mul_zero]

/-- **Exact `x`-space top-oscillation annihilation.** For every `b > 0` and `x > 0`,
`dilationSetOp b β S` identically annihilates `y ↦ y^β finiteOscillation S c (log y)`. -/
theorem dilationSetOp_rpow_mul_finiteOscillation_eq_zero {b : ℝ} (hb : 0 < b) (β : ℝ)
    (S : Finset ℝ) (c : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    dilationSetOp b β S (fun y => y ^ β * finiteOscillation S c (Real.log y)) x = 0 := by
  suffices hC : (dilationSetOp b β S
      (fun y => y ^ β * finiteOscillation S c (Real.log y)) x : ℂ) = 0 from
    Complex.ofReal_eq_zero.mp hC
  rw [dilationSetOp, ← dilationPolyOpC_ofReal]
  set P := dilationSetPoly b β S
  have hpt : ∀ k : ℕ, ((P.coeff k : ℂ) *
      (((x / b ^ k) ^ β * finiteOscillation S c (Real.log (x / b ^ k)) : ℝ) : ℂ)) =
      ∑ μ ∈ oscillationFrequencies S,
        oscillationCoeff S c μ *
          ((P.coeff k : ℂ) * ((x / b ^ k : ℝ) : ℂ) ^ ((β : ℂ) + I * μ)) := by
    intro k
    have hdiv_pos : 0 < x / b ^ k := div_pos hx (pow_pos hb k)
    rw [Complex.ofReal_mul, finiteOscillation_eq_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [cpow_add_I_mul_eq hdiv_pos]
    ring
  rw [dilationPolyOpC, Finset.sum_congr rfl fun k _ => hpt k, Finset.sum_comm]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  rw [← Finset.mul_sum]
  change oscillationCoeff S c μ *
      dilationPolyOpC b P (fun y => (y : ℂ) ^ ((β : ℂ) + I * μ)) x = 0
  rw [dilationPolyOpC_cpow_eq hb hx, dilationSymbol_dilationSetPoly_eq_zero_of_mem hb β S hμ,
    zero_mul, mul_zero]

/-- **Strict positivity of the linear PNT main-term factor** (`b > 1`, `β < 1`). -/
theorem mainTermFactor_ge_pos {b β : ℝ} (hb : 1 < b) (hβ : β < 1) (S : Finset ℝ) :
    (1 - b ^ (β - 1)) ^ (2 * S.card) ≤ mainTermFactor b β S ∧ 0 < mainTermFactor b β S := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hr_lt : b ^ (β - 1) < 1 := by
    calc b ^ (β - 1) < b ^ (0 : ℝ) := Real.rpow_lt_rpow_of_exponent_lt hb (by linarith)
      _ = 1 := Real.rpow_zero b
  have hr_pos : 0 < b ^ (β - 1) := Real.rpow_pos_of_pos hb0 _
  have h1r_pos : 0 < 1 - b ^ (β - 1) := by linarith
  have hfactor_ge : ∀ ω ∈ S, (1 - b ^ (β - 1)) ^ 2 ≤ (dilationPairPoly b β ω).eval b⁻¹ := by
    intro ω _
    simp only [dilationPairPoly, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_one,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    have h1 : b ^ β * b⁻¹ = b ^ (β - 1) := by
      rw [← Real.rpow_neg_one b, ← Real.rpow_add hb0]
      congr 1
      ring
    have h2 : b ^ (2 * β) * b⁻¹ ^ 2 = (b ^ (β - 1)) ^ 2 := by
      rw [← Real.rpow_natCast (b ^ (β - 1)) 2, ← Real.rpow_mul hb0.le, inv_pow,
        ← Real.rpow_natCast b 2, ← Real.rpow_neg hb0.le, ← Real.rpow_add hb0]
      congr 1
      push_cast
      ring
    have hcos : Real.cos (ω * Real.log b) ≤ 1 := Real.cos_le_one _
    have rearr : 1 - 2 * b ^ β * Real.cos (ω * Real.log b) * b⁻¹ + b ^ (2 * β) * b⁻¹ ^ 2 =
        1 - 2 * (b ^ β * b⁻¹) * Real.cos (ω * Real.log b) + b ^ (2 * β) * b⁻¹ ^ 2 := by ring
    rw [rearr, h1, h2]
    nlinarith
  have hle : (1 - b ^ (β - 1)) ^ (2 * S.card) ≤ mainTermFactor b β S := by
    rw [mainTermFactor, dilationSetPoly, Polynomial.eval_prod, pow_mul, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => sq_nonneg _) hfactor_ge
  exact ⟨hle, lt_of_lt_of_le (pow_pos h1r_pos _) hle⟩

/-- **Forward `x`-space collapse.** Any finite-oscillation bound
`|ψ(x) − x − x^β T(log x)| ≤ C x^{σ₀}` (`b ≥ 1`) collapses under `dilationSetOp b β S` to the pure
linear main term `mainTermFactor b β S · x + O(x^{σ₀})`. -/
theorem abs_dilationSetOp_psi_sub_mainTerm_le {b β σ₀ C x₀ : ℝ} (hb : 1 ≤ b) {S : Finset ℝ}
    {c : ℝ → ℂ} (hC : ∀ x, x₀ ≤ x →
      |Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x)| ≤ C * x ^ σ₀) :
    ∃ C_b x_b : ℝ, ∀ x, x_b ≤ x →
      |dilationSetOp b β S Chebyshev.psi x - mainTermFactor b β S * x| ≤ C_b * x ^ σ₀ := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  set P := dilationSetPoly b β S
  set D : ℕ := P.natDegree
  set C_b : ℝ := ∑ k ∈ Finset.range (D + 1), |P.coeff k| * |C| * (b ^ k) ^ (-σ₀)
  refine ⟨C_b, b ^ D * max x₀ 1, fun x hx => ?_⟩
  have hbD_pos : 0 < b ^ D := pow_pos hb0 D
  have hx_pos : 0 < x := lt_of_lt_of_le (mul_pos hbD_pos (by positivity)) hx
  set err : ℝ → ℝ := fun y => Chebyshev.psi y - y - y ^ β * finiteOscillation S c (Real.log y)
  have hdecomp : dilationSetOp b β S Chebyshev.psi x - mainTermFactor b β S * x =
      dilationPolyOp b P err x := by
    have h1 := dilationPolyOp_sub b P Chebyshev.psi
      (fun y => y + y ^ β * finiteOscillation S c (Real.log y)) x
    have h2 : dilationPolyOp b P (fun y => y + y ^ β * finiteOscillation S c (Real.log y)) x =
        dilationSetOp b β S id x +
          dilationSetOp b β S (fun y => y ^ β * finiteOscillation S c (Real.log y)) x := by
      simp only [dilationSetOp, dilationPolyOp, id_eq, mul_add, Finset.sum_add_distrib]
    rw [dilationSetOp_id_eq, dilationSetOp_rpow_mul_finiteOscillation_eq_zero hb0 β S c hx_pos,
      add_zero] at h2
    change dilationPolyOp b P Chebyshev.psi x - mainTermFactor b β S * x = _
    rw [← h2, ← h1]
    simp only [dilationPolyOp, err]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hdecomp, dilationPolyOp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k hk => ?_
  have hkD : k ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hbk_le : b ^ k ≤ b ^ D := pow_le_pow_right₀ hb hkD
  have hbk_pos : 0 < b ^ k := pow_pos hb0 k
  have hy_ge : max x₀ 1 ≤ x / b ^ k := by
    rw [le_div_iff₀ hbk_pos]
    calc max x₀ 1 * b ^ k ≤ max x₀ 1 * b ^ D :=
          mul_le_mul_of_nonneg_left hbk_le (by positivity)
      _ = b ^ D * max x₀ 1 := mul_comm _ _
      _ ≤ x := hx
  have herr_k : |err (x / b ^ k)| ≤ |C| * (x / b ^ k) ^ σ₀ :=
    (hC _ ((le_max_left _ _).trans hy_ge)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (div_pos hx_pos hbk_pos).le _))
  have hrpow : (x / b ^ k) ^ σ₀ = (b ^ k) ^ (-σ₀) * x ^ σ₀ := by
    rw [div_eq_mul_inv, Real.mul_rpow hx_pos.le (inv_nonneg.mpr hbk_pos.le),
      Real.inv_rpow hbk_pos.le, ← Real.rpow_neg hbk_pos.le]
    ring
  rw [abs_mul]
  calc |P.coeff k| * |err (x / b ^ k)|
      ≤ |P.coeff k| * (|C| * (x / b ^ k) ^ σ₀) :=
        mul_le_mul_of_nonneg_left herr_k (abs_nonneg _)
    _ = |P.coeff k| * |C| * (b ^ k) ^ (-σ₀) * x ^ σ₀ := by rw [hrpow]; ring

/-! ### 2. Exact Mellin clearing identity without boundary terms -/

/-- The dilated Chebyshev remainder cut off to `(1, ∞)`. -/
def dilationRemainder (b : ℝ) (P : Polynomial ℝ) : ℝ → ℂ :=
  (Ioi (1 : ℝ)).indicator fun x =>
    ((dilationPolyOp b P Chebyshev.psi x - P.eval b⁻¹ * x : ℝ) : ℂ)

theorem locallyIntegrableOn_dilationRemainder {b : ℝ} (hb : 0 < b) (P : Polynomial ℝ) :
    LocallyIntegrableOn (dilationRemainder b P) (Ioi 0) := by
  have hpsi_k : ∀ k : ℕ, LocallyIntegrableOn
      (fun x : ℝ => ((P.coeff k * Chebyshev.psi (x / b ^ k) : ℝ) : ℂ)) (Ioi 0) := by
    intro k
    have hbk : 0 < b ^ k := pow_pos hb k
    have hmono : Monotone fun x : ℝ => Chebyshev.psi (x / b ^ k) :=
      fun _ _ hxy => Chebyshev.psi_mono (div_le_div_of_nonneg_right hxy hbk.le)
    have hloc : LocallyIntegrableOn (fun x : ℝ => Chebyshev.psi (x / b ^ k)) (Ioi 0) :=
      (hmono.locallyIntegrable (μ := volume)).locallyIntegrableOn _
    have hlocC : LocallyIntegrableOn (fun x : ℝ => (Chebyshev.psi (x / b ^ k) : ℂ)) (Ioi 0) :=
      hloc.mono (Complex.measurable_ofReal.comp hmono.measurable).aestronglyMeasurable
        (ae_of_all _ fun x => by simp)
    simpa [Complex.ofReal_mul] using hlocC.const_mul (P.coeff k : ℂ)
  have hsum : LocallyIntegrableOn
      (fun x : ℝ => ∑ k ∈ Finset.range (P.natDegree + 1),
        ((P.coeff k * Chebyshev.psi (x / b ^ k) : ℝ) : ℂ)) (Ioi 0) := by
    classical
    induction Finset.range (P.natDegree + 1) using Finset.induction_on with
    | empty => simpa using locallyIntegrableOn_const (0 : ℂ)
    | insert k s hks ih =>
      simpa only [Finset.sum_insert hks] using (hpsi_k k).add ih
  have hlin : LocallyIntegrableOn (fun x : ℝ => ((P.eval b⁻¹ * x : ℝ) : ℂ)) (Ioi 0) :=
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).continuousOn
      ).locallyIntegrableOn measurableSet_Ioi
  have herr : LocallyIntegrableOn
      (fun x : ℝ => ((dilationPolyOp b P Chebyshev.psi x - P.eval b⁻¹ * x : ℝ) : ℂ)) (Ioi 0) :=
    (hsum.sub hlin).congr (ae_of_all _ fun x => by simp [dilationPolyOp])
  intro x hx
  rcases herr x hx with ⟨t, ht, hint⟩
  exact ⟨t, ht, hint.indicator measurableSet_Ioi⟩

/-- Rescaling identity on `(1, ∞)`: for `c ≥ 1` and `Re s > 1`,
`∫_1^∞ ψ(t / c) t^{−(s+1)} dt = c^{−s} ∫_1^∞ ψ(u) u^{−(s+1)} du` with zero boundary term at `1`,
because `ψ(u) = 0` for `u ≤ 1 < 2`. -/
theorem integral_Ioi_one_psi_div_mul_cpow {c : ℝ} (hc : 1 ≤ c) {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (1 : ℝ), (Chebyshev.psi (t / c) : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      (c : ℂ) ^ (-s) *
        ∫ u in Ioi (1 : ℝ), (Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hcinv_pos : 0 < c⁻¹ := inv_pos.mpr hc0
  have hcinv_le : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc
  set g : ℝ → ℂ := fun u => (Chebyshev.psi u : ℂ) * ((c * u : ℝ) : ℂ) ^ (-(s + 1))
  have hpt_div : ∀ t ∈ Ioi (1 : ℝ),
      (Chebyshev.psi (t / c) : ℂ) * (t : ℂ) ^ (-(s + 1)) = g (c⁻¹ * t) := by
    intro t _
    simp only [g, div_eq_mul_inv]
    rw [mul_comm t c⁻¹, ← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt_div,
    MeasureTheory.integral_comp_mul_left_Ioi g 1 hcinv_pos, inv_inv, mul_one]
  have hind : (Ioi c⁻¹).indicator g = (Ioi (1 : ℝ)).indicator g := by
    funext u
    by_cases hu1 : (1 : ℝ) < u
    · have huc : c⁻¹ < u := hcinv_le.trans_lt hu1
      simp [Set.indicator_of_mem hu1, Set.indicator_of_mem huc]
    · rw [Set.indicator_of_notMem hu1]
      by_cases huc : c⁻¹ < u
      · rw [Set.indicator_of_mem huc]
        have hu_lt2 : u < 2 := by linarith
        have hfloor : ⌊u⌋₊ ≤ 1 := by
          by_contra hgt
          have h2 : (2 : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast (show 2 ≤ ⌊u⌋₊ by omega)
          have hle : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (lt_trans hcinv_pos huc).le
          linarith
        have hpsi0 : Chebyshev.psi u = 0 := by
          rw [Chebyshev.psi_eq_sum_Icc]
          refine Finset.sum_eq_zero fun n hn => ?_
          have hn1 : n = 1 := by
            have := Finset.mem_Icc.mp hn
            omega
          simp [hn1]
        simp [g, hpsi0]
      · rw [Set.indicator_of_notMem huc]
  have htrim : (∫ u in Ioi c⁻¹, g u) = ∫ u in Ioi (1 : ℝ), g u := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi, hind,
      MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [htrim]
  have hfactor : ∀ u ∈ Ioi (1 : ℝ),
      g u = (c : ℂ) ^ (-(s + 1)) * ((Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-(s + 1))) := by
    intro u hu
    have hu0 : 0 < u := zero_lt_one.trans hu
    simp only [g]
    rw [Complex.ofReal_mul c u, Complex.mul_cpow_ofReal_nonneg hc0.le hu0.le]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfactor, MeasureTheory.integral_const_mul,
    Complex.real_smul, ← mul_assoc]
  congr 1
  have hcC0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have h1 : (c : ℂ) = (c : ℂ) ^ (1 : ℂ) := (Complex.cpow_one _).symm
  calc (c : ℂ) * (c : ℂ) ^ (-(s + 1))
      = (c : ℂ) ^ (1 : ℂ) * (c : ℂ) ^ (-(s + 1)) := by rw [← h1]
    _ = (c : ℂ) ^ ((1 : ℂ) + -(s + 1)) := (Complex.cpow_add _ _ hcC0).symm
    _ = (c : ℂ) ^ (-s) := by congr 1; ring

theorem integrableOn_psi_div_mul_cpow {c : ℝ} (hc : 1 ≤ c) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (Chebyshev.psi (t / c) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hbase : IntegrableOn
      (fun u : ℝ => (Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    refine (integrableOn_criticalCumulative_mul_cpow hs).congr_fun (fun u _ => ?_) measurableSet_Ioi
    rw [criticalCumulative_vonMangoldt_eq_psi]
  have hscaled : IntegrableOn
      (fun u : ℝ => (Chebyshev.psi u : ℂ) * ((c * u : ℝ) : ℂ) ^ (-(s + 1))) (Ioi c⁻¹) := by
    have hmul : IntegrableOn
        (fun u : ℝ => (c : ℂ) ^ (-(s + 1)) * ((Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-(s + 1))))
        (Ioi 1) := hbase.const_mul _
    rw [← MeasureTheory.integrable_indicator_iff measurableSet_Ioi] at hmul ⊢
    refine hmul.congr (ae_of_all _ fun u => ?_)
    by_cases hu1 : (1 : ℝ) < u
    · have huc : c⁻¹ < u := (inv_le_one_of_one_le₀ hc).trans_lt hu1
      have hu0 : 0 < u := zero_lt_one.trans hu1
      simp only [Set.indicator_of_mem hu1, Set.indicator_of_mem huc]
      rw [Complex.ofReal_mul c u, Complex.mul_cpow_ofReal_nonneg hc0.le hu0.le]
      ring
    · rw [Set.indicator_of_notMem hu1]
      by_cases huc : c⁻¹ < u
      · rw [Set.indicator_of_mem huc]
        have hfloor : ⌊u⌋₊ ≤ 1 := by
          by_contra hgt
          have h2 : (2 : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast (show 2 ≤ ⌊u⌋₊ by omega)
          have hle : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (lt_trans (inv_pos.mpr hc0) huc).le
          linarith
        have hpsi0 : Chebyshev.psi u = 0 := by
          rw [Chebyshev.psi_eq_sum_Icc]
          refine Finset.sum_eq_zero fun n hn => ?_
          have hn1 : n = 1 := by have := Finset.mem_Icc.mp hn; omega
          simp [hn1]
        simp [hpsi0]
      · rw [Set.indicator_of_notMem huc]
  have hcomp : IntegrableOn
      (fun t : ℝ => (Chebyshev.psi (c⁻¹ * t) : ℂ) * ((c * (c⁻¹ * t) : ℝ) : ℂ) ^ (-(s + 1)))
      (Ioi 1) := by
    rw [MeasureTheory.integrableOn_Ioi_comp_mul_left_iff _ 1 (inv_pos.mpr hc0), mul_one]
    exact hscaled
  refine hcomp.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [← mul_assoc, mul_inv_cancel₀ hc0.ne', one_mul, div_eq_mul_inv, mul_comm c⁻¹ t]

/-- **Abel–Mellin identity for `dilationRemainder b P` on `Re s > 1`.** -/
theorem mul_mellin_dilationRemainder {b : ℝ} (hb : 1 ≤ b) (P : Polynomial ℝ) {s : ℂ}
    (hs : 1 < s.re) :
    s * mellin (dilationRemainder b P) (-s) =
      dilationSymbol b P s * LSeries (fun n => (vonMangoldt n : ℂ)) s -
        (P.eval b⁻¹ : ℂ) * (s / (s - 1)) := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  have hm : mellin (dilationRemainder b P) (-s) =
      ∫ t in Ioi (1 : ℝ),
        ((dilationPolyOp b P Chebyshev.psi t - P.eval b⁻¹ * t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [mellin]
    have hfun : (fun t : ℝ => (t : ℂ) ^ (-s - 1) • dilationRemainder b P t) =
        (Ioi (1 : ℝ)).indicator (fun t : ℝ =>
          ((dilationPolyOp b P Chebyshev.psi t - P.eval b⁻¹ * t : ℝ) : ℂ) *
            (t : ℂ) ^ (-(s + 1))) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · simp only [dilationRemainder, ht, indicator_of_mem, smul_eq_mul,
          show -s - 1 = -(s + 1) by ring, mul_comm]
      · simp [dilationRemainder, ht]
    rw [hfun, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
  have hre1 : (-s).re < -1 := by simp only [Complex.neg_re]; linarith
  have hi_lin : IntegrableOn (fun t : ℝ => (P.eval b⁻¹ : ℂ) * (t : ℂ) ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt hre1 one_pos).const_mul _
  have hi_sum : ∀ k ∈ Finset.range (P.natDegree + 1), Integrable
      (fun t : ℝ => (P.coeff k : ℂ) * ((Chebyshev.psi (t / b ^ k) : ℂ) * (t : ℂ) ^ (-(s + 1))))
      (volume.restrict (Ioi 1)) :=
    fun k _ => (integrableOn_psi_div_mul_cpow (one_le_pow₀ hb) hs).const_mul _
  have hpt : ∀ t ∈ Ioi (1 : ℝ),
      ((dilationPolyOp b P Chebyshev.psi t - P.eval b⁻¹ * t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (∑ k ∈ Finset.range (P.natDegree + 1),
          (P.coeff k : ℂ) * ((Chebyshev.psi (t / b ^ k) : ℂ) * (t : ℂ) ^ (-(s + 1)))) -
          (P.eval b⁻¹ : ℂ) * (t : ℂ) ^ (-s) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans ht).ne'
    have hpow : (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      have h := Complex.cpow_add (x := (t : ℂ)) 1 (-(s + 1)) ht0
      rwa [Complex.cpow_one, show (1 : ℂ) + -(s + 1) = -s by ring] at h
    simp only [dilationPolyOp, Complex.ofReal_sub, Complex.ofReal_sum, Complex.ofReal_mul,
      sub_mul, Finset.sum_mul, mul_assoc, hpow]
  rw [hm, setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub (integrable_finsetSum _ hi_sum) hi_lin, integral_finset_sum _ hi_sum,
    integral_const_mul, integral_Ioi_cpow_of_lt hre1 one_pos, ofReal_one, one_cpow,
    show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  have hsum_int : (∑ k ∈ Finset.range (P.natDegree + 1),
      ∫ t in Ioi (1 : ℝ),
        (P.coeff k : ℂ) * ((Chebyshev.psi (t / b ^ k) : ℂ) * (t : ℂ) ^ (-(s + 1)))) =
      dilationSymbol b P s *
        ∫ u in Ioi (1 : ℝ), (criticalCumulative (fun n => vonMangoldt n) u : ℂ) *
          (u : ℂ) ^ (-(s + 1)) := by
    rw [dilationSymbol, Polynomial.eval₂_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_Ioi_one_psi_div_mul_cpow (one_le_pow₀ hb) hs]
    have hbk_pow : (((b ^ k : ℝ) : ℂ)) ^ (-s) = ((b : ℂ) ^ (-s)) ^ k := by
      have hbC0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
      have hbkC0 : (((b ^ k : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (pow_pos hb0 k).ne'
      rw [Complex.cpow_def_of_ne_zero hbkC0, Complex.cpow_def_of_ne_zero hbC0,
        ← Complex.ofReal_log (pow_pos hb0 k).le, ← Complex.ofReal_log hb0.le,
        Real.log_pow, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hcc : (∫ u in Ioi (1 : ℝ), (Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-(s + 1))) =
        ∫ u in Ioi (1 : ℝ), (criticalCumulative (fun n => vonMangoldt n) u : ℂ) *
          (u : ℂ) ^ (-(s + 1)) :=
      setIntegral_congr_fun measurableSet_Ioi fun u _ => by rw [criticalCumulative_vonMangoldt_eq_psi]
    rw [hbk_pow, hcc]
    simp only [RCLike.algebraMap_eq_ofReal]
    ring
  rw [hsum_int, mul_sub, ← mul_assoc, mul_comm s (dilationSymbol b P s), mul_assoc,
    ← vonMangoldtLSeries_eq_mul_integral_criticalCumulative hs]
  ring

/-- `dilationSymbol b P` is an entire function of `s` (`b > 0`). -/
theorem differentiable_dilationSymbol {b : ℝ} (hb : 0 < b) (P : Polynomial ℝ) :
    Differentiable ℂ (dilationSymbol b P) := by
  have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hfun : dilationSymbol b P = fun s => P.eval₂ (algebraMap ℝ ℂ) ((b : ℂ) ^ (-s)) := rfl
  rw [hfun]
  have hpow : Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl hb0)
  have heval : ∀ s : ℂ, P.eval₂ (algebraMap ℝ ℂ) ((b : ℂ) ^ (-s)) =
      ∑ k ∈ Finset.range (P.natDegree + 1), (P.coeff k : ℂ) * ((b : ℂ) ^ (-s)) ^ k :=
    fun _ => Polynomial.eval₂_eq_sum_range
  simp_rw [heval]
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (hpow.pow k)

/-- At `s = 1`, `dilationSymbol b P 1 = P.eval b⁻¹` (`b > 0`). -/
theorem dilationSymbol_one {b : ℝ} (hb : 0 < b) (P : Polynomial ℝ) :
    dilationSymbol b P 1 = (P.eval b⁻¹ : ℂ) := by
  have hb1 : (b : ℂ) ^ (-(1 : ℂ)) = (b⁻¹ : ℂ) := by
    rw [Complex.cpow_neg_one, Complex.ofReal_inv]
  rw [dilationSymbol, hb1, Polynomial.eval_eq_sum_range, Polynomial.eval₂_eq_sum_range]
  simp [RCLike.algebraMap_eq_ofReal]

/-- Holomorphic numerator `Q_b(s) = D(1) − dslope D 1 s + s mellin R_b (−s)` after pole clearing. -/
def dilationClearedNumerator (b : ℝ) (P : Polynomial ℝ) (s : ℂ) : ℂ :=
  dilationSymbol b P 1 - dslope (dilationSymbol b P) 1 s + s * mellin (dilationRemainder b P) (-s)

theorem differentiableAt_dilationClearedNumerator {b σ₀ C x₀ : ℝ} (hb : 0 < b) {P : Polynomial ℝ}
    (hbnd : ∀ x, x₀ ≤ x → |dilationPolyOp b P Chebyshev.psi x - P.eval b⁻¹ * x| ≤ C * x ^ σ₀)
    {s : ℂ} (hs : σ₀ < s.re) :
    DifferentiableAt ℂ (dilationClearedNumerator b P) s := by
  have hD : Differentiable ℂ (dilationSymbol b P) := differentiable_dilationSymbol hb P
  have hdslope : Differentiable ℂ (dslope (dilationSymbol b P) 1) :=
    differentiable_iff_differentiableOn_univ.mpr
      ((Complex.differentiableOn_dslope univ_mem).mpr hD.differentiableOn)
  have hbigO_top : dilationRemainder b P =O[atTop] (fun x : ℝ => x ^ (-(-σ₀))) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop x₀, eventually_gt_atTop (1 : ℝ)] with x hx h1
    have hmem : x ∈ Ioi (1 : ℝ) := h1
    rw [dilationRemainder, indicator_of_mem hmem, neg_neg, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact hbnd x hx
  have hbigO_zero : dilationRemainder b P =O[𝓝[>] 0] (fun x : ℝ => x ^ (-((-s).re - 1))) := by
    refine (Asymptotics.isBigO_zero _ _).congr' ?_ EventuallyEq.rfl
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)] with x hx
    have hnot : x ∉ Ioi (1 : ℝ) := fun h => lt_asymm h hx
    rw [dilationRemainder, indicator_of_notMem hnot]
  have hm : DifferentiableAt ℂ (mellin (dilationRemainder b P)) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -σ₀) (b := (-s).re - 1)
      (locallyIntegrableOn_dilationRemainder hb P) hbigO_top (by simpa using hs) hbigO_zero
      (by linarith)
  exact ((differentiableAt_const _).sub (hdslope s)).add
    (differentiableAt_id.mul (hm.comp s (differentiable_neg s)))

/-- **Exact holomorphic clearing identity on `Re s > σ₀`.** -/
theorem neg_dilationSymbol_mul_deriv_zetaResidueUnit_eq {b σ₀ C x₀ : ℝ} (hb : 1 ≤ b)
    {P : Polynomial ℝ}
    (hbnd : ∀ x, x₀ ≤ x → |dilationPolyOp b P Chebyshev.psi x - P.eval b⁻¹ * x| ≤ C * x ^ σ₀)
    {s : ℂ} (hs : σ₀ < s.re) :
    -(dilationSymbol b P s * deriv zetaResidueUnit s) =
      zetaResidueUnit s * dilationClearedNumerator b P s := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  set U : Set ℂ := {w | σ₀ < w.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set F : ℂ → ℂ := fun w => -(dilationSymbol b P w * deriv zetaResidueUnit w) -
      zetaResidueUnit w * dilationClearedNumerator b P w with hF
  have hFd : DifferentiableOn ℂ F U := by
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiable_dilationSymbol hb0 P w).mul
      (analyticAt_zetaResidueUnit w).deriv.differentiableAt).neg).sub
      ((analyticAt_zetaResidueUnit w).differentiableAt.mul
        (differentiableAt_dilationClearedNumerator hb0 hbnd hw))
  have hFa : AnalyticOnNhd ℂ F U := hFd.analyticOnNhd hUo
  set r : ℝ := max 1 σ₀ + 1 with hr
  have hr1 : 1 < r := by have := le_max_left 1 σ₀; linarith
  have hrσ : σ₀ < r := by have := le_max_right 1 σ₀; linarith
  have hz₀ : (r : ℂ) ∈ U := by simpa [U] using hrσ
  have hev : F =ᶠ[𝓝 (r : ℂ)] 0 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simpa using hr1 : 1 < (r : ℂ).re)] with w hw
    have hw1 : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw; exact lt_irrefl 1 hw
    have hζ : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw
    have hZ : zetaResidueUnit w = (w - 1) * riemannZeta w :=
      (zetaResidueUnit_eventuallyEq hw1).eq_of_nhds
    have hdZ : deriv zetaResidueUnit w = riemannZeta w + (w - 1) * deriv riemannZeta w := by
      rw [(zetaResidueUnit_eventuallyEq hw1).deriv_eq]
      have hd : HasDerivAt (fun z => (z - 1) * riemannZeta z)
          (1 * riemannZeta w + (w - 1) * deriv riemannZeta w) w :=
        ((hasDerivAt_id w).sub_const 1).mul (differentiableAt_riemannZeta hw1).hasDerivAt
      rw [hd.deriv, one_mul]
    have hL : LSeries (fun n => (vonMangoldt n : ℂ)) w = -deriv riemannZeta w / riemannZeta w :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw
    simp only [hF, Pi.zero_apply, dilationClearedNumerator, dslope_of_ne _ hw1, slope_def_field,
      mul_mellin_dilationRemainder hb P hw, dilationSymbol_one hb0 P, hL, hZ, hdZ]
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.mpr hw1
    generalize dilationSymbol b P w = Dw
    generalize (P.eval b⁻¹ : ℂ) = D1
    generalize deriv riemannZeta w = z'
    field_simp
    ring
  have hEq := hFa.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt σ₀).isPreconnected hz₀ hev
  exact sub_eq_zero.mp (hEq hs)

/-! ### 3. Single-base periodic ordinate pinning and two-prime finiteness -/

/-- **Symbol vanishing at every right-half-plane zero.** Any zero `ρ ≠ 1` of `ζ` in `{Re s > σ₀}`
must be a root of `dilationSymbol b P`. -/
theorem dilationSymbol_eq_zero_of_zeta_eq_zero {b σ₀ C x₀ : ℝ} (hb : 1 ≤ b) {P : Polynomial ℝ}
    (hbnd : ∀ x, x₀ ≤ x → |dilationPolyOp b P Chebyshev.psi x - P.eval b⁻¹ * x| ≤ C * x ^ σ₀)
    {ρ : ℂ} (hρ : σ₀ < ρ.re) (hρ1 : ρ ≠ 1) (hζ : riemannZeta ρ = 0) :
    dilationSymbol b P ρ = 0 := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  by_contra hDne
  have hZ0 : zetaResidueUnit ρ = 0 := by
    rw [(zetaResidueUnit_eventuallyEq hρ1).eq_of_nhds, hζ, mul_zero]
  have hZa := analyticAt_zetaResidueUnit ρ
  have hdZa : AnalyticAt ℂ (deriv zetaResidueUnit) ρ := hZa.deriv
  have hDa : AnalyticAt ℂ (dilationSymbol b P) ρ :=
    (differentiable_dilationSymbol hb0 P).analyticAt ρ
  have hUo : IsOpen {w : ℂ | σ₀ < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hQa : AnalyticAt ℂ (dilationClearedNumerator b P) ρ := by
    have hd : DifferentiableOn ℂ (dilationClearedNumerator b P) {w : ℂ | σ₀ < w.re} :=
      fun w hw => (differentiableAt_dilationClearedNumerator hb0 hbnd hw).differentiableWithinAt
    exact hd.analyticOnNhd hUo ρ hρ
  have hev : (fun w => dilationSymbol b P w * deriv zetaResidueUnit w) =ᶠ[𝓝 ρ]
      -(zetaResidueUnit * dilationClearedNumerator b P) := by
    filter_upwards [hUo.mem_nhds hρ] with w hw
    have hid := neg_dilationSymbol_mul_deriv_zetaResidueUnit_eq hb hbnd (s := w) hw
    simp only [Pi.neg_apply, Pi.mul_apply]
    rw [← hid, neg_neg]
  have hord := analyticOrderAt_congr hev
  have hleft : analyticOrderAt (fun w => dilationSymbol b P w * deriv zetaResidueUnit w) ρ =
      analyticOrderAt (deriv zetaResidueUnit) ρ := by
    have h := analyticOrderAt_mul (𝕜 := ℂ) hDa hdZa
    rw [hDa.analyticOrderAt_eq_zero.mpr hDne, zero_add] at h
    exact h
  have hright : analyticOrderAt (-(zetaResidueUnit * dilationClearedNumerator b P)) ρ =
      analyticOrderAt zetaResidueUnit ρ + analyticOrderAt (dilationClearedNumerator b P) ρ := by
    rw [analyticOrderAt_neg, analyticOrderAt_mul hZa hQa]
  have hstep : analyticOrderAt (deriv zetaResidueUnit) ρ + 1 = analyticOrderAt zetaResidueUnit ρ := by
    simpa [hZ0] using hZa.analyticOrderAt_deriv_add_one
  have htop : analyticOrderAt zetaResidueUnit ρ ≠ ⊤ := Sieve.zetaResidueUnit_order_ne_top ρ
  rw [hleft, hright] at hord
  rw [hord] at hstep
  generalize analyticOrderAt zetaResidueUnit ρ = m at hstep htop
  generalize analyticOrderAt (dilationClearedNumerator b P) ρ = q at hstep
  induction m using ENat.recTopCoe with
  | top => exact htop rfl
  | coe m =>
    induction q using ENat.recTopCoe with
    | top => simp at hstep
    | coe q => norm_cast at hstep; omega

/-- **Single-base periodic ordinate pinning.** If `dilationSetOp b β S ψ (x) = κ_b x + O(x^{σ₀})`
with `b > 1`, then every zero `ρ ≠ 1` of `ζ` with `Re ρ > σ₀` satisfies `ρ.re = β` and
`ρ.im = α + m (2π / log b)` for some `α ∈ oscillationFrequencies S` and `m ∈ ℤ`. -/
theorem re_eq_and_im_mem_periodic_of_dilation_bound {b β σ₀ C x₀ : ℝ} (hb : 1 < b) {S : Finset ℝ}
    (hbnd : ∀ x, x₀ ≤ x → |dilationSetOp b β S Chebyshev.psi x - mainTermFactor b β S * x| ≤
      C * x ^ σ₀)
    {ρ : ℂ} (hρ : σ₀ < ρ.re) (hρ1 : ρ ≠ 1) (hζ : riemannZeta ρ = 0) :
    ρ.re = β ∧ ∃ α ∈ oscillationFrequencies S, ∃ m : ℤ,
      ρ.im = α + (m : ℝ) * (2 * Real.pi / Real.log b) := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have hD0 := dilationSymbol_eq_zero_of_zeta_eq_zero hb.le hbnd hρ hρ1 hζ
  rw [dilationSymbol_dilationSetPoly_eq hb0] at hD0
  obtain ⟨ω, hω, hprod0⟩ := Finset.prod_eq_zero_iff.mp hD0
  have hextract : ∀ α : ℝ, α ∈ oscillationFrequencies S →
      (b : ℂ) ^ (((β : ℂ) + I * α) - ρ) = 1 →
      ρ.re = β ∧ ∃ α' ∈ oscillationFrequencies S, ∃ m : ℤ,
        ρ.im = α' + (m : ℝ) * (2 * Real.pi / Real.log b) := by
    intro α hα hpow1
    have hbC0 : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
    rw [Complex.cpow_def_of_ne_zero hbC0, ← Complex.ofReal_log hb0.le,
      Complex.exp_eq_one_iff] at hpow1
    obtain ⟨m, hm⟩ := hpow1
    have hre_eq := congrArg Complex.re hm
    have him_eq := congrArg Complex.im hm
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
      Complex.add_re, Complex.I_re, Complex.I_im, Complex.mul_im, Complex.sub_im,
      Complex.add_im] at hre_eq him_eq
    have hre_final : ρ.re = β := by nlinarith [hlogb]
    have him_rel : (α - ρ.im) * Real.log b = (m : ℝ) * (2 * Real.pi) := by
      simpa using him_eq
    refine ⟨hre_final, α, hα, -m, ?_⟩
    have hdiv : α - ρ.im = (m : ℝ) * (2 * Real.pi) / Real.log b :=
      (eq_div_iff hlogb.ne').mpr him_rel
    push_cast
    linarith [show (m : ℝ) * (2 * Real.pi) / Real.log b = (m : ℝ) * (2 * Real.pi / Real.log b)
      by ring]
  rcases mul_eq_zero.mp hprod0 with h1 | h2
  · exact hextract ω (Finset.mem_union_left _ hω) (sub_eq_zero.mp h1).symm
  · have hneg_mem : -ω ∈ oscillationFrequencies S :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ω, hω, rfl⟩)
    have h2' : (b : ℂ) ^ (((β : ℂ) + I * ((-ω : ℝ) : ℂ)) - ρ) = 1 := by
      have hrew : (β : ℂ) + I * ((-ω : ℝ) : ℂ) - ρ = (β : ℂ) - I * (ω : ℂ) - ρ := by
        push_cast
        ring
      rw [hrew]
      exact (sub_eq_zero.mp h2).symm
    exact hextract (-ω) hneg_mem h2'

/-- **Two-prime incommensurable ordinate finiteness.** Joint `O(x^{σ₀})` dilation annihilation at
two distinct prime bases `p ≠ q` confines `{q : XiZeroCopy | σ₀ < Re q}` to a finite set. -/
theorem finite_xiZeroCopy_of_twoPrime_dilation_bound {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {β σ₀ Cp x₀p Cq x₀q : ℝ} {S : Finset ℝ}
    (hbp : ∀ x, x₀p ≤ x →
      |dilationSetOp p β S Chebyshev.psi x - mainTermFactor p β S * x| ≤ Cp * x ^ σ₀)
    (hbq : ∀ x, x₀q ≤ x →
      |dilationSetOp q β S Chebyshev.psi x - mainTermFactor q β S * x| ≤ Cq * x ^ σ₀) :
    {z : XiZeroCopy | σ₀ < (z.1 : ℂ).re}.Finite := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hirr : Irrational (Real.log q / Real.log p) := RHTower.irrational_log_ratio hp hq hpq
  set A : Finset ℝ := oscillationFrequencies S
  -- Any ordinate in `{Im z : z ∈ XiZeroCopy, Re z > σ₀}` is uniquely determined by its `(α_p, α_q)` pair
  set Ord : Set ℝ := (fun z : XiZeroCopy => (z.1 : ℂ).im) '' {z : XiZeroCopy | σ₀ < (z.1 : ℂ).re}
  have hpair : ∀ γ ∈ Ord, ∃ pair ∈ A ×ˢ A,
      (∃ m : ℤ, γ = pair.1 + (m : ℝ) * (2 * Real.pi / Real.log p)) ∧
      (∃ n : ℤ, γ = pair.2 + (n : ℝ) * (2 * Real.pi / Real.log q)) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨_, αp, hαp, m, hm⟩ := re_eq_and_im_mem_periodic_of_dilation_bound hp1 hbp hz
      (xiZeroCopy_ne_one z) (riemannZeta_eq_zero_of_xiZeroCopy z)
    obtain ⟨_, αq, hαq, n, hn⟩ := re_eq_and_im_mem_periodic_of_dilation_bound hq1 hbq hz
      (xiZeroCopy_ne_one z) (riemannZeta_eq_zero_of_xiZeroCopy z)
    exact ⟨(αp, αq), Finset.mem_product.mpr ⟨hαp, hαq⟩, ⟨m, hm⟩, ⟨n, hn⟩⟩
  choose tag htag_mem htag_p htag_q using fun γ (hγ : γ ∈ Ord) => hpair γ hγ
  have hinj : ∀ γ₁ (h₁ : γ₁ ∈ Ord) γ₂ (h₂ : γ₂ ∈ Ord),
      tag γ₁ h₁ = tag γ₂ h₂ → γ₁ = γ₂ := by
    intro γ₁ h₁ γ₂ h₂ heq
    obtain ⟨m₁, hm₁⟩ := htag_p γ₁ h₁
    obtain ⟨n₁, hn₁⟩ := htag_q γ₁ h₁
    obtain ⟨m₂, hm₂⟩ := htag_p γ₂ h₂
    obtain ⟨n₂, hn₂⟩ := htag_q γ₂ h₂
    have hp_fst : (tag γ₁ h₁).1 = (tag γ₂ h₂).1 := congrArg Prod.fst heq
    have hq_snd : (tag γ₁ h₁).2 = (tag γ₂ h₂).2 := congrArg Prod.snd heq
    have hdiff_p : γ₁ - γ₂ = ((m₁ - m₂ : ℤ) : ℝ) * (2 * Real.pi / Real.log p) := by
      push_cast
      linarith [hm₁, hm₂, hp_fst]
    have hdiff_q : γ₁ - γ₂ = ((n₁ - n₂ : ℤ) : ℝ) * (2 * Real.pi / Real.log q) := by
      push_cast
      linarith [hn₁, hn₂, hq_snd]
    by_cases hm_eq : m₁ = m₂
    · subst hm_eq
      simp at hdiff_p
      linarith
    · exfalso
      have hm_ne : ((m₁ - m₂ : ℤ) : ℝ) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr hm_eq
      have hrel : ((m₁ - m₂ : ℤ) : ℝ) * Real.log q = ((n₁ - n₂ : ℤ) : ℝ) * Real.log p := by
        have hpi : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
        have heq_div : ((m₁ - m₂ : ℤ) : ℝ) / Real.log p = ((n₁ - n₂ : ℤ) : ℝ) / Real.log q := by
          apply mul_right_cancel₀ hpi
          calc ((m₁ - m₂ : ℤ) : ℝ) / Real.log p * (2 * Real.pi)
              = ((m₁ - m₂ : ℤ) : ℝ) * (2 * Real.pi / Real.log p) := by ring
            _ = ((n₁ - n₂ : ℤ) : ℝ) * (2 * Real.pi / Real.log q) := hdiff_p.symm.trans hdiff_q
            _ = ((n₁ - n₂ : ℤ) : ℝ) / Real.log q * (2 * Real.pi) := by ring
        exact (div_eq_div_iff hlogp.ne' hlogq.ne').mp heq_div
      have hrat : Real.log q / Real.log p = (((n₁ - n₂ : ℤ) : ℚ) / ((m₁ - m₂ : ℤ) : ℚ) : ℚ) := by
        push_cast
        rw [div_eq_div_iff hlogp.ne' hm_ne]
        linarith
      exact hirr ⟨((n₁ - n₂ : ℤ) : ℚ) / ((m₁ - m₂ : ℤ) : ℚ), hrat.symm⟩
  have hOrd_fin : Ord.Finite := by
    let f : Ord → (A ×ˢ A) := fun x => ⟨tag x.1 x.2, htag_mem x.1 x.2⟩
    have hf_inj : Function.Injective f := fun x y hxy =>
      Subtype.ext (hinj x.1 x.2 y.1 y.2 (congrArg Subtype.val hxy))
    exact Set.finite_coe_iff.mp (Finite.of_injective f hf_inj)
  obtain ⟨M, hM⟩ := (hOrd_fin.image abs).bddAbove
  refine (finite_abs_im_le (max M 0)).subset fun z hz => ?_
  have hmem : |(z.1 : ℂ).im| ∈ abs '' Ord := ⟨(z.1 : ℂ).im, ⟨z, hz, rfl⟩, rfl⟩
  exact (hM hmem).trans (le_max_left _ _)

/-- **Exact two-prime multiplicative dilation characterization of `¬ AsymptoticAbscissaLaw`.**
For any two distinct primes `p ≠ q`, `¬ AsymptoticAbscissaLaw` (`PrimeErrorIsFiniteOscillation`)
holds if and only if there exist `β ∈ (1/2, 1)`, `η > 0`, a finite frequency set `S`, and a zero
`ρ₀` of `ζ` in `{β − η < Re s < 1}` such that both `dilationSetOp p β S ψ` and
`dilationSetOp q β S ψ` collapse to their linear PNT main terms up to `O(x^{β−η})`. -/
theorem not_asymptoticAbscissaLaw_iff_twoPrime_dilationAnnihilation {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬ AsymptoticAbscissaLaw ↔
      ∃ (β η : ℝ) (S : Finset ℝ),
        1 / 2 < β ∧ β < 1 ∧ 0 < η ∧
        (∃ ρ₀ : ℂ, riemannZeta ρ₀ = 0 ∧ β - η < ρ₀.re ∧ ρ₀.re < 1) ∧
        (∃ Cp x₀p : ℝ, ∀ x, x₀p ≤ x →
          |dilationSetOp p β S Chebyshev.psi x - mainTermFactor p β S * x| ≤ Cp * x ^ (β - η)) ∧
        (∃ Cq x₀q : ℝ, ∀ x, x₀q ≤ x →
          |dilationSetOp q β S Chebyshev.psi x - mainTermFactor q β S * x| ≤ Cq * x ^ (β - η)) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
  constructor
  · intro hnot
    obtain ⟨β, η, hβ, hη, S, c, ⟨u₀, hu₀⟩, C, x₀, hC⟩ :=
      primeErrorIsFiniteOscillation_of_not_asymptoticAbscissaLaw hnot
    set σ₀ : ℝ := max (β - η) ((β + 1 / 2) / 2)
    have hσβ : σ₀ < β := max_lt (by linarith) (by linarith)
    have hb : ∀ x, max x₀ 1 ≤ x →
        ‖oscillationError β (oscillationFrequencies S) (oscillationCoeff S c) x‖ ≤
          |C| * x ^ σ₀ := by
      intro x hx
      have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
      have hx0 : 0 < x := by linarith
      have hrep : oscillationError β (oscillationFrequencies S) (oscillationCoeff S c) x =
          ((Chebyshev.psi x - x - x ^ β * finiteOscillation S c (Real.log x) : ℝ) : ℂ) := by
        have hsum : ∑ ω ∈ oscillationFrequencies S,
              oscillationCoeff S c ω * (x : ℂ) ^ ((β : ℂ) + I * ω) =
            ((x ^ β * finiteOscillation S c (Real.log x) : ℝ) : ℂ) := by
          rw [Complex.ofReal_mul, finiteOscillation_eq_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [cpow_add_I_mul_eq hx0]
          ring
        rw [oscillationError, hsum]
        push_cast
        ring
      rw [hrep, Complex.norm_real, Real.norm_eq_abs]
      exact (hC x ((le_max_left _ _).trans hx)).trans
        ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hx0.le _)).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)) (abs_nonneg C)))
    obtain ⟨μ₀, hμ₀, hne_coeff⟩ := exists_oscillationCoeff_ne_zero hu₀
    have hζ₀ := zeta_eq_zero_of_coeff_ne_zero hb hμ₀ hne_coeff hσβ (by linarith)
    have hre₀ : ((β : ℂ) + I * μ₀).re = β := by simp
    have hβ1 : β < 1 := by
      by_contra hge
      exact riemannZeta_ne_zero_of_one_le_re (by rw [hre₀]; linarith) hζ₀
    refine ⟨β, η, S, hβ, hβ1, hη,
      ⟨(β : ℂ) + I * μ₀, hζ₀, by rw [hre₀]; linarith, by rw [hre₀]; exact hβ1⟩,
      abs_dilationSetOp_psi_sub_mainTerm_le hp1 hC,
      abs_dilationSetOp_psi_sub_mainTerm_le hq1 hC⟩
  · rintro ⟨β, η, S, hβ, _, _, ⟨ρ₀, hζ₀, hρ₀_gt, hρ₀_lt1⟩, ⟨Cp, x₀p, hbp⟩, ⟨Cq, x₀q, hbq⟩⟩ hAAL
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hρ₀_ne1 : ρ₀ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ₀_lt1; exact lt_irrefl 1 hρ₀_lt1
    have hρ₀_re : ρ₀.re = β :=
      (re_eq_and_im_mem_periodic_of_dilation_bound hp_gt1 hbp hρ₀_gt hρ₀_ne1 hζ₀).1
    obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_zeta_eq_zero_strip hζ₀
      (by rw [hρ₀_re]; linarith) hρ₀_lt1
    set σ₁ : ℝ := max (β - η) ((β + 1 / 2) / 2)
    have hσ₁_half : 1 / 2 < σ₁ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hσ₁_lt_β : σ₁ < β := max_lt (hρ₀_re ▸ hρ₀_gt) (by linarith)
    have hbp' : ∀ x, max x₀p 1 ≤ x →
        |dilationSetOp p β S Chebyshev.psi x - mainTermFactor p β S * x| ≤ |Cp| * x ^ σ₁ := by
      intro x hx
      have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
      exact (hbp x ((le_max_left _ _).trans hx)).trans
        ((mul_le_mul_of_nonneg_right (le_abs_self Cp) (Real.rpow_nonneg (by linarith) _)).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)) (abs_nonneg Cp)))
    have hbq' : ∀ x, max x₀q 1 ≤ x →
        |dilationSetOp q β S Chebyshev.psi x - mainTermFactor q β S * x| ≤ |Cq| * x ^ σ₁ := by
      intro x hx
      have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
      exact (hbq x ((le_max_left _ _).trans hx)).trans
        ((mul_le_mul_of_nonneg_right (le_abs_self Cq) (Real.rpow_nonneg (by linarith) _)).trans
          (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)) (abs_nonneg Cq)))
    have hfin := finite_xiZeroCopy_of_twoPrime_dilation_bound hp hq hpq hbp' hbq'
    have hfin' : {z : XiZeroCopy | 1 / 2 + (σ₁ - 1 / 2) < (z.1 : ℂ).re}.Finite := by
      simpa [add_sub_cancel] using hfin
    have hall := hAAL (σ₁ - 1 / 2) (by linarith) hfin' q₀
    rw [hq₀, hρ₀_re] at hall
    linarith

end

end GaloisForLFunctions.ZeroConfigurationGeometry
