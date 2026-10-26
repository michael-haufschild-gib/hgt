import GaloisForLFunctions.RHTower.DirichletFirstDifference
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The successor is invisible at zeros

Correspondences act on the fibres of a source at the zeros of `ζ` in three ways. Multiplicative
correspondences — Hecke operators, the archimedean flow, their gauge twists — act diagonally by a
symbol of modulus `p^{σ − ½}`: **hyperbolically** off the critical line
(`norm_twisted_heckeSymbol`, `TheLocalGeometryOfAReflectionPair`). The functional-equation
reflection exchanges the two points of a reflection pair: an **elliptic** symmetry. This file
computes the third, the additive successor `n ↦ n + 1`.

Shifting a source `a` by one replaces its Dirichlet series `Σ a_{n+1}(n+1)^{−s}` by
`Σ a_{n+1}(n+2)^{−s}`. The difference is the **successor defect**
`D_a(s) = Σ a_{n+1}((n+1)^{−s} − (n+2)^{−s})`, whose terms are `O(|s| n^{−σ−1})`:

* **The defect is holomorphic on `Re s > 0`** (`differentiableOn_succShiftDefect`) for every source
  with `Σ |a_{n+1}|(n+1)^{−σ−1} < ∞` at every `σ > 0`.
* **Prime source** (`succShift_vonMangoldt_eq`, `differentiableOn_succShiftDefect_vonMangoldt`). The
  Dirichlet series of the shifted primes `Σ Λ(n)(n+1)^{−s}` equals `−ζ′/ζ(s) − D_Λ(s)` on `Re s > 1`,
  with `D_Λ` holomorphic on the whole half-plane `Re s > 0`. So the shifted prime source has exactly
  the poles of `−ζ′/ζ` in the critical strip, with the same principal parts.

The successor is therefore **unipotent** on the polar fibres: it acts as the identity on the
singular part of every zero. Closure of a carrier under the successor imposes no condition on the
fibres at zeros, which is the fibre-level reason why free successor coordinates impose nothing
(affine positivity is induced from the dilations, APD) and why successor data are pure gauge charge
(ACG). Local types of arithmetic correspondences at an off-line pair: multiplicative — hyperbolic;
reflection — elliptic; additive — unipotent.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-! ### Multiplicative symbols: twists do not change the type -/

/-- **A gauge twist does not change the local type.** Multiplying a Hecke symbol by a unimodular
phase keeps its modulus `p^{σ − ½}`; it is a boost exactly off the line. -/
theorem norm_twisted_heckeSymbol (p : ℝ) (s : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖z * heckeSymbol p s‖ = Real.exp ((s.re - 1 / 2) * Real.log p) := by
  rw [norm_mul, hz, one_mul, norm_heckeSymbol]

/-- The archimedean flow by `t` acts with symbol `e^{(s − ½)t}` of modulus `e^{(σ − ½)t}`. -/
theorem norm_archimedeanSymbol (t : ℝ) (s : ℂ) :
    ‖Complex.exp ((s - 1 / 2) * t)‖ = Real.exp ((s.re - 1 / 2) * t) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-! ### The successor defect -/

/-- The unit step of a power: `‖(x)^{−s} − (x + 1)^{−s}‖ ≤ ‖s‖ x^{−Re s − 1}` for `Re s > 0`. -/
theorem norm_cpow_neg_sub_succ_le {s : ℂ} (hs : 0 < s.re) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * x ^ (-s.re - 1) := by
  have h1 := RHTower.norm_cpow_neg_sub_le hs hx (by linarith : x ≤ x + 1)
  have h2 := RHTower.rpow_sub_rpow_succ_le hs hx
  calc ‖(x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s)‖
      ≤ (‖s‖ / s.re) * (x ^ (-s.re) - (x + 1) ^ (-s.re)) := h1
    _ ≤ (‖s‖ / s.re) * (s.re * x ^ (-s.re - 1)) :=
        mul_le_mul_of_nonneg_left h2 (div_nonneg (norm_nonneg _) hs.le)
    _ = ‖s‖ * x ^ (-s.re - 1) := by field_simp

/-- The terms of the successor defect. -/
def succShiftTerm (a : ℕ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  a (n + 1) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s))

/-- The **successor defect** `D_a(s) = Σ a_{n+1}((n+1)^{−s} − (n+2)^{−s})`. -/
def succShiftDefect (a : ℕ → ℂ) (s : ℂ) : ℂ := ∑' n : ℕ, succShiftTerm a n s

theorem norm_succShiftTerm_le (a : ℕ → ℂ) (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖succShiftTerm a n s‖ ≤ ‖a (n + 1)‖ * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) := by
  rw [succShiftTerm, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cpow_neg_sub_succ_le hs (by positivity)) (norm_nonneg _)

theorem differentiableAt_succShiftTerm (a : ℕ → ℂ) (n : ℕ) (s : ℂ) :
    DifferentiableAt ℂ (succShiftTerm a n) s := by
  have hc : (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  have hd : ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]; positivity
  exact ((differentiableAt_id.neg.const_cpow (Or.inl hc)).sub
    (differentiableAt_id.neg.const_cpow (Or.inl hd))).const_mul _

/-- **The successor defect is holomorphic on `Re s > 0`.** -/
theorem differentiableOn_succShiftDefect (a : ℕ → ℂ)
    (hsum : ∀ σ : ℝ, 0 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1)) :
    DifferentiableOn ℂ (succShiftDefect a) {s | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  set σ₀ := s.re / 2
  set R := ‖s‖ + 1
  have hσ₀ : 0 < σ₀ := half_pos hs
  set V : Set ℂ := {w | σ₀ < w.re} ∩ Metric.ball 0 R
  have hV : IsOpen V := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hsV : s ∈ V := ⟨by show σ₀ < s.re; simp only [σ₀]; linarith, by simp [R]⟩
  have hdiff : DifferentiableOn ℂ (fun w => ∑' n : ℕ, succShiftTerm a n w) V := by
    refine differentiableOn_tsum_of_summable_norm (u := fun n => ‖a (n + 1)‖ *
      (R * ((n : ℝ) + 1) ^ (-σ₀ - 1))) ?_ (fun n => (fun w _ =>
        (differentiableAt_succShiftTerm a n w).differentiableWithinAt)) hV ?_
    · have := (hsum σ₀ hσ₀).mul_left R
      refine this.congr fun n => ?_
      ring
    · intro n w hw
      have hwre : σ₀ < w.re := hw.1
      have hwR : ‖w‖ < R := by simpa using hw.2
      refine (norm_succShiftTerm_le a n (hσ₀.trans hwre)).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
      exact mul_le_mul hwR.le (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
        (by positivity) (by positivity)
  exact (hdiff.differentiableAt (hV.mem_nhds hsV)).differentiableWithinAt

/-- **The successor shifts the Dirichlet series by the defect** on `Re s > 1`:
`Σ a_{n+1}(n+2)^{−s} = Σ a_{n+1}(n+1)^{−s} − D_a(s)`. -/
theorem tsum_succShift_eq (a : ℕ → ℂ)
    (hsum : ∀ σ : ℝ, 0 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1))
    {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, a (n + 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) =
      ∑' n : ℕ, a (n + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - succShiftDefect a s := by
  have hσ : 0 < s.re - 1 := by linarith
  have hb := hsum (s.re - 1) hσ
  have hpow : ∀ x : ℝ, 0 < x → ‖((x : ℝ) : ℂ) ^ (-s)‖ = x ^ (-s.re) := fun x hx => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  have hL : Summable fun n : ℕ => a (n + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) := by
    refine Summable.of_norm (hb.congr fun n => ?_)
    rw [norm_mul, hpow _ (by positivity)]
    congr 2; ring
  have hS : Summable fun n : ℕ => a (n + 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded hb fun n => ?_
    rw [norm_mul, hpow _ (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [show -(s.re - 1) - 1 = -s.re by ring]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hD : succShiftDefect a s =
      ∑' n : ℕ, a (n + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
        ∑' n : ℕ, a (n + 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) := by
    rw [succShiftDefect, ← hL.tsum_sub hS]
    refine tsum_congr fun n => ?_
    rw [succShiftTerm]; ring
  rw [hD]; ring

/-! ### The prime source -/

/-- The prime source as a complex sequence. -/
def vonMangoldtC (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ)

/-- `Σ Λ(n+1)(n+1)^{−σ−1}` converges for every `σ > 0`. -/
theorem summable_vonMangoldt_shift {σ : ℝ} (hσ : 0 < σ) :
    Summable fun n : ℕ => ‖vonMangoldtC (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1) := by
  have hs : 1 < ((1 + σ : ℝ) : ℂ).re := by simp; linarith
  have h := (summable_nat_add_iff 1).mpr
    ((summable_norm_iff).mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt hs))
  refine h.congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n), vonMangoldtC]
  simp only [Complex.ofReal_re]
  push_cast
  rw [Real.rpow_neg (by positivity), div_eq_mul_inv, show -σ - 1 = -(1 + σ) by ring,
    Real.rpow_neg (by positivity)]

/-- **The successor defect of the prime source is holomorphic on `Re s > 0`.** -/
theorem differentiableOn_succShiftDefect_vonMangoldt :
    DifferentiableOn ℂ (succShiftDefect vonMangoldtC) {s | 0 < s.re} :=
  differentiableOn_succShiftDefect _ fun _ hσ => summable_vonMangoldt_shift hσ

/-- `Σ Λ(n+1)(n+1)^{−s} = −ζ′/ζ(s)` on `Re s > 1`. -/
theorem tsum_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, vonMangoldtC (n + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      -deriv riemannZeta s / riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries,
    tsum_eq_zero_add (ArithmeticFunction.LSeriesSummable_vonMangoldt hs), LSeries.term_zero,
    zero_add]
  refine tsum_congr fun n => ?_
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), vonMangoldtC, Complex.cpow_neg, div_eq_mul_inv]
  push_cast
  rfl

/-- **The shifted prime source has the poles of `−ζ′/ζ`.** On `Re s > 1`,
`Σ Λ(n)(n+1)^{−s} = −ζ′/ζ(s) − D_Λ(s)`, and `D_Λ` is holomorphic on `Re s > 0`: the successor
leaves every principal part of `−ζ′/ζ` in the critical strip unchanged. -/
theorem succShift_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, vonMangoldtC (n + 1) * ((((n : ℝ) + 1) + 1 : ℝ) : ℂ) ^ (-s) =
      -deriv riemannZeta s / riemannZeta s - succShiftDefect vonMangoldtC s := by
  rw [tsum_succShift_eq vonMangoldtC (fun _ hσ => summable_vonMangoldt_shift hσ) hs,
    tsum_vonMangoldt_eq hs]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
