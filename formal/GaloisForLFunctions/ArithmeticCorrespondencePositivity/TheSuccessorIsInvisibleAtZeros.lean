import GaloisForLFunctions.RHTower.DirichletFirstDifference
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheLocalGeometryOfAReflectionPair
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.LocallyUniformLimit
import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic

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
* **Size of the defect** (`norm_succShiftDefect_le`, `norm_succShiftDefect_vonMangoldt_le`).
  `|D_a(s)| ≤ |s| Σ |a_{n+1}|(n+1)^{−σ−1}`; for the primes `|D_Λ(s)| ≤ |s| |ζ′/ζ(1 + σ)|`: the
  regular part of the successor grows at most linearly in the height. On the real axis the bound is
  sharp up to `2^{1+σ}`: `D_Λ(σ) ≥ σ 2^{−1−σ} |ζ′/ζ(1 + σ)|` (`le_re_succShiftDefect_vonMangoldt`).

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
  simp only [Complex.ofReal_re, Nat.succ_eq_add_one]
  push_cast
  rw [show -σ - 1 = -(1 + σ) by ring, Real.rpow_neg (by positivity), div_eq_mul_inv]

/-- **The successor defect of the prime source is holomorphic on `Re s > 0`.** -/
theorem differentiableOn_succShiftDefect_vonMangoldt :
    DifferentiableOn ℂ (succShiftDefect vonMangoldtC) {s | 0 < s.re} :=
  differentiableOn_succShiftDefect _ fun _ hσ => summable_vonMangoldt_shift hσ

/-- `Σ Λ(n+1)(n+1)^{−s} = −ζ′/ζ(s)` on `Re s > 1`. -/
theorem tsum_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, vonMangoldtC (n + 1) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) =
      -deriv riemannZeta s / riemannZeta s := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, LSeries,
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).tsum_eq_zero_add, LSeries.term_zero,
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

/-! ### The size of the defect -/

/-- **The defect grows at most linearly in `|s|`**:
`|D_a(s)| ≤ |s| Σ |a_{n+1}| (n+1)^{−Re s − 1}` on `Re s > 0`. -/
theorem norm_succShiftDefect_le (a : ℕ → ℂ)
    (hsum : ∀ σ : ℝ, 0 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1))
    {s : ℂ} (hs : 0 < s.re) :
    ‖succShiftDefect a s‖ ≤ ‖s‖ * ∑' n : ℕ, ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
  have hb : Summable fun n : ℕ => ‖a (n + 1)‖ * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
    ((hsum s.re hs).mul_left ‖s‖).congr fun n => by ring
  calc ‖succShiftDefect a s‖ ≤ ∑' n : ℕ, ‖a (n + 1)‖ * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
        tsum_of_norm_bounded hb.hasSum fun n => norm_succShiftTerm_le a n hs
    _ = ‖s‖ * ∑' n : ℕ, ‖a (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re - 1) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun n => by ring

/-- The prime weights at `1 + σ`: `Σ Λ(n+1)(n+1)^{−σ−1} = −ζ′/ζ(1 + σ)`. -/
theorem tsum_vonMangoldt_shift_eq {σ : ℝ} (hσ : 0 < σ) :
    ((∑' n : ℕ, ‖vonMangoldtC (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1) : ℝ) : ℂ) =
      -deriv riemannZeta (1 + σ) / riemannZeta (1 + σ) := by
  have hs : 1 < ((1 + σ : ℝ) : ℂ).re := by simp; linarith
  have h1 : (1 : ℂ) + (σ : ℂ) = ((1 + σ : ℝ) : ℂ) := by push_cast; ring
  rw [Complex.ofReal_tsum, h1, ← tsum_vonMangoldt_eq hs]
  refine tsum_congr fun n => ?_
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [vonMangoldtC, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_mul,
    Complex.ofReal_cpow hn.le]
  push_cast
  congr 2
  ring

/-- **The regular part of the successor is small**: on `Re s = σ > 0` the defect of the prime
source is at most `|s|` times `|ζ′/ζ(1 + σ)|`. Near a zero `ρ` the shifted prime source is
`−ζ′/ζ` plus a term of size `≤ |ρ| |ζ′/ζ(1 + Re ρ)|`. -/
theorem norm_succShiftDefect_vonMangoldt_le {s : ℂ} (hs : 0 < s.re) :
    ‖succShiftDefect vonMangoldtC s‖ ≤
      ‖s‖ * ‖deriv riemannZeta (1 + s.re) / riemannZeta (1 + s.re)‖ := by
  refine (norm_succShiftDefect_le vonMangoldtC (fun _ hσ => summable_vonMangoldt_shift hσ) hs).trans
    (le_of_eq ?_)
  congr 1
  rw [← norm_neg, ← neg_div, ← tsum_vonMangoldt_shift_eq hs, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (tsum_nonneg fun n => by positivity)]

/-- **The bound is sharp on the real axis**: for real `σ > 0`,
`D_Λ(σ) ≥ σ 2^{−1−σ} Σ Λ(n+1)(n+1)^{−σ−1} = σ 2^{−1−σ} |ζ′/ζ(1 + σ)|`, from
`x^{−σ} − (x+1)^{−σ} ≥ σ (x+1)^{−σ−1}` and `n + 2 ≤ 2(n + 1)`. -/
theorem le_re_succShiftDefect_vonMangoldt {σ : ℝ} (hσ : 0 < σ) :
    σ / 2 ^ (1 + σ) * ∑' n : ℕ, ‖vonMangoldtC (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1) ≤
      (succShiftDefect vonMangoldtC σ).re := by
  -- the defect at a real point is the real series of its terms
  set t : ℕ → ℝ := fun n => ‖vonMangoldtC (n + 1)‖ *
    (((n : ℝ) + 1) ^ (-σ) - (((n : ℝ) + 1) + 1) ^ (-σ))
  have hterm : ∀ n : ℕ, succShiftTerm vonMangoldtC n σ = (t n : ℂ) := by
    intro n
    have h1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) + 1 + 1 := by positivity
    rw [succShiftTerm, show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow h1, ← Complex.ofReal_cpow h2]
    simp only [t, vonMangoldtC, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    push_cast
    ring
  have hlow : ∀ n : ℕ, σ / 2 ^ (1 + σ) * (‖vonMangoldtC (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1)) ≤
      t n := by
    intro n
    have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hstep := (HTGeometry.rpow_unit_step_bounds (q := -σ) (by linarith) hx).1
    -- `(n+2)^{−σ−1} ≥ 2^{−σ−1}(n+1)^{−σ−1}`
    have h2 : (2 : ℝ) ^ (-σ - 1) * ((n : ℝ) + 1) ^ (-σ - 1) ≤ ((n : ℝ) + 1 + 1) ^ (-σ - 1) := by
      rw [← Real.mul_rpow (by norm_num) hx.le]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have h2' : (2 : ℝ) ^ (-σ - 1) = 1 / 2 ^ (1 + σ) := by
      rw [show -σ - 1 = -(1 + σ) by ring, Real.rpow_neg (by norm_num), one_div]
    have hΛ := norm_nonneg (vonMangoldtC (n + 1))
    simp only [t]
    rw [neg_neg, show -σ - 1 = -σ - 1 by ring] at hstep
    have hp : 0 ≤ ((n : ℝ) + 1) ^ (-σ - 1) := (Real.rpow_pos_of_pos hx _).le
    calc σ / 2 ^ (1 + σ) * (‖vonMangoldtC (n + 1)‖ * ((n : ℝ) + 1) ^ (-σ - 1))
        = ‖vonMangoldtC (n + 1)‖ * (σ * (2 ^ (-σ - 1) * ((n : ℝ) + 1) ^ (-σ - 1))) := by
          rw [h2']; ring
      _ ≤ ‖vonMangoldtC (n + 1)‖ * (σ * ((n : ℝ) + 1 + 1) ^ (-σ - 1)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ.le) hΛ
      _ ≤ ‖vonMangoldtC (n + 1)‖ * (((n : ℝ) + 1) ^ (-σ) - ((n : ℝ) + 1 + 1) ^ (-σ)) :=
          mul_le_mul_of_nonneg_left (by simpa using hstep) hΛ
  have hsumL := (summable_vonMangoldt_shift hσ).mul_left (σ / 2 ^ (1 + σ))
  have hsumT : Summable t := by
    refine Summable.of_nonneg_of_le (fun n => le_trans (by positivity) (hlow n)) (fun n => ?_)
      ((summable_vonMangoldt_shift hσ).mul_left σ)
    have h := norm_succShiftTerm_le vonMangoldtC n (s := σ) (by simpa using hσ)
    rw [hterm, Complex.norm_real, Real.norm_eq_abs] at h
    have := (le_abs_self (t n)).trans h
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσ] at this
    linarith
  have hD : succShiftDefect vonMangoldtC σ = ((∑' n, t n : ℝ) : ℂ) := by
    rw [succShiftDefect, Complex.ofReal_tsum]
    exact tsum_congr hterm
  rw [hD, Complex.ofReal_re, ← tsum_mul_left]
  exact hsumL.tsum_le_tsum hlow hsumT

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
