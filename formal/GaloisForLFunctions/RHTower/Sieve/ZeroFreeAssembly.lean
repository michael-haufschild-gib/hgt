import GaloisForLFunctions.RHTower.Sieve.ZeroFreeCombination
import GaloisForLFunctions.RHTower.Sieve.ZetaDerivBound

/-!
# Assembling the zero-free inequality

A zero at `β + iγ` and a point `σ + iγ` with `σ > 1` are joined by a horizontal segment.  Along it
the derivative bound is uniform, so the mean value inequality bounds `‖ζ(σ+iγ)‖` by `M(σ−β)`; the
three-four-one inequality bounds it below by an explicit positive quantity.  Together they force

`exp((−22 − 3 log(1 + 1/(σ−1)) − log B₀)/4) ≤ M (σ − β)`,

with `M` the explicit logarithmic derivative bound.  Every quantity is elementary in
`β, γ, σ, R, N, B₀`.
-/

namespace RHTower.Sieve

open Complex

/-- The segment between two points of the same height is horizontal. -/
theorem segment_re_im (β σ γ t : ℝ) :
    (((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).re
          = β + t * (σ - β)
    ∧ (((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I))).im
          = γ := by
  constructor <;> simp

/-- **The zero-free inequality, assembled.** -/
theorem zero_free_inequality {β σ γ R B₀ : ℝ} {N : ℕ} (hR : 0 < R)
    (hzero : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0)
    (hβσ : β ≤ σ) (hσ1 : 1 < σ)
    (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N)
    (hNp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I))‖ + R ≤ (N : ℝ))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀) :
    Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4)
      ≤ ((2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R)
          * (σ - β) := by
  set M : ℝ := (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R with hM
  have hMseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv riemannZeta (((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)))‖ ≤ M := by
    intro t ht
    obtain ⟨hre, him⟩ := segment_re_im β σ γ t
    refine norm_deriv_riemannZeta_le_log_of_re_ge (β := β) (γ := γ) hR ?_ him hβ hlow hγ hN
      (hNp t ht)
    rw [hre]
    have ht0 : 0 ≤ t := ht.1
    nlinarith [ht0, hβσ]
  have hsmall := norm_riemannZeta_le_of_zero (M := M) hzero hne hMseg
  have hdist : ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)‖ = σ - β := by
    have hrw : ((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
        = ((σ - β : ℝ) : ℂ) := by push_cast; ring
    rw [hrw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hdist, mul_one] at hsmall
  exact le_mul_sub_of_riemannZeta_eq_zero (σ := σ) (β := β) (t := γ) (M := M) (B₀ := B₀)
    hσ1 hB hsmall

/-- **The zero-free statement.**  The contrapositive of the assembled inequality: if the explicit
numeric comparison fails, there is no zero at `β + iγ`.  This is the form a region argument
applies — the remaining work is choosing the parameters so that `hfail` holds. -/
theorem riemannZeta_ne_zero_of_lt {β σ γ R B₀ : ℝ} {N : ℕ} (hR : 0 < R)
    (hβσ : β ≤ σ) (hσ1 : 1 < σ)
    (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N)
    (hNp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I))‖ + R ≤ (N : ℝ))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hfail : ((2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R)
        * (σ - β)
      < Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4)) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  exact absurd (zero_free_inequality hR hzero hβσ hσ1 hβ hlow hγ hN hNp hne hB) (not_le.2 hfail)

/-- **The lower bound as an explicit power.**  The exponential of the three-four-one expression is
at least `e^{-11/2}·(δ/2)^{3/4}·B₀^{-1/4}`, which is the shape the parameter optimisation compares
against. -/
theorem exp_three_four_one_ge {δ B₀ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 < B₀) :
    Real.exp (-22 / 4) * (δ / 2) ^ ((3 : ℝ) / 4) * B₀ ^ (-(1 : ℝ) / 4)
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / δ) - Real.log B₀) / 4) := by
  have hx : (0 : ℝ) < 1 + 1 / δ := by positivity
  have hsplit : ((-22 : ℝ) - 3 * Real.log (1 + 1 / δ) - Real.log B₀) / 4
      = -22 / 4 + (-(3 : ℝ) / 4) * Real.log (1 + 1 / δ) + (-(1 : ℝ) / 4) * Real.log B₀ := by
    ring
  rw [hsplit, Real.exp_add, Real.exp_add]
  have h1 : Real.exp ((-(3 : ℝ) / 4) * Real.log (1 + 1 / δ)) = (1 + 1 / δ) ^ (-(3 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hx]
    ring_nf
  have h2 : Real.exp ((-(1 : ℝ) / 4) * Real.log B₀) = B₀ ^ (-(1 : ℝ) / 4) := by
    rw [Real.rpow_def_of_pos hB]
    ring_nf
  rw [h1, h2]
  have hle : 1 + 1 / δ ≤ 2 / δ := by
    rw [le_div_iff₀ hδ0]
    field_simp
    linarith
  have hpow : (2 / δ) ^ (-(3 : ℝ) / 4) ≤ (1 + 1 / δ) ^ (-(3 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos hx hle (by norm_num)
  have hval : (2 / δ) ^ (-(3 : ℝ) / 4) = (δ / 2) ^ ((3 : ℝ) / 4) := by
    rw [show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring, Real.rpow_neg (by positivity),
      ← Real.inv_rpow (by positivity)]
    congr 1
    field_simp
  rw [hval] at hpow
  have hBnn : (0 : ℝ) < B₀ ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos hB _
  have hexp : (0 : ℝ) < Real.exp (-22 / 4) := Real.exp_pos _
  have hmul := mul_le_mul_of_nonneg_left hpow (le_of_lt hexp)
  have hmul2 := mul_le_mul_of_nonneg_right hmul (le_of_lt hBnn)
  linarith [hmul2]

/-- **The zero-free statement in power form.**  The comparison to discharge is between a product of
powers and the derivative bound — no logarithms of the parameters remain. -/
theorem riemannZeta_ne_zero_of_lt_pow {β σ γ R B₀ : ℝ} {N : ℕ} (hR : 0 < R)
    (hβσ : β ≤ σ) (hσ1 : 1 < σ) (hσ2 : σ - 1 ≤ 1) (hB0 : 0 < B₀)
    (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N)
    (hNp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I))‖ + R ≤ (N : ℝ))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hfail : ((2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R)
        * (σ - β)
      < Real.exp (-22 / 4) * ((σ - 1) / 2) ^ ((3 : ℝ) / 4) * B₀ ^ (-(1 : ℝ) / 4)) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_lt hR hβσ hσ1 hβ hlow hγ hN hNp hne hB ?_
  have hpow := exp_three_four_one_ge (δ := σ - 1) (B₀ := B₀) (by linarith) hσ2 hB0
  linarith

/-- **The optimisation, algebraically.**  The comparison of `riemannZeta_ne_zero_of_lt_pow` holds as
soon as `δ^{1/4}` is below an explicit threshold; the `δ^{3/4}` common to both sides cancels.  This
is what makes the scale `δ ≍ L^{-8}` — a fourth power of the `L²` in the derivative bound — rather
than `δ ≍ 1/L`. -/
theorem lt_of_rpow_quarter_lt {L δ C B : ℝ} (hL : 0 < L) (hδ0 : 0 < δ) (hC : 0 < C)
    (hsmall : δ ^ ((1 : ℝ) / 4)
      < Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * B ^ (-(1 : ℝ) / 4) / (8 * C * L ^ 2)) :
    8 * C * L ^ 2 * δ
      < Real.exp (-22 / 4) * (δ / 2) ^ ((3 : ℝ) / 4) * B ^ (-(1 : ℝ) / 4) := by
  have hq : (0 : ℝ) < δ ^ ((3 : ℝ) / 4) := Real.rpow_pos_of_pos hδ0 _
  have hδsplit : δ = δ ^ ((1 : ℝ) / 4) * δ ^ ((3 : ℝ) / 4) := by
    rw [← Real.rpow_add hδ0]
    norm_num
  have hdiv : (δ / 2) ^ ((3 : ℝ) / 4)
      = δ ^ ((3 : ℝ) / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) := by
    rw [Real.div_rpow hδ0.le (by norm_num), show (-(3 : ℝ) / 4) = -((3 : ℝ) / 4) by ring,
      Real.rpow_neg (by norm_num)]
    ring
  rw [hdiv]
  have hden : (0 : ℝ) < 8 * C * L ^ 2 := by positivity
  rw [lt_div_iff₀ hden] at hsmall
  calc 8 * C * L ^ 2 * δ
      = (δ ^ ((1 : ℝ) / 4) * (8 * C * L ^ 2)) * δ ^ ((3 : ℝ) / 4) := by
        conv_lhs => rw [hδsplit]
        ring
    _ < (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * B ^ (-(1 : ℝ) / 4))
          * δ ^ ((3 : ℝ) / 4) := by
        exact mul_lt_mul_of_pos_right hsmall hq
    _ = Real.exp (-22 / 4) * (δ ^ ((3 : ℝ) / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4))
          * B ^ (-(1 : ℝ) / 4) := by ring

/-- **The zero-free statement in the form the optimisation supplies.**  Every hypothesis is either
geometric or a comparison of explicit quantities in `L = log N`; the analytic content is discharged.
-/
theorem riemannZeta_ne_zero_of_quarter {β σ γ R B₀ C L : ℝ} {N : ℕ} (hR : 0 < R)
    (hβσ : β ≤ σ) (hσ1 : 1 < σ) (hσ2 : σ - 1 ≤ 1) (hB0 : 0 < B₀)
    (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N)
    (hNp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I))‖ + R ≤ (N : ℝ))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hL : 0 < L) (hC : 0 < C)
    (hML : (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R
      ≤ 4 * C * L ^ 2)
    (hgap : σ - β ≤ 2 * (σ - 1))
    (hquarter : (σ - 1) ^ ((1 : ℝ) / 4)
      < Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * B₀ ^ (-(1 : ℝ) / 4) / (8 * C * L ^ 2)) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  refine riemannZeta_ne_zero_of_lt_pow hR hβσ hσ1 hσ2 hB0 hβ hlow hγ hN hNp hne hB ?_
  have hkey := lt_of_rpow_quarter_lt (L := L) (δ := σ - 1) (C := C) (B := B₀) hL
    (by linarith) hC hquarter
  have hMpos : (0 : ℝ) ≤ (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R)
      + 2 * Real.exp 1) / R := by
    have h1 : (0 : ℝ) < |γ| - R := by linarith
    have h2 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
    have h3 : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    positivity
  have hgap0 : (0 : ℝ) ≤ σ - β := by linarith
  calc ((2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R) * (σ - β)
      ≤ (4 * C * L ^ 2) * (2 * (σ - 1)) := by
        exact mul_le_mul hML hgap hgap0 (by positivity)
    _ = 8 * C * L ^ 2 * (σ - 1) := by ring
    _ < Real.exp (-22 / 4) * ((σ - 1) / 2) ^ ((3 : ℝ) / 4) * B₀ ^ (-(1 : ℝ) / 4) := hkey

/-- **The geometric hypotheses discharged.**  A zero close enough to `1` automatically satisfies the
disc placement conditions at radius `R = 1/(4 log N)`, once `log N ≥ 3`. -/
theorem geometric_of_close {β R : ℝ} {N : ℕ} (hlogN : 3 ≤ Real.log N)
    (hR : R = 1 / (4 * Real.log N)) (hclose : 1 - 3 / (4 * Real.log N) ≤ β) :
    1 / 2 + R ≤ β ∧ 1 - 1 / Real.log N ≤ β - R := by
  have hlog : 0 < Real.log N := by linarith
  have hq : 3 / (4 * Real.log N) ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hr : R ≤ 1 / 12 := by
    rw [hR, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  constructor
  · linarith
  · rw [hR]
    have h3 : 1 / Real.log N - 1 / (4 * Real.log N) = 3 / (4 * Real.log N) := by
      field_simp
      ring
    linarith [h3.le, h3.ge]

/-- **The zero-free statement with the geometry discharged.**  At radius `R = 1/(4 log N)`, for a
zero within `3/(4 log N)` of `1`, only the analytic-parameter comparisons remain. -/
theorem riemannZeta_ne_zero_of_close {β σ γ B₀ C L : ℝ} {N : ℕ}
    (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N)
    (hclose : 1 - 3 / (4 * Real.log N) ≤ β)
    (hβσ : β ≤ σ) (hσ1 : 1 < σ) (hσ2 : σ - 1 ≤ 1) (hB0 : 0 < B₀)
    (hγ : 1 / (4 * Real.log N) < |γ|)
    (hNp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I))‖ + 1 / (4 * Real.log N) ≤ (N : ℝ))
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hL : 0 < L) (hC : 0 < C)
    (hML : (2 + Real.exp 1 * Real.log N
        + Real.exp 1 / (|γ| - 1 / (4 * Real.log N)) + 2 * Real.exp 1)
        / (1 / (4 * Real.log N))
      ≤ 4 * C * L ^ 2)
    (hgap : σ - β ≤ 2 * (σ - 1))
    (hquarter : (σ - 1) ^ ((1 : ℝ) / 4)
      < Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * B₀ ^ (-(1 : ℝ) / 4) / (8 * C * L ^ 2)) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  have hlog : 0 < Real.log N := by linarith
  have hRpos : (0 : ℝ) < 1 / (4 * Real.log N) := by positivity
  obtain ⟨hg1, hg2⟩ := geometric_of_close (β := β) (R := 1 / (4 * Real.log N)) hlogN rfl hclose
  exact riemannZeta_ne_zero_of_quarter hRpos hβσ hσ1 hσ2 hB0 hg1 hg2 hγ hN hNp hne hB hL hC
    hML hgap hquarter

/-- **The derivative bound absorbed into `32 log²N`.**  At radius `1/(4 log N)`, with `log N ≥ 3`
and `|γ| ≥ 1`, the explicit constant of `norm_deriv_riemannZeta_le_log` is at most `4·8·log²N`. -/
theorem deriv_const_le {γ : ℝ} {N : ℕ} (hlogN : 3 ≤ Real.log N) (hγ : 1 ≤ |γ|) :
    (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - 1 / (4 * Real.log N))
        + 2 * Real.exp 1) / (1 / (4 * Real.log N))
      ≤ 4 * 8 * (Real.log N) ^ 2 := by
  have hlog : 0 < Real.log N := by linarith
  have he : Real.exp 1 < 2.72 := by
    have := Real.exp_one_lt_d9
    linarith
  have he0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hR : 1 / (4 * Real.log N) ≤ 1 / 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hRpos : (0 : ℝ) < 1 / (4 * Real.log N) := by positivity
  have hden : (11 : ℝ) / 12 ≤ |γ| - 1 / (4 * Real.log N) := by linarith
  have hdenpos : (0 : ℝ) < |γ| - 1 / (4 * Real.log N) := by linarith
  have hfrac : Real.exp 1 / (|γ| - 1 / (4 * Real.log N)) ≤ Real.exp 1 * (12 / 11) := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [he0, hden]
  have hnum : 2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - 1 / (4 * Real.log N))
      + 2 * Real.exp 1 ≤ 8 * Real.log N := by
    nlinarith [hfrac, he, he0, hlogN, hlog]
  rw [div_le_iff₀ hRpos]
  have hrhs : 4 * 8 * (Real.log N) ^ 2 * (1 / (4 * Real.log N)) = 8 * Real.log N := by
    field_simp
  rw [hrhs]
  exact hnum

/-- **The bound at the doubled frequency.**  For `σ ≥ 1` and `|γ| ≥ 1` the pole term is harmless,
so `B₀ = 5/2 + log N` works. -/
theorem norm_riemannZeta_double_le {σ γ : ℝ} {N : ℕ} (hσ : 1 ≤ σ) (hγ : 1 ≤ |γ|)
    (hN : 1 ≤ N) (hNw : ‖(σ : ℂ) + (2 * γ : ℂ) * Complex.I‖ ≤ (N : ℝ))
    (hne : (σ : ℂ) + (2 * γ : ℂ) * Complex.I ≠ 1) :
    ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ 5 / 2 + Real.log N := by
  have hre : ((σ : ℂ) + (2 * γ : ℂ) * Complex.I).re = σ := by simp
  have hbase := norm_riemannZeta_le_log (w := (σ : ℂ) + (2 * γ : ℂ) * Complex.I)
    (by rw [hre]; exact hσ) hne hN hNw
  have him : ((σ : ℂ) + (2 * γ : ℂ) * Complex.I - 1).im = 2 * γ := by simp
  have hnorm : 2 ≤ ‖(σ : ℂ) + (2 * γ : ℂ) * Complex.I - 1‖ := by
    have h := Complex.abs_im_le_norm ((σ : ℂ) + (2 * γ : ℂ) * Complex.I - 1)
    rw [him] at h
    have habs : (2 : ℝ) ≤ |2 * γ| := by
      rw [abs_mul]
      have : |(2 : ℝ)| = 2 := by norm_num
      rw [this]
      linarith
    linarith
  have hpos : (0 : ℝ) < ‖(σ : ℂ) + (2 * γ : ℂ) * Complex.I - 1‖ := by linarith
  have hinv : 1 / ‖(σ : ℂ) + (2 * γ : ℂ) * Complex.I - 1‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith
  linarith

/-- **The truncation range condition.**  The segment stays inside the disc of radius `2 + |γ|`, so
any `N ≥ 3 + |γ|` covers it. -/
theorem segment_norm_le {β σ γ R : ℝ} {N : ℕ} (hβ0 : 0 ≤ β) (hβσ : β ≤ σ) (hσ2 : σ ≤ 2)
    (hR : R ≤ 1) (hN : 2 + |γ| + 1 ≤ (N : ℝ)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I))‖ + R ≤ (N : ℝ) := by
  intro t ht
  obtain ⟨hre, him⟩ := segment_re_im β σ γ t
  have hbound := Complex.norm_le_abs_re_add_abs_im
    (((β : ℂ) + (γ : ℂ) * Complex.I)
      + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)))
  rw [hre, him] at hbound
  have hre0 : 0 ≤ β + t * (σ - β) := by nlinarith [ht.1, hβσ, hβ0]
  have hre2 : β + t * (σ - β) ≤ 2 := by nlinarith [ht.1, ht.2, hβσ, hσ2]
  have habs : |β + t * (σ - β)| ≤ 2 := by
    rw [abs_of_nonneg hre0]
    exact hre2
  linarith

/-- A quarter-power comparison. -/
theorem rpow_quarter_lt_of_lt_pow {δ B : ℝ} (hδ0 : 0 < δ) (hB : 0 < B) (h : δ < B ^ (4 : ℕ)) :
    δ ^ ((1 : ℝ) / 4) < B := by
  have hpow : (B ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) = B := by
    rw [← Real.rpow_natCast B 4, ← Real.rpow_mul hB.le]
    norm_num
  calc δ ^ ((1 : ℝ) / 4) < (B ^ (4 : ℕ)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_lt_rpow hδ0.le h (by norm_num)
    _ = B := hpow

/-- **The quarter comparison holds at the `log^{-9}` scale.**  With
`A = (e^{-11/2}·2^{-3/4}·2^{-1/4}/64)^(4 : ℕ)`, any `δ < A/L^(9 : ℕ)` satisfies the comparison, for every
`L ≥ 3` — no further largeness is needed. -/
theorem quarter_comparison {L δ : ℝ} (hL : 3 ≤ L) (hδ0 : 0 < δ)
    (hδ : δ < (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64)
        ^ (4 : ℕ) / L ^ 9) :
    δ ^ ((1 : ℝ) / 4)
      < Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4)
          / (64 * L ^ 2) := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hK : (0 : ℝ) < Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) := by positivity
  have h2L : (5 : ℝ) / 2 + L ≤ 2 * L := by linarith
  have hLpow : (0 : ℝ) < (2 * L) := by linarith
  have hmono : (2 * L) ^ (-(1 : ℝ) / 4) ≤ ((5 : ℝ) / 2 + L) ^ (-(1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h2L (by norm_num)
  have hsplit : (2 * L) ^ (-(1 : ℝ) / 4)
      = (2 : ℝ) ^ (-(1 : ℝ) / 4) * L ^ (-(1 : ℝ) / 4) :=
    Real.mul_rpow (by norm_num) hL0.le
  have hLneg : L ^ (-(1 : ℝ) / 4) = 1 / L ^ ((1 : ℝ) / 4) := by
    rw [show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg hL0.le]
    exact (one_div _).symm
  set K : ℝ := Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) with hKdef
  have hKpos : (0 : ℝ) < K := by positivity
  have hL9 : (L ^ ((9 : ℝ) / 4)) ^ (4 : ℕ) = L ^ (9 : ℕ) := by
    rw [← Real.rpow_natCast (L ^ ((9 : ℝ) / 4)) 4, ← Real.rpow_mul hL0.le,
      ← Real.rpow_natCast L 9]
    norm_num
  have hstep : ((K / 64) / L ^ ((9 : ℝ) / 4)) ^ (4 : ℕ) = (K / 64) ^ (4 : ℕ) / L ^ 9 := by
    rw [div_pow, hL9]
  have hL94 : L ^ ((9 : ℝ) / 4) = L ^ ((1 : ℝ) / 4) * L ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast L 2, ← Real.rpow_add hL0]
    norm_num
  have hBle : (K / 64) / L ^ ((9 : ℝ) / 4)
      ≤ Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4)
          / (64 * L ^ 2) := by
    have hcancel : (2 : ℝ) ^ (-(1 : ℝ) / 4) * (L ^ ((1 : ℝ) / 4))⁻¹
        = (2 * L) ^ (-(1 : ℝ) / 4) := by
      rw [hsplit, hLneg]
      field_simp
    have hkey : (2 : ℝ) ^ (-(1 : ℝ) / 4) * (L ^ ((1 : ℝ) / 4))⁻¹
        ≤ (5 / 2 + L) ^ (-(1 : ℝ) / 4) := by
      rw [hcancel]
      exact hmono
    have hpos1 : (0 : ℝ) < L ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hL0 _
    have hform : (K / 64) / L ^ ((9 : ℝ) / 4)
        = (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4))
            * ((2 : ℝ) ^ (-(1 : ℝ) / 4) * (L ^ ((1 : ℝ) / 4))⁻¹) / (64 * L ^ 2) := by
      rw [hKdef, hL94]
      field_simp
    rw [hform]
    have hrhs : Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4)
        / (64 * L ^ 2)
        = (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4)) * ((5 / 2 + L) ^ (-(1 : ℝ) / 4))
            / (64 * L ^ 2) := by ring
    rw [hrhs]
    gcongr
  have h4 : ((K / 64) / L ^ ((9 : ℝ) / 4)) ^ (4 : ℕ)
      ≤ (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (5 / 2 + L) ^ (-(1 : ℝ) / 4)
          / (64 * L ^ 2)) ^ (4 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hBle 4
  refine rpow_quarter_lt_of_lt_pow hδ0 (by positivity) ?_
  exact lt_of_lt_of_le hδ (le_trans hstep.ge h4)

/-- **A zero-free region for the Riemann zeta function.**  Every hypothesis is arithmetic in `N`,
`|γ|`, `β` and `σ`; all the analytic content is supplied by the lemmas above. -/
theorem riemannZeta_ne_zero_zero_free {β σ γ : ℝ} {N : ℕ}
    (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N) (hγ : 1 ≤ |γ|)
    (hNbig : 2 + |γ| + 1 ≤ (N : ℝ)) (hNw : ‖(σ : ℂ) + (2 * γ : ℂ) * Complex.I‖ ≤ (N : ℝ))
    (hclose : 1 - 3 / (4 * Real.log N) ≤ β) (hβ0 : 0 ≤ β)
    (hβσ : β ≤ σ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hgap : σ - β ≤ 2 * (σ - 1))
    (hδ : σ - 1
      < (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64) ^ (4 : ℕ)
          / (Real.log N) ^ 9) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  have hlog : 0 < Real.log N := by linarith
  have hR : 1 / (4 * Real.log N) ≤ 1 / 12 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hRγ : 1 / (4 * Real.log N) < |γ| := by linarith
  have hne1 : (σ : ℂ) + (2 * γ : ℂ) * Complex.I ≠ 1 := by
    intro hcon
    have him : ((σ : ℂ) + (2 * γ : ℂ) * Complex.I).im = 2 * γ := by simp
    rw [hcon] at him
    simp only [Complex.one_im] at him
    rcases abs_cases γ with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have hneseg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1 := by
    intro t _ hcon
    obtain ⟨_, him⟩ := segment_re_im β σ γ t
    rw [hcon] at him
    simp only [Complex.one_im] at him
    rcases abs_cases γ with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  refine riemannZeta_ne_zero_of_close hlogN hN hclose hβσ hσ1 (by linarith) (by linarith) hRγ
    (segment_norm_le hβ0 hβσ hσ2 (by linarith) hNbig) hneseg
    (norm_riemannZeta_double_le (by linarith) hγ (by omega) hNw hne1)
    hlog (by norm_num) (deriv_const_le hlogN hγ) hgap
    (by
      have h := quarter_comparison hlogN (by linarith) hδ
      have h64 : (8 : ℝ) * 8 = 64 := by norm_num
      rw [h64]
      exact h)

/-- The absolute constant of the zero-free region. -/
noncomputable def zeroFreeConst : ℝ :=
  (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64) ^ (4 : ℕ)

theorem zeroFreeConst_pos : 0 < zeroFreeConst := by
  rw [zeroFreeConst]
  positivity

theorem zeroFreeConst_le_one : zeroFreeConst ≤ 1 := by
  rw [zeroFreeConst]
  have hbase : Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64
      ≤ 1 := by
    have h1 : Real.exp (-22 / 4) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      norm_num
    have h2 : (2 : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have h3 : (2 : ℝ) ^ (-(1 : ℝ) / 4) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have h1' : (0 : ℝ) < Real.exp (-22 / 4) := Real.exp_pos _
    have h2' : (0 : ℝ) < (2 : ℝ) ^ (-(3 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    have h3' : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
    rw [div_le_one (by norm_num)]
    have hp1 : Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) ≤ 1 := by
      nlinarith [h1, h2, h1', h2']
    have hp1' : (0 : ℝ) < Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) := mul_pos h1' h2'
    have hp2 : Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) ≤ 1 := by
      nlinarith [hp1, h3, h3', hp1']
    linarith
  have hnn : (0 : ℝ) ≤ Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4)
      * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64 := by positivity
  calc (Real.exp (-22 / 4) * (2 : ℝ) ^ (-(3 : ℝ) / 4) * (2 : ℝ) ^ (-(1 : ℝ) / 4) / 64) ^ (4 : ℕ)
      ≤ 1 ^ (4 : ℕ) := pow_le_pow_left₀ hnn hbase 4
    _ = 1 := one_pow 4

/-- **The zero-free region.**  `ζ` has no zero with `1 − c/log⁹N < β ≤ 1` at height `γ`, whenever
`N` is at least `3 + 2|γ|` and `log N ≥ 3`. -/
theorem riemannZeta_ne_zero_of_re_gt {β γ : ℝ} {N : ℕ}
    (hlogN : 3 ≤ Real.log N) (hN : 2 ≤ N) (hγ : 1 ≤ |γ|)
    (hNbig : 3 + 2 * |γ| ≤ (N : ℝ)) (hβ1 : β ≤ 1)
    (hβgt : 1 - zeroFreeConst / (2 * (Real.log N) ^ 9) < β) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  have hlog : 0 < Real.log N := by linarith
  have hL9 : (27 : ℝ) ≤ (Real.log N) ^ 9 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ (Real.log N) ^ 3 := by gcongr
      _ ≤ (Real.log N) ^ 9 := by
        refine pow_le_pow_right₀ (by linarith) (by norm_num)
  have hL9pos : (0 : ℝ) < (Real.log N) ^ 9 := by linarith
  have hcpos := zeroFreeConst_pos
  have hcle := zeroFreeConst_le_one
  set δ : ℝ := zeroFreeConst / (2 * (Real.log N) ^ 9) with hδdef
  have hδpos : 0 < δ := by positivity
  have hδsmall : δ ≤ 1 / 54 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL9, hcle, hcpos]
  refine riemannZeta_ne_zero_zero_free (σ := 1 + δ) hlogN hN hγ (by linarith) ?_ ?_ ?_
    (by linarith) (by linarith) (by linarith) (by linarith) ?_
  · -- ‖σ + 2iγ‖ ≤ N
    have hb := Complex.norm_le_abs_re_add_abs_im (((1 + δ : ℝ) : ℂ) + (2 * γ : ℂ) * Complex.I)
    have hre : (((1 + δ : ℝ) : ℂ) + (2 * γ : ℂ) * Complex.I).re = 1 + δ := by simp
    have him : (((1 + δ : ℝ) : ℂ) + (2 * γ : ℂ) * Complex.I).im = 2 * γ := by simp
    rw [hre, him] at hb
    have h1 : |1 + δ| = 1 + δ := abs_of_nonneg (by linarith)
    have h2 : |2 * γ| = 2 * |γ| := by rw [abs_mul]; norm_num
    rw [h1, h2] at hb
    linarith
  · -- 1 − 3/(4 log N) ≤ β
    have hLL : Real.log N ≤ (Real.log N) ^ 9 := by
      calc Real.log N = (Real.log N) ^ 1 := (pow_one _).symm
        _ ≤ (Real.log N) ^ 9 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hkey : δ ≤ 3 / (4 * Real.log N) := by
      rw [hδdef, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hLL, hcle, hcpos, hlog]
    linarith
  · linarith
  · -- σ − 1 < zeroFreeConst / log⁹N
    have : δ < zeroFreeConst / (Real.log N) ^ 9 := by
      rw [hδdef, div_lt_div_iff₀ (by positivity) hL9pos]
      nlinarith [hcpos, hL9pos]
    simpa [zeroFreeConst] using this

/-- **A quantitative lower bound for `‖ζ‖` left of the abscissa.**  The lower bound at `σ > 1`
survives moving left, provided the derivative bound times the distance is at most half of it.  This
is what a polynomial bound for `1/ζ` on a truncated rectangle needs. -/
theorem le_norm_riemannZeta_left {β σ γ M B₀ : ℝ} (hσ1 : 1 < σ)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv riemannZeta (((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)))‖ ≤ M)
    (hβσ : β ≤ σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hhalf : M * (σ - β)
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) / 2) :
    Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) / 2
      ≤ ‖riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖ := by
  have hlow := exp_le_norm_riemannZeta_shift hσ1 hB
  have hdist : ‖((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)‖ = σ - β := by
    have hrw : ((σ : ℂ) + (γ : ℂ) * Complex.I) - ((β : ℂ) + (γ : ℂ) * Complex.I)
        = ((σ - β : ℝ) : ℂ) := by push_cast; ring
    rw [hrw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hsub := norm_riemannZeta_sub_le hne hM
  rw [hdist, mul_one] at hsub
  have htri : ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
      ≤ ‖riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖
        + ‖riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
            - riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖ := by
    have h := norm_add_le (riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I))
      (riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)
        - riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I))
    simpa using h
  linarith

/-- **The reciprocal bound left of the abscissa.**  This is the `hFbd` hypothesis that the truncated
contour shift needs for `F = 1/ζ`. -/
theorem norm_inv_riemannZeta_left_le {β σ γ M B₀ : ℝ} (hσ1 : 1 < σ)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)) ≠ 1)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖deriv riemannZeta (((β : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - ((β : ℂ) + (γ : ℂ) * Complex.I)))‖ ≤ M)
    (hβσ : β ≤ σ)
    (hB : ‖riemannZeta ((σ : ℂ) + (2 * γ : ℂ) * Complex.I)‖ ≤ B₀)
    (hhalf : M * (σ - β)
      ≤ Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) / 2) :
    ‖(riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I))⁻¹‖
      ≤ 2 / Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) := by
  have hlow := le_norm_riemannZeta_left hσ1 hne hM hβσ hB hhalf
  have hexp : (0 : ℝ)
      < Real.exp ((-22 - 3 * Real.log (1 + 1 / (σ - 1)) - Real.log B₀) / 4) := Real.exp_pos _
  have hzpos : 0 < ‖riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I)‖ := by linarith
  rw [norm_inv, inv_le_iff_one_le_mul₀ hzpos]
  rw [div_mul_eq_mul_div, le_div_iff₀ hexp]
  linarith

end RHTower.Sieve
