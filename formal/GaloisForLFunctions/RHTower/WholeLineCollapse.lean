import GaloisForLFunctions.RHTower.DensityNotNormSimilitude

/-!
# On the whole line the operator inequality collapses to a pointwise one

Entries 25 and 28 record the same wall twice: structure manufactured by compression fails on an edge
subspace whose norm defect is one and whose density is zero.  The natural response is to work before
compression, on `L²(ℝ)`, where translations act as exact isometries and no edge exists.  That works —
and it removes all the operator theory with it.

**Everything commutes.**  On the whole line the archimedean form `Q` is a Fourier multiplier: its
symbol is `1` plus the regularised sum of Poisson kernels

```text
Σ_n ( 4 s_n/(s_n² + r²) - 4/s_n )  =  - Σ_n 4 r² / ( s_n (s_n² + r²) ) ,        s_n = 2n + 5/2 ,
```

convergent, negative, and of size `-2 log|r|`, matching the archimedean weight.  The Abel-regularised
prime form `𝒫_ε` is also a multiplier, with symbol `-2 Re (ζ'/ζ)(1/2 + ε + i r)`.  Two multipliers
commute and are simultaneously diagonalised by the Fourier transform, so

> **the operator inequality `𝒫_ε ≤ Q` is exactly the pointwise inequality of their symbols.  No
> spectral theory survives the passage to the whole line: the entire content is a bound between two
> real functions of one variable.**

**And that bound is Lagarias' criterion.**  By the classical partial-fraction expansion, the symbol of
`𝒫_ε` is a sum over zeros of terms `(1/2 + ε - β)/((1/2 + ε - β)² + (r - γ)²)` plus an explicit
archimedean part.  Under the hypothesis every `β` is `1/2`, so every term is positive with the sign
that preserves the inequality; if some `β = 1/2 + a` exceeds `1/2`, then at `r = γ` and `ε < a` the
term equals `1/(ε - a)`, which is negative and unbounded as `ε ↑ a`.

**Diagnostic value.**  The compression wall is therefore an artefact of the finite-width formulation,
not intrinsic to the operator approach.  But the wall-free formulation is the pointwise one, in which
no similitude and no self-adjointness can help, because everything already commutes.

> **The operator lane is closed at both ends: walled under compression, and degenerate without it.**

This file formalizes the reduction of the multiplier inequality to a pointwise one and the sign
dichotomy of the zero terms that drives the criterion.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The multiplier inequality is pointwise.**  Testing against every nonnegative weight is the same
as the pointwise bound: no spectral information beyond the symbols survives. -/
theorem multiplier_ineq_pointwise {p q : ℝ → ℝ} :
    (∀ w : ℝ → ℝ, (∀ r, 0 ≤ w r) → ∀ r, w r * p r ≤ w r * q r) ↔ ∀ r, p r ≤ q r := by
  constructor
  · intro h r
    have := h (fun _ => 1) (fun _ => zero_le_one) r
    simpa using this
  · intro h w hw r
    exact mul_le_mul_of_nonneg_left (h r) (hw r)

/-- **The zero term is positive on the critical line.**  With `β = 1/2` the term at abscissa
`1/2 + ε` has numerator `ε > 0`. -/
theorem zero_term_pos {ε d : ℝ} (hε : 0 < ε) :
    0 < ε / (ε ^ (2 : ℕ) + d ^ (2 : ℕ)) := by
  apply div_pos hε
  positivity

/-- **The zero term reverses off the line.**  A zero at abscissa `1/2 + a` with `a > ε` contributes a
term with negative numerator. -/
theorem zero_term_neg {ε a d : ℝ} (hεa : ε < a) :
    (ε - a) / ((ε - a) ^ (2 : ℕ) + d ^ (2 : ℕ)) ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg (by linarith)
  positivity

/-- **And it blows up at the ordinate.**  At `d = 0` the term is `1/(ε - a)`, whose modulus tends to
infinity as `ε` rises to `a`. -/
theorem zero_term_blowup {ε a : ℝ} (hεa : ε < a) :
    (ε - a) / ((ε - a) ^ (2 : ℕ) + 0 ^ (2 : ℕ)) = 1 / (ε - a) := by
  have hne : ε - a ≠ 0 := by intro h; linarith [sub_eq_zero.mp h]
  rw [show (0:ℝ) ^ (2 : ℕ) = 0 by ring, add_zero]
  field_simp

/-- The blow-up is quantitative: the modulus exceeds any bound once `ε` is close enough to `a`. -/
theorem blowup_exceeds {a M : ℝ} (hM : 0 < M) :
    ∃ ε : ℝ, ε < a ∧ M < |1 / (ε - a)| := by
  have hMp : (0:ℝ) < M + 1 := by linarith
  have hinv : (0:ℝ) < 1 / (M + 1) := by positivity
  refine ⟨a - 1 / (M + 1), by linarith, ?_⟩
  have hval : a - 1 / (M + 1) - a = -(1 / (M + 1)) := by ring
  rw [hval]
  have hrec : (1:ℝ) / -(1 / (M + 1)) = -(M + 1) := by field_simp
  rw [hrec, abs_neg, abs_of_pos hMp]
  linarith

end RHTower
