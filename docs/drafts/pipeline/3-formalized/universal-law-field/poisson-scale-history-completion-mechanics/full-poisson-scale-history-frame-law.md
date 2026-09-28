# Full Poisson scale-history frame law

- **ID:** ULF-PSH-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN-PROVED] [PRE-DIVISOR] [NOT RH]`
- **Lean:** `RHTower.PoissonScaleHistoryFrame`

## Statement

For a positive orbital clock `t`, define its full positive-aperture Poisson half-density history

\[
 \psi_t(a)=2t\sqrt a\,e^{-ta},\qquad a>0.
\]

Then every clock has unit history mass and every pair has the exact Gram coefficient

\[
 \langle\psi_t,\psi_u\rangle
 =\int_0^\infty4tu\,a e^{-(t+u)a}\,da
 =\frac{4tu}{(t+u)^2}
 =\operatorname{sech}^2\!\left(\frac{\log t-\log u}{2}\right).
\]

Consequently `0 < <psi_t,psi_u> <= 1`, with equality to one exactly when `t=u`.

Under logarithmic aperture `a=e^x` and its half-density Jacobian, put

\[
 \widetilde\psi_t(x)=e^{x/2}\psi_t(e^x),\qquad
 F(x)=2e^x e^{-e^x}.
\]

Then

\[
 \boxed{\widetilde\psi_t(x)=F(x+\log t).}
\]

Thus all clocks form one literal translation orbit; the `sech^2` kernel is its stationary
autocorrelation.

## Proof

For `c>0`, the first Laplace moment is

\[
 \int_0^\infty a e^{-ca}\,da=c^{-2}.
\]

Use `c=t+u` to obtain the rational kernel.  Setting `u=t` gives unit mass.  Moreover

\[
 (t+u)^2-4tu=(t-u)^2,
\]

which gives the upper bound and equality classification.  Finally

\[
 \cosh^2\!\left(\frac{\log(t/u)}2\right)=\frac{(t+u)^2}{4tu},
\]

giving the hyperbolic form.  QED.

## Interpretation and boundary

For the literal Euler clock `t=m log p`, horizontal differentiation supplies the orbital factor
`m log p`; the full Poisson history normalizes that unbounded clock without changing the external
Euler amplitude `p^{-m/2}/m`.  Thus cross-aperture coupling is not free data: integer/Poisson
formation forces the `sech^2` log-clock kernel.

This does **not** remove the all-prime principal-shell divergence: unsquared amplitudes still have
squared principal mass `sum_p 1/p`.  Nor should that class be subtracted: the corpus polarity
theorem shows fixed principal subtraction selects nonneutral grade.  The frame instead realizes
the harmonic class as translation-escape mass.  A completion theorem must retain its oriented
nonreduced class while transporting bulk divergence to a boundary law.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.PoissonScaleHistoryFrame`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.RHTower.PoissonScaleHistoryFrame` (15 constants, axiom audit clean).

| Claim | Lean declaration |
|-|-|
| History `ψ_t(a) = 2t√a e^{-ta}` and Gram pairing | `poissonScaleHistory`, `poissonScaleHistoryGram` |
| First Laplace moment `∫ a e^{-ca} = c^{-2}` and `⟨ψ_t, ψ_u⟩ = 4tu/(t+u)²` | `poissonScaleHistoryGram_eq` (via mathlib `integral_Ioi_id_mul_exp_neg_mul`) |
| Unit history mass | `poissonScaleHistoryGram_self` |
| `0 < ⟨ψ_t, ψ_u⟩` | `poissonScaleHistoryGram_pos` |
| `⟨ψ_t, ψ_u⟩ ≤ 1` | `poissonScaleHistoryGram_le_one` |
| Equality to one exactly when `t = u` | `poissonScaleHistoryGram_eq_one_iff` |
| `⟨ψ_t, ψ_u⟩ = sech²((log t − log u)/2)` | `poissonScaleHistoryGram_eq_inv_cosh_sq` |
| `F(x) = 2eˣe^{-eˣ}`, `ψ̃_t(x) = e^{x/2}ψ_t(eˣ) = F(x + log t)` | `poissonLogScaleMother`, `poissonLogScaleHistory`, `poissonLogScaleHistory_eq_translate` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
