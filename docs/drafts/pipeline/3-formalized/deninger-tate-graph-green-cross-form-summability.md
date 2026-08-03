# Tate graph controls the all-prime Green cross form

- **ID:** `deninger-tate-graph-green-cross-form-summability`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean direct check)
- **Label:** `DAC_TATE_GRAPH_GREEN_CROSS_FORM_SUMMABILITY`
- **Parent:** `deninger-tate-graph-green-prime-sector`
- **Scientific status:** `[NEW ARITHMETIC FORM-LEVEL CLOSURE; HOLDER PARENT STANDARD]`
- **Statement:** weighted Tate graph summability in both variables makes
  the unsmoothed finite-prime oscillatory Green cross form absolutely
  summable and uniformly bounded by the two graph energies; this closes
  that sector of all-place Green-form nuclear summability.

## Theorem

Let (I) index finite-prime oscillatory modes.  For (i\in I), let

\[
 L_i\ge c>0,qquad \lambda_i\ge0,qquad
 x_i,y_i\ge0,                                                \tag{1}
\]

where (x_i,y_i) are squared mode amplitudes.  Put

\[
 W_i(z)=L_i^2(1+\lambda_i)z.                                 \tag{2}
\]

Assume

\[
 \sum_iW_i(x_i)<\infty,
 \qquad
 \sum_iW_i(y_i)<\infty.                                    \tag{3}
\]

Then

\[
 \sum_i\sqrt{\lambda_ix_i}\sqrt{\lambda_iy_i}<\infty       \tag{4}
\]

and

\[
 \sum_i\sqrt{\lambda_ix_i}\sqrt{\lambda_iy_i}
 \le
 \sqrt{\sum_i c^{-2}W_i(x_i)}
 \sqrt{\sum_i c^{-2}W_i(y_i)}.                              \tag{5}
\]

For Deninger prime packets, (L_i=\log p_i) and
(c=\log2).  Therefore the unsmoothed Green cross form on the
all-prime oscillatory sector extends continuously to the weighted Tate
graph completion.

## Proof

The graph majorant from
`DAC_TATE_GRAPH_GREEN_PRIME_SECTOR` gives termwise

\[
 \lambda_i z\le c^{-2}W_i(z),\qquad z\ge0.                  \tag{6}
\]

Thus both energy sequences
((\lambda_ix_i)) and ((\lambda_iy_i)) are summable.  Arithmetic--
geometric mean gives

\[
 \sqrt{\lambda_ix_i}\sqrt{\lambda_iy_i}
 \le {\lambda_ix_i+\lambda_iy_i\over2},                    \tag{7}
\]

proving absolute summability `(4)`.  Holder/Cauchy--Schwarz for
series gives

\[
 \sum_i\sqrt{\lambda_ix_i}\sqrt{\lambda_iy_i}
 \le
 \sqrt{\sum_i\lambda_ix_i}
 \sqrt{\sum_i\lambda_iy_i}.                                \tag{8}
\]

Apply `(6)` under both sums and monotonicity of square root to obtain
`(5)`.

For actual complex mode coefficients (a_i,b_i), absolute value of
the sesquilinear Green term is at most
(sqrt{\lambda_i|a_i|^2}\sqrt{\lambda_i|b_i|^2}), so `(4)`--`(5)`
give absolute convergence and the asserted continuous extension.

## Route-L consequence

The conjecture
`DAC_ALL_PLACE_GREEN_FORM_NUCLEAR_SUMMABILITY` has no remaining
summability debt on the uncoupled finite-prime oscillatory sector once
its defining Banach disk is bounded in the Tate graph norm.  This is a
form-level result: it controls cross terms required for a continuous
bilinear/sesquilinear Green form, not only diagonal energy.

## Hostile scope audit

- The theorem does not construct global Milnor-incidence cross terms.
- It does not control horizontal residue evaluation; the pro-log
  holomorphic factor remains mandatory.
- It does not prove a Banach disk of the full arithmetic coefficient is
  bounded in the graph norm.  That belongs to projective graph
  strictness.
- It does not classify the global radical or compare Green form with
  Paugam cup trace.
- No Xi divisor, zero, RH premise, or numerical calculation occurs.

## Lean

In `GaloisForLFunctions.RHTower.DeningerTateGraphGreenPrimeSector`:

- `deningerTateGraphCrossEnergy_summable`, `deningerTateGraphCrossEnergy_tsum_le`,
  `deningerTateGraphCrossEnergy_tsum_le_graph` formalize `(4)`, `(8)` and `(5)` for the
  nonnegative squared amplitudes.
- `deningerGreenCrossTerm` is the actual sesquilinear Green cross term
  `λ_i \overline{a_i} b_i` of two complex mode families, and `deningerGreenCrossTerm_norm`
  proves its modulus is exactly `√(λ_i|a_i|²)·√(λ_i|b_i|²)`, which is the last paragraph of the
  proof.  `deningerGreenCrossTerm_summable` is therefore the absolute convergence of the Green
  series, and `deningerGreenCrossForm_norm_tsum_le` is the uniform graph bound
  `‖∑_i λ_i \overline{a_i} b_i‖ ≤ √(∑ c^{-2}W_i(|a_i|²))·√(∑ c^{-2}W_i(|b_i|²))` — the
  continuous extension of the form to the weighted Tate graph completion.

Module builds under `lake build`; axiom audit for all seven declarations:
`propext, Classical.choice, Quot.sound`.

## Next exact claim

`[CONJECTURE] [DAC_MILNOR_INCIDENCE_GREEN_CROSS_FORM]`

Construct source-defined off-diagonal Green terms for the relative
Milnor/Sullivan incidence directions and prove they satisfy compatible
projective graph bounds.  Orthogonal ray sums are forbidden by the
existing scalar-collapse no-go.

## Gates

- [x] dependency-closed paper proof
- [x] exact all-prime bound
- [x] Lean declarations
- [x] foreground direct-file check
- [x] targeted cached module audit
- [ ] Milnor-incidence cross form *(successor conjecture, not this theorem)*

## Log

- 2026-08-01 — Upgraded diagonal graph control to absolute
  all-prime cross-form summability and a uniform graph Cauchy--Schwarz
  bound.
- 2026-08-02 — Formalized the sesquilinear layer the paper proof's last
  paragraph asserts: the complex Green cross term, the exact identity for its
  modulus, its absolute summability, and the uniform graph bound on the summed
  form.  Module built and axiom-audited.

### Log

- 2026-08-03 — Verified rather than re-derived: all seven declarations named in the Lean section
  exist, type-check, and audit to `propext, Classical.choice, Quot.sound`, and their statements are
  the card's `(4)`, `(8)`, `(5)` and the sesquilinear extension.  Card moved to 3-formalized.
