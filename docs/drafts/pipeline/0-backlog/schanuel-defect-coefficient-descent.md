# Schanuel defect coefficient descent

- **ID:** schanuel-defect-coefficient-descent
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** `schanuel-logarithmic-differential-defect-lattice.md`; Ax--Kirby differential-form proof
- **Statement:** Defect forms of every `Q`-linearly independent numerical exponential tuple are linearly independent over their value field.

## Goal

Prove Schanuel by converting its transcendence-degree bound into a coefficient-descent theorem for
closed logarithmic differentials.  This is stronger than a reformulation: it identifies the exact
step present in Ax's differential theorem and absent for numerical values.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3  formalized: exact theorem only after paper proof
- [ ] 3 -> 4  publication-ready: independent hostile and literature review

## Conjecture DCD

Let `x_1,...,x_n` be `Q`-linearly independent complex numbers, `y_i=exp(x_i)`, and

\[
  K=\overline{\mathbb Q}(x_1,\ldots,x_n,y_1,\ldots,y_n).
\]

Then the forms

\[
  \epsilon_i=dy_i/y_i-dx_i\in\Omega_{K/\overline{\mathbb Q}}
\]

are `K`-linearly independent.

## Immediate implication

If DCD holds, then

\[
 n\leq\dim_K\Omega_{K/\overline{\mathbb Q}}
   =\operatorname{trdeg}_{\mathbb Q}K,
\]

which is Schanuel's conjecture.

## Boundary checks

1. `n=1`: proved by the defect-lattice theorem; a single defect cannot vanish.
2. All `x_i` algebraic: `dx_i=0`, so DCD is independence of `dlog(y_i)`; classical
   Lindemann--Weierstrass gives algebraic independence of the exponentials and closes this slice.
3. All `y_i` algebraic: `dy_i=0`, so DCD is independence of `dx_i`; this is exactly algebraic
   independence of logarithms of algebraic numbers, already open for two inputs.
4. Therefore DCD is not accessible by a proof using only formal properties of closed forms or
   valuations; such a proof would solve the known logarithm-specialized Schanuel problem.

## Ax comparison

In Ax--Kirby, a minimal `F`-linear dependence among the same invariant forms is differentiated by a
distinguished derivation `D`.  The hypotheses `D^* epsilon_i=0` and `d epsilon_i=0` force every
minimal coefficient into the constant field.  For a numerical tuple, universal derivations satisfy
neither `D^* epsilon_i=0` nor an equivalent common-annihilator condition.  Importing Ax without
constructing that condition is circular.

## Attack plan

1. Derive all consequences of closedness for a minimal dependence
   `sum a_i epsilon_i=0`; in rank two this gives `d rho wedge epsilon_1=0` for the defect slope
   `rho=epsilon_2/epsilon_1`.
2. Use divisor residues `res_P(epsilon_i)=ord_P(y_i) in Z` and higher pole orders from `dx_i` to
   test whether the coefficient field can descend from `K` to `Qbar`.
3. Hostile-test every descent claim on the log-algebraic slice, where it must specialize to the
   known open algebraic-independence-of-logarithms problem rather than silently assume it.
4. Compare any resulting singular coefficient matrix with Structural Rank/MCC.  Reject the bridge
   unless its entries are genuinely logarithms of algebraic numbers; abstract function-field
   residues alone do not meet that type.

## Current hostile verdict

- Descent to `Qbar` is now proved unconditionally in
  `schanuel-defects-algebraic-coefficient-independent.md`, using invariant-form subgroup closure and
  Baker. This is the strongest positive survivor.
- Closedness alone gives integrability, not descent from `K` to `Qbar`.
- Residues are integral only at divisor poles; coefficients may have poles and can absorb higher
  principal parts.
- Matrix Coefficient Conjecture currently applies only to logarithms of algebraic numbers and cannot
  consume arbitrary `x_i` or abstract defect slopes.
- On a stage-two counterexample the defect span fills the entire one-dimensional cotangent space, so
  its annihilator contains no nonzero derivation. The Ax continuation therefore stops before it can
  create a common exponential derivation.
- DCD remains a sufficient conjecture but has no non-circular route beyond the proved `Qbar` floor;
  it returns to backlog while the canonical stage-two defect-slope normal form becomes active.

## Log

- 2026-08-14 -- conjecture frozen; implications and three category-error guards verified.
- 2026-08-14 -- algebraic-coefficient floor proved; Ax-annihilator continuation killed at a
  defect-saturated stage-two counterexample; card returned to backlog.
