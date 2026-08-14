# Canonical defect-slope normal form for a stage-two counterexample

- **ID:** schanuel-stage-two-defect-slope-normal-form
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** algebraic-coefficient defect theorem + Kirby exponential algebraicity
- **Statement:** Any stage-two Schanuel counterexample is a one-variable algebraic-function system with a canonical transcendental, exponentially algebraic defect slope and fixed algebraic-endpoint regulator values.

## Goal

Replace an amorphous four-number algebraic-dependence failure by one canonical one-variable object.
This is the strongest non-circular normal form obtained after the Ax-lift and constant-coefficient
descent attacks.

## Gates

- [x] 0 -> 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 -> 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3  formalized: depends on formal algebraic-coefficient defect theorem
- [ ] 3 -> 4  publication-ready: external novelty and independent proof audit pending

## Statement

Assume `x_1,x_2` are `Q`-linearly independent and

\[
 K=\overline{\mathbb Q}(x_1,x_2,e^{x_1},e^{x_2})
\]

has transcendence degree less than two.  Put `y_i=e^{x_i}` and
`epsilon_i=dy_i/y_i-dx_i` in `Omega_{K/Qbar}`.  Then:

1. `trdeg_Qbar K=1`;
2. there is a unique `rho in K` with `epsilon_2=rho epsilon_1`;
3. `rho` is transcendental over `Qbar`, so `K/Qbar(rho)` is finite;
4. the tuple is an essential counterexample, and `rho` lies in the countable
   exponential-algebraic closure `ecl^C(emptyset)`;
5. on the normalized projective curve `V/Qbar` with function field `K`, for every algebraic smooth
   base point `q` avoiding coordinate poles and zeroes, and every path from `q` to the complex point
   `p=(x,y)`, suitable logarithm branches give

\[
 \int_q^p\epsilon_i=X_i(q)-\log Y_i(q)+2\pi i k_i,\qquad k_i\in\mathbb Z. \tag{R}
\]

Thus a first counterexample is controlled by a transcendental exponentially algebraic slope and a
pair of length-one exponential-period regulator values at algebraic endpoints.

## Proof

Hermite--Lindemann rules out `trdeg K=0`, so a counterexample has `trdeg K=1`.  Therefore
`Omega_{K/Qbar}` is one-dimensional over `K`.  The defect-lattice theorem makes each `epsilon_i`
nonzero, giving a unique quotient `rho=epsilon_2/epsilon_1`.

Algebraic-coefficient independence of the defects rules out `rho in Qbar`.  Hence `rho` is
transcendental and is a transcendence basis of the one-variable function field, so `K` is finite
over `Qbar(rho)`.

For stage two, every proper nonzero rational subspace has dimension one and satisfies Schanuel by
Hermite--Lindemann; every rank-two tuple in the same rational span has transcendence degree at least
one. Hence the counterexample is essential in Kirby's sense. Kirby's theorem places it in
`ecl^C(emptyset)`.  Exponential algebraic closure is an algebraically closed exponential subfield;
it contains `K` and therefore `rho`.

Finally, write the coordinate functions on `V` as `X_i,Y_i`.  Direct integration gives

\[
 \int_q^p(d\log Y_i-dX_i)
 =\log\!\frac{Y_i(p)}{Y_i(q)}-(X_i(p)-X_i(q)).
\]

Using `Y_i(p)=exp(X_i(p))` cancels the transcendental endpoint coordinate and yields (R), with the
integer recording the logarithm branch. **[PROVED HERE]**

## Hostile audit

- The ratio `rho` exists only because the hypothetical value field is a curve; no coordinate choice
  is used.
- Transcendence of `rho` uses the proved algebraic-coefficient floor, not a dimension count over the
  wrong scalar field.
- Kirby supplies countability/exponential algebraicity, not nonexistence; no generic-power theorem
  applies to an exponentially algebraic slope.
- Regulator identity (R) is exact but does not make `p` algebraic. Existing period theorems do not
  control Abelian integrals with a transcendental endpoint.

## Failed continuations

1. **Trace/norm descent.** Applying the finite-field trace to
   `epsilon_2=rho epsilon_1` gives a rational-function differential identity over `Qbar(rho)`, but
   field conjugates do not preserve `Y_i=exp(X_i)`. The value identity is lost exactly where the
   trace would amplify it.
2. **Ax-compatible arc.** A curve through `p` satisfying the exponential differential equation is
   forbidden by the pole-order lemma unless constant.
3. **Generic powers.** The canonical slope lies in exponential algebraic closure, precisely the
   exceptional set excluded by generic-power Schanuel theorems.

## New open core

Prove that no one-variable algebraic-function system over `Qbar(rho)`, with `rho` transcendental and
exponentially algebraic, can realize both regulator specializations (R) at one generic complex point.
Any valid attack must retain the chosen exponential branch under specialization; traces, Galois
conjugation, and function-field Ax theorems erase it.

## Log

- 2026-08-14 -- dependency-closed normal form proved; trace/norm and generic-slope continuations killed.
