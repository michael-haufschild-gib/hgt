# Seam-Log Complete Monotonicity Is Insufficient

- **ID:** seam-log-complete-monotonicity-insufficient
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / analytic shortcut guardrail
- **Source:** `seam-log-markov-pick-rh-equivalence.md`
- **Statement:** Complete monotonicity of the real-axis function `G(-s)` is not enough
  to imply a Markov/Stieltjes representation. The seam-log target requires the
  stricter Stieltjes square-test cone.

## Setup

If the seam-log Markov target holds, then

`G(x)=int_{R_+} 1/(1-xy) dnu(y)`.

On the positive real half-line, setting `x=-s` gives

`H(s)=G(-s)=int_{R_+} 1/(1+sy) dnu(y)`.

Such an `H` is completely monotone:

`(-1)^n H^(n)(s) >= 0`, `s>0`, `n>=0`.

The converse is false.

## Theorem

There exists a completely monotone function `H` on `(0,infty)`, analytic at `0`, whose
Taylor coefficients at `0` have the alternating signs required by complete monotonicity,
but whose coefficient sequence is not a Stieltjes moment sequence. Hence complete
monotonicity does not imply the seam-log Markov/Pick target.

## Proof

Take

`H(s)=exp(-s)`.

It is completely monotone because

`(-1)^n H^(n)(s)=exp(-s)>0`

for every `n>=0` and every `s>0`.

Its Taylor expansion is

`H(s)=sum_{n>=0} (-1)^n s^n/n!`.

If `H` were of the Markov form

`H(s)=int_{R_+} 1/(1+sy) dnu(y)`

near `s=0`, then the coefficient sequence

`m_n=1/n!`

would satisfy the Stieltjes Hankel positivity conditions:

`[m_{i+j}]_{i,j>=0} >= 0`.

But the first `2 x 2` Hankel determinant is

`det [[m_0,m_1],[m_1,m_2]] = det [[1,1],[1,1/2]] = -1/2 < 0`.

Therefore no positive measure on `R_+` has moments `m_n=1/n!`, and `exp(-s)` is not a
Markov/Stieltjes transform of the required kind.

## Consequence for the RH Route

For the seam-log source function

`H_src(s)=G_src(-s)`,

proving complete monotonicity on `s>0` is not enough. It proves only a Laplace-type
positivity shadow. The RH-equivalent target is stricter: `H_src` must be a Stieltjes
function, equivalently its moment coefficients must satisfy every Hankel square test.

Thus a proposed source proof cannot stop at alternating derivative signs on the
positive real axis. It must prove the Markov/Stieltjes representation or the full
Hankel cone.

## Source Boundary

This is an elementary counterexample. It does not touch `xi`; it blocks a weaker
analytic replacement for the Markov/Pick target.

## Gates

- [x] 0 -> 1 in-progress: complete-monotonicity shortcut isolated.
- [x] 1 -> 2 fully-proven: explicit completely monotone non-Stieltjes example.
- [x] 2 -> 3 formalized: analyticity, all alternating derivative signs, reciprocal-factorial
  Taylor coefficients, the negative Hankel determinant, and nonexistence of a positive
  representing measure are proved by
  `exists_analytic_strictlyCompletelyMonotone_nonStieltjesTaylor` in
  `formal/GaloisForLFunctions/HTGeometry/HankelGuardrailCounterexamples.lean`.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal. It records that
  complete monotonicity is only a necessary shadow of the seam-log Markov target, not
  a substitute for Stieltjes positivity.
