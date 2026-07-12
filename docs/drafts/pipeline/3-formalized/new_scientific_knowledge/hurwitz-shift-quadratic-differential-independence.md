# Hurwitz shift quadratic differential independence

- **ID:** `hurwitz-shift-quadratic-differential-independence`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [COROLLARY OF PROJECT-NEW THEOREM]
  [NOVELTY UNVERIFIED]`
- **Statement:** For every nonintegral (s) with (Re s>1), the function
  (a\mapsto\zeta(s,a)) satisfies no nonzero polynomial-coefficient algebraic differential
  relation of total degree at most two, of any finite differential order, on the upper half-plane.

## Exact differential value law

For (a) in the upper half-plane, the project's complex-shift Hurwitz series obeys

\[
 \frac{d}{da}\zeta(s,a)=-s\zeta(s+1,a).
\]

Iterating gives, for every (r\geq0),

\[
 \boxed{
 \frac{d^r}{da^r}\zeta(s,a)
 =(-1)^r(s)_r\zeta(s+r,a),
 }
\]

where ((s)_r=s(s+1)\cdots(s+r-1)).  Since (Re s>1), every coefficient
((-1)^r(s)_r) is nonzero.  Hence the shifted-exponent ladder and the differential jet of the
single base function are related by an invertible diagonal value transform:

\[
 \zeta(s+r,a)
 =\frac{\partial_a^r\zeta(s,a)}{(-1)^r(s)_r}.
\]

The first derivative identity is classical; see
[DLMF 25.11.17](https://dlmf.nist.gov/25.11.E17).  The all-order statement is its iteration.

## Theorem

Fix (N\geq0).  Let (q_{ij},\ell_i,c\in\mathbb C[a]), with (q_{ij}=q_{ji}).  If

\[
 \sum_{i,j=0}^{N}q_{ij}(a)
   \partial_a^i\zeta(s,a)\,\partial_a^j\zeta(s,a)
 +\sum_{i=0}^{N}\ell_i(a)\partial_a^i\zeta(s,a)+c(a)=0
\]

for every (a) in the upper half-plane, then

\[
 q_{ij}=0,\qquad \ell_i=0,\qquad c=0.
\]

Thus (a\mapsto\zeta(s,a)) has no algebraic differential equation of total degree at most two,
at any finite order, with polynomial coefficients.

## Proof

Put (c_i=(-1)^i(s)_i\ne0).  The differential value law rewrites the assumed relation as

\[
 \sum_{i,j}(c_ic_jq_{ij})(a)\zeta(s+i,a)\zeta(s+j,a)
 +\sum_i(c_i\ell_i)(a)\zeta(s+i,a)+c(a)=0.
\]

`HurwitzAllNHZeta.hurwitz_allN_hzeta_upper_half_plane` forces every rescaled coefficient to
vanish.  Cancellation of the nonzero constants (c_i) gives the claimed coefficients.  This is
an invertible change of value coordinates, so no analytic information is lost in passing from
the shifted ladder to the differential jet.

## Lean certificate

`formal/GaloisForLFunctions/Hurwitz/LadderDeformation.lean` proves:

- `hzeta_hasDerivAt` and `hzeta_deriv`;
- `hzeta_iteratedDeriv`;
- `ascPochhammer_eval_ne_zero_of_one_lt_re`;
- `hzeta_shift_eq_iteratedDeriv_div`.

`formal/GaloisForLFunctions/Hurwitz/QuadraticDifferentialIndependence.lean` proves
`HurwitzLadder.hzeta_quadratic_differential_independent`.  The module is imported by the Hurwitz
umbrella.

## Novelty and significance audit

The derivative formula is classical and is classified `[SEARCH] [BRIDGE]`.  The load-bearing
input is the already formalized project-new all-(N) quadratic independence theorem for the
shifted Hurwitz ladder.  The differential theorem is an exact corollary of that result, not an
independent novelty unit.  Searches for Hurwitz-zeta differential algebraic independence mostly
return results in the exponent variable, value-distribution theorems, or formal infinite-order
differential equations; no located source states this finite-order, total-degree-two theorem in
the shift variable.

- **Novelty estimate:** 0.72 as part of the all-(N) Hurwitz package; 0.25 as an independent
  theorem, because the diagonal derivative transform makes it formally equivalent to the parent
  ladder result.
- **Significance estimate:** 0.84.  It converts a multi-function algebraic-independence theorem
  into a recognizable differential-algebraic obstruction for one classical special function.

The positive boundary is exact: the theorem excludes every differential polynomial of total
degree at most two.  Differential degree at least three remains the next value-algebra problem;
the result does not by itself prove hypertranscendence.

## RHTower and parent integration audit

1. `Hurwitz/LadderDeformation.lean` previously established analyticity of each rung but did not
   identify its derivative.  The exact derivative and all-order jet laws close that gap.
2. The `dzeta` undeformed family is now recognized as a normalized differential jet of one base
   Hurwitz function, not merely a parallel list of analytic rungs.
3. `Hurwitz/AllNHZeta.lean` now yields a quadratic differential-independence theorem with no new
   analytic hypothesis.  This is a genuine strengthening of the public theorem surface.
4. Current RHTower modules do not consume the custom complex-shift `hzeta`; therefore no RHTower
   hypothesis is syntactically discharged.  The usable consequence lies in the parent Hurwitz/HT
   layer, where it closes the shift-ladder-to-differential-jet gap.

## Gates

- [x] classical first-derivative parent verified
- [x] all-order differential value law formalized
- [x] shifted ladder identified with a normalized differential jet
- [x] all-(N) quadratic ladder theorem transported to a single-function differential theorem
- [x] direct build and axiom audit
- [x] parent and RHTower consumer audit
- [ ] specialist novelty review of the differential corollary in the Hurwitz literature
