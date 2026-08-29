# Theta cusp direct fixed-action C5 compensation law

- **ID:** TC-C5-JCOMP
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Corpus source:** `ThetaCuspReflectedActionVelocityBalance`,
  `ThetaCuspFixedActionC5Jacobian`, `ThetaCuspActionVelocitySeamLogMinorNoGo`, and
  `ThetaCuspFixedActionC5JacobianGermClosure`
- **Statement:** Direct fixed-action C5 Jacobian orientation is exactly one compensated inequality
  between division-free velocity transport and velocity--slope current transport.

## Result

Write `q=thetaCuspReflectedLogAction`, `r=exp(q)-1`, `a=q_t`, `s=q_u`,
`b=q_tt`, `c=q_ttt`, `m=q_tu`, `n=q_ttu`, and `v=t*a`. Define

```
H = a*(t*m) - (a+t*b)*s,
P = a*(t*m+t^2*n) - (a+3*t*b+t^2*c)*s.
```

Here `H` is the division-free fixed-action transport numerator of `v`, while `P` is the same
transport numerator for `v*w=t*(a+t*b)`. For every `u` and every `t>0`, direct-J satisfies

```
4*r*J = 5*P - (14+10*v+8*v/r)*H.
```

Since `r>0`, strict direct-J orientation is equivalent to the sharp compensation inequality

```
(14+10*v+8*v/r)*H < 5*P.
```

No separate sign is imposed on `H` or `P`. This retains exactly the compensation erased by the
retired two-sign transport subroute.

## Proof `[PROVED HERE]`

The corpus writes normalized C5 as `K/(4r)`, where

`K=24r+5vw-14v-5v^2-4v^2/r`.

Along a fixed-action tangent, every derivative of `r=exp(q)-1` cancels. The transport numerators
of `v` and `v*w` are `H` and `P`; differentiating `K` therefore gives

`5P-(14+10v+8v/r)H`. Expanding the literal source jets proves the displayed identity. Positivity
of `r` converts it to the nonstrict and strict equivalences.

## RH passport

literal compensated inequality for all `u,t>0`
→ global positive direct-J orientation
→ fixed-action comparison with the modular reflection centre
→ reflection-odd rank-four/Ptolemy wall
→ arbitrary finite packets and cofinal no-escape
→ CLG/TTF or Weil polarization nonnegativity
→ `riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg` or
  `riemannHypothesis_iff_xiWeilPolarization_nonneg`
→ RH.

Exact next burden: prove the compensated inequality from literal theta atom--likelihood structure
in the local bivariate, compact-middle, and first-atom-tail chambers. Replacing it by independent
signs of `H` and `P` is forbidden by the formal seam no-go.

## Novelty and audit

- Corpus contained the universal fixed-radius barrier derivative and the literal direct Jacobian,
  but no equality joining them and no exact compensation iff.
- Exact literature searches through 2026-08-29 found no fixed-action C5 Jacobian compensation law.
  Planat--Solé, arXiv:2608.19160, studies a different second-level concavity expression.
- Lean module: `RHTower.ThetaCuspFixedActionC5JacobianCompensation`.
- Direct Lean and targeted build pass. Axiom audit: `propext`, `Classical.choice`, `Quot.sound`
  only; no added axioms.

## Log

- 2026-08-29 — corpus-derived conjecture, paper proof, Lean proof, umbrella wiring, targeted build,
  and axiom audit completed.
