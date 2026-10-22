# Finite-order continuity of literal Burnol Sonine Mellin jets

- **ID:** burnol-sonin-finite-jet-continuity
- **Stage:** 1-in-progress
- **Type:** LITERATURE bridge / Lean formalization target
- **Source:** J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, §§3–6, especially the analytic evaluator system on the extended Sonine spaces.

## Frozen claim

For every positive aperture `a`, every right-strip point `w` with
`1/2 < Re w < 1`, and every finite `j`, the literal functional

```text
f ↦ d^j/dw^j [ Γ_R(w) ∫₀∞ f(t)t^(-w) dt ]
```

is a bounded complex-linear functional on the corpus carrier
`soninExtendedSpace a`.  Consequently every lower Xi jet that vanishes on
the algebraic cosine-closed co-Poisson source space vanishes on its closed
span.

## Paper proof

Write `f=c` a.e. on `(0,a)`.  On the head, the Mellin integral is exactly
`c a^(1-w)/(1-w)`, analytic for `Re w < 1`; the existing head-norm inequality
controls `c` by `||f||/sqrt(a)`.  On the tail choose a positive margin
`epsilon < Re(w)-1/2`.  In a complex ball around `w`, every differentiated
kernel is a constant multiple of

```text
(log t)^j t^(-z),  t > a.
```

After splitting off the compact interval between `a` and `max(a,1)`, its
norm is dominated on the remaining tail by
`C t^(-(Re(w)-epsilon))`; this belongs to `L²` because
`Re(w)-epsilon > 1/2`.  Cauchy–Schwarz makes the product with every `L²`
tail integrable and supplies a bound linear in `||f||`.  Dominated
differentiation gives the stated formula and continuity.  Leibniz with the
analytic Gamma factor gives the completed jet.  Induction on `j` proves all
finite orders.

## Hostile audit

- This does **not** bound the whole unbounded jet tower uniformly; constants
  necessarily deteriorate with `j` and with distance to `Re w=1/2`.
- It does **not** prove `Y_a^⊥ = P_a`, aperture threshold completeness, or
  minimality.  Those require Burnol’s Krein/Nevanlinna factorization step.
- It is not an RH proof: it only repairs the literal closure step currently
  missing between the algebraic lower-jet theorem and its closed source space.
- The carrier match is exact at the needed level: `soninExtendedSpace a`
  imposes the two constant-head conditions defining Burnol’s extended `L_a`.

## Open formal core

Formalize a first-order dominated-differentiation lemma for the literal tail,
then induct it for finite powers of `log t`; use it to turn the algebraic
lower-jet annihilation theorem into a closed-space theorem.
