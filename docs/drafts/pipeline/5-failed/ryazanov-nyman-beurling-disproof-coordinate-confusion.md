# Ryazanov Nyman--Beurling disproof by first-coordinate contradiction

- **ID:** ryazanov-nyman-beurling-disproof-coordinate-confusion
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Vladimir Ryazanov, arXiv:1808.10774v9
- **Statement:** The proposed contradiction identifies a coefficient in the original Nyman--Beurling basis with a coefficient in its Gram--Schmidt orthonormalization; the identification is false.

## Proposed route

Assume RH and use the Nyman--Beurling criterion to make the orthogonal
projections `phi_n` converge to the target `chi`.  A preliminary lemma forces
the coefficient of `a_1` in the original expansion of `phi_n` to tend to
`-1`.  The proof then observes that the coefficient of `e_1` in the
orthonormal expansion is fixed and positive, and declares a contradiction.

## Exact obstruction `[PROVED HERE]`

If `e_k=sum_{j<=k}c_{k,j}a_j`, then the coefficient actually controlled by
the preliminary lemma is

```text
h_1^(n) = sum_{k<=n}<chi,e_k>c_{k,1},
```

not `<chi,e_1>`.  The omitted terms are nontrivial: already

```text
e_2 = [a_2-(<a_2,a_1>/||a_1||^2)a_1]/||b_2||
```

has a nonzero `a_1` component because `<a_2,a_1> > 0` for the paper's
fractional-part functions.  Thus the original coordinate may converge to
`-1` while the orthonormal `e_1` coefficient remains fixed and positive.

The complete proof is in
`../2-fully-proven/needs-audit/ryazanov-gram-schmidt-coordinate-mixing.md`.

## Anti-theatre verdict

The argument yields neither an off-critical zero nor an exact negative
Nyman--Beurling distance forced by the zeta source.  The claimed lower bound
later in the paper reuses the same false fixation of the `a_1` coordinate, so
it does not rescue the route.  Formalizing generic change-of-basis algebra
would not advance the RH-false endpoint; no Lean build is authorized.

## Re-entry condition

Reopen only with a bound on the full changing coordinate
`sum_{k<=n}<chi,e_k>c_{k,1}`, or an independent positive lower bound for the
actual Nyman--Beurling distance.  A bound on the fixed `e_1` coordinate alone
does not qualify.

